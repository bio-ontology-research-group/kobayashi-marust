//! Retained `km incremental-source` session with exact work reuse.
//!
//! Published answers come from the unchanged `km classify` pipeline, either
//! on a complete revision/locality module or on an independently checked exact
//! source subset whose contradiction also proves the admitted revision
//! inconsistent. Retained answers carry exact source support. Reuse never
//! decides an entailment itself:
//!
//! 1. Exact reuse. Revisions are keyed by their exact bytes and by the
//!    order-independent multiset of their top-level statements (plus the
//!    header). A previously classified key returns its stored answer.
//! 2. Deletion reuse. When the revision is a statement subset of a consistent,
//!    complete stored revision `O` (only logical axioms or annotations
//!    removed), the subjects whose ⊥-module in `O` contains a removed axiom are
//!    the only ones whose answers can change (`source_locality`). Monotonicity
//!    narrows them to subjects that had a superclass or were unsatisfiable in
//!    `O`. The pipeline classifies the ⊥-module of those subjects in the new
//!    revision; every other subject keeps its row. When the module of the
//!    empty signature contains a removed axiom, every subject is affected and
//!    NEW-only global/told proofs may still retain exact satisfiable rows;
//!    the complete revision is classified for every remaining subject. The TBox-mode index of a
//!    consistent base reads nominals as empty: a subject whose module
//!    mentions a nominal is affected, and when the remaining subjects' module
//!    mentions one (or is most of a non-EL revision), the complete revision
//!    is classified with the bridge's subject probes restricted to them.
//! 3. Before a common empty-core consistency fallback, a bounded object-ABox
//!    proposal may be independently classified in a fresh process. Only a
//!    complete inconsistent result for exact original source slices licenses
//!    canonical inconsistency publication and a retained support certificate.
//! 4. Otherwise the complete revision is classified.
//!
//! Lean: `ContextCalculus.IncrementalModuleReuse` (module transfer, deletion
//! monotonicity, the merge of retained and recomputed rows, and
//! `nominal_unaffected_query` / `nominal_module_outside` for nominal TBoxes),
//! and `IncrementalVerifiedSupport.verified_support_publication` /
//! `retained_support_publication` for independently checked contradictions;
//! `IncrementalGlobalTold.deletion_row_exact` binds the global-refusal
//! deletion fallback to exact NEW global-role proofs and fixed data semantics.

use std::collections::BTreeSet;
use std::io::{BufRead, Write};
use std::sync::Arc;
use std::time::Instant;

use serde::Deserialize;

use crate::fxhash::{FxHashMap, FxHashSet};
use crate::orchestrate::{Config, OrchestrateError, TaxonomyRows};
use crate::source_locality::{fingerprint, scan, LocalityIndex, Scan, StmtKind};

/// The production flags of `km classify`; set only when the caller left them unset.
const PRODUCTION_DEFAULTS: &[(&str, &str)] = &[
    ("KM_ROUTE", "auto"),
    ("KM_HT_DDB", "1"),
    ("KM_HT_NATIVE_FULL", "1"),
    ("KM_CACHE_CONFORMANCE", "1"),
    ("KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE", "1"),
    ("KM_FAST_IRI_GRAMMAR", "1"),
];

const MEMO_LIMIT: usize = 6;
/// Modules below this many axioms are classified without subject restriction.
const MODULE_RESTRICT_MIN_AXIOMS: usize = 200;
/// Keep serialised answers (whole and per subject) up to this many pairs.
const RENDER_CACHE_PAIRS: usize = 4_000_000;
/// `orchestrate`'s in-process ELC/CB size gate (`INPROC_ELC_MAX`).
const INPROC_SIZE_GATE: usize = 4 << 20;
/// Only search an inconsistency witness when one classification is this cheap.
const WITNESS_MAX_SECONDS: f64 = 3.0;
/// Build the first revision's locality index during `init` only below this.
const EAGER_INDEX_MAX_SECONDS: f64 = 60.0;
const WITNESS_MAX_CHECKS: usize = 400;
const WITNESS_BUDGET_FACTOR: f64 = 10.0;
/// Optional support discovery, including proposal/reconstruction and one check.
const EARLY_OBJECT_SUPPORT_LIMIT: std::time::Duration = std::time::Duration::from_millis(100);

/// `Some(true)`: a fresh `km classify` process published an inconsistent
/// answer within `limit`. `None`: no answer in time.
fn classify_process_inconsistent(doc: &str, limit: std::time::Duration) -> Option<bool> {
    let value = classify_process_json(doc, limit)?;
    Some(value.is_some_and(|v| v.get("consistent") == Some(&serde_json::Value::Bool(false))))
}

/// `Some(Some(json))`: the process published an answer in time;
/// `Some(None)`: it failed; `None`: deadline.
fn classify_process_json(doc: &str, limit: std::time::Duration) -> Option<Option<serde_json::Value>> {
    if limit.is_zero() {
        return None;
    }
    let path = crate::orchestrate::tmpfile::TempPath::new(".ofn");
    std::fs::write(path.path(), doc).ok()?;
    let exe = std::env::current_exe().ok()?;
    let out = crate::orchestrate::tmpfile::TempPath::new("-witness.json");
    use std::os::unix::process::CommandExt;
    let mut child = std::process::Command::new(exe)
        .process_group(0)
        .arg("classify")
        .arg(path.path())
        .stdin(std::process::Stdio::null())
        .stdout(std::fs::File::create(out.path()).ok()?)
        .stderr(std::process::Stdio::null())
        .spawn()
        .ok()?;
    let started = Instant::now();
    loop {
        if let Ok(Some(status)) = child.try_wait() {
            if !status.success() {
                return Some(None);
            }
            let bytes = std::fs::read(out.path()).ok()?;
            return Some(serde_json::from_slice(&bytes).ok());
        }
        if started.elapsed() > limit {
            // The whole group: the worker may have spawned its own workers.
            unsafe { libc::kill(-(child.id() as i32), libc::SIGKILL) };
            let _ = child.wait();
            return None;
        }
        std::thread::sleep(std::time::Duration::from_millis(2));
    }
}

/// Exact full-index preparation plus an optional independently verified core.
/// A failed verifier never certifies a subset, but its index is still reusable.
#[derive(Default)]
struct InconsistencyPreparation {
    witness: Option<Vec<u128>>,
    index: Option<Arc<LocalityIndex>>,
}

/// Verify an empty-signature core, then try a small source-supported clash
/// proposal before the established bounded minimization fallback. Proposals
/// never authorize reuse without an independent inconsistent classification.
fn inconsistency_witness(text: &str, scanned: &Scan, budget_seconds: f64,
    work: &mut PreparationWork) -> InconsistencyPreparation
{
    inconsistency_witness_with(text, scanned, budget_seconds, work,
        classify_process_inconsistent)
}

fn inconsistency_witness_with(text: &str, scanned: &Scan, budget_seconds: f64,
    work: &mut PreparationWork,
    mut verify: impl FnMut(&str, std::time::Duration) -> Option<bool>) -> InconsistencyPreparation
{
    let Ok(index) = work.build_index(text, scanned, false) else {
        return InconsistencyPreparation::default();
    };
    let index = Arc::new(index);
    let core: FxHashSet<u128> = index.empty_module_statements().into_iter().collect();
    let mut header = String::from(&text[..scanned.open_end]);
    header.push('\n');
    let mut candidates = Vec::new();
    let mut seen: FxHashSet<u128> = FxHashSet::default();
    // Preserve the former first probe's bytes: all declarations first, then
    // the unique core axioms in their original order.
    for st in &scanned.statements {
        if st.kind == StmtKind::Declaration {
            header.push_str(&text[st.start..st.end]);
            header.push('\n');
        } else if matches!(st.kind, StmtKind::Logical | StmtKind::Assertion)
            && core.contains(&st.hash) && seen.insert(st.hash)
        {
            candidates.push((st.hash, &text[st.start..st.end]));
        }
    }
    let limit = std::time::Duration::from_secs_f64(budget_seconds);
    let deadline = Instant::now() + limit;
    let mut checks = 0;
    let mut inconsistent = |subset: &[(u128, &str)], per_check: std::time::Duration| {
        checks += 1;
        let remaining = deadline.saturating_duration_since(Instant::now());
        if checks > WITNESS_MAX_CHECKS || remaining.is_zero() {
            return None;
        }
        let mut doc = header.clone();
        for (_, statement) in subset {
            doc.push_str(statement);
            doc.push('\n');
        }
        doc.push_str(")\n");
        let started = Instant::now();
        let verdict = verify(&doc, remaining.min(per_check));
        if std::env::var_os("KM_INCR_DEBUG_WITNESS").is_some() {
            eprintln!("witness check {} statements={} verdict={verdict:?} seconds={:.3}",
                checks, subset.len(), started.elapsed().as_secs_f64());
        }
        Some(verdict == Some(true))
    };
    let first_started = Instant::now();
    if inconsistent(&candidates, limit) != Some(true) {
        return InconsistencyPreparation { witness: None, index: Some(index) };
    }
    let per_check = std::time::Duration::from_secs_f64(
        5.0 * first_started.elapsed().as_secs_f64() + 0.05);
    if deadline > Instant::now() {
        if let Some(proposal) = crate::incr_support::propose(text, scanned) {
            let wanted: FxHashSet<_> = proposal.into_iter().collect();
            let mut emitted = FxHashSet::default();
            let subset: Vec<_> = scanned.statements.iter().filter_map(|statement| {
                (matches!(statement.kind, StmtKind::Logical | StmtKind::Assertion)
                    && wanted.contains(&statement.hash) && emitted.insert(statement.hash))
                    .then(|| (statement.hash, &text[statement.start..statement.end]))
            }).collect();
            // Reconstruct only original source slices. Even a buggy proposal
            // cannot invent a statement or certify itself through this seam.
            if !subset.is_empty() && subset.len() == wanted.len()
                && subset.len() < candidates.len()
                && inconsistent(&subset, per_check) == Some(true)
            {
                return InconsistencyPreparation {
                    witness: Some(subset.into_iter().map(|(hash, _)| hash).collect()),
                    index: Some(index),
                };
            }
        }
    }
    // Preserve the earlier general fallback when no small proposal verifies.
    // Every accepted reduction is independently inconsistent; timeouts keep
    // the last verified support. Both paths share the same deadline and index.
    let mut current = candidates;
    let mut chunk = current.len().div_ceil(2);
    while chunk >= 1 && current.len() > 1 {
        let mut i = 0;
        while i < current.len() {
            let end = (i + chunk).min(current.len());
            let trial: Vec<_> = current[..i].iter().chain(&current[end..]).copied().collect();
            match inconsistent(&trial, per_check) {
                Some(true) => current = trial,
                Some(false) => i = end,
                None => break,
            }
        }
        if chunk == 1 || deadline <= Instant::now() { break; }
        chunk = chunk.div_ceil(2).max(1).min(chunk - 1).max(1);
    }
    InconsistencyPreparation {
        witness: Some(current.into_iter().map(|(hash, _)| hash).collect()),
        index: Some(index),
    }
}

/// A published taxonomy. Rows are shared between revisions.
#[derive(Clone)]
struct Taxonomy {
    consistent: bool,
    dropped: usize,
    iris: Vec<Arc<str>>,
    /// JSON string encoding of each IRI.
    escaped: Vec<Arc<str>>,
    ids: FxHashMap<Arc<str>, u32>,
    rows: Vec<Option<Arc<[u32]>>>,
    unsat: BTreeSet<u32>,
    /// The serialised `result`, kept for repeated publication of the same
    /// answer (exact reuse). Must be cleared whenever rows change.
    rendered: std::sync::OnceLock<Arc<[u8]>>,
    /// Serialised pairs of each subject row (shared between revisions whose
    /// row is unchanged). Reset together with the row.
    chunks: Vec<std::sync::OnceLock<Arc<[u8]>>>,
}

impl Taxonomy {
    fn empty() -> Self {
        Taxonomy {
            consistent: true,
            dropped: 0,
            iris: Vec::new(),
            escaped: Vec::new(),
            ids: FxHashMap::default(),
            rows: Vec::new(),
            unsat: BTreeSet::new(),
            rendered: std::sync::OnceLock::new(),
            chunks: Vec::new(),
        }
    }

    fn id(&mut self, iri: &str) -> u32 {
        if let Some(&id) = self.ids.get(iri) {
            return id;
        }
        let key: Arc<str> = iri.into();
        let id = self.iris.len() as u32;
        self.iris.push(key.clone());
        self.escaped.push(serde_json::to_string(iri).expect("string serialisation").into());
        self.ids.insert(key, id);
        self.rows.push(None);
        self.chunks.push(std::sync::OnceLock::new());
        id
    }

    fn from_rows(t: TaxonomyRows) -> Self {
        let mut tax = Taxonomy::empty();
        tax.consistent = t.consistent;
        tax.dropped = t.dropped;
        let map: Vec<u32> = t.iris.iter().map(|iri| tax.id(iri)).collect();
        for (subject, supers) in t.rows {
            let mut v: Vec<u32> = supers.iter().map(|&s| map[s as usize]).collect();
            v.sort_unstable();
            v.dedup();
            tax.rows[map[subject as usize] as usize] = Some(v.into());
        }
        for u in &t.unsatisfiable {
            let id = tax.id(u);
            tax.unsat.insert(id);
        }
        tax
    }

    /// Write the `result` object, serialising it once (up to 512 MiB).
    fn publish<W: Write>(&self, w: &mut W) -> std::io::Result<()> {
        if let Some(bytes) = self.rendered.get() {
            return w.write_all(bytes);
        }
        if self.pair_count() > RENDER_CACHE_PAIRS {
            return self.write_json(w);
        }
        let mut bytes = Vec::new();
        self.write_json(&mut bytes)?;
        let bytes = self.rendered.get_or_init(|| bytes.into());
        w.write_all(bytes)
    }

    fn pair_count(&self) -> usize {
        self.rows.iter().map(|r| r.as_ref().map_or(0, |v| v.len())).sum()
    }

    /// Write the `result` object as the difference to `prev`, the taxonomy the
    /// client holds at `base_revision`: every subject whose set of superclasses
    /// differs (an empty `o` removes the subject), and the complete
    /// unsatisfiable list. Applying the rows to `prev` gives exactly `self`.
    fn publish_delta<W: Write>(&self, prev: &Taxonomy, base_revision: u64, w: &mut W) -> std::io::Result<()> {
        write!(w, "{{\"delta\":true,\"base_revision\":{base_revision},\"consistent\":{},\"dropped\":{},\"rows\":[",
            self.consistent, self.dropped)?;
        let mut first = true;
        let mut emit = |w: &mut W, subject: &Arc<str>, row: &[&Arc<str>]| -> std::io::Result<()> {
            if !first { w.write_all(b",")?; }
            first = false;
            w.write_all(b"{\"s\":")?;
            w.write_all(subject.as_bytes())?;
            w.write_all(b",\"o\":[")?;
            for (k, o) in row.iter().enumerate() {
                if k > 0 { w.write_all(b",")?; }
                w.write_all(o.as_bytes())?;
            }
            w.write_all(b"]}")
        };
        let aligned = prev.iris.len() <= self.iris.len()
            && prev.iris.iter().zip(&self.iris).all(|(a, b)| Arc::ptr_eq(a, b) || a == b);
        const NONE: &[u32] = &[];
        fn slice(r: &Option<Arc<[u32]>>) -> &[u32] { r.as_deref().unwrap_or(NONE) }
        for (s, row) in self.rows.iter().enumerate() {
            let new_row = slice(row);
            let changed = if aligned {
                let old = prev.rows.get(s).map_or(NONE, slice);
                new_row != old
            } else {
                let old_row = prev.ids.get(&*self.iris[s]).map_or(NONE, |&id| slice(&prev.rows[id as usize]));
                let mut a: Vec<&str> = new_row.iter().map(|&o| &*self.iris[o as usize]).collect();
                let mut b: Vec<&str> = old_row.iter().map(|&o| &*prev.iris[o as usize]).collect();
                a.sort_unstable(); b.sort_unstable();
                a != b
            };
            if changed {
                let objects: Vec<&Arc<str>> = new_row.iter().map(|&o| &self.escaped[o as usize]).collect();
                emit(w, &self.escaped[s], &objects)?;
            }
        }
        if !aligned {
            // Subjects the new taxonomy does not mention at all lose their row.
            for (s, row) in prev.rows.iter().enumerate() {
                if slice(row).is_empty() || self.ids.contains_key(&*prev.iris[s]) { continue; }
                emit(w, &prev.escaped[s], &[])?;
            }
        }
        w.write_all(b"],\"unsatisfiable\":[")?;
        for (k, u) in self.unsat.iter().enumerate() {
            if k > 0 { w.write_all(b",")?; }
            w.write_all(self.escaped[*u as usize].as_bytes())?;
        }
        w.write_all(b"]}")
    }

    fn write_json<W: Write>(&self, w: &mut W) -> std::io::Result<()> {
        let escaped = &self.escaped;
        let cache_chunks = self.pair_count() <= RENDER_CACHE_PAIRS;
        w.write_all(b"{\"consistent\":")?;
        w.write_all(if self.consistent { b"true" } else { b"false" })?;
        w.write_all(b",\"subsumptions\":[")?;
        let mut first = true;
        // The relation is a set: subjects and superclasses in id order.
        for (s, row) in self.rows.iter().enumerate() {
            let Some(row) = row else { continue };
            if row.is_empty() {
                continue;
            }
            if !cache_chunks {
                for &o in row.iter() {
                    if !first {
                        w.write_all(b",")?;
                    }
                    first = false;
                    w.write_all(b"[")?;
                    w.write_all(escaped[s].as_bytes())?;
                    w.write_all(b",")?;
                    w.write_all(escaped[o as usize].as_bytes())?;
                    w.write_all(b"]")?;
                }
                continue;
            }
            let chunk = self.chunks[s].get_or_init(|| {
                let mut c = Vec::with_capacity(row.len() * (escaped[s].len() + 48));
                for (k, &o) in row.iter().enumerate() {
                    if k > 0 {
                        c.push(b',');
                    }
                    c.push(b'[');
                    c.extend_from_slice(escaped[s].as_bytes());
                    c.push(b',');
                    c.extend_from_slice(escaped[o as usize].as_bytes());
                    c.push(b']');
                }
                c.into()
            });
            if !first {
                w.write_all(b",")?;
            }
            first = false;
            w.write_all(chunk)?;
        }
        w.write_all(b"],\"unsatisfiable\":[")?;
        for (k, u) in self.unsat.iter().enumerate() {
            if k > 0 {
                w.write_all(b",")?;
            }
            w.write_all(escaped[*u as usize].as_bytes())?;
        }
        write!(w, "],\"dropped\":{}}}", self.dropped)
    }
}

/// Statement multiset of one revision, by fingerprint.
///
/// Fingerprints only select candidates: every reuse decision is confirmed on
/// the statement texts (`exact_eq`, `confirms_subset`), so a fingerprint
/// collision can never make two different statements or revisions count as
/// equal. A revision with two different statements of equal fingerprint is
/// never reused (`collision`).
struct Statements {
    header_hash: u128,
    /// Count, kind and the span of one statement with this fingerprint.
    counts: FxHashMap<u128, (u32, StmtKind, usize, usize)>,
    total: usize,
    /// The revision text the spans point into.
    text: Arc<String>,
    header_end: usize,
    /// Two statements with equal fingerprint and different text.
    collision: bool,
}

impl Statements {
    fn of(s: &Scan, text: &Arc<String>) -> Self {
        let mut counts: FxHashMap<u128, (u32, StmtKind, usize, usize)> = FxHashMap::default();
        counts.reserve(s.statements.len());
        let mut collision = false;
        for st in &s.statements {
            match counts.entry(st.hash) {
                std::collections::hash_map::Entry::Vacant(v) => {
                    v.insert((1, st.kind, st.start, st.end));
                }
                std::collections::hash_map::Entry::Occupied(mut o) => {
                    let e = o.get_mut();
                    e.0 += 1;
                    collision |= text[e.2..e.3] != text[st.start..st.end];
                }
            }
        }
        Statements {
            header_hash: s.header_hash, counts, total: s.statements.len(), text: text.clone(),
            header_end: s.open_end, collision,
        }
    }

    fn header(&self) -> &str {
        &self.text[..self.header_end]
    }

    fn stmt(&self, h: &u128) -> Option<&str> {
        self.counts.get(h).map(|&(_, _, a, b)| &self.text[a..b])
    }

    /// The same header and the same statement multiset, compared on text.
    fn exact_eq(&self, other: &Statements) -> bool {
        !self.collision && !other.collision
            && self.total == other.total
            && self.counts.len() == other.counts.len()
            && self.header() == other.header()
            && self.counts.iter().all(|(h, &(n, _, a, b))| {
                other.counts.get(h).is_some_and(|&(m, _, c, d)| m == n && self.text[a..b] == other.text[c..d])
            })
    }

    /// Every statement of `self` has the text of `base`'s statement with the
    /// same fingerprint, and the headers are equal: fingerprints are then
    /// injective on the union of both revisions' statements, so the counted
    /// subset and the removed set are exact.
    fn confirms_subset(&self, base: &Statements) -> bool {
        !self.collision && !base.collision
            && self.header() == base.header()
            && self.counts.iter().all(|(h, &(_, _, a, b))| base.stmt(h) == Some(&self.text[a..b]))
    }
}

/// Immutable source support for an already verified inconsistent answer.
/// Lean: `IncrementalModuleReuse.inconsistent_superset`. This owns no locality
/// index and survives independently of the revision that discovered the clash.
struct InconsistencyCertificate {
    /// Identity of the exact source whose inconsistency/support was verified.
    origin_source_key: u128,
    origin_statement_count: usize,
    support: InconsistencySupport,
}

enum InconsistencySupport {
    /// Share the original source/map; do not duplicate its statement strings.
    Full(Arc<Statements>),
    /// The witness verifier keeps the original prefix/ontology header and all
    /// declarations. Preserve those exact supports too, so containment needs
    /// no new declaration-erasure assumption. No original full source is held.
    Witness { header: Arc<str>, statements: Vec<(u128, Arc<str>)> },
}

impl InconsistencyCertificate {
    /// Called only after source inconsistency was established, either by its
    /// complete answer or an independently checked exact subset. A witness
    /// must have its own complete inconsistent result before construction.
    fn from_verified_inconsistent(source: Arc<Statements>, witness: Option<&[u128]>)
        -> Option<Arc<Self>>
    {
        if source.collision { return None; }
        let support = if let Some(witness) = witness {
            if witness.iter().any(|h| source.stmt(h).is_none()) { return None; }
            let wanted: FxHashSet<u128> = witness.iter().copied().collect();
            let statements = source.counts.iter().filter_map(|(hash, &(_, kind, a, b))| {
                (kind == StmtKind::Declaration || wanted.contains(hash))
                    .then(|| (*hash, Arc::<str>::from(&source.text[a..b])))
            }).collect();
            InconsistencySupport::Witness { header: Arc::from(source.header()), statements }
        } else {
            InconsistencySupport::Full(source.clone())
        };
        Some(Arc::new(Self {
            origin_source_key: fingerprint(source.text.as_bytes()),
            origin_statement_count: source.total,
            support,
        }))
    }

    fn contained_in(&self, new: &Statements) -> bool {
        if new.collision { return false; }
        match &self.support {
            InconsistencySupport::Full(source) => source.confirms_subset(new),
            InconsistencySupport::Witness { header, statements } => {
                header.as_ref() == new.header()
                    && statements.iter().all(|(h, text)| new.stmt(h) == Some(text.as_ref()))
            }
        }
    }

    fn strategy(&self) -> &'static str {
        match &self.support {
            InconsistencySupport::Full(_) => "inconsistency_superset_reuse",
            InconsistencySupport::Witness { .. } => "inconsistency_witness_reuse",
        }
    }
}


/// The NEW source has already passed public admission. Proposals supply only
/// statement identities; reconstruct and independently classify original text.
/// No locality index or whole-source inconsistency result is needed here.
fn early_object_support_with(source: &Arc<Statements>, scanned: &Scan,
    verify: &mut impl FnMut(&str, std::time::Duration) -> Option<Option<serde_json::Value>>)
    -> Option<Arc<InconsistencyCertificate>>
{
    let deadline = Instant::now() + EARLY_OBJECT_SUPPORT_LIMIT;
    let proposal = crate::incr_support::propose_object(&source.text, scanned)?;
    verified_source_support_with(source, scanned, &proposal, deadline, verify)
}

fn verified_source_support_with(source: &Arc<Statements>, scanned: &Scan,
    proposal: &[u128], deadline: Instant,
    verify: &mut impl FnMut(&str, std::time::Duration) -> Option<Option<serde_json::Value>>)
    -> Option<Arc<InconsistencyCertificate>>
{
    if source.collision || proposal.is_empty() || proposal.len() > 64
        || scanned.open_end != source.header_end { return None; }
    let wanted: FxHashSet<_> = proposal.iter().copied().collect();
    let mut header = String::from(source.header()); header.push('\n');
    let mut axioms = String::new();
    let mut emitted = FxHashSet::default();
    for statement in &scanned.statements {
        let slice = source.text.get(statement.start..statement.end)?;
        if fingerprint(slice.as_bytes()) != statement.hash
            || source.stmt(&statement.hash) != Some(slice) { return None; }
        if statement.kind == StmtKind::Declaration {
            header.push_str(slice); header.push('\n');
        } else if matches!(statement.kind, StmtKind::Logical | StmtKind::Assertion)
            && wanted.contains(&statement.hash) && emitted.insert(statement.hash)
        {
            axioms.push_str(slice); axioms.push('\n');
        }
    }
    if emitted.len() != wanted.len() { return None; }
    header.push_str(&axioms); header.push_str(")\n");
    let remaining = deadline.saturating_duration_since(Instant::now());
    if remaining.is_zero() { return None; }
    let answer = verify(&header, remaining)??;
    if Instant::now() > deadline
        || answer.get("consistent") != Some(&serde_json::Value::Bool(false))
        || answer.get("dropped").and_then(serde_json::Value::as_u64) != Some(0)
    { return None; }
    InconsistencyCertificate::from_verified_inconsistent(source.clone(), Some(proposal))
}

struct Revision {
    /// The exact revision text; a `text_key` hit is confirmed against it.
    text: Arc<String>,
    /// Its statements (`None` when the scan failed); a `content_key` hit is
    /// confirmed with `Statements::exact_eq`.
    statements: Option<Arc<Statements>>,
    text_key: u128,
    content_key: u128,
    taxonomy: Arc<Taxonomy>,
    /// Propagated without depending on BaseState or an older memo entry.
    inconsistency: Option<Arc<InconsistencyCertificate>>,
    /// Present for completely classified revisions that can serve as a
    /// deletion base: their statements, and their source until the locality
    /// index is built.
    base: Option<BaseState>,
    last_use: u64,
}

/// Preparation state is explicit: a masked union is not an exact NEW index.
/// Nothing here is committed until either module publication succeeds or a
/// complete fresh classification succeeds. Consistent complete answers may
/// retain a masked union; inconsistent answers still materialize exact NEW.
enum PreparedCompiler {
    Exact(Arc<LocalityIndex>),
    Union { source: Arc<String>, scan: Scan, index: Arc<LocalityIndex> },
}

impl PreparedCompiler {
    fn index(&self) -> &Arc<LocalityIndex> {
        match self { Self::Exact(index) | Self::Union { index, .. } => index }
    }

    fn text<'a>(&'a self, exact: &'a str) -> &'a str {
        match self { Self::Exact(_) => exact, Self::Union { source, .. } => source }
    }

    fn scan<'a>(&'a self, exact: &'a Scan) -> &'a Scan {
        match self { Self::Exact(_) => exact, Self::Union { scan, .. } => scan }
    }

    fn tbox_index(&self, exact: &str, scanned: &Scan,
        cached: Option<&Arc<LocalityIndex>>, work: &mut PreparationWork)
        -> Result<Arc<LocalityIndex>, String>
    {
        match cached {
            Some(index) => Ok(index.clone()),
            None => work.build_index(self.text(exact), self.scan(scanned), true).map(Arc::new),
        }
    }

    /// Called only after successful complete, consistent full classification.
    /// Keep the same full-index/mask contract as successful common reuse.
    fn consistent_union_base(&self, text: &str, scanned: &Scan,
        statements: Arc<Statements>) -> Option<BaseState>
    {
        let Self::Union { index, .. } = self else { return None };
        if !index.full_mode || index.spelling_conflict || statements.collision { return None; }
        let names = index.live_public_class_names(|hash| statements.counts.contains_key(&hash))?;
        let mut domain: FxHashSet<Box<str>> = names.into_iter().map(Box::from).collect();
        domain.extend(["owl:Thing", "owl:Nothing", "http://www.w3.org/2002/07/owl#Thing",
            "http://www.w3.org/2002/07/owl#Nothing"].into_iter().map(Box::<str>::from));
        let disabled: Vec<_> = index.axiom_hash.iter()
            .map(|hash| !statements.counts.contains_key(hash)).collect();
        let removed_hashes = index.axiom_hash.iter().zip(&disabled)
            .filter_map(|(hash, disabled)| disabled.then_some(*hash)).collect();
        Some(BaseState {
            statements: statements.clone(), source: None,
            index: Some(Some(index.clone())), compiler_full: Some(index.clone()),
            admission: None, disabled: disabled.into(), full_disabled: Arc::from([]),
            removed_hashes: Arc::new(removed_hashes), class_domain: Some(Arc::new(domain)),
            // Match ordinary full fallback: prepare NEW proofs only when a
            // later index request actually needs them, not on this update.
            full: None, told: None,
            consistent: true, witness: None,
            anonymous: anonymous_assertions(text, scanned), source_bytes: text.len(),
        })
    }

    fn into_exact(self, text: &str, scanned: &Scan, work: &mut PreparationWork)
        -> Option<Arc<LocalityIndex>>
    {
        match self {
            Self::Exact(index) => Some(index),
            Self::Union { source, scan, index } => {
                // This map is needed only on declined common publication,
                // after complete classification succeeded. Successful module
                // reuse never builds another full statement map.
                let statements = Statements::of(&scan, &source);
                if statements.collision { return None; }
                work.build_reusing_full(text, scanned, &index,
                    statements.header(), |hash| statements.stmt(&hash)).ok().map(Arc::new)
            },
        }
    }
}

/// Exact text backing for every support recorded in an immutable told graph.
/// A masked deletion view never changes this provenance.
struct RetainedTold {
    proofs: crate::source_locality::ToldProofs,
    statements: Arc<Statements>,
    preparation: crate::source_locality::ToldReuse,
}

impl RetainedTold {
    fn prepare(text: &str, scanned: &Scan, statements: Arc<Statements>,
        donor: Option<&Self>) -> Self
    {
        let (proofs, preparation) = match donor.filter(|old| !old.statements.collision && !statements.collision) {
            Some(old) => {
                let lookup = |hash| old.statements.stmt(&hash);
                crate::source_locality::ToldProofs::build_reusing(text, scanned,
                    Some((&old.proofs, old.statements.header(), &lookup)))
            }
            None => crate::source_locality::ToldProofs::build_reusing(text, scanned, None),
        };
        Self { proofs, statements, preparation }
    }
}

struct BaseState {
    statements: Arc<Statements>,
    source: Option<(Arc<String>, Scan)>,
    index: Option<Option<Arc<LocalityIndex>>>,
    /// Full-mode compiler donor only, independent of semantic TBox/full masks.
    /// Current Statements are the exact enabled-text guard for every reuse.
    compiler_full: Option<Arc<LocalityIndex>>,
    /// Immutable actually-validated origin; deletion carries this Arc for free.
    admission: Option<Arc<crate::named_subclass_validation::NamedSubclassCertificate>>,
    /// Axioms absent from this exact revision in the shared original index.
    disabled: Arc<[bool]>,
    full_disabled: Arc<[bool]>,
    /// Removed original statements, including told-proof supports.
    removed_hashes: Arc<FxHashSet<u128>>,
    class_domain: Option<Arc<FxHashSet<Box<str>>>>,
    /// The full (assertion-keeping) index, built next to a TBox-mode index
    /// that has nominal axioms: a deletion whose empty-signature module in it
    /// avoids the removed statements keeps the plain module path, which the
    /// nominal TBox index would send to the complete revision.
    full: Option<Arc<LocalityIndex>>,
    /// Told proofs of this revision, built with the index; a deletion masks
    /// its removed statements.
    told: Option<Arc<RetainedTold>>,
    consistent: bool,
    /// Statements of a subset verified inconsistent by the pipeline.
    witness: Option<Vec<u128>>,
    /// Object-property assertions that mention an anonymous individual.
    anonymous: FxHashSet<u128>,
    /// Byte length of the source (selects the pipeline's in-process arms).
    source_bytes: usize,
}

impl BaseState {
    /// Only an unmasked exact-source pair can stand for OLD union NEW on
    /// deletion. A compiler-only donor or a historical masked base cannot.
    fn exact_union_pair(&self, selected: &Statements, new: &Statements)
        -> Option<(PreparedCompiler, Arc<LocalityIndex>)>
    {
        let tbox = self.index.as_ref()?.as_ref()?;
        let full = self.full.as_ref()?;
        if !self.consistent || !tbox.tbox_mode || !full.full_mode
            || tbox.spelling_conflict || full.spelling_conflict
            || !self.removed_hashes.is_empty()
            || self.disabled.len() != tbox.axiom_count()
            || self.full_disabled.len() != full.axiom_count()
            || self.disabled.iter().any(|disabled| *disabled)
            || self.full_disabled.iter().any(|disabled| *disabled)
            || !(std::ptr::eq(self.statements.as_ref(), selected) || self.statements.exact_eq(selected))
            || !new.confirms_subset(&self.statements)
        { return None; }
        let source = self.statements.text.clone();
        let scanned = scan(&source).ok()?;
        Some((PreparedCompiler::Union { source, scan: scanned, index: full.clone() }, tbox.clone()))
    }

    fn index(&mut self, work: &mut PreparationWork) -> Option<&LocalityIndex> {
        if self.index.is_none() {
            let consistent = self.consistent;
            let mut full = None;
            let compiler_full = self.compiler_full.clone();
            let mut told = None;
            let told_statements = self.statements.clone();
            let built = self.source.take().and_then(|(text, s)| {
                if consistent {
                    told = Some(Arc::new(RetainedTold::prepare(&text, &s, told_statements, None)));
                }
                // TBox mode needs both revisions consistent: a deletion from
                // a consistent base. An inconsistent base keeps assertions.
                // A prepared compiler belongs to this exact committed source.
                // For an inconsistent base it is already the required full
                // semantic index, including when the witness probe declined.
                let ix = if !consistent { compiler_full.clone() } else { None };
                let ix = match ix {
                    Some(index) => { debug_assert!(index.full_mode); index },
                    None => Arc::new(work.build_index(&text, &s, consistent).ok()?),
                };
                if ix.tbox_mode && ix.nominal.iter().any(|n| *n) {
                    // source.is_some() means this donor, if present, was
                    // prepared for this exact committed NEW source. Derived
                    // masked bases have source=None and never enter here.
                    full = compiler_full.clone().or_else(||
                        work.build_index(&text, &s, false).ok().map(Arc::new));
                }
                Some(ix)
            });
            self.disabled = vec![false; built.as_ref().map_or(0, |i| i.axiom_count())].into();
            self.full_disabled = vec![false; full.as_ref().map_or(0, |i| i.axiom_count())].into();
            self.class_domain = built.as_ref().map(|i| Arc::new(class_domain(i)));
            if self.compiler_full.is_none() {
                self.compiler_full = full.clone().or_else(||
                    built.as_ref().filter(|index| index.full_mode).cloned());
            }
            self.index = Some(built);
            self.full = full;
            self.told = told;
        }
        if self.consistent && self.told.is_none()
            && self.index.as_ref().is_some_and(|index| index.is_some())
        {
            // Masked UNION has no exact compiler source, but Statements owns
            // exactly NEW. Cache these proofs once without replacing index
            // provenance or inheriting historical disabled proof supports.
            if let Ok(scanned) = scan(&self.statements.text) {
                self.told = Some(Arc::new(RetainedTold::prepare(
                    &self.statements.text, &scanned, self.statements.clone(), None)));
            }
        }
        self.index.as_ref().and_then(|i| i.as_deref())
    }

    /// Retain the exact successor while sharing immutable parsing/index work.
    /// The masks describe its live axiom view; the original base stays intact.
    fn after_deletion(&self, statements: Arc<Statements>, removed: &[u128]) -> Self {
        let mask = |index: Option<&LocalityIndex>, old: &[bool]| -> Arc<[bool]> {
            let Some(index) = index else { return Arc::from([]) };
            assert_eq!(old.len(), index.axiom_count());
            let mut next = old.to_vec();
            for hash in removed {
                if let Some(&id) = index.axiom_by_hash.get(hash) {
                    next[id as usize] = true;
                }
            }
            next.into()
        };
        let disabled = mask(self.index.as_ref().and_then(|i| i.as_deref()), &self.disabled);
        let full_disabled = mask(self.full.as_deref(), &self.full_disabled);
        let mut removed_hashes = (*self.removed_hashes).clone();
        removed_hashes.extend(removed.iter().copied());
        BaseState {
            source_bytes: statements.text.len(),
            statements,
            source: None,
            index: self.index.clone(),
            compiler_full: self.compiler_full.clone(),
            admission: self.admission.clone(),
            disabled,
            full_disabled,
            removed_hashes: Arc::new(removed_hashes),
            class_domain: self.class_domain.clone(),
            full: self.full.clone(),
            told: self.told.clone(),
            consistent: true,
            witness: None,
            anonymous: self.anonymous.clone(),
        }
    }
}

pub struct Session {
    memo: Vec<Revision>,
    current: Option<usize>,
    revision: u64,
    clock: u64,
    /// The current transaction's NEW text passed `check_user_source` (the
    /// public validation the pipeline would repeat), so a classification of
    /// exactly that text may run with `classify_text_certified`.
    validated_new: bool,
}

#[derive(Default)]
struct Receipt {
    strategy: &'static str,
    base_revision_statements: usize,
    removed_statements: usize,
    removed_axioms: usize,
    added_statements: usize,
    added_axioms: usize,
    reused_index_axioms: usize,
    rebuilt_index_axioms: usize,
    index_build_calls: usize,
    index_build_failures: usize,
    cross_revision_compiled_axioms: usize,
    same_update_compiled_axioms: usize,
    compiled_locality_axioms: usize,
    csr_axiom_records: usize,
    csr_conjunctions: usize,
    csr_literal_records: usize,
    resumed_backend_states: usize,
    reused_complete_answer: bool,
    statement_delta_verified: bool,
    affected_subjects: usize,
    reclassified_subjects: usize,
    module_axioms: usize,
    index_axioms: usize,
    reused_subjects: usize,
    /// Relevant subjects whose base row was proved syntactically (kept).
    told_subjects: usize,
    seconds: f64,
    fallback_reason: Option<String>,
}

/// Work completed by index API calls during the entire transaction, including
/// attempts whose reuse certificate later declines. Cached indexes count zero.
/// These count returned index axiom records, not internal compiler operations.
#[derive(Default)]
struct PreparationWork {
    /// Own the bounded set of donors that existed before this transaction.
    /// Lazy index builds during a declined attempt are not cross-revision work.
    prior_compilers: Vec<Arc<LocalityIndex>>,
    rebuilt_index_axioms: usize,
    index_build_calls: usize,
    index_build_failures: usize,
    cross_revision_compiled_axioms: usize,
    same_update_compiled_axioms: usize,
    compiled_locality_axioms: usize,
    csr_axiom_records: usize,
    csr_conjunctions: usize,
    csr_literal_records: usize,
}

impl PreparationWork {
    fn record_assembly(&mut self, index: &LocalityIndex) {
        let (axioms, conjunctions, literals) = index.assembly_work();
        self.rebuilt_index_axioms += axioms;
        self.csr_axiom_records += axioms;
        self.csr_conjunctions += conjunctions;
        self.csr_literal_records += literals;
    }

    fn build_reusing_full<'a>(&mut self, text: &str, scanned: &Scan,
        donor: &LocalityIndex, donor_header: &str,
        donor_statement: impl Fn(u128) -> Option<&'a str>)
        -> Result<LocalityIndex, String>
    {
        let cross_revision = self.prior_compilers.iter().any(|old|
            std::ptr::eq(old.as_ref(), donor));
        self.index_build_calls += 1;
        match LocalityIndex::build_reusing_full(text, scanned, donor, donor_header, donor_statement) {
            Ok((index, stats)) => {
                self.record_assembly(&index);
                self.compiled_locality_axioms += stats.compiled_axioms;
                if cross_revision { self.cross_revision_compiled_axioms += stats.reused_compiled_axioms; }
                else { self.same_update_compiled_axioms += stats.reused_compiled_axioms; }
                Ok(index)
            }
            Err(error) => { self.index_build_failures += 1; Err(error) }
        }
    }
    fn build_index(&mut self, text: &str, scanned: &Scan, tbox: bool)
        -> Result<LocalityIndex, String>
    {
        self.index_build_calls += 1;
        match LocalityIndex::build(text, scanned, tbox) {
            Ok(index) => {
                self.compiled_locality_axioms += index.axiom_count();
                self.record_assembly(&index);
                Ok(index)
            }
            Err(error) => {
                self.index_build_failures += 1;
                Err(error)
            }
        }
    }
}

#[derive(Clone, Copy, Default)]
struct StatementDelta {
    added_statements: usize, removed_statements: usize,
    added_axioms: usize, removed_axioms: usize,
}

impl Receipt {
    fn record_preparation(&mut self, work: &PreparationWork) {
        // Assign the caller's complete ledger once; do not add successful
        // attempt counts again after a decline or repeated publication.
        self.rebuilt_index_axioms = work.rebuilt_index_axioms;
        self.index_build_calls = work.index_build_calls;
        self.index_build_failures = work.index_build_failures;
        self.cross_revision_compiled_axioms = work.cross_revision_compiled_axioms;
        self.same_update_compiled_axioms = work.same_update_compiled_axioms;
        self.compiled_locality_axioms = work.compiled_locality_axioms;
        self.csr_axiom_records = work.csr_axiom_records;
        self.csr_conjunctions = work.csr_conjunctions;
        self.csr_literal_records = work.csr_literal_records;
    }

    fn apply_delta(&mut self, delta: StatementDelta) {
        self.added_statements = delta.added_statements;
        self.removed_statements = delta.removed_statements;
        self.added_axioms = delta.added_axioms;
        self.removed_axioms = delta.removed_axioms;
        self.statement_delta_verified = true;
    }
    fn set_transaction_delta(&mut self, delta: Option<StatementDelta>) {
        self.added_statements = 0;
        self.removed_statements = 0;
        self.added_axioms = 0;
        self.removed_axioms = 0;
        self.statement_delta_verified = false;
        if let Some(delta) = delta { self.apply_delta(delta); }
    }

    fn meaningful_reuse(&self) -> bool {
        self.reused_complete_answer || self.reused_subjects != 0 || self.reused_index_axioms != 0
            || self.cross_revision_compiled_axioms != 0
    }
}

/// Exact source spellings used by the public taxonomy, not the larger union
/// symbol universe. Builtins remain classes even without declarations.
fn is_builtin_class_name(name: &str) -> bool {
    matches!(name, "owl:Thing" | "owl:Nothing"
        | "http://www.w3.org/2002/07/owl#Thing" | "http://www.w3.org/2002/07/owl#Nothing")
}

fn class_domain(index: &LocalityIndex) -> FxHashSet<Box<str>> {
    let mut domain: FxHashSet<Box<str>> = index.names.iter().zip(&index.symbols).zip(&index.is_class)
        .filter(|((_, symbol), class)| **class || is_builtin_class_name(symbol))
        .map(|((name, _), _)| name.clone()).collect();
    domain.extend(["owl:Thing", "owl:Nothing", "http://www.w3.org/2002/07/owl#Thing",
        "http://www.w3.org/2002/07/owl#Nothing"].into_iter().map(Box::<str>::from));
    domain
}

fn anonymous_assertions(text: &str, scanned: &Scan) -> FxHashSet<u128> {
    scanned.statements.iter().filter(|statement| {
        let value = &text[statement.start..statement.end];
        (value.starts_with("ObjectPropertyAssertion") || value.starts_with("NegativeObjectPropertyAssertion"))
            && value.contains("_:")
    }).map(|statement| statement.hash).collect()
}

/// Fingerprints only select comparisons: equal hashes must name equal text.
fn statement_delta(old: &Statements, new: &Statements) -> Option<StatementDelta> {
    statement_delta_probe(old, new, None)
}

/// `statement_delta`, additionally listing (up to `ADDED_PROBE_MAX`) the
/// fingerprints of statements of NEW that OLD lacks. The list is complete only
/// when it is not longer than the cap; a longer one is truncated and unusable.
const ADDED_PROBE_MAX: usize = 32;

fn statement_delta_probe(old: &Statements, new: &Statements, mut added: Option<&mut Vec<u128>>)
    -> Option<StatementDelta>
{
    if old.collision || new.collision || old.header() != new.header() { return None; }
    let mut delta = StatementDelta::default();
    for (hash, &(count, kind, a, b)) in &old.counts {
        if let Some(&(after, _, c, d)) = new.counts.get(hash) {
            if old.text[a..b] != new.text[c..d] { return None; }
            delta.removed_statements += count.saturating_sub(after) as usize;
            delta.added_statements += after.saturating_sub(count) as usize;
        } else {
            delta.removed_statements += count as usize;
            if matches!(kind, StmtKind::Logical | StmtKind::Assertion) { delta.removed_axioms += 1; }
        }
    }
    for (hash, &(count, kind, ..)) in &new.counts {
        if !old.counts.contains_key(hash) {
            delta.added_statements += count as usize;
            if matches!(kind, StmtKind::Logical | StmtKind::Assertion) { delta.added_axioms += 1; }
            if let Some(list) = added.as_deref_mut() {
                if list.len() <= ADDED_PROBE_MAX { list.push(*hash); }
            }
        }
    }
    Some(delta)
}

/// Remove obsolete public subjects/targets without renumbering stable IDs.
/// Every modified row loses its own immutable render cache as well.
fn prune_public_domain(tax: &mut Taxonomy, domain: &FxHashSet<Box<str>>) -> FxHashSet<Box<str>> {
    let mut changed = FxHashSet::default();
    if tax.iris.iter().all(|name| domain.contains(&**name)) { return changed; }
    for id in 0..tax.rows.len() {
        if !domain.contains(&*tax.iris[id]) {
            if tax.rows[id].is_some() || tax.unsat.contains(&(id as u32)) {
                changed.insert(Box::<str>::from(&*tax.iris[id]));
            }
            tax.rows[id] = None;
            tax.unsat.remove(&(id as u32));
            tax.chunks[id] = std::sync::OnceLock::new();
        } else if let Some(row) = &tax.rows[id] {
            let kept: Vec<u32> = row.iter().copied().filter(|&target| domain.contains(&*tax.iris[target as usize])).collect();
            if kept.len() != row.len() {
                changed.insert(Box::<str>::from(&*tax.iris[id]));
                tax.rows[id] = (!kept.is_empty()).then(|| Arc::from(kept));
                tax.chunks[id] = std::sync::OnceLock::new();
            }
        }
    }
    if !changed.is_empty() { tax.rendered = std::sync::OnceLock::new(); }
    changed
}

fn stage(label: &str, started: Instant) {
    if std::env::var_os("KM_INCR_TIMING").is_some() {
        eprintln!("KM_INCR_TIMING {label} @ {:.4}s", started.elapsed().as_secs_f64());
    }
}

fn apply_production_defaults() {
    for (key, value) in PRODUCTION_DEFAULTS {
        if std::env::var_os(key).is_none() {
            std::env::set_var(key, value);
        }
    }
}

/// Restores the complete process environment (the orchestrator's routing
/// changes process-wide KM_* keys).
struct FullEnvironment(Vec<(std::ffi::OsString, std::ffi::OsString)>);

impl FullEnvironment {
    fn capture() -> Self {
        FullEnvironment(std::env::vars_os().collect())
    }
}

impl Drop for FullEnvironment {
    fn drop(&mut self) {
        let keep: FxHashSet<&std::ffi::OsString> = self.0.iter().map(|(k, _)| k).collect();
        let current: Vec<std::ffi::OsString> = std::env::vars_os().map(|(k, _)| k).collect();
        for key in current {
            if !keep.contains(&key) {
                std::env::remove_var(&key);
            }
        }
        for (key, value) in &self.0 {
            if std::env::var_os(key).as_ref() != Some(value) {
                std::env::set_var(key, value);
            }
        }
    }
}

/// The unchanged `km classify` pipeline on one source text.
fn classify_text(text: &str) -> Result<Taxonomy, String> {
    classify_text_with(text, &[])
}

/// The pipeline with extra environment settings (existing pipeline options only).
fn classify_text_with(text: &str, settings: &[(&str, &str)]) -> Result<Taxonomy, String> {
    classify_text_impl(text, settings, false)
}

/// Like `classify_text_with` for a text whose conformance this session already
/// established through a derived admission certificate (the same certificate
/// that lets the common path skip `check_user_source`). The pipeline then does
/// not repeat whole-source validation. Callers must hold such a certificate.
fn classify_text_certified(text: &str, settings: &[(&str, &str)]) -> Result<Taxonomy, String> {
    classify_text_impl(text, settings, true)
}

fn classify_text_impl(text: &str, settings: &[(&str, &str)], certified: bool) -> Result<Taxonomy, String> {
    let rows = classify_rows_impl(text, settings, certified)?;
    let started = Instant::now();
    let tax = Taxonomy::from_rows(rows);
    stage("rows indexed", started);
    Ok(tax)
}

/// The pipeline's grouped answer, before indexing.
fn classify_rows_with(text: &str, settings: &[(&str, &str)]) -> Result<TaxonomyRows, String> {
    classify_rows_impl(text, settings, false)
}

fn classify_rows_impl(text: &str, settings: &[(&str, &str)], certified: bool) -> Result<TaxonomyRows, String> {
    let path = crate::orchestrate::tmpfile::TempPath::new(".ofn");
    std::fs::write(path.path(), text).map_err(|e| e.to_string())?;
    classify_rows_at(&path, settings, certified)
}

/// The pipeline on a source already written to `path` (a fresh temporary
/// file of this process); `certified` as for `classify_text_certified`.
fn classify_taxonomy_at(path: &crate::orchestrate::tmpfile::TempPath, settings: &[(&str, &str)],
    certified: bool) -> Result<Taxonomy, String>
{
    let rows = classify_rows_at(path, settings, certified)?;
    let started = Instant::now();
    let tax = Taxonomy::from_rows(rows);
    stage("rows indexed", started);
    Ok(tax)
}

fn classify_rows_at(path: &crate::orchestrate::tmpfile::TempPath, settings: &[(&str, &str)], certified: bool)
    -> Result<TaxonomyRows, String>
{
    let started = Instant::now();
    let _trusted = certified.then(|| crate::orchestrate::TrustedRewrite::register(path.path()));
    let _env = FullEnvironment::capture();
    for (key, value) in settings {
        std::env::set_var(key, value);
    }
    let cfg = Config::from_env();
    let result = crate::orchestrate::classify_json(&cfg, path.path());
    stage("pipeline returned", started);
    match result {
        Ok(result) => {
            let rows = result.into_rows();
            stage("pipeline rows", started);
            Ok(rows)
        }
        Err(OrchestrateError::OutOfFragment(e)) => Err(format!("out of fragment: {e}")),
        Err(e) => Err(e.to_string()),
    }
}

impl Session {
    pub fn new() -> Self {
        apply_production_defaults();
        Session { memo: Vec::new(), current: None, revision: 0, clock: 0, validated_new: false }
    }

    /// A source whose outer grammar cannot be inherited gets the ordinary
    /// public validation/classification path and no partial scan certificate.
    /// An error returns before insert/touch, preserving the prior revision.
    fn full_without_reuse(&mut self, text: Arc<String>, started: Instant, reason: &str)
        -> Result<(Arc<Taxonomy>, Receipt), String>
    {
        let text_key = fingerprint(text.as_bytes());
        let tax = Arc::new(classify_text(&text)?);
        let receipt = Receipt { strategy: "full_classify", fallback_reason: Some(reason.to_owned()),
            seconds: started.elapsed().as_secs_f64(), ..Default::default() };
        self.insert(Revision { text, statements: None, text_key, content_key: 0,
            taxonomy: tax.clone(), inconsistency: None, base: None, last_use: 0 });
        Ok((tax, receipt))
    }

    fn touch(&mut self, i: usize) {
        self.clock += 1;
        self.memo[i].last_use = self.clock;
        self.current = Some(i);
    }

    fn insert(&mut self, rev: Revision) -> usize {
        if self.memo.len() >= MEMO_LIMIT {
            // Evict the least recently used revision that is not current.
            if let Some((victim, _)) = self
                .memo
                .iter()
                .enumerate()
                .filter(|(i, _)| Some(*i) != self.current)
                .min_by_key(|(_, r)| r.last_use)
            {
                self.memo.swap_remove(victim);
                if self.current == Some(self.memo.len()) {
                    self.current = Some(victim);
                }
            }
        }
        self.memo.push(rev);
        let i = self.memo.len() - 1;
        self.touch(i);
        i
    }

    /// Classify one complete revision (init or replace).
    fn update(&mut self, text: String) -> Result<(Arc<Taxonomy>, Receipt), String> {
        let started = Instant::now();
        self.validated_new = false;
        let mut preparation = PreparationWork::default();
        preparation.prior_compilers = self.memo.iter().filter_map(|revision|
            revision.base.as_ref().and_then(|base| base.compiler_full.clone())).collect();
        let mut prepared_new = None;
        let mut prepared_admission = None;
        let mut prepared_inconsistency = None;
        let mut prepared_full = None;
        let text: Arc<String> = Arc::new(text);
        let text_key = fingerprint(text.as_bytes());
        if let Some(i) = self.memo.iter().position(|r| r.text_key == text_key && *r.text == *text) {
            let delta = if self.current == Some(i) { Some(StatementDelta::default()) } else {
                self.current.and_then(|old| self.memo[old].statements.as_ref()).and_then(|old| {
                    self.memo[i].statements.as_ref().and_then(|new| statement_delta(old, new))
                })
            };
            self.touch(i);
            let mut receipt = Receipt { strategy: "exact_reuse", reused_complete_answer: true, seconds: started.elapsed().as_secs_f64(), ..Default::default() };
            if let Some(delta) = delta { receipt.apply_delta(delta); }
            return Ok((self.memo[i].taxonomy.clone(), receipt));
        }
        stage("text fingerprint", started);
        let scanned = scan(&text);
        stage("scan", started);
        let Ok(scanned) = scanned else {
            // Not reusable: the pipeline reports the precise source error.
            let tax = Arc::new(classify_text(&text)?);
            let receipt = Receipt { strategy: "full_classify", fallback_reason: scanned.err(), seconds: started.elapsed().as_secs_f64(), ..Default::default() };
            self.insert(Revision { text: text.clone(), statements: None, text_key, content_key: 0, taxonomy: tax.clone(), inconsistency: None, base: None, last_use: 0 });
            return Ok((tax, receipt));
        };
        if !crate::source_reuse_grammar::outer_grammar(&text, &scanned) {
            return self.full_without_reuse(text, started, "unsupported source reuse outer grammar");
        }
        let content_key = scanned.content_key();
        let statements = Arc::new(Statements::of(&scanned, &text));
        stage("statements", started);
        // The statements NEW has beyond the current revision are necessary
        // members of any deletion base: checking them first rejects a base
        // that is not a superset without scanning every statement of NEW.
        let mut added_probe = Vec::new();
        let transaction_delta = self.current.and_then(|i| self.memo[i].statements.as_ref())
            .and_then(|old| statement_delta_probe(old, &statements, Some(&mut added_probe)));
        if added_probe.len() > ADDED_PROBE_MAX { added_probe.clear(); }
        stage("transaction delta", started);
        if let Some(i) = self.memo.iter().position(|r| {
            r.content_key == content_key && r.content_key != 0
                && r.statements.as_ref().is_some_and(|s| s.exact_eq(&statements))
        }) {
            let delta = if self.current == Some(i) { Some(StatementDelta::default()) } else {
                self.current.and_then(|old| self.memo[old].statements.as_ref()).and_then(|old| {
                    self.memo[i].statements.as_ref().and_then(|new| statement_delta(old, new))
                })
            };
            self.touch(i);
            let mut receipt = Receipt { strategy: "exact_reuse", reused_complete_answer: true, seconds: started.elapsed().as_secs_f64(), ..Default::default() };
            if let Some(delta) = delta { receipt.apply_delta(delta); }
            return Ok((self.memo[i].taxonomy.clone(), receipt));
        }
        if let Some((tax, mut receipt, certificate)) = self.inconsistency_reuse(&text, &statements)? {
            receipt.set_transaction_delta(transaction_delta);
            receipt.record_preparation(&preparation);
            receipt.seconds = started.elapsed().as_secs_f64();
            self.insert(Revision { text: text.clone(), statements: Some(statements.clone()),
                text_key, content_key, taxonomy: tax.clone(), inconsistency: Some(certificate),
                base: None, last_use: 0 });
            return Ok((tax, receipt));
        }
        stage("content/inconsistency checks", started);
        let mut fallback_reason = None;
        let deletion_attempt = self.deletion(&text, &scanned, &statements, started, transaction_delta, &added_probe, &mut preparation);
        if std::env::var_os("KM_INCR_TIMING").is_some() {
            if let Err(reason) = &deletion_attempt { stage(&format!("deletion declined: {reason}"), started); }
        }
        stage("deletion attempt finished", started);
        match deletion_attempt {
            Ok(Some((tax, mut receipt, base))) => {
                let tax = Arc::new(tax);
                receipt.set_transaction_delta(transaction_delta);
                receipt.record_preparation(&preparation);
                receipt.seconds = started.elapsed().as_secs_f64();
                let inconsistency = (!tax.consistent).then(||
                    InconsistencyCertificate::from_verified_inconsistent(statements.clone(), None)).flatten();
                self.insert(Revision { text: text.clone(), statements: Some(statements.clone()), text_key, content_key, taxonomy: tax.clone(), inconsistency, base, last_use: 0 });
                return Ok((tax, receipt));
            }
            Ok(None) => {}
            Err(reason) => fallback_reason = Some(reason),
        }
        match self.common_module_update(&text, &scanned, &statements, started, transaction_delta, &mut preparation, &mut prepared_new, &mut prepared_admission, &mut prepared_inconsistency, &mut prepared_full, classify_process_json) {
            Ok(Some((tax, mut receipt, base))) => {
                let tax = Arc::new(tax);
                receipt.set_transaction_delta(transaction_delta);
                receipt.record_preparation(&preparation);
                receipt.seconds = started.elapsed().as_secs_f64();
                let inconsistency = (!tax.consistent).then(||
                    prepared_inconsistency.take().or_else(||
                        InconsistencyCertificate::from_verified_inconsistent(statements.clone(), None))).flatten();
                self.insert(Revision { text: text.clone(), statements: Some(statements.clone()), text_key, content_key, taxonomy: tax.clone(), inconsistency, base, last_use: 0 });
                return Ok((tax, receipt));
            }
            Ok(None) => {},
            Err(reason) => fallback_reason = Some(reason),
        }
        // A nominal common attempt already classifies the complete NEW
        // source. Keep its inconsistent/incomplete answer or error without
        // repeating that native attempt, then use ordinary full finalization.
        let (tax, full_seconds) = match prepared_full {
            Some(answer) => { let (tax, seconds) = answer?; (Arc::new(tax), seconds) },
            None => {
                let full_started = Instant::now();
                let tax = if prepared_admission.is_some() || self.validated_new { classify_text_certified(&text, &[])? }
                    else { classify_text(&text)? };
                (Arc::new(tax), full_started.elapsed().as_secs_f64())
            },
        };
        stage("full classified", started);
        // An inconsistent answer is complete; a consistent one must be.
        let reusable = !tax.consistent || tax.dropped == 0;
        // Retain independently verified support and its exact full index.
        // Small clash proposals avoid repeated minimization when available;
        // eager base preparation shares the index instead of rebuilding it.
        let InconsistencyPreparation { witness, index: witness_index } =
            (!tax.consistent && self.current.is_none() && full_seconds < WITNESS_MAX_SECONDS)
                .then(|| inconsistency_witness(&text, &scanned,
                    WITNESS_BUDGET_FACTOR * full_seconds + 15.0, &mut preparation))
                .unwrap_or_default();
        let inconsistency = (!tax.consistent).then(||
            InconsistencyCertificate::from_verified_inconsistent(statements.clone(), witness.as_deref())).flatten();
        let initial = self.current.is_none();
        let source_bytes = text.len();
        // A consistent complete fallback can keep UNION as a masked semantic
        // index, exactly like common publication. It must never claim an exact
        // source=Some compiler. Inconsistent/incomplete and Exact paths retain
        // the established exact-NEW preparation behavior.
        let masked_base = (tax.consistent && tax.dropped == 0).then(||
            prepared_new.as_ref().and_then(|prepared|
                prepared.consistent_union_base(&text, &scanned, statements.clone()))).flatten();
        let prepared_index = if masked_base.is_some() { None } else {
            witness_index.or_else(|| prepared_new.take().and_then(|prepared|
                prepared.into_exact(&text, &scanned, &mut preparation)))
        };
        stage("full prepared_index", started);
        let prepared_domain = prepared_index.as_ref().map(|index| Arc::new(class_domain(index)));
        let admission = prepared_admission.or_else(||
            (initial && reusable && tax.consistent).then(||
                crate::named_subclass_validation::NamedSubclassCertificate::capture_scanned(text.clone(), &scanned)
                    .map(Arc::new)).flatten());
        let mut base = masked_base.or_else(|| reusable.then(|| BaseState {
            source_bytes,
            anonymous: anonymous_assertions(&text, &scanned),
            statements: statements.clone(),
            source: Some((text.clone(), scanned)),
            index: None,
            compiler_full: prepared_index,
            admission: admission.clone(),
            disabled: Arc::from([]),
            full_disabled: Arc::from([]),
            removed_hashes: Arc::new(FxHashSet::default()),
            class_domain: prepared_domain,
            full: None,
            told: None,
            consistent: tax.consistent,
            witness,
        }));
        if let Some(base) = base.as_mut() { base.admission = admission; }
        stage("full base built", started);
        // Skip it when the classification itself was long: the initial
        // revision must still answer within the caller's per-revision budget.
        if initial && full_seconds < EAGER_INDEX_MAX_SECONDS {
            // The first revision is the base of every later deletion: build
            // its locality index now, so no update pays for it.
            if let Some(b) = base.as_mut() {
                let _ = b.index(&mut preparation);
            }
        }
        self.insert(Revision { text, statements: Some(statements), text_key, content_key, taxonomy: tax.clone(), inconsistency, base, last_use: 0 });
        let mut receipt = Receipt {
            strategy: "full_classify",
            fallback_reason,
            seconds: started.elapsed().as_secs_f64(),
            ..Default::default()
        };
        receipt.set_transaction_delta(transaction_delta);
        receipt.record_preparation(&preparation);
        Ok((tax, receipt))
    }

    /// Retained contradictory support proves a valid stronger revision
    /// inconsistent. Preserve the same Arc, including through memo eviction.
    fn inconsistency_reuse(&self, text: &str, new: &Statements)
        -> Result<Option<(Arc<Taxonomy>, Receipt, Arc<InconsistencyCertificate>)>, String>
    {
        let selected = self.memo.iter().filter(|r| !r.taxonomy.consistent).find_map(|revision| {
            let certificate = revision.inconsistency.as_ref()?;
            certificate.contained_in(new).then_some((revision, certificate))
        });
        let Some((revision, certificate)) = selected else { return Ok(None); };
        // A contradiction does not license invalid new syntax/declarations,
        // unresolved imports, or an invalid anonymous-individual structure.
        // Validate before publication or any mutation of the current revision.
        match crate::frontend::conformance::check_user_source(text) {
            Ok(()) => {},
            Err(crate::frontend::conformance::UserSourceError::Imports) =>
                return Err("unresolved owl:imports in new revision".into()),
            Err(crate::frontend::conformance::UserSourceError::Invalid(error)) => return Err(error),
        }
        Ok(Some((revision.taxonomy.clone(), Receipt {
            strategy: certificate.strategy(), reused_complete_answer: true,
            base_revision_statements: revision.statements.as_ref().map_or(
                certificate.origin_statement_count, |source| source.total),
            ..Default::default()
        }, certificate.clone())))
    }

    /// General edits use a full common-module certificate, never deletion's
    /// monotone row/told shortcuts. The union is analysis input only.
    fn common_module_update(&mut self, text: &str, scanned: &Scan,
        new: &Arc<Statements>, started: Instant, transaction_delta: Option<StatementDelta>,
        work: &mut PreparationWork, prepared_new: &mut Option<PreparedCompiler>,
        prepared_admission: &mut Option<Arc<crate::named_subclass_validation::NamedSubclassCertificate>>,
        prepared_inconsistency: &mut Option<Arc<InconsistencyCertificate>>,
        prepared_full: &mut Option<Result<(Taxonomy, f64), String>>,
        mut verify_support: impl FnMut(&str, std::time::Duration) -> Option<Option<serde_json::Value>>)
        -> Result<Option<(Taxonomy, Receipt, Option<BaseState>)>, String>
    {
        let current = self.current;
        // Preserve max_by_key's last-on-tie rule while confirming only the
        // preferred candidate instead of scanning every older full source.
        let mut candidates: Vec<_> = self.memo.iter().enumerate().filter_map(|(i, r)| {
            (r.taxonomy.consistent && r.taxonomy.dropped == 0 && r.base.is_some()
                && r.statements.is_some()).then_some(i)
        }).collect();
        candidates.sort_unstable_by_key(|&i| std::cmp::Reverse(
            (Some(i) == current, self.memo[i].last_use, i)));
        let selected = candidates.into_iter().find_map(|i| {
            let revision = &self.memo[i];
            let old = revision.statements.as_ref().expect("candidate statements");
            let same_current = Some(i) == current && revision.base.as_ref()
                .is_some_and(|base| Arc::ptr_eq(old, &base.statements));
            let delta = if same_current { transaction_delta } else { statement_delta(old, new) };
            delta.map(|delta| (i, delta))
        });
        let Some((bi, delta)) = selected else {
            return if self.memo.is_empty() { Ok(None) }
                else { Err("no complete consistent base with compatible exact source identities".into()) };
        };
        stage("common base and delta selected", started);
        // A removed declaration or annotation is a fixed origin entry, so the
        // derivation would refuse it after a full pass: skip the pass (the
        // only loss is a certificate that was not available anyway). Java
        // renders drop the declaration of an entity whose last use is deleted.
        let admission = if delta.removed_statements > delta.removed_axioms { None } else {
            self.memo[bi].base.as_ref().and_then(|base| base.admission.as_ref())
                .and_then(|origin| origin.derive_scanned(new.text.clone(), scanned)).map(Arc::new)
        };
        stage("common admission derivation", started);
        // Transaction-local until full or module publication succeeds. Never
        // recapture NEW or install public validation provenance on a decline.
        *prepared_admission = admission.clone();
        let predicted_decline = predicts_empty_module_decline(
            self.memo[bi].base.as_ref().expect("selected complete base"),
            self.memo[bi].statements.as_ref().expect("selected statements"), new, text, scanned);
        stage("common decline predicted", started);
        if admission.is_none() {
            // The predicted decline ends in the ordinary full classification,
            // whose pipeline validates NEW itself and reports its error. Only
            // an addition (independent-support proposal) needs the verdict
            // here, because that proposal must never certify an invalid NEW.
            if predicted_decline && delta.added_axioms == 0 {
                return Err(EARLY_DECLINE_REASON.into());
            }
            match crate::frontend::conformance::check_user_source(text) {
            Ok(()) => self.validated_new = true,
            Err(crate::frontend::conformance::UserSourceError::Imports) =>
                return Err("unresolved owl:imports in new revision".into()),
            Err(crate::frontend::conformance::UserSourceError::Invalid(error)) => return Err(error),
        }
        }
        let certified_new = admission.is_some() || self.validated_new;
        if admission.is_some() { stage("common source validation certificate", started); }
        stage("common source validated", started);
        if predicted_decline {
            // Skip the union-index assembly the full path would repeat, but
            // keep the optional independent-support proposal of that path.
            if delta.added_axioms != 0 {
                if let Some(certificate) = early_object_support_with(new, scanned, &mut verify_support) {
                    let old_total = self.memo[bi].statements.as_ref().expect("selected statements").total;
                    let mut tax = Taxonomy::empty(); tax.consistent = false;
                    let mut receipt = Receipt { strategy: "verified_inconsistency_support",
                        base_revision_statements: old_total, ..Default::default() };
                    receipt.apply_delta(delta);
                    *prepared_inconsistency = Some(certificate);
                    stage("independent object support verified", started);
                    return Ok(Some((tax, receipt, None)));
                }
            }
            return Err(EARLY_DECLINE_REASON.into());
        }
        let base_tax = self.memo[bi].taxonomy.clone();
        let selected_statements = self.memo[bi].statements.as_ref().expect("selected statements").clone();
        let base = self.memo[bi].base.as_mut().expect("selected complete base");
        // This may populate a full compiler alongside a nominal TBox index.
        // Resolve the OLD domain before selecting its compiler donor.
        if base.class_domain.is_none() && base.index(work).is_none() {
            return Err("base locality index unavailable".into());
        }
        let old_domain = base.class_domain.as_ref().expect("indexed class domain").clone();
        let old = base.statements.clone();
        let previous = base.compiler_full.clone();
        let previous_told = base.told.clone();
        let mut cached_tbox = None;
        if let Some((prepared, tbox)) = base.exact_union_pair(&selected_statements, new) {
            // Both immutable indexes describe exact OLD. For this deletion
            // OLD union NEW is OLD; keep its original source spans as well.
            *prepared_new = Some(prepared);
            cached_tbox = Some(tbox);
        } else if old.confirms_subset(new) {
            // For an exact addition, the union is NEW. Keep the established
            // one-build path and its exact source provenance.
            let index = Arc::new(match previous {
                Some(donor) => work.build_reusing_full(text, scanned, &donor,
                    old.header(), |hash| old.stmt(&hash))?,
                None => work.build_index(text, scanned, false)?,
            });
            *prepared_new = Some(PreparedCompiler::Exact(index));
        } else {
            let mut union = String::from(old.header());
            union.push('\n');
            let mut emitted = FxHashSet::default();
            for statements in [old.as_ref(), new.as_ref()] {
                let mut ordered: Vec<_> = statements.counts.iter().collect();
                ordered.sort_unstable_by_key(|(_, entry)| entry.2);
                for (hash, _) in ordered {
                    if emitted.insert(*hash) {
                        union.push_str(statements.stmt(hash).expect("statement span"));
                        union.push('\n');
                    }
                }
            }
            union.push_str(")\n");
            let union = Arc::new(union);
            let union_scan = scan(&union)?;
            // Candidate statement_delta checked both collision flags and
            // every shared hash's exact text. Deduplication cannot merge
            // distinct statements when constructing this union.
            let index = Arc::new(match previous {
                // The donor can contain historical disabled formulas. Only
                // OLD's exact enabled statement lookup licenses compilation
                // reuse; raw donor hash membership is never sufficient.
                Some(donor) => work.build_reusing_full(&union, &union_scan, &donor,
                    old.header(), |hash| old.stmt(&hash))?,
                None => work.build_index(&union, &union_scan, false)?,
            });
            *prepared_new = Some(PreparedCompiler::Union {
                source: union, scan: union_scan, index,
            });
        }
        stage("common index built", started);
        let prepared = prepared_new.as_ref().expect("completed union preparation");
        let union_index = prepared.index().clone();
        let union_scan = prepared.scan(scanned);
        if union_index.spelling_conflict { return Err("union has conflicting entity spellings".into()); }
        // A full union's aggregate Class bits include removed OLD uses.
        // Recompute NEW's exact enabled contributions and referenced builtin
        // spellings. A fresh exact index remains the cheaper addition case.
        let new_domain = Arc::new(match prepared {
            PreparedCompiler::Exact(index) => class_domain(index),
            PreparedCompiler::Union { .. } => {
                let names = union_index.live_public_class_names(|hash| new.counts.contains_key(&hash))
                    .ok_or("union compiler does not retain all assertions")?;
                let mut domain: FxHashSet<Box<str>> = names.into_iter().map(Box::from).collect();
                domain.extend(["owl:Thing", "owl:Nothing", "http://www.w3.org/2002/07/owl#Thing",
                    "http://www.w3.org/2002/07/owl#Nothing"].into_iter().map(Box::<str>::from));
                domain
            }
        });
        stage("common new_domain", started);
        let mut marked = vec![false; union_index.axiom_count()];
        let mut disabled = vec![false; union_index.axiom_count()];
        for (id, hash) in union_index.axiom_hash.iter().enumerate() {
            let was = old.counts.contains_key(hash);
            let now = new.counts.contains_key(hash);
            marked[id] = was != now;
            disabled[id] = !now;
        }
        // A resolved-source positive object certificate supplies a model of
        // the whole union, hence of both actual revision subsets. Its ABox
        // cannot change named-class entailments (positive_tbox_named_query).
        // These masks are analysis-only: the saved BaseState below must still
        // describe the complete NEW source, including its assertions.
        let mut analysis_disabled = vec![false; union_index.axiom_count()];
        if union_index.positive_object_source {
            for statement in &union_scan.statements {
                if statement.kind == StmtKind::Assertion {
                    if let Some(&id) = union_index.axiom_by_hash.get(&statement.hash) {
                        analysis_disabled[id as usize] = true;
                    }
                }
            }
        }
        stage("common masks", started);
        let projects_abox = analysis_disabled.iter().any(|disabled| *disabled);
        let module_disabled: Vec<bool> = disabled.iter().zip(&analysis_disabled)
            .map(|(absent, assertion)| *absent || *assertion).collect();
        // Without the positive certificate this is the original full-union
        // consistency transfer. With it, locality is over the exact TBox
        // union and both complete sources have independent positive models.
        if !union_index.empty_module_avoids_with_disabled(&marked, &analysis_disabled) {
            // Healthy common updates pay no optional proposal cost. A dirty
            // full core already requires a consistency decision; additions
            // may have introduced a small independently checkable clash.
            if delta.added_axioms != 0 {
                if let Some(certificate) = early_object_support_with(new, scanned, &mut verify_support) {
                    let mut tax = Taxonomy::empty(); tax.consistent = false;
                    let mut receipt = Receipt { strategy: "verified_inconsistency_support",
                        base_revision_statements: old.total, ..Default::default() };
                    receipt.apply_delta(delta);
                    *prepared_inconsistency = Some(certificate);
                    stage("independent object support verified", started);
                    return Ok(Some((tax, receipt, None)));
                }
            }
            return common_nominal_update(text, scanned, new, &old, &base_tax,
                &old_domain, new_domain, prepared, cached_tbox.as_ref(), admission, certified_new, delta, work,
                prepared_full, started, false);
        }
        stage("common empty_module_avoids", started);
        // Prefer a certified pure-object NEW module when the full common
        // core carries data assertions or a substantial assertion payload.
        // Even a small data core can expand heavily in the backend. Positive
        // projection already removes its payload without a second TBox index.
        let mut preference_reason = None;
        let is_data_assertion = |statement: &crate::source_locality::Stmt| {
            statement.kind == StmtKind::Assertion && matches!(
                crate::frontend::sexpr::tokens(
                    &prepared.text(text)[statement.start..statement.end]).next(),
                Some("DataPropertyAssertion" | "NegativeDataPropertyAssertion"))
        };
        if !projects_abox && (union_scan.statements.iter().any(&is_data_assertion)
            || union_scan.statements.iter()
                .filter(|s| s.kind == StmtKind::Assertion)
                .take(MODULE_RESTRICT_MIN_AXIOMS).count() >= MODULE_RESTRICT_MIN_AXIOMS) {
            let core: FxHashSet<_> = union_index.empty_module_statements().into_iter().collect();
            let assertions: FxHashSet<_> = union_scan.statements.iter()
                .filter(|s| s.kind == StmtKind::Assertion && core.contains(&s.hash))
                .map(|s| s.hash).collect();
            if assertions.len() >= MODULE_RESTRICT_MIN_AXIOMS
                || union_scan.statements.iter().any(|s|
                    assertions.contains(&s.hash) && is_data_assertion(s)) {
                match common_nominal_update(text, scanned, new, &old, &base_tax,
                    &old_domain, new_domain.clone(), prepared, cached_tbox.as_ref(), admission.clone(), certified_new, delta, work,
                    prepared_full, started, true) {
                    Ok(Some(answer)) => return Ok(Some(answer)),
                    Ok(None) => {},
                    Err(error) if prepared_full.is_some() => return Err(error),
                    Err(error) => preference_reason = Some(error),
                }
            }
        }
        stage("common preference done", started);
        let Some(affected) = union_index.affected_classes_with_disabled(&marked, &analysis_disabled) else {
            return Err("union affected-subject certificate unavailable".into());
        };
        let mut wanted: BTreeSet<u32> = affected.into_iter().filter(|&id| {
            new_domain.contains(&*union_index.names[id as usize])
        }).collect();
        for name in new_domain.difference(&old_domain) {
            if let Some(id) = union_index.named(name) { wanted.insert(id); }
            else if !is_builtin_class_name(name) { return Err("new public class missing from union index".into()); }
        }
        stage("common affected computed", started);
        let relevant: Vec<u32> = wanted.into_iter().collect();
        let names: Vec<&str> = relevant.iter().map(|&id| &*union_index.names[id as usize]).collect();
        let mut receipt = Receipt {
            strategy: if projects_abox { "positive_abox_module_reuse" } else { "common_module_reuse" },
            base_revision_statements: old.total,
            affected_subjects: relevant.len(),
            reclassified_subjects: relevant.len(),
            index_axioms: union_index.axiom_count(),
            ..Default::default()
        };
        receipt.apply_delta(delta);
        receipt.fallback_reason = preference_reason;
        stage("common indexes and affected", started);
        let mut tax = (*base_tax).clone();
        tax.rendered = std::sync::OnceLock::new();
        let mut modified = prune_public_domain(&mut tax, &new_domain);
        modified.extend(names.iter().map(|name| Box::<str>::from(*name)));
        if !relevant.is_empty() {
            let (module, signature) = union_index.module(&relevant, &module_disabled);
            stage("common module extracted", started);
            receipt.module_axioms = module.len();
            let module_tax = if module.is_empty() { Taxonomy::empty() } else {
                // Stream the NEW-source module straight into the pipeline's
                // input file: the module covers most of a large ABox-dominated
                // source, so a String copy would be a second source-sized
                // buffer plus a second write.
                let module_file = crate::orchestrate::tmpfile::TempPath::new(".ofn");
                {
                    use std::io::Write;
                    let io = |e: std::io::Error| e.to_string();
                    let in_module: FxHashSet<u32> = module.iter().copied().collect();
                    let mut emitted = FxHashSet::default();
                    let mut out = std::io::BufWriter::with_capacity(1 << 20,
                        std::fs::File::create(module_file.path()).map_err(io)?);
                    out.write_all(new.header().as_bytes()).map_err(io)?;
                    out.write_all(b"\n").map_err(io)?;
                    for statement in &scanned.statements {
                        let keep = match statement.kind {
                            StmtKind::Declaration => union_index.decl_entity.get(&statement.hash)
                                .is_some_and(|&id| signature[id as usize]),
                            StmtKind::Logical | StmtKind::Assertion => union_index.axiom_by_hash.get(&statement.hash)
                                .is_some_and(|id| in_module.contains(id)),
                            StmtKind::Annotation | StmtKind::Import => false,
                        };
                        if keep && emitted.insert(statement.hash) {
                            out.write_all(text[statement.start..statement.end].as_bytes()).map_err(io)?;
                            out.write_all(b"\n").map_err(io)?;
                        }
                    }
                    out.write_all(b")\n").map_err(io)?;
                    out.flush().map_err(io)?;
                }
                stage("common new-source module emitted", started);
                let file = (module.len() >= MODULE_RESTRICT_MIN_AXIOMS)
                    .then(|| crate::orchestrate::tmpfile::TempPath::new("-common-subjects.json"));
                let mut settings = Vec::new();
                if text.len() >= INPROC_SIZE_GATE {
                    settings.extend([("KM_NO_INPROC_ENGINE", "1"), ("KM_NO_INPROC_HT", "1")]);
                }
                let path;
                if let Some(file) = &file {
                    std::fs::write(file.path(), serde_json::to_vec(&names).map_err(|e| e.to_string())?)
                        .map_err(|e| e.to_string())?;
                    path = file.path().to_string_lossy().into_owned();
                    settings.push(("KM_PUBLIC_SUBJECT_IRIS_FILE", path.as_str()));
                }
                classify_taxonomy_at(&module_file, &settings, admission.is_some())
                    .map_err(|e| format!("common module classification: {e}"))?
            };
            if !module_tax.consistent || module_tax.dropped != 0 {
                return Err("common module classification was not complete and consistent".into());
            }
            replace_rows(&mut tax, &module_tax, &names);
            // Module targets outside the NEW public signature never escape.
            modified.extend(prune_public_domain(&mut tax, &new_domain));
        }
        receipt.reused_subjects = retained_subject_count(&base_tax, modified.iter().map(|n| &**n));
        let removed_hashes = union_index.axiom_hash.iter().filter(|h| !new.counts.contains_key(*h)).copied().collect();
        let next = BaseState {
            statements: new.clone(), source: None, index: Some(Some(union_index.clone())),
            admission,
            compiler_full: Some(union_index),
            disabled: disabled.into(), full_disabled: Arc::from([]),
            removed_hashes: Arc::new(removed_hashes), class_domain: Some(new_domain),
            full: None, told: Some(Arc::new(RetainedTold::prepare(text, scanned, new.clone(), previous_told.as_deref()))),
            consistent: true, witness: None,
            anonymous: anonymous_assertions(text, scanned), source_bytes: text.len(),
        };
        stage("common module classified and merged", started);
        Ok(Some((tax, receipt, Some(next))))
    }

    /// Deletion reuse against the closest stored superset revision.
    /// `Ok(None)`: no applicable base. `Err`: a base applied but reuse declined.
    fn deletion(&mut self, text: &str, scanned: &Scan, new: &Arc<Statements>, started: Instant,
        transaction_delta: Option<StatementDelta>, added_probe: &[u128], work: &mut PreparationWork)
        -> Result<Option<(Taxonomy, Receipt, Option<BaseState>)>, String>
    {
        // A base: consistent, complete, same header, statement superset,
        // and every removed statement a logical axiom or an annotation.
        let mut candidates: Vec<_> = self.memo.iter().enumerate().filter_map(|(i, r)| {
            let old = &r.base.as_ref()?.statements;
            (old.header_hash == new.header_hash && old.total >= new.total)
                .then(|| (old.total - new.total, i))
        }).collect();
        // The old scan kept the first eligible candidate at each minimum
        // distance. Sorting distance then original index preserves that rule.
        candidates.sort_unstable();
        let best = candidates.into_iter().find_map(|(_, i)| {
            let old = &self.memo[i].base.as_ref().expect("candidate base").statements;
            if added_probe.iter().any(|hash| !old.counts.contains_key(hash)) { return None; }
            let subset = new.counts.iter().all(|(h, (n, ..))| {
                old.counts.get(h).is_some_and(|(m, ..)| m >= n)
            });
            if !subset { return None; }
            let removed_ok = old.counts.iter().all(|(h, (m, kind, ..))| {
                let kept = new.counts.get(h).map_or(0, |(n, ..)| *n);
                kept == *m || kept > 0 || matches!(kind, StmtKind::Logical | StmtKind::Assertion | StmtKind::Annotation)
            });
            (removed_ok && new.confirms_subset(old)).then_some(i)
        });
        let Some(bi) = best else { return Ok(None) };
        // The revision is not validated again: deleting statements keeps
        // every OWL 2 DL and KM source restriction, except the
        // anonymous-individual forest condition, which a deleted property
        // assertion can split into an invalid tree. Validate those fully.
        if self.memo[bi].base.as_ref().is_some_and(|b| {
            b.anonymous.iter().any(|h| !new.counts.contains_key(h))
        }) {
            return Err("a deleted property assertion mentions an anonymous individual".into());
        }

        let base_tax = self.memo[bi].taxonomy.clone();
        let same_current = self.current == Some(bi) && self.memo[bi].statements.as_ref()
            .is_some_and(|old| Arc::ptr_eq(old, &self.memo[bi].base.as_ref().expect("base state").statements));
        let base = self.memo[bi].base.as_mut().expect("base state");
        let source_delta = if same_current { transaction_delta.expect("confirmed current deletion") }
            else { statement_delta(&base.statements, new).expect("confirmed exact deletion") };
        if !base.consistent {
            // Deletion keeps an inconsistent subset: the stored verified
            // witness, or the module of the empty signature.
            if let Some(w) = &base.witness {
                if w.iter().all(|h| new.counts.contains_key(h)) {
                    let mut receipt = Receipt { strategy: "inconsistency_witness_reuse", reused_complete_answer: true, base_revision_statements: base.statements.total, ..Default::default() };
                    receipt.apply_delta(source_delta);
                    return Ok(Some(((*base_tax).clone(), receipt, None)));
                }
            }
            let removed: Vec<u128> = base.statements.counts.keys().filter(|h| !new.counts.contains_key(*h)).copied().collect();
            let Some(index) = base.index(work) else { return Err("locality index unavailable".into()) };
            let mut marked = vec![false; index.axiom_count()];
            for h in &removed {
                if let Some(&a) = index.axiom_by_hash.get(h) {
                    marked[a as usize] = true;
                }
            }
            if index.empty_module_avoids(&marked) {
                let mut receipt = Receipt { strategy: "inconsistency_module_reuse", reused_complete_answer: true, index_axioms: index.axiom_count(), ..Default::default() };
                receipt.apply_delta(source_delta);
                return Ok(Some(((*base_tax).clone(), receipt, None)));
            }
            return Err("a deleted axiom is in the inconsistent module of the empty signature".into());
        }
        let removed: Vec<u128> = base
            .statements
            .counts
            .iter()
            .filter(|(h, _)| !new.counts.contains_key(*h))
            .map(|(h, _)| *h)
            .collect();
        let base_statements = base.statements.total;
        // The complete revision was above the pipeline's in-process size gate,
        // so it never ran the budgeted in-process CB attempt. Keep those
        // worker boundaries for its module, including HT: a smaller module
        // must not introduce an in-process attempt absent from the source's
        // schedule. The CB attempt can spend its whole budget on
        // a small non-EL module that the HT race answers in a fraction of it.
        let module_settings: &[(&str, &str)] = if base.source_bytes >= INPROC_SIZE_GATE {
            &[("KM_NO_INPROC_ENGINE", "1"), ("KM_NO_INPROC_HT", "1")]
        } else {
            &[]
        };
        let annotations: FxHashSet<u128> = removed
            .iter()
            .filter(|h| base.statements.counts.get(*h).is_some_and(|(_, k, ..)| *k == StmtKind::Annotation))
            .copied()
            .collect();
        let index_was_ready = base.index.as_ref().is_some_and(|i| i.is_some());
        if base.index(work).is_none() {
            return Err("locality index unavailable".into());
        }
        let mut retained_base = base.after_deletion(new.clone(), &removed);
        let mark = |index: &LocalityIndex| -> Result<(Vec<bool>, usize), String> {
            let mut marked = vec![false; index.axiom_count()];
            let mut removed_axioms = 0;
            for h in &removed {
                if let Some(&a) = index.axiom_by_hash.get(h) {
                    marked[a as usize] = true;
                    removed_axioms += 1;
                } else if !index.assertions.contains(h) {
                    // Annotation-only statements carry no logical content; any
                    // other removed statement must be a known axiom.
                    if !annotations.contains(h) {
                        return Err("removed statement outside the locality index".into());
                    }
                }
            }
            Ok((marked, removed_axioms))
        };
        let tbox_index = base.index.as_ref().and_then(|i| i.as_ref()).expect("index built");
        // Prefer the full index when its empty-signature module avoids the
        // removed statements (no nominal axiom then forces any subject).
        let full_choice = base.full.as_ref().and_then(|full| {
            let (marked, removed_axioms) = mark(full).ok()?;
            full.empty_module_avoids_with_disabled(&marked, &base.full_disabled)
                .then_some((full.as_ref(), &*base.full_disabled, marked, removed_axioms))
        });
        let (index, old_disabled, marked, _removed_index_axioms) = match full_choice {
            Some(choice) => choice,
            None => {
                let (marked, removed_axioms) = mark(tbox_index)?;
                (tbox_index.as_ref(), &*base.disabled, marked, removed_axioms)
            }
        };
        let mut receipt = Receipt {
            strategy: "module_reuse",
            base_revision_statements: base_statements,
            index_axioms: index.axiom_count(),
            reused_index_axioms: if index_was_ready { index.axiom_count() } else { 0 },
            ..Default::default()
        };
        receipt.apply_delta(source_delta);
        if index.spelling_conflict {
            return Err("an entity has two source spellings".into());
        }
        // Every published subject must be a class symbol of the index, or a
        // subject could be skipped by name mismatch.
        let uncovered = base_tax.ids.iter().find(|(iri, &id)| {
            let subject = base_tax.rows[id as usize].is_some() || base_tax.unsat.contains(&id);
            subject && !index.named(iri).is_some_and(|s| index.is_class[s as usize])
        });
        if let Some((iri, _)) = uncovered {
            return Err(format!("published subject {iri} is not a class of the locality index"));
        }
        stage("base and index", started);
        // TBox mode reads nominals as empty: a class is unaffected only if
        // its module avoids the removed axioms and mentions no nominal.
        let (affected, global_deletion, globals) = match
            index.affected_classes_tbox_with_disabled(&marked, old_disabled)
        {
            Some(affected) => (affected, false, Vec::new()),
            None => {
                let decline = "a removed or nominal axiom is in the module of the empty signature";
                // The bounded NEW-only collector may decline before any OLD
                // scan or complete shape pass, especially for large sources.
                let globals = crate::incr_global::global_named_classes(text, scanned)
                    .ok_or_else(|| decline.to_string())?;
                if base.statements.text.len() > 4 << 20 { return Err(decline.into()); }
                // Bind both complete theories to the augmented object/data
                // model. This supplies no locality or admission certificate.
                let old_scan = scan(&base.statements.text).map_err(|_| decline.to_string())?;
                if crate::incr_envelope::eligible(&base.statements.text, &old_scan).is_none()
                    || crate::incr_envelope::eligible(text, scanned).is_none()
                { return Err(decline.into()); }
                // The previous global refusal reached common NEW validation.
                // Preserve it: arbitrary deletion is not admission-monotone.
                let admission = base.admission.as_ref().and_then(|origin|
                    origin.derive_scanned(new.text.clone(), scanned)).map(Arc::new);
                if admission.is_none() {
                    match crate::frontend::conformance::check_user_source(text) {
                        Ok(()) => {},
                        Err(crate::frontend::conformance::UserSourceError::Imports) =>
                            return Err("unresolved owl:imports in new revision".into()),
                        Err(crate::frontend::conformance::UserSourceError::Invalid(error)) => return Err(error),
                    }
                }
                if let Some(admission) = admission { retained_base.admission = Some(admission); }
                // Derived seeds belong only to this exact NEW call. Neither
                // the retained graph nor its original statement tags change.
                let affected = index.is_class.iter().enumerate()
                    .filter_map(|(id, class)| class.then_some(id as u32)).collect();
                (affected, true, globals)
            },
        };
        receipt.affected_subjects = affected.len();
        // Deletion from a consistent ontology only removes consequences: a
        // subject with no superclass that was satisfiable keeps that answer.
        let relevant: Vec<u32> = affected
            .into_iter()
            .filter(|&s| {
                let iri = &*index.names[s as usize];
                base_tax.ids.get(iri).is_some_and(|&id| {
                    base_tax.rows[id as usize].is_some() || base_tax.unsat.contains(&id)
                })
            })
            .collect();
        // Told proofs (IncrementalModuleReuse.told_row_exact): a satisfiable
        // subject whose whole base row is proved syntactically in the revision
        // keeps that row, since deletion only removes consequences.
        let relevant: Vec<u32> = if relevant.is_empty() {
            relevant
        } else {
            let removed_set = &*retained_base.removed_hashes;
            let built;
            let proofs = match base.told.as_ref().filter(|_| !global_deletion) {
                Some(p) => &p.proofs,
                None => {
                    built = crate::source_locality::ToldProofs::build(text, scanned);
                    &built
                }
            };
            let before = relevant.len();
            let kept: Vec<u32> = relevant
                .into_iter()
                .filter(|&s| {
                    let iri = &*index.names[s as usize];
                    let Some(&id) = base_tax.ids.get(iri) else { return true };
                    if base_tax.unsat.contains(&id) {
                        return true;
                    }
                    let Some(row) = &base_tax.rows[id as usize] else { return true };
                    let supers: Vec<&str> = row.iter().map(|&o| &*base_tax.iris[o as usize]).collect();
                    !proofs.proves_all_with_globals(iri, &supers, removed_set, &globals)
                })
                .collect();
            receipt.told_subjects = before - kept.len();
            kept
        };
        stage("told proofs", started);
        receipt.reclassified_subjects = relevant.len();
        stage("affected", started);
        if global_deletion {
            if receipt.told_subjects == 0 {
                return Err("no exact told rows survived the global deletion".into());
            }
            // No locality claim survives global refusal. Even an empty
            // remaining request runs full NEW's actual consistency check.
            let names: Vec<String> = relevant.iter().map(|&s| index.names[s as usize].to_string()).collect();
            stage("global deletion told rows", started);
            return restricted_complete(text, &names, &base_tax, receipt, started)
                .map(|(tax, receipt)| Some((tax, receipt, Some(retained_base))));
        }
        let mut tax = (*base_tax).clone();
        tax.rendered = std::sync::OnceLock::new();
        if !relevant.is_empty() {
            let disabled: Vec<bool> = old_disabled.iter().zip(&marked).map(|(old, new)| *old || *new).collect();
            let (module, signature) = index.module(&relevant, &disabled);
            receipt.module_axioms = module.len();
            // A TBox-mode module with a nominal axiom is not a module of the
            // revision: classify the complete revision with the bridge's
            // subject probes restricted to the relevant subjects.
            // KM_INCR_LARGE_MODULE_FULL=1 restores the former rule that also
            // sent modules holding most of a non-EL revision there (on the
            // current pipeline the module is faster: 9724 rev3, 72 % of the
            // axioms, about 0.64x the complete revision).
            let nominal = index.tbox_mode && index.module_has_nominal(&module);
            let large = std::env::var_os("KM_INCR_LARGE_MODULE_FULL").is_some()
                && module.len() * 2 > index.axiom_count() && index.axiom_count() > 2000 && !index.el_like;
            if nominal || large {
                let names: Vec<String> = relevant.iter().map(|&s| index.names[s as usize].to_string()).collect();
                return restricted_complete(text, &names, &base_tax, receipt, started)
                    .map(|(tax, receipt)| Some((tax, receipt, Some(retained_base))));
            }
            let in_module: FxHashSet<u32> = module.iter().copied().collect();
            let mut out = String::with_capacity(scanned.open_end + 256 * (module.len() + 16));
            out.push_str(&text[..scanned.open_end]);
            out.push('\n');
            let mut emitted: FxHashSet<u128> = FxHashSet::default();
            for st in &scanned.statements {
                let keep = match st.kind {
                    StmtKind::Declaration => index
                        .decl_entity
                        .get(&st.hash)
                        .is_some_and(|&e| signature[e as usize]),
                    StmtKind::Logical | StmtKind::Assertion => index
                        .axiom_by_hash
                        .get(&st.hash)
                        .is_some_and(|a| in_module.contains(a)),
                    StmtKind::Annotation | StmtKind::Import => false,
                };
                if keep && emitted.insert(st.hash) {
                    out.push_str(&text[st.start..st.end]);
                    out.push('\n');
                }
            }
            out.push_str(")\n");
            if let Some(path) = std::env::var_os("KM_INCR_DEBUG_MODULE") {
                let _ = std::fs::write(&path, &out);
                let names: Vec<&str> = relevant.iter().map(|&s| &*index.names[s as usize]).collect();
                let _ = std::fs::write(format!("{}.subjects.json", path.to_string_lossy()), serde_json::to_vec(&names).unwrap_or_default());
                eprintln!("KM_INCR relevant={}", names.len());
            }
            stage("module text", started);
            // An empty module entails only trivial subsumptions: every
            // relevant subject is satisfiable with no named superclass.
            let module_tax = if module.is_empty() {
                Taxonomy::empty()
            } else {
                // Only the relevant subjects' rows are used: restrict the
                // bridge's subject probes to them (other routes ignore it).
                // A small module skips the restriction: its two extra
                // temporary files cost more than the probes they save.
                let names: Vec<&str> = relevant.iter().map(|&s| &*index.names[s as usize]).collect();
                let file = (module.len() >= MODULE_RESTRICT_MIN_AXIOMS)
                    .then(|| crate::orchestrate::tmpfile::TempPath::new("-module-subjects.json"));
                let mut settings: Vec<(&str, &str)> = module_settings.to_vec();
                let path;
                if let Some(file) = &file {
                    std::fs::write(file.path(), serde_json::to_vec(&names).map_err(|e| e.to_string())?)
                        .map_err(|e| e.to_string())?;
                    path = file.path().to_string_lossy().into_owned();
                    settings.push(("KM_PUBLIC_SUBJECT_IRIS_FILE", path.as_str()));
                }
                classify_text_with(&out, &settings).map_err(|e| format!("module classification: {e}"))?
            };
            if !module_tax.consistent || module_tax.dropped != 0 {
                return Err("module classification was not complete and consistent".into());
            }
            let names: Vec<&str> = relevant.iter().map(|&s| &*index.names[s as usize]).collect();
            replace_rows(&mut tax, &module_tax, &names);
        }
        stage("module classified and merged", started);
        receipt.reused_subjects = retained_subject_count(&base_tax, relevant.iter().map(|&s| &*index.names[s as usize]));
        Ok(Some((tax, receipt, Some(retained_base))))
    }
}

/// Dirty data owners are included even when unchanged. Thus every retained
/// module is object-only, including when a data-property IRI is punned as Class.
fn nominal_common_subjects(index: &LocalityIndex, old: &Statements, new: &Statements,
    old_domain: &FxHashSet<Box<str>>, new_domain: &FxHashSet<Box<str>>,
    data_tbox: &FxHashSet<u128>) -> Option<Vec<String>>
{
    if !index.tbox_mode || index.spelling_conflict { return None; }
    let marked: Vec<_> = index.axiom_hash.iter().map(|hash|
        old.counts.contains_key(hash) != new.counts.contains_key(hash)
            || data_tbox.contains(hash)).collect();
    // This API also marks every nominal owner, without treating nominal
    // emptiness as an assertion about actual NEW consistency.
    let affected = index.affected_classes_tbox(&marked)?;
    let mut names: BTreeSet<String> = affected.into_iter().map(|id|
        index.names[id as usize].to_string()).filter(|name| new_domain.contains(name.as_str())).collect();
    names.extend(new_domain.difference(old_domain).map(|name| name.to_string()));
    names.extend(new_domain.iter().filter(|name|
        !index.named(name).is_some_and(|id| index.is_class[id as usize])).map(|name| name.to_string()));
    Some(names.into_iter().collect())
}

/// Emit only the actual NEW nominal-free object module. Always retain the
/// empty-signature core, and declare every requested class even if it occurs
/// only in NEW assertions and has no TBox symbol or emitted declaration.
fn object_common_module(text: &str, scanned: &Scan, old: &Statements, new: &Statements,
    full: &LocalityIndex, tbox: &LocalityIndex, names: &[String],
    eligible: &crate::incr_envelope::Eligibility) -> Option<(String, usize)>
{
    if !full.full_mode || !tbox.tbox_mode { return None; }
    let added: Vec<_> = full.axiom_hash.iter().map(|hash| !old.counts.contains_key(hash)).collect();
    // The union's full empty module need only be contained in OLD. It may
    // contain removed OLD assertions; NEW consistency follows by subset.
    if !full.empty_module_avoids(&added) { return None; }
    let disabled: Vec<_> = tbox.axiom_hash.iter().map(|hash| !new.counts.contains_key(hash)).collect();
    let seeds: Vec<_> = names.iter().filter_map(|name| tbox.named(name)).collect();
    let (module, signature) = tbox.module(&seeds, &disabled);
    if tbox.module_has_nominal(&module) || module.iter().any(|id|
        eligible.data_tbox.contains(&tbox.axiom_hash[*id as usize])) { return None; }
    let members: FxHashSet<_> = module.iter().copied().collect();
    let mut output = String::from(new.header()); output.push('\n');
    let mut emitted = FxHashSet::default();
    let mut declared = FxHashSet::default();
    let wanted: FxHashSet<&str> = names.iter().map(String::as_str).collect();
    let mut spellings = FxHashMap::default();
    for statement in &scanned.statements {
        let slice = text.get(statement.start..statement.end)?;
        // Recover actual source token spellings instead of guessing whether
        // a published name was a prefixed token or a bracketed full IRI.
        for token in crate::frontend::sexpr::tokens(slice) {
            let name = token.strip_prefix('<').and_then(|t|t.strip_suffix('>')).unwrap_or(token);
            if wanted.contains(name) { spellings.entry(name).or_insert(token); }
        }
        let keep = match statement.kind {
            StmtKind::Declaration => tbox.decl_entity.get(&statement.hash)
                .is_some_and(|id| signature[*id as usize]),
            StmtKind::Logical => tbox.axiom_by_hash.get(&statement.hash)
                .is_some_and(|id| members.contains(id)),
            _ => false,
        };
        if keep && emitted.insert(statement.hash) {
            output.push_str(slice); output.push('\n');
            if statement.kind == StmtKind::Declaration {
                if let Ok(crate::frontend::sexpr::Node::List("Declaration", args)) =
                    crate::frontend::sexpr::Parser::new(slice).parse()
                {
                    for node in args {
                        if let crate::frontend::sexpr::Node::List("Class", names) = node {
                            if let [crate::frontend::sexpr::Node::Atom(token)] = names.as_slice() {
                                declared.insert(token.strip_prefix('<').and_then(|s|s.strip_suffix('>')).unwrap_or(token).to_string());
                            }
                        }
                    }
                }
            }
        }
    }
    for name in names {
        if declared.contains(name) { continue; }
        let token = spellings.get(name.as_str()).copied().or_else(|| match name.as_str() {
            "owl:Thing" => Some("owl:Thing"), "owl:Nothing" => Some("owl:Nothing"),
            "http://www.w3.org/2002/07/owl#Thing" => Some("<http://www.w3.org/2002/07/owl#Thing>"),
            "http://www.w3.org/2002/07/owl#Nothing" => Some("<http://www.w3.org/2002/07/owl#Nothing>"),
            _ => None,
        })?;
        output.push_str("Declaration(Class("); output.push_str(token); output.push_str("))\n");
    }
    output.push_str(")\n");
    Some((output, module.len()))
}

const EARLY_DECLINE_REASON: &str = "early_decline_empty_signature_module";

/// Cheap, conservative prediction that the common path would decline with
/// "changed axiom belongs to the union empty-signature module" after building
/// the union index. It fires only when the retained full compiler of the base
/// says the source is outside the positive-object projection (assertions stay
/// in every module), the edit adds or removes an assertion, and NEW is not
/// eligible for the nominal common route. A wrong prediction only forgoes
/// reuse: the full classification it falls back to is always sound.
fn predicts_empty_module_decline(base: &BaseState, old: &Statements, new: &Statements,
    text: &str, scanned: &Scan) -> bool
{
    // A retained full compiler decides exactly. Without one (an init that
    // kept only the TBox index) the TBox build's conservative witness is
    // enough: it is set only for an axiom or skipped assertion statement the
    // full compiler would also refuse, so it implies !positive_object_source.
    let outside_positive = match base.compiler_full.as_ref() {
        Some(full) => full.full_mode && !full.positive_object_source,
        None => base.index.as_ref().and_then(|index| index.as_ref())
            .is_some_and(|index| index.outside_positive_object),
    };
    if !outside_positive { return false; }
    let touches = |a: &Statements, b: &Statements| a.counts.iter()
        .any(|(hash, (_, kind, ..))| *kind == StmtKind::Assertion && !b.counts.contains_key(hash));
    (touches(new, old) || touches(old, new)) && crate::incr_envelope::eligible(text, scanned).is_none()
}

/// Both actual revisions need models. The guarded augmented empty-core
/// certificate derives NEW consistency; otherwise classify full NEW, unless
/// this is an optional module-only preference over the existing common path.
fn common_nominal_update(text: &str, scanned: &Scan, new: &Arc<Statements>, old: &Statements,
    base_tax: &Taxonomy, old_domain: &FxHashSet<Box<str>>,
    new_domain: Arc<FxHashSet<Box<str>>>, prepared: &PreparedCompiler,
    cached_tbox: Option<&Arc<LocalityIndex>>,
    admission: Option<Arc<crate::named_subclass_validation::NamedSubclassCertificate>>,
    certified_new: bool,
    delta: StatementDelta, work: &mut PreparationWork,
    prepared_full: &mut Option<Result<(Taxonomy, f64), String>>, started: Instant, module_only: bool)
    -> Result<Option<(Taxonomy, Receipt, Option<BaseState>)>, String>
{
    let decline = "changed axiom belongs to the union empty-signature module";
    if !prepared.index().full_mode { return Err(decline.into()); }
    let union_text = prepared.text(text);
    let union_scan = prepared.scan(scanned);
    // The ordinary positive, assertion-free path already has a cheap exact
    // common analysis; optional nominal preparation cannot improve it.
    if prepared.index().positive_object_source && !union_scan.statements.iter().any(|s| s.kind == StmtKind::Assertion) {
        return if module_only { Ok(None) } else { Err(decline.into()) };
    }
    let Some(eligible) = crate::incr_envelope::eligible(union_text, union_scan) else {
        return Err(decline.into());
    };
    stage("nominal common source shape checked", started);
    let tbox = prepared.tbox_index(text, scanned, cached_tbox, work)?;
    let Some(names) = nominal_common_subjects(&tbox, old, new, old_domain, &new_domain, &eligible.data_tbox) else {
        return Err(decline.into());
    };
    stage("nominal common TBox and affected", started);
    let mut receipt = Receipt { strategy: "common_nominal_subject_reuse",
        base_revision_statements: old.total, index_axioms: tbox.axiom_count(),
        affected_subjects: names.len(), reclassified_subjects: names.len(), ..Default::default() };
    receipt.apply_delta(delta);
    if let Some((module, count)) = object_common_module(text, scanned, old, new,
        prepared.index(), &tbox, &names, &eligible)
    {
        stage("object common consistency certificate and NEW module", started);
        let settings: Vec<_> = if text.len() >= INPROC_SIZE_GATE {
            vec![("KM_NO_INPROC_ENGINE", "1"), ("KM_NO_INPROC_HT", "1")]
        } else { Vec::new() };
        match classify_rows_with(&module, &settings) {
            Ok(answer) if answer.consistent && answer.dropped == 0 => {
                let mut tax = base_tax.clone(); tax.rendered = std::sync::OnceLock::new();
                let mut modified = prune_public_domain(&mut tax, &new_domain);
                modified.extend(names.iter().map(|name| Box::<str>::from(name.as_str())));
                replace_rows_from(&mut tax, answer, &names);
                modified.extend(prune_public_domain(&mut tax, &new_domain));
                receipt.strategy = "common_object_module_reuse";
                receipt.module_axioms = count;
                receipt.reused_subjects = retained_subject_count(base_tax, modified.iter().map(|name| &**name));
                let next = common_full_base(text, scanned, new.clone(), prepared.index().clone(),
                    new_domain, admission);
                stage("object common NEW module classified and merged", started);
                return Ok(Some((tax, receipt, Some(next))));
            },
            Ok(_) => receipt.fallback_reason = Some("object module result was not complete and consistent".into()),
            Err(error) => receipt.fallback_reason = Some(format!("object module classification declined: {error}")),
        }
    }
    if module_only {
        return match receipt.fallback_reason { Some(reason) => Err(reason), None => Ok(None) };
    }
    // Do not special-case an empty request: the full source's consistency
    // check is required even when no existing row needs a new subject probe.
    let full_started = Instant::now();
    let complete = match classify_requested_rows(text, &names, certified_new) {
        Ok(complete) => complete,
        Err(error) => {
            *prepared_full = Some(Err(error));
            return Err("nominal common full-source classification failed".into());
        },
    };
    let seconds = full_started.elapsed().as_secs_f64();
    if !complete.consistent || complete.dropped != 0 {
        *prepared_full = Some(Ok((Taxonomy::from_rows(complete), seconds)));
        return Err("nominal common full-source result requires full finalization".into());
    }
    let mut tax = base_tax.clone();
    tax.rendered = std::sync::OnceLock::new();
    let mut modified = prune_public_domain(&mut tax, &new_domain);
    modified.extend(names.iter().map(|name| Box::<str>::from(name.as_str())));
    replace_rows_from(&mut tax, complete, &names);
    modified.extend(prune_public_domain(&mut tax, &new_domain));
    receipt.reused_subjects = retained_subject_count(base_tax, modified.iter().map(|name| &**name));
    // Keep the full compiler and exact NEW enabled text, not the assertion-
    // omitting analysis TBox. No new deletion/Told shortcut is introduced.
    let next = common_full_base(text, scanned, new.clone(), prepared.index().clone(), new_domain, admission);
    stage("nominal common full source classified and merged", started);
    Ok(Some((tax, receipt, Some(next))))
}

fn common_full_base(text: &str, scanned: &Scan, new: Arc<Statements>, full: Arc<LocalityIndex>,
    new_domain: Arc<FxHashSet<Box<str>>>, admission: Option<Arc<crate::named_subclass_validation::NamedSubclassCertificate>>) -> BaseState
{
    let disabled: Vec<_> = full.axiom_hash.iter().map(|hash| !new.counts.contains_key(hash)).collect();
    let removed_hashes = full.axiom_hash.iter().zip(&disabled)
        .filter_map(|(hash, disabled)| disabled.then_some(*hash)).collect();
    BaseState { statements: new, source: None,
        index: Some(Some(full.clone())), compiler_full: Some(full), admission,
        disabled: disabled.into(), full_disabled: Arc::from([]),
        removed_hashes: Arc::new(removed_hashes), class_domain: Some(new_domain),
        full: None, told: None, consistent: true, witness: None,
        anonymous: anonymous_assertions(text, scanned), source_bytes: text.len() }
}

/// `certified`: the caller holds a derived admission certificate for `text`
/// (the one that let the common path skip `check_user_source`), so the pipeline
/// does not validate the whole source a second and third time.
fn classify_requested_rows(text: &str, names: &[String], certified: bool) -> Result<TaxonomyRows, String> {
    let file = crate::orchestrate::tmpfile::TempPath::new("-subjects.json");
    std::fs::write(file.path(), serde_json::to_vec(names).map_err(|e| e.to_string())?)
        .map_err(|e| e.to_string())?;
    let path = file.path().to_string_lossy().into_owned();
    classify_rows_impl(text, &[("KM_PUBLIC_SUBJECT_IRIS_FILE", path.as_str())], certified)
}

/// Classify the complete revision `text`, restricting only the bridge's
/// subject probes to the subjects `names`, and replace those subjects' rows
/// of the base taxonomy. Every other row is reused as in `deletion`.
fn restricted_complete(text: &str, names: &[String], base_tax: &Taxonomy,
    mut receipt: Receipt, started: Instant) -> Result<(Taxonomy, Receipt), String>
{
    {
        let file = crate::orchestrate::tmpfile::TempPath::new("-subjects.json");
        std::fs::write(file.path(), serde_json::to_vec(&names).map_err(|e| e.to_string())?)
            .map_err(|e| e.to_string())?;
        let path = file.path().to_string_lossy().into_owned();
        stage("subject file", started);
        let complete = classify_rows_with(text, &[("KM_PUBLIC_SUBJECT_IRIS_FILE", path.as_str())])
            .map_err(|e| format!("restricted classification: {e}"))?;
        if !complete.consistent || complete.dropped != 0 {
            return Err("restricted classification was not complete and consistent".into());
        }
        let mut tax = base_tax.clone();
        tax.rendered = std::sync::OnceLock::new();
        replace_rows_from(&mut tax, complete, names);
        receipt.strategy = "subject_reuse";
        receipt.module_axioms = 0;
        receipt.reused_subjects = retained_subject_count(base_tax, names.iter().map(String::as_str));
        stage("restricted classified and merged", started);
        Ok((tax, receipt))
    }
}

/// `replace_rows` for the pipeline's grouped answer: only the rows of
/// `subjects` are indexed (the restricted run still returns every subject's
/// known rows; those are not used).
fn replace_rows_from(tax: &mut Taxonomy, fresh: TaxonomyRows, subjects: &[String]) {
    let mut fresh_ids: FxHashMap<&str, u32> = FxHashMap::default();
    for (i, iri) in fresh.iris.iter().enumerate() {
        fresh_ids.insert(iri, i as u32);
    }
    let mut wanted: FxHashMap<u32, u32> = FxHashMap::default();
    for iri in subjects {
        let id = tax.id(iri);
        tax.unsat.remove(&id);
        tax.rows[id as usize] = None;
        tax.chunks[id as usize] = std::sync::OnceLock::new();
        if let Some(&f) = fresh_ids.get(iri.as_str()) {
            wanted.insert(f, id);
        }
    }
    for u in &fresh.unsatisfiable {
        if let Some(&f) = fresh_ids.get(u.as_str()) {
            if let Some(&id) = wanted.get(&f) {
                tax.unsat.insert(id);
            }
        }
    }
    let mut map: Vec<u32> = vec![u32::MAX; fresh.iris.len()];
    for (subject, supers) in &fresh.rows {
        let Some(&id) = wanted.get(subject) else { continue };
        let mut v: Vec<u32> = Vec::with_capacity(supers.len());
        for &o in supers {
            let m = &mut map[o as usize];
            if *m == u32::MAX {
                *m = tax.id(&fresh.iris[o as usize]);
            }
            v.push(*m);
        }
        v.sort_unstable();
        v.dedup();
        tax.rows[id as usize] = Some(v.into());
    }
}

/// Count published subjects whose rows/verdicts are retained, not recomputed.
fn retained_subject_count<'a>(base: &Taxonomy, reclassified: impl Iterator<Item = &'a str>) -> usize {
    let changed: FxHashSet<&str> = reclassified.collect();
    base.rows.iter().enumerate().filter(|(id, row)| {
        (row.as_ref().is_some_and(|row| !row.is_empty()) || base.unsat.contains(&(*id as u32)))
            && !changed.contains(&*base.iris[*id])
    }).count()
}

/// Replace the rows and unsatisfiability of `subjects` in `tax` by `fresh`.
fn replace_rows(tax: &mut Taxonomy, fresh: &Taxonomy, subjects: &[&str]) {
    for iri in subjects {
        let id = tax.id(iri);
        tax.unsat.remove(&id);
        tax.rows[id as usize] = None;
        tax.chunks[id as usize] = std::sync::OnceLock::new();
        if let Some(&mid) = fresh.ids.get(*iri) {
            if fresh.unsat.contains(&mid) {
                tax.unsat.insert(id);
            }
            if let Some(row) = &fresh.rows[mid as usize] {
                let mut v: Vec<u32> = row.iter().map(|&o| tax.id(&fresh.iris[o as usize])).collect();
                v.sort_unstable();
                tax.rows[id as usize] = Some(v.into());
            }
        }
    }
}

#[derive(Deserialize)]
#[serde(tag = "op", rename_all = "snake_case", deny_unknown_fields)]
enum Command {
    Init { functional_syntax: String },
    /// `base_revision`: the revision whose answer the client already holds. When it
    /// equals the last published revision the answer is sent as a row delta.
    Replace { functional_syntax: String, #[serde(default)] base_revision: Option<u64> },
    Classify,
    Stats,
}

fn write_error<W: Write>(w: &mut W, op: &str, error: &str) -> std::io::Result<()> {
    serde_json::to_writer(&mut *w, &serde_json::json!({"status": "error", "op": op, "error": error}))
        .map_err(std::io::Error::other)
}

pub fn run_jsonl_session<R: BufRead, W: Write>(reader: R, mut writer: W) -> std::io::Result<()> {
    let mut session = Session::new();
    // The taxonomy last published in full or as a delta, with its revision.
    let mut published: Option<(u64, Arc<Taxonomy>)> = None;
    for line in reader.lines() {
        let line = line?;
        if line.trim().is_empty() {
            continue;
        }
        let request_started = Instant::now();
        match serde_json::from_str::<Command>(&line) {
            Ok(command @ (Command::Init { .. } | Command::Replace { .. })) => {
                let (functional_syntax, base_revision) = match command {
                    Command::Init { functional_syntax } => (functional_syntax, None),
                    Command::Replace { functional_syntax, base_revision } => (functional_syntax, base_revision),
                    _ => unreachable!(),
                };
                drop(line);
                let delta_base = match (&published, base_revision) {
                    (Some((revision, tax)), Some(base)) if *revision == base && session.revision == base
                        && session.current.is_some() => Some(tax.clone()),
                    _ => None,
                };
                stage("request parsed", request_started);
                let op = if session.current.is_none() { "init" } else { "replace" };
                match session.update(functional_syntax) {
                    Ok((tax, receipt)) => {
                        stage("update returned", request_started);
                        session.revision += 1;
                        write!(writer, "{{\"status\":\"ok\",\"op\":\"{op}\",\"revision\":{},\"route\":\"auto\",\"retained_backend\":{},\"receipt\":",
                            session.revision, receipt.meaningful_reuse())?;
                        serde_json::to_writer(&mut writer, &serde_json::json!({
                            "strategy": receipt.strategy,
                            "base_revision_statements": receipt.base_revision_statements,
                            "removed_statements": receipt.removed_statements,
                            "removed_axioms": receipt.removed_axioms,
                            "added_statements": receipt.added_statements,
                            "added_axioms": receipt.added_axioms,
                            "reused_index_axioms": receipt.reused_index_axioms,
                            "rebuilt_index_axioms": receipt.rebuilt_index_axioms,
                            "index_build_calls": receipt.index_build_calls,
                            "index_build_failures": receipt.index_build_failures,
                            "cross_revision_compiled_axioms": receipt.cross_revision_compiled_axioms,
                            "same_update_compiled_axioms": receipt.same_update_compiled_axioms,
                            "compiled_locality_axioms": receipt.compiled_locality_axioms,
                            "csr_axiom_records": receipt.csr_axiom_records,
                            "csr_conjunctions": receipt.csr_conjunctions,
                            "csr_literal_records": receipt.csr_literal_records,
                            "resumed_backend_states": receipt.resumed_backend_states,
                            "reused_complete_answer": receipt.reused_complete_answer,
                            "statement_delta_verified": receipt.statement_delta_verified,
                            "affected_subjects": receipt.affected_subjects,
                            "reclassified_subjects": receipt.reclassified_subjects,
                            "module_axioms": receipt.module_axioms,
                            "index_axioms": receipt.index_axioms,
                            "reused_subjects": receipt.reused_subjects,
                            "told_subjects": receipt.told_subjects,
                            "published_pairs": tax.pair_count(),
                            "seconds": receipt.seconds,
                            "fallback_reason": receipt.fallback_reason,
                            "meaningful_incremental_update": receipt.meaningful_reuse(),
                        })).map_err(std::io::Error::other)?;
                        writer.write_all(b",\"result\":")?;
                        stage("receipt written", request_started);
                        match &delta_base {
                            Some(prev) => tax.publish_delta(prev, session.revision - 1, &mut writer)?,
                            None => tax.publish(&mut writer)?,
                        }
                        published = Some((session.revision, tax.clone()));
                        writer.write_all(b"}")?;
                    }
                    Err(error) => write_error(&mut writer, op, &error)?,
                }
            }
            Ok(Command::Classify) | Ok(Command::Stats) => match session.current {
                Some(i) => {
                    let tax = session.memo[i].taxonomy.clone();
                    write!(writer, "{{\"status\":\"ok\",\"op\":\"classify\",\"revision\":{},\"route\":\"auto\",\"retained_backend\":true,\"result\":", session.revision)?;
                    tax.publish(&mut writer)?;
                    writer.write_all(b"}")?;
                }
                None => write_error(&mut writer, "classify", "session is not initialised")?,
            },
            Err(error) => write_error(&mut writer, "parse", &error.to_string())?,
        }
        writer.write_all(b"\n")?;
        writer.flush()?;
        stage("response written", request_started);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn taxonomy_json_round_trips_rows_and_unsatisfiable() {
        let rows = TaxonomyRows {
            consistent: true,
            dropped: 0,
            unsatisfiable: vec!["http://e/U".into()],
            iris: vec!["http://e/A".into(), "http://e/B\"q".into(), "http://e/C".into()],
            rows: vec![(0, vec![1, 2]), (2, vec![1])],
        };
        let tax = Taxonomy::from_rows(rows);
        let mut out = Vec::new();
        tax.write_json(&mut out).unwrap();
        let value: serde_json::Value = serde_json::from_slice(&out).unwrap();
        let mut pairs: Vec<(String, String)> = value["subsumptions"]
            .as_array()
            .unwrap()
            .iter()
            .map(|p| (p[0].as_str().unwrap().into(), p[1].as_str().unwrap().into()))
            .collect();
        pairs.sort();
        assert_eq!(pairs, vec![
            ("http://e/A".into(), "http://e/B\"q".into()),
            ("http://e/A".into(), "http://e/C".into()),
            ("http://e/C".into(), "http://e/B\"q".into()),
        ]);
        assert_eq!(value["unsatisfiable"], serde_json::json!(["http://e/U"]));
        assert_eq!(value["consistent"], true);
        assert_eq!(tax.pair_count(), 3);
    }

    #[test]
    fn cloned_rendered_taxonomy_shares_bytes_and_invalidates_independently() {
        let base = Taxonomy::from_rows(TaxonomyRows {
            consistent: true, dropped: 0, unsatisfiable: Vec::new(),
            iris: vec!["http://e/A".into(), "http://e/B".into()],
            rows: vec![(0, vec![1])],
        });
        let mut original = Vec::new();
        base.publish(&mut original).unwrap();
        let mut next = base.clone();
        assert!(Arc::ptr_eq(base.rendered.get().unwrap(), next.rendered.get().unwrap()));
        next.rows[0] = None;
        next.rendered = std::sync::OnceLock::new();
        next.chunks[0] = std::sync::OnceLock::new();
        let mut changed = Vec::new();
        next.publish(&mut changed).unwrap();
        assert!(serde_json::from_slice::<serde_json::Value>(&changed).unwrap()["subsumptions"]
            .as_array().unwrap().is_empty());
        let mut unchanged = Vec::new();
        base.publish(&mut unchanged).unwrap();
        assert_eq!(unchanged, original);
        assert_ne!(changed, original);
    }

    #[test]
    fn current_class_domain_distinguishes_punning_and_implicit_builtin_aliases() {
        let text = "Prefix(:=<http://e/>) Prefix(o:=<http://www.w3.org/2002/07/owl#>) Ontology(Declaration(ObjectProperty(:A)) Declaration(Class(:B)) SubClassOf(o:Thing :B))";
        let scanned = scan(text).unwrap();
        let index = LocalityIndex::build(text, &scanned, false).unwrap();
        let domain = class_domain(&index);
        assert!(!domain.contains(":A"));
        assert!(domain.contains(":B"));
        assert!(domain.contains("o:Thing"));
        assert!(domain.contains("owl:Thing"));
        assert!(domain.contains("owl:Nothing"));
    }

    #[test]
    fn two_pass_statement_delta_matches_previous_algorithm_for_multisets_and_collisions() {
        fn reference_delta(old: &Statements, new: &Statements) -> Option<StatementDelta> {
            if old.collision || new.collision || old.header() != new.header() { return None; }
            if old.counts.keys().any(|hash| new.counts.contains_key(hash) && old.stmt(hash) != new.stmt(hash)) {
                return None;
            }
            let mut delta = StatementDelta::default();
            for (hash, &(count, kind, ..)) in &old.counts {
                let after = new.counts.get(hash).map_or(0, |entry| entry.0);
                delta.removed_statements += count.saturating_sub(after) as usize;
                if after == 0 && matches!(kind, StmtKind::Logical | StmtKind::Assertion) { delta.removed_axioms += 1; }
            }
            for (hash, &(count, kind, ..)) in &new.counts {
                let before = old.counts.get(hash).map_or(0, |entry| entry.0);
                delta.added_statements += count.saturating_sub(before) as usize;
                if before == 0 && matches!(kind, StmtKind::Logical | StmtKind::Assertion) { delta.added_axioms += 1; }
            }
            Some(delta)
        }
        let make = |mask: usize| {
            let mut text = String::from("Prefix(:=<urn:e#>) Ontology(<urn:e/o>\n");
            for (i, statement) in ["Declaration(Class(:A))", "SubClassOf(:A :B)",
                "ClassAssertion(:A :a)", "Annotation(:p :v)"].iter().enumerate() {
                for _ in 0..((mask >> (2*i)) & 3) { text.push_str(statement); text.push('\n'); }
            }
            text.push(')');
            let text = Arc::new(text);
            Statements::of(&scan(&text).unwrap(), &text)
        };
        let fields = |delta: Option<StatementDelta>| delta.map(|d|
            (d.added_statements, d.removed_statements, d.added_axioms, d.removed_axioms));
        let masks: Vec<_> = (0..32).chain([64, 128, 255]).collect();
        for &a in &masks {
            for &b in &masks {
                let (old, new) = (make(a), make(b));
                assert_eq!(fields(statement_delta(&old, &new)), fields(reference_delta(&old, &new)));
            }
        }
        let old = make(4);
        let changed = Arc::new("Prefix(:=<urn:e#>) Ontology(<urn:e/o> SubClassOf(:X :Y))".to_string());
        let mut scanned = scan(&changed).unwrap();
        scanned.statements[0].hash = *old.counts.keys().next().unwrap();
        let new = Statements::of(&scanned, &changed);
        assert!(statement_delta(&old, &new).is_none());
        assert_eq!(fields(statement_delta(&old, &new)), fields(reference_delta(&old, &new)));
    }

    #[test]
    fn preparation_ledger_records_failures_and_assignment_does_not_double_count() {
        let mut work = PreparationWork::default();
        let source = "Prefix(:=<urn:e#>) Ontology(Declaration(Class(:A)) Declaration(Class(:B)) SubClassOf(:A :B))";
        let scanned = scan(source).unwrap();
        assert_eq!(work.build_index(source, &scanned, false).unwrap().axiom_count(), 1);
        let imported = "Ontology(Import(<urn:unresolved>))";
        let scanned = scan(imported).unwrap();
        assert!(work.build_index(imported, &scanned, false).is_err());
        // A zero witness budget performs no subprocess check, but its initial
        // full index compilation must still belong to this same ledger.
        let scanned = scan(source).unwrap();
        assert!(inconsistency_witness(source, &scanned, 0.0, &mut work).witness.is_none());
        assert_eq!(work.index_build_calls, 3);
        assert_eq!(work.index_build_failures, 1);
        assert_eq!(work.rebuilt_index_axioms, 2);
        let mut receipt = Receipt::default();
        receipt.record_preparation(&work);
        receipt.record_preparation(&work);
        assert_eq!(receipt.index_build_calls, 3);
        assert_eq!(receipt.index_build_failures, 1);
        assert_eq!(receipt.rebuilt_index_axioms, 2);
        assert!(!receipt.meaningful_reuse());
    }

    #[test]
    fn compiler_ledger_distinguishes_prior_committed_donors_from_same_update_builds() {
        let text = "Prefix(:=<urn:e#>) Ontology(SubClassOf(:A :B))";
        let scanned = scan(text).unwrap();
        let donor = Arc::new(LocalityIndex::build(text, &scanned, false).unwrap());
        let lookup = |hash| scanned.statements.iter().find(|st| st.hash == hash)
            .map(|st| &text[st.start..st.end]);
        let mut same_update = PreparationWork::default();
        same_update.build_reusing_full(text, &scanned, &donor, &text[..scanned.open_end], lookup).unwrap();
        assert_eq!(same_update.same_update_compiled_axioms, 1);
        assert_eq!(same_update.cross_revision_compiled_axioms, 0);
        let mut prior = PreparationWork::default();
        prior.prior_compilers.push(donor.clone());
        prior.build_reusing_full(text, &scanned, &donor, &text[..scanned.open_end], lookup).unwrap();
        assert_eq!(prior.cross_revision_compiled_axioms, 1);
        assert_eq!(prior.same_update_compiled_axioms, 0);
        assert_eq!(prior.compiled_locality_axioms, 0);
        assert_eq!(prior.csr_axiom_records, 1);
    }

    #[test]
    fn receipt_strategy_alone_does_not_claim_meaningful_reuse() {
        let mut receipt = Receipt { strategy: "common_module_reuse", rebuilt_index_axioms: 10, ..Default::default() };
        assert!(!receipt.meaningful_reuse());
        assert_eq!(receipt.resumed_backend_states, 0);
        receipt.same_update_compiled_axioms = 10;
        assert!(!receipt.meaningful_reuse());
        receipt.cross_revision_compiled_axioms = 1;
        assert!(receipt.meaningful_reuse());
        receipt.cross_revision_compiled_axioms = 0;
        receipt.reused_subjects = 1;
        assert!(receipt.meaningful_reuse());
        receipt.reused_subjects = 0;
        receipt.reused_index_axioms = 10;
        assert!(receipt.meaningful_reuse());
    }

    #[test]
    fn statement_multisets_ignore_order_and_layout_outside_statements() {
        let a = "Prefix(:=<http://e/>)\nOntology(<http://e/o>\nSubClassOf(:A :B)\n# note\nSubClassOf(:B :C)\n)\n";
        let b = "Prefix(:=<http://e/>)\nOntology(<http://e/o>\n\nSubClassOf(:B :C)\nSubClassOf(:A :B)\n)";
        let c = "Prefix(:=<http://e/>)\nOntology(<http://e/o>\nSubClassOf(:B :C)\n)\n";
        let (sa, sb, sc) = (scan(a).unwrap(), scan(b).unwrap(), scan(c).unwrap());
        assert_eq!(sa.content_key(), sb.content_key());
        assert_ne!(sa.content_key(), sc.content_key());
        let (ta, tb, tc) = (Arc::new(a.to_string()), Arc::new(b.to_string()), Arc::new(c.to_string()));
        let (old, new) = (Statements::of(&sa, &ta), Statements::of(&sc, &tc));
        assert_eq!(old.header_hash, new.header_hash);
        assert!(new.counts.iter().all(|(h, (n, ..))| old.counts.get(h).is_some_and(|(m, ..)| m >= n)));
        assert!(new.confirms_subset(&old));
        assert!(old.exact_eq(&Statements::of(&sb, &tb)));
        assert!(!old.exact_eq(&new));
    }

    #[test]
    fn fingerprint_collisions_never_decide_reuse() {
        // Forge a collision: give two different statements the same
        // fingerprint and check that text confirmation rejects it.
        let a = "Prefix(:=<http://e/>)\nOntology(<http://e/o>\nSubClassOf(:A :B)\nSubClassOf(:B :C)\n)\n";
        let c = "Prefix(:=<http://e/>)\nOntology(<http://e/o>\nSubClassOf(:A :X)\n)\n";
        let (sa, mut sc) = (scan(a).unwrap(), scan(c).unwrap());
        sc.statements[0].hash = sa.statements[0].hash;
        let (ta, tc) = (Arc::new(a.to_string()), Arc::new(c.to_string()));
        let (old, new) = (Statements::of(&sa, &ta), Statements::of(&sc, &tc));
        assert!(new.counts.keys().all(|h| old.counts.contains_key(h)));
        assert!(!new.confirms_subset(&old));
        // A revision whose own statements collide is never reused.
        let mut sd = scan(a).unwrap();
        sd.statements[1].hash = sd.statements[0].hash;
        assert!(Statements::of(&sd, &ta).collision);
    }

    #[test]
    fn full_environment_guard_restores_added_and_changed_keys() {
        std::env::set_var("KM_INCR_SESSION_TEST_KEEP", "1");
        {
            let _guard = FullEnvironment::capture();
            std::env::set_var("KM_INCR_SESSION_TEST_KEEP", "2");
            std::env::set_var("KM_INCR_SESSION_TEST_NEW", "x");
        }
        assert_eq!(std::env::var("KM_INCR_SESSION_TEST_KEEP").unwrap(), "1");
        assert!(std::env::var_os("KM_INCR_SESSION_TEST_NEW").is_none());
        std::env::remove_var("KM_INCR_SESSION_TEST_KEEP");
    }
    fn certificate_source(extra: &str) -> Arc<Statements> {
        let text = Arc::new(format!("Prefix(:=<urn:cert#>)\nOntology(<urn:cert>\nDeclaration(Class(:A))\nDeclaration(Class(:B))\nDeclaration(Class(:E))\nDeclaration(Class(:F))\nDeclaration(AnnotationProperty(:note))\n{extra}\n)\n"));
        Arc::new(Statements::of(&scan(&text).unwrap(), &text))
    }

    #[test]
    fn early_object_support_requires_complete_timely_independent_result() {
        let source = certificate_source("Declaration(NamedIndividual(:a)) ClassAssertion(:A :a) ClassAssertion(:B :a) DisjointClasses(:A :B) SubClassOf(:E :F)");
        let scanned = scan(&source.text).unwrap();
        let proposal = crate::incr_support::propose_object(&source.text, &scanned).unwrap();
        assert_eq!(proposal.len(), 3);
        for answer in [None, Some(None), Some(Some(serde_json::json!({"consistent":true,"dropped":0}))),
            Some(Some(serde_json::json!({"consistent":false}))),
            Some(Some(serde_json::json!({"consistent":false,"dropped":1}))),
            Some(Some(serde_json::json!({"consistent":false,"dropped":false}))),
            Some(Some(serde_json::json!({"consistent":false,"dropped":-1})))]
        {
            let mut calls = 0;
            assert!(verified_source_support_with(&source, &scanned, &proposal,
                Instant::now() + EARLY_OBJECT_SUPPORT_LIMIT, &mut |doc, limit| {
                    calls += 1;
                    assert!(limit > std::time::Duration::ZERO && limit <= EARLY_OBJECT_SUPPORT_LIMIT);
                    assert!(doc.starts_with(source.header()));
                    assert!(doc.contains("Declaration(NamedIndividual(:a))"));
                    assert!(!doc.contains("SubClassOf(:E :F)"));
                    answer.clone()
                }).is_none());
            assert_eq!(calls, 1);
        }
        let cert = early_object_support_with(&source, &scanned, &mut |_, _|
            Some(Some(serde_json::json!({"consistent":false,"dropped":0})))).unwrap();
        assert!(matches!(&cert.support, InconsistencySupport::Witness { .. }));
        assert!(cert.contained_in(&source));
        let deadline = Instant::now() + std::time::Duration::from_millis(2);
        assert!(verified_source_support_with(&source, &scanned, &proposal, deadline, &mut |_, left| {
            std::thread::sleep(left + std::time::Duration::from_millis(2));
            Some(Some(serde_json::json!({"consistent":false,"dropped":0})))
        }).is_none(), "a late answer does not mint a certificate");
    }

    #[test]
    fn early_object_support_rejects_unknown_ids_collisions_and_expired_budget() {
        let source = certificate_source("SubClassOf(:A :B)");
        let scanned = scan(&source.text).unwrap();
        let hash = fingerprint(b"SubClassOf(:A :B)");
        let mut forbidden = |_: &str, _: std::time::Duration| -> Option<Option<serde_json::Value>> {
            panic!("invalid support cannot invoke the verifier")
        };
        for proposal in [vec![], vec![fingerprint(b"invented")], vec![hash;65],
            vec![fingerprint(b"Declaration(Class(:A))")]] {
            assert!(verified_source_support_with(&source,&scanned,&proposal,
                Instant::now()+EARLY_OBJECT_SUPPORT_LIMIT,&mut forbidden).is_none());
        }
        assert!(verified_source_support_with(&source,&scanned,&[hash],Instant::now(),&mut forbidden).is_none());
        let mut forged_scan = scanned.clone();
        forged_scan.statements[0].hash = hash;
        assert!(verified_source_support_with(&source,&forged_scan,&[hash],
            Instant::now()+EARLY_OBJECT_SUPPORT_LIMIT,&mut forbidden).is_none());
        let mut collided = Arc::try_unwrap(certificate_source("SubClassOf(:A :B)")).ok().unwrap();
        collided.collision = true;
        assert!(verified_source_support_with(&Arc::new(collided),&scanned,&[hash],
            Instant::now()+EARLY_OBJECT_SUPPORT_LIMIT,&mut forbidden).is_none());
    }

    fn early_support_session(old: &Arc<Statements>) -> Session {
        let scanned = scan(&old.text).unwrap();
        let index = Arc::new(LocalityIndex::build(&old.text, &scanned, false).unwrap());
        let domain = Arc::new(class_domain(&index));
        let base = common_full_base(&old.text,&scanned,old.clone(),index,domain,None);
        let mut session = Session { memo: Vec::new(), current: None, revision:0, clock:0, validated_new: false };
        session.insert(Revision { text:old.text.clone(), statements:Some(old.clone()),
            text_key:fingerprint(old.text.as_bytes()), content_key:scanned.content_key(),
            taxonomy:Arc::new(Taxonomy::empty()), inconsistency:None, base:Some(base),last_use:0 });
        session
    }

    #[test]
    fn global_deletion_without_proved_rows_declines_before_backend() {
        let old = certificate_source("Declaration(ObjectProperty(:r)) ReflexiveObjectProperty(:r) ObjectPropertyDomain(:r :A) SubClassOf(:B :E)");
        let new = certificate_source("Declaration(ObjectProperty(:r)) ReflexiveObjectProperty(:r) SubClassOf(:B :E)");
        let mut session = early_support_session(&old);
        let mut tax = Taxonomy::empty();
        let e=tax.id(":E"); let a=tax.id(":A");
        tax.rows[e as usize]=Some(vec![a].into());
        session.memo[0].taxonomy=Arc::new(tax);
        let before=(session.current,session.clock,session.memo.len());
        let result=session.deletion(&new.text,&scan(&new.text).unwrap(),&new,Instant::now(),
            statement_delta(&old,&new),&[],&mut PreparationWork::default());
        assert!(matches!(result,Err(ref reason) if reason=="no exact told rows survived the global deletion"));
        assert_eq!(before,(session.current,session.clock,session.memo.len()));
        assert!(session.memo[0].taxonomy.rows[e as usize].as_ref().unwrap().contains(&a));
    }

    #[test]
    fn global_deletion_requires_old_augmented_fragment_even_when_new_is_eligible() {
        let old=certificate_source("Declaration(ObjectProperty(:r)) Declaration(DataProperty(:p)) Declaration(NamedIndividual(:a)) ReflexiveObjectProperty(:r) ObjectPropertyDomain(:r :A) ClassAssertion(DataSomeValuesFrom(:p xsd:string) :a) SubClassOf(:B :E)");
        let new=certificate_source("Declaration(ObjectProperty(:r)) Declaration(DataProperty(:p)) Declaration(NamedIndividual(:a)) ReflexiveObjectProperty(:r) SubClassOf(:B :E)");
        assert!(crate::incr_envelope::eligible(&old.text,&scan(&old.text).unwrap()).is_none());
        assert!(crate::incr_envelope::eligible(&new.text,&scan(&new.text).unwrap()).is_some());
        let mut session=early_support_session(&old);
        let before=(session.current,session.clock,session.memo.len());
        let result=session.deletion(&new.text,&scan(&new.text).unwrap(),&new,Instant::now(),
            statement_delta(&old,&new),&[],&mut PreparationWork::default());
        assert!(matches!(result,Err(ref reason) if reason=="a removed or nominal axiom is in the module of the empty signature"));
        assert_eq!(before,(session.current,session.clock,session.memo.len()));
    }

    #[test]
    fn early_object_support_skips_healthy_common_additions() {
        let old = certificate_source("");
        let new = certificate_source("SubClassOf(:A owl:Thing)");
        let scanned = scan(&new.text).unwrap();
        let mut session = early_support_session(&old);
        let mut support = None;
        let result = session.common_module_update(&new.text,&scanned,&new,Instant::now(),
            statement_delta(&old,&new),&mut PreparationWork::default(),&mut None,&mut None,
            &mut support,&mut None,|_,_| panic!("healthy common route cannot invoke support verifier"));
        assert!(result.unwrap().unwrap().0.consistent);
        assert!(support.is_none());
    }

    #[test]
    fn early_object_support_admission_publication_and_retained_rollback() {
        const CHILD:&str = "KM_EARLY_OBJECT_SUPPORT_TEST_CHILD";
        if std::env::var(CHILD).as_deref()!=Ok("1") {
            let mut command=std::process::Command::new(std::env::current_exe().unwrap());
            for (key,_) in std::env::vars_os() {
                if key.to_string_lossy().starts_with("KM_") { command.env_remove(key); }
            }
            let output=command.args(["--exact",
                "incr_session::tests::early_object_support_admission_publication_and_retained_rollback",
                "--nocapture","--test-threads=1"]).env(CHILD,"1").output().unwrap();
            assert!(output.status.success(),"isolated support test failed:\n{}\n{}",
                String::from_utf8_lossy(&output.stdout),String::from_utf8_lossy(&output.stderr));
            assert!(String::from_utf8_lossy(&output.stdout).contains("1 passed; 0 failed"));
            return;
        }
        let premise="Declaration(NamedIndividual(:a)) ClassAssertion(:A :a) DisjointClasses(:A :B) SubClassOf(:E :F)";
        let old=certificate_source(premise);
        crate::frontend::conformance::check_user_source(&old.text).unwrap();
        let mut session=early_support_session(&old);
        let before=(session.current,session.clock,session.memo.len());
        let invalid=certificate_source(&format!("{premise} ClassAssertion(:B :a) SubClassOf(:A :Undeclared)"));
        let mut invalid_support=None;
        assert!(session.common_module_update(&invalid.text,&scan(&invalid.text).unwrap(),&invalid,
            Instant::now(),statement_delta(&old,&invalid),&mut PreparationWork::default(),
            &mut None,&mut None,&mut invalid_support,&mut None,
            |_,_| panic!("NEW admission must precede independent support verification")).is_err());
        assert!(invalid_support.is_none());
        assert_eq!(before,(session.current,session.clock,session.memo.len()));
        // A declined verifier follows the existing refusal path without
        // publishing support. The unrelated universal-role axiom makes the
        // optional common nominal envelope decline before a backend call.
        let declined=certificate_source(&format!("{premise} ClassAssertion(:B :a) SubClassOf(:E ObjectSomeValuesFrom(owl:topObjectProperty :F))"));
        let mut declined_support=None;
        let mut declined_full=None;
        let mut declined_calls=0;
        assert!(session.common_module_update(&declined.text,&scan(&declined.text).unwrap(),&declined,
            Instant::now(),statement_delta(&old,&declined),&mut PreparationWork::default(),
            &mut None,&mut None,&mut declined_support,&mut declined_full,|_,_| {
                declined_calls+=1; None
            }).is_err());
        assert_eq!(declined_calls,1);
        assert!(declined_support.is_none() && declined_full.is_none());
        assert_eq!(before,(session.current,session.clock,session.memo.len()));
        let new=certificate_source(&format!("{premise} ClassAssertion(:B :a)"));
        let scanned=scan(&new.text).unwrap();
        let mut certificate=None;
        let mut calls=0;
        let result=session.common_module_update(&new.text,&scanned,&new,Instant::now(),
            statement_delta(&old,&new),&mut PreparationWork::default(),&mut None,&mut None,
            &mut certificate,&mut None,|doc,limit| {
                calls+=1;
                assert!(limit<=EARLY_OBJECT_SUPPORT_LIMIT);
                crate::frontend::conformance::check_user_source(doc).unwrap();
                assert!(doc.contains("ClassAssertion(:A :a)") && doc.contains("ClassAssertion(:B :a)"));
                assert!(!doc.contains("SubClassOf(:E :F)"));
                Some(Some(serde_json::json!({"consistent":false,"dropped":0})))
            }).unwrap().unwrap();
        assert_eq!(calls,1);
        assert_eq!(before,(session.current,session.clock,session.memo.len()),"uncommitted discovery must stay transaction-local");
        let (tax,receipt,base)=result;
        assert!(!tax.consistent && tax.dropped==0 && tax.pair_count()==0 && tax.unsat.is_empty());
        assert!(base.is_none());
        assert_eq!(receipt.strategy,"verified_inconsistency_support");
        assert!(!receipt.reused_complete_answer && receipt.reused_subjects==0 && receipt.resumed_backend_states==0);
        let certificate=certificate.unwrap();
        assert!(matches!(&certificate.support,InconsistencySupport::Witness{..}));
        let mut published=Vec::new();tax.write_json(&mut published).unwrap();
        assert_eq!(serde_json::from_slice::<serde_json::Value>(&published).unwrap(),
            serde_json::json!({"consistent":false,"subsumptions":[],"unsatisfiable":[],"dropped":0}));
        session.insert(Revision {text:new.text.clone(),statements:Some(new.clone()),
            text_key:fingerprint(new.text.as_bytes()),content_key:scanned.content_key(),
            taxonomy:Arc::new(tax),inconsistency:Some(certificate.clone()),base:None,last_use:0});
        let stronger=certificate_source("Declaration(NamedIndividual(:a)) ClassAssertion(:A :a) ClassAssertion(:B :a) DisjointClasses(:A :B)");
        let (tax,receipt,retained)=session.inconsistency_reuse(&stronger.text,&stronger).unwrap().unwrap();
        assert!(!tax.consistent && receipt.reused_complete_answer);
        assert!(Arc::ptr_eq(&certificate,&retained),"next publication keeps the narrow certificate");
        let repaired=certificate_source("Declaration(NamedIndividual(:a)) ClassAssertion(:A :a) DisjointClasses(:A :B)");
        assert!(session.inconsistency_reuse(&repaired.text,&repaired).unwrap().is_none());
        let before=(session.current,session.clock,session.memo.len());
        assert!(session.inconsistency_reuse(&invalid.text,&invalid).is_err());
        assert_eq!(before,(session.current,session.clock,session.memo.len()));
    }

    #[test]
    fn first_verified_core_shares_one_full_index_with_inconsistent_base() {
        // Interleave declarations deliberately: the verifier document must
        // retain the old all-declarations-before-core layout byte for byte.
        let text = Arc::new("Prefix(:=<urn:core#>) Ontology(<urn:core> SubClassOf(owl:Thing :A) Declaration(Class(:A)) SubClassOf(:A owl:Nothing) Declaration(Class(:B)) SubClassOf(:B :A))".to_owned());
        let scanned = scan(&text).unwrap();
        let statements = Arc::new(Statements::of(&scanned, &text));
        let mut work = PreparationWork::default();
        let mut calls = 0;
        let prepared = inconsistency_witness_with(&text, &scanned, 1.0, &mut work, |doc, _| {
            calls += 1;
            if calls == 1 {
                assert_eq!(doc, "Prefix(:=<urn:core#>) Ontology(<urn:core>\nDeclaration(Class(:A))\nDeclaration(Class(:B))\nSubClassOf(owl:Thing :A)\nSubClassOf(:A owl:Nothing)\n)\n");
            }
            Some(calls == 1) // Preserve the first support when reductions fail.
        });
        assert_eq!(calls, 3, "unsupported sources retain bounded minimization");
        assert_eq!(work.index_build_calls, 1);
        let index = prepared.index.unwrap();
        assert!(index.full_mode);
        let expected: BTreeSet<_> = index.empty_module_statements().into_iter().collect();
        assert_eq!(prepared.witness.as_ref().unwrap().iter().copied().collect::<BTreeSet<_>>(), expected);
        let mut base = BaseState {
            statements, source: Some((text.clone(), scanned)), index: None,
            compiler_full: Some(index.clone()), admission: None,
            disabled: Arc::from([]), full_disabled: Arc::from([]),
            removed_hashes: Arc::new(FxHashSet::default()), class_domain: None,
            full: None, told: None, consistent: false, witness: prepared.witness,
            anonymous: FxHashSet::default(), source_bytes: text.len(),
        };
        assert!(base.index(&mut work).is_some());
        assert!(Arc::ptr_eq(base.index.as_ref().unwrap().as_ref().unwrap(), &index));
        assert!(Arc::ptr_eq(base.compiler_full.as_ref().unwrap(), &index));
        assert_eq!(work.index_build_calls, 1, "initial eager indexing must share preparation");
        assert!(base.source.is_none());
        assert_eq!(base.disabled.len(), index.axiom_count());
        assert!(base.disabled.iter().all(|disabled| !disabled));
        assert!(base.full.is_none() && base.told.is_none());
    }

    #[test]
    fn first_core_failed_verifier_retains_index_but_only_full_source_certificate() {
        let source = certificate_source("SubClassOf(owl:Thing owl:Nothing)");
        let scanned = scan(&source.text).unwrap();
        for verdict in [Some(false), None] {
            let mut work = PreparationWork::default();
            let mut calls = 0;
            let prepared = inconsistency_witness_with(&source.text, &scanned, 1.0, &mut work, |_, _| {
                calls += 1;
                verdict
            });
            assert_eq!(calls, 1);
            assert!(prepared.witness.is_none());
            assert!(prepared.index.as_ref().unwrap().full_mode);
            assert_eq!(work.index_build_calls, 1);
            // The caller's original complete classification is still the
            // authority; a failed core probe cannot turn into a witness.
            let cert = InconsistencyCertificate::from_verified_inconsistent(source.clone(), prepared.witness.as_deref()).unwrap();
            assert!(matches!(cert.support, InconsistencySupport::Full(_)));
        }
        let mut work = PreparationWork::default();
        let prepared = inconsistency_witness_with(&source.text, &scanned, 0.0, &mut work,
            |_, _| panic!("zero budget must not invoke any verifier"));
        assert!(prepared.witness.is_none() && prepared.index.is_some());
        assert_eq!(work.index_build_calls, 1);
    }

    #[test]
    fn first_core_containment_loss_declines_even_if_a_smaller_clash_survives() {
        let original = certificate_source("SubClassOf(owl:Thing owl:Nothing)\nSubClassOf(owl:Thing :E)");
        let scanned = scan(&original.text).unwrap();
        let mut work = PreparationWork::default();
        let mut calls = 0;
        let prepared = inconsistency_witness_with(&original.text, &scanned, 1.0, &mut work, |_, _| {
            calls += 1;
            Some(calls == 1)
        });
        assert_eq!(prepared.witness.as_ref().unwrap().len(), 2);
        let cert = InconsistencyCertificate::from_verified_inconsistent(original.clone(), prepared.witness.as_deref()).unwrap();
        let mut taxonomy = Taxonomy::empty(); taxonomy.consistent = false;
        let mut session = Session { memo: Vec::new(), current: None, revision: 0, clock: 0, validated_new: false };
        session.insert(Revision { text: original.text.clone(), statements: Some(original.clone()),
            text_key: fingerprint(original.text.as_bytes()), content_key: 1,
            taxonomy: Arc::new(taxonomy), inconsistency: Some(cert), base: None, last_use: 0 });
        // A stronger revision keeps the complete independently verified core.
        let stronger = certificate_source("SubClassOf(owl:Thing owl:Nothing)\nSubClassOf(owl:Thing :E)\nSubClassOf(:A :B)");
        assert!(session.inconsistency_reuse(&stronger.text, &stronger).unwrap().is_some());
        // Broad support can lose a reuse opportunity even while a smaller
        // contradiction survives. Dispatch must decline and classify normally.
        let smaller = certificate_source("SubClassOf(owl:Thing owl:Nothing)");
        assert!(session.inconsistency_reuse(&smaller.text, &smaller).unwrap().is_none());
        let repaired = certificate_source("SubClassOf(:A :B)");
        assert!(session.inconsistency_reuse(&repaired.text, &repaired).unwrap().is_none());
    }

    fn data_clash_proposal_source() -> Arc<Statements> {
        let text = Arc::new("Prefix(:=<urn:proposal#>) Ontology(<urn:proposal> Declaration(Class(:A)) Declaration(DataProperty(:p)) Declaration(NamedIndividual(:a)) SubClassOf(owl:Thing :A) FunctionalDataProperty(:p) DataPropertyAssertion(:p :a \"one\") DataPropertyAssertion(:p :a \"two\"))".to_owned());
        Arc::new(Statements::of(&scan(&text).unwrap(), &text))
    }

    #[test]
    fn small_support_proposal_requires_its_own_verified_inconsistent_answer() {
        let source = data_clash_proposal_source();
        let scanned = scan(&source.text).unwrap();
        let expected = crate::incr_support::propose(&source.text, &scanned).unwrap();
        assert_eq!(expected.len(), 3);
        let mut work = PreparationWork::default();
        let mut calls = 0;
        let prepared = inconsistency_witness_with(&source.text, &scanned, 1.0, &mut work, |doc, limit| {
            calls += 1;
            assert!(!limit.is_zero() && limit <= std::time::Duration::from_secs(1));
            assert!(doc.contains("Declaration(DataProperty(:p))\n"));
            assert!(doc.contains("Declaration(NamedIndividual(:a))\n"));
            match calls {
                1 => assert!(doc.contains("SubClassOf(owl:Thing :A)")),
                2 => {
                    assert!(!doc.contains("SubClassOf(owl:Thing :A)"));
                    assert!(doc.contains("DataPropertyAssertion(:p :a \"one\")\n"));
                    assert!(doc.contains("DataPropertyAssertion(:p :a \"two\")\n"));
                }
                _ => panic!("verified proposal must skip further minimization"),
            }
            Some(true)
        });
        assert_eq!(calls, 2);
        assert_eq!(prepared.witness.unwrap(), expected);
        assert_eq!(work.index_build_calls, 1);
    }

    #[test]
    fn rejected_or_timed_out_proposal_keeps_verified_support_and_minimizes_normally() {
        let source = data_clash_proposal_source();
        let scanned = scan(&source.text).unwrap();
        for proposal_verdict in [Some(false), None] {
            let mut work = PreparationWork::default();
            let mut calls = 0;
            let prepared = inconsistency_witness_with(&source.text, &scanned, 1.0, &mut work, |doc, _| {
                calls += 1;
                if calls == 1 { return Some(true); }
                if calls == 2 {
                    assert!(!doc.contains("SubClassOf(owl:Thing :A)"));
                    return proposal_verdict;
                }
                Some(false)
            });
            assert!(calls > 2, "a failed optional proposal must not remove general fallback");
            let index = prepared.index.unwrap();
            assert_eq!(prepared.witness.unwrap().into_iter().collect::<BTreeSet<_>>(),
                index.empty_module_statements().into_iter().collect());
            assert_eq!(work.index_build_calls, 1);
        }
    }

    #[test]
    fn exhausted_total_witness_budget_does_not_invoke_optional_proposal_verifier() {
        let source = data_clash_proposal_source();
        let scanned = scan(&source.text).unwrap();
        let mut work = PreparationWork::default();
        let mut calls = 0;
        let prepared = inconsistency_witness_with(&source.text, &scanned, 0.01, &mut work, |_, remaining| {
            calls += 1;
            assert_eq!(calls, 1);
            std::thread::sleep(remaining + std::time::Duration::from_millis(2));
            Some(true)
        });
        assert_eq!(calls, 1);
        let index = prepared.index.unwrap();
        assert_eq!(prepared.witness.unwrap().into_iter().collect::<BTreeSet<_>>(),
            index.empty_module_statements().into_iter().collect());
        assert_eq!(work.index_build_calls, 1);
    }

    fn clash_hash(source: &Statements) -> u128 {
        *source.counts.keys().find(|h| source.stmt(h) == Some("SubClassOf(owl:Thing owl:Nothing)")).unwrap()
    }

    #[test]
    fn inconsistency_certificate_full_support_shares_source_and_checks_exact_identity() {
        let source = certificate_source("SubClassOf(owl:Thing owl:Nothing)");
        let certificate = InconsistencyCertificate::from_verified_inconsistent(source.clone(), None).unwrap();
        assert_eq!(certificate.origin_source_key, fingerprint(source.text.as_bytes()));
        match &certificate.support {
            InconsistencySupport::Full(shared) => assert!(Arc::ptr_eq(shared, &source)),
            _ => panic!("expected shared full-source support"),
        }
        assert!(certificate.contained_in(&certificate_source("SubClassOf(owl:Thing owl:Nothing)\nSubClassOf(:A :B)")));
        assert!(!certificate.contained_in(&certificate_source("SubClassOf(:A :B)")));
        let changed_header = Arc::new(source.text.replacen("urn:cert#", "urn:other#", 1));
        let changed = Statements::of(&scan(&changed_header).unwrap(), &changed_header);
        assert!(!certificate.contained_in(&changed));
    }

    #[test]
    fn inconsistency_certificate_compact_support_checks_text_collisions_and_context() {
        let source = certificate_source("SubClassOf(owl:Thing owl:Nothing)\nSubClassOf(:A :B)");
        let hash = clash_hash(&source);
        let certificate = InconsistencyCertificate::from_verified_inconsistent(source.clone(), Some(&[hash])).unwrap();
        assert!(matches!(&certificate.support, InconsistencySupport::Witness { .. }));
        // Unrelated logical support can change; all verifier declarations stay.
        assert!(certificate.contained_in(&certificate_source("SubClassOf(owl:Thing owl:Nothing)\nSubClassOf(:E :F)")));
        let mut forged = Arc::try_unwrap(certificate_source("SubClassOf(:A :B)")).ok().unwrap();
        let actual = *forged.counts.keys().find(|h| forged.stmt(h) == Some("SubClassOf(:A :B)")).unwrap();
        let descriptor = forged.counts.remove(&actual).unwrap();
        forged.counts.insert(hash, descriptor);
        assert!(!certificate.contained_in(&forged), "hash membership must not stand in for exact text");
        forged.collision = true;
        assert!(!certificate.contained_in(&forged));
        assert!(InconsistencyCertificate::from_verified_inconsistent(Arc::new(forged), None).is_none());
        let rebound = Arc::new(source.text.replacen("urn:cert#", "urn:other#", 1));
        assert!(!certificate.contained_in(&Statements::of(&scan(&rebound).unwrap(), &rebound)));
        let missing_declaration = Arc::new(source.text.replace("Declaration(Class(:B))", ""));
        assert!(!certificate.contained_in(&Statements::of(&scan(&missing_declaration).unwrap(), &missing_declaration)));
        let duplicate = certificate_source("SubClassOf(owl:Thing owl:Nothing)\nSubClassOf(owl:Thing owl:Nothing)");
        let duplicate_certificate = InconsistencyCertificate::from_verified_inconsistent(duplicate.clone(), Some(&[clash_hash(&duplicate)])).unwrap();
        assert!(duplicate_certificate.contained_in(&certificate_source("SubClassOf(owl:Thing owl:Nothing)")));
    }

    #[test]
    fn inconsistency_certificate_arc_survives_memo_eviction_without_old_source() {
        let original = certificate_source("SubClassOf(owl:Thing owl:Nothing)\nSubClassOf(:A :B)");
        let weak_source = Arc::downgrade(&original.text);
        let certificate = InconsistencyCertificate::from_verified_inconsistent(original.clone(), Some(&[clash_hash(&original)])).unwrap();
        let mut taxonomy = Taxonomy::empty(); taxonomy.consistent = false;
        let taxonomy = Arc::new(taxonomy);
        let mut session = Session { memo: Vec::new(), current: None, revision: 0, clock: 0, validated_new: false };
        session.insert(Revision { text: original.text.clone(), statements: Some(original.clone()),
            text_key: fingerprint(original.text.as_bytes()), content_key: 1, taxonomy,
            inconsistency: Some(certificate.clone()), base: None, last_use: 0 });
        drop(original);
        for n in 0..MEMO_LIMIT + 2 {
            let source = certificate_source(&format!("SubClassOf(owl:Thing owl:Nothing)\nAnnotationAssertion(:note :A \"{n}\")"));
            let (taxonomy, receipt, inherited) = session.inconsistency_reuse(&source.text, &source).unwrap().unwrap();
            assert_eq!(receipt.strategy, "inconsistency_witness_reuse");
            assert!(Arc::ptr_eq(&inherited, &certificate));
            session.insert(Revision { text: source.text.clone(), statements: Some(source.clone()),
                text_key: fingerprint(source.text.as_bytes()), content_key: n as u128 + 2,
                taxonomy, inconsistency: Some(inherited), base: None, last_use: 0 });
        }
        assert_eq!(session.memo.len(), MEMO_LIMIT);
        assert!(weak_source.upgrade().is_none(), "compact certificate must not pin the evicted full source");
        let without_clash = certificate_source("SubClassOf(:E :F)");
        assert!(session.inconsistency_reuse(&without_clash.text, &without_clash).unwrap().is_none());
        let invalid = certificate_source("SubClassOf(owl:Thing owl:Nothing)\nSubClassOf(:A :Undeclared)");
        let before = (session.current, session.clock, session.memo.len());
        assert!(session.inconsistency_reuse(&invalid.text, &invalid).is_err());
        assert_eq!(before, (session.current, session.clock, session.memo.len()));
    }
    #[test]
    fn inconsistency_certificate_full_support_propagates_same_arc_after_eviction() {
        let original = certificate_source("SubClassOf(owl:Thing owl:Nothing)");
        let certificate = InconsistencyCertificate::from_verified_inconsistent(original.clone(), None).unwrap();
        let mut taxonomy = Taxonomy::empty(); taxonomy.consistent = false;
        let mut session = Session { memo: Vec::new(), current: None, revision: 0, clock: 0, validated_new: false };
        session.insert(Revision { text: original.text.clone(), statements: Some(original.clone()),
            text_key: fingerprint(original.text.as_bytes()), content_key: 1,
            taxonomy: Arc::new(taxonomy), inconsistency: Some(certificate.clone()),
            base: None, last_use: 0 });
        for n in 0..MEMO_LIMIT + 2 {
            let source = certificate_source(&format!("SubClassOf(owl:Thing owl:Nothing)\nAnnotationAssertion(:note :A \"{n}\")"));
            let (taxonomy, receipt, inherited) = session.inconsistency_reuse(&source.text, &source).unwrap().unwrap();
            assert_eq!(receipt.strategy, "inconsistency_superset_reuse");
            assert!(Arc::ptr_eq(&inherited, &certificate));
            session.insert(Revision { text: source.text.clone(), statements: Some(source.clone()),
                text_key: fingerprint(source.text.as_bytes()), content_key: n as u128 + 2,
                taxonomy, inconsistency: Some(inherited), base: None, last_use: 0 });
        }
        assert_eq!(session.memo.len(), MEMO_LIMIT);
        assert!(session.memo.iter().all(|revision| !Arc::ptr_eq(revision.statements.as_ref().unwrap(), &original)));
        match &certificate.support {
            InconsistencySupport::Full(shared) => assert!(Arc::ptr_eq(shared, &original)),
            _ => panic!("full support must keep one shared source backing"),
        }
    }
    #[test]
    fn pure_addition_new_index_matches_explicit_union_despite_order_and_duplicates() {
        let source = |body: &str| Arc::new(format!("Prefix(:=<urn:add#>) Ontology(<urn:add>\nDeclaration(Class(:A))\nDeclaration(Class(:B))\nDeclaration(Class(:C))\nDeclaration(Class(:E))\nDeclaration(Class(:F))\nDeclaration(ObjectProperty(:r))\nDeclaration(NamedIndividual(:a))\n{body}\n)"));
        for (old_body, new_body) in [
            ("SubClassOf(:A :B)\nSubClassOf(:E :F)", "SubClassOf(:E :F)\nSubClassOf(:B :C)\nSubClassOf(:A :B)\nSubClassOf(:A :B)"),
            ("SubClassOf(:A :B)", "ClassAssertion(:A :a)\nSubClassOf(:A :B)"),
            ("SubClassOf(:A :B)", "Declaration(ObjectProperty(:A))\nObjectPropertyDomain(:A :C)\nSubClassOf(:A :B)"),
        ] {
            let (old_text, new_text) = (source(old_body), source(new_body));
            let (old_scan, new_scan) = (scan(&old_text).unwrap(), scan(&new_text).unwrap());
            let (old, new) = (Statements::of(&old_scan, &old_text), Statements::of(&new_scan, &new_text));
            assert!(old.confirms_subset(&new));
            // Independent old construction: stable OLD order, then NEW-only
            // statement text. NEW's order and duplicate counts differ.
            let mut union = old.header().to_owned(); union.push('\n');
            let mut seen = FxHashSet::default();
            for (text, scanned) in [(&old_text, &old_scan), (&new_text, &new_scan)] {
                for statement in &scanned.statements {
                    if seen.insert(statement.hash) {
                        union.push_str(&text[statement.start..statement.end]); union.push('\n');
                    }
                }
            }
            union.push(')');
            let union_scan = scan(&union).unwrap();
            let a = LocalityIndex::build(&new_text, &new_scan, false).unwrap();
            let b = LocalityIndex::build(&union, &union_scan, false).unwrap();
            assert!(a.full_mode && b.full_mode);
            assert_eq!(a.positive_object_source, b.positive_object_source);
            let classes = |ix: &LocalityIndex| ix.symbols.iter().zip(&ix.is_class)
                .filter(|(_, class)| **class).map(|(name, _)| name.to_string()).collect::<BTreeSet<_>>();
            assert_eq!(classes(&a), classes(&b));
            let mut seeds: Vec<Option<&str>> = a.names.iter().map(|n| Some(n.as_ref())).collect(); seeds.push(None);
            for seed in seeds {
                let canonical_module = |ix: &LocalityIndex| {
                    let seeds: Vec<_> = seed.into_iter().map(|name| ix.named(name).unwrap()).collect();
                    let (module, signature) = ix.module(&seeds, &vec![false; ix.axiom_count()]);
                    let hashes = module.iter().map(|&id| ix.axiom_hash[id as usize]).collect::<BTreeSet<_>>();
                    let symbols = ix.symbols.iter().zip(signature).filter(|(_, present)| *present)
                        .map(|(name, _)| name.to_string()).collect::<BTreeSet<_>>();
                    (hashes, symbols)
                };
                assert_eq!(canonical_module(&a), canonical_module(&b), "seed {seed:?}");
            }
        }
        let old_text = source("SubClassOf(:A :B)");
        let old = Statements::of(&scan(&old_text).unwrap(), &old_text);
        let rebound = Arc::new(old_text.replacen("urn:add#", "urn:rebound#", 1));
        assert!(!old.confirms_subset(&Statements::of(&scan(&rebound).unwrap(), &rebound)));
        let replacement = source("SubClassOf(:E :F)");
        let mut forged = Statements::of(&scan(&replacement).unwrap(), &replacement);
        let old_hash = *old.counts.keys().find(|h| old.stmt(h) == Some("SubClassOf(:A :B)")).unwrap();
        let new_hash = *forged.counts.keys().find(|h| forged.stmt(h) == Some("SubClassOf(:E :F)")).unwrap();
        let entry = forged.counts.remove(&new_hash).unwrap(); forged.counts.insert(old_hash, entry);
        assert!(!old.confirms_subset(&forged), "hash collision must not admit the fast path");
    }
    #[test]
    fn empty_module_decline_prediction_needs_no_full_compiler() {
        let head = "Prefix(:=<urn:pred#>) Ontology(Declaration(Class(:A)) Declaration(Class(:B)) \
            Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b)) SubClassOf(:A :B) ";
        let make = |body: &str| Arc::new(format!("{head}{body})"));
        let state = |text: &Arc<String>, full: bool| {
            let scanned = scan(text).unwrap();
            let mut work = PreparationWork::default();
            let tbox = Arc::new(work.build_index(text, &scanned, true).unwrap());
            let compiler_full = full.then(|| Arc::new(work.build_index(text, &scanned, false).unwrap()));
            BaseState { statements: Arc::new(Statements::of(&scanned, text)), source: None,
                index: Some(Some(tbox)), compiler_full, admission: None, disabled: Arc::from([]),
                full_disabled: Arc::from([]), removed_hashes: Arc::new(FxHashSet::default()),
                class_domain: None, full: None, told: None, consistent: true, witness: None,
                anonymous: FxHashSet::default(), source_bytes: text.len() }
        };
        for (old_body, new_body) in [
            ("ClassAssertion(:A :a) DifferentIndividuals(:a :b)", "DifferentIndividuals(:a :b)"),
            ("ClassAssertion(:A :a) DifferentIndividuals(:a :b)", "ClassAssertion(:A :a) ClassAssertion(:B :b) DifferentIndividuals(:a :b)"),
            ("ClassAssertion(:A :a)", "ClassAssertion(:B :a)"),
            ("ClassAssertion(:A :a)", ""),
            ("DifferentIndividuals(:a :b)", "SubClassOf(:B :A) DifferentIndividuals(:a :b)"),
        ] {
            let (old_text, new_text) = (make(old_body), make(new_body));
            let old = Statements::of(&scan(&old_text).unwrap(), &old_text);
            let new_scan = scan(&new_text).unwrap();
            let new = Statements::of(&new_scan, &new_text);
            let exact = predicts_empty_module_decline(&state(&old_text, true), &old, &new, &new_text, &new_scan);
            let tbox_only = predicts_empty_module_decline(&state(&old_text, false), &old, &new, &new_text, &new_scan);
            // TBox-only prediction is conservative: never fires when the exact one does not.
            assert!(!tbox_only || exact, "{old_body} -> {new_body}");
            // These sources have a witness (DifferentIndividuals) or are positive.
            assert_eq!(tbox_only, exact, "{old_body} -> {new_body}");
        }
    }

    fn exact_pair_fixture() -> (Arc<Statements>, Arc<Statements>, BaseState) {
        let make = |body: &str| Arc::new(format!("Prefix(:=<urn:pair#>) Ontology(Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C)) Declaration(Class(:K)) Declaration(ObjectProperty(:r)) Declaration(NamedIndividual(:a)) SubClassOf(:A ObjectSomeValuesFrom(:r ObjectOneOf(:a))) ClassAssertion(:K :a) {body})"));
        let text = make("SubClassOf(:B :C)");
        let scanned = scan(&text).unwrap();
        let old = Arc::new(Statements::of(&scanned, &text));
        let next = make("");
        let new = Arc::new(Statements::of(&scan(&next).unwrap(), &next));
        let mut base = BaseState { statements: old.clone(), source: Some((text.clone(), scanned)),
            index: None, compiler_full: None, admission: None, disabled: Arc::from([]),
            full_disabled: Arc::from([]), removed_hashes: Arc::new(FxHashSet::default()),
            class_domain: None, full: None, told: None, consistent: true, witness: None,
            anonymous: FxHashSet::default(), source_bytes: text.len() };
        let mut work = PreparationWork::default();
        assert!(base.index(&mut work).unwrap().tbox_mode);
        assert_eq!(work.index_build_calls, 2);
        (old, new, base)
    }

    #[test]
    fn exact_union_pair_reuses_both_indexes_with_fresh_module_and_domain_parity() {
        let (old, new, base) = exact_pair_fixture();
        let (prepared, cached) = base.exact_union_pair(&old, &new).unwrap();
        assert!(Arc::ptr_eq(prepared.index(), base.full.as_ref().unwrap()));
        assert!(Arc::ptr_eq(&cached, base.index.as_ref().unwrap().as_ref().unwrap()));
        assert!(std::ptr::eq(prepared.text(&new.text), old.text.as_str()));
        let new_scan = scan(&new.text).unwrap();
        let mut reused_work = PreparationWork::default();
        let tbox = prepared.tbox_index(&new.text, &new_scan, Some(&cached), &mut reused_work).unwrap();
        assert!(Arc::ptr_eq(&tbox, &cached));
        assert_eq!(reused_work.index_build_calls, 0);
        let mut fresh_work = PreparationWork::default();
        let old_scan = scan(&old.text).unwrap();
        let full = Arc::new(fresh_work.build_index(&old.text, &old_scan, false).unwrap());
        let fresh = PreparedCompiler::Union { source: old.text.clone(), scan: old_scan, index: full };
        let fresh_tbox = fresh.tbox_index(&new.text, &new_scan, None, &mut fresh_work).unwrap();
        assert_eq!(fresh_work.index_build_calls, 2);
        assert_eq!(class_domain(prepared.index()), class_domain(fresh.index()));
        let domain = |index: &LocalityIndex| index.live_public_class_names(|h| new.counts.contains_key(&h)).unwrap().into_iter().map(str::to_string).collect::<BTreeSet<_>>();
        assert_eq!(domain(prepared.index()), domain(fresh.index()));
        for (a,b) in [(prepared.index().as_ref(), fresh.index().as_ref()), (tbox.as_ref(), fresh_tbox.as_ref())] {
            assert_eq!(a.axiom_hash, b.axiom_hash);
            for seed in a.names.iter().map(|n| Some(n.as_ref())).chain(std::iter::once(None)) {
                let module = |ix: &LocalityIndex| {
                    let seeds: Vec<_> = seed.into_iter().map(|name| ix.named(name).unwrap()).collect();
                    let disabled: Vec<_> = ix.axiom_hash.iter().map(|h| !new.counts.contains_key(h)).collect();
                    let (members, signature) = ix.module(&seeds, &disabled);
                    (members.into_iter().map(|id| ix.axiom_hash[id as usize]).collect::<BTreeSet<_>>(),
                        ix.symbols.iter().zip(signature).filter(|(_,yes)| *yes).map(|(n,_)| n.to_string()).collect::<BTreeSet<_>>())
                };
                assert_eq!(module(a),module(b), "seed {seed:?}");
            }
        }
        // A tentative deletion and a later deletion keep the donor immutable;
        // their masked/historical views must never requalify as an exact pair.
        let removed = [fingerprint(b"SubClassOf(:B :C)")];
        let candidate = base.after_deletion(new.clone(), &removed);
        assert!(candidate.exact_union_pair(&new, &new).is_none());
        drop(candidate);
        assert!(base.exact_union_pair(&old, &new).is_some());
        let repeated = base.after_deletion(new.clone(), &removed).after_deletion(new.clone(), &[]);
        assert!(repeated.exact_union_pair(&new, &new).is_none());
        assert!(base.disabled.iter().all(|x| !x) && base.full_disabled.iter().all(|x| !x));
    }

    #[test]
    fn exact_union_pair_rejects_masks_missing_pairs_and_unconfirmed_source() {
        let (old, new, mut base) = exact_pair_fixture();
        let saved = base.disabled.clone();
        base.disabled = Arc::from([]);
        assert!(base.exact_union_pair(&old,&new).is_none());
        base.disabled = vec![true; saved.len()].into();
        assert!(base.exact_union_pair(&old,&new).is_none());
        base.disabled = saved;
        let saved = base.full_disabled.clone();
        base.full_disabled = Arc::from([]);
        assert!(base.exact_union_pair(&old,&new).is_none());
        base.full_disabled = vec![true; saved.len()].into();
        assert!(base.exact_union_pair(&old,&new).is_none());
        base.full_disabled = saved;
        base.removed_hashes = Arc::new([fingerprint(b"historical")].into_iter().collect());
        assert!(base.exact_union_pair(&old,&new).is_none());
        base.removed_hashes = Arc::new(FxHashSet::default());
        let full = base.full.take();
        assert!(base.compiler_full.is_some());
        assert!(base.exact_union_pair(&old,&new).is_none());
        base.full = full;
        let tbox = base.index.take();
        base.index = Some(Some(base.full.as_ref().unwrap().clone()));
        assert!(base.exact_union_pair(&old,&new).is_none());
        base.index = None;
        assert!(base.exact_union_pair(&old,&new).is_none());
        base.index = tbox;
        let changed = Arc::new(new.text.replacen("urn:pair#","urn:other#",1));
        let changed = Statements::of(&scan(&changed).unwrap(),&changed);
        assert!(base.exact_union_pair(&old,&changed).is_none());
        assert!(base.exact_union_pair(&new,&new).is_none());
        let mut collided = Statements::of(&scan(&new.text).unwrap(),&new.text);
        collided.collision = true;
        assert!(base.exact_union_pair(&old,&collided).is_none());
        // A forged matching hash must still compare exact statement bytes.
        let changed = Arc::new(new.text.replace("ClassAssertion(:K :a)","ClassAssertion(:B :a)"));
        let mut forged = Statements::of(&scan(&changed).unwrap(),&changed);
        let entry = forged.counts.remove(&fingerprint(b"ClassAssertion(:B :a)")).unwrap();
        forged.counts.insert(fingerprint(b"ClassAssertion(:K :a)"),entry);
        assert!(base.exact_union_pair(&old,&forged).is_none());
        assert!(base.exact_union_pair(&old,&new).is_some());
    }

    #[test]
    fn pending_union_materializes_exact_new_before_nominal_full_index_reuse() {
        let make = |body: &str| Arc::new(format!("Prefix(:=<urn:prepared#>) Ontology(Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C)) Declaration(Class(:K)) Declaration(ObjectProperty(:r)) Declaration(NamedIndividual(:a)) {body})"));
        let nominal = "SubClassOf(:A ObjectSomeValuesFrom(:r ObjectOneOf(:a)))";
        let union_text = make(&format!("{nominal} SubClassOf(:B :C) SubClassOf(owl:Thing :A) ClassAssertion(:K :a)"));
        let union_scan = scan(&union_text).unwrap();
        let union = Arc::new(LocalityIndex::build(&union_text, &union_scan, false).unwrap());
        let removed = fingerprint(b"SubClassOf(:B :C)");
        assert!(union.axiom_by_hash.contains_key(&removed));
        let new_text = make(&format!("{nominal} SubClassOf(owl:Thing :A) ClassAssertion(:K :a)"));
        let new_scan = scan(&new_text).unwrap();
        let mut work = PreparationWork::default();
        let pending = PreparedCompiler::Union { source: union_text, scan: union_scan, index: union.clone() };
        let exact = pending.into_exact(&new_text, &new_scan, &mut work).unwrap();
        assert!(!Arc::ptr_eq(&exact, &union));
        assert_eq!(exact.axiom_count(), 3);
        assert!(!exact.axiom_by_hash.contains_key(&removed));
        assert_eq!(work.index_build_calls, 1);
        assert_eq!(work.same_update_compiled_axioms, 3);
        assert_eq!(work.cross_revision_compiled_axioms, 0);
        let mut base = BaseState {
            statements: Arc::new(Statements::of(&new_scan, &new_text)),
            source: Some((new_text.clone(), new_scan.clone())), index: None,
            admission: None,
            compiler_full: Some(exact.clone()), disabled: Arc::from([]), full_disabled: Arc::from([]),
            removed_hashes: Arc::new(FxHashSet::default()), class_domain: Some(Arc::new(class_domain(&exact))),
            full: None, told: None, consistent: true, witness: None,
            anonymous: FxHashSet::default(), source_bytes: new_text.len(),
        };
        assert!(base.index(&mut work).is_some());
        assert!(Arc::ptr_eq(base.full.as_ref().unwrap(), &exact));
        assert_eq!(base.full_disabled.len(), exact.axiom_count());
        assert!(base.full_disabled.iter().all(|disabled| !disabled));
        assert!(!base.full.as_ref().unwrap().axiom_by_hash.contains_key(&removed));
        let mut no_work = PreparationWork::default();
        let reused = PreparedCompiler::Exact(exact.clone()).into_exact(&new_text, &new_scan, &mut no_work).unwrap();
        assert!(Arc::ptr_eq(&reused, &exact));
        assert_eq!(no_work.index_build_calls, 0);
    }

    #[test]
    fn mixed_union_donor_callback_excludes_historical_disabled_formulas() {
        let make = |body: &str| Arc::new(format!("Prefix(:=<urn:donor#>) Ontology(Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C)) Declaration(Class(:E)) Declaration(Class(:F)) Declaration(Class(:G)) {body})"));
        let historical = make("SubClassOf(:A :B) SubClassOf(:E :F) SubClassOf(:F :G)");
        let historical_scan = scan(&historical).unwrap();
        let donor = Arc::new(LocalityIndex::build(&historical, &historical_scan, false).unwrap());
        let old_text = make("SubClassOf(:A :B) SubClassOf(:E :F)");
        let old = Statements::of(&scan(&old_text).unwrap(), &old_text);
        let union_text = make("SubClassOf(:A :B) SubClassOf(:E :F) SubClassOf(:F :G) SubClassOf(:B :C)");
        let union_scan = scan(&union_text).unwrap();
        let mut work = PreparationWork::default(); work.prior_compilers.push(donor.clone());
        let actual = work.build_reusing_full(&union_text, &union_scan, &donor, old.header(), |h| old.stmt(&h)).unwrap();
        assert_eq!(actual.axiom_count(), 4);
        assert_eq!(work.cross_revision_compiled_axioms, 2);
        // Historical F<=G exists physically but was absent from exact OLD.
        assert_eq!(work.compiled_locality_axioms, 2);
        assert_eq!(work.same_update_compiled_axioms, 0);
        assert_eq!(work.csr_axiom_records, 4);
        let fresh = LocalityIndex::build(&union_text, &union_scan, false).unwrap();
        assert_eq!(class_domain(&actual), class_domain(&fresh));
    }
    #[test]
    fn consistent_fallback_retains_masked_union_without_second_build() {
        let make = |body: &str| Arc::new(format!("Prefix(:=<urn:masked#>) Ontology(Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:K)) Declaration(ObjectProperty(:r)) Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:C)) {body})"));
        let nominal = "SubClassOf(:A ObjectSomeValuesFrom(:r ObjectOneOf(:a)))";
        let removed_global = "SubClassOf(owl:Thing :B)";
        let removed_class = "SubClassOf(:C :B)";
        let union_text = make(&format!("{nominal} {removed_global} {removed_class} ClassAssertion(:K :C) SubClassOf(:B :K)"));
        let union_scan = scan(&union_text).unwrap();
        let index = Arc::new(LocalityIndex::build(&union_text, &union_scan, false).unwrap());
        let pending = PreparedCompiler::Union { source: union_text.clone(), scan: union_scan, index: index.clone() };
        let new_text = make(&format!("{nominal} ClassAssertion(:K :C) SubClassOf(:B :K)"));
        let new_scan = scan(&new_text).unwrap();
        let statements = Arc::new(Statements::of(&new_scan, &new_text));
        let mut base = pending.consistent_union_base(&new_text, &new_scan, statements.clone()).unwrap();
        assert!(base.told.is_none(), "fallback must not eagerly parse proof supports");
        let mut work = PreparationWork::default();
        assert!(base.index(&mut work).is_some());
        let told = base.told.as_ref().unwrap().clone();
        assert!(told.preparation.parsed_statements > 0);
        assert_eq!(told.preparation.reused_statements, 0);
        assert!(base.index(&mut work).is_some());
        assert!(Arc::ptr_eq(base.told.as_ref().unwrap(), &told));
        assert_eq!(work.index_build_calls, 0);
        assert!(base.source.is_none());
        assert!(Arc::ptr_eq(base.index.as_ref().unwrap().as_ref().unwrap(), &index));
        assert!(Arc::ptr_eq(base.compiler_full.as_ref().unwrap(), &index));
        let fresh = LocalityIndex::build(&new_text, &new_scan, false).unwrap();
        assert_eq!(base.class_domain.as_deref().unwrap(), &class_domain(&fresh));
        assert!(!base.class_domain.as_ref().unwrap().contains(":C"));
        for statement in [removed_global, removed_class] {
            assert!(base.removed_hashes.contains(&fingerprint(statement.as_bytes())));
        }
        assert_eq!(base.told.as_ref().unwrap().statements.text.as_str(), new_text.as_str());
        let compare = |base: &BaseState, text: &str| {
            let fresh = LocalityIndex::build(text, &scan(text).unwrap(), false).unwrap();
            let shared = base.index.as_ref().unwrap().as_ref().unwrap();
            for seed in fresh.names.iter().map(|name| Some(name.as_ref())).chain(std::iter::once(None)) {
                let module = |ix: &LocalityIndex, disabled: &[bool]| {
                    let seeds: Vec<_> = seed.into_iter().map(|name| ix.named(name).unwrap()).collect();
                    let (module, signature) = ix.module(&seeds, disabled);
                    let hashes = module.into_iter().map(|id| ix.axiom_hash[id as usize]).collect::<BTreeSet<_>>();
                    let names = ix.symbols.iter().zip(signature).filter(|(_, present)| *present)
                        .map(|(name, _)| name.to_string()).collect::<BTreeSet<_>>();
                    (hashes, names)
                };
                assert_eq!(module(shared, &base.disabled), module(&fresh, &vec![false; fresh.axiom_count()]), "seed {seed:?}");
            }
        };
        compare(&base, &new_text);
        assert!(told.proofs.proves_all(":B", &[":K"], &FxHashSet::default()));
        let deleted_text = make("ClassAssertion(:K :C)");
        let deleted_scan = scan(&deleted_text).unwrap();
        let mut deleted = base.after_deletion(Arc::new(Statements::of(&deleted_scan, &deleted_text)), &[fingerprint(nominal.as_bytes()), fingerprint(b"SubClassOf(:B :K)")]);
        assert!(deleted.index(&mut work).is_some());
        assert!(Arc::ptr_eq(deleted.told.as_ref().unwrap(), &told));
        assert!(!deleted.told.as_ref().unwrap().proofs.proves_all(":B", &[":K"], &deleted.removed_hashes));
        compare(&deleted, &deleted_text);
        // Preparing/dropping a candidate cannot alter the published donor's masks.
        assert_eq!(base.disabled.iter().filter(|disabled| **disabled).count(), 2);
        drop(deleted);
        compare(&base, &new_text);
        // A physically retained historical formula is not an enabled donor.
        let mut reuse = PreparationWork::default(); reuse.prior_compilers.push(index.clone());
        let restored = reuse.build_reusing_full(&union_text, &scan(&union_text).unwrap(), &index,
            statements.header(), |hash| statements.stmt(&hash)).unwrap();
        assert_eq!(reuse.compiled_locality_axioms, 2);
        assert_eq!(reuse.cross_revision_compiled_axioms, fresh.axiom_count());
        assert_eq!(class_domain(&restored), class_domain(&index));
        base.index = Some(None);
        base.told = None;
        assert!(base.index(&mut work).is_none());
        assert!(base.told.is_none(), "failed semantic indexes must not prepare lazy proofs");
    }

    #[test]
    fn consistent_fallback_refuses_conflicted_union_without_consuming_exact_recovery() {
        let text = Arc::new("Prefix(:=<urn:conflict#>) Ontology(Declaration(Class(:A)) SubClassOf(:A <urn:conflict#A>))".to_string());
        let scanned = scan(&text).unwrap();
        let index = Arc::new(LocalityIndex::build(&text, &scanned, false).unwrap());
        assert!(index.spelling_conflict);
        let pending = PreparedCompiler::Union { source: text.clone(), scan: scanned.clone(), index };
        assert!(pending.consistent_union_base(&text, &scanned,
            Arc::new(Statements::of(&scanned, &text))).is_none());
        let mut work = PreparationWork::default();
        assert!(pending.into_exact(&text, &scanned, &mut work).is_some());
        assert_eq!(work.index_build_calls, 1);
        let exact = PreparedCompiler::Exact(Arc::new(LocalityIndex::build(&text, &scanned, false).unwrap()));
        assert!(exact.consistent_union_base(&text, &scanned,
            Arc::new(Statements::of(&scanned, &text))).is_none());
    }

    #[test]
    fn declined_common_admission_remains_transaction_local_and_keeps_origin_provenance() {
        const CHILD: &str = "KM_INCR_ADMISSION_FALLBACK_TEST_CHILD";
        if std::env::var(CHILD).as_deref() != Ok("1") {
            let mut command = std::process::Command::new(std::env::current_exe().unwrap());
            for (key, _) in std::env::vars_os() {
                if key.to_string_lossy().starts_with("KM_") { command.env_remove(key); }
            }
            let output = command.args(["--exact",
                    "incr_session::tests::declined_common_admission_remains_transaction_local_and_keeps_origin_provenance",
                    "--nocapture", "--test-threads=1"])
                .env(CHILD, "1").env("KM_CACHE_CONFORMANCE", "1")
                .output().expect("launch isolated admission fallback test");
            assert!(output.status.success(), "isolated admission fallback failed:\n{}\n{}",
                String::from_utf8_lossy(&output.stdout), String::from_utf8_lossy(&output.stderr));
            assert!(String::from_utf8_lossy(&output.stdout).contains("1 passed; 0 failed"));
            return;
        }
        let origin = certificate_source("SubClassOf(owl:Thing :A) SubClassOf(owl:Thing :B)");
        crate::frontend::conformance::check_user_source(&origin.text).unwrap();
        let origin_certificate = crate::named_subclass_validation::NamedSubclassCertificate::capture_scanned(
            origin.text.clone(), &scan(&origin.text).unwrap()).unwrap();
        let old = certificate_source("SubClassOf(owl:Thing :A)");
        let old_scan = scan(&old.text).unwrap();
        let old_certificate = Arc::new(origin_certificate.derive_scanned(old.text.clone(), &old_scan).unwrap());
        let old_index = Arc::new(LocalityIndex::build(&old.text, &old_scan, false).unwrap());
        let old_pending = PreparedCompiler::Union { source: old.text.clone(), scan: old_scan.clone(), index: old_index };
        let mut base = old_pending.consistent_union_base(&old.text, &old_scan, old.clone()).unwrap();
        base.admission = Some(old_certificate.clone());
        let mut session = Session::new();
        session.insert(Revision { text: old.text.clone(), statements: Some(old.clone()),
            text_key: fingerprint(old.text.as_bytes()), content_key: old_scan.content_key(),
            taxonomy: Arc::new(Taxonomy::empty()), inconsistency: None, base: Some(base), last_use: 0 });
        let before = (session.current, session.clock, session.memo.len());
        let new = certificate_source("SubClassOf(owl:Thing :B)");
        let new_scan = scan(&new.text).unwrap();
        let mut work = PreparationWork::default();
        let mut pending = None;
        let mut admission = None;
        let result = session.common_module_update(&new.text, &new_scan, &new, Instant::now(),
            statement_delta(&old, &new), &mut work, &mut pending, &mut admission, &mut None, &mut None, classify_process_json);
        assert!(matches!(result, Err(ref reason) if reason == "changed axiom belongs to the union empty-signature module"));
        let passed = admission.unwrap();
        // This certificate is derived from the verified origin, rather than
        // forged by inserting NEW into the process-wide validation cache.
        assert!(!crate::frontend::conformance::cached_user_source_accepted(&new.text));
        assert!(passed.derive_scanned(origin.text.clone(), &scan(&origin.text).unwrap()).is_some());
        let changed_header = Arc::new(new.text.replacen("urn:cert#", "urn:other#", 1));
        assert!(passed.derive_scanned(changed_header.clone(), &scan(&changed_header).unwrap()).is_none());
        assert_eq!(before, (session.current, session.clock, session.memo.len()));
        assert!(Arc::ptr_eq(session.memo[0].base.as_ref().unwrap().admission.as_ref().unwrap(), &old_certificate));
        let mut candidate = pending.as_ref().unwrap().consistent_union_base(&new.text, &new_scan, new.clone()).unwrap();
        candidate.admission = Some(passed.clone());
        assert!(Arc::ptr_eq(candidate.admission.as_ref().unwrap(), &passed));
        // Failure/drop before publication never changes the committed origin.
        drop(candidate); drop(pending);
        let invalid = certificate_source("SubClassOf(:A :Undeclared)");
        let mut invalid_pending = None;
        let mut invalid_admission = None;
        assert!(session.common_module_update(&invalid.text, &scan(&invalid.text).unwrap(), &invalid,
            Instant::now(), statement_delta(&old, &invalid), &mut work,
            &mut invalid_pending, &mut invalid_admission, &mut None, &mut None, classify_process_json).is_err());
        assert!(invalid_admission.is_none() && invalid_pending.is_none());
        assert_eq!(before, (session.current, session.clock, session.memo.len()));
    }

    #[test]
    fn nominal_common_marks_every_data_owner_including_shared_iri_punning() {
        let make=|body:&str| Arc::new(format!("Prefix(:=<urn:punned#>) Ontology(Declaration(Class(:P)) Declaration(DataProperty(:P)) Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C)) {body})"));
        let old_text=make("SubClassOf(:A :P) DataPropertyRange(:P xsd:string)");
        let new_text=make("SubClassOf(:A :P) DataPropertyRange(:P xsd:string) SubClassOf(:B :C)");
        let old=Statements::of(&scan(&old_text).unwrap(),&old_text);
        let new_scan=scan(&new_text).unwrap();
        let new=Statements::of(&new_scan,&new_text);
        let eligible=crate::incr_envelope::eligible(&new_text,&new_scan).unwrap();
        let data=fingerprint(b"DataPropertyRange(:P xsd:string)");
        assert!(eligible.data_tbox.contains(&data));
        let index=LocalityIndex::build(&new_text,&new_scan,true).unwrap();
        assert!(index.tbox_mode);
        let old_full=LocalityIndex::build(&old_text,&scan(&old_text).unwrap(),false).unwrap();
        let new_full=LocalityIndex::build(&new_text,&new_scan,false).unwrap();
        let old_domain=class_domain(&old_full);let new_domain=class_domain(&new_full);
        let names=nominal_common_subjects(&index,&old,&new,&old_domain,&new_domain,&eligible.data_tbox).unwrap();
        assert!(names.iter().any(|name|name==":P"));
        assert!(names.iter().any(|name|name==":A"));
        // Without the mandatory data mark this punned module would be reused.
        let changes:Vec<_>=index.axiom_hash.iter().map(|hash|old.counts.contains_key(hash)!=new.counts.contains_key(hash)).collect();
        let without=index.affected_classes_tbox(&changes).unwrap();
        let p=index.named(":P").unwrap();assert!(!without.contains(&p));
        assert!(index.module(&[p],&vec![false;index.axiom_count()]).0.iter().any(|id|index.axiom_hash[*id as usize]==data));
        for name in new_domain.iter().filter(|name|!names.iter().any(|n|n==name.as_ref())) {
            let Some(seed)=index.named(name) else {continue};
            let (module,_)=index.module(&[seed],&vec![false;index.axiom_count()]);
            assert!(module.iter().all(|id|!eligible.data_tbox.contains(&index.axiom_hash[*id as usize])));
            assert!(!index.module_has_nominal(&module));
        }
    }

    #[test]
    fn object_certificate_uses_old_core_and_declares_uncovered_requested_classes() {
        let make=|body:&str|Arc::new(format!("Prefix(:=<urn:object-module#>) Ontology(Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:K)) Declaration(NamedIndividual(:a)) {body})"));
        let old_text=make("SubClassOf(owl:Thing :A) ClassAssertion(:K :a) ClassAssertion(rdfs:Resource :a)");
        let new_text=make("SubClassOf(owl:Thing :A) ClassAssertion(rdfs:Resource :a)");
        let union_scan=scan(&old_text).unwrap();let new_scan=scan(&new_text).unwrap();
        let old=Statements::of(&union_scan,&old_text);let new=Statements::of(&new_scan,&new_text);
        let full=LocalityIndex::build(&old_text,&union_scan,false).unwrap();
        let tbox=LocalityIndex::build(&old_text,&union_scan,true).unwrap();
        let eligible=crate::incr_envelope::eligible(&old_text,&union_scan).unwrap();
        assert!(eligible.object_only);
        let removed:Vec<_>=full.axiom_hash.iter().map(|hash|!new.counts.contains_key(hash)).collect();
        assert!(!full.empty_module_avoids(&removed),"removed OLD assertion belongs to full empty core");
        assert!(tbox.named("rdfs:Resource").is_none());
        let names=vec!["rdfs:Resource".into(),"owl:Thing".into(),"owl:Nothing".into(),
            "http://www.w3.org/2002/07/owl#Thing".into(),"http://www.w3.org/2002/07/owl#Nothing".into()];
        let (module,count)=object_common_module(&new_text,&new_scan,&old,&new,&full,&tbox,&names,&eligible).unwrap();
        assert!(count>0,"module includes NEW empty-signature core even without a known subject seed");
        assert!(module.contains("SubClassOf(owl:Thing :A)"));
        assert!(!module.contains("ClassAssertion"));
        assert!(module.contains("Declaration(Class(rdfs:Resource))"));
        for token in ["owl:Thing","owl:Nothing","<http://www.w3.org/2002/07/owl#Thing>","<http://www.w3.org/2002/07/owl#Nothing>"] {
            assert!(module.contains(&format!("Declaration(Class({token}))")));
        }
        assert!(crate::source_reuse_grammar::outer_grammar(&module, &scan(&module).unwrap()));
        // No requested rows is still a real module containing the empty core.
        assert!(object_common_module(&new_text,&new_scan,&old,&new,&full,&tbox,&[],&eligible).unwrap().0.contains("SubClassOf(owl:Thing :A)"));
        let nominal_text=make("SubClassOf(owl:Thing :A) EquivalentClasses(:B ObjectOneOf(:a))");
        let nominal_scan=scan(&nominal_text).unwrap();let nominal=Statements::of(&nominal_scan,&nominal_text);
        let nf=LocalityIndex::build(&nominal_text,&nominal_scan,false).unwrap();
        let nt=LocalityIndex::build(&nominal_text,&nominal_scan,true).unwrap();
        let ne=crate::incr_envelope::eligible(&nominal_text,&nominal_scan).unwrap();
        assert!(object_common_module(&nominal_text,&nominal_scan,&nominal,&nominal,&nf,&nt,&[":B".into()],&ne).is_none(),"affected nominal module requires full NEW classification");
    }


    // ---- row-delta answers -------------------------------------------------

    fn tax_of(iris: &[&str], rows: Vec<(u32, Vec<u32>)>, unsat: &[&str]) -> Taxonomy {
        Taxonomy::from_rows(TaxonomyRows {
            consistent: true, dropped: 0,
            unsatisfiable: unsat.iter().map(|s| s.to_string()).collect(),
            iris: iris.iter().map(|s| Arc::<str>::from(*s)).collect(), rows,
        })
    }

    fn delta_value(new: &Taxonomy, prev: &Taxonomy) -> serde_json::Value {
        let mut out = Vec::new();
        new.publish_delta(prev, 3, &mut out).unwrap();
        serde_json::from_slice(&out).unwrap()
    }

    /// Superclass sets by subject, from a full or a delta-patched answer.
    type Pairs = std::collections::BTreeMap<String, std::collections::BTreeSet<String>>;

    fn pairs_of(tax: &Taxonomy) -> Pairs {
        let mut out = Vec::new();
        tax.publish(&mut out).unwrap();
        pairs_of_value(&serde_json::from_slice(&out).unwrap())
    }

    fn pairs_of_value(v: &serde_json::Value) -> Pairs {
        let mut m = Pairs::new();
        for p in v["subsumptions"].as_array().unwrap() {
            m.entry(p[0].as_str().unwrap().into()).or_default().insert(p[1].as_str().unwrap().into());
        }
        m
    }

    fn patch(base: &mut Pairs, delta: &serde_json::Value) {
        for r in delta["rows"].as_array().unwrap() {
            let o: std::collections::BTreeSet<String> =
                r["o"].as_array().unwrap().iter().map(|x| x.as_str().unwrap().into()).collect();
            let s = r["s"].as_str().unwrap().to_string();
            if o.is_empty() { base.remove(&s); } else { base.insert(s, o); }
        }
    }

    #[test]
    fn delta_of_identical_taxonomy_is_empty() {
        let t = tax_of(&["http://e/A", "http://e/B"], vec![(0, vec![1])], &["http://e/U"]);
        let d = delta_value(&t.clone(), &t);
        assert_eq!(d["delta"], true);
        assert_eq!(d["base_revision"], 3);
        assert_eq!(d["rows"], serde_json::json!([]));
        assert_eq!(d["unsatisfiable"], serde_json::json!(["http://e/U"]));
    }

    #[test]
    fn delta_removes_subjects_and_patches_rows_aligned_and_unaligned() {
        let prev = tax_of(&["http://e/A", "http://e/B\"q", "http://e/C"],
            vec![(0, vec![1, 2]), (2, vec![1])], &[]);
        // Aligned: same ids, one row shrinks and one subject loses its row.
        let mut next = prev.clone();
        next.rows[0] = Some(vec![1u32].into());
        next.rows[2] = None;
        next.rendered = std::sync::OnceLock::new();
        let d = delta_value(&next, &prev);
        let mut state = pairs_of(&prev);
        patch(&mut state, &d);
        assert_eq!(state, pairs_of(&next));
        assert!(d["rows"].as_array().unwrap().iter().any(|r| r["s"] == "http://e/C" && r["o"] == serde_json::json!([])));
        // Unaligned: different id order, an IRI dropped altogether, a new one added.
        let other = tax_of(&["http://e/D", "http://e/B\"q", "http://e/A"],
            vec![(2, vec![1, 0]), (0, vec![1])], &["http://e/D"]);
        let d = delta_value(&other, &prev);
        let mut state = pairs_of(&prev);
        patch(&mut state, &d);
        assert_eq!(state, pairs_of(&other));
        assert!(d["rows"].as_array().unwrap().iter().any(|r| r["s"] == "http://e/C" && r["o"] == serde_json::json!([])));
        assert_eq!(d["unsatisfiable"], serde_json::json!(["http://e/D"]));
    }

    fn ofn(axioms: &str) -> String {
        format!("Prefix(:=<urn:d:>) Ontology(<urn:d:o> Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C)) {axioms})")
    }

    fn session_lines(commands: &[serde_json::Value]) -> Vec<serde_json::Value> {
        let input = commands.iter().map(|c| c.to_string()).collect::<Vec<_>>().join("\n") + "\n";
        let mut out = Vec::new();
        run_jsonl_session(std::io::Cursor::new(input), &mut out).unwrap();
        String::from_utf8(out).unwrap().lines().map(|l| serde_json::from_str(l).unwrap()).collect()
    }

    /// The pipeline rewrites process-wide KM_* settings, so the session protocol
    /// tests run alone in a child process (as the admission tests above do).
    #[test]
    fn session_row_delta_protocol_runs_isolated() {
        const CHILD: &str = "KM_INCR_ROW_DELTA_TEST_CHILD";
        if std::env::var(CHILD).as_deref() != Ok("1") {
            let mut command = std::process::Command::new(std::env::current_exe().unwrap());
            for (key, _) in std::env::vars_os() {
                if key.to_string_lossy().starts_with("KM_") { command.env_remove(key); }
            }
            let output = command.args(["--exact", "incr_session::tests::session_row_delta_protocol_runs_isolated",
                    "--nocapture", "--test-threads=1"])
                .env(CHILD, "1").output().expect("launch isolated row-delta test");
            assert!(output.status.success(), "isolated row-delta protocol failed:\n{}\n{}",
                String::from_utf8_lossy(&output.stdout), String::from_utf8_lossy(&output.stderr));
            assert!(String::from_utf8_lossy(&output.stdout).contains("1 passed; 0 failed"));
            return;
        }
        session_delta_mismatch_failure_and_recovery_equal_full_answers();
        session_delta_after_refused_update_uses_last_published_revision();
    }

    fn session_delta_mismatch_failure_and_recovery_equal_full_answers() {
        use serde_json::json;
        let src = [
            ofn("SubClassOf(:A :B)"),
            ofn("SubClassOf(:A :B) SubClassOf(:B :C)"),
            ofn("SubClassOf(:A :B) SubClassOf(:B :C)"),
            ofn("SubClassOf(:B :C)"),
            ofn("SubClassOf(:A :B)"),
        ];
        let lines = session_lines(&[
            json!({"op":"init","functional_syntax":src[0]}),
            json!({"op":"replace","functional_syntax":src[1],"base_revision":1}),   // delta
            json!({"op":"replace","functional_syntax":src[2],"base_revision":2}),   // empty delta
            json!({"op":"replace","functional_syntax":"Ontology(","base_revision":3}), // refused
            json!({"op":"replace","functional_syntax":src[3],"base_revision":99}),  // mismatch: full
            json!({"op":"replace","functional_syntax":src[4],"base_revision":4}),   // delta again
            json!({"op":"replace","functional_syntax":src[0]}),                     // no base: full
        ]);
        // Independent sessions give the reference full answers.
        let reference: Vec<Pairs> = src.iter().map(|s| {
            let l = session_lines(&[json!({"op":"init","functional_syntax":s})]);
            pairs_of_value(&l[0]["result"])
        }).collect::<Vec<_>>();
        assert_eq!(lines[0]["result"].get("delta"), None);
        let mut state = pairs_of_value(&lines[0]["result"]);
        assert_eq!(state, reference[0]);
        assert_eq!(lines[1]["result"]["delta"], true);
        patch(&mut state, &lines[1]["result"]);
        assert_eq!(state, reference[1]);
        assert_eq!(lines[2]["result"]["delta"], true);
        assert_eq!(lines[2]["result"]["rows"], json!([]));
        assert_eq!(lines[3]["status"], "error");
        // The refused update left revision 3 published: base_revision 3 still matches,
        // but this request carries 99 and receives the complete answer.
        assert_eq!(lines[4]["result"].get("delta"), None);
        assert_eq!(lines[4]["revision"], 4);
        state = pairs_of_value(&lines[4]["result"]);
        assert_eq!(state, reference[3]);
        assert_eq!(lines[5]["result"]["delta"], true);
        assert_eq!(lines[5]["result"]["base_revision"], 4);
        patch(&mut state, &lines[5]["result"]);
        assert_eq!(state, reference[4]);
        assert_eq!(lines[6]["result"].get("delta"), None);
        assert_eq!(pairs_of_value(&lines[6]["result"]), reference[0]);
    }

    fn session_delta_after_refused_update_uses_last_published_revision() {
        use serde_json::json;
        let lines = session_lines(&[
            json!({"op":"init","functional_syntax":ofn("SubClassOf(:A :B)")}),
            json!({"op":"replace","functional_syntax":"Ontology(","base_revision":1}),
            json!({"op":"replace","functional_syntax":ofn("SubClassOf(:A :C)"),"base_revision":1}),
        ]);
        assert_eq!(lines[1]["status"], "error");
        assert_eq!(lines[2]["result"]["delta"], true);
        assert_eq!(lines[2]["result"]["base_revision"], 1);
        assert_eq!(lines[2]["revision"], 2);
    }
}
