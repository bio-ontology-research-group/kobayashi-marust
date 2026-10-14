//! Retained `km incremental-source` session with exact work reuse.
//!
//! Every published answer comes from the unchanged `km classify` pipeline
//! (`orchestrate::classify_json`, automatic routing, production budgets), run
//! in-process either on the complete revision or on a ⊥-locality module of it.
//! Reuse never decides an entailment itself:
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
//!    the complete revision is classified. The TBox-mode index of a
//!    consistent base reads nominals as empty: a subject whose module
//!    mentions a nominal is affected, and when the remaining subjects' module
//!    mentions one (or is most of a non-EL revision), the complete revision
//!    is classified with the bridge's subject probes restricted to them.
//! 3. Otherwise the complete revision is classified.
//!
//! Lean: `ContextCalculus.IncrementalModuleReuse` (module transfer, deletion
//! monotonicity, the merge of retained and recomputed rows, and
//! `nominal_unaffected_query` / `nominal_module_outside` for nominal TBoxes).

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

/// A small subset of the logical statements that the pipeline classifies as
/// inconsistent (QuickXplain over the module of the empty signature), or
/// `None`. The final subset is re-classified; only a verified one is kept.
fn inconsistency_witness(text: &str, scanned: &Scan, budget_seconds: f64) -> Option<Vec<u128>> {
    let index = LocalityIndex::build(text, scanned, false).ok()?;
    let core: FxHashSet<u128> = index.empty_module_statements().into_iter().collect();
    let mut header = String::from(&text[..scanned.open_end]);
    header.push('\n');
    let mut candidates: Vec<(u128, &str)> = Vec::new();
    let mut seen: FxHashSet<u128> = FxHashSet::default();
    for st in &scanned.statements {
        match st.kind {
            StmtKind::Declaration => {
                header.push_str(&text[st.start..st.end]);
                header.push('\n');
            }
            StmtKind::Logical | StmtKind::Assertion if core.contains(&st.hash) && seen.insert(st.hash) => {
                candidates.push((st.hash, &text[st.start..st.end]));
            }
            _ => {}
        }
    }
    let mut checks = 0usize;
    let deadline = Instant::now() + std::time::Duration::from_secs_f64(budget_seconds);
    // `Some(true)` only for a verified inconsistent answer within the per-check
    // limit; a timeout or any other outcome keeps the statements (`Some(false)`).
    // `None` ends the search (budget or check count exhausted).
    let mut per_check = std::time::Duration::from_secs_f64(budget_seconds);
    let mut inconsistent = |subset: &[(u128, &str)], per_check: std::time::Duration| -> Option<bool> {
        checks += 1;
        if checks > WITNESS_MAX_CHECKS {
            return None;
        }
        let remaining = deadline.saturating_duration_since(Instant::now());
        if remaining.is_zero() {
            return None;
        }
        let mut doc = header.clone();
        for (_, s) in subset {
            doc.push_str(s);
            doc.push('\n');
        }
        doc.push_str(")\n");
        // A subset can be far harder than the whole: run each check as a
        // separate `km classify` process under a deadline.
        let t = Instant::now();
        let verdict = classify_process_inconsistent(&doc, remaining.min(per_check));
        if std::env::var_os("KM_INCR_DEBUG_WITNESS").is_some() {
            eprintln!("witness check {} statements={} verdict={verdict:?} seconds={:.3}", checks, subset.len(), t.elapsed().as_secs_f64());
        }
        Some(verdict.unwrap_or(false))
    };
    // Deletion filter with halving chunks: drop a chunk only when the rest is
    // still verified inconsistent. Large still-inconsistent sets are what the
    // pipeline decides fastest; a check that is slower than a few times the
    // complete document is treated as "keep" instead of waited for.
    let started = Instant::now();
    if !inconsistent(&candidates, per_check)? {
        return None;
    }
    per_check = std::time::Duration::from_secs_f64(5.0 * started.elapsed().as_secs_f64() + 0.05);
    let mut current = candidates;
    let mut chunk = current.len().div_ceil(2);
    while chunk >= 1 && current.len() > 1 {
        let mut i = 0;
        while i < current.len() {
            let end = (i + chunk).min(current.len());
            let trial: Vec<(u128, &str)> = current[..i].iter().chain(&current[end..]).copied().collect();
            match inconsistent(&trial, per_check) {
                Some(true) => current = trial,
                Some(false) => i = end,
                None => break,
            }
        }
        if chunk == 1 || deadline <= Instant::now() {
            break;
        }
        chunk = chunk.div_ceil(2).max(1).min(chunk - 1).max(1);
    }
    let witness = current;
    // Every accepted step was itself a verified inconsistent subset; the
    // final set is the last accepted one (or the verified complete core).
    Some(witness.into_iter().map(|(h, _)| h).collect())
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
    rendered: std::sync::OnceLock<Vec<u8>>,
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
        let bytes = self.rendered.get_or_init(|| bytes);
        w.write_all(bytes)
    }

    fn pair_count(&self) -> usize {
        self.rows.iter().map(|r| r.as_ref().map_or(0, |v| v.len())).sum()
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

struct Revision {
    /// The exact revision text; a `text_key` hit is confirmed against it.
    text: Arc<String>,
    /// Its statements (`None` when the scan failed); a `content_key` hit is
    /// confirmed with `Statements::exact_eq`.
    statements: Option<Arc<Statements>>,
    text_key: u128,
    content_key: u128,
    taxonomy: Arc<Taxonomy>,
    /// Present for completely classified revisions that can serve as a
    /// deletion base: their statements, and their source until the locality
    /// index is built.
    base: Option<BaseState>,
    last_use: u64,
}

struct BaseState {
    statements: Arc<Statements>,
    source: Option<(Arc<String>, Scan)>,
    index: Option<Option<LocalityIndex>>,
    /// The full (assertion-keeping) index, built next to a TBox-mode index
    /// that has nominal axioms: a deletion whose empty-signature module in it
    /// avoids the removed statements keeps the plain module path, which the
    /// nominal TBox index would send to the complete revision.
    full: Option<LocalityIndex>,
    /// Told proofs of this revision, built with the index; a deletion masks
    /// its removed statements.
    told: Option<crate::source_locality::ToldProofs>,
    consistent: bool,
    /// Statements of a subset verified inconsistent by the pipeline.
    witness: Option<Vec<u128>>,
    /// Object-property assertions that mention an anonymous individual.
    anonymous: FxHashSet<u128>,
    /// Byte length of the source (selects the pipeline's in-process arms).
    source_bytes: usize,
}

impl BaseState {
    fn index(&mut self) -> Option<&LocalityIndex> {
        if self.index.is_none() {
            let consistent = self.consistent;
            let mut full = None;
            let mut told = None;
            let built = self.source.take().and_then(|(text, s)| {
                if consistent {
                    told = Some(crate::source_locality::ToldProofs::build(&text, &s));
                }
                // TBox mode needs both revisions consistent: a deletion from
                // a consistent base. An inconsistent base keeps assertions.
                let ix = LocalityIndex::build(&text, &s, consistent).ok()?;
                if ix.tbox_mode && ix.nominal.iter().any(|n| *n) {
                    full = LocalityIndex::build(&text, &s, false).ok();
                }
                Some(ix)
            });
            self.index = Some(built);
            self.full = full;
            self.told = told;
        }
        self.index.as_ref().and_then(|i| i.as_ref())
    }
}

pub struct Session {
    memo: Vec<Revision>,
    current: Option<usize>,
    revision: u64,
    clock: u64,
}

#[derive(Default)]
struct Receipt {
    strategy: &'static str,
    base_revision_statements: usize,
    removed_statements: usize,
    removed_axioms: usize,
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
    let rows = classify_rows_with(text, settings)?;
    let started = Instant::now();
    let tax = Taxonomy::from_rows(rows);
    stage("rows indexed", started);
    Ok(tax)
}

/// The pipeline's grouped answer, before indexing.
fn classify_rows_with(text: &str, settings: &[(&str, &str)]) -> Result<TaxonomyRows, String> {
    let started = Instant::now();
    let path = crate::orchestrate::tmpfile::TempPath::new(".ofn");
    std::fs::write(path.path(), text).map_err(|e| e.to_string())?;
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
        Session { memo: Vec::new(), current: None, revision: 0, clock: 0 }
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
        let text: Arc<String> = Arc::new(text);
        let text_key = fingerprint(text.as_bytes());
        if let Some(i) = self.memo.iter().position(|r| r.text_key == text_key && *r.text == *text) {
            self.touch(i);
            let receipt = Receipt { strategy: "exact_reuse", seconds: started.elapsed().as_secs_f64(), ..Default::default() };
            return Ok((self.memo[i].taxonomy.clone(), receipt));
        }
        stage("text fingerprint", started);
        let scanned = scan(&text);
        stage("scan", started);
        let Ok(scanned) = scanned else {
            // Not reusable: the pipeline reports the precise source error.
            let tax = Arc::new(classify_text(&text)?);
            let receipt = Receipt { strategy: "full_classify", fallback_reason: scanned.err(), seconds: started.elapsed().as_secs_f64(), ..Default::default() };
            self.insert(Revision { text: text.clone(), statements: None, text_key, content_key: 0, taxonomy: tax.clone(), base: None, last_use: 0 });
            return Ok((tax, receipt));
        };
        let content_key = scanned.content_key();
        let statements = Arc::new(Statements::of(&scanned, &text));
        stage("statements", started);
        if let Some(i) = self.memo.iter().position(|r| {
            r.content_key == content_key && r.content_key != 0
                && r.statements.as_ref().is_some_and(|s| s.exact_eq(&statements))
        }) {
            self.touch(i);
            let receipt = Receipt { strategy: "exact_reuse", seconds: started.elapsed().as_secs_f64(), ..Default::default() };
            return Ok((self.memo[i].taxonomy.clone(), receipt));
        }
        let mut fallback_reason = None;
        match self.deletion(&text, &scanned, &statements, started) {
            Ok(Some((tax, mut receipt))) => {
                let tax = Arc::new(tax);
                receipt.seconds = started.elapsed().as_secs_f64();
                self.insert(Revision { text: text.clone(), statements: Some(statements.clone()), text_key, content_key, taxonomy: tax.clone(), base: None, last_use: 0 });
                return Ok((tax, receipt));
            }
            Ok(None) => {}
            Err(reason) => fallback_reason = Some(reason),
        }
        let full_started = Instant::now();
        let tax = Arc::new(classify_text(&text)?);
        let full_seconds = full_started.elapsed().as_secs_f64();
        // An inconsistent answer is complete; a consistent one must be.
        let reusable = !tax.consistent || tax.dropped == 0;
        // For a cheap inconsistent initial revision, keep a small verified
        // inconsistent subset: every later revision containing it is
        // inconsistent too.
        let witness = (!tax.consistent && self.current.is_none() && full_seconds < WITNESS_MAX_SECONDS)
            .then(|| inconsistency_witness(&text, &scanned, WITNESS_BUDGET_FACTOR * full_seconds + 15.0))
            .flatten();
        let initial = self.current.is_none();
        let anonymous: FxHashSet<u128> = scanned
            .statements
            .iter()
            .filter(|st| {
                let t = &text[st.start..st.end];
                (t.starts_with("ObjectPropertyAssertion") || t.starts_with("NegativeObjectPropertyAssertion"))
                    && t.contains("_:")
            })
            .map(|st| st.hash)
            .collect();
        let source_bytes = text.len();
        let mut base = reusable.then(|| BaseState {
            source_bytes,
            anonymous,
            statements: statements.clone(),
            source: Some((text.clone(), scanned)),
            index: None,
            full: None,
            told: None,
            consistent: tax.consistent,
            witness,
        });
        // Skip it when the classification itself was long: the initial
        // revision must still answer within the caller's per-revision budget.
        if initial && full_seconds < EAGER_INDEX_MAX_SECONDS {
            // The first revision is the base of every later deletion: build
            // its locality index now, so no update pays for it.
            if let Some(b) = base.as_mut() {
                let _ = b.index();
            }
        }
        self.insert(Revision { text, statements: Some(statements), text_key, content_key, taxonomy: tax.clone(), base, last_use: 0 });
        let receipt = Receipt {
            strategy: "full_classify",
            fallback_reason,
            seconds: started.elapsed().as_secs_f64(),
            ..Default::default()
        };
        Ok((tax, receipt))
    }

    /// Deletion reuse against the closest stored superset revision.
    /// `Ok(None)`: no applicable base. `Err`: a base applied but reuse declined.
    fn deletion(&mut self, text: &str, scanned: &Scan, new: &Statements, started: Instant)
        -> Result<Option<(Taxonomy, Receipt)>, String>
    {
        // A base: consistent, complete, same header, statement superset,
        // and every removed statement a logical axiom or an annotation.
        let mut best: Option<(usize, usize)> = None;
        for (i, r) in self.memo.iter().enumerate() {
            let Some(base) = &r.base else { continue };
            let old = &base.statements;
            if old.header_hash != new.header_hash || old.total < new.total {
                continue;
            }
            let subset = new.counts.iter().all(|(h, (n, ..))| {
                old.counts.get(h).is_some_and(|(m, ..)| m >= n)
            });
            if !subset {
                continue;
            }
            let removed_ok = old.counts.iter().all(|(h, (m, kind, ..))| {
                let kept = new.counts.get(h).map_or(0, |(n, ..)| *n);
                kept == *m || kept > 0 || matches!(kind, StmtKind::Logical | StmtKind::Assertion | StmtKind::Annotation)
            });
            if !removed_ok {
                continue;
            }
            // Confirm on text: the counted subset is exact only when equal
            // fingerprints are equal statements.
            if !new.confirms_subset(old) {
                continue;
            }
            let diff = old.total - new.total;
            if best.is_none_or(|(_, d)| diff < d) {
                best = Some((i, diff));
            }
        }
        let Some((bi, _)) = best else { return Ok(None) };
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
        let base = self.memo[bi].base.as_mut().expect("base state");
        if !base.consistent {
            // Deletion keeps an inconsistent subset: the stored verified
            // witness, or the module of the empty signature.
            if let Some(w) = &base.witness {
                if w.iter().all(|h| new.counts.contains_key(h)) {
                    let receipt = Receipt { strategy: "inconsistency_witness_reuse", base_revision_statements: base.statements.total, ..Default::default() };
                    return Ok(Some(((*base_tax).clone(), receipt)));
                }
            }
            let removed: Vec<u128> = base.statements.counts.keys().filter(|h| !new.counts.contains_key(*h)).copied().collect();
            let Some(index) = base.index() else { return Err("locality index unavailable".into()) };
            let mut marked = vec![false; index.axiom_count()];
            for h in &removed {
                if let Some(&a) = index.axiom_by_hash.get(h) {
                    marked[a as usize] = true;
                }
            }
            if index.empty_module_avoids(&marked) {
                let receipt = Receipt { strategy: "inconsistency_module_reuse", index_axioms: index.axiom_count(), ..Default::default() };
                return Ok(Some(((*base_tax).clone(), receipt)));
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
        // so it never ran the budgeted in-process CB attempt. Keep that
        // schedule for its module: the attempt can spend its whole budget on
        // a small non-EL module that the HT race answers in a fraction of it.
        let module_settings: &[(&str, &str)] = if base.source_bytes >= INPROC_SIZE_GATE {
            &[("KM_NO_INPROC_ENGINE", "1")]
        } else {
            &[]
        };
        let annotations: FxHashSet<u128> = removed
            .iter()
            .filter(|h| base.statements.counts.get(*h).is_some_and(|(_, k, ..)| *k == StmtKind::Annotation))
            .copied()
            .collect();
        if base.index().is_none() {
            return Err("locality index unavailable".into());
        }
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
            full.empty_module_avoids(&marked).then_some((full, marked, removed_axioms))
        });
        let (index, marked, removed_axioms) = match full_choice {
            Some(choice) => choice,
            None => {
                let (marked, removed_axioms) = mark(tbox_index)?;
                (tbox_index, marked, removed_axioms)
            }
        };
        let mut receipt = Receipt {
            strategy: "module_reuse",
            base_revision_statements: base_statements,
            removed_statements: removed.len(),
            removed_axioms,
            index_axioms: index.axiom_count(),
            ..Default::default()
        };
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
        let Some(affected) = index.affected_classes_tbox(&marked) else {
            return Err("a removed or nominal axiom is in the module of the empty signature".into());
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
            let removed_set: FxHashSet<u128> = removed.iter().copied().collect();
            let built;
            let proofs = match base.told.as_ref() {
                Some(p) => p,
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
                    !proofs.proves_all(iri, &supers, &removed_set)
                })
                .collect();
            receipt.told_subjects = before - kept.len();
            kept
        };
        stage("told proofs", started);
        receipt.reclassified_subjects = relevant.len();
        stage("affected", started);
        let mut tax = (*base_tax).clone();
        tax.rendered = std::sync::OnceLock::new();
        if !relevant.is_empty() {
            let (module, signature) = index.module(&relevant, &marked);
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
                return restricted_complete(text, &names, &base_tax, receipt, started).map(Some);
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
        receipt.reused_subjects = tax.rows.iter().filter(|r| r.is_some()).count();
        Ok(Some((tax, receipt)))
    }
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
        receipt.reused_subjects = tax.rows.iter().filter(|r| r.is_some()).count();
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
    Replace { functional_syntax: String },
    Classify,
    Stats,
}

fn write_error<W: Write>(w: &mut W, op: &str, error: &str) -> std::io::Result<()> {
    serde_json::to_writer(&mut *w, &serde_json::json!({"status": "error", "op": op, "error": error}))
        .map_err(std::io::Error::other)
}

pub fn run_jsonl_session<R: BufRead, W: Write>(reader: R, mut writer: W) -> std::io::Result<()> {
    let mut session = Session::new();
    for line in reader.lines() {
        let line = line?;
        if line.trim().is_empty() {
            continue;
        }
        let request_started = Instant::now();
        match serde_json::from_str::<Command>(&line) {
            Ok(Command::Init { functional_syntax }) | Ok(Command::Replace { functional_syntax }) => {
                drop(line);
                stage("request parsed", request_started);
                let op = if session.current.is_none() { "init" } else { "replace" };
                match session.update(functional_syntax) {
                    Ok((tax, receipt)) => {
                        stage("update returned", request_started);
                        session.revision += 1;
                        write!(writer, "{{\"status\":\"ok\",\"op\":\"{op}\",\"revision\":{},\"route\":\"auto\",\"retained_backend\":{},\"receipt\":",
                            session.revision, receipt.strategy != "full_classify")?;
                        serde_json::to_writer(&mut writer, &serde_json::json!({
                            "strategy": receipt.strategy,
                            "base_revision_statements": receipt.base_revision_statements,
                            "removed_statements": receipt.removed_statements,
                            "removed_axioms": receipt.removed_axioms,
                            "affected_subjects": receipt.affected_subjects,
                            "reclassified_subjects": receipt.reclassified_subjects,
                            "module_axioms": receipt.module_axioms,
                            "index_axioms": receipt.index_axioms,
                            "reused_subjects": receipt.reused_subjects,
                            "told_subjects": receipt.told_subjects,
                            "published_pairs": tax.pair_count(),
                            "seconds": receipt.seconds,
                            "fallback_reason": receipt.fallback_reason,
                            "meaningful_incremental_update": receipt.strategy != "full_classify",
                        })).map_err(std::io::Error::other)?;
                        writer.write_all(b",\"result\":")?;
                        stage("receipt written", request_started);
                        tax.publish(&mut writer)?;
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
}
