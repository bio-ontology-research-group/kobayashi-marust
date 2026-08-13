//! Pure-Rust classify orchestrator — the replacement for
//! `engine/py/owl_classify.py`. A typed supervisor that spawns the worker
//! reasoners (`ofn`, `elc`, `kobayashi-marust`, and later `tableau_cli`) as
//! subprocesses, preserving the process-isolation the memory-watchdog and the
//! reasoner races depend on.
//!
//! Phase 1 (this file) implements the production path with all race flags off:
//!   ofn --meta  ->  (el_rbox_safe ? elc : CB-engine-adaptive)  ->  output map.
//! The elc PARTIAL-certificate residue (exit 4) is resolved by re-running the
//! engine on `KM_QUERIES`. Races (absorbed/plain, CB/tableau, CB/HT, elc/CB)
//! and the `cb_to_ht` conversion land in later phases.

pub mod cb_to_ht;
pub mod config;
pub mod engine_run;
pub mod explain;
pub mod features;
pub mod frontend_run;
pub mod input;
pub mod mirror;
pub mod race;
pub mod tmpfile;

use std::collections::{BTreeMap, HashSet};
use std::fs::File;
use std::io::{BufReader, Write};
use std::path::Path;
use std::sync::Arc;

pub use config::Config;
use config::Mechanism;

/// Canonical spellings of the OWL bottom concept (⊥).
///
/// A class in another namespace may legitimately have local name `Nothing`;
/// the frontend keeps it as an ordinary named class, so bare `Nothing` must
/// not be interpreted as OWL bottom here.
fn is_bottom(s: &str) -> bool {
    s == "owl:Nothing"
        || s == "http://www.w3.org/2002/07/owl#Nothing"
        || s == "\u{22A5}"
}

/// Flatten full-IRI rows into the same lexicographic order as sorting all
/// `[subject, superclass]` pairs globally, but compare each repeated subject
/// only at row granularity.
fn flatten_grouped_subsumptions(
    grouped: BTreeMap<String, Vec<String>>,
) -> Vec<[String; 2]> {
    let pair_count: usize = grouped.values().map(Vec::len).sum();
    let mut pairs = Vec::with_capacity(pair_count);
    for (subject, mut supers) in grouped {
        supers.sort_unstable();
        pairs.extend(
            supers
                .into_iter()
                .map(|superclass| [subject.clone(), superclass]),
        );
    }
    pairs
}

struct GroupedJsonTaxonomy {
    iris: Vec<Arc<str>>,
    rows: BTreeMap<u32, Vec<u32>>,
}

struct JsonIriIds<'a> {
    local_ids: BTreeMap<&'a str, u32>,
    by_iri: BTreeMap<Arc<str>, u32>,
    iris: Vec<Arc<str>>,
    appended_fallback: bool,
}

impl<'a> JsonIriIds<'a> {
    fn new(map: &'a BTreeMap<String, String>) -> Self {
        let distinct: std::collections::BTreeSet<&str> =
            map.values().map(String::as_str).collect();
        let mut by_iri = BTreeMap::new();
        let mut iris = Vec::with_capacity(distinct.len());
        for iri in distinct {
            let id = iris.len() as u32;
            let iri: Arc<str> = Arc::from(iri);
            by_iri.insert(Arc::clone(&iri), id);
            iris.push(iri);
        }
        let local_ids = map
            .iter()
            .map(|(local, full)| {
                (
                    local.as_str(),
                    *by_iri
                        .get(full.as_str())
                        .expect("frontend IRI value was indexed"),
                )
            })
            .collect();
        Self {
            local_ids,
            by_iri,
            iris,
            appended_fallback: false,
        }
    }

    fn id(&mut self, local: &str) -> u32 {
        if let Some(&id) = self.local_ids.get(&local) {
            return id;
        }
        if let Some(&id) = self.by_iri.get(local) {
            return id;
        }
        let id = self.iris.len() as u32;
        let iri: Arc<str> = Arc::from(local);
        self.by_iri.insert(Arc::clone(&iri), id);
        self.iris.push(iri);
        self.appended_fallback = true;
        id
    }

    fn finish(self, mut rows: BTreeMap<u32, Vec<u32>>) -> GroupedJsonTaxonomy {
        if !self.appended_fallback {
            for supers in rows.values_mut() {
                supers.sort_unstable();
            }
            return GroupedJsonTaxonomy {
                iris: self.iris,
                rows,
            };
        }

        // Fallback names are rare and were appended after the frontend map.
        // Restore lexicographic id order once, then sort compact integer rows.
        let mut remap = vec![0u32; self.iris.len()];
        let mut iris = Vec::with_capacity(self.iris.len());
        for (new, (iri, old)) in self.by_iri.into_iter().enumerate() {
            remap[old as usize] = new as u32;
            iris.push(iri);
        }
        let mut remapped = BTreeMap::new();
        for (subject, mut supers) in rows {
            for superclass in &mut supers {
                *superclass = remap[*superclass as usize];
            }
            supers.sort_unstable();
            remapped
                .entry(remap[subject as usize])
                .or_insert_with(Vec::new)
                .extend(supers);
        }
        GroupedJsonTaxonomy {
            iris,
            rows: remapped,
        }
    }
}

fn mapped_iri<'a>(map: &'a BTreeMap<String, String>, iri: &'a str) -> &'a str {
    map.get(iri).map_or(iri, String::as_str)
}

// ---------------------------------------------------------------------------
// errors (hand-rolled; no extra dependency)
// ---------------------------------------------------------------------------
#[derive(Debug)]
pub enum OrchestrateError {
    /// ofn exit 3: ontology outside the supported fragment (datatypes)
    OutOfFragment(String),
    /// a worker exited non-zero (other than the modelled elc 3/4 codes)
    Worker {
        bin: String,
        code: i32,
        stderr: String,
    },
    /// failed to spawn a worker binary
    Spawn {
        bin: String,
        source: std::io::Error,
    },
    Io(std::io::Error),
    Json(serde_json::Error),
}

impl std::fmt::Display for OrchestrateError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OrchestrateError::OutOfFragment(m) => write!(f, "out of fragment: {m}"),
            OrchestrateError::Worker { bin, code, stderr } => {
                write!(f, "worker {bin} exited {code}: {stderr}")
            }
            OrchestrateError::Spawn { bin, source } => write!(f, "spawn {bin}: {source}"),
            OrchestrateError::Io(e) => write!(f, "io: {e}"),
            OrchestrateError::Json(e) => write!(f, "json: {e}"),
        }
    }
}
impl std::error::Error for OrchestrateError {}
impl From<std::io::Error> for OrchestrateError {
    fn from(e: std::io::Error) -> Self {
        OrchestrateError::Io(e)
    }
}
impl From<serde_json::Error> for OrchestrateError {
    fn from(e: serde_json::Error) -> Self {
        OrchestrateError::Json(e)
    }
}

// ---------------------------------------------------------------------------
// data
// ---------------------------------------------------------------------------
/// The reasoner-output JSON shape shared by the engine and elc:
/// `{subsumptions:{A:[B,...]}, inconsistent, dropped, unresolved}`.
/// `subsumptions`, `inconsistent` and `dropped` are REQUIRED: both workers
/// always serialise them (`JOutput` / `ElcOutput`), so an empty or truncated
/// object must fail to parse and surface as a worker error instead of
/// decoding into a fail-open "consistent, nothing subsumes" answer. Only
/// `unresolved` is legitimately absent (elc skips it when empty).
#[derive(serde::Deserialize, Default)]
pub struct EngineOut {
    pub subsumptions: BTreeMap<String, Vec<String>>,
    pub inconsistent: bool,
    pub dropped: usize,
    /// elc exit-4 residue (named subjects the certificate could not determine)
    #[serde(default)]
    pub unresolved: Vec<String>,
}

/// The final classification, serialised exactly like `owl_classify`'s output.
#[derive(serde::Serialize)]
pub struct Classification {
    pub consistent: bool,
    pub subsumptions: Vec<[String; 2]>,
    pub unsatisfiable: Vec<String>,
    pub dropped: usize,
}

/// Internal oracle provenance kept out of the stable classification shape.
pub(crate) struct ClassificationEvidence {
    pub classification: Classification,
    /// Final full-IRI rows retained in grouped form for the JSON-only CLI.
    /// Library and explanation callers keep the established flat API.
    grouped_subsumptions: Option<GroupedJsonTaxonomy>,
    /// An exact consistency mechanism covered the complete source even when a
    /// later taxonomy-only fall-through could not retain every clause.
    pub consistency_certified: bool,
}

pub(crate) fn parse_out(res: &engine_run::EngineResult) -> Result<EngineOut, OrchestrateError> {
    Ok(serde_json::from_reader(BufReader::new(File::open(
        res.stdout.path(),
    )?))?)
}

/// The CB stack chosen by the production flags. Mirrors `owl_classify`'s
/// `cb_stack` closure: absorption portfolio (KM_ABSORB_PORTFOLIO + KM_ABSORB) is
/// raced against the tableau when KM_TAB_RACE, the tableau alone races the plain
/// adaptive engine when only KM_TAB_RACE, else the bare adaptive engine.
///
/// `engine_threads` is the effective `KM_THREADS` for every engine run in the
/// stack — `cfg.threads` normally, or a reduced count when the HT racer reserved
/// a core (Python achieves this by mutating the global `os.environ`; the Rust
/// port threads it explicitly).
fn cb_stack(
    cfg: &Config,
    ont: &std::path::Path,
    clauses_path: &std::path::Path,
    named: &HashSet<String>,
    engine_threads: Option<usize>,
) -> Result<EngineOut, OrchestrateError> {
    if cfg.absorb_portfolio && cfg.absorb_on {
        if cfg.tab_race {
            return race::race_cb_vs_tableau(cfg, clauses_path, named, || {
                race::race_absorbed_plain(cfg, ont, clauses_path, engine_threads)
            });
        }
        return race::race_absorbed_plain(cfg, ont, clauses_path, engine_threads);
    }
    if cfg.tab_race {
        return race::race_cb_vs_tableau(cfg, clauses_path, named, || {
            run_adaptive(cfg, clauses_path, engine_threads)
        });
    }
    run_adaptive(cfg, clauses_path, engine_threads)
}

fn run_adaptive(
    cfg: &Config,
    clauses_path: &std::path::Path,
    engine_threads: Option<usize>,
) -> Result<EngineOut, OrchestrateError> {
    let res = engine_run::run_engine_adaptive(cfg, clauses_path, None, engine_threads)?;
    if res.code == 4 {
        return Err(OrchestrateError::OutOfFragment(
            "selected CB mechanism did not reach its complete fixpoint".into(),
        ));
    }
    if res.code != 0 {
        return Err(OrchestrateError::Worker {
            bin: "engine".into(),
            code: res.code,
            stderr: res.stderr,
        });
    }
    parse_out(&res)
}

/// Map an `elc` worker exit code to an `out` (port of the `if proc is not None`
/// block in `owl_classify.classify`): exit 3 → `None` (fall through to CB), exit
/// 4 → resolve the certificate residue, exit 0 → use it, anything else → error.
fn handle_elc_result(
    cfg: &Config,
    res: engine_run::EngineResult,
    clauses_path: &Path,
) -> Result<Option<EngineOut>, OrchestrateError> {
    match res.code {
        3 => Ok(None),
        4 => Ok(Some(resolve_residue(cfg, parse_out(&res)?, clauses_path)?)),
        0 => Ok(Some(parse_out(&res)?)),
        c => Err(OrchestrateError::Worker {
            bin: "elc".into(),
            code: c,
            stderr: res.stderr,
        }),
    }
}

/// Execute one EL completion attempt and never resolve a residue with CB. Exit
/// 3 (not EL) and exit 4 (certificate residue) are honest fragment declines for
/// an atomic EL mechanism, not invitations to start another classifier.
fn run_atomic_elc(cfg: &Config, clauses_path: &Path) -> Result<EngineOut, OrchestrateError> {
    let (program, prefix) = cfg.elc_cmd();
    let res = engine_run::run_engine(
        &program,
        &prefix,
        clauses_path,
        None,
        Some(cfg.par_mem_gb),
        None,
        &[],
        false,
    )?;
    match res.code {
        0 => {
            let out = parse_out(&res)?;
            if out.unresolved.is_empty() {
                Ok(out)
            } else {
                Err(OrchestrateError::OutOfFragment(
                    "EL completion returned a classification residue".into(),
                ))
            }
        }
        3 => Err(OrchestrateError::OutOfFragment(
            "ontology is outside the selected EL completion fragment".into(),
        )),
        4 => Err(OrchestrateError::OutOfFragment(
            "EL completeness certificate left an unresolved residue".into(),
        )),
        code => Err(OrchestrateError::Worker {
            bin: "elc".into(),
            code,
            stderr: res.stderr,
        }),
    }
}

/// Execute one CB configuration exactly once. In particular this bypasses the
/// adaptive central-to-legacy retry, the in-process probe, every EL/HT racer,
/// and the absorbed/plain portfolio. Thread count, central/per-function mode,
/// ordering, and frontend transformation are the selected mechanism's explicit
/// settings and are measured as such.
fn run_atomic_cb(cfg: &Config, clauses_path: &Path) -> Result<EngineOut, OrchestrateError> {
    let (program, prefix) = cfg.engine_cmd();
    let threads = cfg.threads.map(|n| n.to_string());
    let res = engine_run::run_engine(
        &program,
        &prefix,
        clauses_path,
        threads.as_deref(),
        Some(cfg.par_mem_gb),
        if cfg.no_central {
            None
        } else {
            Some(cfg.central_time_cap)
        },
        &[],
        false,
    )?;
    if res.code == 4 {
        return Err(OrchestrateError::OutOfFragment(
            "selected CB mechanism did not reach its complete fixpoint".into(),
        ));
    }
    if res.code != 0 {
        return Err(OrchestrateError::Worker {
            bin: "engine".into(),
            code: res.code,
            stderr: res.stderr,
        });
    }
    parse_out(&res)
}

/// Dispatch an isolated top-level mechanism. `None` means the explicitly
/// requested historical portfolio; every other variant returns one worker's
/// answer or an honest out-of-fragment/error result, never a fallback answer.
fn run_atomic_mechanism(
    cfg: &Config,
    clauses_path: &Path,
    named: &HashSet<String>,
) -> Result<Option<EngineOut>, OrchestrateError> {
    match &cfg.mechanism {
        Mechanism::Portfolio => Ok(None),
        Mechanism::Elc => run_atomic_elc(cfg, clauses_path).map(Some),
        Mechanism::Cb => run_atomic_cb(cfg, clauses_path).map(Some),
        Mechanism::Ht => race::run_ht_only(cfg, clauses_path, named).map(Some),
        Mechanism::Tableau => race::run_tableau_only(cfg, clauses_path, named).map(Some),
        Mechanism::Unknown(name) => Err(OrchestrateError::OutOfFragment(format!(
            "unknown KM_MECHANISM {name:?}"
        ))),
    }
}

/// Upper size bound (bytes of the source ontology) for the in-process elc
/// fast path. Trivial ORE onts are a few hundred KB; the bound stays well
/// below the giants (whose elc peak must remain in an isolated subprocess).
const INPROC_ELC_MAX: u64 = 4 << 20;

#[inline]
fn use_elc_portfolio(elc: bool, elc_portfolio: bool, is_giant: bool, tab_race: bool) -> bool {
    elc && elc_portfolio && !is_giant && !tab_race
}

/// In-process elc for small EL-safe ontologies (`KM_NO_INPROC_ELC` to opt out).
///
/// Calls `elcomplete::classify` directly — no `fork`/`exec` of the elc worker
/// and no clause-JSON stdout round-trip. Byte-identical to the worker path:
/// the worker builds `ElcOutput { subsumptions, inconsistent, unresolved }`
/// and serialises it; `parse_out` deserialises the same fields into
/// `EngineOut`. Here the same `ElResult` fields populate `EngineOut` directly
/// (the `subsumptions` BTreeMap serialises identically either way).
///
/// The exit-code contract is preserved 1:1: `classify` → `None` is the
/// worker's exit 3 (not EL ⇒ caller falls through to the portfolio/CB path);
/// a non-empty `unresolved` is exit 4 (certificate residue, resolved by the
/// same `resolve_residue`); an empty residue is exit 0 (use it).
///
/// This is the trusted bare-elc answer (identical to the non-portfolio
/// `el_rbox_safe` branch), so returning it and SKIPPING the concurrent
/// portfolio race is sound+complete for exactly the onts elc fully certifies
/// — while removing the per-ont worker forks that dominate the wall on the
/// trivial band (where km already uses less memory than Konclude but ties or
/// narrowly loses on time because of the fork/thread-startup contention).
/// In-process CB engine fast path for small NON-EL ontologies
/// (`KM_NO_INPROC_ENGINE` to opt out). Runs `Reasoner::{new,saturate,
/// subsumptions}` directly on a worker thread, skipping the fork/exec of the
/// engine worker and the clause-JSON stdin round-trip — the same
/// fork-elimination the in-process elc gave the EL band, extended to the
/// small non-EL near-tie band (km already lighter than Konclude there, tying
/// or narrowly losing on wall because of the worker-fork/thread-startup
/// contention).
///
/// Sound+complete + no-blowup gates (checked in the body): NO DL-safe rules
/// (rule onts need the KM_HT_RULES route, where plain CB over the clauses
/// alone would miss the rule-induced (in)consistency) AND no INTERNAL DEFINER
/// DISJUNCTION (`Reasoner::has_internal_definer_disjunction` — the signature
/// of the CB memory-blowup family, ore_ont_9635: 45 GB). The definer gate is
/// what makes the budgeted-detach safe: only non-blowup onts saturate here,
/// so a worker still running when the budget trips holds BOUNDED memory and
/// detaching it cannot OOM the forked fallthrough (the failure mode of the
/// first version, which regressed 9635/12698). The CB engine is otherwise the
/// trusted sound+complete path (complete since 2026-06-13; the HT/portfolio
/// arms are speed fallbacks, preferred-CB-when-it-finishes), and onts that
/// decline or overrun take that forked adaptive/HT path unchanged (keeping HT
/// recovery for e.g. 5303). A completed in-process run is byte-identical to
/// the forked engine worker, minus the fork/stdin overhead.
fn try_inproc_engine(
    clauses_path: &Path,
    budget: std::time::Duration,
) -> Result<Option<EngineOut>, OrchestrateError> {
    use crate::json_io::JInput;
    let buf = std::fs::read(clauses_path)?;
    let input: JInput = serde_json::from_slice(&buf)?;
    // The raw JSON bytes are dead once parsed; free them now instead of
    // holding them across the whole in-process saturation below.
    drop(buf);
    if !input.rules.is_empty() {
        return Ok(None); // rule ontologies need the HT-rules route
    }
    let clauses = input.clauses;
    // Worker sends `None` (decline) fast if the clause set carries an INTERNAL
    // DEFINER DISJUNCTION — the signature of the CB memory-blowup family
    // (ore_ont_9635: 45 GB). Only NON-blowup onts saturate here, so a worker
    // still running when the budget trips holds BOUNDED memory: detaching it
    // and falling through to the forked path cannot OOM (the failure mode of
    // the first budgeted-detach version, which regressed 9635/12698). Onts
    // that decline OR overrun take the forked adaptive/HT path unchanged
    // (keeping HT recovery for e.g. 5303). A completed run is byte-identical
    // to the forked engine worker, minus the fork/stdin overhead.
    let (tx, rx) = std::sync::mpsc::channel();
    std::thread::Builder::new()
        .name("inproc-cb".into())
        .stack_size(256 << 20)
        .spawn(move || {
            use crate::reasoner::Reasoner;
            let mut r = Reasoner::new(&clauses);
            // The String-owning `JClause` block is fully interned into the
            // Reasoner; free it before saturation rather than holding it (it
            // is several times the raw JSON size) across the peak.
            drop(clauses);
            if r.has_internal_definer_disjunction() {
                let _ = tx.send(None); // blow-up-prone ⇒ decline, use forked path
                return;
            }
            r.saturate();
            let out = inproc_engine_out(&mut r);
            // Contexts, arenas, and indexes are dead once the answer is out.
            drop(r);
            let _ = tx.send(out);
        })
        .map_err(|e| OrchestrateError::Spawn {
            bin: "inproc-cb".into(),
            source: e,
        })?;
    match rx.recv_timeout(budget) {
        Ok(Some(out)) => Ok(Some(out)),
        Ok(None) => Ok(None), // declined (definer disjunction / incomplete closure)
        Err(_) => Ok(None),   // overran the budget ⇒ fall through (bounded mem)
    }
}

/// The in-process CB publish gate. A saturated reasoner's output may be
/// published only when no resource backstop fired: `incomplete()` means the
/// accumulated closure is sound but PARTIAL, and the forked engine worker
/// declines exactly that state with exit 4 (`cli.rs`). The in-process fast
/// path must hold the same line — decline (fall through to the forked path)
/// rather than publish a silently incomplete taxonomy as a complete one.
/// A published result carries the reasoner's real `dropped_unsupported()`
/// count, keeping it byte-identical to the forked worker's output.
fn inproc_engine_out(r: &mut crate::reasoner::Reasoner) -> Option<EngineOut> {
    if r.incomplete() {
        return None;
    }
    Some(EngineOut {
        subsumptions: r
            .take_subsumptions()
            .into_iter()
            .map(|(k, v)| (k, v.into_iter().collect::<Vec<_>>()))
            .collect(),
        inconsistent: r.inconsistent(),
        dropped: r.dropped_unsupported(),
        unresolved: Vec::new(),
    })
}

fn try_inproc_elc(
    cfg: &Config,
    clauses_path: &Path,
) -> Result<Option<EngineOut>, OrchestrateError> {
    let buf = std::fs::read(clauses_path)?;
    let input: crate::json_io::JInput = serde_json::from_slice(&buf)?;
    // Raw JSON bytes are dead once parsed; `classify` itself drops the parsed
    // clause block before its saturation, so free the bytes symmetrically.
    drop(buf);
    match crate::elcomplete::classify(input.clauses) {
        None => Ok(None), // not EL ⇒ exit-3 equivalent, fall through
        Some(res) => {
            let out = EngineOut {
                subsumptions: res.subsumptions,
                inconsistent: res.inconsistent,
                dropped: 0,
                unresolved: res.unresolved,
            };
            if out.unresolved.is_empty() {
                Ok(Some(out))
            } else {
                Ok(Some(resolve_residue(cfg, out, clauses_path)?))
            }
        }
    }
}

// ---------------------------------------------------------------------------
// the conductor
// ---------------------------------------------------------------------------
pub fn classify(initial_cfg: &Config, ont: &Path) -> Result<Classification, OrchestrateError> {
    classify_with_evidence(initial_cfg, ont).map(|evidence| evidence.classification)
}

/// A JSON-only classification result that may retain taxonomy rows in grouped
/// form until serialization. This keeps the public [`Classification`] shape
/// unchanged while avoiding one cloned subject `String` per pair in the CLI.
pub struct JsonClassification {
    classification: Classification,
    grouped_subsumptions: Option<GroupedJsonTaxonomy>,
}

impl JsonClassification {
    pub fn write_json<W: Write>(&self, writer: W) -> serde_json::Result<()> {
        let mut ser = serde_json::Serializer::with_formatter(writer, PyFmt);
        serde::Serialize::serialize(self, &mut ser)
    }
}

impl serde::Serialize for JsonClassification {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeStruct;

        struct GroupedPairs<'a>(&'a GroupedJsonTaxonomy);
        impl serde::Serialize for GroupedPairs<'_> {
            fn serialize<S: serde::Serializer>(
                &self,
                serializer: S,
            ) -> Result<S::Ok, S::Error> {
                use serde::ser::SerializeSeq;
                let len = self.0.rows.values().map(Vec::len).sum();
                let mut seq = serializer.serialize_seq(Some(len))?;
                for (subject, supers) in &self.0.rows {
                    for superclass in supers {
                        seq.serialize_element(&(
                            self.0.iris[*subject as usize].as_ref(),
                            self.0.iris[*superclass as usize].as_ref(),
                        ))?;
                    }
                }
                seq.end()
            }
        }

        let mut state = serializer.serialize_struct("Classification", 4)?;
        state.serialize_field("consistent", &self.classification.consistent)?;
        if let Some(grouped) = &self.grouped_subsumptions {
            state.serialize_field("subsumptions", &GroupedPairs(grouped))?;
        } else {
            state.serialize_field("subsumptions", &self.classification.subsumptions)?;
        }
        state.serialize_field("unsatisfiable", &self.classification.unsatisfiable)?;
        state.serialize_field("dropped", &self.classification.dropped)?;
        state.end()
    }
}

/// Classify for the normal JSON CLI without forcing grouped taxonomy rows into
/// the flat public representation first.
pub fn classify_json(
    initial_cfg: &Config,
    ont: &Path,
) -> Result<JsonClassification, OrchestrateError> {
    classify_with_evidence_mode(initial_cfg, ont, true).map(|evidence| JsonClassification {
        classification: evidence.classification,
        grouped_subsumptions: evidence.grouped_subsumptions,
    })
}

fn composite_layout(profile: &crate::frontend::profile::OntologyProfile) -> Option<u32> {
    let individuals = profile
        .clauses
        .individual_term_symbols
        .max(profile.source.distinct_individuals);
    if profile.clauses.function_term_symbols == 0 {
        crate::calc::choose_comp_ind_bits_unknown_functions(individuals)
    } else {
        crate::calc::choose_comp_ind_bits(profile.clauses.function_term_symbols, individuals)
    }
}

pub(crate) fn classify_with_evidence(
    initial_cfg: &Config,
    ont: &Path,
) -> Result<ClassificationEvidence, OrchestrateError> {
    classify_with_evidence_mode(initial_cfg, ont, false)
}

fn classify_with_evidence_mode(
    initial_cfg: &Config,
    ont: &Path,
    retain_grouped_output: bool,
) -> Result<ClassificationEvidence, OrchestrateError> {
    // Route selection changes process-wide KM_* keys because the frontend and
    // worker subprocesses share the established environment contract. Restore
    // them on every return path so repeated library calls route independently.
    let _environment_guard = crate::routing::EnvironmentGuard::capture();
    let t_start = std::time::Instant::now();
    let timing = std::env::var_os("KM_TIMING").is_some();
    // Certified private negative-existential mirror route: a family of private
    // `N ≡ ¬∃R.F` definitions is a family of top-level disjunctions the CB
    // calculus cannot absorb, but removing them leaves a positive fragment that
    // classifies in seconds and reconstructs the original taxonomy exactly.
    // Preprocessing only — it classifies ordinary projections through this same
    // pipeline and fails closed (returns None) unless every premise holds.
    if let Some(classification) = mirror::try_classify(initial_cfg, ont)? {
        if timing {
            eprintln!(
                "KM_TIMING frontend done @ {:.2}s route=mirror_private",
                t_start.elapsed().as_secs_f64()
            );
        }
        return Ok(ClassificationEvidence {
            classification,
            grouped_subsumptions: None,
            consistency_certified: true,
        });
    }
    let (clauses_path, meta) = frontend_run::run_ofn_split(initial_cfg, ont)?;
    let selected_route = meta
        .route
        .parse::<crate::routing::Route>()
        .map_err(|error| OrchestrateError::OutOfFragment(format!("configuration: {error}")))?;

    let routed_cfg = if matches!(
        selected_route,
        crate::routing::Route::Auto | crate::routing::Route::Manual
    ) {
        None
    } else {
        // The frontend subprocess cannot mutate its parent's environment. Apply
        // the same typed bundle here, then freeze subsequent frontend retries in
        // manual mode so the absorption portfolio can explicitly request its
        // plain/absorbed pass without the tree overriding it.
        selected_route.apply_environment();
        if let Some(bits) = composite_layout(&meta.profile) {
            std::env::set_var("KM_COMP_IND_BITS", bits.to_string());
        }
        std::env::set_var("KM_ROUTE", "manual");
        Some(Config::from_env())
    };
    let cfg = routed_cfg.as_ref().unwrap_or(initial_cfg);
    if timing {
        eprintln!(
            "KM_TIMING frontend done @ {:.2}s route={}",
            t_start.elapsed().as_secs_f64(),
            selected_route,
        );
    }

    // The frontend proved the ABox forces an individual into disjoint named
    // classes: inconsistent. The CB engine drops the ABox, so short-circuit.
    if meta.abox_inconsistent {
        return Ok(ClassificationEvidence {
            classification: Classification {
                consistent: false,
                subsumptions: vec![],
                unsatisfiable: vec![],
                dropped: 0,
            },
            grouped_subsumptions: None,
            consistency_certified: true,
        });
    }

    let mut consistency_certified = false;
    // Development gate for the positive-EL ABox certificate. Automatic
    // selection is added only after focused corpus validation proves both its
    // semantic and resource contract.
    if meta.profile.positive_el_abox_materializable
        || std::env::var_os("KM_EL_ABOX_CHECK").is_some()
    {
        let input: crate::json_io::JInput =
            serde_json::from_reader(BufReader::new(File::open(clauses_path.path())?))?;
        match crate::elcomplete::positive_abox_consistent(input.clauses, &input.nominal_abox) {
            Some(false) => {
                return Ok(ClassificationEvidence {
                    classification: Classification {
                        consistent: false,
                        subsumptions: vec![],
                        unsatisfiable: vec![],
                        dropped: 0,
                    },
                    grouped_subsumptions: None,
                    consistency_certified: true,
                });
            }
            Some(true) => consistency_certified = true,
            None => {
                return Err(OrchestrateError::OutOfFragment(
                    "positive EL ABox consistency certificate declined".into(),
                ));
            }
        }
    }

    // SWRL DL-safe rule support (Stage 2): if the ontology has DL-safe rules, run
    // the rule-aware HT consistency check (ABox seeded as named nominal nodes;
    // rules fired over named individuals). We short-circuit ONLY on a detected
    // INCONSISTENCY: then ⊥ subsumes everything and `consistent=false` with an
    // empty subsumption set is the complete, correct answer (this is the
    // 2669/15516 contested-gold case — genuinely inconsistent, gold wrong; see
    // docs/CONTESTED-GOLD.md). A CONSISTENT rule ontology falls THROUGH to normal
    // classification so its class hierarchy is still computed — the rules are
    // DL-safe (range only over named individuals) and so cannot change any TBox
    // class subsumption, making the fall-through sound and complete. Inert when
    // the ontology has no rule (`rules_consistency` returns None). Opt out with
    // KM_NO_HT_RULES.
    if cfg.ht_rules {
        match rules_consistency(cfg, clauses_path.path(), &meta)? {
            Some(false) => {
                if timing {
                    eprintln!(
                        "KM_TIMING rules-consistency done @ {:.2}s consistent=false",
                        t_start.elapsed().as_secs_f64(),
                    );
                }
                return Ok(ClassificationEvidence {
                    classification: Classification {
                        consistent: false,
                        subsumptions: vec![],
                        unsatisfiable: vec![],
                        dropped: 0,
                    },
                    grouped_subsumptions: None,
                    consistency_certified: true,
                });
            }
            Some(true) => consistency_certified = true,
            None => {}
        }
    }

    let named: HashSet<&str> = meta.named.iter().map(String::as_str).collect();
    let asserted: HashSet<&str> = meta.asserted_classes.iter().map(String::as_str).collect();
    // Owned declaration set consumed by the CB-to-HT conversion. A declared
    // class is always a query even when its spelling resembles an internal
    // frontend symbol.
    let named_set: HashSet<String> = meta.named.iter().cloned().collect();
    // In the Rust-frontend path the per-ontology short registry is empty, so
    // `short(n) == n`; is_internal keys directly on the internal name.
    let is_internal = |n: &str| -> bool {
        if named.contains(n) {
            return false;
        }
        n.starts_with("Q_")
            || n.starts_with("__")
            || n.starts_with("aux_")
            || n.starts_with("def_")
            || (n.contains(':') && !is_bottom(n))
    };

    // EL fast path (elc) when the RBox is EL-safe, else the CB engine. The
    // certified-elc portfolio (KM_ELC_PORTFOLIO) skips the bare elc and the
    // forced attempt — it races a certified elc against the engine below.
    // The QO router runs the hybrid certify as the HT arm in the SAME
    // correctness-aware FALLBACK mode as the normal HT race: CB (the trusted
    // sound+complete engine) is preferred whenever it finishes, and the HT
    // certify is taken ONLY when CB errors or runs past KM_HT_BUDGET_S. This is
    // what makes the router safe even though the kpset certify is not guaranteed
    // complete on every inverse ont (e.g. ore_ont_15098: the certify yields 939,
    // CB yields the correct 951 — fallback keeps CB's answer; race mode wrongly
    // let the faster incomplete certify win). On a CB-timeout ont (7581) CB never
    // finishes, so the certify (done in ~31s) is taken and the ont is recovered.
    let ht_mode: &str = cfg.ht_mode.as_str();
    let atomic_out = match run_atomic_mechanism(cfg, clauses_path.path(), &named_set) {
        Ok(out) => out,
        Err(_error) if selected_route == crate::routing::Route::CertifiedElProduction => {
            // The source gate is only a scheduling hint. A certificate refusal,
            // resource failure, or worker error must retain the exact automatic
            // coverage by rerunning the established absorbed production route.
            crate::routing::Route::ProductionAll.apply_environment();
            std::env::set_var(
                "KM_ROUTE",
                crate::routing::Route::ProductionAll.as_str(),
            );
            let fallback_cfg = Config::from_env();
            return classify_with_evidence_mode(&fallback_cfg, ont, retain_grouped_output);
        }
        Err(error) => return Err(error),
    };
    let out: EngineOut = match atomic_out {
        Some(out) => out,
        None => {
            // The 3 ORE giants OOM under the concurrent elc-portfolio race (it runs CB
            // and elc side by side); keep them on the safe single-arm paths (bare elc
            // when EL-safe, else the CB stack) by suppressing the portfolio for them.
            let is_giant = std::fs::metadata(ont)
                .map(|m| m.len() > 100_000_000)
                .unwrap_or(false);
            // KM_TAB_RACE is an explicitly selected alternative portfolio. A later
            // certified-EL integration accidentally shadowed `cb_stack` (the only
            // place the lazy tableau is composed) on every non-giant ontology.
            // Suppress that outer EL race when tableau racing is requested; the
            // normal bare-EL fast path still gets first refusal, and a non-EL input
            // reaches the documented absorbed-CB-vs-tableau procedure below.
            let portfolio_on =
                use_elc_portfolio(cfg.elc, cfg.elc_portfolio, is_giant, cfg.tab_race);
            let mut out: Option<EngineOut> = None;
            let (elc_prog, elc_pre) = cfg.elc_cmd();

            // In-process elc fast path for SMALL EL-safe ontologies: run elc as a
            // library call and, when it fully certifies, skip the portfolio race
            // entirely (no CB/HT/elc-cert forks). Equivalent to the trusted
            // bare-elc branch below; elc reporting not-EL (None) falls straight
            // through to the existing logic unchanged. Gated by size so the
            // giants keep their isolated-subprocess elc. Opt out KM_NO_INPROC_ELC.
            let inproc_ok = std::env::var_os("KM_NO_INPROC_ELC").is_none();
            let small = std::fs::metadata(ont)
                .map(|m| m.len() < INPROC_ELC_MAX)
                .unwrap_or(false);
            if cfg.elc && inproc_ok && small && meta.el_rbox_safe {
                out = try_inproc_elc(cfg, clauses_path.path())?;
                if timing && out.is_some() {
                    eprintln!(
                        "KM_TIMING in-process elc done @ {:.2}s (no race)",
                        t_start.elapsed().as_secs_f64()
                    );
                }
            }

            if cfg.elc && out.is_none() && meta.el_rbox_safe && !portfolio_on {
                // bare elc: it decides EL-membership itself (exit 3 ⇒ not EL).
                let res = engine_run::run_engine(
                    &elc_prog,
                    &elc_pre,
                    clauses_path.path(),
                    None,
                    None,
                    None,
                    &[],
                    false,
                )?;
                out = handle_elc_result(cfg, res, clauses_path.path())?;
                if out.is_none() {
                    // EL-safe RBox but a non-EL TBox residual (covering disjunction /
                    // nominal / cardinality), so cert-off elc bailed before saturating.
                    // This branch is reached only when the portfolio is suppressed —
                    // i.e. for the >100MB giants, where racing CB and elc concurrently
                    // would OOM. Retry elc alone with the repair certificate: when the
                    // canonical EL model certifies the residual (an inert/covering
                    // disjunction whose EL answer is already complete — exactly what
                    // ELK computes by dropping the non-EL axioms), elc answers soundly
                    // in EL time and memory instead of the CB engine blowing up.
                    // Bounded by wall+RSS so a failing certificate still falls through
                    // to CB. Recovers EL-safe giants 15803, 6212 (240s/18GB timeout →
                    // ~25s/82s at 1.2GB, gold-clean) while leaving the pure-EL giants
                    // (no residual, solved on the first attempt) untouched.
                    let res = engine_run::run_engine(
                        &elc_prog,
                        &elc_pre,
                        clauses_path.path(),
                        None,
                        Some(cfg.elc_force_mem_gb),
                        Some(cfg.elc_force_budget_s),
                        &[("KM_ELC_CERT", "2")],
                        false,
                    )?;
                    if !(res.oom || res.timed_out) {
                        out = handle_elc_result(cfg, res, clauses_path.path())?;
                    }
                }
            } else if cfg.elc && !meta.el_rbox_safe && !portfolio_on && cfg.elc_force {
                // KM_ELC_FORCE: attempt elc on a non-EL-safe RBox; only a passing
                // completeness certificate lets it answer, and a failing attempt can
                // be arbitrarily expensive, so bound it by wall clock + RSS. Hitting
                // either bound falls through to the CB engine exactly like exit 3.
                let res = engine_run::run_engine(
                    &elc_prog,
                    &elc_pre,
                    clauses_path.path(),
                    None,
                    Some(cfg.elc_force_mem_gb),
                    Some(cfg.elc_force_budget_s),
                    &[("KM_ELC_CERT", "2")],
                    false,
                )?;
                if !(res.oom || res.timed_out) {
                    out = handle_elc_result(cfg, res, clauses_path.path())?;
                }
            }
            // In-process CB engine fast path for SMALL NON-EL HORN ontologies: run
            // the trusted CB engine as a library call and, when it finishes, skip
            // the fork/race entirely. Eligible when the ont is small (same file
            // gate as in-process elc) and NOT EL-safe (EL-safe small onts already
            // took the in-process elc above). The rule + Horn (no-blowup) gates and
            // soundness argument live in `try_inproc_engine`. Opt out
            // KM_NO_INPROC_ENGINE.
            if out.is_none()
                && small
                && !meta.el_rbox_safe
                && std::env::var_os("KM_NO_INPROC_ENGINE").is_none()
            {
                let budget_s: f64 = std::env::var("KM_INPROC_ENGINE_BUDGET_S")
                    .ok()
                    .and_then(|s| s.parse().ok())
                    .unwrap_or(4.0);
                out = try_inproc_engine(
                    clauses_path.path(),
                    std::time::Duration::from_secs_f64(budget_s),
                )?;
                if timing && out.is_some() {
                    eprintln!(
                        "KM_TIMING in-process engine done @ {:.2}s (no race)",
                        t_start.elapsed().as_secs_f64()
                    );
                }
            }

            match out {
                Some(o) => o,
                None => {
                    if portfolio_on && cfg.ht_race {
                        // Combined router: HT races against (CB-adaptive vs certified
                        // elc). Per ont, whichever sound+complete arm finishes first
                        // wins; in fallback mode HT answers only when the CB/elc arm
                        // fails or runs past budget (monotone-safe). This reaches the
                        // union of the HT and elc-portfolio recoveries in one pass.
                        race::race_cb_vs_ht(cfg, clauses_path.path(), &named_set, ht_mode, |th| {
                            race::race_adaptive_vs_elc(cfg, ont, clauses_path.path(), th)
                        })?
                    } else if portfolio_on {
                        // race the certified EL path against the context engine; both
                        // are sound+complete so the first finisher wins. Reserve a core
                        // (only when KM_THREADS is unset) for the certificate racer.
                        let th = race::elc_portfolio_threads(cfg);
                        race::race_adaptive_vs_elc(cfg, ont, clauses_path.path(), th)?
                    } else if cfg.ht_race {
                        // race the whole CB stack against the KM_HT hypertableau.
                        race::race_cb_vs_ht(cfg, clauses_path.path(), &named_set, ht_mode, |th| {
                            cb_stack(cfg, ont, clauses_path.path(), &named_set, th)
                        })?
                    } else {
                        cb_stack(cfg, ont, clauses_path.path(), &named_set, cfg.threads)?
                    }
                }
            }
        }
    };

    if timing {
        eprintln!(
            "KM_TIMING engine block done @ {:.2}s (subs_keys={})",
            t_start.elapsed().as_secs_f64(),
            out.subsumptions.len()
        );
    }
    // Output mapping: emit FULL IRIs (the harness canonicalises once); filter
    // generated names; drop self-subsumptions; collect ⊥-subsumptions as unsat.
    // Preserve Python's lexicographic pair ordering without globally sorting
    // every materialised pair.  Worker output is already grouped by subject;
    // grouping again by the mapped full IRI, sorting each (much smaller)
    // super-row, and then flattening BTreeMap order is exactly equivalent to
    // `Vec<[String; 2]>::sort()`.  This avoids repeatedly comparing the same
    // potentially long subject IRI on dense taxonomies.
    let mut grouped_subs: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut grouped_json: BTreeMap<u32, Vec<u32>> = BTreeMap::new();
    // The JSON-only path stores one compact id per pair. Full IRIs remain in a
    // sorted dictionary and are borrowed only while serializing.
    let mut iri_ids = retain_grouped_output.then(|| JsonIriIds::new(&meta.iri_map));
    let mut unsat_set: std::collections::BTreeSet<String> =
        std::collections::BTreeSet::new();
    let mut unsat_names: HashSet<&str> = HashSet::new();
    for (a, sups) in &out.subsumptions {
        if is_internal(a) {
            continue;
        }
        let fa = mapped_iri(&meta.iri_map, a);
        if retain_grouped_output {
            let iri_ids = iri_ids.as_mut().expect("JSON IRI ids are initialized");
            let mut mapped_supers = Vec::with_capacity(sups.len());
            for s in sups {
                if is_bottom(s) {
                    // Preserve the previous first-full-IRI-representative
                    // behaviour when multiple local aliases map to one class.
                    if unsat_set.insert(fa.to_string()) {
                        unsat_names.insert(a.as_str());
                    }
                } else if !is_internal(s) && s != a {
                    mapped_supers.push(iri_ids.id(s));
                }
            }
            if !mapped_supers.is_empty() {
                grouped_json
                    .entry(iri_ids.id(a))
                    .or_default()
                    .extend(mapped_supers);
            }
        } else {
            let mut mapped_supers = Vec::with_capacity(sups.len());
            for s in sups {
                if is_bottom(s) {
                    // Preserve the previous first-full-IRI-representative
                    // behaviour when multiple local aliases map to one class.
                    if unsat_set.insert(fa.to_string()) {
                        unsat_names.insert(a.as_str());
                    }
                } else if !is_internal(s) && s != a {
                    mapped_supers.push(mapped_iri(&meta.iri_map, s).to_string());
                }
            }
            if !mapped_supers.is_empty() {
                // Moving `fa` here avoids cloning the same subject once per
                // superclass. Aliases that map to one full IRI merge into one row.
                grouped_subs
                    .entry(fa.to_string())
                    .or_default()
                    .extend(mapped_supers);
            }
        }
    }
    if unsat_names.iter().any(|n| asserted.contains(*n)) {
        return Ok(ClassificationEvidence {
            classification: Classification {
                consistent: false,
                subsumptions: vec![],
                unsatisfiable: vec![],
                dropped: out.dropped,
            },
            grouped_subsumptions: None,
            consistency_certified: consistency_certified || out.dropped == 0,
        });
    }
    let (subs, grouped_subsumptions) = if retain_grouped_output {
        (
            Vec::new(),
            Some(
                iri_ids
                    .expect("JSON IRI ids are initialized")
                    .finish(grouped_json),
            ),
        )
    } else {
        (flatten_grouped_subsumptions(grouped_subs), None)
    };
    let unsat = unsat_set.into_iter().collect();
    Ok(ClassificationEvidence {
        classification: Classification {
            consistent: !out.inconsistent,
            subsumptions: subs,
            unsatisfiable: unsat,
            dropped: out.dropped,
        },
        grouped_subsumptions,
        consistency_certified: consistency_certified || out.dropped == 0,
    })
}

/// KM_HT_RULES (Stage 2): consistency check of a DL-safe-rule ontology. Reads the
/// clause file (which under `KM_HT_RULES` also carries the ground ABox + the
/// parsed rules), and — only if the ontology actually has rules — builds the
/// rule-aware TInput (ABox seeded as named nominal nodes, rules turned into HT
/// clauses with an O-guard) and runs the `km tableau` worker in
/// CONSISTENCY-ONLY mode (`KM_RULES_CONSISTENCY`, default Tableau, no `KM_HT`).
/// Returns `Some(consistent)` when rules are present, `None` otherwise (caller
/// then takes the normal route).
fn rules_consistency(
    cfg: &Config,
    clauses_path: &Path,
    meta: &frontend_run::Meta,
) -> Result<Option<bool>, OrchestrateError> {
    use crate::json_io::JInput;
    use std::process::{Command, Stdio};
    let input: JInput = serde_json::from_reader(BufReader::new(File::open(clauses_path)?))?;
    if input.rules.is_empty() {
        return Ok(None);
    }
    let named: HashSet<String> = meta.named.iter().cloned().collect();
    // rbox is deliberately NOT threaded here (`None`): this is the validated
    // 2669/15516 precheck configuration. The rbox side channel only feeds the
    // fast-Ht first-class role machinery and, crucially, its inverse records
    // arm the `nominal+inverse(SHOI/SHOIQ)` classification fence, which would
    // unseat the ABox nominal seeds this consistency check exists to create
    // (the tableau then has no roots, trivially answers "consistent", and the
    // rule-detected inconsistency is lost). Inverse/subrole/domain/range
    // semantics still reach the tableau through the frontend's bridge clauses
    // inside `input.clauses`, so a detected clash remains a real clash.
    let tin = cb_to_ht::convert(
        &input.clauses,
        None,
        &named,
        &input.cardinalities,
        &input.definers,
        &input.source_axioms,
        false, // keep the clausal cardinality (Eq-heads) for the default Tableau
        &input.rules,
        true, // ht_rules: seed the ABox + emit rule clauses
    );
    let tin_bytes = serde_json::to_vec(&tin)?;
    let (tab_prog, tab_pre) = cfg.tab_cmd();
    let out_path = tmpfile::TempPath::new(".rulescons.json");
    let mut cmd = Command::new(&tab_prog);
    cmd.args(&tab_pre)
        .stdin(Stdio::piped())
        .stdout(File::create(out_path.path())?)
        .stderr(Stdio::null())
        .env("KM_RULES_CONSISTENCY", "1");
    // do NOT set KM_HT here: the default Tableau is what seeds the nominal roots
    // and applies the o-rule in `consistent(&[])`.
    cmd.env_remove("KM_HT");
    let mut child = cmd.spawn().map_err(|e| OrchestrateError::Spawn {
        bin: "tableau".into(),
        source: e,
    })?;
    {
        use std::io::Write as _;
        let mut stdin = child.stdin.take().expect("tableau stdin");
        stdin.write_all(&tin_bytes)?;
    }
    let status = child.wait()?;
    if !status.success() {
        return Err(OrchestrateError::Worker {
            bin: "tableau".into(),
            code: status.code().unwrap_or(-1),
            stderr: String::new(),
        });
    }
    #[derive(serde::Deserialize)]
    struct TOut {
        #[serde(default = "tt")]
        consistent: bool,
    }
    fn tt() -> bool {
        true
    }
    let t: TOut = serde_json::from_reader(BufReader::new(File::open(out_path.path())?))?;
    Ok(Some(t.consistent))
}

/// Complete a PARTIAL certified-elc answer (exit 4): classify the residue with
/// the engine under `KM_QUERIES` and merge. Port of `_resolve_residue`.
fn resolve_residue(
    cfg: &Config,
    mut partial: EngineOut,
    clauses_path: &Path,
) -> Result<EngineOut, OrchestrateError> {
    let names = std::mem::take(&mut partial.unresolved);
    if names.is_empty() {
        return Ok(partial);
    }
    let q = names.join(",");
    // mirror `_RACE_WON.clear()`: a prior race may have set the cancel flag; clear
    // it so the residue engine run is allowed to spawn.
    engine_run::reset_cancel();
    let res = engine_run::run_engine_adaptive(cfg, clauses_path, Some(&q), None)?;
    if res.code == 4 {
        return Err(OrchestrateError::OutOfFragment(
            "CB residue completion did not reach its complete fixpoint".into(),
        ));
    }
    if res.code != 0 {
        return Err(OrchestrateError::Worker {
            bin: "engine".into(),
            code: res.code,
            stderr: res.stderr,
        });
    }
    let eng = parse_out(&res)?;
    for (k, v) in eng.subsumptions {
        partial.subsumptions.insert(k, v); // dict.update: eng overwrites partial
    }
    partial.inconsistent = partial.inconsistent || eng.inconsistent;
    Ok(partial)
}

// ---------------------------------------------------------------------------
// output formatting
// ---------------------------------------------------------------------------
/// A `serde_json` formatter matching Python's `json.dumps` default spacing
/// (`", "` between items, `": "` after keys) so `km classify` stdout is
/// byte-identical to `owl_classify.py` for ASCII IRIs.
struct PyFmt;
impl serde_json::ser::Formatter for PyFmt {
    fn begin_array_value<W: ?Sized + Write>(
        &mut self,
        w: &mut W,
        first: bool,
    ) -> std::io::Result<()> {
        if first {
            Ok(())
        } else {
            w.write_all(b", ")
        }
    }
    fn begin_object_key<W: ?Sized + Write>(
        &mut self,
        w: &mut W,
        first: bool,
    ) -> std::io::Result<()> {
        if first {
            Ok(())
        } else {
            w.write_all(b", ")
        }
    }
    fn begin_object_value<W: ?Sized + Write>(&mut self, w: &mut W) -> std::io::Result<()> {
        w.write_all(b": ")
    }
}

impl Classification {
    /// Write `json.dumps(res)`-compatible bytes directly to a stream.
    ///
    /// The CLI uses this path so a dense taxonomy does not coexist with a
    /// second, whole-output byte vector. `to_json` remains the convenient
    /// allocation-returning API and delegates here to pin byte identity.
    pub fn write_json<W: Write>(&self, writer: W) -> serde_json::Result<()> {
        let mut ser = serde_json::Serializer::with_formatter(writer, PyFmt);
        serde::Serialize::serialize(self, &mut ser)
    }

    /// `json.dumps(res)`-compatible bytes.
    pub fn to_json(&self) -> Vec<u8> {
        let mut buf = Vec::new();
        self.write_json(&mut buf).expect("serialise Classification");
        buf
    }

    /// The dependency-free line format for the Java/Protégé plugin (`--lines`).
    pub fn to_lines(&self) -> String {
        let mut out = vec![
            format!("CONSISTENT {}", if self.consistent { 1 } else { 0 }),
            format!("DROPPED {}", self.dropped),
        ];
        for p in &self.subsumptions {
            out.push(format!("SUB\t{}\t{}", p[0], p[1]));
        }
        for c in &self.unsatisfiable {
            out.push(format!("UNSAT\t{}", c));
        }
        out.join("\n")
    }
}

#[cfg(test)]
mod tests {
    use super::{
        composite_layout, flatten_grouped_subsumptions, inproc_engine_out, is_bottom,
        use_elc_portfolio,
    };
    use crate::reasoner::Reasoner;

    #[test]
    fn streamed_classification_json_matches_allocating_api() {
        let classification = super::Classification {
            consistent: true,
            subsumptions: vec![["http://example.org/A".into(), "owl:Thing".into()]],
            unsatisfiable: vec!["http://example.org/B".into()],
            dropped: 0,
        };
        let expected = classification.to_json();
        let mut streamed = Vec::new();
        classification.write_json(&mut streamed).unwrap();
        assert_eq!(streamed, expected);
    }

    #[test]
    fn grouped_json_classification_matches_flat_bytes() {
        let grouped = std::collections::BTreeMap::from([
            (
                "http://a.example/A".to_string(),
                vec!["S1".to_string(), "S1".to_string(), "S2".to_string()],
            ),
            (
                "http://z.example/A".to_string(),
                vec!["S1".to_string(), "S3".to_string()],
            ),
        ]);
        let flat = super::flatten_grouped_subsumptions(grouped.clone());
        let grouped_json = super::GroupedJsonTaxonomy {
            iris: vec![
                std::sync::Arc::from("S1"),
                std::sync::Arc::from("S2"),
                std::sync::Arc::from("S3"),
                std::sync::Arc::from("http://a.example/A"),
                std::sync::Arc::from("http://z.example/A"),
            ],
            rows: std::collections::BTreeMap::from([
                (3, vec![0, 0, 1]),
                (4, vec![0, 2]),
            ]),
        };
        let classification = super::Classification {
            consistent: true,
            subsumptions: flat,
            unsatisfiable: vec!["http://example.org/B".into()],
            dropped: 2,
        };
        let expected = classification.to_json();
        let grouped = super::JsonClassification {
            classification: super::Classification {
                consistent: true,
                subsumptions: Vec::new(),
                unsatisfiable: vec!["http://example.org/B".into()],
                dropped: 2,
            },
            grouped_subsumptions: Some(grouped_json),
        };
        let mut actual = Vec::new();
        grouped.write_json(&mut actual).unwrap();
        assert_eq!(actual, expected);
    }

    #[test]
    fn json_iri_ids_share_repeated_values_and_reorder_fallbacks() {
        let map = std::collections::BTreeMap::from([
            ("local:a".to_string(), "http://z.example/Z".to_string()),
            ("local:b".to_string(), "http://z.example/Z".to_string()),
        ]);
        let mut ids = super::JsonIriIds::new(&map);
        let z = ids.id("local:a");
        assert_eq!(z, ids.id("local:b"));
        let a = ids.id("http://a.example/A");
        let grouped = ids.finish(std::collections::BTreeMap::from([(z, vec![a, a])]));
        assert_eq!(
            grouped
                .iris
                .iter()
                .map(|iri| iri.as_ref())
                .collect::<Vec<_>>(),
            vec!["http://a.example/A", "http://z.example/Z"]
        );
        assert_eq!(grouped.rows, std::collections::BTreeMap::from([(1, vec![0, 0])]));
    }

    /// Regression: the in-process CB fast path published a resource-truncated
    /// (incomplete) closure as a complete taxonomy — the forked worker declines
    /// that state with exit 4, and the fast path must decline it too.
    #[test]
    fn inproc_engine_declines_an_incomplete_reasoner() {
        let mut r = Reasoner::new(&[]);
        r.saturate();
        assert!(
            inproc_engine_out(&mut r).is_some(),
            "a complete closure must publish"
        );
        // Force the resource-backstop state the engine workers report.
        r.absorb(Vec::new(), false, true, 0);
        assert!(
            inproc_engine_out(&mut r).is_none(),
            "a resource-truncated closure must defer to the forked path, not publish"
        );
    }

    /// Regression: the in-process path hard-coded `dropped: 0`, hiding the
    /// reasoner's unsupported-clause count from the output contract.
    #[test]
    fn inproc_engine_reports_the_real_dropped_count() {
        use crate::json_io::{JAtom, JClause, JTerm};
        // An `aux` term is unsupported by the CB reasoner: the clause is
        // dropped and counted.
        let clauses = vec![JClause {
            body: vec![],
            head: vec![JAtom::Concept {
                concept: "A".into(),
                term: JTerm::Aux {
                    root: "a0".into(),
                    label: vec![],
                },
            }],
        }];
        let mut r = Reasoner::new(&clauses);
        r.saturate();
        let out = inproc_engine_out(&mut r).expect("complete closure publishes");
        assert_eq!(out.dropped, 1, "the dropped count must be forwarded");
    }

    #[test]
    fn explicit_tableau_race_is_not_shadowed_by_elc_portfolio() {
        assert!(use_elc_portfolio(true, true, false, false));
        assert!(!use_elc_portfolio(true, true, false, true));
        assert!(!use_elc_portfolio(true, true, true, false));
        assert!(!use_elc_portfolio(false, true, false, false));
    }

    #[test]
    fn bottom_recognition_is_namespace_exact() {
        assert!(is_bottom("owl:Nothing"));
        assert!(is_bottom("http://www.w3.org/2002/07/owl#Nothing"));
        assert!(is_bottom("\u{22A5}"));
        assert!(!is_bottom("Nothing"));
        assert!(!is_bottom("http://example.org#Nothing"));
    }

    #[test]
    fn grouped_subsumption_order_matches_global_pair_sort() {
        use std::collections::BTreeMap;

        // One row represents aliases that mapped to the same full subject;
        // duplicates must be retained because the previous global sort kept
        // them too.
        let grouped = BTreeMap::from([
            (
                "http://z.example/A".to_string(),
                vec!["S3".to_string(), "S1".to_string()],
            ),
            (
                "http://a.example/A".to_string(),
                vec!["S2".to_string(), "S1".to_string(), "S1".to_string()],
            ),
        ]);
        let mut global: Vec<[String; 2]> = grouped
            .iter()
            .flat_map(|(subject, supers)| {
                supers
                    .iter()
                    .map(|superclass| [subject.clone(), superclass.clone()])
            })
            .collect();
        global.sort();
        assert_eq!(flatten_grouped_subsumptions(grouped), global);
    }

    #[test]
    fn composite_layout_uses_source_individuals_before_nominal_clause_augmentation() {
        let mut profile = crate::frontend::profile::OntologyProfile::default();
        profile.clauses.individual_term_symbols = 0;
        profile.source.distinct_individuals = 18_055;
        assert_eq!(composite_layout(&profile), Some(15));

        profile.source.distinct_individuals = 129_647;
        assert_eq!(composite_layout(&profile), Some(17));

        profile.clauses.function_term_symbols = 130_303;
        profile.source.distinct_individuals = 18_055;
        assert_eq!(composite_layout(&profile), Some(15));
    }
}
