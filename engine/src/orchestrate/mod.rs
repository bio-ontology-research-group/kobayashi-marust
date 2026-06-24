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
pub mod features;
pub mod frontend_run;
pub mod race;
pub mod tmpfile;

use std::collections::{BTreeMap, HashSet};
use std::fs::File;
use std::io::{BufReader, Write};
use std::path::Path;

pub use config::Config;

/// Local names denoting the bottom concept (⊥). Matches `owl_classify.BOTTOM`.
fn is_bottom(s: &str) -> bool {
    s == "Nothing" || s == "owl:Nothing" || s == "\u{22A5}"
}

// ---------------------------------------------------------------------------
// errors (hand-rolled; no extra dependency)
// ---------------------------------------------------------------------------
#[derive(Debug)]
pub enum OrchestrateError {
    /// ofn exit 3: ontology outside the supported fragment (datatypes)
    OutOfFragment(String),
    /// a worker exited non-zero (other than the modelled elc 3/4 codes)
    Worker { bin: String, code: i32, stderr: String },
    /// failed to spawn a worker binary
    Spawn { bin: String, source: std::io::Error },
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
#[derive(serde::Deserialize, Default)]
pub struct EngineOut {
    #[serde(default)]
    pub subsumptions: BTreeMap<String, Vec<String>>,
    #[serde(default)]
    pub inconsistent: bool,
    #[serde(default)]
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

pub(crate) fn parse_out(res: &engine_run::EngineResult) -> Result<EngineOut, OrchestrateError> {
    Ok(serde_json::from_reader(BufReader::new(File::open(res.stdout.path())?))?)
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
    engine_threads: Option<usize>,
) -> Result<EngineOut, OrchestrateError> {
    if cfg.absorb_portfolio && cfg.absorb_on {
        if cfg.tab_race {
            return race::race_cb_vs_tableau(cfg, clauses_path, || {
                race::race_absorbed_plain(cfg, ont, clauses_path, engine_threads)
            });
        }
        return race::race_absorbed_plain(cfg, ont, clauses_path, engine_threads);
    }
    if cfg.tab_race {
        return race::race_cb_vs_tableau(cfg, clauses_path, || run_adaptive(cfg, clauses_path, engine_threads));
    }
    run_adaptive(cfg, clauses_path, engine_threads)
}

fn run_adaptive(
    cfg: &Config,
    clauses_path: &std::path::Path,
    engine_threads: Option<usize>,
) -> Result<EngineOut, OrchestrateError> {
    let res = engine_run::run_engine_adaptive(cfg, clauses_path, None, engine_threads)?;
    if res.code != 0 {
        return Err(OrchestrateError::Worker { bin: "engine".into(), code: res.code, stderr: res.stderr });
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
        c => Err(OrchestrateError::Worker { bin: "elc".into(), code: c, stderr: res.stderr }),
    }
}

// ---------------------------------------------------------------------------
// the conductor
// ---------------------------------------------------------------------------
pub fn classify(cfg: &Config, ont: &Path) -> Result<Classification, OrchestrateError> {
    let t_start = std::time::Instant::now();
    let timing = std::env::var_os("KM_TIMING").is_some();
    let (clauses_path, meta) = frontend_run::run_ofn_split(cfg, ont)?;
    if timing {
        eprintln!("KM_TIMING frontend done @ {:.2}s", t_start.elapsed().as_secs_f64());
    }

    // The frontend proved the ABox forces an individual into disjoint named
    // classes: inconsistent. The CB engine drops the ABox, so short-circuit.
    if meta.abox_inconsistent {
        return Ok(Classification {
            consistent: false,
            subsumptions: vec![],
            unsatisfiable: vec![],
            dropped: 0,
        });
    }

    let named: HashSet<&str> = meta.named.iter().map(String::as_str).collect();
    let asserted: HashSet<&str> = meta.asserted_classes.iter().map(String::as_str).collect();
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
    // Under the QO router the HT arm is a sound certify-or-defer specialist, so
    // race it (first valid finisher wins) rather than fallback — this is what lets
    // the fast hybrid certify (e.g. 7581 in ~31s) beat a CB engine that would
    // otherwise time out. For non-candidate onts spawn_ht returns None so CB runs
    // alone regardless of mode; normal HT-routable onts stay sound under race.
    let ht_mode: &str = if cfg.qo_router { "race" } else { cfg.ht_mode.as_str() };
    let out: EngineOut = {
        // The 3 ORE giants OOM under the concurrent elc-portfolio race (it runs CB
        // and elc side by side); keep them on the safe single-arm paths (bare elc
        // when EL-safe, else the CB stack) by suppressing the portfolio for them.
        let is_giant = std::fs::metadata(ont).map(|m| m.len() > 100_000_000).unwrap_or(false);
        let portfolio_on = cfg.elc_portfolio && !is_giant;
        let mut out: Option<EngineOut> = None;
        let (elc_prog, elc_pre) = cfg.elc_cmd();
        if meta.el_rbox_safe && !portfolio_on {
            // bare elc: it decides EL-membership itself (exit 3 ⇒ not EL).
            let res = engine_run::run_engine(&elc_prog, &elc_pre, clauses_path.path(), None, None, None, &[], false)?;
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
        } else if !meta.el_rbox_safe && !portfolio_on && cfg.elc_force {
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
                &[],
                false,
            )?;
            if !(res.oom || res.timed_out) {
                out = handle_elc_result(cfg, res, clauses_path.path())?;
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
                    race::race_cb_vs_ht(cfg, clauses_path.path(), ht_mode, |th| {
                        race::race_adaptive_vs_elc(cfg, clauses_path.path(), th)
                    })?
                } else if portfolio_on {
                    // race the certified EL path against the context engine; both
                    // are sound+complete so the first finisher wins. Reserve a core
                    // (only when KM_THREADS is unset) for the certificate racer.
                    let th = race::elc_portfolio_threads(cfg);
                    race::race_adaptive_vs_elc(cfg, clauses_path.path(), th)?
                } else if cfg.ht_race {
                    // race the whole CB stack against the KM_HT hypertableau.
                    race::race_cb_vs_ht(cfg, clauses_path.path(), ht_mode, |th| {
                        cb_stack(cfg, ont, clauses_path.path(), th)
                    })?
                } else {
                    cb_stack(cfg, ont, clauses_path.path(), cfg.threads)?
                }
            }
        }
    };

    if timing {
        eprintln!("KM_TIMING engine block done @ {:.2}s (subs_keys={})", t_start.elapsed().as_secs_f64(), out.subsumptions.len());
    }
    // Output mapping: emit FULL IRIs (the harness canonicalises once); filter
    // generated names; drop self-subsumptions; collect ⊥-subsumptions as unsat.
    let full_iri = |n: &str| -> String { meta.iri_map.get(n).cloned().unwrap_or_else(|| n.to_string()) };
    let mut subs: Vec<[String; 2]> = Vec::new();
    let mut unsat: Vec<String> = Vec::new();
    let mut unsat_names: HashSet<&str> = HashSet::new();
    for (a, sups) in &out.subsumptions {
        if is_internal(a) {
            continue;
        }
        let fa = full_iri(a);
        for s in sups {
            if is_bottom(s) {
                if !unsat.iter().any(|u| u == &fa) {
                    unsat.push(fa.clone());
                    unsat_names.insert(a.as_str());
                }
            } else if !is_internal(s) && s != a {
                subs.push([fa.clone(), full_iri(s)]);
            }
        }
    }
    if unsat_names.iter().any(|n| asserted.contains(*n)) {
        return Ok(Classification {
            consistent: false,
            subsumptions: vec![],
            unsatisfiable: vec![],
            dropped: out.dropped,
        });
    }
    subs.sort();
    unsat.sort();
    Ok(Classification {
        consistent: !out.inconsistent,
        subsumptions: subs,
        unsatisfiable: unsat,
        dropped: out.dropped,
    })
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
    fn begin_array_value<W: ?Sized + Write>(&mut self, w: &mut W, first: bool) -> std::io::Result<()> {
        if first {
            Ok(())
        } else {
            w.write_all(b", ")
        }
    }
    fn begin_object_key<W: ?Sized + Write>(&mut self, w: &mut W, first: bool) -> std::io::Result<()> {
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
    /// `json.dumps(res)`-compatible bytes.
    pub fn to_json(&self) -> Vec<u8> {
        let mut buf = Vec::new();
        {
            let mut ser = serde_json::Serializer::with_formatter(&mut buf, PyFmt);
            serde::Serialize::serialize(self, &mut ser).expect("serialise Classification");
        }
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
