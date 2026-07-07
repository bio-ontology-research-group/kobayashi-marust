//! Reasoner races (Phase 3a — the deployed production config). Port of
//! `owl_classify._race_absorbed_plain`, `_spawn_tableau`, `_race_cb_vs_tableau`.
//!
//! `race_absorbed_plain` is SEQUENTIAL (an 8 s plain probe, then the absorbed set
//! with the full budget) — only one engine is ever resident, respecting the job
//! memcap. `race_cb_vs_tableau` is the one concurrent race: the engine work runs
//! in a scoped thread while the label-caching tableau is spawned lazily after a
//! grace delay; the first sound+complete finisher wins and the loser is killed
//! (`cancel_and_kill_engines` SIGKILLs the engine children and blocks any retry).

use std::collections::BTreeMap;
use std::fs::File;
use std::io::{BufReader, Write};
use std::path::Path;
use std::process::{Child, Command, Stdio};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};

use crate::json_io::{JClause, JInput};

use super::{cb_to_ht, engine_run, frontend_run, parse_out, Config, EngineOut, OrchestrateError};

// ---------------------------------------------------------------------------
// tableau output -> engine `out` shape
// ---------------------------------------------------------------------------
#[derive(serde::Deserialize)]
struct TOutput {
    #[serde(default = "default_true")]
    consistent: bool,
    #[serde(default)]
    subsumptions: Vec<Vec<String>>,
    #[serde(default)]
    unsatisfiable: Vec<String>,
}
fn default_true() -> bool {
    true
}

fn tableau_to_out(t: TOutput) -> EngineOut {
    let mut subs: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for p in &t.subsumptions {
        if p.len() >= 2 {
            subs.entry(p[0].clone()).or_default().push(p[1].clone());
        }
    }
    for u in &t.unsatisfiable {
        subs.entry(u.clone())
            .or_default()
            .push("owl:Nothing".to_string());
    }
    EngineOut {
        subsumptions: subs,
        inconsistent: !t.consistent,
        dropped: 0,
        unresolved: Vec::new(),
    }
}

// ---------------------------------------------------------------------------
// lazily-spawned label-caching tableau racer
// ---------------------------------------------------------------------------
fn spawn_tableau(
    cfg: &Config,
    clauses_path: &Path,
    named: &std::collections::HashSet<String>,
) -> Option<(Child, super::tmpfile::TempPath)> {
    if !cfg.tab_race {
        return None;
    }
    let (tab_prog, tab_pre) = cfg.tab_cmd();
    let (cl, cards): (Vec<JClause>, Vec<crate::json_io::CardMeta>) = {
        // from_slice on a read buffer, not from_reader — the clause file is
        // multi-MB on large onts and the reader path is markedly slower.
        let buf = std::fs::read(clauses_path).ok()?;
        let v: JInput = serde_json::from_slice(&buf).ok()?;
        (v.clauses, v.cardinalities)
    };
    // giants: the engine path owns them
    if cl.len() > cfg.tab_max_clauses {
        return None;
    }
    // no disjunctive head => deterministic => the engine handles it
    if !cl.iter().any(|c| c.head.len() >= 2) {
        return None;
    }
    let tin = cb_to_ht::convert(&cl, None, named, &cards, false, &[], false);
    // only race when the TInput faithfully represents the ontology
    if !tin.fenced.is_empty() || tin.dropped != 0 {
        return None;
    }
    if !tin.nominals.is_empty() {
        return None;
    }
    if !cfg.tab_feat && (tin.inverse || tin.number) {
        return None;
    }
    let out_path = super::tmpfile::TempPath::new(".tabrace.json");
    let mut cmd = if cfg.tab_race_nice {
        let mut c = Command::new("nice");
        c.arg("-n").arg("19").arg(&tab_prog).args(&tab_pre);
        c
    } else {
        let mut c = Command::new(&tab_prog);
        c.args(&tab_pre);
        c
    };
    cmd.stdin(Stdio::piped())
        .stdout(File::create(out_path.path()).ok()?)
        .stderr(Stdio::null())
        .env("KM_TAB_CACHE", "1")
        .env("KM_TAB_ORD", &cfg.tab_ord);
    let mut child = cmd.spawn().ok()?;
    // feed the TInput on a background thread (ignore broken pipe if the tableau
    // exits before draining — the small TInput never deadlocks)
    let stdin = child.stdin.take()?;
    let bytes = serde_json::to_vec(&tin).ok()?;
    thread::spawn(move || {
        let mut w = stdin;
        let _ = w.write_all(&bytes);
    });
    Some((child, out_path))
}

// ---------------------------------------------------------------------------
// CB-engine procedure vs the lazily-spawned tableau; first valid finisher wins
// ---------------------------------------------------------------------------
pub fn race_cb_vs_tableau<F>(
    cfg: &Config,
    clauses_path: &Path,
    named: &std::collections::HashSet<String>,
    engine_run: F,
) -> Result<EngineOut, OrchestrateError>
where
    F: FnOnce() -> Result<EngineOut, OrchestrateError> + Send,
{
    let eng_done = Arc::new(AtomicBool::new(false));
    thread::scope(|s| -> Result<EngineOut, OrchestrateError> {
        let ed = eng_done.clone();
        let handle = s.spawn(move || {
            let r = engine_run();
            ed.store(true, Ordering::SeqCst);
            r
        });

        // grace delay: an ontology the engine finishes within it pays zero
        // tableau cost (no clause read, no conversion, no extra process).
        // Adaptive sleep (1 ms doubling to 200 ms): a fast engine exit is
        // noticed near-immediately instead of after a 200 ms quantum.
        let t0 = Instant::now();
        let mut interval = Duration::from_millis(1);
        while t0.elapsed().as_secs_f64() < cfg.tab_race_delay {
            if eng_done.load(Ordering::SeqCst) {
                break;
            }
            thread::sleep(interval);
            interval = (interval * 2).min(Duration::from_millis(200));
        }
        let mut tab = if eng_done.load(Ordering::SeqCst) {
            None
        } else {
            spawn_tableau(cfg, clauses_path, named)
        };

        let mut winner: Option<EngineOut> = None;
        let mut interval = Duration::from_millis(1);
        loop {
            let mut tab_failed = false;
            if let Some((child, outp)) = tab.as_mut() {
                if let Ok(Some(st)) = child.try_wait() {
                    let mut won = None;
                    if st.success() {
                        if let Ok(f) = File::open(outp.path()) {
                            if let Ok(t) = serde_json::from_reader::<_, TOutput>(BufReader::new(f))
                            {
                                won = Some(tableau_to_out(t));
                            }
                        }
                    }
                    match won {
                        Some(w) => {
                            engine_run::cancel_and_kill_engines();
                            winner = Some(w);
                        }
                        None => tab_failed = true, // tableau failed/fenced: engine answers
                    }
                }
            }
            if winner.is_some() {
                break;
            }
            if tab_failed {
                tab = None;
            }
            if eng_done.load(Ordering::SeqCst) {
                break;
            }
            thread::sleep(interval);
            interval = (interval * 2).min(Duration::from_millis(50));
        }

        // reap any tableau child still around
        if let Some((mut child, _)) = tab.take() {
            let _ = child.kill();
            let _ = child.wait();
        }
        match winner {
            Some(w) => {
                let _ = handle.join(); // engine children were killed; reap the thread
                Ok(w)
            }
            None => handle.join().expect("engine thread panicked"),
        }
    })
}

// ---------------------------------------------------------------------------
// absorption portfolio (sequential): plain probe, then absorbed
// ---------------------------------------------------------------------------
/// `engine_threads` is the effective `KM_THREADS` for the engine runs (the
/// ambient `cfg.threads`, or a reduced count when a racer reserved a core); the
/// plain probe and the absorbed adaptive run both honour it, matching Python
/// where both inherit the (possibly reduced) global `os.environ["KM_THREADS"]`.
pub fn race_absorbed_plain(
    cfg: &Config,
    ont: &Path,
    absorbed_path: &Path,
    engine_threads: Option<usize>,
) -> Result<EngineOut, OrchestrateError> {
    if let Some(plain) = frontend_run::run_ofn_plain(cfg, ont, false) {
        let threads = engine_threads.map(|t| t.to_string());
        let (engine_prog, engine_pre) = cfg.engine_cmd();
        let res = engine_run::run_engine(
            &engine_prog,
            &engine_pre,
            plain.path(),
            threads.as_deref(),
            Some(cfg.par_mem_gb),
            Some(cfg.absorb_probe_s),
            &[],
            false,
        )?;
        if res.code == 0 {
            return parse_out(&res);
        }
    }
    // plain absent or did not finish fast: run the absorbed set with full budget
    let res = engine_run::run_engine_adaptive(cfg, absorbed_path, None, engine_threads)?;
    if res.code != 0 {
        return Err(OrchestrateError::Worker {
            bin: "engine".into(),
            code: res.code,
            stderr: res.stderr,
        });
    }
    parse_out(&res)
}

// ---------------------------------------------------------------------------
// certified-elc portfolio (KM_ELC_PORTFOLIO): race adaptive CB vs certified elc
// ---------------------------------------------------------------------------
/// Available logical CPUs (the cpuset on Linux). Used only when `KM_THREADS` is
/// unset; the benchmark harness always sets it, so the racer reservations below
/// resolve to `cfg.threads` in practice.
fn avail_cpus() -> usize {
    std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(2)
}

/// Spawn the certified-elc racer (`KM_ELC_CERT`, default 2). Its (possibly
/// hundreds-of-MB) output goes straight to a temp file, never an undrained pipe.
/// Not registered in the LIVE engine set — it is killed directly, mirroring
/// `owl_classify` where `elc_race` is never added to `_LIVE_ENGINES`.
fn spawn_elc_cert(cfg: &Config, clauses_path: &Path) -> Option<(Child, super::tmpfile::TempPath)> {
    let out_path = super::tmpfile::TempPath::new(".elcrace.json");
    let cert = std::env::var("KM_ELC_CERT").unwrap_or_else(|_| "2".to_string());
    let (elc_prog, elc_pre) = cfg.elc_cmd();
    let mut cmd = Command::new(&elc_prog);
    cmd.args(&elc_pre)
        .stdin(File::open(clauses_path).ok()?)
        .stdout(File::create(out_path.path()).ok()?)
        .stderr(Stdio::null())
        .env("KM_ELC_CERT", &cert);
    let child = cmd.spawn().ok()?;
    Some((child, out_path))
}

/// Race `run_engine_adaptive` (a scoped thread) against an already-started
/// certified-elc process. Both sides only ever produce sound AND complete
/// answers (a failing certificate exits 3), so the first finisher wins and the
/// loser is killed. A PARTIAL certificate (elc exit 4) spawns a THIRD racer — a
/// query-restricted engine run under the elc RSS cap — so the partial progress
/// is not forfeited. Port of `_race_adaptive_vs_elc`.
pub fn race_adaptive_vs_elc(
    cfg: &Config,
    ont: &Path,
    clauses_path: &Path,
    engine_threads: Option<usize>,
) -> Result<EngineOut, OrchestrateError> {
    // The CB arm must run through the SAME absorbed-plain path `cb_stack` uses
    // (an 8s plain probe, then the absorbed set), NOT `run_engine_adaptive` on
    // the absorbed clauses directly. Measured: on onts where absorption makes the
    // clause set harder for CB (e.g. ore_ont_1082), the absorbed-only run is
    // 44s/8.7GB where the plain probe finishes in 2.9s/130MB — that mismatch, not
    // the elc process, is why the portfolio path lost speed/memory vs cb_stack.
    // Both paths are the same sound+complete engine on output-preserving clause
    // encodings, so the CB answer is unchanged.
    let cb_run = move || -> Result<EngineOut, OrchestrateError> {
        if cfg.absorb_portfolio && cfg.absorb_on {
            race_absorbed_plain(cfg, ont, clauses_path, engine_threads)
        } else {
            let res = engine_run::run_engine_adaptive(cfg, clauses_path, None, engine_threads)?;
            if res.code != 0 {
                return Err(OrchestrateError::Worker {
                    bin: "engine".into(),
                    code: res.code,
                    stderr: res.stderr,
                });
            }
            parse_out(&res)
        }
    };

    let (mut elc, elc_out) = match spawn_elc_cert(cfg, clauses_path) {
        Some(x) => x,
        // elc could not start: the engine answers alone.
        None => return cb_run(),
    };
    let cap_bytes = (cfg.elc_port_mem_gb * (1u64 << 30) as f64) as u64;

    let read_tout = |p: &Path| -> Option<EngineOut> {
        let f = File::open(p).ok()?;
        serde_json::from_reader::<_, EngineOut>(BufReader::new(f)).ok()
    };

    let cb_done = Arc::new(AtomicBool::new(false));
    let result: Result<EngineOut, OrchestrateError> = thread::scope(|s| {
        let cd = cb_done.clone();
        let cb = s.spawn(move || {
            let r = cb_run();
            cd.store(true, Ordering::SeqCst);
            r
        });

        // the lazily-spawned residue racer (elc exit 4): run_engine with KM_QUERIES
        let mut tgt: Option<
            thread::ScopedJoinHandle<Result<engine_run::EngineResult, OrchestrateError>>,
        > = None;
        let mut partial: Option<EngineOut> = None;
        let mut elc_lost = false;
        let mut winner: Option<EngineOut> = None;

        let mut interval = Duration::from_millis(1);
        loop {
            // --- poll the certified-elc process ---
            if !elc_lost {
                if let Ok(Some(st)) = elc.try_wait() {
                    let rc = st.code().unwrap_or(-1);
                    if rc == 0 {
                        winner = read_tout(elc_out.path());
                        elc_lost = true;
                        if winner.is_some() {
                            // certified full answer wins: kill the CB engine.
                            engine_run::cancel_and_kill_engines();
                            break;
                        }
                        // unparseable (never happens on a real exit-0): let CB answer.
                    } else if rc == 4 && partial.is_none() {
                        if let Some(mut p) = read_tout(elc_out.path()) {
                            let names = std::mem::take(&mut p.unresolved);
                            partial = Some(p);
                            if names.is_empty() {
                                engine_run::cancel_and_kill_engines();
                                winner = partial.take();
                                break;
                            }
                            let q = names.join(",");
                            tgt = Some(s.spawn(move || {
                                // Python inherits the (possibly reserved) global
                                // KM_THREADS; we pass it explicitly for the same effect.
                                let ts = engine_threads.map(|t| t.to_string());
                                let (engine_prog, engine_pre) = cfg.engine_cmd();
                                engine_run::run_engine(
                                    &engine_prog,
                                    &engine_pre,
                                    clauses_path,
                                    ts.as_deref(),
                                    Some(cfg.elc_port_mem_gb),
                                    None,
                                    &[("KM_QUERIES", q.as_str())],
                                    false,
                                )
                            }));
                        }
                        elc_lost = true; // elc itself is done; the racers continue
                    } else if rc != 4 {
                        elc_lost = true; // exit 3 / crash: the engine must answer
                    }
                }
            }

            // --- the residue racer finished? ---
            if let Some(h) = tgt.as_ref() {
                if h.is_finished() {
                    // take() drops the handle from `tgt`; on any failure the loop
                    // simply continues and the full CB engine remains (Python sets
                    // `tgt_thread = None`).
                    let handle = tgt.take().unwrap();
                    if let Ok(res) = handle.join().expect("residue racer panicked") {
                        if res.code == 0 {
                            engine_run::cancel_and_kill_engines();
                            let eng = parse_out(&res)?;
                            let mut p = partial.take().unwrap_or_default();
                            for (k, v) in eng.subsumptions {
                                p.subsumptions.insert(k, v); // dict.update: eng overwrites
                            }
                            p.inconsistent = p.inconsistent || eng.inconsistent;
                            winner = Some(p);
                            break;
                        }
                    }
                }
            }

            // --- the full CB engine finished? ---
            if cb_done.load(Ordering::SeqCst) {
                break;
            }

            // --- watchdog the still-running certified-elc RSS ---
            if !elc_lost {
                if let Some(rss) = engine_run::read_rss(elc.id()) {
                    if rss > cap_bytes {
                        let _ = elc.kill();
                    }
                }
            }
            thread::sleep(interval);
            interval = (interval * 2).min(Duration::from_millis(100));
        }

        // a racer (elc/residue) won: kill the elc process + reap; engines already
        // cancelled. The scope auto-joins the CB (and any residue) thread, whose
        // children were SIGKILLed by `cancel_and_kill_engines`.
        if let Some(w) = winner {
            let _ = elc.kill();
            let _ = elc.wait();
            let _ = cb.join();
            return Ok(w);
        }

        // the full engine answered: stop the certified elc + any residue racer.
        let _ = elc.kill();
        let _ = elc.wait();
        engine_run::cancel_and_kill_engines();
        cb.join().expect("engine thread panicked")
    });
    result
}

/// Effective engine thread count for the elc portfolio: reserve a core ONLY when
/// `KM_THREADS` is unset (the harness always sets it, so in practice the engine
/// keeps `cfg.threads`). Mirrors `classify`'s `if "KM_THREADS" not in os.environ`.
pub fn elc_portfolio_threads(cfg: &Config) -> Option<usize> {
    cfg.threads
        .or_else(|| Some(avail_cpus().saturating_sub(1).max(1)))
}

// ---------------------------------------------------------------------------
// KM_HT hypertableau race (KM_HT_RACE)
// ---------------------------------------------------------------------------
/// HT is SOUND on this fragment; route iff the cb_to_ht encoding is faithful
/// (nothing fenced/dropped) and there are no inverse roles and no nominals.
/// Number restrictions (ALCQ) ARE allowed. Port of `_ht_routable`.
fn ht_routable(tin: &cb_to_ht::TInput) -> bool {
    if !tin.fenced.is_empty() || tin.dropped != 0 {
        return false;
    }
    if !tin.nominals.is_empty() || tin.inverse {
        return false;
    }
    true
}

/// Does the clause set contain an inverse/symmetric BRIDGE clause
/// (`R(a,b) → R'(b,a)`: a single role head whose args are swapped relative to a
/// body role atom)? This is the structural signal the QO hybrid targets; it is
/// independent of cb_to_ht's `inverse` flag (which only fires for the
/// pairwise-inverse encoding, not bridge clauses).
fn has_inverse_bridge(cl: &[crate::json_io::JClause]) -> bool {
    use crate::json_io::{JAtom, JTerm};
    let var = |t: &JTerm| -> Option<String> {
        if let JTerm::Var { name } = t {
            Some(name.clone())
        } else {
            None
        }
    };
    cl.iter().any(|c| {
        if c.head.len() != 1 {
            return false;
        }
        if let JAtom::Role {
            source: hs,
            target: ht,
            ..
        } = &c.head[0]
        {
            let (hs, ht) = match (var(hs), var(ht)) {
                (Some(a), Some(b)) => (a, b),
                _ => return false,
            };
            c.body.iter().any(|a| match a {
                JAtom::Role { source, target, .. } => {
                    var(source).as_deref() == Some(ht.as_str())
                        && var(target).as_deref() == Some(hs.as_str())
                }
                _ => false,
            })
        } else {
            false
        }
    })
}

/// Does the clause set encode datatype values? The frontend represents a literal
/// value as an opaque `__dt__val__<lit>` concept (pairwise-disjoint), with no
/// concrete-domain oracle in the fast Ht — forcing such an ontology to the Ht
/// yields spurious unsat (cf ore_ont_10621). Datatype onts must stay on the CB
/// engine, which owns the oracle.
fn has_datatype(cl: &[crate::json_io::JClause]) -> bool {
    use crate::json_io::JAtom;
    cl.iter().any(|c| {
        c.body
            .iter()
            .chain(c.head.iter())
            .any(|a| matches!(a, JAtom::Concept { concept, .. } if concept.contains("__dt__val__")))
    })
}

/// Spawn `tableau_cli` under `KM_HT=1` as a racer on the HT-routable fragment.
/// Returns `(child, out_path)` or `None`. Port of `_spawn_ht`.
fn spawn_ht(
    cfg: &Config,
    clauses_path: &Path,
    named: &std::collections::HashSet<String>,
) -> Option<(Child, super::tmpfile::TempPath, bool)> {
    let (tab_prog, tab_pre) = cfg.tab_cmd();
    let (cl, cards): (Vec<JClause>, Vec<crate::json_io::CardMeta>) = {
        // from_slice on a read buffer, not from_reader — the clause file is
        // multi-MB on large onts and the reader path is markedly slower.
        let buf = std::fs::read(clauses_path).ok()?;
        let v: JInput = serde_json::from_slice(&buf).ok()?;
        (v.clauses, v.cardinalities)
    };
    let _tconv = Instant::now();
    let tin = cb_to_ht::convert(
        &cl,
        None,
        named,
        &cards,
        std::env::var_os("KM_NO_HT_CARD").is_none(),
        &[],
        false,
    );
    if std::env::var_os("KM_TIMING").is_some() {
        eprintln!(
            "KM_TIMING spawn_ht: read+convert {} clauses in {:.2}s",
            cl.len(),
            _tconv.elapsed().as_secs_f64()
        );
    }
    // KM_DUMP_TIN=<path>: write the cb_to_ht TInput JSON (so the tableau worker can
    // be run standalone on it with any flags + visible stderr) and print the
    // routing-guard-relevant fields, then carry on. Diagnostic only.
    if let Some(p) = std::env::var_os("KM_DUMP_TIN") {
        if let Ok(bytes) = serde_json::to_vec(&tin) {
            let _ = std::fs::write(&p, &bytes);
        }
        eprintln!(
            "KM_DUMP_TIN clauses={} dropped={} fenced={} nominals={} inverse={} number={} queries={} -> {:?}",
            cl.len(),
            tin.dropped,
            tin.fenced.len(),
            tin.nominals.len(),
            tin.inverse,
            tin.number,
            tin.queries.len(),
            p,
        );
    }
    // KM_HT_FORCE: bypass the soundness routing guard to test the HT algorithm on
    // out-of-fragment onts (inverse / nominals / fenced role-chains). The cb_to_ht
    // encoding may be an approximation there, so results are NOT guaranteed
    // gold-clean — this is for algorithm/scaling measurement only, not production.
    // KM_HT_QO_ROUTER candidate: a faithful, nominal-free TInput that HAS inverse
    // roles. `ht_routable` rejects inverse (the plain HT is unsound there), but the
    // hybrid QO certify path handles exactly this fragment soundly (certify or
    // defer), so such onts get the HT arm under the router even though
    // `ht_routable` is false.
    // cb_to_ht reports `tin.inverse=false` for 7581-style onts because their
    // inverse is encoded as BRIDGE CLAUSES (`R(a,b) → R'(b,a)`), not the
    // pairwise-inverse flag. The hybrid's target signal is exactly those bridges
    // (what `compose_inverse` resolves), so detect them in the clause set — and
    // gate ONLY on bridges so non-inverse HT-routable onts (e.g. 5303) keep their
    // normal branching HT path rather than the certify-only hybrid.
    // SHQ number route (KM_HT_CARD): a faithful, datatype/inverse/nominal-free
    // TInput that HAS first-class number restrictions (`card_defs`). `ht_routable`
    // rejects `number`, so these would otherwise never reach the fast Ht. The
    // first-class `≥n`/`≤n` rules fold the cardinality model the legacy Eq-merge
    // cannot (the disjunction-family cardinality wall). Inverse stays fenced
    // (SHIQ needs double blocking), nominals stay on the shoq route, datatype onts
    // are excluded (no concrete-domain oracle in the Ht). Computed FIRST so it
    // takes precedence over the QO route: a card ont may also carry inert inverse
    // bridges (so `has_inverse_bridge` is true), but the QO certify path's
    // `apply_head` does not handle the kept cardinality recognition Eq-heads — the
    // branching classify with the card rules is the correct route. Monotone-safe:
    // fallback mode keeps CB's answer whenever CB finishes, so the corpus sweep
    // validates soundness — the card arm only answers on CB timeout.
    // Nominals ARE allowed here (unlike qo/shoq's structural split): the fast Ht's
    // SHOQ o-rule composes with the first-class card rules through the shared
    // `merge_into` (Konclude `mergeIndividual`), so a SHOQ number ont folds under
    // the card arm instead of the non-folding QMERGE shoq arm (ore_ont_9540:
    // 46252→64 nodes, 66/66 gold-exact). The card branch already forces
    // KM_HT_PAR=1, which the nominal o-rule requires (parallel merges race). Inverse
    // and datatype stay excluded (no NN-rule / no concrete-domain oracle in the Ht).
    // KM_HT_CARD_RECOG (propagation-based ≤n recognition, see the card env block
    // below) makes the card route sound under inverse: the SHIQ non-shared ∀ +
    // mode-5 blocking it activates handle the inverse soundly, and the
    // deterministic counting recognition converges where the clausal excluded
    // middle did not. So when recognition is requested, drop the `!tin.inverse`
    // exclusion and let inverse+cardinality onts (the SRIQ number giants) onto the
    // card route. Default OFF -> production routing is unchanged.
    let card_recog = std::env::var_os("KM_NO_HT_CARD_RECOG").is_none();
    let card_candidate = cfg.ht_card
        && !tin.card_defs.is_empty()
        && tin.dropped == 0
        && tin.fenced.is_empty()
        && (!tin.inverse || card_recog)
        && !has_datatype(&cl);
    let qo_candidate = cfg.qo_router
        && !card_candidate
        && tin.dropped == 0
        && tin.fenced.is_empty()
        && tin.nominals.is_empty()
        && has_inverse_bridge(&cl);
    // SHOQ/SHOIN/SHON route (KM_HT_SHOQ): a faithful, datatype-free ontology that
    // HAS nominals. `ht_routable` rejects nominals (and these onts carry inverse
    // bridges that the fast Ht's nominal o-rule + self-loop fix + ≥n recognition
    // handle soundly — 10908/15672 are gold-exact), so they would otherwise never
    // reach the fast Ht. The nominal requirement is the structural separator from
    // the number-only inverse SRIQ giants (9724/7914, nominals=0) where the fast
    // Ht IS unsound (shared-filler ∀ pollution) — those stay on CB. Datatype onts
    // are excluded (no concrete-domain oracle in the Ht; cf 10621). Monotone-safe:
    // fallback mode keeps CB's answer whenever CB finishes.
    let shoq_candidate = cfg.ht_shoq
        && !card_candidate
        && tin.dropped == 0
        && tin.fenced.is_empty()
        && !tin.nominals.is_empty()
        && !has_datatype(&cl);
    // KM_HT_BRIDGE route: the konclude_ht bridge (Konclude's completion kernel
    // in Rust) answers sound+complete-or-DEFER by construction (deterministic
    // read-off / pairwise-verified candidates; declines anything it cannot
    // encode losslessly). Nominal-free faithful TInputs only; the worker's
    // bridge arm re-checks coverage per clause. Opt-in while under validation.
    let bridge_candidate = std::env::var_os("KM_HT_BRIDGE").is_some()
        && tin.dropped == 0
        && tin.fenced.is_empty()
        && tin.nominals.is_empty();
    if !ht_routable(&tin)
        && !qo_candidate
        && !shoq_candidate
        && !card_candidate
        && !bridge_candidate
        && std::env::var_os("KM_HT_FORCE").is_none()
    {
        return None;
    }
    let out_path = super::tmpfile::TempPath::new(".htrace.json");
    // a light nice keeps HT from preempting CB on the onts CB finishes quickly.
    let mut cmd = if cfg.ht_nice != "0" && !cfg.ht_nice.is_empty() {
        let mut c = Command::new("nice");
        c.arg("-n").arg(&cfg.ht_nice).arg(&tab_prog).args(&tab_pre);
        c
    } else {
        let mut c = Command::new(&tab_prog);
        c.args(&tab_pre);
        c
    };
    cmd.stdin(Stdio::piped())
        .stdout(File::create(out_path.path()).ok()?);
    // stderr: inherit when stats/trace requested (diagnostic), else null.
    if std::env::var_os("KM_HT_STATS").is_some() || std::env::var_os("KM_HT_TRACE").is_some() {
        cmd.stderr(Stdio::inherit());
    } else {
        cmd.stderr(Stdio::null());
    }
    cmd.env("KM_HT", "1");
    if bridge_candidate
        && !ht_routable(&tin)
        && !qo_candidate
        && !shoq_candidate
        && !card_candidate
    {
        // The bridge is the ONLY reason this worker was spawned: if its arm
        // declines, the worker must produce NO answer (the legacy tableau is
        // not validated on this fragment — "tableau is NOT a fallback").
        cmd.env("KM_HT_BRIDGE_ONLY", "1");
    }
    if qo_candidate {
        // Route this Horn-inverse ont to the validated hybrid certify path, run as
        // a sound certify-OR-DEFER arm: KM_HT_QO_CERTIFY_ONLY makes it emit a
        // (sound+complete-by-construction) answer only when kpset certifies, and
        // produce NO answer otherwise — so the CB engine wins the race on anything
        // the hybrid cannot certify. KM_HT_FORCE lets the inverse ont reach the Ht
        // QO path (the in-fragment gate otherwise routes inverse onts away).
        for (k, v) in [
            ("KM_HT_FORCE", "1"),
            ("KM_HT_QO", "1"),
            ("KM_HT_QO_PC", "1"),
            ("KM_HT_QO_INVCOMPOSE", "1"),
            ("KM_HT_QO_FPROP", "1"),
            ("KM_HT_QO_SAT", "1"),
            ("KM_HT_QO_KPSET", "1"),
            // KM_HT_QO_CARD: a functional/≤n cardinality Eq-head otherwise bails the
            // whole pass `unsupported` at the first occurrence (apply_head:4474), so
            // any SHIF/SRIQ giant (9724: 674 eq-heads) never even completes the
            // forward pass. card_defer instead marks the cardinality anchor
            // INSUFFICIENT (sound — routes those concepts to the per-node card-split
            // verify) and lets the deterministic bulk certify. Required for the
            // cardinality throughput giants.
            ("KM_HT_QO_CARD", "1"),
            // KM_HT_QO_INVCHAIN / INVONEWAY: compose the one-way and chain-consumed
            // inverse bridges too (not just the single-role-body ones), so an ont
            // whose few inverse bridges are all composable reaches ZERO residual
            // bridges and the forward closure becomes complete. KM_HT_QO_GFCERT then
            // lets the certify-only router return that CLEAN global-forward closure
            // (sound+complete by construction; defers otherwise). Together these
            // recover 7581 (4 bridges → 0 residual, certifies ~18s) which the bare
            // certify-only kpset path defers to a CB timeout. Composition is a
            // semantics-preserving resolvent (compose_inverse), and GFCERT only
            // answers when global_fwd is fully clean — so no unsound/incomplete risk.
            ("KM_HT_QO_INVCHAIN", "1"),
            ("KM_HT_QO_INVONEWAY", "1"),
            ("KM_HT_QO_GFCERT", "1"),
            ("KM_HT_QO_CERTIFY_ONLY", "1"),
        ] {
            cmd.env(k, v);
        }
    }
    if shoq_candidate {
        // Activate the nominal o-rule + cardinality rules for the SHOQ route, and
        // force SINGLE-THREADED classify. KM_HT_NOMINALS makes run_json's nominal
        // path fire (set_nominals + set_number); KM_HT_QMERGE enables the qualified
        // ≤n merge and the ≥n recognition head. KM_HT_PAR=1 is REQUIRED: the
        // parallel per-concept classify is UNSOUND with the nominal o-rule (nominal
        // merges are global state; parallel workers race -> false-UNSAT, e.g. 10908
        // collapses to 86 of 6001 subs at PAR=8 but is gold-exact single-threaded).
        // These onts classify in <1s to a few seconds single-threaded, so no
        // parallelism is needed. Validated on ws: 10908 6001/6001 (0.22s), 15672
        // 142/142 (3s). Explicit env overrides win.
        for (k, v) in [
            ("KM_HT_NOMINALS", "1"),
            ("KM_HT_QMERGE", "1"),
            ("KM_HT_PAR", "1"),
        ] {
            if std::env::var_os(k).is_none() {
                cmd.env(k, v);
            }
        }
    }
    if card_candidate {
        // KM_HT_FORCE bypasses run_json's `number` in-fragment gate so the SHQ ont
        // reaches the fast Ht; the worker installs the first-class `card_defs` from
        // the TInput (independent of env) and the `≥n`/`≤n` rules fire instead of
        // the clausal Eq-merge. KM_HT_QMERGE is NOT set — the card rules replace it.
        // Single-threaded by default: `classify_parallel` IS now sound with card +
        // nominals (it re-installs `card_defs`/`nom_set` per worker), but the
        // per-concept card+nominal classify is heavy (ore_ont_9540: 86 nominals, 50
        // tests, ~18 GB, times out even all-cores) and all-cores here would
        // oversubscribe a concurrent sweep, so leave it serial; set KM_HT_PAR to opt
        // into the (sound) parallel card classify.
        for (k, v) in [
            ("KM_HT_FORCE", "1"),
            ("KM_HT_CARD", "1"),
            ("KM_HT_PAR", "1"),
        ] {
            if std::env::var_os(k).is_none() {
                cmd.env(k, v);
            }
        }
        // Propagation-based ≤n RECOGNITION (KM_HT_CARD_RECOG): replaces the
        // frontend's per-node `⊤→Q∨NQ` excluded middle (which branches on every
        // node × every cardinality definer -> disjunction non-convergence) with a
        // deterministic count at saturation (card_recog_step + filler_impossible).
        // When enabled, also activate the SHIQ non-shared-successor ∀ handling
        // (KM_HT_QO_SHIQ) and Konclude optimized blocking (mode 5) that keep the
        // recognition sound and convergent under inverse roles. Closes the small
        // SHIQ cardinality giants (10019 162/162, 12107 116/116, gold-exact vs the
        // HermiT transitive closure). Scoped to the card route only.
        if card_recog {
            for (k, v) in [("KM_HT_QO_SHIQ", "1"), ("KM_HT_BLOCK", "5")] {
                if std::env::var_os(k).is_none() {
                    cmd.env(k, v);
                }
            }
        }
    }
    // Production HT search discipline (validated on the live ∀+⊔ disjunction
    // family, ore_ont_5303): EAGER model folding + NEGTRIED (HermiT
    // startNextChoice) + ORD=1 (least-failing-first disjunct order). Together
    // these turn 5303 from a timeout into a sound+complete classification in
    // ~20s single-threaded (the inverted-index subset blocking is already the
    // default). Each is set only when not already specified in the environment,
    // so explicit overrides (e.g. for A/B testing) still win.
    // INCRBLOCK2: incremental subset blocking — re-evaluate only the changed node
    // suffix per saturation pass instead of rescanning every node. Result-identical
    // to the default full subset scan (validated byte-for-byte on the family); it
    // cut blocking from ~65% to ~23% of the per-test wall (5303 standalone 54s→25s).
    // INCROBLIG: incremental ∃-obligation processing — a pass scans only the
    // obligations of currently-unblocked, not-yet-discharged nodes instead of every
    // accumulated obligation. Result-identical to the flat scan; on 5303 it cut the
    // obligation loop 11x (240M→3M iterations), standalone 25s→10s single-threaded.
    for (k, v) in [
        ("KM_HT_EAGER", "1"),
        ("KM_HT_NEGTRIED", "1"),
        ("KM_HT_ORD", "1"),
        ("KM_HT_INCRBLOCK2", "1"),
        ("KM_HT_INCROBLIG", "1"),
    ] {
        if std::env::var_os(k).is_none() {
            cmd.env(k, v);
        }
    }
    // Parallelise the HT racer's per-concept SAT tests (KM_HT_PAR). The racer is
    // `nice`'d, so on ontologies CB wins these threads simply fill idle cores and
    // yield to CB; on the disjunction-family / central-blowup onts where CB never
    // finishes, the parallelism is what brings HT in under budget (5303: ~23s
    // single-threaded → ~10s). Default to the available core count; explicit
    // KM_HT_PAR wins.
    // NB shoq_candidate forces KM_HT_PAR=1 above (parallel classify is unsound with
    // the nominal o-rule); do not override it back to all-cores here.
    if std::env::var_os("KM_HT_PAR").is_none() && !shoq_candidate && !card_candidate {
        cmd.env("KM_HT_PAR", avail_cpus().max(1).to_string());
    }
    if cfg.ht_qo {
        // QuasiOrderClassification: non-branching park-saturation + residual SAT
        // tests. Contrapositives of clash clauses (A∧B=>⊥ ⇒ A=>¬B) feed unit
        // propagation inside the park fixpoint. Default OFF (opt-in via
        // KM_HT_QO): validation found it a strict -2 regression with no
        // recoveries (see config.rs / project_km_qo_deadend). Kept for the record.
        cmd.env("KM_HT_QO", "1").env("KM_HT_CONTRA", "1");
    }
    let mut child = cmd.spawn().ok()?;
    let stdin = child.stdin.take()?;
    let bytes = serde_json::to_vec(&tin).ok()?;
    thread::spawn(move || {
        let mut w = stdin;
        let _ = w.write_all(&bytes);
    });
    // The third element gates the SHORT race budget: true for the fast certify-or-
    // defer arms (SHOQ fast-Ht AND the QO hybrid). Both emit an answer ONLY when
    // they soundly+completely certify (CERTIFY_ONLY), so harvesting that answer as
    // soon as it is ready — instead of waiting out the full ht_budget_s for a doomed
    // CB — is monotone-safe (CB is still preferred whenever CB finishes first). The
    // QO arm certifies 7581 in ~17s but the old full-budget path never harvested it
    // within the 120-240s wall, so 7581 timed out despite a ready sound answer.
    // card_candidate joins the SHORT-race arms: the first-class card rules + o-rule
    // are a complete decision procedure for the SHQ/SHOQ fragment and fold quickly
    // (9540: 64 nodes, <1s), so harvest the answer after the short budget instead of
    // waiting out the doomed CB for the full ht_budget_s (which on a 240s sweep gives
    // the card arm only a 15s window). CB-preference is preserved: `take_cb` is
    // checked every loop iteration, so a card ont CB solves fast still goes to CB.
    Some((
        child,
        out_path,
        shoq_candidate || qo_candidate || card_candidate,
    ))
}

/// Reserved engine thread count for the HT race: reduce `KM_THREADS` by one when
/// it is set and > 1, else `avail-1` when unset, else leave unchanged. Reserves
/// one core for the single-threaded HT racer. Port of `_race_cb_vs_ht`'s
/// core-reservation arithmetic. Only applied when HT actually spawned.
fn ht_reserved_threads(cfg: &Config) -> Option<usize> {
    match cfg.threads {
        Some(n) if n > 1 => Some(n - 1),
        Some(n) => Some(n), // n <= 1: unchanged (1 stays 1)
        None => Some(avail_cpus().saturating_sub(1).max(1)),
    }
}

/// Race the CB engine stack against the KM_HT hypertableau. CB is the certified
/// sound+complete engine; HT is sound but incomplete on the live-disjunction
/// fragment, so the win rule is correctness-aware:
///   - "fallback" (default, monotone-safe): CB is preferred whenever it
///     finishes; HT's answer is taken ONLY when CB errors or runs past
///     `KM_HT_BUDGET_S`.
///   - "race" (speed): the first VALID finisher wins.
/// On a non-routable ontology HT never spawns and CB runs alone (no reservation).
/// `engine_run(threads)` runs the CB stack with the given thread count. Port of
/// `_race_cb_vs_ht`.
pub fn race_cb_vs_ht<F>(
    cfg: &Config,
    clauses_path: &Path,
    named: &std::collections::HashSet<String>,
    mode: &str,
    engine_run: F,
) -> Result<EngineOut, OrchestrateError>
where
    F: FnOnce(Option<usize>) -> Result<EngineOut, OrchestrateError> + Send,
{
    let (mut ht, ht_out, fast_certify) = match spawn_ht(cfg, clauses_path, named) {
        Some(x) => x,
        None => return engine_run(cfg.threads), // HT not routable: CB alone, no reservation
    };
    let reserved = ht_reserved_threads(cfg);
    // Fast certify-or-defer arms (SHOQ fast-Ht, QO hybrid): sound+complete on their
    // fragment and decide quickly (SHOQ <1-3s, QO certify ~tens of s), so take the
    // answer after a SHORT budget instead of waiting out the doomed CB for the full
    // ht_budget_s. CB still wins when it finishes first (preserves CB-preference /
    // monotone-safety on CB-solvable onts). The budget is only the "start accepting
    // HT" threshold: past it, the certified answer is harvested the moment it is
    // ready, so a QO arm that certifies later than the SHOQ default is still taken.
    let budget = if fast_certify {
        cfg.shoq_budget_s.min(cfg.ht_budget_s)
    } else {
        cfg.ht_budget_s
    };

    let read_tout = |p: &Path| -> Option<EngineOut> {
        let f = File::open(p).ok()?;
        serde_json::from_reader::<_, TOutput>(BufReader::new(f))
            .ok()
            .map(tableau_to_out)
    };

    // the CB result, written by the CB thread when it finishes — the analogue of
    // Python's `done` dict (Ok = `done["out"]`, Err = `done["exc"]`). Inspecting
    // it each iteration lets the loop distinguish "CB succeeded" (always prefer)
    // from "CB errored" (wait for HT) without consuming the join handle.
    let cb_slot: Arc<Mutex<Option<Result<EngineOut, OrchestrateError>>>> =
        Arc::new(Mutex::new(None));
    let race_mode = mode.to_string();
    let result: Result<EngineOut, OrchestrateError> = thread::scope(|s| {
        let slot = cb_slot.clone();
        s.spawn(move || {
            let r = engine_run(reserved);
            *slot.lock().unwrap() = Some(r);
        });

        let mut ht_res: Option<EngineOut> = None;
        let mut ht_polled = false;
        let t0 = Instant::now();
        let timing = std::env::var_os("KM_TIMING").is_some();
        let mut cb_logged = false;

        let mut interval = Duration::from_millis(1);
        loop {
            // poll HT once it finishes (capture its valid answer)
            if !ht_polled {
                if let Ok(Some(st)) = ht.try_wait() {
                    ht_polled = true;
                    if timing {
                        eprintln!(
                            "KM_TIMING race: HT worker exited @ {:.2}s (success={})",
                            t0.elapsed().as_secs_f64(),
                            st.success()
                        );
                    }
                    if st.success() {
                        ht_res = read_tout(ht_out.path());
                        if timing {
                            eprintln!(
                                "KM_TIMING race: read_tout done @ {:.2}s",
                                t0.elapsed().as_secs_f64()
                            );
                        }
                    }
                }
            }
            if timing && !cb_logged {
                if let Some(r) = cb_slot.lock().unwrap().as_ref() {
                    eprintln!(
                        "KM_TIMING race: CB slot filled @ {:.2}s (ok={})",
                        t0.elapsed().as_secs_f64(),
                        r.is_ok()
                    );
                    cb_logged = true;
                }
            }

            // inspect the CB result slot (without removing it unless we commit).
            let mut take_cb = false;
            let mut cb_errored = false;
            match cb_slot.lock().unwrap().as_ref() {
                Some(Ok(_)) => take_cb = true,     // CB succeeded: always prefer CB
                Some(Err(_)) => cb_errored = true, // CB errored: HT is the only hope
                None => {}
            }
            if take_cb {
                let cb = cb_slot.lock().unwrap().take().unwrap();
                let _ = ht.kill();
                let _ = ht.wait();
                return cb; // the scope joins the (finished) CB thread
            }

            if race_mode == "race" {
                if let Some(w) = ht_res.take() {
                    // HT finished first (and valid): kill CB and win.
                    engine_run::cancel_and_kill_engines();
                    let _ = ht.wait();
                    return Ok(w);
                }
                if cb_errored && ht_polled {
                    // CB failed and HT produced no valid answer: surface CB's error.
                    return cb_slot.lock().unwrap().take().unwrap();
                }
            } else {
                // fallback mode
                if cb_errored {
                    if let Some(w) = ht_res.take() {
                        let _ = ht.wait();
                        return Ok(w);
                    }
                    if ht_polled {
                        return cb_slot.lock().unwrap().take().unwrap();
                    }
                } else if t0.elapsed().as_secs_f64() > budget {
                    if let Some(w) = ht_res.take() {
                        // CB over budget: HT fills the gap.
                        engine_run::cancel_and_kill_engines();
                        let _ = ht.wait();
                        return Ok(w);
                    }
                }
            }
            thread::sleep(interval);
            interval = (interval * 2).min(Duration::from_millis(50));
        }
    });
    result
}
