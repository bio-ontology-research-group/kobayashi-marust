//! Reasoner races (Phase 3a — the deployed production config). Port of
//! `owl_classify._race_absorbed_plain`, `_spawn_tableau`, `_race_cb_vs_tableau`.
//!
//! `race_absorbed_plain` is SEQUENTIAL (an 8 s plain probe, then the absorbed set
//! with the full budget) — only one engine is ever resident, respecting the job
//! memcap. `race_cb_vs_tableau` is the one concurrent race: the engine work runs
//! in a scoped thread while the label-caching tableau is spawned lazily after a
//! grace delay; the first sound+complete finisher wins and the loser is killed
//! (`cancel_and_kill_engines` SIGKILLs the engine children and blocks any retry).

use std::borrow::Cow;
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
/// All three fields are REQUIRED: every tableau/HT worker serialises the full
/// `Classification` shape, so a structurally-valid-but-empty object (`{}`, a
/// truncated write, a version skew) must fail to parse — the race then treats
/// the arm as having no answer and CB stays authoritative — rather than decode
/// into a fail-open "consistent, nothing subsumes" verdict that would win the
/// race and kill the CB engine.
#[derive(serde::Deserialize)]
struct TOutput {
    consistent: bool,
    subsumptions: Vec<Vec<String>>,
    unsatisfiable: Vec<String>,
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
    let (cl, rbox, cards, definers, source_axioms, nominal_abox): (
        Vec<JClause>,
        Vec<Vec<String>>,
        Vec<crate::json_io::CardMeta>,
        Vec<crate::json_io::DefinerMeta>,
        Vec<crate::json_io::SourceAxiomMeta>,
        crate::json_io::NominalAboxMeta,
    ) = {
        // from_slice on a read buffer, not from_reader — the clause file is
        // multi-MB on large onts and the reader path is markedly slower.
        let buf = std::fs::read(clauses_path).ok()?;
        let v: JInput = serde_json::from_slice(&buf).ok()?;
        (
            v.clauses,
            v.rbox,
            v.cardinalities,
            v.definers,
            v.source_axioms,
            v.nominal_abox,
        )
    };
    // giants: the engine path owns them
    if cl.len() > cfg.tab_max_clauses {
        return None;
    }
    // no disjunctive head => deterministic => the engine handles it
    if !cl.iter().any(|c| c.head.len() >= 2) {
        return None;
    }
    let mut tin = cb_to_ht::convert(
        &cl,
        Some(&rbox),
        named,
        &cards,
        &definers,
        &source_axioms,
        false,
        &[],
        false,
    );
    cb_to_ht::install_nominal_abox(&mut tin, &nominal_abox);
    // Diagnostic parity with the HT racer: preserve the exact converted input
    // before any legacy-tableau fragment fence is applied.  This is inert unless
    // explicitly requested and makes a declined race distinguishable from a
    // worker failure without weakening a single soundness gate.
    if let Some(path) = std::env::var_os("KM_TAB_DUMP_TIN") {
        if let Ok(bytes) = serde_json::to_vec(&tin) {
            let _ = std::fs::write(path, bytes);
        }
    }
    if std::env::var_os("KM_TAB_TRACE").is_some() {
        eprintln!(
            "KM_TAB_ROUTE clauses={} converted={} dropped={} fenced={} nominals={} inverse={} number={}",
            cl.len(),
            tin.clauses.len(),
            tin.dropped,
            tin.fenced.len(),
            tin.nominals.len(),
            tin.inverse,
            tin.number,
        );
        for fence in &tin.fenced {
            eprintln!(
                "KM_TAB_ROUTE fence={} detail={}",
                fence.reason, fence.detail
            );
        }
    }
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

/// Fences that belong to the legacy fast tableau rather than the Konclude
/// completion bridge. The bridge has native inverse-role and cardinality
/// processing, so their combination is not a coverage loss there. Complex
/// domains/ranges are also exact when the bridge builds Konclude's native
/// terminology from `source_axioms`; they remain fenced on the reconstructed
/// clause path, where the complex source expression is no longer available.
fn bridge_fences_supported(tin: &cb_to_ht::TInput, source_tbox: bool) -> bool {
    tin.fenced.iter().all(|fence| {
        matches!(
            fence.reason.as_str(),
            "inverse+number(SHIQ)" | "inverse-functional"
        ) || (source_tbox && matches!(fence.reason.as_str(), "complex-domain" | "complex-range"))
            || (source_tbox
                && tin.nominal_abox.complete
                && fence.reason == "nominal+inverse(SHOI/SHOIQ)")
    })
}

/// A named specialist route must never degrade into the unrestricted legacy
/// HT racer when its structural/certificate candidate is absent. The general,
/// QO, SHOQ, and first-class-cardinality racers are useful as explicit
/// measurement arms, but corpus counterexamples show that each can return an
/// incomplete taxonomy. They therefore cannot masquerade as policy-safe
/// procedures. The Konclude completion bridge is different: its read-off path
/// either returns a complete answer or explicitly defers to CB.
///
/// `certified` is the production portfolio's mode (`PRODUCTION_ALL`,
/// `KM_MECHANISM=portfolio`). There the HT arm runs INSIDE `race_cb_vs_ht` in
/// fallback mode, where CB is authoritative: an HT arm's answer is taken ONLY
/// when the certified CB engine errors or runs past its budget. Under that
/// CB-preference the first-class cardinality arm is monotone-safe — it can only
/// ever replace a CB timeout, and the number rules are sound (they never assert
/// a subsumption CB would not), so admitting it recovers the SHQ/SHOQ number
/// onts (ore_ont_7499 / 9540, both previously 240 s timeouts) without a
/// MATCH-to-DIFF risk. This is the additive production cardinality behaviour the
/// pre-fence default already validated (job 48067625: 573 gold-MATCH). It is a
/// distinct question from policy-LEAF eligibility (`sriq_policy_eligible`, which
/// still excludes `HtCard`): the fence keeps the ISOLATED `ht_card` specialist —
/// where CB never runs — out of the learned tree, and this admittance only adds
/// the CB-guarded fallback arm. An inverse+nominal ontology becomes a card
/// candidate only when BOTH the source profile and the normalized HT input
/// certify that every number-role component is disjoint from inverse and
/// non-simple roles. Inputs such as ore_ont_10702 fail closed; recognition alone
/// does not expose their incomplete isolated-card result. SHOQ and QO stay
/// bridge-only under certified (their incomplete onts, e.g. 10702/15098, could
/// otherwise surface a wrong taxonomy on a CB timeout).
fn specialist_route_allows(
    requested: Option<&str>,
    qo_candidate: bool,
    shoq_candidate: bool,
    card_candidate: bool,
    bridge_candidate: bool,
) -> bool {
    match requested {
        None => true,
        Some("general") => true,
        Some("certified") => bridge_candidate || card_candidate,
        Some("qo") => qo_candidate,
        Some("shoq") => shoq_candidate,
        Some("card") => card_candidate,
        Some("bridge") => bridge_candidate,
        // Composite single-worker mechanisms. The common structural gate below
        // still requires at least one faithful candidate before spawning.
        Some("features") | Some("full") => true,
        Some(_) => false,
    }
}

/// Gate for `KM_HT_BRIDGE_ONLY`: the worker must produce NO answer when the
/// bridge arm declines (the legacy tableau is not a validated fallback) — but
/// ONLY when the bridge is genuinely the sole arm this worker carries. Under the
/// certified production portfolio a worker may carry BOTH a bridge and a card
/// arm; forcing bridge-only there would suppress the card fallback the bridge
/// defer should hand off to, so require the other candidates absent.
fn bridge_only_worker(
    requested: Option<&str>,
    bridge_candidate: bool,
    ht_routable: bool,
    qo_candidate: bool,
    shoq_candidate: bool,
    card_candidate: bool,
) -> bool {
    if !bridge_candidate {
        return false;
    }
    let no_other_arm = !qo_candidate && !shoq_candidate && !card_candidate;
    requested == Some("bridge")
        || (requested == Some("certified") && no_other_arm)
        || (!ht_routable && no_other_arm)
}

/// Whether this worker is the exact native-nominal bridge and has no legacy
/// HT arm that can answer after the bridge defers. The metadata still faces
/// the bridge's independent name/id/coverage validation before any result can
/// be published; this predicate controls scheduling only.
fn typed_nominal_bridge_exclusive(tin: &cb_to_ht::TInput, bridge_exclusive: bool) -> bool {
    bridge_exclusive
        && tin.nominal_abox.complete
        && tin.nominal_abox.unsupported.is_empty()
        && !tin.nominal_abox.individuals.is_empty()
}

/// The first-class number route (`KM_HT_CARD`): a faithful,
/// datatype/inverse/nominal-safe TInput carrying first-class `≥n`/`≤n`
/// restrictions (`card_defs`). Extracted so the exact gate the production
/// portfolio uses can be exercised on a reduced cardinality probe. `card_recog`
/// (propagation-based `≤n` recognition, default on) admits inverse only together
/// with the normalized role-separation certificate; datatype onts are always
/// excluded (no concrete-domain oracle in the fast Ht). Thus an arbitrary
/// inverse+nominal input cannot become a candidate merely by carrying card data.
fn card_candidate_from(
    tin: &cb_to_ht::TInput,
    ht_card: bool,
    card_recog: bool,
    has_datatype: bool,
) -> bool {
    ht_card
        && !tin.card_defs.is_empty()
        && tin.dropped == 0
        && tin.fenced.is_empty()
        && (!tin.inverse || (card_recog && tin.inverse_cardinality_role_separable))
        && (tin.nominals.is_empty() || tin.native_abox.complete)
        && native_abox_role_automata_separable(tin)
        && !has_datatype
}

/// Exact outer gate for the native completion bridge.  The bridge repeats a
/// stronger, input-level certificate check before it may return an answer.
fn bridge_candidate_from(tin: &cb_to_ht::TInput, bridge_enabled: bool, source_tbox: bool) -> bool {
    bridge_enabled
        && tin.dropped == 0
        && bridge_fences_supported(tin, source_tbox)
        && (tin.nominals.is_empty() || tin.nominal_abox.complete)
}

/// Independent normalized-side fence for native role assertions.
/// The Ht consumes ordinary subrole/inverse role clauses exactly, but raw
/// chain/transitivity axioms are represented as side data whose default use is
/// universal propagation, not materializing every named-individual edge. A
/// negative assertion is therefore admitted only when its entire role-clause
/// component is disjoint from all chain/transitive roles; a positive assertion
/// must be disjoint from every proper chain component. This repeats the source
/// proof after name resolution and cb_to_ht conversion.
fn native_abox_role_automata_separable(tin: &cb_to_ht::TInput) -> bool {
    use std::collections::HashSet;

    if tin.native_abox.negative_role_assertions.is_empty()
        && tin.native_abox.role_assertions.is_empty()
    {
        return true;
    }
    let mut adjacency: Vec<HashSet<usize>> = vec![HashSet::new(); tin.roles.len()];
    let mut connect = |roles: &[usize]| {
        for &left in roles {
            for &right in roles {
                if left < adjacency.len() && right < adjacency.len() && left != right {
                    adjacency[left].insert(right);
                }
            }
        }
    };
    for clause in &tin.clauses {
        let mut roles: Vec<usize> = clause
            .body
            .iter()
            .chain(clause.head.iter())
            .filter_map(|atom| match atom {
                cb_to_ht::HAtom::Role { r, .. } => Some(*r),
                _ => None,
            })
            .collect();
        roles.sort_unstable();
        roles.dedup();
        connect(&roles);
    }
    let mut non_simple = HashSet::new();
    let mut proper_chain_roles = HashSet::new();
    for &(left, right, target) in &tin.chains {
        connect(&[left, right, target]);
        non_simple.extend([left, right, target]);
        if !(left == right && right == target && tin.transitive.contains(&left)) {
            proper_chain_roles.extend([left, right, target]);
        }
    }
    non_simple.extend(tin.transitive.iter().copied());

    let mut seen = HashSet::new();
    let mut pending: Vec<usize> = tin
        .native_abox
        .negative_role_assertions
        .iter()
        .map(|&(role, _, _)| role)
        .collect();
    while let Some(role) = pending.pop() {
        if role >= adjacency.len() {
            return false;
        }
        if !seen.insert(role) {
            continue;
        }
        if non_simple.contains(&role) {
            return false;
        }
        pending.extend(adjacency[role].iter().copied());
    }

    let mut seen_positive = HashSet::new();
    let mut pending_positive: Vec<usize> = tin
        .native_abox
        .role_assertions
        .iter()
        .map(|&(role, _, _)| role)
        .collect();
    while let Some(role) = pending_positive.pop() {
        if role >= adjacency.len() {
            return false;
        }
        if !seen_positive.insert(role) {
            continue;
        }
        if proper_chain_roles.contains(&role) {
            return false;
        }
        pending_positive.extend(adjacency[role].iter().copied());
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

/// True only for a ground/singleton clause represented independently by the
/// complete typed ABox. This is an exact pattern filter, not a generic
/// individual-term projection: unknown shapes remain for conversion to reject.
fn native_nominal_clause_represented(
    clause: &JClause,
    nominal_abox: &crate::json_io::NominalAboxMeta,
    definers: &[crate::json_io::DefinerMeta],
) -> bool {
    use crate::frontend::syntax::Concept;
    use crate::json_io::DefinerKind;
    use crate::json_io::{JAtom, JTerm};

    let entry = |individual: &str| {
        nominal_abox
            .individuals
            .iter()
            .find(|entry| entry.individual == individual)
    };
    let proxy_maps_to = |proxy: &str, individual: &str| {
        entry(individual).is_some_and(|entry| entry.proxies.iter().any(|name| name == proxy))
    };
    let exact_top_definer = |marker: &str| {
        let mut definitions = definers.iter().filter(|definer| definer.marker == marker);
        definitions.next().is_some_and(|definer| {
            definer.kind == DefinerKind::Top
                && definer.operands.is_empty()
                && definer.role.is_none()
                && definer.n.is_none()
        }) && definitions.next().is_none()
    };
    let role_matches = |assertions: &[crate::json_io::NominalRoleAssertionMeta],
                        role: &str,
                        source: &str,
                        target: &str| {
        assertions.iter().any(|assertion| {
            assertion.role == role && assertion.source == source && assertion.target == target
        })
    };
    let assertion_marker_maps_to = |marker: &str, individual: &str| {
        entry(individual).is_some_and(|entry| {
            entry
                .assertion_markers
                .iter()
                .enumerate()
                .any(|(index, name)| {
                    name == marker
                        && entry
                            .assertions
                            .get(index)
                            .is_some_and(|assertion| match assertion {
                                Concept::Top => exact_top_definer(marker),
                                Concept::Name(name) => name == marker,
                                _ => true,
                            })
                })
        })
    };

    match (clause.body.as_slice(), clause.head.as_slice()) {
        // Source ClassAssertion marker, or DL7 `top -> proxy(individual)`.
        (
            [],
            [JAtom::Concept {
                concept,
                term: JTerm::Ind { name },
            }],
        ) => {
            proxy_maps_to(concept, name)
                || entry(name).is_some_and(|entry| {
                    entry
                        .assertions
                        .iter()
                        .any(|assertion| assertion == &Concept::Name(concept.clone()))
                        // The normalizer reifies ClassAssertion(owl:Thing, i)
                        // as `[] -> Q_top(i)`. The typed payload retains the
                        // source `Top`, and trigger provenance independently
                        // proves that this exact marker denotes Top. Both
                        // sides are required; an arbitrary Q_* ground fact is
                        // never projected merely because it looks internal.
                        || (exact_top_definer(concept)
                            && entry
                                .assertions
                                .iter()
                                .any(|assertion| matches!(assertion, Concept::Top)))
                })
                || assertion_marker_maps_to(concept, name)
        }
        // Source ObjectPropertyAssertion.
        (
            [],
            [JAtom::Role {
                role,
                source: JTerm::Ind { name: source },
                target: JTerm::Ind { name: target },
            }],
        ) => role_matches(&nominal_abox.role_assertions, role, source, target),
        // Source NegativeObjectPropertyAssertion.
        (
            [JAtom::Role {
                role,
                source: JTerm::Ind { name: source },
                target: JTerm::Ind { name: target },
            }],
            [],
        ) => role_matches(&nominal_abox.negative_role_assertions, role, source, target),
        // Pairwise parser expansion of DifferentIndividuals.
        (
            [JAtom::Eq {
                left: JTerm::Ind { name: left },
                right: JTerm::Ind { name: right },
            }],
            [],
        ) => nominal_abox
            .different
            .iter()
            .any(|(a, b)| (a == left && b == right) || (a == right && b == left)),
        // DL8: proxy(x) -> x = individual. DL7 (top -> proxy(ind)) is
        // recognized by the first arm through the same exact proxy mapping.
        (
            [JAtom::Concept {
                concept: proxy,
                term: JTerm::Var { name: body_var },
            }],
            [JAtom::Eq { left, right }],
        ) => {
            let mapped = match (left, right) {
                (JTerm::Var { name: eq_var }, JTerm::Ind { name: individual })
                | (JTerm::Ind { name: individual }, JTerm::Var { name: eq_var })
                    if eq_var == body_var =>
                {
                    Some(individual.as_str())
                }
                _ => None,
            };
            mapped.is_some_and(|individual| proxy_maps_to(proxy, individual))
        }
        // Any other individual-bearing clause stays in the HT conversion. The
        // converter will count unsupported ground/mixed terms and the bridge
        // candidate will defer instead of trusting an unproved projection.
        _ => false,
    }
}

/// Clause view for the certified bridge arm of `certified_nominals`.
///
/// `KM_NOMINALS` deliberately adds ground ABox and singleton-defining clauses
/// for the exact CB fallback. `cb_to_ht` cannot translate ground terms and
/// would count those clauses as dropped before the native bridge sees the
/// typed `nominal_abox` channel. When that channel carries the frontend's
/// complete certificate, remove only exact clause shapes independently
/// represented by that payload. Any other individual-bearing clause remains,
/// making `cb_to_ht` count the unsupported construct and forcing a bridge
/// defer. The original clause file is untouched and remains the input of the
/// nominal-aware CB arm.
fn native_nominal_bridge_clauses<'a>(
    clauses: &'a [JClause],
    nominal_abox: &crate::json_io::NominalAboxMeta,
    definers: &[crate::json_io::DefinerMeta],
    enabled: bool,
    has_rules: bool,
) -> Cow<'a, [JClause]> {
    if !enabled
        || has_rules
        || !nominal_abox.complete
        || !nominal_abox.unsupported.is_empty()
        || nominal_abox.individuals.is_empty()
    {
        return Cow::Borrowed(clauses);
    }
    Cow::Owned(
        clauses
            .iter()
            .filter(|clause| !native_nominal_clause_represented(clause, nominal_abox, definers))
            .cloned()
            .collect(),
    )
}

/// Exact clause view for the native nominal fast-Ht tests and callers that do
/// not have definer provenance. In particular, a reified Top assertion remains
/// unprojected here and therefore forces an honest defer.
fn native_nominal_ht_view<'a>(
    clauses: &'a [JClause],
    nominal_abox: &crate::json_io::NominalAboxMeta,
    enabled: bool,
    has_rules: bool,
) -> Cow<'a, [JClause]> {
    native_nominal_bridge_clauses(clauses, nominal_abox, &[], enabled, has_rules)
}

/// Spawn `tableau_cli` under `KM_HT=1` as a racer on the HT-routable fragment.
/// Returns `(child, out_path)` or `None`. Port of `_spawn_ht`.
fn spawn_ht(
    cfg: &Config,
    clauses_path: &Path,
    named: &std::collections::HashSet<String>,
) -> Option<(
    Child,
    super::tmpfile::TempPath,
    bool,
    Option<usize>,
    bool,
    bool,
)> {
    let (tab_prog, tab_pre) = cfg.tab_cmd();
    let (cl, rbox, cards, definers, source_axioms, nominal_abox, rules): (
        Vec<JClause>,
        Vec<Vec<String>>,
        Vec<crate::json_io::CardMeta>,
        Vec<crate::json_io::DefinerMeta>,
        Vec<crate::json_io::SourceAxiomMeta>,
        crate::json_io::NominalAboxMeta,
        Vec<crate::json_io::JRule>,
    ) = {
        // from_slice on a read buffer, not from_reader — the clause file is
        // multi-MB on large onts and the reader path is markedly slower.
        let buf = std::fs::read(clauses_path).ok()?;
        let v: JInput = serde_json::from_slice(&buf).ok()?;
        (
            v.clauses,
            v.rbox,
            v.cardinalities,
            v.definers,
            v.source_axioms,
            v.nominal_abox,
            v.rules,
        )
    };
    let _tconv = Instant::now();
    let nominal_bridge_view = native_nominal_bridge_clauses(
        &cl,
        &nominal_abox,
        &definers,
        std::env::var_os("KM_NOMINALS").is_some()
            && std::env::var_os("KM_TRIGGER_ABSORB").is_some(),
        !rules.is_empty(),
    );
    let mut tin = cb_to_ht::convert(
        &nominal_bridge_view,
        Some(&rbox),
        named,
        &cards,
        &definers,
        &source_axioms,
        std::env::var_os("KM_NO_HT_CARD").is_none(),
        &[],
        false,
    );
    cb_to_ht::install_nominal_abox(&mut tin, &nominal_abox);
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
    // cannot (the disjunction-family cardinality wall). Inverse is admitted only
    // under the dual source/normalized number-role separation certificate;
    // uncertified SHIQ stays fenced. Datatype onts are excluded (no concrete-domain
    // oracle in the Ht). Computed FIRST so it
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
    // KM_HT_PAR=1, which the nominal o-rule requires (parallel merges race).
    // KM_HT_CARD_RECOG (propagation-based ≤n recognition, see the card env block
    // below) is necessary but not sufficient for inverse inputs. The route also
    // requires `inverse_cardinality_role_separable`, independently reconstructed
    // from normalized clauses/RBox data. That certificate rules out the NN/NI
    // nominal-predecessor premise missing from the fast HT while inverse axioms
    // themselves remain exact. Uncertified inverse+cardinality inputs stay out;
    // datatype inputs always stay out (no concrete-domain oracle in the Ht).
    let card_recog = std::env::var_os("KM_NO_HT_CARD_RECOG").is_none();
    let card_candidate = card_candidate_from(&tin, cfg.ht_card, card_recog, has_datatype(&cl));
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
        && tin.native_abox.complete
        && !has_datatype(&cl);
    // KM_HT_BRIDGE route: the konclude_ht bridge (Konclude's completion kernel
    // in Rust) answers sound+complete-or-DEFER by construction (deterministic
    // read-off / pairwise-verified candidates; declines anything it cannot
    // encode losslessly). Nominal-free faithful TInputs only; the worker's
    // bridge arm re-checks coverage per clause. Nominal inputs require the
    // typed source/ABox certificate; the worker independently re-checks it.
    let trigger_bridge = std::env::var_os("KM_TRIGGER_ABSORB").is_some();
    let source_tbox = trigger_bridge
        && !tin.source_axioms.is_empty()
        && std::env::var_os("KM_NO_SOURCE_TBOX").is_none();
    let bridge_candidate = bridge_candidate_from(
        &tin,
        std::env::var_os("KM_HT_BRIDGE").is_some() || trigger_bridge,
        source_tbox,
    );
    let specialist_only = std::env::var("KM_HT_ONLY").ok();
    if !specialist_route_allows(
        specialist_only.as_deref(),
        qo_candidate,
        shoq_candidate,
        card_candidate,
        bridge_candidate,
    ) {
        return None;
    }
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
    if bridge_candidate || std::env::var_os("KM_TRIGGER_ABSORB").is_some() {
        cmd.env("KM_HT_BRIDGE", "1");
    }
    let bridge_exclusive = bridge_only_worker(
        specialist_only.as_deref(),
        bridge_candidate,
        ht_routable(&tin),
        qo_candidate,
        shoq_candidate,
        card_candidate,
    );
    if bridge_exclusive {
        // The bridge is the ONLY reason this worker was spawned: if its arm
        // declines, the worker must produce NO answer (the legacy tableau is
        // not validated on this fragment — "tableau is NOT a fallback"). When a
        // card arm rides along (certified production portfolio), the worker must
        // instead hand a bridge defer off to the card path, so this stays unset.
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
        // into the parallel card classify.
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
        // recognition convergent and preserve inverse semantics for the separately
        // certified number-role fragment. Closes the small SHIQ cardinality giants
        // (10019 162/162, 12107 116/116, gold-exact vs the HermiT transitive
        // closure). Scoped to the card route only; recognition itself is never
        // treated as an inverse/cardinality soundness certificate.
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
    let typed_nominal_exclusive = typed_nominal_bridge_exclusive(&tin, bridge_exclusive);
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
        shoq_candidate || qo_candidate || card_candidate || bridge_candidate,
        bridge_candidate.then_some(tin.queries.len()),
        // Whether KM_HT_BRIDGE_ONLY was set on this worker: only then does the
        // race scheduler's instant (0 s) trigger-absorb harvest apply — any
        // other worker can answer from a non-bridge arm without the bridge's
        // complete-answer-or-defer guarantee.
        bridge_exclusive,
        // Only the native bridge consumes this exact typed ABox channel.  The
        // scheduler uses the conjunction with bridge exclusivity to prevent a
        // speculative multi-threaded CB fallback from starving that serial,
        // certified worker without ever making the bridge authoritative.
        typed_nominal_exclusive,
    ))
}

/// Run exactly the selected HT mechanism. Unlike `race_cb_vs_ht`, this starts
/// no CB thread and has no fallback: a structural gate failure or a
/// certify-only defer is reported as out-of-fragment to the caller.
pub fn run_ht_only(
    cfg: &Config,
    clauses_path: &Path,
    named: &std::collections::HashSet<String>,
) -> Result<EngineOut, OrchestrateError> {
    let Some((mut child, out_path, _, _, _, _)) = spawn_ht(cfg, clauses_path, named) else {
        return Err(OrchestrateError::OutOfFragment(
            "ontology is outside the selected HT mechanism's structural gate".into(),
        ));
    };
    let status = child.wait()?;
    if !status.success() {
        return Err(OrchestrateError::OutOfFragment(format!(
            "selected HT mechanism deferred (worker exit {})",
            status.code().unwrap_or(-1)
        )));
    }
    let output = File::open(out_path.path())?;
    let parsed: TOutput = serde_json::from_reader(BufReader::new(output)).map_err(|error| {
        OrchestrateError::Worker {
            bin: "tableau/ht".into(),
            code: 0,
            stderr: format!("successful worker emitted no valid taxonomy: {error}"),
        }
    })?;
    Ok(tableau_to_out(parsed))
}

/// Run the historical label-caching tableau as an isolated mechanism. Its
/// existing structural gate remains authoritative, but CB is never started if
/// the gate declines or the worker fails.
pub fn run_tableau_only(
    cfg: &Config,
    clauses_path: &Path,
    named: &std::collections::HashSet<String>,
) -> Result<EngineOut, OrchestrateError> {
    let Some((mut child, out_path)) = spawn_tableau(cfg, clauses_path, named) else {
        return Err(OrchestrateError::OutOfFragment(
            "ontology is outside the selected tableau mechanism's structural gate".into(),
        ));
    };
    let status = child.wait()?;
    if !status.success() {
        return Err(OrchestrateError::Worker {
            bin: "tableau".into(),
            code: status.code().unwrap_or(-1),
            stderr: String::new(),
        });
    }
    let output = File::open(out_path.path())?;
    let parsed: TOutput = serde_json::from_reader(BufReader::new(output))?;
    Ok(tableau_to_out(parsed))
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

/// The Konclude completion bridge currently executes its KPSet satisfiability
/// jobs synchronously. On very large class sets, letting the speculative CB arm
/// occupy every remaining core starves that serial, certified arm on memory
/// bandwidth. `ore_ont_3215` is the measured boundary case: 54,974 active
/// classes finish in 137 s with one CB competitor thread but exceed 240 s with
/// fifteen, while producing the same gold-exact result.
///
/// A typed-nominal bridge has the same contention pattern below that generic
/// threshold: ORE 10621 has 41,647 active classes, but its exact nominal-aware
/// CB fallback with fifteen threads pushes the shared race to 16.8 GiB and both
/// arms miss the standard limit. Give that fallback one thread only when the
/// typed channel is complete and the worker is bridge-exclusive. A bridge
/// defer still leaves the exact CB computation running; no answer is accepted
/// without one of the unchanged reasoner certificates.
///
/// This changes only concurrent scheduling. Both reasoners and the fallback/
/// winner rules remain unchanged.
const LARGE_SYNCHRONOUS_BRIDGE_CLASS_COUNT: usize = 50_000;

fn limit_synchronous_bridge_competitor(
    reserved: Option<usize>,
    bridge_class_count: Option<usize>,
    typed_nominal_bridge_exclusive: bool,
) -> Option<usize> {
    if typed_nominal_bridge_exclusive
        || bridge_class_count.is_some_and(|count| count >= LARGE_SYNCHRONOUS_BRIDGE_CLASS_COUNT)
    {
        Some(1)
    } else {
        reserved
    }
}

/// Wall-clock threshold after which a finished HT answer is accepted in
/// fallback mode. Under source-terminology trigger absorption a
/// BRIDGE-EXCLUSIVE worker's answer can only come from the Konclude bridge
/// (sound+complete or no result — `KM_HT_BRIDGE_ONLY` forbids any other arm
/// from answering), so it is harvested the moment it is ready — waiting out
/// CB's fallback budget on a 3215-scale terminology would discard a finished
/// exact closure. The instant harvest is gated on `bridge_exclusive`: a
/// certified worker that also carries a card (or, under manual env
/// combinations, a legacy/specialist) arm can emit an answer that does NOT
/// carry the bridge's complete-answer-or-defer guarantee, and accepting that
/// at 0 s would let it preempt a healthy CB run — those workers keep the
/// fast-certify / full HT budgets. CB is still preferred whenever it
/// finishes: the CB slot is checked before the budget on every loop
/// iteration.
fn ht_acceptance_budget(
    trigger_absorb: bool,
    bridge_exclusive: bool,
    fast_certify: bool,
    shoq_budget_s: f64,
    ht_budget_s: f64,
) -> f64 {
    if trigger_absorb && bridge_exclusive {
        0.0
    } else if fast_certify {
        shoq_budget_s.min(ht_budget_s)
    } else {
        ht_budget_s
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
    let (
        mut ht,
        ht_out,
        fast_certify,
        bridge_class_count,
        bridge_exclusive,
        typed_nominal_exclusive,
    ) = match spawn_ht(cfg, clauses_path, named) {
        Some(x) => x,
        None => return engine_run(cfg.threads), // HT not routable: CB alone, no reservation
    };
    let reserved = limit_synchronous_bridge_competitor(
        ht_reserved_threads(cfg),
        bridge_class_count,
        typed_nominal_exclusive,
    );
    if std::env::var_os("KM_TIMING").is_some()
        && (typed_nominal_exclusive
            || bridge_class_count
                .is_some_and(|count| count >= LARGE_SYNCHRONOUS_BRIDGE_CLASS_COUNT))
    {
        eprintln!(
            "KM_TIMING race: synchronous bridge classes={} typed_nominal={} cb_threads={}",
            bridge_class_count.unwrap_or_default(),
            typed_nominal_exclusive,
            reserved.unwrap_or(1),
        );
    }
    // Fast certify-or-defer arms (SHOQ fast-Ht, QO hybrid): sound+complete on their
    // fragment and decide quickly (SHOQ <1-3s, QO certify ~tens of s), so take the
    // answer after a SHORT budget instead of waiting out the doomed CB for the full
    // ht_budget_s. CB still wins when it finishes first (preserves CB-preference /
    // monotone-safety on CB-solvable onts). The budget is only the "start accepting
    // HT" threshold: past it, the certified answer is harvested the moment it is
    // ready, so a QO arm that certifies later than the SHOQ default is still taken.
    let budget = ht_acceptance_budget(
        std::env::var_os("KM_TRIGGER_ABSORB").is_some(),
        bridge_exclusive,
        fast_certify,
        cfg.shoq_budget_s,
        cfg.ht_budget_s,
    );

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

        // RSS cap on the HT racer (KM_HT_MEM_GB, default 12): the HT arm is a
        // helper — it must never grow until the harness memcap kills the WHOLE
        // process group (observed: ore_ont_541's bridge arm reached 56 GB in
        // 51 s and turned a CB timeout into a memout). Kill the arm over-cap
        // and let CB keep its full budget; monotone-safe (same as HT erroring).
        let ht_cap_bytes: u64 = {
            let gb = std::env::var("KM_HT_MEM_GB")
                .ok()
                .and_then(|v| v.parse::<f64>().ok())
                .unwrap_or(12.0);
            (gb * (1u64 << 30) as f64) as u64
        };

        let mut interval = Duration::from_millis(1);
        loop {
            // watchdog the still-running HT racer's RSS
            if !ht_polled {
                if let Some(rss) = engine_run::read_rss(ht.id()) {
                    if rss > ht_cap_bytes {
                        if timing {
                            eprintln!(
                                "KM_TIMING race: HT worker over memcap ({} MB) @ {:.2}s, killed",
                                rss >> 20,
                                t0.elapsed().as_secs_f64()
                            );
                        }
                        let _ = ht.kill();
                    }
                }
            }
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

#[cfg(test)]
mod tests {
    use super::*;

    fn ind(name: &str) -> crate::json_io::JTerm {
        crate::json_io::JTerm::Ind { name: name.into() }
    }

    fn var(name: &str) -> crate::json_io::JTerm {
        crate::json_io::JTerm::Var { name: name.into() }
    }

    #[test]
    fn native_nominal_view_filters_only_exact_typed_shapes_and_preserves_cb_input() {
        use crate::json_io::{
            JAtom, JClause, NominalAboxMeta, NominalIndividualMeta, NominalRoleAssertionMeta,
        };
        let meta = NominalAboxMeta {
            complete: true,
            individuals: vec![
                NominalIndividualMeta {
                    individual: "a".into(),
                    proxies: vec!["NA".into()],
                    assertions: vec![crate::frontend::syntax::Concept::Name("A".into())],
                    assertion_markers: vec!["A".into()],
                },
                NominalIndividualMeta {
                    individual: "b".into(),
                    proxies: vec!["NB".into()],
                    assertions: Vec::new(),
                    assertion_markers: Vec::new(),
                },
            ],
            different: vec![("a".into(), "b".into())],
            role_assertions: vec![NominalRoleAssertionMeta {
                role: "r".into(),
                source: "a".into(),
                target: "b".into(),
            }],
            negative_role_assertions: vec![NominalRoleAssertionMeta {
                role: "s".into(),
                source: "b".into(),
                target: "a".into(),
            }],
            unsupported: Vec::new(),
        };
        let clauses = vec![
            JClause {
                body: Vec::new(),
                head: vec![JAtom::Concept {
                    concept: "NA".into(),
                    term: ind("a"),
                }],
            },
            JClause {
                body: Vec::new(),
                head: vec![JAtom::Concept {
                    concept: "A".into(),
                    term: ind("a"),
                }],
            },
            JClause {
                body: Vec::new(),
                head: vec![JAtom::Role {
                    role: "r".into(),
                    source: ind("a"),
                    target: ind("b"),
                }],
            },
            JClause {
                body: vec![JAtom::Role {
                    role: "s".into(),
                    source: ind("b"),
                    target: ind("a"),
                }],
                head: Vec::new(),
            },
            JClause {
                body: vec![JAtom::Eq {
                    left: ind("a"),
                    right: ind("b"),
                }],
                head: Vec::new(),
            },
            JClause {
                body: vec![JAtom::Concept {
                    concept: "NA".into(),
                    term: var("x"),
                }],
                head: vec![JAtom::Eq {
                    left: var("x"),
                    right: ind("a"),
                }],
            },
            // Unknown ground clause: contains an individual but is not in the
            // typed payload, so it must remain for cb_to_ht to reject/fence.
            JClause {
                body: Vec::new(),
                head: vec![JAtom::Concept {
                    concept: "UNKNOWN".into(),
                    term: ind("a"),
                }],
            },
            // Near-DL8 with a mismatched equality variable must also remain.
            JClause {
                body: vec![JAtom::Concept {
                    concept: "NA".into(),
                    term: var("x"),
                }],
                head: vec![JAtom::Eq {
                    left: var("y"),
                    right: ind("a"),
                }],
            },
        ];
        let original_bytes = serde_json::to_vec(&clauses).unwrap();
        let view = native_nominal_ht_view(&clauses, &meta, true, false);
        assert_eq!(view.len(), 2, "only the two unknown shapes remain");
        assert_eq!(
            serde_json::to_vec(&clauses).unwrap(),
            original_bytes,
            "the complete CB clause vector must be byte-identical after making the HT view"
        );
        assert!(matches!(view, Cow::Owned(_)));

        let disabled = native_nominal_ht_view(&clauses, &meta, false, false);
        assert!(matches!(disabled, Cow::Borrowed(_)));
        assert_eq!(serde_json::to_vec(&*disabled).unwrap(), original_bytes);
    }

    #[test]
    fn source_auto_route_serializes_and_consumes_the_complete_native_card_abox() {
        // Reduced 9540 shape: first-class has_point cardinality plus a direct
        // positive/negative has_point clash on named roots; a separate active
        // inverse role pair; and DifferentIndividuals. The test crosses every
        // production boundary: source OFN -> auto route -> exact HT clause view
        // -> cb_to_ht numeric install -> serialized worker input -> run_json.
        let source = r#"
            Prefix(:=<http://example.org/>)
            Ontology(
              Declaration(Class(:Shape))
              Declaration(Class(:Point))
              Declaration(Class(:Other))
              Declaration(ObjectProperty(:has_point))
              Declaration(ObjectProperty(:is_front))
              Declaration(ObjectProperty(:is_back))
              Declaration(NamedIndividual(:a))
              Declaration(NamedIndividual(:b))
              InverseObjectProperties(:is_front :is_back)
              ObjectPropertyRange(:is_back :Other)
              SubClassOf(:Shape ObjectSomeValuesFrom(:is_front :Other))
              SubClassOf(:Shape ObjectExactCardinality(1 :has_point :Point))
              ClassAssertion(:Shape :a)
              ObjectPropertyAssertion(:has_point :a :b)
              NegativeObjectPropertyAssertion(:has_point :a :b)
              DifferentIndividuals(:a :b)
            )
        "#;
        crate::frontend::with_ofn_to_clauses_requested_route(
            source,
            crate::routing::Route::Auto,
            |frontend| {
                assert_eq!(
                    frontend.route,
                    crate::routing::Route::CertifiedCardNominals.as_str()
                );
                assert!(frontend.profile.inverse_cardinality_role_separable);
                assert_eq!(
                    crate::routing::select(&frontend.profile),
                    crate::routing::Route::CertifiedCardNominals,
                    "the automatic source-profile policy selects the certified native-card route"
                );
                assert!(frontend.nominal_abox.complete);
                assert_eq!(frontend.nominal_abox.individuals.len(), 2);
                assert_eq!(frontend.nominal_abox.role_assertions.len(), 1);
                assert_eq!(frontend.nominal_abox.negative_role_assertions.len(), 1);
                assert_eq!(frontend.nominal_abox.different.len(), 1);
                assert!(!frontend.cardinalities.is_empty());

                let original_cb = serde_json::to_vec(&frontend.clauses).unwrap();
                let ht_view =
                    native_nominal_ht_view(&frontend.clauses, &frontend.nominal_abox, true, false);
                let named: std::collections::HashSet<String> =
                    frontend.named.iter().cloned().collect();
                let mut tin = cb_to_ht::convert(
                    &ht_view,
                    Some(&frontend.rbox),
                    &named,
                    &frontend.cardinalities,
                    &frontend.definers,
                    &frontend.source_axioms,
                    true,
                    &[],
                    false,
                );
                assert!(cb_to_ht::install_nominal_abox(
                    &mut tin,
                    &frontend.nominal_abox
                ));
                assert_eq!(
                    serde_json::to_vec(&frontend.clauses).unwrap(),
                    original_cb,
                    "constructing the HT view must not mutate the exact CB source vector"
                );
                assert!(tin.inverse_cardinality_role_separable);
                assert!(card_candidate_from(&tin, true, true, false));

                let wire = serde_json::to_string(&tin).unwrap();
                let output = crate::tableau::run_json_for_native_ht_test(&wire)
                    .expect("native card Ht consumes its complete wire payload");
                let output: serde_json::Value = serde_json::from_str(&output).unwrap();
                assert_eq!(
                    output["consistent"], false,
                    "the typed role clash must fire"
                );
            },
        )
        .expect("source fixture parses through automatic production routing");
    }

    #[test]
    fn native_nominal_bridge_view_preserves_the_exact_cb_clause_file() {
        use crate::frontend::syntax::Concept;
        use crate::json_io::{JAtom, JTerm, NominalAboxMeta, NominalIndividualMeta};

        let var = || JTerm::Var { name: "x".into() };
        let ind = |name: &str| JTerm::Ind { name: name.into() };
        let clauses = vec![
            // Ground class assertion retained for the nominal-aware CB arm.
            JClause {
                body: vec![],
                head: vec![JAtom::Concept {
                    concept: "A".into(),
                    term: ind("b"),
                }],
            },
            // DL7 is removed only because the typed payload maps this exact
            // proxy spelling to this exact individual.
            JClause {
                body: vec![],
                head: vec![JAtom::Concept {
                    concept: "__nom__a".into(),
                    term: ind("a"),
                }],
            },
            // Singleton defining equality retained for CB and reconstructed
            // natively by the bridge from the typed proxy mapping.
            JClause {
                body: vec![JAtom::Concept {
                    concept: "__nom__a".into(),
                    term: var(),
                }],
                head: vec![JAtom::Eq {
                    left: var(),
                    right: ind("a"),
                }],
            },
            // Pairwise expansion of DifferentIndividuals(a,b).
            JClause {
                body: vec![JAtom::Eq {
                    left: ind("a"),
                    right: ind("b"),
                }],
                head: vec![],
            },
            // Ordinary TBox clause remains in both arms.
            JClause {
                body: vec![JAtom::Concept {
                    concept: "A".into(),
                    term: var(),
                }],
                head: vec![JAtom::Concept {
                    concept: "C".into(),
                    term: var(),
                }],
            },
            // An unsupported mixed-individual clause is not inferred from the
            // presence of the same individual in the payload. It must remain
            // so cb_to_ht records the coverage loss and the bridge defers.
            JClause {
                body: vec![JAtom::Concept {
                    concept: "A".into(),
                    term: ind("a"),
                }],
                head: vec![JAtom::Concept {
                    concept: "C".into(),
                    term: var(),
                }],
            },
            // Likewise, a DL8-looking clause for a proxy not mapped by the
            // typed ObjectOneOf/ObjectHasValue coverage must remain.
            JClause {
                body: vec![JAtom::Concept {
                    concept: "__nom__uncovered".into(),
                    term: var(),
                }],
                head: vec![JAtom::Eq {
                    left: var(),
                    right: ind("a"),
                }],
            },
        ];
        let exact = NominalAboxMeta {
            complete: true,
            individuals: vec![
                NominalIndividualMeta {
                    individual: "a".into(),
                    proxies: vec!["__nom__a".into()],
                    assertions: vec![],
                    assertion_markers: vec![],
                },
                NominalIndividualMeta {
                    individual: "b".into(),
                    proxies: vec!["__nom__b".into()],
                    assertions: vec![Concept::Name("A".into())],
                    assertion_markers: vec!["A".into()],
                },
            ],
            different: vec![("a".into(), "b".into())],
            role_assertions: vec![],
            negative_role_assertions: vec![],
            unsupported: vec![],
        };

        let bridge = native_nominal_bridge_clauses(&clauses, &exact, &[], true, false);
        assert_eq!(
            bridge.len(),
            3,
            "ordinary and unsupported/mismatched clauses remain in the HT coverage check"
        );
        assert_eq!(
            clauses.len(),
            7,
            "the exact CB fallback retains its ground ABox/singleton clauses"
        );
        let named = ["A".to_string(), "C".to_string()].into_iter().collect();
        let converted = cb_to_ht::convert(&bridge, None, &named, &[], &[], &[], false, &[], false);
        assert!(
            converted.dropped > 0,
            "the unsupported mixed-individual and uncovered proxy clauses force bridge defer"
        );

        let disabled = native_nominal_bridge_clauses(&clauses, &exact, &[], false, false);
        assert!(matches!(disabled, Cow::Borrowed(_)));
        assert_eq!(disabled.len(), clauses.len());

        let rules_present = native_nominal_bridge_clauses(&clauses, &exact, &[], true, true);
        assert!(
            matches!(rules_present, Cow::Borrowed(_)),
            "DL-safe rules disable every nominal-clause projection"
        );
        assert_eq!(rules_present.len(), clauses.len());

        let mut incomplete = exact;
        incomplete.complete = false;
        incomplete.unsupported.push("coverage gap".into());
        let fail_closed = native_nominal_bridge_clauses(&clauses, &incomplete, &[], true, false);
        assert!(matches!(fail_closed, Cow::Borrowed(_)));
        assert_eq!(fail_closed.len(), clauses.len());
    }

    #[test]
    fn production_top_assertions_require_typed_definer_provenance() {
        use crate::frontend::syntax::Concept;
        use crate::json_io::{
            DefinerKind, DefinerMeta, JAtom, JTerm, NominalAboxMeta, NominalIndividualMeta,
        };

        // ORE 10621's complete ABox has exactly 85
        // ClassAssertion(owl:Thing, individual) axioms. Normalisation reifies
        // Top once and emits 85 ground copies of this exact shape.
        let individuals: Vec<NominalIndividualMeta> = (0..85)
            .map(|index| NominalIndividualMeta {
                individual: format!("individual_{index}"),
                proxies: vec![format!("__nom__individual_{index}")],
                assertions: vec![Concept::Top],
                assertion_markers: vec!["Q_top".into()],
            })
            .collect();
        let clauses: Vec<JClause> = individuals
            .iter()
            .map(|entry| JClause {
                body: vec![],
                head: vec![JAtom::Concept {
                    concept: "Q_top".into(),
                    term: JTerm::Ind {
                        name: entry.individual.clone(),
                    },
                }],
            })
            .collect();
        let nominal_abox = NominalAboxMeta {
            complete: true,
            individuals,
            different: vec![],
            role_assertions: vec![],
            negative_role_assertions: vec![],
            unsupported: vec![],
        };
        let top_definer = DefinerMeta {
            marker: "Q_top".into(),
            kind: DefinerKind::Top,
            operands: vec![],
            role: None,
            n: None,
        };
        let definers = vec![top_definer.clone()];

        let projected =
            native_nominal_bridge_clauses(&clauses, &nominal_abox, &definers, true, false);
        assert!(projected.is_empty(), "all 85 exact Top copies are typed");
        assert_eq!(
            clauses.len(),
            85,
            "the nominal-aware CB input remains untouched"
        );
        let named = std::collections::HashSet::new();
        let converted = cb_to_ht::convert(
            &projected,
            None,
            &named,
            &[],
            &definers,
            &[],
            false,
            &[],
            false,
        );
        assert_eq!(converted.dropped, 0);

        // Marker spelling is never evidence. Without the exact Top definer,
        // the same 85 ground clauses remain and force an honest bridge defer.
        let no_provenance =
            native_nominal_bridge_clauses(&clauses, &nominal_abox, &[], true, false);
        assert_eq!(no_provenance.len(), 85);
        let unprojected = cb_to_ht::convert(
            &no_provenance,
            None,
            &named,
            &[],
            &[],
            &[],
            false,
            &[],
            false,
        );
        assert_eq!(
            unprojected.dropped, 85,
            "the regression reproduces the production gate failure exactly"
        );
        let wrong_definer = DefinerMeta {
            marker: "Q_top".into(),
            kind: DefinerKind::And,
            operands: vec!["A".into()],
            role: None,
            n: None,
        };
        let wrong =
            native_nominal_bridge_clauses(&clauses, &nominal_abox, &[wrong_definer], true, false);
        assert_eq!(wrong.len(), 85);

        // Even beside a valid Q_top definition, an arbitrary Q_* ground fact
        // is retained and counted as unsupported by cb_to_ht.
        let mut adversarial = clauses.clone();
        adversarial.push(JClause {
            body: vec![],
            head: vec![JAtom::Concept {
                concept: "Q_unproven".into(),
                term: JTerm::Ind {
                    name: "individual_0".into(),
                },
            }],
        });
        let fail_closed =
            native_nominal_bridge_clauses(&adversarial, &nominal_abox, &definers, true, false);
        assert_eq!(fail_closed.len(), 1);
        let converted = cb_to_ht::convert(
            &fail_closed,
            None,
            &named,
            &[],
            &definers,
            &[],
            false,
            &[],
            false,
        );
        assert!(
            converted.dropped > 0,
            "an unproved Q_* ground assertion must reject the bridge candidate"
        );

        // Definer provenance alone is also insufficient: the individual's
        // typed source assertion must independently say Top.
        let mut source_mismatch = nominal_abox;
        source_mismatch.individuals[0].assertions = vec![Concept::Name("A".into())];
        let mismatch =
            native_nominal_bridge_clauses(&clauses, &source_mismatch, &definers, true, false);
        assert_eq!(mismatch.len(), 1);
    }

    #[test]
    fn certified_nominal_object_one_of_and_has_value_convert_losslessly() {
        use crate::frontend::syntax::{Concept, Role};
        use crate::json_io::{
            JAtom, JTerm, NominalAboxMeta, NominalIndividualMeta, SourceAxiomKind, SourceAxiomMeta,
        };

        let var = || JTerm::Var { name: "x".into() };
        let ind = |name: &str| JTerm::Ind { name: name.into() };
        let fun = || JTerm::Fun {
            function: "f_has_value".into(),
            arg: Box::new(var()),
        };
        let clauses = vec![
            // Exact ABox and DL7/DL8 copies, all independently carried by the
            // typed nominal payload.
            JClause {
                body: vec![],
                head: vec![JAtom::Concept {
                    concept: "A".into(),
                    term: ind("b"),
                }],
            },
            JClause {
                body: vec![],
                head: vec![JAtom::Concept {
                    concept: "__nom__a".into(),
                    term: ind("a"),
                }],
            },
            JClause {
                body: vec![JAtom::Concept {
                    concept: "__nom__a".into(),
                    term: var(),
                }],
                head: vec![JAtom::Eq {
                    left: var(),
                    right: ind("a"),
                }],
            },
            JClause {
                body: vec![],
                head: vec![JAtom::Concept {
                    concept: "__nom__b".into(),
                    term: ind("b"),
                }],
            },
            JClause {
                body: vec![JAtom::Concept {
                    concept: "__nom__b".into(),
                    term: var(),
                }],
                head: vec![JAtom::Eq {
                    left: var(),
                    right: ind("b"),
                }],
            },
            JClause {
                body: vec![JAtom::Eq {
                    left: ind("a"),
                    right: ind("b"),
                }],
                head: vec![],
            },
            // Variable proxy definitions keep the ObjectOneOf proxy in the
            // converted concept vocabulary after its ground DL7/DL8 copies
            // are projected away.
            JClause {
                body: vec![JAtom::Concept {
                    concept: "OnlyA".into(),
                    term: var(),
                }],
                head: vec![JAtom::Concept {
                    concept: "__nom__a".into(),
                    term: var(),
                }],
            },
            JClause {
                body: vec![JAtom::Concept {
                    concept: "OnlyB".into(),
                    term: var(),
                }],
                head: vec![JAtom::Concept {
                    concept: "__nom__b".into(),
                    term: var(),
                }],
            },
            JClause {
                body: vec![JAtom::Concept {
                    concept: "HasA".into(),
                    term: var(),
                }],
                head: vec![
                    JAtom::Role {
                        role: "r".into(),
                        source: var(),
                        target: fun(),
                    },
                    JAtom::Concept {
                        concept: "__nom__a".into(),
                        term: fun(),
                    },
                ],
            },
        ];
        let nominal_abox = NominalAboxMeta {
            complete: true,
            individuals: vec![
                NominalIndividualMeta {
                    individual: "a".into(),
                    proxies: vec!["__nom__a".into()],
                    assertions: vec![],
                    assertion_markers: vec![],
                },
                NominalIndividualMeta {
                    individual: "b".into(),
                    proxies: vec!["__nom__b".into()],
                    assertions: vec![Concept::Name("A".into())],
                    assertion_markers: vec!["A".into()],
                },
            ],
            different: vec![("a".into(), "b".into())],
            role_assertions: vec![],
            negative_role_assertions: vec![],
            unsupported: vec![],
        };
        let source_axioms = vec![
            SourceAxiomMeta {
                kind: SourceAxiomKind::Equivalent,
                left: Concept::Name("OnlyA".into()),
                right: Concept::Nominal("a".into()),
            },
            SourceAxiomMeta {
                kind: SourceAxiomKind::SubClass,
                left: Concept::Name("HasA".into()),
                right: Concept::Exists(
                    Role::Name("r".into()),
                    Box::new(Concept::Nominal("a".into())),
                ),
            },
            SourceAxiomMeta {
                kind: SourceAxiomKind::Equivalent,
                left: Concept::Name("OnlyB".into()),
                right: Concept::Nominal("b".into()),
            },
        ];
        let bridge = native_nominal_bridge_clauses(&clauses, &nominal_abox, &[], true, false);
        let named = ["A", "OnlyA", "OnlyB", "HasA"]
            .into_iter()
            .map(str::to_string)
            .collect();
        let mut tin = cb_to_ht::convert(
            &bridge,
            None,
            &named,
            &[],
            &[],
            &source_axioms,
            false,
            &[],
            false,
        );
        tin.nominal_abox = nominal_abox;
        assert_eq!(tin.dropped, 0, "the certified bridge view is lossless");
        assert!(tin.concepts.iter().any(|name| name == "__nom__a"));
        assert!(tin.concepts.iter().any(|name| name == "__nom__b"));
        assert!(
            bridge_candidate_from(&tin, true, true),
            "the exact ObjectOneOf/ObjectHasValue input reaches the native bridge"
        );
    }

    #[test]
    fn konclude_bridge_accepts_only_legacy_fast_tableau_fences() {
        let mut tin = cb_to_ht::TInput::default();
        assert!(bridge_fences_supported(&tin, false));
        tin.fenced.push(cb_to_ht::Fenced {
            reason: "inverse+number(SHIQ)".into(),
            detail: "legacy fast-tableau fence".into(),
        });
        assert!(bridge_fences_supported(&tin, false));
        tin.fenced.push(cb_to_ht::Fenced {
            reason: "inverse-functional".into(),
            detail: "r".into(),
        });
        assert!(bridge_fences_supported(&tin, false));
        tin.fenced.push(cb_to_ht::Fenced {
            reason: "complex-domain".into(),
            detail: "R -> (A or B)".into(),
        });
        assert!(!bridge_fences_supported(&tin, false));
        assert!(bridge_fences_supported(&tin, true));
        tin.fenced.push(cb_to_ht::Fenced {
            reason: "complex-range".into(),
            detail: "R -> (C or D)".into(),
        });
        assert!(bridge_fences_supported(&tin, true));
        tin.fenced.push(cb_to_ht::Fenced {
            reason: "nominal+inverse(SHOI/SHOIQ)".into(),
            detail: "typed nominal source".into(),
        });
        assert!(
            !bridge_fences_supported(&tin, true),
            "legacy nominal+inverse fence stays closed without exact ABox coverage"
        );
        tin.nominal_abox.complete = true;
        assert!(bridge_fences_supported(&tin, true));
        tin.fenced.push(cb_to_ht::Fenced {
            reason: "irreflexivity".into(),
            detail: "r".into(),
        });
        assert!(!bridge_fences_supported(&tin, true));
    }

    #[test]
    fn number_feature_does_not_bypass_bridge_lossless_input_gate() {
        let mut tin = cb_to_ht::TInput {
            number: true,
            dropped: 1,
            ..Default::default()
        };
        assert!(
            !bridge_candidate_from(&tin, true, true),
            "a dropped number construct must remain outside the bridge"
        );

        tin.dropped = 0;
        tin.fenced.push(cb_to_ht::Fenced {
            reason: "unsupported-number-shape".into(),
            detail: "synthetic regression".into(),
        });
        assert!(
            !bridge_candidate_from(&tin, true, true),
            "an unsupported number fence must remain outside the bridge"
        );
    }

    #[test]
    fn named_ht_specialists_never_fall_through_to_general_ht() {
        assert!(specialist_route_allows(None, false, false, false, false));
        assert!(specialist_route_allows(
            Some("general"),
            false,
            false,
            false,
            false
        ));
        assert!(!specialist_route_allows(
            Some("certified"),
            false,
            false,
            false,
            false
        ));
        // certified admits the bridge and the CB-guarded additive card arm, but
        // NOT a lone SHOQ or QO candidate (those stay bridge-only under the
        // production portfolio; their incomplete onts could otherwise emit a
        // wrong taxonomy on a CB timeout).
        assert!(!specialist_route_allows(
            Some("certified"),
            false,
            true,
            false,
            false
        ));
        assert!(!specialist_route_allows(
            Some("certified"),
            true,
            false,
            false,
            false
        ));
        // A card candidate is enough under certified even with no bridge.
        assert!(specialist_route_allows(
            Some("certified"),
            false,
            false,
            true,
            false
        ));
        assert!(specialist_route_allows(
            Some("certified"),
            true,
            true,
            true,
            false
        ));
        assert!(specialist_route_allows(
            Some("certified"),
            true,
            true,
            true,
            true
        ));
        assert!(specialist_route_allows(
            Some("qo"),
            true,
            false,
            false,
            false
        ));
        assert!(!specialist_route_allows(
            Some("qo"),
            false,
            true,
            true,
            true
        ));
        assert!(specialist_route_allows(
            Some("shoq"),
            false,
            true,
            false,
            false
        ));
        assert!(specialist_route_allows(
            Some("card"),
            false,
            false,
            true,
            false
        ));
        assert!(specialist_route_allows(
            Some("bridge"),
            false,
            false,
            false,
            true
        ));
        assert!(specialist_route_allows(
            Some("features"),
            false,
            false,
            false,
            false
        ));
        assert!(specialist_route_allows(
            Some("full"),
            true,
            true,
            true,
            true
        ));
        assert!(!specialist_route_allows(
            Some("unknown"),
            true,
            true,
            true,
            true
        ));
    }

    /// Build the smallest TInput that carries a first-class `≥n` restriction.
    fn card_def_tin() -> cb_to_ht::TInput {
        let mut tin = cb_to_ht::TInput::default();
        tin.card_defs.push(cb_to_ht::CardDefJson {
            marker: 0,
            min: true,
            n: 2,
            role: 0,
            filler: 1,
        });
        tin
    }

    #[test]
    fn card_arm_is_a_candidate_and_certified_admits_it() {
        // A reduced cardinality probe: a datatype/inverse-free TInput with a
        // single `≥2 R.C` restriction is a card candidate, and the production
        // portfolio's `certified` mode admits it as the CB-guarded fallback arm
        // that recovers ore_ont_7499 / 9540.
        let tin = card_def_tin();
        let card = card_candidate_from(&tin, true, true, false);
        assert!(card, "≥n restriction must be a card candidate");
        assert!(specialist_route_allows(
            Some("certified"),
            false,
            false,
            card,
            false
        ));
    }

    #[test]
    fn card_arm_respects_its_fences() {
        let tin = card_def_tin();
        // KM_NO_HT_CARD (ht_card=false) disables the arm entirely.
        assert!(!card_candidate_from(&tin, false, true, false));
        // A datatype ontology is always excluded (no concrete-domain oracle).
        assert!(!card_candidate_from(&tin, true, true, true));
        // A dropped/fenced TInput is not faithful and is excluded.
        let mut dropped = card_def_tin();
        dropped.dropped = 1;
        assert!(!card_candidate_from(&dropped, true, true, false));
        let mut fenced = card_def_tin();
        fenced.fenced.push(cb_to_ht::Fenced {
            reason: "inverse+number(SHIQ)".into(),
            detail: "x".into(),
        });
        assert!(!card_candidate_from(&fenced, true, true, false));
        // Inverse requires BOTH recognition and the normalized role-separation
        // certificate. Recognition alone must never globally weaken the fence.
        let mut inverse = card_def_tin();
        inverse.inverse = true;
        assert!(!card_candidate_from(&inverse, true, false, false));
        assert!(!card_candidate_from(&inverse, true, true, false));
        inverse.inverse_cardinality_role_separable = true;
        assert!(card_candidate_from(&inverse, true, true, false));
        // No card_defs (e.g. the inverse+nominal ore_ont_10702, whose convert
        // refuses the card transform) is never a card candidate.
        let empty = cb_to_ht::TInput::default();
        assert!(!card_candidate_from(&empty, true, true, false));

        // A nominal-bearing card input is admitted only after the typed ABox
        // installer has produced its complete numeric certificate.
        let mut nominal = card_def_tin();
        nominal.nominals.push(7);
        assert!(!card_candidate_from(&nominal, true, true, false));
        nominal.native_abox.complete = true;
        assert!(card_candidate_from(&nominal, true, true, false));
    }

    #[test]
    fn negative_native_roles_must_be_separate_from_chain_and_transitive_components() {
        let mut chained = card_def_tin();
        chained.roles = vec!["left".into(), "right".into(), "target".into()];
        chained.native_abox.complete = true;
        chained.native_abox.negative_role_assertions.push((2, 0, 1));
        chained.chains.push((0, 1, 2));
        assert!(!native_abox_role_automata_separable(&chained));
        assert!(!card_candidate_from(&chained, true, true, false));

        let mut transitive_super = card_def_tin();
        transitive_super.roles = vec!["negative-sub".into(), "transitive-super".into()];
        transitive_super.native_abox.complete = true;
        transitive_super
            .native_abox
            .negative_role_assertions
            .push((0, 0, 1));
        transitive_super.transitive.push(1);
        transitive_super.clauses.push(cb_to_ht::HtClause {
            body: vec![cb_to_ht::HAtom::Role { r: 0, s: 0, t: 1 }],
            head: vec![cb_to_ht::HAtom::Role { r: 1, s: 0, t: 1 }],
        });
        assert!(!native_abox_role_automata_separable(&transitive_super));

        let mut positive_chain = card_def_tin();
        positive_chain.roles = vec!["left".into(), "right".into(), "target".into()];
        positive_chain.native_abox.complete = true;
        positive_chain.native_abox.role_assertions = vec![(0, 0, 1), (1, 1, 2)];
        positive_chain.chains.push((0, 1, 2));
        assert!(!native_abox_role_automata_separable(&positive_chain));
        assert!(!card_candidate_from(&positive_chain, true, true, false));

        // 9540's relevant shape: has_point carries cardinalities/negative facts;
        // is_front and is_back are an inverse pair; unrelated spatial roles are
        // transitive. None of the three negative-role components is non-simple.
        let mut separated = card_def_tin();
        separated.roles = vec![
            "has_point".into(),
            "is_front".into(),
            "is_back".into(),
            "is_completely_inside".into(),
        ];
        separated.native_abox.complete = true;
        separated.native_abox.negative_role_assertions = vec![(0, 0, 1), (1, 0, 1), (2, 1, 0)];
        separated.transitive.push(3);
        separated.clauses.extend([
            cb_to_ht::HtClause {
                body: vec![cb_to_ht::HAtom::Role { r: 1, s: 0, t: 1 }],
                head: vec![cb_to_ht::HAtom::Role { r: 2, s: 1, t: 0 }],
            },
            cb_to_ht::HtClause {
                body: vec![cb_to_ht::HAtom::Role { r: 2, s: 0, t: 1 }],
                head: vec![cb_to_ht::HAtom::Role { r: 1, s: 1, t: 0 }],
            },
        ]);
        assert!(native_abox_role_automata_separable(&separated));
        assert!(card_candidate_from(&separated, true, true, false));
    }

    #[test]
    fn convert_emits_card_defs_for_a_faithful_ge_n_restriction() {
        // End-to-end reduced cardinality probe through cb_to_ht::convert: a
        // single `≥2 R.C` CardMeta on a datatype-free, inverse-free clause set
        // produces exactly one first-class card_def, which is what makes the
        // ontology a production card candidate.
        use crate::json_io::CardMeta;
        let named = std::collections::HashSet::new();
        let cards = vec![CardMeta {
            marker: "M".into(),
            min: true,
            n: 2,
            role: "R".into(),
            filler: "C".into(),
        }];
        let tin = cb_to_ht::convert(&[], None, &named, &cards, &[], &[], true, &[], false);
        assert_eq!(tin.card_defs.len(), 1);
        assert!(tin.card_defs[0].min && tin.card_defs[0].n == 2);
        assert!(card_candidate_from(&tin, true, true, false));

        // card_enabled=false (KM_NO_HT_CARD) suppresses the transform entirely.
        let off = cb_to_ht::convert(&[], None, &named, &cards, &[], &[], false, &[], false);
        assert!(off.card_defs.is_empty());
        assert!(!card_candidate_from(&off, true, true, false));
    }

    #[test]
    fn bridge_only_worker_keeps_card_fallback_under_certified() {
        // Isolated bridge route: always bridge-only.
        assert!(bridge_only_worker(
            Some("bridge"),
            true,
            false,
            false,
            false,
            false
        ));
        // certified + bridge alone: bridge-only (no card to hand off to).
        assert!(bridge_only_worker(
            Some("certified"),
            true,
            true,
            false,
            false,
            false
        ));
        // certified + bridge AND card: NOT bridge-only, so a bridge defer hands
        // the worker off to the card fallback arm instead of exiting empty.
        assert!(!bridge_only_worker(
            Some("certified"),
            true,
            true,
            false,
            false,
            true
        ));
        // No bridge candidate: never bridge-only.
        assert!(!bridge_only_worker(
            Some("certified"),
            false,
            true,
            false,
            false,
            false
        ));
    }

    #[test]
    fn bridge_answers_are_harvested_immediately_under_trigger_absorption() {
        // The proven 3215 closure depends on taking the bridge's finished
        // exact answer without waiting out CB's 225 s fallback budget — but
        // ONLY when the worker is bridge-exclusive (KM_HT_BRIDGE_ONLY), i.e.
        // its answer necessarily carries the bridge's complete-answer-or-defer
        // guarantee.
        assert_eq!(ht_acceptance_budget(true, true, false, 20.0, 225.0), 0.0);
        assert_eq!(ht_acceptance_budget(true, true, true, 20.0, 225.0), 0.0);
        // Fast certify-or-defer arms keep the short SHOQ budget; the plain HT
        // racer keeps the full fallback budget.
        assert_eq!(ht_acceptance_budget(false, false, true, 20.0, 225.0), 20.0);
        assert_eq!(
            ht_acceptance_budget(false, false, true, 300.0, 225.0),
            225.0
        );
        assert_eq!(
            ht_acceptance_budget(false, false, false, 20.0, 225.0),
            225.0
        );
    }

    /// Regression: under trigger absorption a NON-bridge-exclusive worker (the
    /// certified production portfolio may carry a card arm as the bridge-defer
    /// fallback, and manual trigger-absorb env combinations can carry legacy or
    /// specialist arms) must NOT get the instant harvest: its answer can come
    /// from an arm without the bridge's complete-answer-or-defer guarantee,
    /// and accepting it at 0 s would let it preempt a healthy CB run instead
    /// of only ever replacing a CB timeout.
    #[test]
    fn non_bridge_exclusive_workers_keep_their_budgets_under_trigger_absorption() {
        // bridge+card certified worker: fast-certify short budget, not 0.
        assert_eq!(ht_acceptance_budget(true, false, true, 20.0, 225.0), 20.0);
        // manual trigger-absorb worker with a legacy arm: full fallback budget.
        assert_eq!(ht_acceptance_budget(true, false, false, 20.0, 225.0), 225.0);
    }

    #[test]
    fn large_synchronous_bridge_limits_speculative_cb_to_one_thread() {
        assert_eq!(
            limit_synchronous_bridge_competitor(Some(15), Some(54_974), false),
            Some(1)
        );
        assert_eq!(
            limit_synchronous_bridge_competitor(Some(15), Some(49_999), false),
            Some(15)
        );
        assert_eq!(
            limit_synchronous_bridge_competitor(Some(15), None, false),
            Some(15)
        );
    }

    #[test]
    fn typed_nominal_bridge_limits_speculative_cb_below_large_threshold() {
        // ORE 10621 has 41,647 active classes, below the legacy 50k cutoff,
        // but its typed nominal bridge is serial and exact. One speculative CB
        // thread preserves the honest fallback while avoiding the measured
        // 15-thread 16.8-GiB contention that makes both arms time out.
        assert_eq!(
            limit_synchronous_bridge_competitor(Some(15), Some(41_647), true),
            Some(1)
        );
        // Neither class count nor a generic bridge is enough below 50k. This
        // keeps ordinary production portfolios and manual HT combinations on
        // their existing reservation policy.
        assert_eq!(
            limit_synchronous_bridge_competitor(Some(15), Some(41_647), false),
            Some(15)
        );
    }

    #[test]
    fn typed_nominal_competitor_gate_requires_complete_exclusive_payload() {
        use crate::json_io::NominalIndividualMeta;

        let mut tin = cb_to_ht::TInput::default();
        assert!(!typed_nominal_bridge_exclusive(&tin, true));
        tin.nominal_abox.complete = true;
        tin.nominal_abox.individuals.push(NominalIndividualMeta {
            individual: "a".into(),
            proxies: vec!["__nom__a".into()],
            assertions: vec![],
            assertion_markers: vec![],
        });
        assert!(typed_nominal_bridge_exclusive(&tin, true));
        assert!(
            !typed_nominal_bridge_exclusive(&tin, false),
            "a worker with any other answer arm keeps the ordinary reservation"
        );
        tin.nominal_abox.unsupported.push("coverage gap".into());
        assert!(
            !typed_nominal_bridge_exclusive(&tin, true),
            "incomplete typed coverage must never alter scheduling"
        );
    }
}
