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
use std::sync::Arc;
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
        subs.entry(u.clone()).or_default().push("owl:Nothing".to_string());
    }
    EngineOut { subsumptions: subs, inconsistent: !t.consistent, dropped: 0, unresolved: Vec::new() }
}

// ---------------------------------------------------------------------------
// lazily-spawned label-caching tableau racer
// ---------------------------------------------------------------------------
fn spawn_tableau(cfg: &Config, clauses_path: &Path) -> Option<(Child, super::tmpfile::TempPath)> {
    if !cfg.tab_race {
        return None;
    }
    let tab_bin = cfg.tab_bin()?;
    let cl: Vec<JClause> = {
        let f = File::open(clauses_path).ok()?;
        let v: JInput = serde_json::from_reader(BufReader::new(f)).ok()?;
        v.clauses
    };
    // giants: the engine path owns them
    if cl.len() > cfg.tab_max_clauses {
        return None;
    }
    // no disjunctive head => deterministic => the engine handles it
    if !cl.iter().any(|c| c.head.len() >= 2) {
        return None;
    }
    let named = std::collections::HashSet::new();
    let tin = cb_to_ht::convert(&cl, None, &named);
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
        c.arg("-n").arg("19").arg(&tab_bin);
        c
    } else {
        Command::new(&tab_bin)
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
pub fn race_cb_vs_tableau<F>(cfg: &Config, clauses_path: &Path, engine_run: F) -> Result<EngineOut, OrchestrateError>
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
        let t0 = Instant::now();
        while t0.elapsed().as_secs_f64() < cfg.tab_race_delay {
            if eng_done.load(Ordering::SeqCst) {
                break;
            }
            thread::sleep(Duration::from_millis(200));
        }
        let mut tab = if eng_done.load(Ordering::SeqCst) {
            None
        } else {
            spawn_tableau(cfg, clauses_path)
        };

        let mut winner: Option<EngineOut> = None;
        loop {
            let mut tab_failed = false;
            if let Some((child, outp)) = tab.as_mut() {
                if let Ok(Some(st)) = child.try_wait() {
                    let mut won = None;
                    if st.success() {
                        if let Ok(f) = File::open(outp.path()) {
                            if let Ok(t) = serde_json::from_reader::<_, TOutput>(BufReader::new(f)) {
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
            thread::sleep(Duration::from_millis(50));
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
pub fn race_absorbed_plain(cfg: &Config, ont: &Path, absorbed_path: &Path) -> Result<EngineOut, OrchestrateError> {
    if let Some(plain) = frontend_run::run_ofn_plain(cfg, ont, false) {
        let threads = cfg.threads.map(|t| t.to_string());
        let res = engine_run::run_engine(
            &cfg.engine_bin(),
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
    let res = engine_run::run_engine_adaptive(cfg, absorbed_path, None)?;
    if res.code != 0 {
        return Err(OrchestrateError::Worker { bin: "engine".into(), code: res.code, stderr: res.stderr });
    }
    parse_out(&res)
}
