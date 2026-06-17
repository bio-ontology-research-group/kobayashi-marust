//! Worker (engine / elc) invocation with the RSS + wall-clock watchdog and the
//! adaptive single-threaded retry. Port of `owl_classify._run_engine` and
//! `_run_engine_adaptive`.
//!
//! Process isolation is the whole point: a parallel attempt that blows past the
//! RSS cap is `SIGKILL`ed (`Child::kill`) and reaped (`Child::wait`), and the
//! orchestrator retries single-threaded — impossible to do safely in-process.
//! Child stdout goes to a temp file (parsed with `from_reader`, so the giants'
//! hundreds-of-MB output never lands in a `String` nor deadlocks an undrained
//! pipe); stderr (small) is captured to a temp file too.

use std::fs::File;
use std::path::Path;
use std::process::Command;
use std::time::{Duration, Instant};

use super::tmpfile::TempPath;
use super::{Config, OrchestrateError};

pub struct EngineResult {
    pub code: i32,
    /// temp file holding the worker's stdout; parse with `serde_json::from_reader`
    pub stdout: TempPath,
    pub stderr: String,
    pub oom: bool,
    pub timed_out: bool,
}

/// Resident set size of `pid` in bytes, from `/proc/<pid>/statm` field 2 (pages)
/// × 4096. The page size is hardcoded to 4096 to match `owl_classify` exactly
/// (the kill decision must be bit-for-bit reproducible).
fn read_rss(pid: u32) -> Option<u64> {
    let s = std::fs::read_to_string(format!("/proc/{}/statm", pid)).ok()?;
    let resident: u64 = s.split_whitespace().nth(1)?.parse().ok()?;
    Some(resident * 4096)
}

#[allow(clippy::too_many_arguments)]
pub fn run_engine(
    binary: &Path,
    clauses_path: &Path,
    threads: Option<&str>,
    rss_cap_gb: Option<f64>,
    time_cap_s: Option<f64>,
    extra_env: &[(&str, &str)],
    nice: bool,
) -> Result<EngineResult, OrchestrateError> {
    let bin_name = binary
        .file_name()
        .map(|s| s.to_string_lossy().into_owned())
        .unwrap_or_else(|| "worker".into());

    let stdout_tmp = TempPath::new(".out.json");
    let stderr_tmp = TempPath::new(".err");

    let mut cmd = if nice {
        // the niced racer only consumes cores the primary leaves idle.
        let mut c = Command::new("nice");
        c.arg("-n").arg("19").arg(binary);
        c
    } else {
        Command::new(binary)
    };
    cmd.stdin(File::open(clauses_path)?)
        .stdout(File::create(stdout_tmp.path())?)
        .stderr(File::create(stderr_tmp.path())?);
    if let Some(t) = threads {
        cmd.env("KM_THREADS", t);
    }
    for (k, v) in extra_env {
        cmd.env(k, v);
    }

    let mut child = cmd
        .spawn()
        .map_err(|e| OrchestrateError::Spawn { bin: bin_name.clone(), source: e })?;
    let pid = child.id();

    let cap_bytes = rss_cap_gb.map(|g| (g * (1u64 << 30) as f64) as u64);
    let deadline = time_cap_s.map(|s| Instant::now() + Duration::from_secs_f64(s));
    let mut oom = false;
    let mut timed_out = false;

    let status = if cap_bytes.is_none() && deadline.is_none() {
        child.wait()?
    } else {
        // poll the resident set and wall clock every 100 ms; SIGKILL on breach.
        loop {
            if let Some(st) = child.try_wait()? {
                break st;
            }
            if let Some(cap) = cap_bytes {
                if let Some(rss) = read_rss(pid) {
                    if rss > cap {
                        oom = true;
                        let _ = child.kill();
                        break child.wait()?;
                    }
                }
            }
            if let Some(d) = deadline {
                if Instant::now() > d {
                    timed_out = true;
                    let _ = child.kill();
                    break child.wait()?;
                }
            }
            std::thread::sleep(Duration::from_millis(100));
        }
    };

    let code = status.code().unwrap_or(-1); // signal-killed -> negative-ish; we branch on oom/timed/rc anyway
    let stderr = std::fs::read_to_string(stderr_tmp.path()).unwrap_or_default();
    Ok(EngineResult { code, stdout: stdout_tmp, stderr, oom, timed_out })
}

/// Parallel attempt under the RSS+time watchdog; on overflow/timeout/failure,
/// fall back to a single-threaded legacy (per-`f`) run. Port of
/// `_run_engine_adaptive`. `queries`, when set, is passed as `KM_QUERIES`
/// (residue resolution) — never by mutating the global environment.
pub fn run_engine_adaptive(
    cfg: &Config,
    clauses_path: &Path,
    queries: Option<&str>,
) -> Result<EngineResult, OrchestrateError> {
    let engine = cfg.engine_bin();
    let central_on = !cfg.no_central;

    let mut env1: Vec<(&str, &str)> = Vec::new();
    if let Some(q) = queries {
        env1.push(("KM_QUERIES", q));
    }
    // First attempt: inherit the ambient KM_THREADS (so threads=None), RSS cap,
    // and a wall cap only when the central strategy is active.
    let mut proc = run_engine(
        &engine,
        clauses_path,
        None,
        Some(cfg.par_mem_gb),
        if central_on { Some(cfg.central_time_cap) } else { None },
        &env1,
        false,
    )?;

    let failed = proc.oom || proc.timed_out || proc.code != 0;
    if failed && !cfg.no_retry {
        if central_on {
            // central blew up: legacy per-`f` strategy is the complete fallback;
            // single-threaded, uncapped (the harness budget + external memcap bound it).
            let mut env2: Vec<(&str, &str)> = vec![("KM_NO_CENTRAL", "1")];
            if let Some(q) = queries {
                env2.push(("KM_QUERIES", q));
            }
            proc = run_engine(&engine, clauses_path, Some("1"), None, None, &env2, false)?;
        } else if cfg.threads != Some(1) {
            // explicit legacy run: single-threaded retry
            proc = run_engine(&engine, clauses_path, Some("1"), None, None, &env1, false)?;
        }
    }
    Ok(proc)
}
