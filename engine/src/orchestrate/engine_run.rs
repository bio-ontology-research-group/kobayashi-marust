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
#[cfg(target_os = "linux")]
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd};
use std::path::Path;
use std::process::Command;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Condvar, Mutex};
use std::time::{Duration, Instant};

use super::tmpfile::TempPath;
use super::{Config, OrchestrateError};

// Engine children currently alive + a race-won flag — the analogue of
// owl_classify's `_LIVE_ENGINES` / `_RACE_WON`. A race winner (tableau/HT/elc)
// calls `cancel_and_kill_engines`, which SIGKILLs every live engine child and
// stops any subsequent spawn (e.g. the adaptive single-threaded retry) from
// starting. Process-global is correct: `km classify` handles one ontology per
// process, so there is no cross-ontology leakage to reset.
static LIVE: Mutex<Vec<u32>> = Mutex::new(Vec::new());
static CANCEL: AtomicBool = AtomicBool::new(false);

#[cfg(target_os = "linux")]
pub(crate) fn open_pidfd(pid: u32) -> Option<OwnedFd> {
    let fd = unsafe { libc::syscall(libc::SYS_pidfd_open, pid, 0) as libc::c_int };
    if fd < 0 {
        None
    } else {
        Some(unsafe { OwnedFd::from_raw_fd(fd) })
    }
}

#[cfg(not(target_os = "linux"))]
pub(crate) fn open_pidfd(_pid: u32) -> Option<()> {
    None
}

#[cfg(target_os = "linux")]
pub(crate) fn wait_for_exit_or_interval(pidfd: Option<&OwnedFd>, interval: Duration) {
    let Some(pidfd) = pidfd else {
        std::thread::sleep(interval);
        return;
    };
    let mut pollfd = libc::pollfd {
        fd: pidfd.as_raw_fd(),
        events: libc::POLLIN,
        revents: 0,
    };
    let timeout_ms = interval.as_millis().min(libc::c_int::MAX as u128) as libc::c_int;
    if unsafe { libc::poll(&mut pollfd, 1, timeout_ms) } < 0 {
        std::thread::sleep(interval);
    }
}

#[cfg(not(target_os = "linux"))]
pub(crate) fn wait_for_exit_or_interval(_pidfd: Option<&()>, interval: Duration) {
    std::thread::sleep(interval);
}

/// Wake-up channel between a race scheduler and its arms.
///
/// The race loops in `race.rs` inspect every arm, then sleep for an
/// exponentially growing interval (1 ms doubling to 50-100 ms). That interval
/// is the only thing bounding how late a finished arm is noticed: a CB worker
/// that exits 16 ms into the race is harvested at the 31 ms wake-up, and the
/// enclosing HT race notices that harvest at ITS next wake-up (63 ms). On the
/// small-ontology band the whole classification is shorter than one such
/// quantum, so the sleep ladder, not reasoning, set the wall clock. Arms now
/// bump this event when they finish and waiters block on the condition
/// variable instead of an unconditional sleep. Waiters read the epoch BEFORE
/// inspecting the arms and wait only while it is unchanged, so a completion
/// that lands between the inspection and the wait is never slept through.
///
/// The decision logic of every race is untouched: the same checks run in the
/// same order on every wake-up, and the interval ladder still bounds the RSS
/// watchdog and budget cadence exactly as before.
pub(crate) struct ArmEvent {
    epoch: Mutex<u64>,
    changed: Condvar,
}

impl ArmEvent {
    pub(crate) fn new() -> Arc<ArmEvent> {
        Arc::new(ArmEvent {
            epoch: Mutex::new(0),
            changed: Condvar::new(),
        })
    }

    /// Current completion epoch; pass it to `wait_past` after inspecting arms.
    pub(crate) fn epoch(&self) -> u64 {
        *self
            .epoch
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
    }

    /// An arm finished (or changed state): wake every waiter.
    pub(crate) fn notify(&self) {
        let mut epoch = self
            .epoch
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        *epoch = epoch.wrapping_add(1);
        self.changed.notify_all();
    }

    /// Block until the epoch moves past `seen` or `timeout` elapses, whichever
    /// comes first. Returns immediately when a notification already happened
    /// after `seen` was read.
    pub(crate) fn wait_past(&self, seen: u64, timeout: Duration) {
        let deadline = Instant::now() + timeout;
        let mut epoch = self
            .epoch
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        while *epoch == seen {
            let now = Instant::now();
            if now >= deadline {
                return;
            }
            epoch = self
                .changed
                .wait_timeout(epoch, deadline - now)
                .unwrap_or_else(|poisoned| poisoned.into_inner())
                .0;
        }
    }
}

/// Notify `event` as soon as the child process `pid` exits.
///
/// Linux: a detached thread blocks on the child's pidfd, which becomes
/// readable on exit (also after the child has been reaped by the owner of the
/// `Child`), so the thread always terminates. The watcher only wakes the race
/// loop; the loop still reaps and inspects the child itself through
/// `try_wait`, exactly as before. Other platforms keep the interval poll.
#[cfg(target_os = "linux")]
pub(crate) fn notify_on_exit(pid: u32, event: Arc<ArmEvent>) {
    let Some(pidfd) = open_pidfd(pid) else {
        // Already gone (or pidfd unsupported): the loop's own poll proceeds.
        event.notify();
        return;
    };
    let watcher_event = event.clone();
    let spawned = std::thread::Builder::new()
        .name("arm-exit".into())
        .spawn(move || {
            let mut pollfd = libc::pollfd {
                fd: pidfd.as_raw_fd(),
                events: libc::POLLIN,
                revents: 0,
            };
            loop {
                let rc = unsafe { libc::poll(&mut pollfd, 1, -1) };
                if rc >= 0 {
                    break;
                }
                if std::io::Error::last_os_error().kind() != std::io::ErrorKind::Interrupted {
                    break;
                }
            }
            watcher_event.notify();
        });
    if spawned.is_err() {
        // No watcher thread: the caller's interval poll remains the wake source.
        event.notify();
    }
}

#[cfg(not(target_os = "linux"))]
pub(crate) fn notify_on_exit(_pid: u32, _event: Arc<ArmEvent>) {}

/// A race was won elsewhere: SIGKILL every live engine child and block new spawns.
pub fn cancel_and_kill_engines() {
    CANCEL.store(true, Ordering::SeqCst);
    let pids = LIVE.lock().unwrap().clone();
    for pid in pids {
        unsafe {
            libc::kill(pid as i32, libc::SIGKILL);
        }
    }
}
/// Clear the race-won flag (mirrors `_RACE_WON.clear()` before residue resolution).
pub fn reset_cancel() {
    CANCEL.store(false, Ordering::SeqCst);
}
fn register(pid: u32) {
    LIVE.lock().unwrap().push(pid);
}
fn deregister(pid: u32) {
    let mut g = LIVE.lock().unwrap();
    if let Some(i) = g.iter().position(|&p| p == pid) {
        g.remove(i);
    }
}

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
pub(crate) fn read_rss(pid: u32) -> Option<u64> {
    let s = std::fs::read_to_string(format!("/proc/{}/statm", pid)).ok()?;
    let resident: u64 = s.split_whitespace().nth(1)?.parse().ok()?;
    Some(resident * 4096)
}

#[allow(clippy::too_many_arguments)]
pub fn run_engine(
    program: &Path,
    prefix: &[String],
    clauses_path: &Path,
    threads: Option<&str>,
    rss_cap_gb: Option<f64>,
    time_cap_s: Option<f64>,
    extra_env: &[(&str, &str)],
    nice: bool,
) -> Result<EngineResult, OrchestrateError> {
    let bin_name = program
        .file_name()
        .map(|s| s.to_string_lossy().into_owned())
        .unwrap_or_else(|| "worker".into());

    // a race already answered: do not spawn (the racing thread may still be
    // unwinding its adaptive retry). Mirrors `_RACE_WON.is_set()` -> -9.
    if CANCEL.load(Ordering::SeqCst) {
        return Ok(EngineResult {
            code: -9,
            stdout: TempPath::new(".cancelled"),
            stderr: "race won: skip spawn".into(),
            oom: false,
            timed_out: false,
        });
    }

    let stdout_tmp = TempPath::new(".out.json");
    let stderr_tmp = TempPath::new(".err");

    let mut cmd = if nice {
        // the niced racer only consumes cores the primary leaves idle.
        let mut c = Command::new("nice");
        c.arg("-n").arg("19").arg(program).args(prefix);
        c
    } else {
        let mut c = Command::new(program);
        c.args(prefix);
        c
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

    let mut child = cmd.spawn().map_err(|e| OrchestrateError::Spawn {
        bin: bin_name.clone(),
        source: e,
    })?;
    let pid = child.id();
    register(pid);
    let pidfd = open_pidfd(pid);
    // This process now idles until the worker exits, and the harness sums
    // resident pages over the whole process tree. Freed frontend and
    // conversion garbage left here would otherwise stay resident beside the
    // worker's own peak for its entire lifetime (see `crate::mem`).
    crate::mem::release_transient_heap();

    let cap_bytes = rss_cap_gb.map(|g| (g * (1u64 << 30) as f64) as u64);
    let deadline = time_cap_s.map(|s| Instant::now() + Duration::from_secs_f64(s));
    let mut oom = false;
    let mut timed_out = false;

    let status = if cap_bytes.is_none() && deadline.is_none() {
        child.wait()?
    } else {
        // Poll the resident set and wall clock; SIGKILL on breach. The poll
        // interval starts at 1 ms and doubles up to 100 ms: a worker that
        // exits in ~10 ms is noticed in ~10 ms (the old fixed 100 ms sleep
        // put a ~0.1 s latency floor under EVERY subprocess stage, which
        // dominated km classify wall on small ontologies), while long runs
        // converge to the same 100 ms watchdog cadence as before.
        let mut interval = Duration::from_millis(1);
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
            // Linux pidfds become readable when the child exits, avoiding up
            // to one full watchdog interval of latency. RSS and deadline
            // checks retain the same cadence; unsupported kernels use sleep.
            wait_for_exit_or_interval(pidfd.as_ref(), interval);
            interval = (interval * 2).min(Duration::from_millis(100));
        }
    };

    deregister(pid);
    let code = status.code().unwrap_or(-1); // signal-killed -> negative-ish; we branch on oom/timed/rc anyway
    let stderr = std::fs::read_to_string(stderr_tmp.path()).unwrap_or_default();
    Ok(EngineResult {
        code,
        stdout: stdout_tmp,
        stderr,
        oom,
        timed_out,
    })
}

/// Parallel attempt under the RSS+time watchdog; on overflow/timeout/failure,
/// fall back to a single-threaded legacy (per-`f`) run. Port of
/// `_run_engine_adaptive`. `queries`, when set, is passed as `KM_QUERIES`
/// (residue resolution) — never by mutating the global environment. `threads`
/// overrides the first-attempt thread count (the racers' core reservation);
/// `None` inherits the ambient `KM_THREADS` (`cfg.threads`), exactly like
/// Python's `first = str(threads) if threads is not None else env[KM_THREADS]`.
pub fn run_engine_adaptive(
    cfg: &Config,
    clauses_path: &Path,
    queries: Option<&str>,
    threads: Option<usize>,
) -> Result<EngineResult, OrchestrateError> {
    let (engine, engine_pre) = cfg.engine_cmd();
    let central_on = !cfg.no_central;

    // first-attempt thread count: explicit override, else the ambient KM_THREADS.
    let first: Option<String> = match threads {
        Some(t) => Some(t.to_string()),
        None => cfg.threads.map(|t| t.to_string()),
    };

    let mut env1: Vec<(&str, &str)> = Vec::new();
    if let Some(q) = queries {
        env1.push(("KM_QUERIES", q));
    }
    // First attempt: the resolved thread count, RSS cap, and a wall cap only
    // when the central strategy is active.
    let mut proc = run_engine(
        &engine,
        &engine_pre,
        clauses_path,
        first.as_deref(),
        Some(cfg.par_mem_gb),
        if central_on {
            Some(cfg.central_time_cap)
        } else {
            None
        },
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
            proc = run_engine(
                &engine,
                &engine_pre,
                clauses_path,
                Some("1"),
                None,
                None,
                &env2,
                false,
            )?;
        } else if first.as_deref() != Some("1") {
            // explicit legacy run: single-threaded retry
            proc = run_engine(
                &engine,
                &engine_pre,
                clauses_path,
                Some("1"),
                None,
                None,
                &env1,
                false,
            )?;
        }
    }
    Ok(proc)
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;

    fn empty_input() -> TempPath {
        let path = TempPath::new(".watchdog-input");
        File::create(path.path()).unwrap();
        path
    }

    #[test]
    fn exit_notification_preserves_normal_completion() {
        let input = empty_input();
        let result = run_engine(
            Path::new("/bin/sh"),
            &["-c".into(), "exit 0".into()],
            input.path(),
            None,
            Some(1.0),
            Some(1.0),
            &[],
            false,
        )
        .unwrap();
        assert_eq!(result.code, 0);
        assert!(!result.oom);
        assert!(!result.timed_out);
    }

    #[test]
    fn exit_notification_preserves_timeout_kill() {
        let input = empty_input();
        let result = run_engine(
            Path::new("/bin/sh"),
            &["-c".into(), "sleep 1".into()],
            input.path(),
            None,
            None,
            Some(0.02),
            &[],
            false,
        )
        .unwrap();
        assert!(result.timed_out);
        assert!(!result.oom);
    }

    #[test]
    fn arm_event_wakes_waiter_before_its_timeout() {
        let event = ArmEvent::new();
        let seen = event.epoch();
        let notifier = event.clone();
        let handle = std::thread::spawn(move || {
            std::thread::sleep(Duration::from_millis(20));
            notifier.notify();
        });
        let started = Instant::now();
        event.wait_past(seen, Duration::from_secs(5));
        assert!(started.elapsed() < Duration::from_secs(2));
        assert_ne!(event.epoch(), seen);
        handle.join().unwrap();
    }

    #[test]
    fn arm_event_does_not_sleep_through_an_earlier_notification() {
        let event = ArmEvent::new();
        let seen = event.epoch();
        event.notify();
        let started = Instant::now();
        event.wait_past(seen, Duration::from_secs(5));
        assert!(started.elapsed() < Duration::from_secs(1));
    }

    #[test]
    fn arm_event_times_out_without_a_notification() {
        let event = ArmEvent::new();
        let seen = event.epoch();
        let started = Instant::now();
        event.wait_past(seen, Duration::from_millis(30));
        assert!(started.elapsed() >= Duration::from_millis(30));
        assert_eq!(event.epoch(), seen);
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn exit_notifier_wakes_on_child_exit() {
        let mut child = std::process::Command::new("/bin/sh")
            .arg("-c")
            .arg("sleep 0.05")
            .stdout(std::process::Stdio::null())
            .spawn()
            .unwrap();
        let event = ArmEvent::new();
        let seen = event.epoch();
        notify_on_exit(child.id(), event.clone());
        let started = Instant::now();
        event.wait_past(seen, Duration::from_secs(10));
        assert!(started.elapsed() < Duration::from_secs(5));
        assert!(child.wait().unwrap().success());
    }

    #[test]
    fn exit_notification_preserves_rss_kill() {
        let input = empty_input();
        let result = run_engine(
            Path::new("/bin/sh"),
            &["-c".into(), "while :; do :; done".into()],
            input.path(),
            None,
            Some(1.0 / (1u64 << 30) as f64),
            Some(1.0),
            &[],
            false,
        )
        .unwrap();
        assert!(result.oom);
        assert!(!result.timed_out);
    }
}
