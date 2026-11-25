//! A wall-clock budget for one nested classification attempt.
//!
//! [`run`] calls the attempt on the current thread. A watchdog thread waits
//! for the budget; once it expires, the watchdog sends SIGKILL to every
//! descendant process of this process (the attempt's workers and their
//! checkers) and keeps doing so every 20 ms until the attempt returns, so a
//! worker the attempt starts after the expiry dies at once too. A killed
//! worker ends with a signal status, which every caller reads as a failed
//! worker, never as an answer. Work the attempt does in this process is not
//! interrupted; the budget bounds the subprocess part only.
//!
//! The caller must run nothing else that spawns processes while the attempt
//! runs. Only Linux enumerates descendants (`/proc`); elsewhere the attempt
//! runs unbounded.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Condvar, Mutex};
use std::time::{Duration, Instant};

/// Run `attempt` under `budget`. Returns its result and whether the budget
/// expired before it returned.
pub(crate) fn run<R>(budget: Duration, attempt: impl FnOnce() -> R) -> (R, bool) {
    let expired = Arc::new(AtomicBool::new(false));
    let done = Arc::new((Mutex::new(false), Condvar::new()));
    let watchdog = {
        let expired = expired.clone();
        let done = done.clone();
        std::thread::Builder::new().name("attempt-budget".into()).spawn(move || {
            let deadline = Instant::now() + budget;
            let (lock, wake) = &*done;
            let mut finished = lock.lock().unwrap();
            loop {
                if *finished {
                    return;
                }
                let now = Instant::now();
                if now < deadline {
                    finished = wake.wait_timeout(finished, deadline - now).unwrap().0;
                    continue;
                }
                expired.store(true, Ordering::SeqCst);
                kill_descendants();
                finished = wake.wait_timeout(finished, Duration::from_millis(20)).unwrap().0;
            }
        })
    };
    let result = attempt();
    {
        let (lock, wake) = &*done;
        *lock.lock().unwrap() = true;
        wake.notify_all();
    }
    if let Ok(handle) = watchdog {
        let _ = handle.join();
    }
    (result, expired.load(Ordering::SeqCst))
}

#[cfg(target_os = "linux")]
fn kill_descendants() {
    use std::collections::{HashMap, HashSet};
    let me = std::process::id();
    let mut children: HashMap<u32, Vec<u32>> = HashMap::new();
    let Ok(entries) = std::fs::read_dir("/proc") else { return };
    for entry in entries.flatten() {
        let Some(pid) = entry.file_name().to_str().and_then(|n| n.parse::<u32>().ok()) else {
            continue;
        };
        let Ok(stat) = std::fs::read_to_string(format!("/proc/{pid}/stat")) else { continue };
        // `pid (comm) state ppid ...`; comm may hold spaces and parentheses.
        let Some(rest) = stat.rfind(')').map(|at| &stat[at + 1..]) else { continue };
        let Some(ppid) = rest.split_whitespace().nth(1).and_then(|p| p.parse::<u32>().ok()) else {
            continue;
        };
        children.entry(ppid).or_default().push(pid);
    }
    let mut seen = HashSet::new();
    let mut stack = children.get(&me).cloned().unwrap_or_default();
    while let Some(pid) = stack.pop() {
        if !seen.insert(pid) {
            continue;
        }
        if let Some(grand) = children.get(&pid) {
            stack.extend(grand.iter().copied());
        }
        unsafe {
            libc::kill(pid as i32, libc::SIGKILL);
        }
    }
}

#[cfg(not(target_os = "linux"))]
fn kill_descendants() {}

// The expiry path is tested end to end in tests/finite_rule_taxonomy.rs: it
// kills every descendant of the process, which in a multi-threaded test
// binary would include the processes of other tests.
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn attempt_within_its_budget_is_untouched() {
        let (value, expired) = run(Duration::from_secs(30), || 7);
        assert!(!expired);
        assert_eq!(value, 7);
    }
}
