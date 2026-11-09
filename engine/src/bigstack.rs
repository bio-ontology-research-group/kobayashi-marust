//! Deep-recursion stacks that do not reserve memory the input never uses.
//!
//! The tableau and bridge searches recurse once per branching level and ran
//! on dedicated threads with multi-GiB stacks (`stack_size(4 << 30)`), on the
//! assumption that an untouched stack costs nothing. That holds only under
//! heuristic overcommit. On a host with strict accounting
//! (`vm.overcommit_memory = 2`, the workstation `ws`) a thread stack is a
//! private writable mapping and is charged in full against the commit limit
//! when the thread starts. When other processes hold most of the limit the
//! spawn fails with `EAGAIN` before the worker reads its first clause, and a
//! KM run failed for a reason unrelated to its input (review 2026-10-30:
//! 15 of 1,757 on/off pairs at 12 parallel jobs, `worker tableau exited 1`).
//!
//! The main thread's stack is the one mapping Linux grows on demand: the
//! kernel charges each page when the stack grows into it, and reserves only
//! address space (the gap below the stack, sized from `RLIMIT_STACK` at
//! `execve`). [`ensure_main_stack`] gives a worker process such a stack: if
//! the soft limit is too small it raises it and re-executes the process once,
//! so the kernel lays out the address space with the larger gap. [`run`] then
//! executes deep work inline whenever the current thread already has the
//! stack it asks for, and spawns a thread (retrying a failed spawn) only when
//! it does not. Neither path changes what the closure computes; they change
//! only which stack it runs on and when memory is charged.

use std::cell::Cell;

/// The stack the deep tableau and bridge searches have always requested.
pub const DEEP_STACK: usize = 4 << 30;

/// Extra stack above a request: covers the frames between the point that
/// checks the budget and the work itself, so nested requests of the same
/// size run inline instead of spawning a second deep thread.
const HEADROOM: usize = 64 << 20;

/// Bytes kept free above the kernel's guard gap when computing the main
/// thread's budget.
const GUARD_MARGIN: usize = 4 << 20;

/// Set while a worker re-executes itself with a larger `RLIMIT_STACK`; makes
/// the re-exec happen at most once.
const REEXEC_ENV: &str = "KM_MAIN_STACK_REEXEC";

/// Failed spawns are retried with these pauses (milliseconds) before the
/// error is reported. About 5 s in total.
const RETRY_PAUSES_MS: [u64; 9] = [10, 20, 40, 80, 160, 320, 640, 1280, 2560];

thread_local! {
    /// Lowest address this thread may use for stack, or 0 when unknown (a
    /// thread whose stack size this module did not establish).
    static STACK_FLOOR: Cell<usize> = const { Cell::new(0) };
}

#[inline(never)]
fn stack_pointer() -> usize {
    let marker = 0u8;
    std::hint::black_box(&marker) as *const u8 as usize
}

/// Stack bytes known to be available below the caller's frame on this
/// thread (0 when this module did not establish the thread's stack).
pub fn remaining() -> usize {
    let floor = STACK_FLOOR.with(Cell::get);
    if floor == 0 {
        return 0;
    }
    stack_pointer().saturating_sub(floor)
}

fn is_resource_error(error: &std::io::Error) -> bool {
    matches!(error.raw_os_error(), Some(libc::EAGAIN) | Some(libc::ENOMEM))
}

/// Run `f` with at least `bytes` of stack and return its value.
///
/// Inline when the current thread already has `bytes` available (a worker
/// main thread prepared by [`ensure_main_stack`], or a thread started by this
/// function); otherwise on a new thread with `bytes + HEADROOM` of stack. A
/// spawn that fails for lack of memory or threads is retried for about six
/// seconds; a spawn that still fails returns an error naming the thread, the
/// stack size and the operating system's reason.
pub fn run<T: Send>(what: &str, bytes: usize, f: impl FnOnce() -> T + Send) -> Result<T, String> {
    if remaining() >= bytes {
        return Ok(f());
    }
    let size = bytes.saturating_add(HEADROOM);
    // `spawn_scoped` consumes its closure even when the spawn fails; keep the
    // work in a slot the closure only borrows, so a retry can still take it.
    let slot = std::sync::Mutex::new(Some(f));
    std::thread::scope(|scope| {
        let mut attempts = 0usize;
        loop {
            attempts += 1;
            let slot = &slot;
            let spawned = std::thread::Builder::new()
                .name(what.to_string())
                .stack_size(size)
                .spawn_scoped(scope, move || {
                    STACK_FLOOR.with(|floor| floor.set(stack_pointer().saturating_sub(bytes)));
                    let f = slot.lock().unwrap_or_else(|e| e.into_inner()).take()
                        .expect("deep-stack work taken twice");
                    f()
                });
            match spawned {
                Ok(handle) => {
                    return handle.join().map_err(|_| format!("{what} thread panicked"));
                }
                Err(error) if is_resource_error(&error) && attempts <= RETRY_PAUSES_MS.len() => {
                    std::thread::sleep(std::time::Duration::from_millis(RETRY_PAUSES_MS[attempts - 1]));
                }
                Err(error) => {
                    return Err(format!(
                        "could not start the {what} thread with a {} MiB stack after {attempts} attempt(s): {error}",
                        size >> 20,
                    ));
                }
            }
        }
    })
}

/// `std::thread::Builder::new().stack_size(size).spawn_scoped(scope, f)`
/// for a worker pool, retrying a spawn that fails for lack of memory or
/// threads on the same schedule as [`run`]. Pool workers run in parallel, so
/// they cannot share the caller's stack; this only removes the transient
/// failure. The error after the last attempt names the stack size and the
/// operating system's reason.
pub fn spawn_scoped_retrying<'scope, 'env, T, F>(
    size: usize,
    scope: &'scope std::thread::Scope<'scope, 'env>,
    f: F,
) -> std::io::Result<std::thread::ScopedJoinHandle<'scope, T>>
where
    F: FnOnce() -> T + Send + 'scope,
    T: Send + 'scope,
{
    // As in `run`: a failed spawn drops its closure, so the work stays in a
    // shared slot that each attempt's closure only references.
    let slot = std::sync::Arc::new(std::sync::Mutex::new(Some(f)));
    let mut attempts = 0usize;
    loop {
        attempts += 1;
        let work = slot.clone();
        let spawned = std::thread::Builder::new().stack_size(size).spawn_scoped(scope, move || {
            let f = work.lock().unwrap_or_else(|e| e.into_inner()).take()
                .expect("pool work taken twice");
            f()
        });
        match spawned {
            Ok(handle) => return Ok(handle),
            Err(error) if is_resource_error(&error) && attempts <= RETRY_PAUSES_MS.len() => {
                std::thread::sleep(std::time::Duration::from_millis(RETRY_PAUSES_MS[attempts - 1]));
            }
            Err(error) => {
                return Err(std::io::Error::new(error.kind(), format!(
                    "could not start a worker thread with a {} MiB stack after {attempts} attempt(s): {error}",
                    size >> 20,
                )));
            }
        }
    }
}

/// The main thread's usable stack: the smaller of the soft `RLIMIT_STACK`
/// and the unmapped gap between the `[stack]` mapping's top and the next
/// mapping below it, minus the kernel guard gap and a margin. Reads
/// `/proc/self/maps`, so it reflects the layout the kernel actually chose.
#[cfg(target_os = "linux")]
fn main_stack_extent(soft_limit: usize) -> Option<(usize, usize)> {
    let maps = std::fs::read_to_string("/proc/self/maps").ok()?;
    let mut ranges = Vec::new();
    let mut stack = None;
    for line in maps.lines() {
        let range = line.split_whitespace().next()?;
        let (start, end) = range.split_once('-')?;
        let start = usize::from_str_radix(start, 16).ok()?;
        let end = usize::from_str_radix(end, 16).ok()?;
        if line.ends_with("[stack]") {
            stack = Some((start, end));
        } else {
            ranges.push((start, end));
        }
    }
    let (start, top) = stack?;
    let below = ranges.iter().filter(|&&(_, end)| end <= start).map(|&(_, end)| end).max().unwrap_or(0);
    // The kernel keeps `stack_guard_gap` (256 pages by default) between a
    // growing stack and the mapping below it.
    let guard = std::fs::read_to_string("/proc/sys/vm/stack_guard_gap").ok()
        .and_then(|text| text.trim().parse::<usize>().ok())
        .map(|pages| pages.saturating_mul(4096))
        .unwrap_or(1 << 20);
    let usable = (top - below).saturating_sub(guard).min(soft_limit).saturating_sub(GUARD_MARGIN);
    Some((top, usable))
}

/// Give this process's main thread at least `bytes` (+ headroom) of stack
/// that the kernel commits page by page as it grows, and record it so that
/// [`run`] executes deep work inline on the main thread.
///
/// Call it first thing in a worker process's `main`, before any other thread
/// exists and before stdin is read: when the soft `RLIMIT_STACK` is too small
/// and the hard limit allows more, the process raises the soft limit and
/// re-executes itself once (same executable, arguments, environment and file
/// descriptors). When that is impossible, nothing is recorded and [`run`]
/// spawns threads as before.
pub fn ensure_main_stack(bytes: usize) {
    #[cfg(target_os = "linux")]
    {
        let want = bytes.saturating_add(2 * HEADROOM);
        let mut limit = libc::rlimit { rlim_cur: 0, rlim_max: 0 };
        if unsafe { libc::getrlimit(libc::RLIMIT_STACK, &mut limit) } != 0 {
            return;
        }
        let soft = if limit.rlim_cur == libc::RLIM_INFINITY { usize::MAX } else { limit.rlim_cur as usize };
        if let Some((top, usable)) = main_stack_extent(soft) {
            if usable >= bytes.saturating_add(HEADROOM) {
                STACK_FLOOR.with(|floor| floor.set(top - usable));
                std::env::remove_var(REEXEC_ENV);
                return;
            }
        }
        if std::env::var_os(REEXEC_ENV).is_some() {
            // Already re-executed and the layout still lacks the gap: keep
            // the thread fallback rather than loop.
            std::env::remove_var(REEXEC_ENV);
            return;
        }
        let hard_allows = limit.rlim_max == libc::RLIM_INFINITY || limit.rlim_max as usize >= want;
        if !hard_allows || soft >= want {
            return;
        }
        let raised = libc::rlimit { rlim_cur: want as libc::rlim_t, rlim_max: limit.rlim_max };
        if unsafe { libc::setrlimit(libc::RLIMIT_STACK, &raised) } != 0 {
            return;
        }
        use std::os::unix::process::CommandExt as _;
        let mut args = std::env::args_os();
        let arg0 = args.next().unwrap_or_default();
        let error = std::process::Command::new("/proc/self/exe")
            .arg0(arg0)
            .args(args)
            .env(REEXEC_ENV, "1")
            .exec();
        // `exec` returned, so it failed: restore the limit and fall back.
        let _ = error;
        unsafe { libc::setrlimit(libc::RLIMIT_STACK, &limit) };
    }
    #[cfg(not(target_os = "linux"))]
    let _ = bytes;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn spawned_thread_records_its_budget_and_nested_requests_run_inline() {
        let outer = std::thread::current().id();
        let (inner_thread, nested_thread, budget) = run("bigstack-test", 64 << 20, || {
            let here = std::thread::current().id();
            let budget = remaining();
            let nested = run("bigstack-nested", 32 << 20, || std::thread::current().id()).unwrap();
            (here, nested, budget)
        })
        .unwrap();
        assert_ne!(inner_thread, outer, "an unprepared thread must spawn");
        assert_eq!(nested_thread, inner_thread, "a nested smaller request must run inline");
        assert!(budget >= 63 << 20, "budget {budget} below the request");
        assert_eq!(remaining(), 0, "the caller's thread must stay unprepared");
    }

    #[test]
    fn deep_recursion_uses_the_requested_stack() {
        fn depth(n: usize) -> usize {
            let pad = std::hint::black_box([0u8; 1024]);
            if n == 0 { pad[0] as usize } else { 1 + depth(n - 1) + pad[0] as usize }
        }
        // About 20 MiB of frames: overflows the default 2 MiB thread stack.
        assert_eq!(run("bigstack-depth", 64 << 20, || depth(20_000)).unwrap(), 20_000);
    }

    #[test]
    fn pool_spawn_runs_the_work_and_reports_a_failure() {
        let results: Vec<usize> = std::thread::scope(|scope| {
            let handles: Vec<_> = (0..4)
                .map(|i| spawn_scoped_retrying(8 << 20, scope, move || i * 2).unwrap())
                .collect();
            handles.into_iter().map(|h| h.join().unwrap()).collect()
        });
        assert_eq!(results, vec![0, 2, 4, 6]);
        let error = std::thread::scope(|scope| spawn_scoped_retrying(usize::MAX >> 2, scope, || ()).map(|_| ()))
            .unwrap_err();
        assert!(error.to_string().contains("MiB stack"), "{error}");
    }

    #[test]
    fn spawn_failure_reports_the_reason() {
        // An absurd request fails on every host; the error must name it.
        let error = run("bigstack-absurd", usize::MAX >> 2, || ()).unwrap_err();
        assert!(error.contains("bigstack-absurd") && error.contains("MiB stack"), "{error}");
    }
}
