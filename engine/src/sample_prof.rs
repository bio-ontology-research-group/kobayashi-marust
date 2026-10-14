//! Diagnostic CPU sampling profiler, compiled only with the `sample-profiler`
//! feature. `KM_SAMPLE_PROFILE=<dir>` arms an `ITIMER_PROF` signal that walks
//! frame pointers (build with `-C force-frame-pointers=yes`) and, at process
//! exit, writes `<dir>/prof.<pid>` (one sample per line: hex return
//! addresses, innermost first) and `<dir>/maps.<pid>` for symbolization.
//! Worker subprocesses inherit the variable and profile themselves.
#![allow(static_mut_refs)]

use std::sync::atomic::{AtomicUsize, Ordering};

const CAP: usize = 1 << 25;
const DEPTH: usize = 96;
static mut BUF: *mut u64 = std::ptr::null_mut();
static POS: AtomicUsize = AtomicUsize::new(0);
static mut STACK_LO: u64 = 0;
static mut STACK_HI: u64 = 0;
static mut DIR: Option<String> = None;

extern "C" fn on_prof(_sig: libc::c_int, _info: *mut libc::siginfo_t, ctx: *mut libc::c_void) {
    unsafe {
        let uc = ctx as *mut libc::ucontext_t;
        let rip = (*uc).uc_mcontext.gregs[libc::REG_RIP as usize] as u64;
        let mut rbp = (*uc).uc_mcontext.gregs[libc::REG_RBP as usize] as u64;
        let mut frame = [0u64; DEPTH];
        frame[0] = rip;
        let mut n = 1;
        while n < DEPTH && rbp >= STACK_LO && rbp + 16 <= STACK_HI && rbp % 8 == 0 {
            let ret = *((rbp + 8) as *const u64);
            let next = *(rbp as *const u64);
            if ret == 0 {
                break;
            }
            frame[n] = ret;
            n += 1;
            if next <= rbp {
                break;
            }
            rbp = next;
        }
        let start = POS.fetch_add(n + 1, Ordering::Relaxed);
        if start + n + 1 >= CAP {
            return;
        }
        *BUF.add(start) = n as u64;
        for (i, value) in frame[..n].iter().enumerate() {
            *BUF.add(start + 1 + i) = *value;
        }
    }
}

extern "C" fn dump() {
    unsafe {
        let Some(dir) = DIR.as_ref() else { return };
        let off = libc::itimerval {
            it_interval: libc::timeval { tv_sec: 0, tv_usec: 0 },
            it_value: libc::timeval { tv_sec: 0, tv_usec: 0 },
        };
        libc::setitimer(libc::ITIMER_PROF, &off, std::ptr::null_mut());
        let pid = std::process::id();
        let end = POS.load(Ordering::Relaxed).min(CAP);
        let mut out = String::new();
        let mut i = 0;
        while i < end {
            let n = *BUF.add(i) as usize;
            if n == 0 || i + 1 + n > end {
                break;
            }
            for k in 0..n {
                if k > 0 {
                    out.push(' ');
                }
                out.push_str(&format!("{:x}", *BUF.add(i + 1 + k)));
            }
            out.push('\n');
            i += n + 1;
        }
        let args: Vec<String> = std::env::args().collect();
        let _ = std::fs::write(format!("{dir}/prof.{pid}"), out);
        let _ = std::fs::write(format!("{dir}/cmd.{pid}"), args.join(" "));
        if let Ok(maps) = std::fs::read_to_string("/proc/self/maps") {
            let _ = std::fs::write(format!("{dir}/maps.{pid}"), maps);
        }
    }
}

/// Arm the profiler when `KM_SAMPLE_PROFILE` names an output directory.
pub fn install() {
    let Some(dir) = std::env::var_os("KM_SAMPLE_PROFILE") else { return };
    unsafe {
        let mut attr: libc::pthread_attr_t = std::mem::zeroed();
        let mut addr: *mut libc::c_void = std::ptr::null_mut();
        let mut size: libc::size_t = 0;
        if libc::pthread_getattr_np(libc::pthread_self(), &mut attr) == 0 {
            libc::pthread_attr_getstack(&attr, &mut addr, &mut size);
            libc::pthread_attr_destroy(&mut attr);
        }
        STACK_LO = addr as u64;
        STACK_HI = addr as u64 + size as u64;
        let layout = std::alloc::Layout::array::<u64>(CAP).unwrap();
        BUF = std::alloc::alloc_zeroed(layout) as *mut u64;
        DIR = Some(dir.to_string_lossy().into_owned());
        let mut action: libc::sigaction = std::mem::zeroed();
        action.sa_sigaction = on_prof as usize;
        action.sa_flags = libc::SA_SIGINFO | libc::SA_RESTART;
        libc::sigaction(libc::SIGPROF, &action, std::ptr::null_mut());
        libc::atexit(dump);
        let period = std::env::var("KM_SAMPLE_PROFILE_US")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(500);
        let timer = libc::itimerval {
            it_interval: libc::timeval { tv_sec: 0, tv_usec: period },
            it_value: libc::timeval { tv_sec: 0, tv_usec: period },
        };
        libc::setitimer(libc::ITIMER_PROF, &timer, std::ptr::null_mut());
    }
}
