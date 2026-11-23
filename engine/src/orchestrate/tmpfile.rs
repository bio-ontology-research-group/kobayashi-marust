//! Temporary files of one km run.
//!
//! Every temporary file or directory km creates lives in one per-run
//! directory, `$TMPDIR/km-run-<pid>-<nonce>/` (`std::env::temp_dir`, so
//! `TMPDIR` is honoured). The supervisor (`km classify`, `km explain`) creates
//! it before it spawns any worker and exports it as [`RUN_DIR_ENV`]; workers
//! put their files there. A standalone worker without a supervisor creates its
//! own run directory on first use.
//!
//! The process that created the directory removes it with everything in it
//! on every exit path it can observe:
//!
//! * normal return from `main` and every `std::process::exit` (an `atexit`
//!   hook);
//! * `SIGTERM`, `SIGINT` and `SIGHUP` (a handler that removes the directory
//!   with raw system calls only, then re-raises the signal with its default
//!   action, so the exit status still reports the signal). Workers exit
//!   within 100 ms of their supervisor (`cli::die_with_supervisor`), and a
//!   worker cannot recreate the removed directory: files are created with
//!   `File::create`, which needs the parent to exist.
//!
//! `SIGKILL` and an aborting panic (`panic = "abort"`) cannot be observed. A
//! supervisor therefore removes, at start, every run directory in the temp
//! directory whose owning process no longer exists, together with legacy
//! `km-<pid>-...` files of dead processes.
//!
//! [`TempPath`] remains the RAII handle for one file: it is unlinked on drop
//! as before, so long runs do not accumulate files.

use std::ffi::CString;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicPtr, AtomicU64, Ordering};
use std::sync::OnceLock;

/// The run directory a supervisor exports to its workers.
pub const RUN_DIR_ENV: &str = "KM_RUN_TMPDIR";

static CTR: AtomicU64 = AtomicU64::new(0);
static RUN_DIR: OnceLock<PathBuf> = OnceLock::new();
/// NUL-terminated path of the directory this process owns (null: none). Read
/// by the exit hook and the signal handler.
static OWNED: AtomicPtr<libc::c_char> = AtomicPtr::new(std::ptr::null_mut());

fn nonce() -> u128 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|duration| duration.as_nanos())
        .unwrap_or(0)
}

/// Create and own a fresh run directory under the system temp directory.
fn create_owned_run_dir() -> PathBuf {
    let base = std::env::temp_dir();
    for attempt in 0..16u32 {
        let dir = base.join(format!("km-run-{}-{}-{attempt}", std::process::id(), nonce()));
        match std::fs::create_dir(&dir) {
            Ok(()) => {
                own(&dir);
                return dir;
            }
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(_) => break,
        }
    }
    // The temp directory is unusable; callers report their own write errors.
    base
}

/// Record `dir` as owned by this process and arm the exit and signal hooks.
fn own(dir: &Path) {
    let Ok(c_path) = CString::new(dir.as_os_str().as_encoded_bytes()) else {
        return;
    };
    let previous = OWNED.swap(c_path.into_raw(), Ordering::SeqCst);
    if !previous.is_null() {
        return; // hooks are already armed
    }
    unsafe {
        libc::atexit(remove_owned_at_exit);
    }
    #[cfg(unix)]
    for signal in [libc::SIGTERM, libc::SIGINT, libc::SIGHUP] {
        unsafe {
            let mut action: libc::sigaction = std::mem::zeroed();
            // Keep a disposition the caller chose to ignore (`nohup`, `trap ''`).
            if libc::sigaction(signal, std::ptr::null(), &mut action) == 0
                && action.sa_sigaction == libc::SIG_IGN
            {
                continue;
            }
            let mut handler: libc::sigaction = std::mem::zeroed();
            handler.sa_sigaction = remove_owned_on_signal as usize;
            libc::sigemptyset(&mut handler.sa_mask);
            handler.sa_flags = libc::SA_RESETHAND;
            libc::sigaction(signal, &handler, std::ptr::null_mut());
        }
    }
}

extern "C" fn remove_owned_at_exit() {
    let path = OWNED.load(Ordering::SeqCst);
    if !path.is_null() {
        unsafe { remove_tree_raw(path, 0) };
    }
}

#[cfg(unix)]
extern "C" fn remove_owned_on_signal(signal: libc::c_int) {
    let path = OWNED.load(Ordering::SeqCst);
    if !path.is_null() {
        unsafe { remove_tree_raw(path, 0) };
    }
    // SA_RESETHAND restored the default action: re-raise to terminate with it.
    unsafe {
        libc::raise(signal);
    }
}

/// Remove `path` and everything below it using async-signal-safe system calls
/// only (`open`, `getdents64`, `unlinkat`, `rmdir`, `close`) and stack buffers.
/// Workers may still be creating files while it runs, so a non-empty
/// directory is retried a few times.
#[cfg(target_os = "linux")]
unsafe fn remove_tree_raw(path: *const libc::c_char, depth: u32) {
    if depth > 4 {
        return;
    }
    for _ in 0..4 {
        let fd = libc::open(path, libc::O_RDONLY | libc::O_DIRECTORY | libc::O_CLOEXEC | libc::O_NOFOLLOW);
        if fd < 0 {
            libc::unlink(path);
            return;
        }
        let mut buffer = [0u8; 4096];
        loop {
            let read = libc::syscall(
                libc::SYS_getdents64,
                fd,
                buffer.as_mut_ptr(),
                buffer.len(),
            );
            if read <= 0 {
                break;
            }
            let mut offset = 0usize;
            while offset < read as usize {
                // struct linux_dirent64 { u64 ino; i64 off; u16 reclen; u8 type; char name[]; }
                let record = buffer.as_ptr().add(offset);
                let reclen = u16::from_ne_bytes([*record.add(16), *record.add(17)]) as usize;
                let kind = *record.add(18);
                let name = record.add(19) as *const libc::c_char;
                offset += reclen.max(1);
                let first = *name as u8;
                let second = *name.add(1) as u8;
                let third = *name.add(2) as u8;
                if first == b'.' && (second == 0 || (second == b'.' && third == 0)) {
                    continue;
                }
                if kind == libc::DT_DIR {
                    // Build "<path>/<name>" in a stack buffer.
                    let mut child = [0 as libc::c_char; 4096];
                    let mut length = 0usize;
                    let mut cursor = path;
                    while *cursor != 0 && length + 1 < child.len() {
                        child[length] = *cursor;
                        length += 1;
                        cursor = cursor.add(1);
                    }
                    if length + 1 < child.len() {
                        child[length] = b'/' as libc::c_char;
                        length += 1;
                    }
                    let mut cursor = name;
                    while *cursor != 0 && length + 1 < child.len() {
                        child[length] = *cursor;
                        length += 1;
                        cursor = cursor.add(1);
                    }
                    child[length] = 0;
                    remove_tree_raw(child.as_ptr(), depth + 1);
                } else {
                    libc::unlinkat(fd, name, 0);
                }
            }
        }
        libc::close(fd);
        if libc::rmdir(path) == 0 {
            return;
        }
        let error = *libc::__errno_location();
        if error != libc::ENOTEMPTY && error != libc::EEXIST {
            return;
        }
    }
}

#[cfg(not(target_os = "linux"))]
unsafe fn remove_tree_raw(path: *const libc::c_char, _depth: u32) {
    let path = std::ffi::CStr::from_ptr(path);
    let _ = std::fs::remove_dir_all(std::path::Path::new(
        &*String::from_utf8_lossy(path.to_bytes()),
    ));
}

#[cfg(unix)]
fn process_alive(pid: libc::pid_t) -> bool {
    if pid <= 0 {
        return false;
    }
    // `kill(pid, 0)` probes for existence. Read errno through std so the
    // code builds on every Unix (glibc, musl and macOS name it differently).
    unsafe { libc::kill(pid, 0) == 0 }
        || std::io::Error::last_os_error().raw_os_error() != Some(libc::ESRCH)
}

/// Remove run directories and legacy `km-<pid>-...` files of processes that
/// no longer exist. Only entries owned by this user are considered.
/// Unix only: other platforms keep stale entries (no portable liveness and
/// ownership test), which costs disk space and nothing else.
#[cfg(not(unix))]
fn sweep_stale(_base: &Path) {}

/// See the non-Unix variant above for the contract.
#[cfg(unix)]
fn sweep_stale(base: &Path) {
    let Ok(entries) = std::fs::read_dir(base) else { return };
    let uid = unsafe { libc::getuid() };
    for entry in entries.flatten() {
        let name = entry.file_name();
        let Some(name) = name.to_str() else { continue };
        let pid_text = if let Some(rest) = name.strip_prefix("km-run-") {
            rest
        } else if let Some(rest) = name.strip_prefix("km-") {
            rest
        } else {
            continue;
        };
        let Some(pid) = pid_text.split('-').next().and_then(|p| p.parse::<libc::pid_t>().ok()) else {
            continue;
        };
        if process_alive(pid) {
            continue;
        }
        let Ok(metadata) = entry.metadata() else { continue };
        if std::os::unix::fs::MetadataExt::uid(&metadata) != uid {
            continue;
        }
        let path = entry.path();
        if metadata.is_dir() {
            let _ = std::fs::remove_dir_all(&path);
        } else {
            let _ = std::fs::remove_file(&path);
        }
    }
}

/// Create this supervisor's run directory, export it to the workers, and
/// remove stale run directories of dead processes. Call once at the start of
/// a supervisor command, before any worker or thread starts.
pub fn install_supervisor_run_dir() {
    sweep_stale(&std::env::temp_dir());
    let dir = create_owned_run_dir();
    std::env::set_var(RUN_DIR_ENV, &dir);
    let _ = RUN_DIR.set(dir);
}

/// The directory for this process's temporary files: the supervisor's run
/// directory when one was exported and exists, else a run directory this
/// process creates and owns.
pub fn run_dir() -> &'static Path {
    RUN_DIR.get_or_init(|| {
        if let Some(dir) = std::env::var_os(RUN_DIR_ENV).map(PathBuf::from) {
            if dir.is_dir() {
                return dir;
            }
        }
        create_owned_run_dir()
    })
}

/// A unique path in the run directory. The file is NOT created here (the
/// caller does, e.g. by redirecting a child's stdout into it); `Drop` removes
/// it if present.
pub struct TempPath(PathBuf);

impl TempPath {
    pub fn new(suffix: &str) -> TempPath {
        let n = CTR.fetch_add(1, Ordering::Relaxed);
        let name = format!("km-{}-{}{}", std::process::id(), n, suffix);
        TempPath(run_dir().join(name))
    }

    pub fn path(&self) -> &Path {
        &self.0
    }
}

impl Drop for TempPath {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

#[cfg(test)]
mod tests {
    use super::TempPath;

    #[cfg(unix)]
    #[test]
    fn stale_entries_of_dead_processes_are_swept() {
        let _test_env = crate::test_env::read();
        let base = super::run_dir().join("sweep-probe");
        std::fs::create_dir_all(base.join("km-run-4000000-1-0")).unwrap();
        std::fs::write(base.join("km-run-4000000-1-0").join("x"), b"x").unwrap();
        std::fs::write(base.join("km-4000000-7-0.clauses.json"), b"x").unwrap();
        let live = format!("km-run-{}-1-0", std::process::id());
        std::fs::create_dir_all(base.join(&live)).unwrap();
        std::fs::write(base.join("unrelated"), b"x").unwrap();
        super::sweep_stale(&base);
        let mut left: Vec<String> = std::fs::read_dir(&base)
            .unwrap()
            .map(|e| e.unwrap().file_name().into_string().unwrap())
            .collect();
        left.sort();
        assert_eq!(left, vec![live, "unrelated".to_string()]);
        std::fs::remove_dir_all(&base).unwrap();
    }

    #[test]
    fn paths_are_unique_and_reuse_the_process_directory() {
        let _test_env = crate::test_env::read();
        let first = TempPath::new(".json");
        let second = TempPath::new(".json");
        assert_ne!(first.path(), second.path());
        assert_eq!(first.path().parent(), second.path().parent());
    }
}
