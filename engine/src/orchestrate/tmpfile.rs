//! RAII temp-file path: created lazily by the caller (via `File::create`),
//! unlinked on `Drop` — including on panic (the release profile keeps
//! `panic = "unwind"`). Replaces every Python `tempfile.mkstemp(...)` +
//! `finally: os.unlink(...)` pair in `owl_classify.py`.

use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::OnceLock;

static CTR: AtomicU64 = AtomicU64::new(0);
static PROCESS_TEMP: OnceLock<(PathBuf, u128)> = OnceLock::new();

fn process_temp() -> &'static (PathBuf, u128) {
    PROCESS_TEMP.get_or_init(|| {
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|duration| duration.as_nanos())
            .unwrap_or(0);
        (std::env::temp_dir(), nonce)
    })
}

/// A unique path under `$TMPDIR`. The file is NOT created here (the caller does,
/// e.g. by redirecting a child's stdout into it); `Drop` removes it if present.
pub struct TempPath(PathBuf);

impl TempPath {
    pub fn new(suffix: &str) -> TempPath {
        let n = CTR.fetch_add(1, Ordering::Relaxed);
        // One process nonce prevents collision with stale files after PID reuse.
        // The counter is sufficient within this process, so querying the clock
        // and TMPDIR for every worker handoff is unnecessary orchestration work.
        let (directory, nonce) = process_temp();
        let name = format!("km-{}-{}-{}{}", std::process::id(), nonce, n, suffix);
        TempPath(directory.join(name))
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

    #[test]
    fn paths_are_unique_and_reuse_the_process_directory() {
        let first = TempPath::new(".json");
        let second = TempPath::new(".json");
        assert_ne!(first.path(), second.path());
        assert_eq!(first.path().parent(), second.path().parent());
    }
}
