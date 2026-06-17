//! RAII temp-file path: created lazily by the caller (via `File::create`),
//! unlinked on `Drop` — including on panic (the release profile keeps
//! `panic = "unwind"`). Replaces every Python `tempfile.mkstemp(...)` +
//! `finally: os.unlink(...)` pair in `owl_classify.py`.

use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

static CTR: AtomicU64 = AtomicU64::new(0);

/// A unique path under `$TMPDIR`. The file is NOT created here (the caller does,
/// e.g. by redirecting a child's stdout into it); `Drop` removes it if present.
pub struct TempPath(PathBuf);

impl TempPath {
    pub fn new(suffix: &str) -> TempPath {
        let n = CTR.fetch_add(1, Ordering::Relaxed);
        // SystemTime is fine in the compiled binary (the Date/random ban applies
        // only to workflow scripts, not to runtime Rust).
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0);
        let name = format!("km-{}-{}-{}{}", std::process::id(), n, nanos, suffix);
        TempPath(std::env::temp_dir().join(name))
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
