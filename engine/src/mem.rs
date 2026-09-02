//! Process-level allocator hints shared by the supervisor, the in-process
//! classifiers, and the worker binaries.
//!
//! glibc's malloc keeps freed chunks resident. The main arena returns memory
//! to the kernel only when its top chunk exceeds the trim threshold, and that
//! threshold grows dynamically once a large buffer has been freed, so parse
//! trees, normalisation intermediates, and wire buffers usually stay resident
//! after they are dropped. Every worker thread's arena additionally retains
//! the largest state that thread ever built. The ORE harness measures resident
//! set size (sampled over the whole process tree and maxed with the direct
//! child's high-water mark), not live bytes, so garbage from one finished phase
//! stays inside the measured peak of the next one.
//!
//! [`release_transient_heap`] makes the resident set track live data again at
//! a phase boundary. It never touches a live allocation, changes no reasoner
//! state, and is a no-op outside glibc. `KM_NO_HEAP_TRIM=1` disables every
//! call site so the effect can be measured in isolation.

use std::ffi::OsStr;
use std::sync::OnceLock;

/// Pure decision behind [`heap_trim_enabled`]: only an explicit, non-empty
/// value other than `0` opts out.
pub(crate) fn heap_trim_enabled_from(value: Option<&OsStr>) -> bool {
    match value {
        None => true,
        Some(value) => value.is_empty() || value.to_str() == Some("0"),
    }
}

fn heap_trim_enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| heap_trim_enabled_from(std::env::var_os("KM_NO_HEAP_TRIM").as_deref()))
}

/// Return every free page of every malloc arena to the kernel.
///
/// This is `malloc_trim(0)` on glibc: free chunks inside each heap are
/// released with `madvise(MADV_DONTNEED)` and each heap top is shrunk. Live
/// allocations are untouched, so this is invisible to every reasoner; only the
/// resident-set accounting of pages that nobody reads any more changes.
#[inline]
pub fn release_transient_heap() {
    if !heap_trim_enabled() {
        return;
    }
    #[cfg(all(target_os = "linux", target_env = "gnu"))]
    unsafe {
        libc::malloc_trim(0);
    }
}

#[cfg(test)]
mod tests {
    use super::{heap_trim_enabled_from, release_transient_heap};
    use std::ffi::OsStr;

    #[test]
    fn heap_trim_opt_out_requires_an_explicit_switch() {
        assert!(heap_trim_enabled_from(None));
        assert!(heap_trim_enabled_from(Some(OsStr::new(""))));
        assert!(heap_trim_enabled_from(Some(OsStr::new("0"))));
        assert!(!heap_trim_enabled_from(Some(OsStr::new("1"))));
        assert!(!heap_trim_enabled_from(Some(OsStr::new("yes"))));
    }

    #[test]
    fn releasing_the_heap_preserves_live_allocations() {
        // A trim must only affect freed pages: live data survives byte for byte.
        let live: Vec<Vec<u8>> = (0..64u8).map(|i| vec![i; 64 << 10]).collect();
        let garbage: Vec<Vec<u8>> = (0..64u8).map(|i| vec![i; 256 << 10]).collect();
        drop(garbage);
        release_transient_heap();
        for (i, block) in live.iter().enumerate() {
            assert!(block.iter().all(|&b| b as usize == i));
        }
        release_transient_heap();
    }
}
