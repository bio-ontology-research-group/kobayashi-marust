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
//! state, and is a no-op outside glibc. `KM_HEAP_TRIM=1` enables the calls on
//! measured routes; `KM_NO_HEAP_TRIM=1` remains a diagnostic override.

use std::ffi::OsStr;
fn switched_on(value: Option<&OsStr>) -> bool {
    matches!(value.and_then(OsStr::to_str), Some(value) if !value.is_empty() && value != "0")
}

fn heap_trim_enabled() -> bool {
    switched_on(std::env::var_os("KM_HEAP_TRIM").as_deref())
        && !switched_on(std::env::var_os("KM_NO_HEAP_TRIM").as_deref())
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
    use super::{release_transient_heap, switched_on};
    use std::ffi::OsStr;

    #[test]
    fn heap_trim_requires_an_explicit_nonzero_switch() {
        assert!(!switched_on(None));
        assert!(!switched_on(Some(OsStr::new(""))));
        assert!(!switched_on(Some(OsStr::new("0"))));
        assert!(switched_on(Some(OsStr::new("1"))));
        assert!(switched_on(Some(OsStr::new("yes"))));
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
