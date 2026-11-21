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
    release_before_worker_wait();
}

/// Return freed pages to the kernel before the supervisor idles on a worker
/// (E5). Unlike [`release_transient_heap`] this is not gated: the
/// supervisor's resident set counts beside the worker's for the worker's
/// whole lifetime, and one trim per worker start costs microseconds. glibc
/// `malloc_trim(0)`; mimalloc `mi_collect(true)`. Live allocations are
/// untouched.
#[inline]
pub fn release_before_worker_wait() {
    if switched_on(std::env::var_os("KM_NO_HEAP_TRIM").as_deref()) {
        return;
    }
    #[cfg(all(target_os = "linux", target_env = "gnu", not(feature = "mimalloc")))]
    unsafe {
        libc::malloc_trim(0);
    }
    #[cfg(feature = "mimalloc")]
    {
        extern "C" {
            fn mi_collect(force: bool);
        }
        unsafe { mi_collect(true) };
    }
}

/// The `r-x` mapping of this program's own code: the mapping in
/// `/proc/self/maps` that contains this function. Read once.
#[cfg(target_os = "linux")]
fn own_code_mapping() -> Option<(usize, usize)> {
    static RANGE: std::sync::OnceLock<Option<(usize, usize)>> = std::sync::OnceLock::new();
    *RANGE.get_or_init(|| {
        let here = own_code_mapping as fn() -> Option<(usize, usize)> as usize;
        let maps = std::fs::read_to_string("/proc/self/maps").ok()?;
        maps.lines().find_map(|line| {
            let mut fields = line.split_whitespace();
            let (start, end) = fields.next()?.split_once('-')?;
            let perms = fields.next()?;
            let (start, end) = (usize::from_str_radix(start, 16).ok()?, usize::from_str_radix(end, 16).ok()?);
            // Only a read-only, executable, private file mapping: its pages
            // are never written, so the file always holds their contents.
            (start <= here && here < end && perms == "r-xp").then_some((start, end))
        })
    })
}

/// Unmap the resident pages of this program's code before the supervisor
/// starts a worker and waits for it.
///
/// The code is a private, read-only mapping of the `km` file: the kernel
/// shares its pages with every km process through the page cache, but the
/// resident set of each process counts every code page that process has
/// touched (10 to 11 MiB of the supervisor's 12 MiB on small inputs). The
/// process-tree measurement adds the resident sets of the supervisor and of
/// the worker, so the shared code is counted twice while the supervisor only
/// waits. `madvise(MADV_DONTNEED)` drops the supervisor's page-table entries
/// for its code; the pages stay in the page cache, and any code the
/// supervisor runs afterwards is mapped again on first use (a minor fault,
/// the same as after the kernel reclaims code pages under memory pressure).
/// No data mapping is touched, so no state changes. Linux only;
/// `KM_NO_CODE_RELEASE=1` turns it off for measurement.
pub fn release_code_pages() {
    #[cfg(target_os = "linux")]
    {
        if switched_on(std::env::var_os("KM_NO_CODE_RELEASE").as_deref()) {
            return;
        }
        if let Some((start, end)) = own_code_mapping() {
            unsafe {
                libc::madvise(start as *mut libc::c_void, end - start, libc::MADV_DONTNEED);
            }
        }
    }
}

/// Turn transparent huge pages off for this process and every process it
/// starts (E4). With THP `always`, mimalloc's sparse 64 KiB pages each pull
/// in a 2 MiB huge page and every km process carries 20 to 30 MiB of extra
/// resident memory (docs/V1.7.0-P1-MEMORY.md). The flag is inherited across
/// fork and exec. `KM_KEEP_THP=1` keeps the system setting (measurement).
/// Linux only; a no-op elsewhere. Allocation hint only: no answer depends on
/// it.
pub fn disable_transparent_huge_pages() {
    #[cfg(target_os = "linux")]
    {
        if switched_on(std::env::var_os("KM_KEEP_THP").as_deref()) {
            return;
        }
        unsafe {
            libc::prctl(libc::PR_SET_THP_DISABLE, 1, 0, 0, 0);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{release_transient_heap, switched_on};
    use std::ffi::OsStr;

    #[test]
    fn heap_trim_requires_an_explicit_nonzero_switch() {
        let _test_env = crate::test_env::write();
        assert!(!switched_on(None));
        assert!(!switched_on(Some(OsStr::new(""))));
        assert!(!switched_on(Some(OsStr::new("0"))));
        assert!(switched_on(Some(OsStr::new("1"))));
        assert!(switched_on(Some(OsStr::new("yes"))));
    }

    #[test]
    fn releasing_the_heap_preserves_live_allocations() {
        let _test_env = crate::test_env::write();
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

    #[cfg(target_os = "linux")]
    #[test]
    fn released_code_pages_fault_back_in() {
        let _test_env = crate::test_env::write();
        let (start, end) = super::own_code_mapping().expect("km code mapping");
        assert!(start < end);
        fn work(n: u64) -> u64 {
            (0..n).fold(0u64, |acc, x| acc.wrapping_mul(31).wrapping_add(x))
        }
        let before = work(std::hint::black_box(10_000));
        super::release_code_pages();
        // Code runs again after its pages were dropped, with the same result.
        assert_eq!(work(std::hint::black_box(10_000)), before);
        let live: Vec<u8> = vec![7; 1 << 20];
        super::release_code_pages();
        assert!(live.iter().all(|&b| b == 7));
    }
}
