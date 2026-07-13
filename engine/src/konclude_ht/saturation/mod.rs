//! `saturation` — the approximate-saturation pre-pass
//! (Konclude `Source/Reasoner/Kernel/Algorithm/`
//! `CCalculationTableauApproximationSaturationTaskHandleAlgorithm.{h,cpp}`).
//!
//! The cheap, non-branching, deterministic tableau-style saturation that runs
//! BEFORE the full backtracking completion: it applies the expansion rules but
//! never case-splits (disjunctions fold into a common-disjunct over-approximation,
//! successors merge rather than branch), and per concept/individual computes a
//! saturated label plus insufficiency / criticality flags marking where the cheap
//! over-approximation is unsound (the spots a real completion must revisit). See
//! `manifest/03-saturation-calc.md`.
//!
//! W4 ports the STRUCT DEFINITION (member fields) here; the ~195 method bodies
//! land later as the `SAT u01..u12` batches (see `manifest/03-saturation-calc.md`).
//!
//! KONCLUDE-PORT-NOTE[ownership]: like the `completion/` layer, the saturation
//! task-handle algorithm is NOT arena-allocated — Konclude holds exactly one PER
//! WORKER THREAD (built by the `CTaskHandleAlgorithmBuilder` injection seam). It
//! is therefore a plain owned Rust struct, not an `Id<T>`-addressed arena element;
//! there are no saturation-layer id aliases.

pub mod algorithm;
pub mod satellites; // W4.5: saturation-layer per-test satellites (linkers/descriptors/label-set)
pub mod stubs; // W4: saturation-layer not-yet-ported placeholder markers // W4: CCalculationTableauApproximationSaturationTaskHandleAlgorithm — fields

/// Cached `KM_SAT_CLASH_TRACE=1` gate for the per-site clash / implication
/// diagnostics (env looked up once — several of the sites are hot-path).
pub(crate) fn sat_clash_trace_enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("KM_SAT_CLASH_TRACE").is_some())
}

/// Cached `KM_SAT_ADD_TRACE=<concept index>` watch target (`None` = off).
pub(crate) fn sat_add_trace_watch() -> Option<usize> {
    static WATCH: std::sync::OnceLock<Option<usize>> = std::sync::OnceLock::new();
    *WATCH.get_or_init(|| {
        std::env::var_os("KM_SAT_ADD_TRACE")
            .and_then(|value| value.to_string_lossy().parse::<usize>().ok())
    })
}

// These diagnostics sit in rule-application and label-insertion hot paths.
// Read each immutable CLI environment setting once: ore_ont_3215 performs
// roughly 187 million insertion attempts, so even a disabled `getenv` per
// attempt dominates the actual Konclude rule work.
macro_rules! cached_sat_debug_tag {
    ($function:ident, $variable:literal) => {
        pub(crate) fn $function() -> Option<i64> {
            static TAG: std::sync::OnceLock<Option<i64>> = std::sync::OnceLock::new();
            *TAG.get_or_init(|| {
                std::env::var_os($variable)
                    .and_then(|value| value.to_string_lossy().parse::<i64>().ok())
            })
        }
    };
}

cached_sat_debug_tag!(sat_add_trace_tag, "KM_SAT_ADD_TRACE_TAG");
cached_sat_debug_tag!(sat_copy_debug_tag, "KM_SAT_COPY_DEBUG_TAG");
cached_sat_debug_tag!(sat_final_debug_tag, "KM_SAT_FINAL_DEBUG_TAG");
cached_sat_debug_tag!(sat_init_debug_tag, "KM_SAT_INIT_DEBUG_TAG");
cached_sat_debug_tag!(sat_link_debug_tag, "KM_SAT_LINK_DEBUG_TAG");
cached_sat_debug_tag!(sat_or_debug_tag, "KM_SAT_OR_DEBUG_TAG");
cached_sat_debug_tag!(sat_status_debug_tag, "KM_SAT_STATUS_DEBUG_TAG");
cached_sat_debug_tag!(sat_common_debug_tag, "KM_SAT_COMMON_DEBUG_TAG");

pub(crate) fn sat_common_debug_operands() -> &'static std::collections::BTreeSet<i64> {
    static OPERANDS: std::sync::OnceLock<std::collections::BTreeSet<i64>> =
        std::sync::OnceLock::new();
    OPERANDS.get_or_init(|| {
        std::env::var_os("KM_SAT_COMMON_DEBUG_OPERANDS")
            .into_iter()
            .flat_map(|value| {
                value
                    .to_string_lossy()
                    .split(',')
                    .filter_map(|part| part.trim().parse::<i64>().ok())
                    .collect::<Vec<_>>()
            })
            .collect()
    })
}

pub(crate) fn sat_clash_backtrace_enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("KM_SAT_CLASH_BT").is_some())
}

// W4 method-batch units SAT u01..u12 (the ~195 apply*Rule / driver / node-init /
// ATMOST-merging / critical-concept / extension-propagation / cache-handoff
// method bodies — see manifest/03-saturation-calc.md). Reconciled in W4-reconcile.
pub mod s01;
pub mod s02;
pub mod s03;
pub mod s04;
pub mod s05;
pub mod s06;
pub mod s07;
pub mod s08;
pub mod s09;
pub mod s10;
pub mod s11;
pub mod s12;

// W4-RECONCILE: minimal PORT-PENDING sibling stubs (the cross-unit `self.foo(...)`
// calls defined in no s-unit). See completion/pending.rs for the W3 twin.
pub mod pending;
