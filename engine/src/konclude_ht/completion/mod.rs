//! `completion` — the SROIQ hypertableau completion engine
//! (Konclude `Source/Reasoner/Kernel/Algorithm/`).
//!
//! Layer 7 of the type-dependency DAG (`manifest/00-type-dag.md`): the per-thread
//! algorithm context (`CCalculationAlgorithmContext` /
//! `CCalculationAlgorithmContextBase`) and the completion task-handle algorithm
//! (`CCalculationTableauCompletionTaskHandleAlgorithm`) that drives every
//! `apply*Rule` over the `process/` completion-graph data model.
//!
//! W3 ports the STRUCT DEFINITIONS (member fields) here; the ~450 method bodies
//! land later as the `u01..u36` batches (see `manifest/01-completion-methods.md`).
//!
//! KONCLUDE-PORT-NOTE[ownership]: unlike the `model/` and `process/` layers, the
//! context and the algorithm are NOT arena-allocated — Konclude holds exactly one
//! of each PER WORKER THREAD (created in `createCalculationAlgorithmContext`).
//! They are therefore plain owned Rust structs, not `Id<T>`-addressed arena
//! elements; there are no completion-layer id aliases.

pub mod algorithm; // W3: CCalculationTableauCompletionTaskHandleAlgorithm — fields
pub mod clash; // W3c: clash/stop propagation (CCalculation{Clash,Stop}ProcessingException)
pub mod computed_cons_handler; // W129: CComputedConsequencesCacheHandler type-write queueing
pub mod context; // W3: CCalculationAlgorithmContext{,Base} — the per-thread context
pub mod dependency_factory;
pub mod grounding; // W44: CConceptNominalSchemaGroundingHandler helper methods
pub mod satexp_absorb; // satisfiable-cached absorption gates (docs/HYBRID-CB-HT.md section 23)
pub mod satexp_trace; // diagnostic: KM_HT_SATEXP_TRACE (docs/HYBRID-CB-HT.md section 23)
pub mod sat_node_exp_handler; // W128: CSaturationNodeExpansionCacheHandler concept-unsat queueing
pub mod strategy; // W3: Strategy/ rule-application priority + cache-retrieval policies
pub mod stubs; // W3: Algorithm-layer not-yet-ported placeholder markers // W3c: the create*Dependency allocator (CDependencyFactory)
pub mod unsat_handler; // W120: CUnsatisfiableCacheHandler memo/precheck slices

// W3 method-batch units u01..u36 (the apply*Rule engine bodies). Wired by the
// W3-RECONCILE integrator; cross-unit disagreements reconciled in pending.rs.
pub mod pending;
pub mod u01;
pub mod u02;
pub mod u03;
pub mod u04;
pub mod u05;
pub mod u06;
pub mod u07;
pub mod u08;
pub mod u09;
pub mod u10;
pub mod u11;
pub mod u12;
pub mod u13;
pub mod u14;
pub mod u15;
pub mod u16;
pub mod u17;
pub mod u18;
pub mod u19;
pub mod u20;
pub mod u21;
pub mod u22;
pub mod u23;
pub mod u24;
pub mod u25;
pub mod u26;
pub mod u27;
pub mod u28;
pub mod u29;
pub mod u30;
pub mod u31;
pub mod u32;
pub mod u33;
pub mod u34;
pub mod u35;
pub mod u36; // W3-RECONCILE: minimal PORT-PENDING sibling stubs (api gaps)

// ---------------------------------------------------------------------------
// Cached diagnostic environment gates.
//
// The `apply*Rule` / label-insertion bodies below are the completion hot path:
// `add_concept_to_individual*`, `insert_concepts_to_individual_concept_set`,
// `create_successor_individual` and the clash/OR sites run once per concept
// addition. A CLI-only diagnostic must not cost a `getenv` there.
// `std::env::var` additionally takes the process-wide environment lock and
// allocates a `String` on every call, and the KPSet classification phase makes
// hundreds of millions of those additions (ore_ont_3215: 18,323 satisfiability
// jobs over a 54,974-class terminology). The environment is immutable for the
// life of a worker, so read each setting once — the same treatment
// `saturation/mod.rs` already gives its own hot-path gates.
//
// Semantics are unchanged: every accessor returns exactly what the inline
// `std::env::var*` call returned, only without repeating the lookup.
// ---------------------------------------------------------------------------

macro_rules! cached_completion_flag {
    ($function:ident, $variable:literal) => {
        /// Cached `is_some()` gate for the identically named environment
        /// variable (looked up once — the call sites are hot-path).
        pub(crate) fn $function() -> bool {
            static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
            *ON.get_or_init(|| std::env::var_os($variable).is_some())
        }
    };
}

cached_completion_flag!(bridge_progress_enabled, "KM_BRIDGE_PROGRESS");
cached_completion_flag!(automat_rest_link_disabled, "KM_HT_NO_AUTOMAT_REST_LINK");
/// Konclude's restricted automaton re-fire (cpp 9662-9700): a state re-fired
/// for one freshly installed link propagates over that link only. On by
/// default since 2026-11-02 (docs/HYBRID-CB-HT.md section 17 argues it
/// derives the same closure as the all-successors arm);
/// `KM_HT_NO_AUTOMAT_REST_LINK=1` restores the all-successors re-fire.
pub(crate) fn automat_rest_link_enabled() -> bool {
    !automat_rest_link_disabled()
}
cached_completion_flag!(stop_trace_enabled, "KM_HT_STOP_TRACE");
cached_completion_flag!(blocking_scan_trace_enabled, "KM_HT_BLOCKING_SCAN_TRACE");
cached_completion_flag!(automat_rest_link_audit_enabled, "KM_HT_AUTOMAT_REST_LINK_AUDIT");
cached_completion_flag!(automat_rest_link_drop_enabled, "KM_HT_AUTOMAT_REST_LINK_DROP");
cached_completion_flag!(automat_closure_audit_enabled, "KM_HT_AUTOMAT_CLOSURE_AUDIT");
cached_completion_flag!(graph_dump_enabled, "KM_HT_GRAPH_DUMP");
cached_completion_flag!(satexp_trace_enabled, "KM_HT_SATEXP_TRACE");
cached_completion_flag!(atmost_rearm_disabled, "KM_HT_DIAG_NO_ATMOST_REARM");
cached_completion_flag!(automat_rest_link_audit_detail, "KM_HT_AUTOMAT_REST_LINK_AUDIT_DETAIL");

/// One operand the all-successors arm adds outside a restricted link
/// (`KM_HT_AUTOMAT_REST_LINK_AUDIT`). Printed at the first miss and at exit
/// of the worker through [`automat_rest_link_audit_report`].
pub(crate) fn automat_rest_link_audit_miss() {
    let n = AUTOMAT_REST_LINK_AUDIT_MISSES.fetch_add(1, std::sync::atomic::Ordering::Relaxed) + 1;
    if n == 1 || n.is_power_of_two() {
        eprintln!("AUTOMAT-REST-LINK-AUDIT misses={n}");
    }
}
/// One automaton re-fire restricted to a link (counted under
/// `KM_HT_AUTOMAT_REST_LINK_AUDIT` only, printed at powers of two).
pub(crate) fn automat_rest_link_refire() {
    if !automat_rest_link_audit_enabled() {
        return;
    }
    let n = AUTOMAT_REST_LINK_REFIRES.fetch_add(1, std::sync::atomic::Ordering::Relaxed) + 1;
    if n.is_power_of_two() {
        eprintln!("AUTOMAT-REST-LINK-AUDIT refires={n} misses={}",
            AUTOMAT_REST_LINK_AUDIT_MISSES.load(std::sync::atomic::Ordering::Relaxed));
    }
}
pub(crate) static AUTOMAT_REST_LINK_REFIRES: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
pub(crate) static AUTOMAT_REST_LINK_AUDIT_MISSES: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
cached_completion_flag!(bridge_phase_timing_enabled, "KM_BRIDGE_PHASE_TIMING");

/// Cap on the drive iterations of one completion run (`u02.rs`), looked up
/// once. `KM_HT_MAX_DRIVE_ITERATIONS` raises it for measurement; an overrun
/// still stops the drive, so the value never changes an answer.
pub(crate) fn max_drive_iterations() -> u64 {
    static CAP: std::sync::OnceLock<u64> = std::sync::OnceLock::new();
    *CAP.get_or_init(|| {
        std::env::var("KM_HT_MAX_DRIVE_ITERATIONS")
            .ok()
            .and_then(|value| value.parse().ok())
            .unwrap_or(5_000_000)
    })
}
cached_completion_flag!(ht_singleton_scan_after_merge_enabled, "KM_HT_SINGLETON_SCAN_AFTER_MERGE");
cached_completion_flag!(bridge_base_audit_enabled, "KM_BRIDGE_BASE_AUDIT");
cached_completion_flag!(bridge_search_log_enabled, "KM_BRIDGE_SEARCH_LOG");
cached_completion_flag!(bridge_dump_clash_enabled, "KM_BRIDGE_DUMP_CLASH");
cached_completion_flag!(bridge_dump_dep_chain_enabled, "KM_BRIDGE_DUMP_DEP_CHAIN");
cached_completion_flag!(bridge_watch_merge_enabled, "KM_BRIDGE_WATCH_MERGE");
cached_completion_flag!(bridge_watch_singleton_enabled, "KM_BRIDGE_WATCH_SINGLETON");
cached_completion_flag!(bridge_watch_atmost_enabled, "KM_BRIDGE_WATCH_ATMOST");
cached_completion_flag!(bridge_cache_debug_enabled, "KM_BRIDGE_CACHE_DEBUG");
cached_completion_flag!(sat_absorb_debug_enabled, "KM_SAT_ABSORB_DEBUG");
cached_completion_flag!(sat_no_root_initialization, "KM_HT_NO_SAT_ROOT_INITIALIZATION");
cached_completion_flag!(sat_no_successor_label_replay, "KM_HT_NO_SAT_SUCCESSOR_LABEL_REPLAY");
cached_completion_flag!(ht_or_trace_enabled, "KM_HT_OR_TRACE");
cached_completion_flag!(ht_ddb_no_skip_enabled, "KM_HT_DDB_NO_SKIP");
cached_completion_flag!(ht_atmost_rest_enabled, "KM_HT_ATMOST_REST");
cached_completion_flag!(ht_no_nn_rule, "KM_HT_NO_NN_RULE");
// The two changes of docs/HYBRID-CB-HT.md section 25 to optimized blocking
// (`u19.rs`), each with its own negative-control switch;
// `KM_HT_NO_SAT578_FIX=1` turns both off.
cached_completion_flag!(no_sat578_fix, "KM_HT_NO_SAT578_FIX");
cached_completion_flag!(no_b6_collision_guard, "KM_HT_NO_B6_COLLISION_GUARD");
cached_completion_flag!(no_b4a_nominal_guard, "KM_HT_NO_B4A_NOMINAL_GUARD");
/// `KM_HT_NO_B6_COLLISION_GUARD=1`: B6 keeps a successor in `C` c-blocked
/// under `not (<=n R.C)` at the parent without the collision test, as
/// Konclude does.
pub(crate) fn ht_no_b6_collision_guard() -> bool {
    no_sat578_fix() || no_b6_collision_guard()
}
/// `KM_HT_NO_B4A_NOMINAL_GUARD=1`: B4a counts every nominal neighbour of the
/// blocker, and ghosts of nodes merged into a nominal, as before.
pub(crate) fn ht_no_b4a_nominal_guard() -> bool {
    no_sat578_fix() || no_b4a_nominal_guard()
}
cached_completion_flag!(ht_nn_trace_enabled, "KM_HT_NN_TRACE");
cached_completion_flag!(ht_nn_distinct_first, "KM_HT_NN_DISTINCT_FIRST");
cached_completion_flag!(compact_distinct_groups_enabled, "KM_COMPACT_DISTINCT_GROUPS");

/// Cached value of `KM_HT_SATEXP_ABSORB_LEGACY` (diagnostic, read by
/// `satexp_absorb`; docs/HYBRID-CB-HT.md section 23), looked up once: its
/// readers sit on the at-most, existential and replay rule paths.
pub(crate) fn satexp_absorb_legacy_value() -> Option<&'static str> {
    static VALUE: std::sync::OnceLock<Option<String>> = std::sync::OnceLock::new();
    VALUE
        .get_or_init(|| std::env::var("KM_HT_SATEXP_ABSORB_LEGACY").ok())
        .as_deref()
}

macro_rules! cached_completion_i64 {
    ($function:ident, $variable:literal) => {
        /// Cached numeric watch target for the identically named environment
        /// variable (`None` = unset or unparsable), looked up once.
        pub(crate) fn $function() -> Option<crate::konclude_ht::model::Cint64> {
            static VALUE: std::sync::OnceLock<Option<crate::konclude_ht::model::Cint64>> =
                std::sync::OnceLock::new();
            *VALUE.get_or_init(|| {
                std::env::var_os($variable).and_then(|value| {
                    value
                        .to_string_lossy()
                        .parse::<crate::konclude_ht::model::Cint64>()
                        .ok()
                })
            })
        }
    };
}

cached_completion_i64!(bridge_watch_tag, "KM_BRIDGE_WATCH_TAG");
cached_completion_i64!(bridge_watch_negtag, "KM_BRIDGE_WATCH_NEGTAG");
cached_completion_i64!(bridge_watch_node, "KM_BRIDGE_WATCH_NODE");
cached_completion_i64!(bridge_ddb_trace_limit, "KM_BRIDGE_DDB_TRACE");
cached_completion_i64!(sat_label_debug_tag, "KM_SAT_LABEL_DEBUG_TAG");

macro_rules! cached_completion_u64 {
    ($function:ident, $variable:literal, $default:expr) => {
        /// Cached numeric limit for the identically named environment variable
        /// (`$default` when unset or unparsable), looked up once.
        pub(crate) fn $function() -> u64 {
            static VALUE: std::sync::OnceLock<u64> = std::sync::OnceLock::new();
            *VALUE.get_or_init(|| {
                std::env::var_os($variable)
                    .and_then(|value| value.to_string_lossy().parse::<u64>().ok())
                    .unwrap_or($default)
            })
        }
    };
}

cached_completion_u64!(bridge_max_drives, "KM_BRIDGE_MAX_DRIVES", u64::MAX);
cached_completion_u64!(bridge_search_log_limit, "KM_BRIDGE_SEARCH_LOG", 0);
cached_completion_u64!(bridge_dump_clash_limit, "KM_BRIDGE_DUMP_CLASH_LIMIT", 8);

/// Cached `KM_SAT_CACHE_TRACE_TAG=<tag>[,<tag>...]` watch list (empty = off).
pub(crate) fn sat_cache_trace_tags() -> &'static [crate::konclude_ht::model::Cint64] {
    static TAGS: std::sync::OnceLock<Vec<crate::konclude_ht::model::Cint64>> =
        std::sync::OnceLock::new();
    TAGS.get_or_init(|| {
        std::env::var_os("KM_SAT_CACHE_TRACE_TAG")
            .map(|spec| {
                spec.to_string_lossy()
                    .split(',')
                    .filter_map(|tag| tag.parse::<crate::konclude_ht::model::Cint64>().ok())
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default()
    })
}

#[cfg(test)]
mod cached_gate_test {
    /// The diagnostics are opt-in, so an unconfigured run must take the cheap
    /// path at every gate the rule bodies now consult.
    #[test]
    fn cached_gates_are_off_without_the_environment() {
        assert!(!super::bridge_progress_enabled());
        assert!(!super::bridge_search_log_enabled());
        assert!(!super::bridge_dump_clash_enabled());
        assert!(!super::bridge_dump_dep_chain_enabled());
        assert!(!super::bridge_watch_merge_enabled());
        assert!(!super::bridge_watch_singleton_enabled());
        assert!(!super::bridge_watch_atmost_enabled());
        assert!(!super::bridge_cache_debug_enabled());
        assert!(!super::sat_absorb_debug_enabled());
        assert!(!super::ht_or_trace_enabled());
        assert!(!super::ht_ddb_no_skip_enabled());
        assert!(!super::ht_atmost_rest_enabled());
        assert_eq!(super::bridge_watch_tag(), None);
        assert_eq!(super::bridge_watch_negtag(), None);
        assert_eq!(super::bridge_watch_node(), None);
        assert_eq!(super::sat_label_debug_tag(), None);
        assert!(super::sat_cache_trace_tags().is_empty());
        assert_eq!(super::bridge_max_drives(), u64::MAX);
        assert_eq!(super::bridge_search_log_limit(), 0);
    }
}

#[cfg(test)]
mod classify_test;
#[cfg(test)]
mod selftest; // W5: the first behavioural run — trivial consistency verdicts // W13: classification via consistency (subsumption = unsat probe)
