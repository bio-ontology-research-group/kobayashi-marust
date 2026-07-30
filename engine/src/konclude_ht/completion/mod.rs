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
cached_completion_flag!(bridge_search_log_enabled, "KM_BRIDGE_SEARCH_LOG");
cached_completion_flag!(bridge_dump_clash_enabled, "KM_BRIDGE_DUMP_CLASH");
cached_completion_flag!(bridge_dump_dep_chain_enabled, "KM_BRIDGE_DUMP_DEP_CHAIN");
cached_completion_flag!(bridge_watch_merge_enabled, "KM_BRIDGE_WATCH_MERGE");
cached_completion_flag!(bridge_watch_singleton_enabled, "KM_BRIDGE_WATCH_SINGLETON");
cached_completion_flag!(bridge_watch_atmost_enabled, "KM_BRIDGE_WATCH_ATMOST");
cached_completion_flag!(bridge_cache_debug_enabled, "KM_BRIDGE_CACHE_DEBUG");
cached_completion_flag!(sat_absorb_debug_enabled, "KM_SAT_ABSORB_DEBUG");
cached_completion_flag!(ht_or_trace_enabled, "KM_HT_OR_TRACE");
cached_completion_flag!(ht_ddb_no_skip_enabled, "KM_HT_DDB_NO_SKIP");
cached_completion_flag!(ht_atmost_rest_enabled, "KM_HT_ATMOST_REST");

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
