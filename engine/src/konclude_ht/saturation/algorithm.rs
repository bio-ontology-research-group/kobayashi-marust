//! `saturation::algorithm` — the approximate-saturation task-handle.
//!
//! Ports the MEMBER FIELDS of Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauApproximationSaturationTaskHandleAlgorithm.h`
//! (the `// protected variables` block, lines 467–590). This is the struct
//! definition only (wave W4); the ~195 method bodies (the `apply*Rule` saturation
//! engine, the driver loop, node init, ATMOST cardinality merging, critical-concept
//! detection, extension propagation, cache hand-off) land later as the
//! `SAT u01..u12` batches — see `manifest/03-saturation-calc.md`.
//!
//! KONCLUDE-PORT-NOTE[ownership]: `CCalculationTableauApproximationSaturationTaskHandleAlgorithm`
//! is NOT arena-allocated — one instance lives per worker thread (built by the
//! `CTaskHandleAlgorithmBuilder`). The context back-pointer `mCalcAlgContext` and
//! the databox alias `mProcessingDataBox` become opaque `Cint64`; the
//! ctor-injected backend cache handler + occurrence-statistics collector and the
//! two by-value saturation analysers use `saturation::stubs`; the cached
//! completion-graph vectors reuse `process::stubs`, and the last-config / debug
//! task reuse `completion::stubs`. Method bodies are the `SAT u01..u12` units below.

#![allow(dead_code)]

use super::super::completion::stubs::{
    CalculationConfigurationExtension, SatisfiableCalculationTask,
};
use super::super::model::substrate::{Cint64, Id, INVALID};
use super::super::process::node_resolution::IndividualProcessNodeVector;
use super::stubs::{
    SatisfiableTaskSaturationIndividualsAnalyser,
    SatisfiableTaskSaturationOccurrenceStatisticsCollector,
    SatisfiableTaskSaturationPreyingAnalyser, SaturationNodeBackendAssociationCacheHandler,
};

/// KONCLUDE-PORT-NOTE[pointer-alias]: `typedef void (...::*TableauRuleFunction)(...)`
/// — a pointer-to-member of the rule-application methods. Until the `apply*Rule`
/// saturation methods are ported (the `SAT u01..u12` batches), a rule slot is an
/// opaque `Cint64` index/handle (`INVALID` == `nullptr`). The jump tables become
/// fixed `[Cint64; N]`.
pub type TableauRuleFunction = Cint64;

/// Number of rule slots in the jump tables (`mRuleFuncCount`).
pub const RULE_FUNC_COUNT: usize = 200;

/// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm`.
///
/// The per-thread approximate-saturation engine. This unit ports the member
/// fields only; the method bodies are deferred.
///
/// W4 method-batch: SAT u01..u12  (the ~195 `apply*Rule` / driver / node-init /
/// ATMOST-merging / critical-concept / extension-propagation / cache-handoff
/// methods — see `manifest/03-saturation-calc.md`).
pub struct SaturationTaskHandleAlgorithm {
    // --- context + databox back-refs (.h 469–470) ---
    /// `CCalculationAlgorithmContextBase* mCalcAlgContext`. [ownership] opaque
    /// back-handle (the Layer-7 ctx↔algo cycle).
    pub calc_alg_context: Cint64,
    /// `CProcessingDataBox* mProcessingDataBox`. [ownership] opaque alias of the
    /// context-owned databox.
    pub processing_data_box: Cint64,

    // --- satisfiable-task analysers + collectors + backend cache (.h 472–476) ---
    /// `CSatisfiableTaskSaturationPreyingAnalyser` (by value).
    pub sat_task_saturation_prey_analyser: SatisfiableTaskSaturationPreyingAnalyser,
    /// `CSatisfiableTaskSaturationIndividualsAnalyser` (by value).
    pub sat_task_saturation_indi_analyser: SatisfiableTaskSaturationIndividualsAnalyser,
    /// `CSatisfiableTaskSaturationOccurrenceStatisticsCollector*` (ctor-injected pointer).
    pub sat_task_occ_stat_collector: Id<SatisfiableTaskSaturationOccurrenceStatisticsCollector>,
    /// `CSaturationNodeBackendAssociationCacheHandler*` (ctor-injected pointer).
    pub backend_ass_cace_handler: Id<SaturationNodeBackendAssociationCacheHandler>,

    // --- rule jump tables (.h 479–485) ---
    /// `TableauRuleFunction* mPosJumpFuncVec`. [pointer-alias] opaque (points into
    /// `pos_tableau_rule_jump_func_vec`).
    pub pos_jump_func_vec: Cint64,
    /// `TableauRuleFunction* mNegJumpFuncVec`.
    pub neg_jump_func_vec: Cint64,
    pub pos_tableau_rule_jump_func_vec: [TableauRuleFunction; RULE_FUNC_COUNT],
    pub neg_tableau_rule_jump_func_vec: [TableauRuleFunction; RULE_FUNC_COUNT],

    // --- saturation mode + config flags (.h 488–526) ---
    pub opt_independent_saturation_mode: bool,
    pub conf_implication_adding_skipping: bool,
    pub conf_force_all_concept_insertion: bool,
    pub conf_force_all_copy_instead_of_substituition: bool,
    pub conf_debugging_write_data: bool,
    pub conf_debugging_write_data_saturation_tasks: bool,
    pub wrote_functional_succ_pred_merging_debug_string: bool,
    pub conf_add_critical_concepts_to_queues: bool,
    pub conf_directly_critical_to_insufficient: bool,
    pub conf_check_critical_concepts: bool,
    pub conf_concepts_extension_processing: bool,
    pub conf_all_concepts_extension_processing: bool,
    pub conf_functional_concepts_extension_processing: bool,
    pub conf_nominal_processing: bool,
    pub conf_copy_node_from_top_individual_for_many_concepts: bool,
    pub conf_simple_merging_test_for_atmost_critical_testing: bool,
    pub conf_detailed_merging_test_for_atmost_critical_testing: bool,
    pub conf_delayed_merging_critical_atmost_concepts: bool,
    pub conf_delayed_merging_critical_atmost_concepts_cardinality_size: Cint64,
    pub conf_resolve_operand_concept_size: Cint64,
    pub conf_force_many_concept_saturation: Cint64,
    pub conf_referred_node_many_concept_count: Cint64,
    pub conf_many_concept_referred_node_count_process_limit: Cint64,
    pub conf_referred_node_concept_count_process_limit: Cint64,
    pub conf_referred_node_unprocessed_count_process_limit: Cint64,
    pub conf_referred_node_checking_depth: Cint64,
    pub conf_occurrence_statistics_collection: Cint64,

    // --- last config (.h 528) ---
    pub last_config: Id<CalculationConfigurationExtension>,

    // --- cached completion-graph state (.h 532–540) ---
    pub cached_completion_graph_missing: bool,
    pub cached_completion_graph_loaded: bool,
    pub det_cached_cg_indi_vector: Id<IndividualProcessNodeVector>,
    pub non_det_cached_cg_indi_vector: Id<IndividualProcessNodeVector>,
    pub non_det_consistency_cg: bool,
    pub det_consistency_cg: bool,
    pub representative_data_loaded: bool,
    pub representative_data_available: bool,

    // --- applied-rule counters (debugging, .h 545–551) ---
    pub applied_all_rule_count: Cint64,
    pub applied_some_rule_count: Cint64,
    pub applied_and_rule_count: Cint64,
    pub applied_or_rule_count: Cint64,
    pub applied_atleast_rule_count: Cint64,
    pub applied_atmost_rule_count: Cint64,
    pub applied_total_rule_count: Cint64,

    // --- added-concept counters (.h 553–558) ---
    pub added_all_concepts: Cint64,
    pub added_some_concepts: Cint64,
    pub added_impl_concepts: Cint64,
    pub added_trigg_concepts: Cint64,
    pub added_sub_concepts: Cint64,
    pub added_else_concepts: Cint64,

    // --- node-substitution / copy counters (.h 560–561) ---
    pub substituited_indi_node_count: Cint64,
    pub copied_indi_node_count: Cint64,

    // --- status-update counters (.h 563–564) ---
    pub direct_updated_status_indi_node_count: Cint64,
    pub indirect_updated_status_indi_node_count: Cint64,

    // --- nominal / cardinality update counters (.h 566–567) ---
    pub successor_connected_nominal_updated_count: Cint64,
    pub maximum_cardinality_candidates_updated_count: Cint64,

    // --- ALL-successor-ext + disjunction-skip counters (.h 569, 572) ---
    pub all_succ_ext_initialized_count: Cint64,
    pub disjunction_initialized_skipped_count: Cint64,

    // --- debug model strings (.h 575–584) ---
    pub debug_indi_model_string_list: Vec<String>,
    pub debug_indi_model_string: String,
    pub rule_begin_debug_indi_model_string: String,
    pub rule_end_debug_indi_model_string: String,
    pub end_saturation_debug_indi_model_string: String,
    /// `CSatisfiableCalculationTask* mDebugTestingSaturationTask`.
    pub debug_testing_saturation_task: Id<SatisfiableCalculationTask>,
    pub debug_test_saturation_debug_indi_model_string: String,

    // --- insufficiency counters (.h 588–589) ---
    pub insufficient_atmost_count: Cint64,
    pub insufficient_all_count: Cint64,
    // KM diagnostic counters (no C++ analogue): per-type critical-deferral
    // tallies surfaced through the KM_SAT_DEBUG stats line.
    pub insufficient_or_count: Cint64,
    pub insufficient_eqcand_count: Cint64,
    pub insufficient_value_count: Cint64,
    pub insufficient_nominal_count: Cint64,
}

impl SaturationTaskHandleAlgorithm {
    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm`
    /// construction.
    ///
    /// KONCLUDE-PORT-NOTE[uninit]: the C++ ctor sets the rule jump-table and takes
    /// the two ctor-injected handles (`backendAssCaceHandler`, `satTaskOccStatCollector`);
    /// the remaining fields are seeded by `readCalculationConfig` /
    /// `createCalculationAlgorithmContext`. The port mirrors that: every handle
    /// starts `INVALID`/`Id::NONE`, counters `0`, flags `false`, collections empty.
    /// The two ctor-injected handles are `Id::NONE` here; `new_with_handlers`
    /// installs them when the calling factory is ported.
    pub fn new() -> Self {
        SaturationTaskHandleAlgorithm {
            calc_alg_context: INVALID,
            processing_data_box: INVALID,

            sat_task_saturation_prey_analyser: Default::default(),
            sat_task_saturation_indi_analyser: Default::default(),
            sat_task_occ_stat_collector: Id::NONE,
            backend_ass_cace_handler: Id::NONE,

            pos_jump_func_vec: INVALID,
            neg_jump_func_vec: INVALID,
            pos_tableau_rule_jump_func_vec: [INVALID; RULE_FUNC_COUNT],
            neg_tableau_rule_jump_func_vec: [INVALID; RULE_FUNC_COUNT],

            opt_independent_saturation_mode: false,
            conf_implication_adding_skipping: false,
            conf_force_all_concept_insertion: false,
            conf_force_all_copy_instead_of_substituition: false,
            conf_debugging_write_data: false,
            conf_debugging_write_data_saturation_tasks: false,
            wrote_functional_succ_pred_merging_debug_string: false,
            conf_add_critical_concepts_to_queues: false,
            conf_directly_critical_to_insufficient: false,
            conf_check_critical_concepts: false,
            conf_concepts_extension_processing: false,
            conf_all_concepts_extension_processing: false,
            conf_functional_concepts_extension_processing: false,
            conf_nominal_processing: false,
            conf_copy_node_from_top_individual_for_many_concepts: false,
            conf_simple_merging_test_for_atmost_critical_testing: false,
            conf_detailed_merging_test_for_atmost_critical_testing: false,
            conf_delayed_merging_critical_atmost_concepts: false,
            conf_delayed_merging_critical_atmost_concepts_cardinality_size: 0,
            conf_resolve_operand_concept_size: 0,
            conf_force_many_concept_saturation: 0,
            conf_referred_node_many_concept_count: 0,
            conf_many_concept_referred_node_count_process_limit: 0,
            conf_referred_node_concept_count_process_limit: 0,
            conf_referred_node_unprocessed_count_process_limit: 0,
            conf_referred_node_checking_depth: 0,
            conf_occurrence_statistics_collection: 0,

            last_config: Id::NONE,

            cached_completion_graph_missing: false,
            cached_completion_graph_loaded: false,
            det_cached_cg_indi_vector: Id::NONE,
            non_det_cached_cg_indi_vector: Id::NONE,
            non_det_consistency_cg: false,
            det_consistency_cg: false,
            representative_data_loaded: false,
            representative_data_available: false,

            applied_all_rule_count: 0,
            applied_some_rule_count: 0,
            applied_and_rule_count: 0,
            applied_or_rule_count: 0,
            applied_atleast_rule_count: 0,
            applied_atmost_rule_count: 0,
            applied_total_rule_count: 0,

            added_all_concepts: 0,
            added_some_concepts: 0,
            added_impl_concepts: 0,
            added_trigg_concepts: 0,
            added_sub_concepts: 0,
            added_else_concepts: 0,

            substituited_indi_node_count: 0,
            copied_indi_node_count: 0,

            direct_updated_status_indi_node_count: 0,
            indirect_updated_status_indi_node_count: 0,

            successor_connected_nominal_updated_count: 0,
            maximum_cardinality_candidates_updated_count: 0,

            all_succ_ext_initialized_count: 0,
            disjunction_initialized_skipped_count: 0,

            debug_indi_model_string_list: Vec::new(),
            debug_indi_model_string: String::new(),
            rule_begin_debug_indi_model_string: String::new(),
            rule_end_debug_indi_model_string: String::new(),
            end_saturation_debug_indi_model_string: String::new(),
            debug_testing_saturation_task: Id::NONE,
            debug_test_saturation_debug_indi_model_string: String::new(),

            insufficient_atmost_count: 0,
            insufficient_all_count: 0,
            insufficient_or_count: 0,
            insufficient_eqcand_count: 0,
            insufficient_value_count: 0,
            insufficient_nominal_count: 0,
        }
    }

    // ----------------------------------------------------------------------
    // Simple accessors. Every stateful method (the driver loop `handleTask`,
    // the apply*Rule saturation engine, node init, ATMOST cardinality merging,
    // critical-concept detection, extension propagation, cache hand-off) is
    // deferred to the W4 method-batch units (see manifest/03-saturation-calc.md).
    //
    // W4 method-batch: SAT u01..u12
    // ----------------------------------------------------------------------

    /// Port of `getAppliedANDRuleCount`.
    pub fn applied_and_rule_count(&self) -> Cint64 {
        self.applied_and_rule_count
    }
    /// Port of `getAppliedORRuleCount`.
    pub fn applied_or_rule_count(&self) -> Cint64 {
        self.applied_or_rule_count
    }
    /// Port of `getAppliedSOMERuleCount`.
    pub fn applied_some_rule_count(&self) -> Cint64 {
        self.applied_some_rule_count
    }
    /// Port of `getAppliedATLEASTRuleCount`.
    pub fn applied_atleast_rule_count(&self) -> Cint64 {
        self.applied_atleast_rule_count
    }
    /// Port of `getAppliedALLRuleCount`.
    pub fn applied_all_rule_count(&self) -> Cint64 {
        self.applied_all_rule_count
    }
    /// Port of `getAppliedATMOSTRuleCount`.
    pub fn applied_atmost_rule_count(&self) -> Cint64 {
        self.applied_atmost_rule_count
    }
    /// Port of `getAppliedTotalRuleCount`.
    pub fn applied_total_rule_count(&self) -> Cint64 {
        self.applied_total_rule_count
    }
}

impl Default for SaturationTaskHandleAlgorithm {
    fn default() -> Self {
        Self::new()
    }
}
