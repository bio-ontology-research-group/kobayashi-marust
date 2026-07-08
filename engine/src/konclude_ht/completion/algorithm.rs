//! `completion::algorithm` — the SROIQ hypertableau completion task-handle.
//!
//! Ports the MEMBER FIELDS of Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.h`
//! (the `// protected variables` block, lines 1082–1593). This is the struct
//! definition only (wave W3); the ~450 method bodies (the `apply*Rule` engine,
//! the driver loop, blocking, caching, merging, backtracking) land later as the
//! `u01..u36` batches — see `manifest/01-completion-methods.md`.
//!
//! KONCLUDE-PORT-NOTE[ownership]: `CCalculationTableauCompletionTaskHandleAlgorithm`
//! is NOT arena-allocated — one instance lives per worker thread. It caches handles
//! into the per-thread `CalculationAlgorithmContextBase` (the Layer-7 ctx↔algo
//! cycle, `manifest/00-type-dag.md`): the back-pointer `mCalcAlgContext` and the
//! databox alias `mProcessingDataBox` become opaque `Cint64`; the processing-queue
//! caches reuse the `process::stubs` markers; the strategy/factory/handler/analyser
//! caches use `completion::stubs`. Method bodies are the `u01..u36` units below.

#![allow(dead_code)]

use std::collections::{BTreeMap, HashMap, HashSet};

use super::super::model::substrate::{Cint64, Id, NegLink, INVALID};
use super::super::model::ConceptId;
use super::super::process::stubs::{
    IndividualConceptBatchProcessingQueue, IndividualCustomPriorityProcessingQueue,
    IndividualDepthProcessingQueue, IndividualLinkerRotationProcessingQueue,
    IndividualProcessingQueue, IndividualReactivationProcessingQueue,
    IndividualUnsortedProcessingQueue, ReusingReviewData, SignatureBlockingReviewSet,
};
use super::super::process::{BranchNodeId, DependencyId, NodeId, RestrictionSpecId, TrackPointId};
use super::grounding::ConceptNominalSchemaGroundingHandler;
use super::strategy::{
    ConceptProcessingPriorityStrategy,
    IndividualAncestorDepthMaximumConceptProcessingPriorityStrategy,
    IndividualProcessingPriorityStrategy, TaskProcessingPriorityStrategy,
    UnsatisfiableCacheRetrievalStrategy,
};
use super::stubs::{
    CalculationConfigurationExtension, ClashDescriptorFactory, CompletionGraphCacheHandler,
    ComputedConsequencesCacheHandler, DatatypeIndividualProcessNodeHandler, DependencyFactory,
    IncrementalCompletionGraphCompatibleExpansionHandler, IndividualNodeBackendCacheHandler,
    IndividualNodeManager, OccurrenceStatisticsCacheHandler, ReuseCompletionGraphCacheHandler,
    SatisfiableExpanderCacheHandler, SatisfiableTaskClassificationMessageAnalyser,
    SatisfiableTaskComplexAnsweringMessageAnalyser, SatisfiableTaskConsistencyPreyingAnalyser,
    SatisfiableTaskIncrementalConsistencyPreyingAnalyser,
    SatisfiableTaskMarkerIndividualPropagationAnalyser,
    SatisfiableTaskPossibleAssertionCollectingAnalyser,
    SatisfiableTaskPropagationBindingAnsweringMessageAnalyser,
    SatisfiableTaskPropertyClassificationMessageAnalyser, SaturationNodeExpansionCacheHandler,
    UnsatisfiableCacheHandler,
};

/// KONCLUDE-PORT-NOTE[pointer-alias]: `typedef void (...::*TableauRuleFunction)(...)`
/// — a pointer-to-member of the rule-application methods. Until the `apply*Rule`
/// methods are ported (the `u01..u36` batches), a rule slot is an opaque `Cint64`
/// index/handle (`INVALID` == `nullptr`). The jump tables become fixed `[Cint64; N]`.
pub type TableauRuleFunction = Cint64;

/// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::INDINODEQUEUETYPE`
/// (the source queue an individual node was taken from).
///
/// KONCLUDE-PORT-NOTE[overload]: variant names mirror the C++ `INQT_*` enumerators
/// verbatim as port anchors; `non_camel_case_types` is allowed to keep them legible.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[allow(non_camel_case_types)]
pub enum IndiNodeQueueType {
    Inqt_None,
    Inqt_CacheTest,
    Inqt_Immediate,
    Inqt_DelayedBackendInit,
    Inqt_RoleAss,
    Inqt_BackendSyncRetest,
    Inqt_BackendDirectInfluenceExpansion,
    Inqt_BackendIndirectCompatibilityExpansion,
    Inqt_DetExp,
    Inqt_VstSatTesting,
    Inqt_VsTriggering,
    Inqt_BlockReact,
    Inqt_CompCachedReact,
    Inqt_BlockUp,
    Inqt_DepthNormal,
    Inqt_Nominal,
    Inqt_NominalCachingLossReactivation,
    Inqt_DepthFirst,
    Inqt_Outdated,
    Inqt_VarBindBatchQue,
    Inqt_DelayedNominal,
    Inqt_BackendExpansionReuse,
}

impl Default for IndiNodeQueueType {
    fn default() -> Self {
        IndiNodeQueueType::Inqt_None
    }
}

/// Port of the nested class
/// `CCalculationTableauCompletionTaskHandleAlgorithm::IndiAssociatedConceptSetCacheData`.
#[derive(Debug, Default, Clone)]
pub struct IndiAssociatedConceptSetCacheData {
    /// `QSet<QSet<CConcept*>> mConceptSet`. KONCLUDE-PORT-NOTE[api]: a set-of-sets
    /// is not directly expressible as `HashSet<HashSet<_>>` (inner not `Hash`); kept
    /// as insertion-ordered `Vec<Vec<ConceptId>>`, same elements.
    pub concept_set: Vec<Vec<ConceptId>>,
    /// `bool mCreated = false`.
    pub created: bool,
}

/// Number of rule slots in the jump tables (`mRuleFuncCount`).
pub const RULE_FUNC_COUNT: usize = 200;
/// `mDebugTaskIDVectorSize`.
pub const DEBUG_TASK_ID_VECTOR_SIZE: usize = 100;
/// `mDeterministicProcessPriority`.
pub const DETERMINISTIC_PROCESS_PRIORITY: Cint64 = 4;
/// `mImmediatelyProcessPriority`.
pub const IMMEDIATELY_PROCESS_PRIORITY: Cint64 = 8;

/// The at-most merge-branching payload (`mergeMergingIndividualNodesPairwise`,
/// cpp 15044–15093): Konclude forks one `createMergeBranchingTask` PER MERGEABLE
/// PAIR of the counted successors — which pair merges is a non-deterministic
/// CHOICE, and a clash under one pairing must backtrack into trying another.
/// The in-process realisation makes each pairing an alternative of an
/// `OrBranchPoint`: alternative `k` merges `pairs[k].1` INTO `pairs[k].0`, then
/// re-checks the bound (Konclude re-fires via reapplication; the port re-enters
/// `ht_atmost_merge_loop`, which pushes a nested branch point if still over).
/// A merge mutates node labels / links / distinct hashes across nodes, which
/// the single-node label snapshot cannot undo — merge branch points therefore
/// ALWAYS own a branch epoch (`own_epoch`), independent of the global COW mode.
pub struct AtMostMergeBranch {
    /// The mergeable `(into, from)` pairs, in gather order (alternative k
    /// merges `pairs[k].1` into `pairs[k].0`; pair 0 is the pair the previous
    /// greedy realisation merged, so deterministic runs are unchanged).
    pub pairs: Vec<(NodeId, NodeId)>,
    /// The counted parent (the at-most rule's process individual): re-seeded
    /// onto the immediately-processing queue and used as the link-relocation
    /// source after each merge alternative.
    pub parent: NodeId,
    /// The at-most concept's role.
    pub role: super::super::model::RoleId,
    /// The at-most qualifier operand list (for the bound re-check re-gather).
    pub concept_linker: Vec<NegLink<ConceptId>>,
    /// The rule-level negation flag the at-most was dispatched with.
    pub negate: bool,
    /// The at-most bound (already `getParameter() - 1*negate`-adjusted).
    pub cardinality: Cint64,
    /// The at-most concept descriptor (the clash anchor for the re-check).
    pub con_des: super::super::process::ConDescId,
}

/// What the alternatives of an `OrBranchPoint` DO: add a disjunct (the OR rule),
/// merge a successor pair (the at-most rule's non-deterministic merging), or
/// qualify a successor (the choose rule).
pub enum BranchKind {
    /// The alternatives live in `OrBranchPoint::disjuncts`.
    Disjunction,
    /// The alternatives are the merge pairs (see [`AtMostMergeBranch`]).
    AtMostMerge(AtMostMergeBranch),
    /// The choose rule (`qualifyMergingIndividualNodes`, cpp 15677–15816): a
    /// `role`-successor whose label decides NEITHER polarity of the at-most
    /// qualifier is non-deterministically qualified — alternative 0 adds the
    /// NEGATED qualifier (Konclude's `qualNeg = true` first task), alternative
    /// 1 adds the positive qualifier (making it a merge candidate); both
    /// re-fire the at-most bound check on the counted parent.
    AtMostQualify {
        /// The successor being qualified.
        succ: NodeId,
        /// The at-most re-check payload.
        atmost: AtMostMergeBranch,
    },
}

/// An open disjunction branch point on the in-process chronological search stack.
///
/// KONCLUDE-PORT-NOTE[branching]: Konclude does NOT keep an in-process branch stack
/// — `applyORRule`/`executeORBranching` (u09) FORK a `CSatisfiableCalculationTask`
/// per alternative and throw `CCalculationStopProcessingException`, and the
/// scheduler re-drives each child task; backtracking is the dependency-directed
/// `clashedBacktracking` (u29) over the `CBranchTreeNode` / non-deterministic
/// `CDependencyTrackPoint` graph. Both the Task/scheduler layer and the u29
/// tracking-line records are still unported (`W3-DEFER`/`PORT-PENDING`). To exercise
/// disjunction end-to-end the port models the search IN-PROCESS: each disjunction
/// pushes one `OrBranchPoint`, the first unexplored alternative is added eagerly, and
/// on a clash the drive loop (u02) restores to the topmost branch with a remaining
/// alternative and tries the next disjunct (a CHRONOLOGICAL backtrack). The faithful
/// per-alternative task fork + dependency-directed backjump is the documented gap;
/// the `branch_node` / `or_dependency_node` are the real ported records (`CBranchTreeNode`
/// / `CORDependencyNode`) so the eventual faithful path reuses them.
pub struct OrBranchPoint {
    /// The individual node the disjunction is processed on.
    pub node: NodeId,
    /// The disjunction's operand list (`concept->getOperandList()`), in order.
    pub disjuncts: Vec<NegLink<ConceptId>>,
    /// The `negate` flag the OR rule was dispatched with (each alternative's
    /// effective negation is `disjunct.negated ^ negate`).
    pub negate: bool,
    /// Index of the NEXT unexplored alternative (the first was added at push time,
    /// so this starts at 1).
    pub next_alt: usize,
    /// The dependency track point the chosen disjunct is added under.
    pub dep_track_point: TrackPointId,
    /// The allocated `CBranchTreeNode` for this branch (search-tree spine).
    pub branch_node: BranchNodeId,
    /// The allocated `CORDependencyNode` (`DNTORDEPENDENCY`).
    pub or_dependency_node: DependencyId,
    /// DDB (`conf_dependency_backjumping`): one non-deterministic dependency
    /// track point PER ALTERNATIVE, minted upfront at push time (Konclude mints
    /// one per forked branch task in `executeORBranching`; upfront minting is
    /// required so "all sibling branches clashed" in the u29 analysis means the
    /// whole disjunction is refuted — lazily-minted siblings would make the
    /// propagation fire while untried alternatives remain). Alternative `k`'s
    /// concepts are added under `alt_track_points[k]`, whose branching tag is
    /// this branch point's nesting depth — the tag the tracked-clash analysis
    /// keys on. Empty when the dependency spine is off (chronological mode).
    pub alt_track_points: Vec<TrackPointId>,
    /// The `used_branch_tree_node` at push time, restored when this branch
    /// point is popped (each active alternative installs its own branch node
    /// as the used node so nested disjunctions nest one level deeper).
    pub parent_used_branch_node: BranchNodeId,
    /// SOUND-BACKTRACK snapshot of `node`'s concept label set taken BEFORE the
    /// first disjunct was added. On backtrack it is restored (undoing the failed
    /// disjunct's downstream derivations) so the next alternative is tried on the
    /// clean pre-disjunction state — fixing the chronological-backtrack
    /// unsoundness (see `try_backtrack_or_branch`). Sound ONLY when no successor
    /// node was created since the push (`node_count_at_push` guard); a
    /// successor-creating disjunct still needs the full task-fork restore.
    pub node_label_snapshot: super::super::process::satellites::ReapplyConceptLabelSet,
    /// SOUND-BACKTRACK snapshot of `node`'s concept PROCESSING QUEUE at push time,
    /// restored together with the label set. The two are coupled: a trigger
    /// descriptor consumed from the queue during a failed alternative may have
    /// registered its reapply entry in the (restored-away) label set; restoring the
    /// queue re-supplies that descriptor so the registration / firing is re-derived
    /// on the next alternative. Safe because concept process descriptors are
    /// arena-allocated and never reused, and an existing descriptor's intrusive
    /// `next` link is only written when the descriptor itself is (re)inserted — a
    /// push-time head therefore still addresses exactly the push-time chain.
    pub node_queue_snapshot: super::super::process::queues::ConceptProcessingQueue,
    /// `process_context.node_count()` at push — the guard: restore the snapshot
    /// only if no new node was created (i.e. the disjunct stayed on `node`).
    pub node_count_at_push: usize,
    /// What this branch point's alternatives do (disjunct add vs successor merge).
    pub kind: BranchKind,
    /// Whether THIS branch point pushed a branch epoch at push time (and so must
    /// pop it on discard / pop+re-push on advance). True for every branch point
    /// under global in-process COW; ALWAYS true for at-most merge branch points
    /// (their mutations are only undoable by epoch rollback).
    pub own_epoch: bool,
}

impl OrBranchPoint {
    /// Number of alternatives this branch point enumerates.
    pub fn alternatives_len(&self) -> usize {
        match &self.kind {
            BranchKind::Disjunction => self.disjuncts.len(),
            BranchKind::AtMostMerge(m) => m.pairs.len(),
            BranchKind::AtMostQualify { .. } => 2,
        }
    }
}

/// Port of `CCalculationTableauCompletionTaskHandleAlgorithm`.
///
/// The per-thread completion engine. This unit ports the member fields only; the
/// method bodies are deferred.
///
/// W3 method-batch: u01..u36  (the ~450 `apply*Rule` / driver / blocking / caching /
/// merging / dependency / backtracking / clash / helper methods — see
/// `manifest/01-completion-methods.md`).
pub struct CompletionTaskHandleAlgorithm {
    // --- context + databox back-refs (.h 1084–1085) ---
    /// `CCalculationAlgorithmContextBase* mCalcAlgContext`. [ownership] opaque
    /// back-handle (the Layer-7 ctx↔algo cycle).
    pub calc_alg_context: Cint64,
    /// `CProcessingDataBox* mProcessingDataBox`. [ownership] opaque alias of the
    /// context-owned databox.
    pub processing_data_box: Cint64,

    // --- cached processing queues (.h 1087–1116) ---
    pub processing_queue: Id<IndividualProcessingQueue>,
    pub nominal_processing_queue: Id<IndividualDepthProcessingQueue>,
    pub nominal_deterministic_processing_queue: Id<IndividualDepthProcessingQueue>,
    pub depth_first_processing_queue: Id<IndividualUnsortedProcessingQueue>,
    pub nominal_caching_loss_reactivation_processing_queue: Id<IndividualUnsortedProcessingQueue>,
    pub sig_block_rev_set: Id<SignatureBlockingReviewSet>,
    pub reusing_review_data: Id<ReusingReviewData>,
    pub indi_immediate_pro_queue: Id<IndividualUnsortedProcessingQueue>,
    pub indi_det_exp_pro_queue: Id<IndividualDepthProcessingQueue>,
    pub indi_det_dept_first_exp_pro_queue: Id<IndividualUnsortedProcessingQueue>,
    pub indi_block_react_pro_queue: Id<IndividualDepthProcessingQueue>,
    pub indi_sig_block_upd_pro_queue: Id<IndividualDepthProcessingQueue>,
    pub depth_processing_queue: Id<IndividualDepthProcessingQueue>,
    pub early_indi_react_processing_queue: Id<IndividualReactivationProcessingQueue>,
    pub late_indi_react_processing_queue: Id<IndividualReactivationProcessingQueue>,
    pub var_bind_con_batch_processing_queue: Id<IndividualConceptBatchProcessingQueue>,
    pub delayed_nominal_processing_queue: Id<IndividualUnsortedProcessingQueue>,
    pub role_assertion_processing_queue: Id<IndividualUnsortedProcessingQueue>,
    pub value_space_triggering_pro_queue: Id<IndividualDepthProcessingQueue>,
    pub value_space_sat_checking_queue: Id<IndividualDepthProcessingQueue>,
    pub backend_sync_retest_processing_queue: Id<IndividualUnsortedProcessingQueue>,
    pub backend_direct_influence_expansion_queue: Id<IndividualUnsortedProcessingQueue>,
    pub backend_indirect_compatibility_expansion_queue: Id<IndividualUnsortedProcessingQueue>,
    pub backend_neighbour_expansion_queue: Id<IndividualLinkerRotationProcessingQueue>,
    pub backend_late_neighbour_expansion_queue: Id<IndividualUnsortedProcessingQueue>,
    pub backend_reuse_expansion_queue: Id<IndividualUnsortedProcessingQueue>,
    pub incremental_expansion_initializing_processing_queue: Id<IndividualDepthProcessingQueue>,
    pub incremental_expansion_processing_queue: Id<IndividualCustomPriorityProcessingQueue>,
    pub incremental_compatibility_checking_queue: Id<IndividualDepthProcessingQueue>,

    /// `INDINODEQUEUETYPE mIndiNodeFromQueueType` (.h 1121).
    pub indi_node_from_queue_type: IndiNodeQueueType,

    // --- processing cursors (.h 1123–1127) ---
    pub min_concept_processing_priority_level: f64,
    pub indi_node_conclude_unsat_caching: bool,
    pub current_rec_proc_depth: Cint64,
    pub current_rec_proc_depth_limit: Cint64,

    // --- priority strategies (.h 1130–1134) ---
    pub indi_anc_depth_mas_con_proc_pri_str:
        IndividualAncestorDepthMaximumConceptProcessingPriorityStrategy,
    pub concept_priority_strategy: ConceptProcessingPriorityStrategy,
    pub individual_priority_strategy: IndividualProcessingPriorityStrategy,
    pub task_processing_strategy: TaskProcessingPriorityStrategy,

    // --- satisfiable-task message analysers (by value, .h 1136–1143) ---
    pub sat_task_cons_analyser: SatisfiableTaskConsistencyPreyingAnalyser,
    pub sat_task_inc_cons_analyser: SatisfiableTaskIncrementalConsistencyPreyingAnalyser,
    pub class_mess_analyser: SatisfiableTaskClassificationMessageAnalyser,
    pub marker_prop_real_mess_analyser: SatisfiableTaskMarkerIndividualPropagationAnalyser,
    pub poss_ass_coll_analyser: SatisfiableTaskPossibleAssertionCollectingAnalyser,
    pub sat_task_prop_class_analyser: SatisfiableTaskPropertyClassificationMessageAnalyser,
    pub sat_task_comp_answer_analyser: SatisfiableTaskComplexAnsweringMessageAnalyser,
    pub sat_task_prop_binding_answer_analyser:
        SatisfiableTaskPropagationBindingAnsweringMessageAnalyser,

    // --- factories / cache handlers (.h 1146–1160) ---
    pub clash_des_factory: Id<ClashDescriptorFactory>,
    pub dependency_factory: Id<DependencyFactory>,
    pub indi_node_manager: Id<IndividualNodeManager>,
    pub unsat_cache_handler: Id<UnsatisfiableCacheHandler>,
    pub sat_exp_cache_handler: Id<SatisfiableExpanderCacheHandler>,
    pub comp_graph_cache_handler: Id<CompletionGraphCacheHandler>,
    pub reuse_comp_graph_cache_handler: Id<ReuseCompletionGraphCacheHandler>,
    pub grounding_handler: Id<ConceptNominalSchemaGroundingHandler>,
    pub unsat_cach_ret_strategy: UnsatisfiableCacheRetrievalStrategy,
    pub sat_node_exp_cache_handler: Id<SaturationNodeExpansionCacheHandler>,
    pub datatype_handler: Id<DatatypeIndividualProcessNodeHandler>,
    pub comp_cons_cache_handler: Id<ComputedConsequencesCacheHandler>,
    pub backend_cache_handler: Id<IndividualNodeBackendCacheHandler>,
    pub inc_exp_handler: Id<IncrementalCompletionGraphCompatibleExpansionHandler>,
    pub occ_stats_cache_handler: Id<OccurrenceStatisticsCacheHandler>,

    // --- last unsat-cache-tested node (.h 1162–1163) ---
    pub last_unsat_cache_tested_indi_node: NodeId,
    pub last_unsat_cache_tested_indi_node_concept_set_size: Cint64,

    // --- rule jump tables (.h 1166–1170) ---
    /// `TableauRuleFunction* mPosJumpFuncVec`. [pointer-alias] opaque (points into
    /// `pos_tableau_rule_jump_func_vec`).
    pub pos_jump_func_vec: Cint64,
    /// `TableauRuleFunction* mNegJumpFuncVec`.
    pub neg_jump_func_vec: Cint64,
    pub pos_tableau_rule_jump_func_vec: [TableauRuleFunction; RULE_FUNC_COUNT],
    pub neg_tableau_rule_jump_func_vec: [TableauRuleFunction; RULE_FUNC_COUNT],

    // --- incremental-expansion options (.h 1172–1177) ---
    pub opt_incremental_expansion: bool,
    pub opt_incremental_compatible_expansion: bool,
    pub opt_incremental_caching_expansion: bool,
    pub opt_incremental_deterministic_expansion: bool,
    pub opt_incremental_nondeterministic_expansion: bool,

    // --- blocking / branching config flags (.h 1179–1202) ---
    pub conf_ancestor_blocking_search: bool,
    pub conf_anywhere_blocking_search: bool,
    pub conf_save_core_blocking_concepts_candidates: bool,
    pub conf_anywhere_blocking_linked_candidate_hash_search: bool,
    pub conf_anywhere_blocking_candidate_hash_search: bool,
    pub conf_anywhere_blocking_lazy_exact_hashing: bool,
    pub conf_anywhere_blocking_some_initialization_hashing: bool,
    pub conf_sub_set_blocking: bool,
    pub conf_optimized_sub_set_blocking: bool,
    pub conf_equal_set_blocking: bool,
    pub conf_pairwise_equal_set_blocking: bool,
    pub conf_specialized_automate_rules: bool,
    pub conf_semantic_branching: bool,
    pub conf_atomic_semantic_branching: bool,
    pub conf_branch_triggering: bool,
    pub conf_strict_indi_node_processing: bool,
    pub conf_id_indi_priorization: bool,
    pub conf_propagate_node_processed: bool,
    pub conf_direct_rule_preprocessing: bool,
    pub conf_lazy_new_nominal_generation: bool,
    pub conf_cons_restricted_non_strict_indi_node_processing: bool,
    pub conf_unique_name_assumption: bool,
    pub conf_pairwise_merging: bool,
    pub conf_representative_propagation_rules: bool,

    // --- dependency / backtracking config (.h 1205–1216) ---
    pub conf_build_all_branching_nodes: bool,
    pub conf_build_dependencies: bool,
    pub conf_dependency_backtracking: bool,
    pub conf_dependency_backjumping: bool,
    /// In-process COW branch epochs (see `push_branch_epoch`): every OR
    /// alternative runs under an arena journal + databox snapshot, so a
    /// backtrack restores the COMPLETE graph state (multi-node, queues,
    /// blocking data). Replaces the single-node label snapshot when on.
    pub conf_inprocess_cow: bool,
    pub conf_write_unsat_caching: bool,
    pub conf_test_occur_unsat_cached: bool,
    pub conf_test_precheck_unsat_cached: bool,
    pub conf_minimize_merging: bool,
    pub conf_tested_concept_write_unsat_caching: bool,
    pub conf_late_blocking_resolving: bool,

    // --- sat-exp cache config (.h 1219–1235) ---
    pub conf_sat_exp_cache_retrieval: bool,
    pub conf_sat_exp_cache_concept_expansion: bool,
    pub conf_sat_exp_cache_satisfiable_blocking: bool,
    pub conf_sat_exp_cache_writing: bool,
    pub conf_signature_mirroring_blocking: bool,
    pub conf_signature_saving: bool,
    pub opt_signature_mirroring_blocking_force_subset: bool,
    pub opt_signature_mirroring_blocking_in_blocking: bool,
    pub conf_individual_reusing_from_signature_blocking: bool,
    pub conf_sat_exp_cached_disj_absorp: bool,
    pub conf_sat_exp_cached_merg_absorp: bool,
    pub conf_sat_exp_cached_succ_absorp: bool,

    // --- unsat-caching / misc config (.h 1237–1261) ---
    pub conf_unsat_caching_use_full_node_dependency: bool,
    pub conf_unsat_caching_use_node_signature_set: bool,
    pub conf_skip_and_concepts: bool,
    pub conf_completion_graph_caching: bool,
    pub conf_ignore_blocking_completion_graph_cached_non_blocking_nodes: bool,
    pub conf_delay_completion_graph_caching_reactivation: bool,
    pub conf_individuals_backend_cache_loading: bool,
    pub conf_depth_orientated_processing: bool,
    pub conf_current_individual_queuing: bool,
    pub opt_processed_node_propagation: bool,
    pub opt_processed_cons_node_propagation: bool,
    pub opt_consistence_node_marking: bool,
    pub opt_processing_blocking_tests: bool,
    pub opt_cons_node_processing_blocking_tests: bool,
    pub opt_non_strict_indi_node_processing: bool,
    pub opt_det_exp_preporcessing: bool,
    pub conf_unsat_branch_satisfiable_caching: bool,
    pub conf_atleast_atmost_fast_clash_check: bool,

    // --- completion-graph reuse / saturation config (.h 1264–1278) ---
    pub conf_comp_graph_reuse_cache_retrieval: bool,
    pub conf_comp_graph_deterministic_reuse: bool,
    pub conf_comp_graph_non_deterministic_reuse: bool,
    pub conf_saturation_caching_with_nominals: bool,
    pub conf_exact_nominal_dependency_tracking: bool,
    pub conf_concept_unsatisfiability_saturated_testing: bool,
    pub conf_saturation_satisfiabilitiy_expansion_cache_writing: bool,
    pub conf_saturation_expansion_cache_reading: bool,
    pub conf_saturation_caching_testing_during_blocking_tests: bool,
    pub conf_saturation_concept_unsatisfiability_saturated_cache_writing: bool,
    pub conf_saturation_incomplete_expansion_from_cache: bool,
    pub conf_collect_caching_updated_blockable_indi_nodes: bool,

    // --- datatype / computed-consequences config (.h 1281–1289) ---
    pub conf_datatype_reasoning: bool,
    pub conf_cache_computed_consequences: bool,
    pub conf_add_cached_computed_consequences: bool,
    pub conf_analogous_propagation_path_blocking_with_answering_propagation_adapters: bool,
    pub opt_analogous_propagation_path_blocking: bool,

    // --- delayed backend init / backend expansion config (.h 1292–1305) ---
    pub conf_delayed_backend_initializiation: bool,
    pub opt_delayed_backend_initializiation: bool,
    pub opt_delayed_backend_initializiation_with_root_linkers: bool,
    pub conf_allow_backend_successor_expansion_blocking: bool,
    pub conf_allow_backend_neighbour_expansion_blocking: bool,
    pub conf_only_deterministic_representative_backend_individual_data_consideration: bool,
    pub conf_occurrence_statistics_collecting: bool,
    pub opt_collect_occurrence_statistics: bool,

    // --- debugging write-data flags (.h 1308–1318) ---
    pub conf_debugging_write_data: bool,
    pub conf_debugging_write_data_complation_tasks: bool,
    pub conf_debugging_write_data_only_on_satisfiability: bool,
    pub conf_debugging_write_data_for_consistency_tests: bool,
    pub conf_debugging_write_data_for_classification_tests: bool,
    pub conf_debugging_write_data_for_incremental_expansion_tests: bool,
    pub conf_debugging_write_data_for_rep_cache_indi_computation_tests: bool,
    pub conf_debugging_write_data_for_answering_propagation_tests: bool,
    pub conf_debugging_write_data_for_all_tests: bool,
    /// `bool mDebug = false`.
    pub debug: bool,
    pub backtrack_debug: bool,

    // --- branching statistics (.h 1320–1321) ---
    pub conf_branching_statistics_analysing: bool,
    pub last_analysing_branch_node_tree: BranchNodeId,

    // --- successor saturation / merge-constructed config (.h 1326–1331) ---
    pub conf_expand_created_successors_from_saturation: bool,
    pub conf_successor_saturation_expansion_restrictions_resolving: bool,
    pub conf_caching_blocking_from_saturation: bool,
    pub conf_merge_constructed_individual_node: bool,
    pub opt_merge_constructed_individual_node: bool,

    // --- backend neighbour expansion config (.h 1338–1374) ---
    pub conf_variable_binding_steering_backend_neighbour_expansion: bool,
    pub conf_backend_expansion_reuse: bool,
    pub conf_backend_expansion_limit_reached_reuse_activation: bool,
    pub conf_backend_expansion_late_dynamic_reuse_activation: bool,
    pub conf_backend_expansion_same_individual_count_reuse_activation: Cint64,
    pub conf_backend_expansion_neighbour_individual_count_reuse_activation: Cint64,
    pub conf_limit_backend_neighbour_expansion: bool,
    pub conf_all_problematic_backend_neighbour_direct_expansion: bool,
    pub conf_min_backend_neighbour_direct_expansion_count: Cint64,
    pub opt_min_backend_neighbour_direct_expansion_count: Cint64,
    pub conf_min_direct_neighbour_expansion_over_critical_reduction_size: Cint64,
    pub opt_min_direct_neighbour_expansion_over_critical_reduction_size: Cint64,
    pub conf_max_backend_neighbour_total_expansion_count: Cint64,
    pub opt_max_backend_neighbour_total_expansion_count: Cint64,
    pub conf_critical_backend_neighbour_total_expansion_count: Cint64,
    pub opt_critical_backend_neighbour_total_expansion_count: Cint64,
    pub conf_queued_backend_neighbour_expansion_indis_batch_size: Cint64,
    pub opt_queued_backend_neighbour_expansion_indis_batch_size: Cint64,
    pub conf_queued_backend_neighbour_expansion_roles_batch_count: Cint64,
    pub opt_queued_backend_neighbour_expansion_roles_batch_count: Cint64,
    pub conf_atmost_all_direct_backend_neighbour_expansion: bool,
    pub conf_default_individual_precomputation_count: Cint64,
    pub conf_neighbour_label_representative_expansion_delaying: bool,
    pub opt_neighbour_label_representative_expansion_delaying: bool,
    pub opt_limit_backend_neighbour_expansion: bool,
    pub opt_backend_expansion_reuse: bool,
    pub conf_new_mergings_only_inferring_expansion: bool,
    /// `= true` in C++.
    pub conf_expand_deterministic_merged_handled_neighbours: bool,
    /// `= false` in C++.
    pub conf_cardinality_neighbour_expansion_representative_counting: bool,

    // --- query generation + tuning (.h 1380–1396) ---
    pub conf_generate_queries: bool,
    pub max_blocking_caching_saved_candidate_count: Cint64,
    pub map_comparison_direct_lookup_factor: Cint64,
    pub last_config: Id<CalculationConfigurationExtension>,
    /// `QSet<cint64> mUnsatCachingSignatureSet`.
    pub unsat_caching_signature_set: HashSet<Cint64>,
    pub process_rule_to_task_processing_verification_count: Cint64,
    pub remain_process_rule_to_task_processing_verification: Cint64,

    // --- representative expansion stats (.h 1401–1404, `= 0`) ---
    pub stat_representative_expansion_trying_neighbour_individual_count: Cint64,
    pub stat_representative_expanded_neighbour_individual_count: Cint64,
    pub stat_representative_expansion_already_existing_neighbour_individual_count: Cint64,
    pub stat_representative_delayed_neighbour_individual_expansion_count: Cint64,

    // --- possible-instance merging config (.h 1408) ---
    pub conf_possible_instance_individuals_merging: bool,

    // --- debugging hashes / lists (.h 1416–1424) ---
    pub indi_node_init_concept_sig_count_hash: HashMap<Cint64, Cint64>,
    pub closed_branch_level_count_hash: HashMap<Cint64, Cint64>,
    pub signature_indi_node_status_hash: HashMap<Cint64, Cint64>,
    pub signature_indi_node_pred_dep_hash: HashMap<Cint64, Cint64>,
    /// `QMap<cint64,cint64>` (ordered) → `BTreeMap`.
    pub indi_node_count_map: BTreeMap<Cint64, Cint64>,
    pub indi_node_count_list: Vec<Cint64>,
    pub critical_concept_set_string_set: HashSet<String>,
    pub found_critical_concept_set: bool,

    // --- debug task-id vector + backtracking step (.h 1427–1432) ---
    pub debug_task_id_vector: [Cint64; DEBUG_TASK_ID_VECTOR_SIZE],
    pub backtracking_step: Cint64,
    pub last_jump_func: TableauRuleFunction,
    pub last_branching_merging_proc_rest: RestrictionSpecId,

    // --- debug model strings (.h 1434–1491) ---
    pub debug_indi_model_string_list: Vec<String>,
    pub debug_indi_model_string: String,
    pub begin_task_debug_indi_model_string: String,
    pub before_rule_debug_indi_model_string: String,
    pub after_rule_debug_indi_model_string: String,
    pub clashed_debug_indi_model_string: String,
    pub end_task_debug_indi_model_string: String,
    pub inc_exp_comp_indi_model_string: String,
    pub inc_exp_merged_indi_model_string: String,
    pub before_merging_task_debug_indi_model_string: String,
    pub after_merging_task_debug_indi_model_string: String,
    pub merged_string_list: Vec<String>,
    pub sat_task_debug_indi_model_string: String,
    pub before_rule_task_debug_indi_model_string: String,
    pub begin_backtracking_clash_string: String,
    pub begin_backtracking_trackline_string: String,
    pub end_backtracking_trackline_string: String,
    pub file_backtracking_step_trackline_string: String,
    pub begin_backtracking_step_trackline_string: String,
    pub end_backtracking_step_trackline_string: String,
    pub begin_det_prev_backtracking_step_trackline_string: String,
    pub end_det_prev_backtracking_step_trackline_string: String,
    pub begin_non_det_prev_backtracking_step_trackline_string: String,
    pub end_non_det_prev_backtracking_step_trackline_string: String,
    pub non_det_dependency_track_point_reason_string: String,
    pub non_det_dependency_before_processed_tracked_string: String,
    pub non_det_dependency_collected_tracked_string: String,
    pub merging_clash_string: String,
    pub caching_clash_string: String,
    pub sorted_caching_clash_string: String,
    pub merging_queue_string: String,
    pub branch_level_closed_count_string: String,
    pub before_grounding_debug_indi_model_string: String,
    pub after_grounding_debug_indi_model_string: String,
    pub analogous_propagation_blocking_testing_indi_associated_concepts_string: String,
    pub analogous_propagation_blocking_blocking_indi_associated_concepts_string: String,
    pub analogous_propagation_blocking_testing_indi_all_associated_concepts_string: String,
    pub analogous_propagation_blocking_blocking_indi_all_associated_concepts_string: String,

    // --- applied-rule counters (.h 1495–1501) ---
    pub applied_all_rule_count: Cint64,
    pub applied_some_rule_count: Cint64,
    pub applied_and_rule_count: Cint64,
    pub applied_or_rule_count: Cint64,
    pub applied_atleast_rule_count: Cint64,
    pub applied_atmost_rule_count: Cint64,
    pub applied_total_rule_count: Cint64,

    /// KM-BRIDGE: singleton concepts — any two distinct nodes positively
    /// carrying one are the SAME individual (the bridge's realisation of the
    /// clausal datatype value-identity `C(x) ∧ C(y) → x = y`; Konclude gets
    /// this identity natively from its databox literal handling, the clausal
    /// frontend surfaces it as a role-free eq-head clause). Consumed by the
    /// deterministic scan-at-fixpoint merge in `run_saturation_loop` (u02).
    /// Tiny (the distinct literal VALUES a counting constraint compares);
    /// empty on ontologies without such clauses — the rule is then inert.
    pub singleton_concepts: Vec<ConceptId>,
    pub applied_singleton_merge_count: Cint64,
    /// Node-arena index intervals `[at_push, at_pop)` created by REFUTED
    /// alternatives that were advanced/discarded WITHOUT a complete restore
    /// (no in-process COW): chronological backtracking leaves those nodes in
    /// the arena as PHANTOMS — dead state no longer part of the current
    /// branch. The global singleton scan must skip them (merging a live
    /// carrier with a phantom entangles live labels with clash-laden dead
    /// ones → spurious unsat). Under COW the epochs truncate the arenas, so
    /// no intervals are recorded (indices are reused — an interval would be
    /// wrong). Never cleared within a drive: a phantom stays a phantom.
    pub phantom_node_intervals: Vec<(usize, usize)>,

    // --- variable-binding stats (.h 1504–1513) ---
    pub stat_var_binding_created_count: Cint64,
    pub stat_var_binding_grounding_count: Cint64,
    pub stat_var_binding_implication_count: Cint64,
    pub stat_var_binding_join_combines_count: Cint64,
    pub stat_var_binding_propagate_succ_count: Cint64,
    pub stat_var_binding_propagate_succ_fresh_count: Cint64,
    pub stat_var_binding_propagate_succ_initial_count: Cint64,
    pub stat_var_binding_propagate_count: Cint64,
    pub stat_var_binding_propagate_fresh_count: Cint64,
    pub stat_var_binding_propagate_initial_count: Cint64,

    // --- representative stats (.h 1516–1529) ---
    pub stat_representative_created_count: Cint64,
    pub stat_representative_grounding_count: Cint64,
    pub stat_representative_implication_count: Cint64,
    pub stat_representative_join_combines_count: Cint64,
    pub stat_representative_join_count: Cint64,
    pub stat_representative_joined_count: Cint64,
    pub stat_representative_join_quick_fail_count: Cint64,
    pub stat_representative_propagate_succ_count: Cint64,
    pub stat_representative_propagate_count: Cint64,
    pub stat_representative_propagate_new_representative_count: Cint64,
    pub stat_representative_propagate_reused_representative_count: Cint64,
    pub stat_representative_propagate_use_representative_count: Cint64,
    pub stat_back_prop_activation_count: Cint64,

    // --- concept-descriptor + possible-instance stats (.h 1532–1548) ---
    pub stat_con_des_insertion_count: Cint64,
    pub stat_con_des_contained_count: Cint64,
    pub stat_possible_instance_merging_trying_count: Cint64,
    pub stat_possible_instance_merging_count: Cint64,
    pub stat_possible_instance_merging_search_indi_count: Cint64,
    pub stat_possible_instance_merging_found_indi_count: Cint64,
    pub stat_possible_instance_merging_skip_indi_count: Cint64,
    pub stat_possible_instance_merging_not_mergeable_count: Cint64,
    pub stat_possible_instance_merging_maybe_mergeable_count: Cint64,
    pub stat_possible_instance_merging_success_submit_count: Cint64,
    pub stat_possible_instance_merging_trivially_success_count: Cint64,
    pub stat_clash_count: Cint64,
    pub stat_satisfiable_count: Cint64,
    pub stat_stopped_count: Cint64,

    // --- timers (.h 1551–1553) ---
    /// `QTime mTimerBacktracing`. KONCLUDE-PORT-NOTE[api]: Qt wall-clock timer →
    /// opaque `Cint64` placeholder until a timing facility is ported.
    pub timer_backtracing: Cint64,
    pub unsat_cache_retrieval: Cint64,
    pub compl_graph_reuse_cache_retrieval: Cint64,

    // --- nominal-merge + decision stats (.h 1556–1560) ---
    pub nominal_merged: bool,
    pub nominal_merged_count: Cint64,
    pub over_jumped_non_deterministic_decision_count: Cint64,
    pub relevant_non_deterministic_decision_count: Cint64,

    // --- cached associated-concept-set hash (.h 1569) ---
    pub cached_indi_associated_concept_set_hash: HashMap<NodeId, IndiAssociatedConceptSetCacheData>,

    // --- first-write debug flags (.h 1572–1573, `= false`) ---
    pub first_blocking_test_debug_written: bool,
    pub first_binding_creation_debug_written: bool,

    // --- prop-cut id sets (.h 1577–1578) ---
    pub prop_cutted_indi_ids: HashSet<Cint64>,
    pub prop_cutted_expanded_indi_ids: HashSet<Cint64>,

    // --- reporting tuning (.h 1582–1585, initialized) ---
    /// `= 1000`.
    pub next_reporting_expansion_count: Cint64,
    /// `= 0`.
    pub last_recomputation_task_id: Cint64,
    /// `= 100`.
    pub last_task_depth: Cint64,
    /// `= 500`.
    pub debug_expansion_count: Cint64,

    /// The in-process disjunction search stack (see [`OrBranchPoint`]). Empty in the
    /// faithful (task-fork) model; populated by the chronological-branching port the
    /// drive loop (u02) + `initialize_or_processing` (u03) install.
    pub or_branch_stack: Vec<OrBranchPoint>,
    /// Monotone counter of disjunction backtracks (`try_backtrack_or_branch`
    /// advancing to a next alternative OR popping an exhausted branch point). An
    /// outer re-drive loop that re-applies global constraints (GCI re-seeding) must
    /// NOT conclude fixpoint on a pass in which this advanced: the backtrack restore
    /// wipes queued-but-independent work (e.g. re-seeded implication descriptors)
    /// that only the next re-seed pass re-derives, and a swapped disjunct keeps the
    /// label-set concept COUNT stable even though the label changed.
    pub or_backtrack_count: u64,
    /// Count of OR branch points OPENED (pushed). A drive with
    /// `or_branch_open_count` unchanged made NO nondeterministic choice, so a
    /// model read-off is authoritative. `or_backtrack_count` alone is NOT a
    /// determinism witness: a drive can open branch points and commit to first
    /// disjuncts without ever clashing — concepts added under those choices
    /// are branch-dependent (Konclude gates the same read-off on the
    /// dependency track point's branching tag, cpp 4121; the in-process OR
    /// adds disjuncts under the OR concept's own track point, so the tag is
    /// not observable downstream and the open-count stands in).
    pub or_branch_open_count: u64,
    /// Set by `cancellation_root_task` (u32): the tracked-clash analysis
    /// (`clashedBacktracking`, u29) traced a clash to branching level 0 — the
    /// clash is independent of every open disjunction alternative, so the
    /// whole problem is unsatisfiable regardless of remaining branches. The
    /// in-process drive loop (u02) reads this as its stand-in for Konclude's
    /// root-task cancellation (the Task-subsystem side of `cancellationTask`
    /// is W6-DEFER). Reset at the top of `run_completion_on`.
    pub ddb_root_cancelled: bool,
    /// Wall-clock deadline for the drive loop (`run_completion_on`): on
    /// overrun the drive raises a STOP (an UNKNOWN verdict — callers DEFER).
    /// Set per-probe by `bridged_unsat` from `KM_BRIDGE_PROBE_BUDGET_S`; the
    /// between-passes budget check alone cannot bound a single search (one
    /// `run_completion_on` call owns the whole backtracking loop — measured:
    /// a 5 s budget probe ran 10+ min to 117 GB before the pass check).
    pub drive_deadline: Option<std::time::Instant>,
    /// DDB diagnostics: analyses aborted at tracking-line initialization
    /// (error-flagged closures — the fallback precursor).
    pub ddb_line_init_fail_count: u64,
    /// DDB diagnostics: analyses that reached an ALREADY-MARKED nondet track
    /// point and early-returned without a new mark (stale-mark thrash).
    pub ddb_already_marked_count: u64,
    /// DDB diagnostics: refuted-and-exhausted decisions discarded (with their
    /// stacked subtrees) by the backjump scan.
    pub ddb_refuted_discard_count: u64,
    /// KM_BRIDGE_SEARCH_LOG budget counter.
    pub search_log_count: u64,
    /// DDB diagnostics: backjumps taken (target found by the scan).
    pub ddb_jump_count: u64,
    /// DDB diagnostics: branch points POPPED PAST by backjumps (jump distance
    /// beyond the plain advance; 0 for a topmost-target jump — the
    /// chronological-equivalent case).
    pub ddb_jump_pop_total: u64,
    /// DDB diagnostics: clashes where the analysis marked NO open branch
    /// point (chronological fallback taken).
    pub ddb_fallback_count: u64,
    /// DDB diagnostics: `set_clashes` markings performed by the analysis.
    pub ddb_mark_count: u64,
    /// Advances where the snapshot restore was SKIPPED (successor nodes were
    /// created since the push, so the single-node snapshot cannot restore the
    /// graph). While this is non-zero the labels may carry branch-dependent
    /// leftovers, so the DDB pop-unmarked backjump is DISABLED (a clash
    /// involving leftovers would implicate stale track points and the
    /// level-ordering argument no longer covers the open branch points).
    /// Root-level cancellation stays trustworthy: a leftover descriptor
    /// carries its ORIGINAL non-deterministic tag, so it cannot appear in a
    /// branching-level-0 closure.
    pub unrestored_advance_count: u64,
    /// DDB diagnostics: clash-closure dumps emitted so far (first few
    /// analyses under KM_BRIDGE_PROGRESS).
    pub ddb_analysis_dumps: u64,
    /// KM_BRIDGE_DUMP_CLASH: line budget for the per-walk DDB-DISCARD-LIVE
    /// dump (task #12 — which live alternatives the mark-driven walk drops).
    pub ddb_discard_dump_lines: u64,
    /// KM_BRIDGE_DUMP_DEP_CHAIN: how many live-discarding walks already got
    /// a driving-clash dependency-chain dump.
    pub ddb_walk_chain_dumps: u64,
}

impl CompletionTaskHandleAlgorithm {
    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm` construction.
    ///
    /// KONCLUDE-PORT-NOTE[uninit]: the C++ ctor leaves most fields uninitialised
    /// (set by `initTaskCalculation`/`initCalculationConfiguration`); only the
    /// fields with inline `= ...` initialisers seed a value. The port mirrors that:
    /// inline-initialised fields take their literal, every other handle starts
    /// `INVALID`/`Id::NONE`, counters `0`, flags `false`, collections empty.
    pub fn new() -> Self {
        CompletionTaskHandleAlgorithm {
            calc_alg_context: INVALID,
            processing_data_box: INVALID,

            processing_queue: Id::NONE,
            nominal_processing_queue: Id::NONE,
            nominal_deterministic_processing_queue: Id::NONE,
            depth_first_processing_queue: Id::NONE,
            nominal_caching_loss_reactivation_processing_queue: Id::NONE,
            sig_block_rev_set: Id::NONE,
            reusing_review_data: Id::NONE,
            indi_immediate_pro_queue: Id::NONE,
            indi_det_exp_pro_queue: Id::NONE,
            indi_det_dept_first_exp_pro_queue: Id::NONE,
            indi_block_react_pro_queue: Id::NONE,
            indi_sig_block_upd_pro_queue: Id::NONE,
            depth_processing_queue: Id::NONE,
            early_indi_react_processing_queue: Id::NONE,
            late_indi_react_processing_queue: Id::NONE,
            var_bind_con_batch_processing_queue: Id::NONE,
            delayed_nominal_processing_queue: Id::NONE,
            role_assertion_processing_queue: Id::NONE,
            value_space_triggering_pro_queue: Id::NONE,
            value_space_sat_checking_queue: Id::NONE,
            backend_sync_retest_processing_queue: Id::NONE,
            backend_direct_influence_expansion_queue: Id::NONE,
            backend_indirect_compatibility_expansion_queue: Id::NONE,
            backend_neighbour_expansion_queue: Id::NONE,
            backend_late_neighbour_expansion_queue: Id::NONE,
            backend_reuse_expansion_queue: Id::NONE,
            incremental_expansion_initializing_processing_queue: Id::NONE,
            incremental_expansion_processing_queue: Id::NONE,
            incremental_compatibility_checking_queue: Id::NONE,

            indi_node_from_queue_type: IndiNodeQueueType::Inqt_None,

            min_concept_processing_priority_level: 0.0,
            indi_node_conclude_unsat_caching: false,
            current_rec_proc_depth: 0,
            current_rec_proc_depth_limit: 0,

            indi_anc_depth_mas_con_proc_pri_str:
                IndividualAncestorDepthMaximumConceptProcessingPriorityStrategy::new(),
            concept_priority_strategy: ConceptProcessingPriorityStrategy::new_concrete_operator(),
            individual_priority_strategy:
                IndividualProcessingPriorityStrategy::new_ancestor_depth_maximum(),
            task_processing_strategy:
                TaskProcessingPriorityStrategy::new_equal_depth_cache_orientated(),

            sat_task_cons_analyser: Default::default(),
            sat_task_inc_cons_analyser: Default::default(),
            class_mess_analyser: Default::default(),
            marker_prop_real_mess_analyser: Default::default(),
            poss_ass_coll_analyser: Default::default(),
            sat_task_prop_class_analyser: Default::default(),
            sat_task_comp_answer_analyser: Default::default(),
            sat_task_prop_binding_answer_analyser: Default::default(),

            clash_des_factory: Id::NONE,
            dependency_factory: Id::NONE,
            indi_node_manager: Id::NONE,
            unsat_cache_handler: Id::NONE,
            sat_exp_cache_handler: Id::NONE,
            comp_graph_cache_handler: Id::NONE,
            reuse_comp_graph_cache_handler: Id::NONE,
            grounding_handler: Id::NONE,
            unsat_cach_ret_strategy:
                UnsatisfiableCacheRetrievalStrategy::new_generative_non_deterministic(),
            sat_node_exp_cache_handler: Id::NONE,
            datatype_handler: Id::NONE,
            comp_cons_cache_handler: Id::NONE,
            backend_cache_handler: Id::NONE,
            inc_exp_handler: Id::NONE,
            occ_stats_cache_handler: Id::NONE,

            last_unsat_cache_tested_indi_node: Id::NONE,
            last_unsat_cache_tested_indi_node_concept_set_size: 0,

            pos_jump_func_vec: INVALID,
            neg_jump_func_vec: INVALID,
            pos_tableau_rule_jump_func_vec: [INVALID; RULE_FUNC_COUNT],
            neg_tableau_rule_jump_func_vec: [INVALID; RULE_FUNC_COUNT],

            opt_incremental_expansion: false,
            opt_incremental_compatible_expansion: false,
            opt_incremental_caching_expansion: false,
            opt_incremental_deterministic_expansion: false,
            opt_incremental_nondeterministic_expansion: false,

            conf_ancestor_blocking_search: false,
            conf_anywhere_blocking_search: false,
            conf_save_core_blocking_concepts_candidates: false,
            conf_anywhere_blocking_linked_candidate_hash_search: false,
            conf_anywhere_blocking_candidate_hash_search: false,
            conf_anywhere_blocking_lazy_exact_hashing: false,
            conf_anywhere_blocking_some_initialization_hashing: false,
            conf_sub_set_blocking: false,
            conf_optimized_sub_set_blocking: false,
            conf_equal_set_blocking: false,
            conf_pairwise_equal_set_blocking: false,
            conf_specialized_automate_rules: false,
            conf_semantic_branching: false,
            conf_atomic_semantic_branching: false,
            conf_branch_triggering: false,
            conf_strict_indi_node_processing: false,
            conf_id_indi_priorization: false,
            conf_propagate_node_processed: false,
            conf_direct_rule_preprocessing: false,
            conf_lazy_new_nominal_generation: false,
            conf_cons_restricted_non_strict_indi_node_processing: false,
            conf_unique_name_assumption: false,
            conf_pairwise_merging: false,
            conf_representative_propagation_rules: false,

            conf_build_all_branching_nodes: false,
            conf_build_dependencies: false,
            conf_dependency_backtracking: false,
            conf_dependency_backjumping: false,
            conf_inprocess_cow: false,
            conf_write_unsat_caching: false,
            conf_test_occur_unsat_cached: false,
            conf_test_precheck_unsat_cached: false,
            conf_minimize_merging: false,
            conf_tested_concept_write_unsat_caching: false,
            conf_late_blocking_resolving: false,

            conf_sat_exp_cache_retrieval: false,
            conf_sat_exp_cache_concept_expansion: false,
            conf_sat_exp_cache_satisfiable_blocking: false,
            conf_sat_exp_cache_writing: false,
            conf_signature_mirroring_blocking: false,
            conf_signature_saving: false,
            opt_signature_mirroring_blocking_force_subset: false,
            opt_signature_mirroring_blocking_in_blocking: false,
            conf_individual_reusing_from_signature_blocking: false,
            conf_sat_exp_cached_disj_absorp: false,
            conf_sat_exp_cached_merg_absorp: false,
            conf_sat_exp_cached_succ_absorp: false,

            conf_unsat_caching_use_full_node_dependency: false,
            conf_unsat_caching_use_node_signature_set: false,
            conf_skip_and_concepts: false,
            conf_completion_graph_caching: false,
            conf_ignore_blocking_completion_graph_cached_non_blocking_nodes: false,
            conf_delay_completion_graph_caching_reactivation: false,
            conf_individuals_backend_cache_loading: false,
            conf_depth_orientated_processing: false,
            conf_current_individual_queuing: false,
            opt_processed_node_propagation: false,
            opt_processed_cons_node_propagation: false,
            opt_consistence_node_marking: false,
            opt_processing_blocking_tests: false,
            opt_cons_node_processing_blocking_tests: false,
            opt_non_strict_indi_node_processing: false,
            opt_det_exp_preporcessing: false,
            conf_unsat_branch_satisfiable_caching: false,
            conf_atleast_atmost_fast_clash_check: false,

            conf_comp_graph_reuse_cache_retrieval: false,
            conf_comp_graph_deterministic_reuse: false,
            conf_comp_graph_non_deterministic_reuse: false,
            conf_saturation_caching_with_nominals: false,
            conf_exact_nominal_dependency_tracking: false,
            conf_concept_unsatisfiability_saturated_testing: false,
            conf_saturation_satisfiabilitiy_expansion_cache_writing: false,
            conf_saturation_expansion_cache_reading: false,
            conf_saturation_caching_testing_during_blocking_tests: false,
            conf_saturation_concept_unsatisfiability_saturated_cache_writing: false,
            conf_saturation_incomplete_expansion_from_cache: false,
            conf_collect_caching_updated_blockable_indi_nodes: false,

            conf_datatype_reasoning: false,
            conf_cache_computed_consequences: false,
            conf_add_cached_computed_consequences: false,
            conf_analogous_propagation_path_blocking_with_answering_propagation_adapters: false,
            opt_analogous_propagation_path_blocking: false,

            conf_delayed_backend_initializiation: false,
            opt_delayed_backend_initializiation: false,
            opt_delayed_backend_initializiation_with_root_linkers: false,
            conf_allow_backend_successor_expansion_blocking: false,
            conf_allow_backend_neighbour_expansion_blocking: false,
            conf_only_deterministic_representative_backend_individual_data_consideration: false,
            conf_occurrence_statistics_collecting: false,
            opt_collect_occurrence_statistics: false,

            conf_debugging_write_data: false,
            conf_debugging_write_data_complation_tasks: false,
            conf_debugging_write_data_only_on_satisfiability: false,
            conf_debugging_write_data_for_consistency_tests: false,
            conf_debugging_write_data_for_classification_tests: false,
            conf_debugging_write_data_for_incremental_expansion_tests: false,
            conf_debugging_write_data_for_rep_cache_indi_computation_tests: false,
            conf_debugging_write_data_for_answering_propagation_tests: false,
            conf_debugging_write_data_for_all_tests: false,
            debug: false,
            backtrack_debug: false,

            conf_branching_statistics_analysing: false,
            last_analysing_branch_node_tree: Id::NONE,

            conf_expand_created_successors_from_saturation: false,
            conf_successor_saturation_expansion_restrictions_resolving: false,
            conf_caching_blocking_from_saturation: false,
            conf_merge_constructed_individual_node: false,
            opt_merge_constructed_individual_node: false,

            conf_variable_binding_steering_backend_neighbour_expansion: false,
            conf_backend_expansion_reuse: false,
            conf_backend_expansion_limit_reached_reuse_activation: false,
            conf_backend_expansion_late_dynamic_reuse_activation: false,
            conf_backend_expansion_same_individual_count_reuse_activation: 0,
            conf_backend_expansion_neighbour_individual_count_reuse_activation: 0,
            conf_limit_backend_neighbour_expansion: false,
            conf_all_problematic_backend_neighbour_direct_expansion: false,
            conf_min_backend_neighbour_direct_expansion_count: 0,
            opt_min_backend_neighbour_direct_expansion_count: 0,
            conf_min_direct_neighbour_expansion_over_critical_reduction_size: 0,
            opt_min_direct_neighbour_expansion_over_critical_reduction_size: 0,
            conf_max_backend_neighbour_total_expansion_count: 0,
            opt_max_backend_neighbour_total_expansion_count: 0,
            conf_critical_backend_neighbour_total_expansion_count: 0,
            opt_critical_backend_neighbour_total_expansion_count: 0,
            conf_queued_backend_neighbour_expansion_indis_batch_size: 0,
            opt_queued_backend_neighbour_expansion_indis_batch_size: 0,
            conf_queued_backend_neighbour_expansion_roles_batch_count: 0,
            opt_queued_backend_neighbour_expansion_roles_batch_count: 0,
            conf_atmost_all_direct_backend_neighbour_expansion: false,
            conf_default_individual_precomputation_count: 0,
            conf_neighbour_label_representative_expansion_delaying: false,
            opt_neighbour_label_representative_expansion_delaying: false,
            opt_limit_backend_neighbour_expansion: false,
            opt_backend_expansion_reuse: false,
            conf_new_mergings_only_inferring_expansion: false,
            conf_expand_deterministic_merged_handled_neighbours: true,
            conf_cardinality_neighbour_expansion_representative_counting: false,

            conf_generate_queries: false,
            max_blocking_caching_saved_candidate_count: 0,
            map_comparison_direct_lookup_factor: 20,
            last_config: Id::NONE,
            unsat_caching_signature_set: HashSet::new(),
            process_rule_to_task_processing_verification_count: 0,
            remain_process_rule_to_task_processing_verification: 0,

            stat_representative_expansion_trying_neighbour_individual_count: 0,
            stat_representative_expanded_neighbour_individual_count: 0,
            stat_representative_expansion_already_existing_neighbour_individual_count: 0,
            stat_representative_delayed_neighbour_individual_expansion_count: 0,

            conf_possible_instance_individuals_merging: false,

            indi_node_init_concept_sig_count_hash: HashMap::new(),
            closed_branch_level_count_hash: HashMap::new(),
            signature_indi_node_status_hash: HashMap::new(),
            signature_indi_node_pred_dep_hash: HashMap::new(),
            indi_node_count_map: BTreeMap::new(),
            indi_node_count_list: Vec::new(),
            critical_concept_set_string_set: HashSet::new(),
            found_critical_concept_set: false,

            debug_task_id_vector: [0; DEBUG_TASK_ID_VECTOR_SIZE],
            backtracking_step: 0,
            last_jump_func: INVALID,
            last_branching_merging_proc_rest: Id::NONE,

            debug_indi_model_string_list: Vec::new(),
            debug_indi_model_string: String::new(),
            begin_task_debug_indi_model_string: String::new(),
            before_rule_debug_indi_model_string: String::new(),
            after_rule_debug_indi_model_string: String::new(),
            clashed_debug_indi_model_string: String::new(),
            end_task_debug_indi_model_string: String::new(),
            inc_exp_comp_indi_model_string: String::new(),
            inc_exp_merged_indi_model_string: String::new(),
            before_merging_task_debug_indi_model_string: String::new(),
            after_merging_task_debug_indi_model_string: String::new(),
            merged_string_list: Vec::new(),
            sat_task_debug_indi_model_string: String::new(),
            before_rule_task_debug_indi_model_string: String::new(),
            begin_backtracking_clash_string: String::new(),
            begin_backtracking_trackline_string: String::new(),
            end_backtracking_trackline_string: String::new(),
            file_backtracking_step_trackline_string: String::new(),
            begin_backtracking_step_trackline_string: String::new(),
            end_backtracking_step_trackline_string: String::new(),
            begin_det_prev_backtracking_step_trackline_string: String::new(),
            end_det_prev_backtracking_step_trackline_string: String::new(),
            begin_non_det_prev_backtracking_step_trackline_string: String::new(),
            end_non_det_prev_backtracking_step_trackline_string: String::new(),
            non_det_dependency_track_point_reason_string: String::new(),
            non_det_dependency_before_processed_tracked_string: String::new(),
            non_det_dependency_collected_tracked_string: String::new(),
            merging_clash_string: String::new(),
            caching_clash_string: String::new(),
            sorted_caching_clash_string: String::new(),
            merging_queue_string: String::new(),
            branch_level_closed_count_string: String::new(),
            before_grounding_debug_indi_model_string: String::new(),
            after_grounding_debug_indi_model_string: String::new(),
            analogous_propagation_blocking_testing_indi_associated_concepts_string: String::new(),
            analogous_propagation_blocking_blocking_indi_associated_concepts_string: String::new(),
            analogous_propagation_blocking_testing_indi_all_associated_concepts_string: String::new(
            ),
            analogous_propagation_blocking_blocking_indi_all_associated_concepts_string:
                String::new(),

            applied_all_rule_count: 0,
            applied_some_rule_count: 0,
            applied_and_rule_count: 0,
            applied_or_rule_count: 0,
            applied_atleast_rule_count: 0,
            applied_atmost_rule_count: 0,
            applied_total_rule_count: 0,

            singleton_concepts: Vec::new(),
            applied_singleton_merge_count: 0,
            phantom_node_intervals: Vec::new(),

            stat_var_binding_created_count: 0,
            stat_var_binding_grounding_count: 0,
            stat_var_binding_implication_count: 0,
            stat_var_binding_join_combines_count: 0,
            stat_var_binding_propagate_succ_count: 0,
            stat_var_binding_propagate_succ_fresh_count: 0,
            stat_var_binding_propagate_succ_initial_count: 0,
            stat_var_binding_propagate_count: 0,
            stat_var_binding_propagate_fresh_count: 0,
            stat_var_binding_propagate_initial_count: 0,

            stat_representative_created_count: 0,
            stat_representative_grounding_count: 0,
            stat_representative_implication_count: 0,
            stat_representative_join_combines_count: 0,
            stat_representative_join_count: 0,
            stat_representative_joined_count: 0,
            stat_representative_join_quick_fail_count: 0,
            stat_representative_propagate_succ_count: 0,
            stat_representative_propagate_count: 0,
            stat_representative_propagate_new_representative_count: 0,
            stat_representative_propagate_reused_representative_count: 0,
            stat_representative_propagate_use_representative_count: 0,
            stat_back_prop_activation_count: 0,

            stat_con_des_insertion_count: 0,
            stat_con_des_contained_count: 0,
            stat_possible_instance_merging_trying_count: 0,
            stat_possible_instance_merging_count: 0,
            stat_possible_instance_merging_search_indi_count: 0,
            stat_possible_instance_merging_found_indi_count: 0,
            stat_possible_instance_merging_skip_indi_count: 0,
            stat_possible_instance_merging_not_mergeable_count: 0,
            stat_possible_instance_merging_maybe_mergeable_count: 0,
            stat_possible_instance_merging_success_submit_count: 0,
            stat_possible_instance_merging_trivially_success_count: 0,
            stat_clash_count: 0,
            stat_satisfiable_count: 0,
            stat_stopped_count: 0,

            timer_backtracing: 0,
            unsat_cache_retrieval: 0,
            compl_graph_reuse_cache_retrieval: 0,

            nominal_merged: false,
            nominal_merged_count: 0,
            over_jumped_non_deterministic_decision_count: 0,
            relevant_non_deterministic_decision_count: 0,

            cached_indi_associated_concept_set_hash: HashMap::new(),

            first_blocking_test_debug_written: false,
            first_binding_creation_debug_written: false,

            prop_cutted_indi_ids: HashSet::new(),
            prop_cutted_expanded_indi_ids: HashSet::new(),

            next_reporting_expansion_count: 1000,
            last_recomputation_task_id: 0,
            last_task_depth: 100,
            debug_expansion_count: 500,

            or_branch_stack: Vec::new(),
            or_backtrack_count: 0,
            or_branch_open_count: 0,
            ddb_root_cancelled: false,
            drive_deadline: None,
            ddb_line_init_fail_count: 0,
            ddb_already_marked_count: 0,
            ddb_refuted_discard_count: 0,
            search_log_count: 0,
            ddb_jump_count: 0,
            ddb_jump_pop_total: 0,
            ddb_fallback_count: 0,
            ddb_mark_count: 0,
            ddb_analysis_dumps: 0,
            ddb_discard_dump_lines: 0,
            ddb_walk_chain_dumps: 0,
            unrestored_advance_count: 0,
        }
    }

    // ----------------------------------------------------------------------
    // Simple accessors. Every stateful method (the driver loop, the apply*Rule
    // engine, blocking/caching/merging, dependency tracking, backtracking, clash
    // processing, helpers) is deferred to the W3 method-batch units u01..u36
    // (see manifest/01-completion-methods.md).
    //
    // W3 method-batch: u01..u36
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

impl Default for CompletionTaskHandleAlgorithm {
    fn default() -> Self {
        Self::new()
    }
}
