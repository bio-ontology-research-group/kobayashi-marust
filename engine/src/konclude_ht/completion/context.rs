//! `completion::context` — the per-thread algorithm context.
//!
//! Ports Konclude `Source/Reasoner/Kernel/Algorithm/CCalculationAlgorithmContext.h`
//! (`CCalculationAlgorithmContext`, the `mUsed*` cache base, derives `CContext`)
//! and `CCalculationAlgorithmContextBase.h` (`CCalculationAlgorithmContextBase`,
//! the `m*` init/source fields, derives `CCalculationAlgorithmContext`).
//!
//! Struct-definition unit only (wave W3): every declared member is reproduced 1:1
//! for method-by-method diffability; the `init*`/getter logic ports later. Only
//! the simplest accessors are inlined here.
//!
//! KONCLUDE-PORT-NOTE[ownership]: C++ has no Rust inheritance, so
//! `CCalculationAlgorithmContextBase` FOLDS its base `CCalculationAlgorithmContext`
//! in as a `base` composition field (the same idiom `process/node.rs` uses for its
//! four bases). The `mUsed*` slots cache the corresponding `m*` source pointers
//! after `initCalculationAlgorithmContext`; here they are kept as the explicit
//! separate fields the two C++ classes declare.

#![allow(dead_code)]

use super::super::cache::context::CacheContext;
use super::super::model::ontology::OntologyArenas;
use super::super::model::substrate::{Arena, Cint64, Id, INVALID};
use super::super::process::backend_control::BackendNeighbourExpansionControllingData;
use super::super::process::blocking_hash::{
    BlockingIndividualNodeCandidateHashId, BlockingIndividualNodeLinkedCandidateHashId,
    ReusingReviewData, SignatureBlockingReviewSet,
};
use super::super::process::context::ProcessContext;
use super::super::process::databox::ProcessingDataBox;
use super::super::process::marker_hash::MarkerIndividualNodeHashId;
use super::super::process::node_switch_history::NodeSwitchHistoryId;
use super::super::process::queues::{
    IndividualConceptBatchProcessingQueue, IndividualCustomPriorityProcessingQueue,
    IndividualDepthProcessingQueue, IndividualLinkerRotationProcessingQueue,
    IndividualProcessingQueue, IndividualReactivationProcessingQueue,
    IndividualUnsortedProcessingQueue,
};
use super::super::process::reapply_sat::SigBlockCandHashId;
use super::super::process::representative::{
    RepresentativeJoiningHash, RepresentativeJoiningHashId,
    RepresentativeVariableBindingPathJoiningKeyHash,
    RepresentativeVariableBindingPathJoiningKeyHashId, RepresentativeVariableBindingPathSetHash,
    RepresentativeVariableBindingPathSetHashId,
};
use super::super::process::{BranchNodeId, DependencyId, NodeId, TrackPointId};
use super::super::task::adapters::{
    IndividualDependenceTrackingCollector, IndividualDependenceTrackingCollectorId,
    IndividualDependenceTrackingMarker, IndividualDependenceTrackingMarkerId,
    SatisfiableTaskClassificationMessageAdapter,
    SatisfiableTaskClassificationRoleMarkedMessageAdapter,
    SatisfiableTaskIncrementalConsistencyTestingAdapter,
    SatisfiableTaskIndividualDependenceTrackingAdapter,
};
use super::super::task::task_data::{TaskData, TaskDataId};
use super::clash::CalcSignal;
use super::strategy::{
    ConceptProcessingPriorityStrategy, IndividualProcessingPriorityStrategy,
    TaskProcessingPriorityStrategy, UnsatisfiableCacheRetrievalStrategy,
};
use super::stubs::{
    ClashDescriptorFactory, ComputedConsequencesCacheHandler, DependencyFactory,
    IndividualNodeManager, OccurrenceStatisticsCacheHandler, ProcessTagger,
    ProcessingStatisticGathering, SatisfiableCalculationTask, SatisfiableExpanderCacheHandler,
    SaturationNodeExpansionCacheHandler, UnsatisfiableCacheHandler,
};

/// Live Rust owner for the C++ `CUnsatisfiableCacheHandler*` plus the collapsed
/// cache-family arenas it references through reader/writer ids.
pub struct UsedUnsatisfiableCacheHandlerState {
    pub handler: UnsatisfiableCacheHandler,
    pub cache_context: CacheContext,
}

/// Live Rust owner for the C++ `CSatisfiableExpanderCacheHandler*` and its
/// ontology-wide signature cache. The state survives per-probe context resets.
pub struct UsedSatisfiableExpanderCacheHandlerState {
    pub handler: SatisfiableExpanderCacheHandler,
}

/// Live Rust owner for the C++ `CSaturationNodeExpansionCacheHandler*`.
pub struct UsedSaturationNodeExpansionCacheHandlerState {
    pub handler: SaturationNodeExpansionCacheHandler,
    pub cache_context: CacheContext,
}

/// Live Rust owner for the C++ `CComputedConsequencesCacheHandler*`.
pub struct UsedComputedConsequencesCacheHandlerState {
    pub handler: ComputedConsequencesCacheHandler,
}

/// Port of `CCalculationAlgorithmContext`.
///
/// The `mUsed*` cache base: a flat record of the strategy/handler/factory handles
/// and the live branch/dependency/individual cursors the algorithm reads on the
/// hot path (Konclude caches these so the abstract `getX()` virtuals collapse to
/// a field load via `getUsedX()`).
///
/// KONCLUDE-PORT-NOTE[ownership]: per `manifest/00-type-dag.md` §4, the per-thread
/// CONTEXT owns the completion-graph arenas, so the single `CProcessingDataBox`
/// is OWNED here by value (`used_processing_data_box`); the base/derived/algorithm
/// `m*ProcessingDataBox` back-pointers become opaque `Cint64` aliases of it.
pub struct CalculationAlgorithmContext {
    /// `CTaskHandleMemoryAllocationManager* mUsedTempMemMan` (public in C++).
    /// KONCLUDE-PORT-NOTE[memory-pool]: pool allocator → opaque handle; the arena
    /// model replaces it. `INVALID` == `nullptr`.
    pub used_temp_mem_man: Cint64,
    /// `CMemoryAllocationManager* mUsedPrTaskMemMan`. [memory-pool] opaque handle.
    pub used_pr_task_mem_man: Cint64,
    /// `CProcessTagger* mUsedProcessTagger`.
    pub used_process_tagger: Id<ProcessTagger>,
    /// `CProcessContext* mUsedProcessContext` — the OWNED per-test arena container.
    /// KONCLUDE-PORT-NOTE[ownership]: per `manifest/00-type-dag.md` §4 the per-thread
    /// context owns the per-test object pools, so the `CProcessContext` is held here
    /// BY VALUE (the same idiom as `used_processing_data_box`); the base/algorithm
    /// `m*ProcessContext` back-pointers become opaque `Cint64` aliases of it. Every
    /// completion/process method resolves its `NodeId`/`ConDescId`/… ids against
    /// THIS container (`ctx.used_process_context.node(id)`, …).
    pub used_process_context: ProcessContext,
    /// The static read-shared terminology (`CConcept`/`CRole`/`CIndividual`/
    /// `CVariable`). KONCLUDE-PORT-NOTE[ownership]: semantically the TBox/RBox
    /// shared across all tests, NOT per-test; held here by value only so the
    /// calculation context can reach it to resolve `ConceptId`/`RoleId`/… ids.
    pub ontology_arenas: OntologyArenas,
    /// `CConceptProcessingPriorityStrategy* mUsedConceptPriorityStrategy`.
    pub used_concept_priority_strategy: Option<ConceptProcessingPriorityStrategy>,
    /// `CIndividualProcessingPriorityStrategy* mUsedIndividualPriorityStrategy`.
    pub used_individual_priority_strategy: Option<IndividualProcessingPriorityStrategy>,
    /// `CProcessingDataBox* mUsedProcessingDataBox` — the OWNED per-test state box.
    pub used_processing_data_box: ProcessingDataBox,
    /// `CSatisfiableCalculationTask* mUsedSatCalcTask`.
    pub used_sat_calc_task: Id<SatisfiableCalculationTask>,
    /// `CTaskProcessorContext* mUsedTaskProcessorContext`. [api] opaque (scheduler).
    pub used_task_processor_context: Cint64,
    /// `CTaskProcessingPriorityStrategy* mUsedTaskPriorityStrategy`.
    pub used_task_priority_strategy: Option<TaskProcessingPriorityStrategy>,
    /// `CProcessingStatisticGathering* mUsedProcessStatGath`.
    pub used_process_stat_gath: Id<ProcessingStatisticGathering>,
    /// `CBranchTreeNode* mUsedBranchTreeNode`.
    pub used_branch_tree_node: BranchNodeId,
    /// `CDependencyNode* mUsedBaseDepNode`.
    pub used_base_dep_node: DependencyId,
    /// `cint64 mMinModificationAncestorDepth`.
    pub min_modification_ancestor_depth: Cint64,
    /// `cint64 mMinModificationIndividualID`.
    pub min_modification_individual_id: Cint64,
    /// `bool mMinModificationUpdated`.
    pub min_modification_updated: bool,
    /// `CUnsatisfiableCacheHandler* mUsedUnsatCacheHandler`.
    pub used_unsat_cache_handler: Id<UnsatisfiableCacheHandler>,
    /// Live owner for the used unsat-cache handler when the pointer is resolved.
    pub used_unsat_cache_handler_state: Option<UsedUnsatisfiableCacheHandlerState>,
    /// `CIndividualNodeManager* mUsedIndividualNodeManager`.
    pub used_individual_node_manager: Id<IndividualNodeManager>,
    /// `CClashDescriptorFactory* mUsedClashDescriptorFactory`.
    pub used_clash_descriptor_factory: Id<ClashDescriptorFactory>,
    /// `CUnsatisfiableCacheRetrievalStrategy* mUsedUnsatCachRetStrategy`.
    pub used_unsat_cach_ret_strategy: Option<UnsatisfiableCacheRetrievalStrategy>,
    /// `CDependencyFactory* mUsedDepFactory`.
    pub used_dep_factory: Id<DependencyFactory>,
    /// `CSatisfiableExpanderCacheHandler* mUsedSatExpCacheHandler`.
    pub used_sat_exp_cache_handler: Id<SatisfiableExpanderCacheHandler>,
    /// Live owner for the used satisfiable-expander cache handler.
    pub used_sat_exp_cache_handler_state: Option<UsedSatisfiableExpanderCacheHandlerState>,
    /// `cint64 mMaxCompletionGraphCachedIndiNodeID`.
    pub max_completion_graph_cached_indi_node_id: Cint64,
    /// `CIndividualProcessNode* mCurrentIndiNode`.
    pub current_indi_node: NodeId,
    /// `cint64 mCompletionGraphCachedLocalizationTag`.
    pub completion_graph_cached_localization_tag: Cint64,
    /// `CSaturationNodeExpansionCacheHandler* mUsedSatNodeExpCacheHandler`.
    pub used_sat_node_exp_cache_handler: Id<SaturationNodeExpansionCacheHandler>,
    /// Live owner for the used saturation-node expansion handler when resolved.
    pub used_sat_node_exp_cache_handler_state: Option<UsedSaturationNodeExpansionCacheHandlerState>,
    /// Live owner for the computed-consequences handler when resolved.
    pub used_computed_consequences_cache_handler_state:
        Option<UsedComputedConsequencesCacheHandlerState>,

    /// KONCLUDE-PORT-NOTE[exceptions]: the pending clash/stop signal — the Rust
    /// stand-in for an in-flight `CCalculation{Clash,Stop}ProcessingException`
    /// (Konclude has no such field; the throw lives only on the C++ call stack).
    /// Per-task, raised by `raise_clash`/`raise_stop` deep in the rules and drained
    /// by the `handleTask` catch (`take_pending_signal`). See `completion/clash.rs`.
    pub pending_signal: CalcSignal,

    /// Resolution arena for the satisfiable tasks the context's `mUsedSatCalcTask` /
    /// the base's `mSatCalcTask` reference.
    /// KONCLUDE-PORT-NOTE[ownership]: Konclude tasks are scheduler-managed heap
    /// objects pointed at by `mSatCalcTask`; per the uniform convention (PORT.md §5,
    /// `CClass*` → `Id<T>` + `Arena<T>`) the port resolves `Id<SatisfiableCalculationTask>`
    /// against this thin arena rather than a raw pointer. It is NOT a heavyweight
    /// per-test task container (Konclude has none); the satisfiable task instance —
    /// and the incremental-consistency adapter it carries — is held on the task, not
    /// here. Empty until `initCalculationAlgorithmContext` (a deferred orchestration
    /// step) populates it, so every resolver guards `Id::NONE`.
    pub sat_calc_task_arena: Arena<SatisfiableCalculationTask>,
    /// Resolution arena for the incremental-consistency testing adapter the task's
    /// `mSatIncConsTestingAdapter` references (same convention as above).
    pub inc_cons_testing_adapter_arena: Arena<SatisfiableTaskIncrementalConsistencyTestingAdapter>,
    /// Resolution arena for the classification message adapter the task's
    /// `mClassMessAdapter` references (same convention as above).
    pub classification_message_adapter_arena: Arena<SatisfiableTaskClassificationMessageAdapter>,
    /// Resolution arena for the role-marked classification message adapter the
    /// task's `mClassRoleMarkedMessageAdapter` references.
    pub classification_role_marked_message_adapter_arena:
        Arena<SatisfiableTaskClassificationRoleMarkedMessageAdapter>,
    /// Resolution arena for the individual-dependence tracking adapter the task's
    /// `mSatIndDepTrackAdapter` references (same convention as above).
    pub individual_dependence_tracking_adapter_arena:
        Arena<SatisfiableTaskIndividualDependenceTrackingAdapter>,
    /// Resolution arena for `CIndividualDependenceTrackingCollector` observer
    /// instances used by the individual-dependence tracking adapter.
    pub individual_dependence_tracking_collector_arena:
        Arena<IndividualDependenceTrackingCollector>,
    /// Resolution arena for the classifier-item
    /// `CIndividualDependenceTrackingMarker` payload.
    pub individual_dependence_tracking_marker_arena: Arena<IndividualDependenceTrackingMarker>,
    /// Resolution arena for `CConsistenceTaskData` / `CIncrementalConsistenceTaskData`
    /// records reachable from incremental-consistency previous ontology seams.
    pub task_data_arena: Arena<TaskData>,
}

impl CalculationAlgorithmContext {
    /// Port of `CCalculationAlgorithmContext::CCalculationAlgorithmContext`.
    /// KONCLUDE-PORT-NOTE[uninit]: the C++ ctor leaves the caches unset; the real
    /// values arrive in `initCalculationAlgorithmContext`. Here every handle starts
    /// `INVALID`/`Id::NONE`, counters `0`, flags `false`, and the owned databox empty.
    pub fn new() -> Self {
        CalculationAlgorithmContext {
            used_temp_mem_man: INVALID,
            used_pr_task_mem_man: INVALID,
            used_process_tagger: Id::NONE,
            used_concept_priority_strategy: None,
            used_individual_priority_strategy: None,
            used_process_context: ProcessContext::new(),
            ontology_arenas: OntologyArenas::new(),
            // The C++ calculation context receives a fully constructed
            // CProcessingDataBox. `new()` is only the port's zeroed storage
            // initializer; the constructor seeds, among other counters,
            // mNextSatResSuccExtIndividualNodeID with -1 so its first use starts
            // after the populated saturation-node vector.
            used_processing_data_box: ProcessingDataBox::with_process_context(INVALID),
            used_sat_calc_task: Id::NONE,
            used_task_processor_context: INVALID,
            used_task_priority_strategy: None,
            used_process_stat_gath: Id::NONE,
            used_branch_tree_node: Id::NONE,
            used_base_dep_node: Id::NONE,
            min_modification_ancestor_depth: 0,
            min_modification_individual_id: 0,
            min_modification_updated: false,
            used_unsat_cache_handler: Id::NONE,
            used_unsat_cache_handler_state: None,
            used_individual_node_manager: Id::NONE,
            used_clash_descriptor_factory: Id::NONE,
            used_unsat_cach_ret_strategy: None,
            used_dep_factory: Id::NONE,
            used_sat_exp_cache_handler: Id::NONE,
            used_sat_exp_cache_handler_state: None,
            max_completion_graph_cached_indi_node_id: 0,
            current_indi_node: Id::NONE,
            completion_graph_cached_localization_tag: 0,
            used_sat_node_exp_cache_handler: Id::NONE,
            used_sat_node_exp_cache_handler_state: None,
            used_computed_consequences_cache_handler_state: None,
            pending_signal: CalcSignal::Continue,
            sat_calc_task_arena: Arena::new(),
            inc_cons_testing_adapter_arena: Arena::new(),
            classification_message_adapter_arena: Arena::new(),
            classification_role_marked_message_adapter_arena: Arena::new(),
            individual_dependence_tracking_adapter_arena: Arena::new(),
            individual_dependence_tracking_collector_arena: Arena::new(),
            individual_dependence_tracking_marker_arena: Arena::new(),
            task_data_arena: Arena::new(),
        }
    }

    /// Resolve a satisfiable task id (the `mSatCalcTask` / `mUsedSatCalcTask` target).
    pub fn sat_calc_task(&self, id: Id<SatisfiableCalculationTask>) -> &SatisfiableCalculationTask {
        self.sat_calc_task_arena.get(id)
    }
    /// Fallible satisfiable-task resolver for context-init paths that may still
    /// receive a scheduler-owned task id from an arena outside this context.
    pub fn try_sat_calc_task(
        &self,
        id: Id<SatisfiableCalculationTask>,
    ) -> Option<&SatisfiableCalculationTask> {
        if id.is_some() && id.index() < self.sat_calc_task_arena.len() {
            Some(self.sat_calc_task(id))
        } else {
            None
        }
    }
    /// Mutable resolve of a satisfiable task id.
    pub fn sat_calc_task_mut(
        &mut self,
        id: Id<SatisfiableCalculationTask>,
    ) -> &mut SatisfiableCalculationTask {
        self.sat_calc_task_arena.get_mut(id)
    }
    /// Pool-allocate a satisfiable task (`new CSatisfiableCalculationTask`).
    pub fn alloc_sat_calc_task(
        &mut self,
        task: SatisfiableCalculationTask,
    ) -> Id<SatisfiableCalculationTask> {
        self.sat_calc_task_arena.push(task)
    }
    /// Arena-aware port of
    /// `CSatisfiableCalculationTask::initBranchDependedSatisfiableCalculationTask`.
    pub fn alloc_branch_depended_satisfiable_calculation_task(
        &mut self,
        depended_task: Id<SatisfiableCalculationTask>,
    ) -> Id<SatisfiableCalculationTask> {
        let task_id = self.alloc_sat_calc_task(SatisfiableCalculationTask::new());
        let task_as_base_id = Id::new(task_id.raw);
        let parent_as_base_id = Id::new(depended_task.raw);
        let (
            root_task,
            task_depth,
            task_type,
            process_context,
            processing_data_box,
            calc_stat_coll,
            calculation_config,
            cons_adapter,
            indi_anal_adapter,
            class_mess_adapter,
            real_mess_adapter,
            sat_inc_cons_testing_adapter,
            sat_ind_dep_track_adapter,
            poss_ass_coll_adapter,
            class_role_marked_message_adapter,
            answerer_subsumption_message_adapter,
            answerer_binding_propagation_adapter,
            satisfiable_possible_instances_merging_adapter,
            answerer_instance_propagation_message_adapter,
            representative_backend_updating_adapter,
            occurrence_statistics_collecting_adapter,
            answerer_materialization_adapter,
            cancellation_adapter,
        ) = {
            let parent = self.sat_calc_task(depended_task);
            (
                parent.base.root_task,
                parent.base.task_depth,
                parent.base.task_type,
                parent.process_context,
                parent.processing_data_box,
                parent.calc_stat_coll,
                parent.calculation_config,
                parent.cons_adapter,
                parent.indi_anal_adapter,
                parent.class_mess_adapter,
                parent.real_mess_adapter,
                parent.sat_inc_cons_testing_adapter,
                parent.sat_ind_dep_track_adapter,
                parent.poss_ass_coll_adapter,
                parent.class_role_marked_message_adapter,
                parent.answerer_subsumption_message_adapter,
                parent.answerer_binding_propagation_adapter,
                parent.satisfiable_possible_instances_merging_adapter,
                parent.answerer_instance_propagation_message_adapter,
                parent.representative_backend_updating_adapter,
                parent.occurrence_statistics_collecting_adapter,
                parent.answerer_materialization_adapter,
                parent.cancellation_adapter,
            )
        };
        let root_task = if root_task.is_some() {
            root_task
        } else {
            parent_as_base_id
        };

        {
            let parent = self.sat_calc_task_mut(depended_task);
            parent.base.active_task_reference_count += 1;
            parent.base.referenced_task_linker.insert(
                0,
                super::super::model::NegLink {
                    target: task_as_base_id,
                    negated: true,
                },
            );
        }

        let child = self.sat_calc_task_mut(task_id);
        child.init_task(parent_as_base_id);
        child.base.parent_task = parent_as_base_id;
        child.base.root_task = root_task;
        child.base.task_depth = task_depth + 1;
        child.base.task_type = task_type;
        child.process_context = process_context;
        child.processing_data_box = processing_data_box;
        child.calc_stat_coll = calc_stat_coll;
        child.calculation_config = calculation_config;
        child.cons_adapter = cons_adapter;
        child.indi_anal_adapter = indi_anal_adapter;
        child.class_mess_adapter = class_mess_adapter;
        child.real_mess_adapter = real_mess_adapter;
        child.sat_inc_cons_testing_adapter = sat_inc_cons_testing_adapter;
        child.sat_ind_dep_track_adapter = sat_ind_dep_track_adapter;
        child.poss_ass_coll_adapter = poss_ass_coll_adapter;
        child.class_role_marked_message_adapter = class_role_marked_message_adapter;
        child.answerer_subsumption_message_adapter = answerer_subsumption_message_adapter;
        child.answerer_binding_propagation_adapter = answerer_binding_propagation_adapter;
        child.satisfiable_possible_instances_merging_adapter =
            satisfiable_possible_instances_merging_adapter;
        child.answerer_instance_propagation_message_adapter =
            answerer_instance_propagation_message_adapter;
        child.representative_backend_updating_adapter = representative_backend_updating_adapter;
        child.occurrence_statistics_collecting_adapter = occurrence_statistics_collecting_adapter;
        child.answerer_materialization_adapter = answerer_materialization_adapter;
        child.cancellation_adapter = cancellation_adapter;
        task_id
    }
    /// Resolve an incremental-consistency testing adapter id.
    pub fn inc_cons_testing_adapter(
        &self,
        id: Id<SatisfiableTaskIncrementalConsistencyTestingAdapter>,
    ) -> &SatisfiableTaskIncrementalConsistencyTestingAdapter {
        self.inc_cons_testing_adapter_arena.get(id)
    }
    /// Pool-allocate an incremental-consistency testing adapter.
    pub fn alloc_inc_cons_testing_adapter(
        &mut self,
        adapter: SatisfiableTaskIncrementalConsistencyTestingAdapter,
    ) -> Id<SatisfiableTaskIncrementalConsistencyTestingAdapter> {
        self.inc_cons_testing_adapter_arena.push(adapter)
    }

    /// Resolve a classification message adapter id.
    pub fn classification_message_adapter(
        &self,
        id: Id<SatisfiableTaskClassificationMessageAdapter>,
    ) -> &SatisfiableTaskClassificationMessageAdapter {
        self.classification_message_adapter_arena.get(id)
    }
    /// Mutable resolve of a classification message adapter id.
    pub fn classification_message_adapter_mut(
        &mut self,
        id: Id<SatisfiableTaskClassificationMessageAdapter>,
    ) -> &mut SatisfiableTaskClassificationMessageAdapter {
        self.classification_message_adapter_arena.get_mut(id)
    }
    /// Pool-allocate a classification message adapter.
    pub fn alloc_classification_message_adapter(
        &mut self,
        adapter: SatisfiableTaskClassificationMessageAdapter,
    ) -> Id<SatisfiableTaskClassificationMessageAdapter> {
        self.classification_message_adapter_arena.push(adapter)
    }

    /// Resolve a role-marked classification message adapter id.
    pub fn classification_role_marked_message_adapter(
        &self,
        id: Id<SatisfiableTaskClassificationRoleMarkedMessageAdapter>,
    ) -> &SatisfiableTaskClassificationRoleMarkedMessageAdapter {
        self.classification_role_marked_message_adapter_arena
            .get(id)
    }
    /// Mutable resolve of a role-marked classification message adapter id.
    pub fn classification_role_marked_message_adapter_mut(
        &mut self,
        id: Id<SatisfiableTaskClassificationRoleMarkedMessageAdapter>,
    ) -> &mut SatisfiableTaskClassificationRoleMarkedMessageAdapter {
        self.classification_role_marked_message_adapter_arena
            .get_mut(id)
    }
    /// Pool-allocate a role-marked classification message adapter.
    pub fn alloc_classification_role_marked_message_adapter(
        &mut self,
        adapter: SatisfiableTaskClassificationRoleMarkedMessageAdapter,
    ) -> Id<SatisfiableTaskClassificationRoleMarkedMessageAdapter> {
        self.classification_role_marked_message_adapter_arena
            .push(adapter)
    }

    /// Resolve an individual-dependence tracking adapter id.
    pub fn individual_dependence_tracking_adapter(
        &self,
        id: Id<SatisfiableTaskIndividualDependenceTrackingAdapter>,
    ) -> &SatisfiableTaskIndividualDependenceTrackingAdapter {
        self.individual_dependence_tracking_adapter_arena.get(id)
    }

    /// Mutable resolve of an individual-dependence tracking adapter id.
    pub fn individual_dependence_tracking_adapter_mut(
        &mut self,
        id: Id<SatisfiableTaskIndividualDependenceTrackingAdapter>,
    ) -> &mut SatisfiableTaskIndividualDependenceTrackingAdapter {
        self.individual_dependence_tracking_adapter_arena
            .get_mut(id)
    }

    /// Pool-allocate an individual-dependence tracking adapter.
    pub fn alloc_individual_dependence_tracking_adapter(
        &mut self,
        adapter: SatisfiableTaskIndividualDependenceTrackingAdapter,
    ) -> Id<SatisfiableTaskIndividualDependenceTrackingAdapter> {
        self.individual_dependence_tracking_adapter_arena
            .push(adapter)
    }

    /// Resolve an individual-dependence tracking collector observer id.
    pub fn individual_dependence_tracking_collector(
        &self,
        id: IndividualDependenceTrackingCollectorId,
    ) -> &IndividualDependenceTrackingCollector {
        self.individual_dependence_tracking_collector_arena.get(id)
    }

    /// Mutable resolve of an individual-dependence tracking collector observer id.
    pub fn individual_dependence_tracking_collector_mut(
        &mut self,
        id: IndividualDependenceTrackingCollectorId,
    ) -> &mut IndividualDependenceTrackingCollector {
        self.individual_dependence_tracking_collector_arena
            .get_mut(id)
    }

    /// Pool-allocate an individual-dependence tracking collector observer.
    pub fn alloc_individual_dependence_tracking_collector(
        &mut self,
        collector: IndividualDependenceTrackingCollector,
    ) -> IndividualDependenceTrackingCollectorId {
        self.individual_dependence_tracking_collector_arena
            .push(collector)
    }

    /// Resolve an individual-dependence tracking marker id.
    pub fn individual_dependence_tracking_marker(
        &self,
        id: IndividualDependenceTrackingMarkerId,
    ) -> &IndividualDependenceTrackingMarker {
        self.individual_dependence_tracking_marker_arena.get(id)
    }

    /// Mutable resolve of an individual-dependence tracking marker id.
    pub fn individual_dependence_tracking_marker_mut(
        &mut self,
        id: IndividualDependenceTrackingMarkerId,
    ) -> &mut IndividualDependenceTrackingMarker {
        self.individual_dependence_tracking_marker_arena.get_mut(id)
    }

    /// Pool-allocate an individual-dependence tracking marker.
    pub fn alloc_individual_dependence_tracking_marker(
        &mut self,
        marker: IndividualDependenceTrackingMarker,
    ) -> IndividualDependenceTrackingMarkerId {
        self.individual_dependence_tracking_marker_arena
            .push(marker)
    }

    /// Resolve a task-data record.
    pub fn task_data(&self, id: TaskDataId) -> &TaskData {
        self.task_data_arena.get(id)
    }

    /// Pool-allocate a task-data record.
    pub fn alloc_task_data(&mut self, task_data: TaskData) -> TaskDataId {
        self.task_data_arena.push(task_data)
    }

    /// Port of the `satCalcTask->getClassificationMessageAdapter()` deref:
    /// resolve the task and return its classification-message adapter id.
    pub fn satisfiable_task_classification_message_adapter(
        &self,
        sat_calc_task: Id<SatisfiableCalculationTask>,
    ) -> Id<SatisfiableTaskClassificationMessageAdapter> {
        if sat_calc_task.is_none() {
            return Id::NONE;
        }
        self.sat_calc_task(sat_calc_task)
            .get_classification_message_adapter()
    }

    /// Port of the `satCalcTask->getSatisfiableTaskIncrementalConsistencyTestingAdapter()`
    /// deref: resolve the task and return its incremental-consistency adapter id
    /// (`Id::NONE` when the task is unset — the C++ `nullptr` task / adapter).
    pub fn satisfiable_task_incremental_consistency_testing_adapter(
        &self,
        sat_calc_task: Id<SatisfiableCalculationTask>,
    ) -> Id<SatisfiableTaskIncrementalConsistencyTestingAdapter> {
        if sat_calc_task.is_none() {
            return Id::NONE;
        }
        self.sat_calc_task(sat_calc_task)
            .get_satisfiable_task_incremental_consistency_testing_adapter()
    }

    /// Port of
    /// `satCalcTask->getSatisfiableTaskIndividualDependenceTrackingAdapter()`.
    pub fn satisfiable_task_individual_dependence_tracking_adapter(
        &self,
        sat_calc_task: Id<SatisfiableCalculationTask>,
    ) -> Id<SatisfiableTaskIndividualDependenceTrackingAdapter> {
        if sat_calc_task.is_none() {
            return Id::NONE;
        }
        self.sat_calc_task(sat_calc_task)
            .get_satisfiable_task_individual_dependence_tracking_adapter()
    }

    /// Port of `getUsedProcessingDataBox`.
    pub fn used_processing_data_box(&self) -> &ProcessingDataBox {
        &self.used_processing_data_box
    }
    /// Mutable access to the owned databox (the `getUsedProcessingDataBox` target).
    pub fn used_processing_data_box_mut(&mut self) -> &mut ProcessingDataBox {
        &mut self.used_processing_data_box
    }
    /// Port of `getUsedProcessContext` — the owned per-test arena container.
    pub fn used_process_context(&self) -> &ProcessContext {
        &self.used_process_context
    }
    /// Mutable access to the owned process context (the id-allocation path).
    pub fn used_process_context_mut(&mut self) -> &mut ProcessContext {
        &mut self.used_process_context
    }
    /// The static read-shared terminology arenas.
    pub fn ontology_arenas(&self) -> &OntologyArenas {
        &self.ontology_arenas
    }
    /// Mutable terminology access (construction time only).
    pub fn ontology_arenas_mut(&mut self) -> &mut OntologyArenas {
        &mut self.ontology_arenas
    }
    /// Install a live port-owned `CUnsatisfiableCacheHandler` target for
    /// `getUsedUnsatisfiableCacheHandler`.
    pub fn install_used_unsatisfiable_cache_handler(
        &mut self,
        handler: UnsatisfiableCacheHandler,
        cache_context: CacheContext,
    ) -> Id<UnsatisfiableCacheHandler> {
        let handler_id = Id::new(0);
        self.used_unsat_cache_handler = handler_id;
        self.used_unsat_cache_handler_state = Some(UsedUnsatisfiableCacheHandlerState {
            handler,
            cache_context,
        });
        handler_id
    }
    /// Temporarily move out the live handler target so callers can also borrow
    /// the calculation context mutably, matching a C++ raw-pointer call.
    pub fn take_used_unsatisfiable_cache_handler(
        &mut self,
    ) -> Option<UsedUnsatisfiableCacheHandlerState> {
        self.used_unsat_cache_handler_state.take()
    }
    /// Restore a handler target after `take_used_unsatisfiable_cache_handler`.
    pub fn restore_used_unsatisfiable_cache_handler(
        &mut self,
        state: UsedUnsatisfiableCacheHandlerState,
    ) {
        self.used_unsat_cache_handler_state = Some(state);
        self.used_unsat_cache_handler = Id::new(0);
    }
    /// Install a live port-owned `CSatisfiableExpanderCacheHandler` target for
    /// `getUsedSatisfiableExpanderCacheHandler`.
    pub fn install_used_satisfiable_expander_cache_handler(
        &mut self,
        handler: SatisfiableExpanderCacheHandler,
    ) -> Id<SatisfiableExpanderCacheHandler> {
        let handler_id = Id::new(0);
        self.used_sat_exp_cache_handler = handler_id;
        self.used_sat_exp_cache_handler_state =
            Some(UsedSatisfiableExpanderCacheHandlerState { handler });
        handler_id
    }
    /// Temporarily move out the live satisfiable-expander handler target.
    pub fn take_used_satisfiable_expander_cache_handler(
        &mut self,
    ) -> Option<UsedSatisfiableExpanderCacheHandlerState> {
        self.used_sat_exp_cache_handler_state.take()
    }
    /// Restore a handler target after
    /// `take_used_satisfiable_expander_cache_handler`.
    pub fn restore_used_satisfiable_expander_cache_handler(
        &mut self,
        state: UsedSatisfiableExpanderCacheHandlerState,
    ) {
        self.used_sat_exp_cache_handler_state = Some(state);
        self.used_sat_exp_cache_handler = Id::new(0);
    }
    /// Install a live port-owned `CSaturationNodeExpansionCacheHandler` target for
    /// `getUsedSaturationNodeExpansionCacheHandler`.
    pub fn install_used_saturation_node_expansion_cache_handler(
        &mut self,
        handler: SaturationNodeExpansionCacheHandler,
        cache_context: CacheContext,
    ) -> Id<SaturationNodeExpansionCacheHandler> {
        let handler_id = Id::new(0);
        self.used_sat_node_exp_cache_handler = handler_id;
        self.used_sat_node_exp_cache_handler_state =
            Some(UsedSaturationNodeExpansionCacheHandlerState {
                handler,
                cache_context,
            });
        handler_id
    }
    /// Temporarily move out the live saturation-node expansion handler target.
    pub fn take_used_saturation_node_expansion_cache_handler(
        &mut self,
    ) -> Option<UsedSaturationNodeExpansionCacheHandlerState> {
        self.used_sat_node_exp_cache_handler_state.take()
    }
    /// Restore a handler target after `take_used_saturation_node_expansion_cache_handler`.
    pub fn restore_used_saturation_node_expansion_cache_handler(
        &mut self,
        state: UsedSaturationNodeExpansionCacheHandlerState,
    ) {
        self.used_sat_node_exp_cache_handler_state = Some(state);
        self.used_sat_node_exp_cache_handler = Id::new(0);
    }
    /// Install a live port-owned `CComputedConsequencesCacheHandler` target.
    pub fn install_used_computed_consequences_cache_handler(
        &mut self,
        handler: ComputedConsequencesCacheHandler,
    ) -> Id<ComputedConsequencesCacheHandler> {
        let handler_id = Id::new(0);
        self.used_computed_consequences_cache_handler_state =
            Some(UsedComputedConsequencesCacheHandlerState { handler });
        handler_id
    }
    /// Temporarily move out the live computed-consequences handler target.
    pub fn take_used_computed_consequences_cache_handler(
        &mut self,
    ) -> Option<UsedComputedConsequencesCacheHandlerState> {
        self.used_computed_consequences_cache_handler_state.take()
    }
    /// Restore a handler target after `take_used_computed_consequences_cache_handler`.
    pub fn restore_used_computed_consequences_cache_handler(
        &mut self,
        state: UsedComputedConsequencesCacheHandlerState,
    ) {
        self.used_computed_consequences_cache_handler_state = Some(state);
    }
    /// Port of `getCurrentIndividualNode`.
    pub fn current_individual_node(&self) -> NodeId {
        self.current_indi_node
    }
    /// Port of `setCurrentIndividualNode`.
    pub fn set_current_individual_node(&mut self, n: NodeId) -> &mut Self {
        self.current_indi_node = n;
        self
    }
    /// Port of `getUsedBranchTreeNode`.
    pub fn used_branch_tree_node(&self) -> BranchNodeId {
        self.used_branch_tree_node
    }
    /// Port of `getUsedBaseDependencyNode`.
    pub fn used_base_dependency_node(&self) -> DependencyId {
        self.used_base_dep_node
    }
    /// Port of `getUsedConceptPriorityStrategy`.
    pub fn used_concept_priority_strategy(&self) -> Option<&ConceptProcessingPriorityStrategy> {
        self.used_concept_priority_strategy.as_ref()
    }
    /// Port of `getUsedIndividualPriorityStrategy`.
    pub fn used_individual_priority_strategy(
        &self,
    ) -> Option<&IndividualProcessingPriorityStrategy> {
        self.used_individual_priority_strategy.as_ref()
    }
    /// Port of `getUsedTaskPriorityStrategy`.
    pub fn used_task_priority_strategy(&self) -> Option<&TaskProcessingPriorityStrategy> {
        self.used_task_priority_strategy.as_ref()
    }
    /// Port of `getUsedUnsatisfiableCacheRetrievalStrategy`.
    pub fn used_unsatisfiable_cache_retrieval_strategy(
        &self,
    ) -> Option<&UnsatisfiableCacheRetrievalStrategy> {
        self.used_unsat_cach_ret_strategy.as_ref()
    }
    /// Port of `isMinModificationUpdated`.
    pub fn is_min_modification_updated(&self) -> bool {
        self.min_modification_updated
    }
    /// Port of `getMinModificationAncestorDepth`.
    pub fn min_modification_ancestor_depth(&self) -> Cint64 {
        self.min_modification_ancestor_depth
    }
    /// Port of `getMinModificationIndividualID`.
    pub fn min_modification_individual_id(&self) -> Cint64 {
        self.min_modification_individual_id
    }
    /// Port of `setMinModificationAncestorDepth`.
    pub fn set_min_modification_ancestor_depth(&mut self, anc_depth: Cint64) -> &mut Self {
        self.min_modification_ancestor_depth = anc_depth;
        self.min_modification_updated = false;
        self
    }
    /// Port of `setMinModificationIndividualID`.
    pub fn set_min_modification_individual_id(&mut self, indi_id: Cint64) -> &mut Self {
        self.min_modification_individual_id = indi_id;
        self.min_modification_updated = false;
        self
    }
    /// Port of `setMinModificationIndividual`.
    pub fn set_min_modification_individual(&mut self, indi_node: NodeId) -> &mut Self {
        let (indi_id, ancestor_depth) = {
            let n = self.used_process_context.node(indi_node);
            (n.individual_node_id(), n.individual_ancestor_depth())
        };
        self.set_min_modification_individual_id(indi_id);
        self.set_min_modification_ancestor_depth(ancestor_depth);
        self
    }
    /// Port of `setMinModificationAncestorDepthCandidate`.
    ///
    /// KONCLUDE-PORT-NOTE[unclear]: Konclude's inline implementation compares
    /// `ancDepthCandidate` against `mMinModificationIndividualID` and writes the
    /// minimum back to `mMinModificationIndividualID` rather than
    /// `mMinModificationAncestorDepth`. The port preserves that source behaviour.
    pub fn set_min_modification_ancestor_depth_candidate(
        &mut self,
        anc_depth_candidate: Cint64,
    ) -> bool {
        let updated = anc_depth_candidate < self.min_modification_individual_id;
        self.min_modification_individual_id =
            self.min_modification_individual_id.min(anc_depth_candidate);
        updated
    }
    /// Port of `setMinModificationIndividualIDCandidate`.
    pub fn set_min_modification_individual_id_candidate(
        &mut self,
        indi_id_candidate: Cint64,
    ) -> bool {
        let updated = indi_id_candidate < self.min_modification_individual_id;
        self.min_modification_individual_id =
            self.min_modification_individual_id.min(indi_id_candidate);
        updated
    }
    /// Port of `setMinModificationIndividualCandidate`.
    pub fn set_min_modification_individual_candidate(&mut self, indi_node: NodeId) -> bool {
        let (indi_id, ancestor_depth) = {
            let n = self.used_process_context.node(indi_node);
            (n.individual_node_id(), n.individual_ancestor_depth())
        };
        self.set_min_modification_individual_id_candidate(indi_id)
            || self.set_min_modification_ancestor_depth_candidate(ancestor_depth)
    }
    /// Port of `getMaxCompletionGraphCachedIndividualNodeID`.
    pub fn max_completion_graph_cached_individual_node_id(&self) -> Cint64 {
        self.max_completion_graph_cached_indi_node_id
    }
    /// Port of `getCompletionGraphCachedLocalizationTag`.
    pub fn completion_graph_cached_localization_tag(&self) -> Cint64 {
        self.completion_graph_cached_localization_tag
    }
}

impl Default for CalculationAlgorithmContext {
    fn default() -> Self {
        Self::new()
    }
}

/// Port of `CCalculationAlgorithmContextBase`.
///
/// The init/source side of the context: the `m*` fields that
/// `initCalculationAlgorithmContext` reads and copies into the `mUsed*` cache of
/// the folded-in `base`. Field order mirrors the C++ `.h` (109–128) after `base`.
pub struct CalculationAlgorithmContextBase {
    /// The folded-in `CCalculationAlgorithmContext` base (holds the `mUsed*` cache
    /// + the owned `ProcessingDataBox`).
    pub base: CalculationAlgorithmContext,

    /// `CTaskHandleMemoryAllocationManager* mTempMemMan`. [memory-pool] opaque.
    pub temp_mem_man: Cint64,
    /// `CMemoryAllocationManager* mPrTaskMemMan`. [memory-pool] opaque.
    pub pr_task_mem_man: Cint64,
    /// `CProcessTagger* mProcessTagger`.
    pub process_tagger: Id<ProcessTagger>,
    /// `CProcessContext* mProcessContext`. KONCLUDE-PORT-NOTE[ownership]: an
    /// opaque `Cint64` ALIAS of `base.used_process_context` (single owner; the
    /// real container is held by value in `base`).
    pub process_context: Cint64,
    /// `CConceptProcessingPriorityStrategy* mConceptPriorityStrategy`.
    pub concept_priority_strategy: Option<ConceptProcessingPriorityStrategy>,
    /// `CIndividualProcessingPriorityStrategy* mIndividualPriorityStrategy`.
    pub individual_priority_strategy: Option<IndividualProcessingPriorityStrategy>,
    /// `CTaskProcessingPriorityStrategy* mTaskPriorityStrategy`.
    pub task_priority_strategy: Option<TaskProcessingPriorityStrategy>,
    /// `CProcessingDataBox* mProcessingDataBox`. KONCLUDE-PORT-NOTE[ownership]:
    /// an opaque `Cint64` ALIAS of `base.used_processing_data_box` (single owner).
    pub processing_data_box: Cint64,
    /// `CSatisfiableCalculationTask* mSatCalcTask`.
    pub sat_calc_task: Id<SatisfiableCalculationTask>,
    /// `CTaskProcessorContext* mTaskProcessorContext`. [api] opaque (scheduler).
    pub task_processor_context: Cint64,
    /// `CProcessingStatisticGathering* mProcStatGath`.
    pub proc_stat_gath: Id<ProcessingStatisticGathering>,
    /// `CBranchTreeNode* mBranchTreeNode`.
    pub branch_tree_node: BranchNodeId,
    /// `CDependencyNode* mBaseDepNode`.
    pub base_dep_node: DependencyId,
    /// Branch-epoch databox snapshots (in-process COW): one whole-databox
    /// clone per open epoch, restored on pop together with the process
    /// context's arena journals (see `ProcessContext::push_branch_epoch`).
    pub databox_epoch_stack: Vec<ProcessingDataBox>,
    /// Port-owned cache: a deterministic track point on the branching tree's
    /// INDEPENDENT base dependency node, lazily materialized by
    /// [`Self::get_or_create_base_dependency_track_point`]. Konclude
    /// semantics: with dependency building ON nothing is untracked — an
    /// untracked clash descriptor is a tracking ERROR that aborts the whole
    /// `clashedBacktracking` analysis.
    pub base_independent_track_point: TrackPointId,
    /// `CIndividualNodeManager* mIndiNodeManager`.
    pub indi_node_manager: Id<IndividualNodeManager>,
    /// `CUnsatisfiableCacheHandler* mUnsatCacheHandler`.
    pub unsat_cache_handler: Id<UnsatisfiableCacheHandler>,
    /// `CClashDescriptorFactory* mClashDescriptorFactory`.
    pub clash_descriptor_factory: Id<ClashDescriptorFactory>,
    /// `CUnsatisfiableCacheRetrievalStrategy* mUnsatCachRetStrategy`.
    pub unsat_cach_ret_strategy: Option<UnsatisfiableCacheRetrievalStrategy>,
    /// `CDependencyFactory* mDepFactory`.
    pub dep_factory: Id<DependencyFactory>,
    /// `CSatisfiableExpanderCacheHandler* mSatExpCacheHandler`.
    pub sat_exp_cache_handler: Id<SatisfiableExpanderCacheHandler>,
    /// `CSaturationNodeExpansionCacheHandler* mSatNodeExpCacheHandler`.
    pub sat_node_exp_cache_handler: Id<SaturationNodeExpansionCacheHandler>,
    /// `CComputedConsequencesCacheHandler* mCompConsCacheHandler`.
    pub comp_cons_cache_handler: Id<ComputedConsequencesCacheHandler>,
    /// Live port-owned `COccurrenceStatisticsCacheHandler` used by occurrence-stat
    /// collection tails that already have the threaded calculation context.
    pub occurrence_statistics_cache_handler: OccurrenceStatisticsCacheHandler,
}

/// Generate a databox processing-queue getter forwarder that threads the
/// `ProcessContext` queue arena (both are disjoint fields of `base`).
macro_rules! db_queue_forward {
    ($name:ident, $ret:ty) => {
        #[inline]
        pub fn $name(&mut self, create: bool) -> $ret {
            let b = &mut self.base;
            b.used_processing_data_box
                .$name(&mut b.used_process_context, create)
        }
    };
}

impl CalculationAlgorithmContextBase {
    /// Port of `CCalculationAlgorithmContextBase::CCalculationAlgorithmContextBase`.
    pub fn new() -> Self {
        CalculationAlgorithmContextBase {
            base: CalculationAlgorithmContext::new(),
            temp_mem_man: INVALID,
            pr_task_mem_man: INVALID,
            process_tagger: Id::NONE,
            process_context: INVALID,
            concept_priority_strategy: None,
            individual_priority_strategy: None,
            task_priority_strategy: None,
            processing_data_box: INVALID,
            sat_calc_task: Id::NONE,
            task_processor_context: INVALID,
            proc_stat_gath: Id::NONE,
            branch_tree_node: Id::NONE,
            base_dep_node: Id::NONE,
            databox_epoch_stack: Vec::new(),
            base_independent_track_point: Id::NONE,
            indi_node_manager: Id::NONE,
            unsat_cache_handler: Id::NONE,
            clash_descriptor_factory: Id::NONE,
            unsat_cach_ret_strategy: None,
            dep_factory: Id::NONE,
            sat_exp_cache_handler: Id::NONE,
            sat_node_exp_cache_handler: Id::NONE,
            comp_cons_cache_handler: Id::NONE,
            occurrence_statistics_cache_handler: OccurrenceStatisticsCacheHandler::new(),
        }
    }

    /// Port of `CCalculationAlgorithmContextBase::initTaskProcessContext`.
    ///
    /// C++ copies `processContext`/`satCalcTask` into the source fields and caches
    /// `mUsedProcessContext`, `mUsedProcessingDataBox`, and `mUsedSatCalcTask` in
    /// the base context. In the Rust ownership model the concrete process context
    /// and databox are owned by `base`; the `Cint64` fields remain pointer aliases.
    /// If the satisfiable-task id resolves in this context's task arena, the
    /// databox alias is read from the task exactly as Konclude does. A fresh
    /// by-value context cannot resolve a task allocated in a different arena, so
    /// that orchestration step remains deferred instead of fabricating a databox.
    pub fn init_task_process_context(
        &mut self,
        process_context: Cint64,
        sat_calc_task: Id<SatisfiableCalculationTask>,
    ) -> &mut Self {
        self.process_context = process_context;
        self.sat_calc_task = sat_calc_task;
        self.base.used_sat_calc_task = sat_calc_task;

        if let Some(task) = self.base.try_sat_calc_task(sat_calc_task) {
            self.processing_data_box = task.get_processing_data_box();
        }
        let branching_tree = self.branching_tree(true);
        let branch_tree_node = self
            .base
            .used_process_context
            .branching_tree_branch_tree_node(branching_tree, sat_calc_task.raw, false);
        self.branch_tree_node = branch_tree_node;
        self.base.used_branch_tree_node = branch_tree_node;
        let base_dep_node = self
            .base
            .used_process_context
            .branching_tree_base_dependency_node(branching_tree, true);
        self.base_dep_node = base_dep_node;
        self.base.used_base_dep_node = base_dep_node;
        self
    }

    /// Port of `CCalculationAlgorithmContextBase::initCalculationAlgorithmContext`.
    pub fn init_calculation_algorithm_context(
        &mut self,
        processor_context: Cint64,
        concept_priority_strategy: ConceptProcessingPriorityStrategy,
        individual_priority_strategy: IndividualProcessingPriorityStrategy,
        task_priority_strategy: TaskProcessingPriorityStrategy,
        unsat_cach_ret_strategy: UnsatisfiableCacheRetrievalStrategy,
        indi_node_manager: Id<IndividualNodeManager>,
        clash_descriptor_factory: Id<ClashDescriptorFactory>,
        dep_factory: Id<DependencyFactory>,
        unsat_cache_handler: Id<UnsatisfiableCacheHandler>,
        sat_exp_cache_handler: Id<SatisfiableExpanderCacheHandler>,
        sat_node_exp_cache_handler: Id<SaturationNodeExpansionCacheHandler>,
    ) -> &mut Self {
        self.task_processor_context = processor_context;
        self.concept_priority_strategy = Some(concept_priority_strategy.clone());
        self.individual_priority_strategy = Some(individual_priority_strategy.clone());
        self.task_priority_strategy = Some(task_priority_strategy.clone());
        self.unsat_cach_ret_strategy = Some(unsat_cach_ret_strategy.clone());
        self.indi_node_manager = indi_node_manager;
        self.clash_descriptor_factory = clash_descriptor_factory;
        self.dep_factory = dep_factory;
        self.unsat_cache_handler = unsat_cache_handler;
        self.sat_exp_cache_handler = sat_exp_cache_handler;
        self.sat_node_exp_cache_handler = sat_node_exp_cache_handler;

        self.base.used_task_processor_context = processor_context;
        self.base.used_concept_priority_strategy = Some(concept_priority_strategy);
        self.base.used_individual_priority_strategy = Some(individual_priority_strategy);
        self.base.used_task_priority_strategy = Some(task_priority_strategy);
        self.base.used_unsat_cach_ret_strategy = Some(unsat_cach_ret_strategy);
        self.base.used_individual_node_manager = indi_node_manager;
        self.base.used_clash_descriptor_factory = clash_descriptor_factory;
        self.base.used_dep_factory = dep_factory;
        self.base.used_unsat_cache_handler = unsat_cache_handler;
        self.base.used_sat_exp_cache_handler = sat_exp_cache_handler;
        self.base.used_sat_node_exp_cache_handler = sat_node_exp_cache_handler;
        self
    }

    /// Port of `getProcessingDataBox` — the owned databox lives in `base`.
    pub fn processing_data_box(&self) -> &ProcessingDataBox {
        &self.base.used_processing_data_box
    }
    /// Mutable owned-databox access.
    pub fn processing_data_box_mut(&mut self) -> &mut ProcessingDataBox {
        &mut self.base.used_processing_data_box
    }
    /// Port of `getProcessContext` — the owned container lives in `base`.
    pub fn process_context(&self) -> &ProcessContext {
        &self.base.used_process_context
    }
    /// Mutable owned process-context access.
    pub fn process_context_mut(&mut self) -> &mut ProcessContext {
        &mut self.base.used_process_context
    }

    /// Context-threaded port of
    /// `CProcessingDataBox::getNextSaturationResolvedSuccessorExtensionIndividualNodeID`.
    pub fn next_saturation_resolved_successor_extension_individual_node_id(
        &mut self,
        increment_next_id: bool,
    ) -> Cint64 {
        let ontology_individual_count = self.base.ontology_arenas.individual_count();
        let max_triples_indexed_individual_id = self
            .base
            .ontology_arenas
            .get_max_triples_indexed_individual_id();
        self.base
            .used_processing_data_box
            .next_saturation_resolved_successor_extension_individual_node_id_resolved(
                ontology_individual_count,
                Some(max_triples_indexed_individual_id),
                increment_next_id,
            )
    }

    /// Context-threaded port of
    /// `CProcessingDataBox::getSaturationSucessorExtensionIndividualNodeProcessingQueue`.
    pub fn saturation_sucessor_extension_individual_node_processing_queue(
        &mut self,
        create: bool,
    ) -> Id<
        super::super::process::sat_queue::SaturationSuccessorExtensionIndividualNodeProcessingQueue,
    > {
        let b = &mut self.base;
        b.used_processing_data_box
            .saturation_sucessor_extension_individual_node_processing_queue(
                &mut b.used_process_context,
                create,
            )
    }

    /// Context-threaded port of
    /// `CProcessingDataBox::getSaturationCriticalIndividualNodeProcessingQueue`.
    pub fn saturation_critical_individual_node_processing_queue(
        &mut self,
        create: bool,
    ) -> Id<super::super::process::sat_queue::CriticalIndividualNodeProcessingQueue> {
        let b = &mut self.base;
        b.used_processing_data_box
            .saturation_critical_individual_node_processing_queue(
                &mut b.used_process_context,
                create,
            )
    }

    /// Context-threaded port of
    /// `CProcessingDataBox::getSaturationCriticalIndividualNodeConceptTestSet`.
    pub fn saturation_critical_individual_node_concept_test_set(
        &mut self,
        create: bool,
    ) -> Id<super::super::process::sat_queue::CriticalIndividualNodeConceptTestSet> {
        let b = &mut self.base;
        b.used_processing_data_box
            .saturation_critical_individual_node_concept_test_set(
                &mut b.used_process_context,
                create,
            )
    }

    /// Context-threaded port of
    /// `CProcessingDataBox::getSaturationInfluencedNominalSet`.
    pub fn saturation_influenced_nominal_set(
        &mut self,
        create: bool,
    ) -> Id<super::super::process::sat_nominal::SaturationInfluencedNominalSet> {
        let b = &mut self.base;
        b.used_processing_data_box
            .saturation_influenced_nominal_set(&mut b.used_process_context, create)
    }

    /// Context-threaded port of
    /// `CProcessingDataBox::getSaturationNominalDependentNodeHash`.
    pub fn saturation_nominal_dependent_node_hash(
        &mut self,
        create: bool,
    ) -> Id<super::super::process::sat_nominal::SaturationNominalDependentNodeHash> {
        let b = &mut self.base;
        b.used_processing_data_box
            .saturation_nominal_dependent_node_hash(&mut b.used_process_context, create)
    }

    /// Context-threaded port of
    /// `CProcessingDataBox::getNodeSwitchHistory(create)`.
    pub fn node_switch_history(&mut self, create: bool) -> NodeSwitchHistoryId {
        let b = &mut self.base;
        b.used_process_context
            .processing_data_box_node_switch_history(&mut b.used_processing_data_box, create)
    }

    /// Context-threaded port of
    /// `CProcessingDataBox::getBranchingTree(create)`.
    pub fn branching_tree(
        &mut self,
        create: bool,
    ) -> super::super::process::branching_tree::BranchingTreeId {
        let b = &mut self.base;
        b.used_process_context
            .processing_data_box_branching_tree(&mut b.used_processing_data_box, create)
    }

    /// Open a branch epoch: arena journals + watermarks across the process
    /// context, plus a whole-databox snapshot. One epoch per ACTIVE OR
    /// alternative — popping restores the COMPLETE graph state to the push
    /// point (the in-process stand-in for Konclude's per-alternative task
    /// fork over a copy-on-write databox).
    pub fn push_branch_epoch(&mut self) {
        self.base.used_process_context.push_branch_epoch();
        self.databox_epoch_stack
            .push(self.base.used_processing_data_box.clone());
    }

    /// Close the innermost branch epoch (rollback).
    pub fn pop_branch_epoch(&mut self) {
        self.base.used_process_context.pop_branch_epoch();
        if let Some(db) = self.databox_epoch_stack.pop() {
            self.base.used_processing_data_box = db;
        }
        self.base
            .used_process_context
            .ht_check_dangling_satellites("pop_branch_epoch");
    }

    /// Lazily materialize the branching tree's INDEPENDENT base dependency
    /// node and return a (cached) deterministic track point on it.
    ///
    /// Konclude semantics: when dependency building is ON, nothing is ever
    /// untracked — base/seeded concept insertions carry the independent base
    /// dependency. An untracked clash descriptor is a tracking ERROR that
    /// aborts the whole `clashedBacktracking` analysis (measured on
    /// ore_ont_541: every clash closure carried one untracked seed partner,
    /// so no clash was ever analyzed and DDB never fired).
    pub fn get_or_create_base_dependency_track_point(&mut self) -> TrackPointId {
        if self.base_independent_track_point.is_some() {
            return self.base_independent_track_point;
        }
        let tree = self.branching_tree(true);
        let (dep, tp) = {
            let b = &mut self.base;
            let dep = b
                .used_process_context
                .branching_tree_base_dependency_node(tree, true);
            let tp = b
                .used_process_context
                .materialize_continue_dependency_track_point(dep);
            (dep, tp)
        };
        self.base_dep_node = dep;
        self.base.used_base_dep_node = dep;
        self.base_independent_track_point = tp;
        tp
    }

    /// Context-threaded port of
    /// `CProcessingDataBox::getSignatureBlockingCandidateHash(create)`.
    pub fn signature_blocking_candidate_hash(&mut self, create: bool) -> SigBlockCandHashId {
        let b = &mut self.base;
        b.used_process_context
            .processing_data_box_signature_blocking_candidate_hash(
                &mut b.used_processing_data_box,
                create,
            )
    }

    /// Context-threaded port of
    /// `CProcessingDataBox::getSignatureNominalDelayingCandidateHash(create)`.
    pub fn signature_nominal_delaying_candidate_hash(
        &mut self,
        create: bool,
    ) -> SigBlockCandHashId {
        let b = &mut self.base;
        b.used_process_context
            .processing_data_box_signature_nominal_delaying_candidate_hash(
                &mut b.used_processing_data_box,
                create,
            )
    }

    /// Context-threaded port of
    /// `CProcessingDataBox::getBlockingIndividualNodeCandidateHash(create)`.
    pub fn blocking_individual_node_candidate_hash(
        &mut self,
        create: bool,
    ) -> BlockingIndividualNodeCandidateHashId {
        let b = &mut self.base;
        b.used_process_context
            .processing_data_box_blocking_individual_node_candidate_hash(
                &mut b.used_processing_data_box,
                create,
            )
    }

    /// Context-threaded port of
    /// `CProcessingDataBox::getBlockingIndividualNodeLinkedCandidateHash(create)`.
    pub fn blocking_individual_node_linked_candidate_hash(
        &mut self,
        create: bool,
    ) -> BlockingIndividualNodeLinkedCandidateHashId {
        let b = &mut self.base;
        b.used_process_context
            .processing_data_box_blocking_individual_node_linked_candidate_hash(
                &mut b.used_processing_data_box,
                create,
            )
    }

    /// Port of the `handleTask` node-switch prologue for one individual:
    /// `incNodeSwitchTag`, `addIndividualProcessNodeSwitch`, and
    /// `setMinModificationIndividual`.
    pub fn add_node_switch_for_individual(&mut self, indi_node: NodeId) {
        let history = self.node_switch_history(true);
        let (ancestor_depth, individual_id, switch_tag) = {
            let pc = &mut self.base.used_process_context;
            pc.used_process_tagger_mut().inc_node_switch_tag();
            let switch_tag = pc.used_process_tagger().get_current_node_switch_tag();
            let node = pc.node(indi_node);
            (
                node.individual_ancestor_depth(),
                node.individual_node_id(),
                switch_tag,
            )
        };
        self.base
            .used_process_context
            .node_switch_history_mut(history)
            .add_individual_process_node_switch(ancestor_depth, individual_id, switch_tag);
        self.base.set_min_modification_individual(indi_node);
    }

    /// Port of the `handleTask` node-switch epilogue after one individual.
    pub fn update_latest_node_switch_from_min_modification(
        &mut self,
        history: NodeSwitchHistoryId,
    ) {
        if history.is_some() && self.base.is_min_modification_updated() {
            let ancestor_depth = self.base.min_modification_ancestor_depth();
            let individual_id = self.base.min_modification_individual_id();
            self.base
                .used_process_context
                .node_switch_history_mut(history)
                .update_last_individual_process_node_switch(ancestor_depth, individual_id);
        }
    }

    /// Port helper for the blocking callers of
    /// `CNodeSwitchHistory::getMinIndividualAncestorDepthAndNodeID`.
    pub fn node_switch_history_min_bounds(
        &self,
        history: NodeSwitchHistoryId,
        switch_tag: Cint64,
        min_node_floor: Cint64,
        min_depth_floor: Cint64,
    ) -> (Cint64, Cint64) {
        let (_, min_anc_depth, min_indi_id) = self
            .process_context()
            .node_switch_history(history)
            .get_min_individual_ancestor_depth_and_node_id(switch_tag);
        (
            min_indi_id.max(min_node_floor),
            min_anc_depth.max(min_depth_floor),
        )
    }

    /// Context-threaded port of
    /// `CProcessingDataBox::getMarkerIndividualNodeHash(true)`.
    pub fn marker_individual_node_hash(
        &mut self,
        create_or_force_localisation: bool,
    ) -> MarkerIndividualNodeHashId {
        let b = &mut self.base;
        b.used_process_context
            .processing_data_box_marker_individual_node_hash(
                &mut b.used_processing_data_box,
                create_or_force_localisation,
            )
    }

    /// Context-threaded port of
    /// `CProcessingDataBox::getRepresentativeVariableBindingPathSetHash(true)`.
    ///
    /// The databox stores the loc/use ids; `ProcessContext` owns the arena that
    /// allocates and init-copies the hash.
    pub fn representative_variable_binding_path_set_hash(
        &mut self,
        force_localisation: bool,
    ) -> RepresentativeVariableBindingPathSetHashId {
        if force_localisation
            && self
                .base
                .used_processing_data_box
                .loc_rep_var_bind_path_set_hash
                .is_none()
        {
            let prev = self
                .base
                .used_processing_data_box
                .use_rep_var_bind_path_set_hash;
            let new_id = self
                .base
                .used_process_context
                .alloc_rep_var_bind_path_set_hash(RepresentativeVariableBindingPathSetHash::new(
                    INVALID,
                ));
            if prev.is_some() {
                let taken = std::mem::replace(
                    self.base
                        .used_process_context
                        .rep_var_bind_path_set_hash_mut(prev),
                    RepresentativeVariableBindingPathSetHash::new(INVALID),
                );
                self.base
                    .used_process_context
                    .rep_var_bind_path_set_hash_mut(new_id)
                    .init_representative_variable_binding_path_set_hash(Some(&taken));
                *self
                    .base
                    .used_process_context
                    .rep_var_bind_path_set_hash_mut(prev) = taken;
            } else {
                self.base
                    .used_process_context
                    .rep_var_bind_path_set_hash_mut(new_id)
                    .init_representative_variable_binding_path_set_hash(None);
            }
            self.base
                .used_processing_data_box
                .loc_rep_var_bind_path_set_hash = new_id;
            self.base
                .used_processing_data_box
                .use_rep_var_bind_path_set_hash = new_id;
        }
        self.base
            .used_processing_data_box
            .use_rep_var_bind_path_set_hash
    }

    /// Context-threaded port of
    /// `CProcessingDataBox::getRepresentativeVariableBindingPathJoiningKeyHash(true)`.
    pub fn representative_variable_binding_path_joining_key_hash(
        &mut self,
        force_localisation: bool,
    ) -> RepresentativeVariableBindingPathJoiningKeyHashId {
        if force_localisation
            && self
                .base
                .used_processing_data_box
                .loc_rep_var_bind_path_joining_key_hash
                .is_none()
        {
            let prev = self
                .base
                .used_processing_data_box
                .use_rep_var_bind_path_joining_key_hash;
            let new_id = self
                .base
                .used_process_context
                .alloc_rep_var_bind_path_joining_key_hash(
                    RepresentativeVariableBindingPathJoiningKeyHash::new(INVALID),
                );
            if prev.is_some() {
                let taken = std::mem::replace(
                    self.base
                        .used_process_context
                        .rep_var_bind_path_joining_key_hash_mut(prev),
                    RepresentativeVariableBindingPathJoiningKeyHash::new(INVALID),
                );
                self.base
                    .used_process_context
                    .rep_var_bind_path_joining_key_hash_mut(new_id)
                    .init_representative_variable_binding_path_joining_key_hash(Some(&taken));
                *self
                    .base
                    .used_process_context
                    .rep_var_bind_path_joining_key_hash_mut(prev) = taken;
            } else {
                self.base
                    .used_process_context
                    .rep_var_bind_path_joining_key_hash_mut(new_id)
                    .init_representative_variable_binding_path_joining_key_hash(None);
            }
            self.base
                .used_processing_data_box
                .loc_rep_var_bind_path_joining_key_hash = new_id;
            self.base
                .used_processing_data_box
                .use_rep_var_bind_path_joining_key_hash = new_id;
        }
        self.base
            .used_processing_data_box
            .use_rep_var_bind_path_joining_key_hash
    }

    /// Context-threaded port of
    /// `CProcessingDataBox::getRepresentativeJoiningHash(true)`.
    pub fn representative_joining_hash(
        &mut self,
        force_localisation: bool,
    ) -> RepresentativeJoiningHashId {
        if force_localisation
            && self
                .base
                .used_processing_data_box
                .loc_rep_joining_hash
                .is_none()
        {
            let prev = self.base.used_processing_data_box.use_rep_joining_hash;
            let new_id = self
                .base
                .used_process_context
                .alloc_rep_joining_hash(RepresentativeJoiningHash::new(INVALID));
            if prev.is_some() {
                let taken = std::mem::replace(
                    self.base.used_process_context.rep_joining_hash_mut(prev),
                    RepresentativeJoiningHash::new(INVALID),
                );
                self.base
                    .used_process_context
                    .rep_joining_hash_mut(new_id)
                    .init_representative_joining_hash(Some(&taken));
                *self.base.used_process_context.rep_joining_hash_mut(prev) = taken;
            } else {
                self.base
                    .used_process_context
                    .rep_joining_hash_mut(new_id)
                    .init_representative_joining_hash(None);
            }
            self.base.used_processing_data_box.loc_rep_joining_hash = new_id;
            self.base.used_processing_data_box.use_rep_joining_hash = new_id;
        }
        self.base.used_processing_data_box.use_rep_joining_hash
    }
    // --- processing-queue getter forwarders ---------------------------------
    // The db3 `getXxx(create)` allocation site needs BOTH the databox (the
    // `mX`/`mUseX`/`mPrev` triple) AND the `ProcessContext` queue arena. Both are
    // disjoint fields of `base`, so these forwarders destructure `base` and hand
    // the db getter `&mut used_process_context`. Callers that previously wrote
    // `ctx.processing_data_box_mut().get_X(create)` now write `ctx.get_X(create)`.
    db_queue_forward!(
        get_individual_immediately_processing_queue,
        Id<IndividualUnsortedProcessingQueue>
    );
    db_queue_forward!(individual_processing_queue, Id<IndividualProcessingQueue>);
    db_queue_forward!(
        get_individual_depth_first_processing_queue,
        Id<IndividualUnsortedProcessingQueue>
    );
    db_queue_forward!(
        get_role_assertion_expansion_processing_queue,
        Id<IndividualUnsortedProcessingQueue>
    );
    db_queue_forward!(
        get_backend_cache_synchronization_processing_queue,
        Id<IndividualUnsortedProcessingQueue>
    );
    db_queue_forward!(
        get_backend_direct_influence_expansion_queue,
        Id<IndividualUnsortedProcessingQueue>
    );
    db_queue_forward!(
        get_backend_indirect_compatibility_expansion_queue,
        Id<IndividualUnsortedProcessingQueue>
    );
    db_queue_forward!(
        get_backend_individual_reuse_expansion_queue,
        Id<IndividualUnsortedProcessingQueue>
    );
    db_queue_forward!(
        get_backend_late_individual_neighbour_expansion_queue,
        Id<IndividualUnsortedProcessingQueue>
    );
    db_queue_forward!(
        get_delaying_nominal_processing_queue,
        Id<IndividualUnsortedProcessingQueue>
    );
    db_queue_forward!(
        get_nominal_caching_loss_reactivation_processing_queue,
        Id<IndividualUnsortedProcessingQueue>
    );
    db_queue_forward!(
        get_individual_depth_first_deterministic_expansion_processing_queue,
        Id<IndividualUnsortedProcessingQueue>
    );
    db_queue_forward!(
        get_backend_individual_neighbour_expansion_queue,
        Id<IndividualLinkerRotationProcessingQueue>
    );
    db_queue_forward!(
        get_variable_binding_concept_batch_processing_queue,
        Id<IndividualConceptBatchProcessingQueue>
    );
    db_queue_forward!(
        get_individual_depth_processing_queue,
        Id<IndividualDepthProcessingQueue>
    );
    db_queue_forward!(
        get_nominal_deterministic_processing_queue,
        Id<IndividualDepthProcessingQueue>
    );
    db_queue_forward!(
        get_nominal_processing_queue,
        Id<IndividualDepthProcessingQueue>
    );
    db_queue_forward!(
        get_incremental_expansion_initializing_processing_queue,
        Id<IndividualDepthProcessingQueue>
    );
    db_queue_forward!(
        get_incremental_expansion_processing_queue,
        Id<IndividualCustomPriorityProcessingQueue>
    );
    db_queue_forward!(
        get_incremental_compatibility_checking_queue,
        Id<IndividualDepthProcessingQueue>
    );
    db_queue_forward!(
        get_individual_depth_deterministic_expansion_preprocessing_queue,
        Id<IndividualDepthProcessingQueue>
    );
    db_queue_forward!(
        get_blocking_update_review_processing_queue,
        Id<IndividualDepthProcessingQueue>
    );
    db_queue_forward!(
        get_blocked_reactivation_processing_queue,
        Id<IndividualDepthProcessingQueue>
    );
    db_queue_forward!(
        get_value_space_triggering_processing_queue,
        Id<IndividualDepthProcessingQueue>
    );
    db_queue_forward!(
        get_distinct_value_space_satisfiability_checking_queue,
        Id<IndividualDepthProcessingQueue>
    );
    db_queue_forward!(
        early_individual_reactivation_processing_queue,
        Id<IndividualReactivationProcessingQueue>
    );
    db_queue_forward!(
        late_individual_reactivation_processing_queue,
        Id<IndividualReactivationProcessingQueue>
    );
    db_queue_forward!(
        signature_blocking_review_set,
        Id<SignatureBlockingReviewSet>
    );
    db_queue_forward!(reusing_review_data, Id<ReusingReviewData>);
    db_queue_forward!(
        backend_neighbour_expansion_controlling_data,
        Id<BackendNeighbourExpansionControllingData>
    );

    /// The static terminology arenas (live in `base`).
    pub fn ontology_arenas(&self) -> &OntologyArenas {
        &self.base.ontology_arenas
    }
    /// Mutable terminology access.
    pub fn ontology_arenas_mut(&mut self) -> &mut OntologyArenas {
        &mut self.base.ontology_arenas
    }

    /// Borrow the mutable per-probe graph and immutable ontology together.
    ///
    /// Konclude passes both as independent raw pointers. Rust callers that port
    /// those methods need this explicit split over the two disjoint `base`
    /// fields instead of borrowing the complete calculation context twice.
    pub fn process_context_and_ontology(&mut self) -> (&mut ProcessContext, &OntologyArenas) {
        let base = &mut self.base;
        (&mut base.used_process_context, &base.ontology_arenas)
    }

    /// Disjoint borrow helper for
    /// `CIndividualConceptBatchProcessingQueue::takeNextConceptProcessIndividual`.
    pub fn take_next_variable_binding_concept_batch_process_individual(
        &mut self,
        qid: Id<IndividualConceptBatchProcessingQueue>,
    ) -> Option<(
        super::super::model::ConceptId,
        NodeId,
        super::super::process::ConProcDescId,
    )> {
        let base = &mut self.base;
        base.used_process_context
            .indi_concept_batch_queue_take_next(qid, &base.ontology_arenas)
    }
    /// Live occurrence-statistics cache handler.
    pub fn occurrence_statistics_cache_handler(&self) -> &OccurrenceStatisticsCacheHandler {
        &self.occurrence_statistics_cache_handler
    }
    /// Mutable live occurrence-statistics cache handler.
    pub fn occurrence_statistics_cache_handler_mut(
        &mut self,
    ) -> &mut OccurrenceStatisticsCacheHandler {
        &mut self.occurrence_statistics_cache_handler
    }
    /// Install a live port-owned `CUnsatisfiableCacheHandler` target for this
    /// calculation context.
    pub fn install_used_unsatisfiable_cache_handler(
        &mut self,
        handler: UnsatisfiableCacheHandler,
        cache_context: CacheContext,
    ) -> Id<UnsatisfiableCacheHandler> {
        let handler_id = self
            .base
            .install_used_unsatisfiable_cache_handler(handler, cache_context);
        self.unsat_cache_handler = handler_id;
        handler_id
    }
    /// Temporarily move out the live unsat-cache handler target.
    pub fn take_used_unsatisfiable_cache_handler(
        &mut self,
    ) -> Option<UsedUnsatisfiableCacheHandlerState> {
        self.base.take_used_unsatisfiable_cache_handler()
    }
    /// Restore a handler target after `take_used_unsatisfiable_cache_handler`.
    pub fn restore_used_unsatisfiable_cache_handler(
        &mut self,
        state: UsedUnsatisfiableCacheHandlerState,
    ) {
        self.base.restore_used_unsatisfiable_cache_handler(state);
        self.unsat_cache_handler = self.base.used_unsat_cache_handler;
    }
    /// Install the live satisfiable-expander cache handler for this context.
    pub fn install_used_satisfiable_expander_cache_handler(
        &mut self,
        handler: SatisfiableExpanderCacheHandler,
    ) -> Id<SatisfiableExpanderCacheHandler> {
        let handler_id = self
            .base
            .install_used_satisfiable_expander_cache_handler(handler);
        self.sat_exp_cache_handler = handler_id;
        handler_id
    }
    /// Temporarily move out the live satisfiable-expander handler target.
    pub fn take_used_satisfiable_expander_cache_handler(
        &mut self,
    ) -> Option<UsedSatisfiableExpanderCacheHandlerState> {
        self.base.take_used_satisfiable_expander_cache_handler()
    }
    /// Restore a handler target after
    /// `take_used_satisfiable_expander_cache_handler`.
    pub fn restore_used_satisfiable_expander_cache_handler(
        &mut self,
        state: UsedSatisfiableExpanderCacheHandlerState,
    ) {
        self.base
            .restore_used_satisfiable_expander_cache_handler(state);
        self.sat_exp_cache_handler = self.base.used_sat_exp_cache_handler;
    }
    /// Install a live port-owned `CSaturationNodeExpansionCacheHandler` target for
    /// this calculation context.
    pub fn install_used_saturation_node_expansion_cache_handler(
        &mut self,
        handler: SaturationNodeExpansionCacheHandler,
        cache_context: CacheContext,
    ) -> Id<SaturationNodeExpansionCacheHandler> {
        let handler_id = self
            .base
            .install_used_saturation_node_expansion_cache_handler(handler, cache_context);
        self.sat_node_exp_cache_handler = handler_id;
        handler_id
    }
    /// Temporarily move out the live saturation-node expansion handler target.
    pub fn take_used_saturation_node_expansion_cache_handler(
        &mut self,
    ) -> Option<UsedSaturationNodeExpansionCacheHandlerState> {
        self.base
            .take_used_saturation_node_expansion_cache_handler()
    }
    /// Restore a handler target after `take_used_saturation_node_expansion_cache_handler`.
    pub fn restore_used_saturation_node_expansion_cache_handler(
        &mut self,
        state: UsedSaturationNodeExpansionCacheHandlerState,
    ) {
        self.base
            .restore_used_saturation_node_expansion_cache_handler(state);
        self.sat_node_exp_cache_handler = self.base.used_sat_node_exp_cache_handler;
    }
    /// Install a live port-owned `CComputedConsequencesCacheHandler` target for
    /// this calculation context.
    pub fn install_used_computed_consequences_cache_handler(
        &mut self,
        handler: ComputedConsequencesCacheHandler,
    ) -> Id<ComputedConsequencesCacheHandler> {
        let handler_id = self
            .base
            .install_used_computed_consequences_cache_handler(handler);
        self.comp_cons_cache_handler = handler_id;
        handler_id
    }
    /// Temporarily move out the live computed-consequences handler target.
    pub fn take_used_computed_consequences_cache_handler(
        &mut self,
    ) -> Option<UsedComputedConsequencesCacheHandlerState> {
        self.base.take_used_computed_consequences_cache_handler()
    }
    /// Restore a handler target after `take_used_computed_consequences_cache_handler`.
    pub fn restore_used_computed_consequences_cache_handler(
        &mut self,
        state: UsedComputedConsequencesCacheHandlerState,
    ) {
        self.base
            .restore_used_computed_consequences_cache_handler(state);
        self.comp_cons_cache_handler = Id::new(0);
    }
    /// Port of `getBranchTreeNode`.
    pub fn branch_tree_node(&self) -> BranchNodeId {
        self.branch_tree_node
    }
    /// Port of `getNewBranchTreeNode`.
    pub fn get_new_branch_tree_node(&mut self) -> BranchNodeId {
        let branching_tree = self.branching_tree(true);
        let branch_tree_node = self
            .base
            .used_process_context
            .branching_tree_branch_tree_node(branching_tree, self.sat_calc_task.raw, true);
        self.branch_tree_node = branch_tree_node;
        self.base.used_branch_tree_node = branch_tree_node;
        branch_tree_node
    }
    /// Port of `getBaseDependencyNode`.
    pub fn base_dependency_node(&self) -> DependencyId {
        self.base_dep_node
    }

    /// Forwarder for `satCalcTask->getSatisfiableTaskIncrementalConsistencyTestingAdapter()`
    /// (the task-resolution arena lives in `base`).
    pub fn satisfiable_task_incremental_consistency_testing_adapter(
        &self,
        sat_calc_task: Id<SatisfiableCalculationTask>,
    ) -> Id<SatisfiableTaskIncrementalConsistencyTestingAdapter> {
        self.base
            .satisfiable_task_incremental_consistency_testing_adapter(sat_calc_task)
    }
    /// Resolve an incremental-consistency adapter id (forwarder).
    pub fn inc_cons_testing_adapter(
        &self,
        id: Id<SatisfiableTaskIncrementalConsistencyTestingAdapter>,
    ) -> &SatisfiableTaskIncrementalConsistencyTestingAdapter {
        self.base.inc_cons_testing_adapter(id)
    }
    /// Forwarder for `satCalcTask->getClassificationMessageAdapter()`.
    pub fn satisfiable_task_classification_message_adapter(
        &self,
        sat_calc_task: Id<SatisfiableCalculationTask>,
    ) -> Id<SatisfiableTaskClassificationMessageAdapter> {
        self.base
            .satisfiable_task_classification_message_adapter(sat_calc_task)
    }
    /// Resolve a classification message adapter id (forwarder).
    pub fn classification_message_adapter(
        &self,
        id: Id<SatisfiableTaskClassificationMessageAdapter>,
    ) -> &SatisfiableTaskClassificationMessageAdapter {
        self.base.classification_message_adapter(id)
    }
}

impl Default for CalculationAlgorithmContextBase {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod context_init_tests {
    use crate::konclude_ht::model::individual::Individual;
    use crate::konclude_ht::process::node::IndividualProcessNode;
    use crate::konclude_ht::process::sat_node::IndividualSaturationProcessNode;
    use crate::konclude_ht::process::stubs::{NodeSwitchHistory, ProcessContextId};

    use super::*;

    #[test]
    fn init_task_process_context_copies_task_and_databox_alias() {
        let mut ctx = CalculationAlgorithmContextBase::new();
        let mut task = SatisfiableCalculationTask::new();
        task.processing_data_box = 42;
        let task_id = ctx.base.alloc_sat_calc_task(task);

        ctx.init_task_process_context(7, task_id);

        assert_eq!(ctx.process_context, 7);
        assert_eq!(ctx.sat_calc_task, task_id);
        assert_eq!(ctx.base.used_sat_calc_task, task_id);
        assert_eq!(ctx.processing_data_box, 42);
    }

    #[test]
    fn init_task_process_context_initializes_branch_tree_and_base_dependency() {
        let mut ctx = CalculationAlgorithmContextBase::new();
        let task_id = ctx
            .base
            .alloc_sat_calc_task(SatisfiableCalculationTask::new());

        ctx.init_task_process_context(7, task_id);

        let branch_tree = ctx.processing_data_box().use_branching_tree;
        assert!(branch_tree.is_some());
        assert_eq!(ctx.branch_tree_node, ctx.base.used_branch_tree_node());
        assert_eq!(
            ctx.branch_tree_node,
            ctx.process_context().branching_tree(branch_tree).curr_node
        );
        assert_eq!(
            ctx.process_context()
                .branch_node(ctx.branch_tree_node)
                .get_satisfiable_calculation_task(),
            task_id.raw
        );
        assert_eq!(ctx.base_dep_node, ctx.base.used_base_dependency_node());
        assert_eq!(
            ctx.process_context()
                .branching_tree(branch_tree)
                .base_dep_node,
            ctx.base_dep_node
        );
        assert!(ctx
            .process_context()
            .dep_node(ctx.base_dep_node)
            .is_independent_base_dependency_type());
    }

    #[test]
    fn init_task_process_context_keeps_external_task_id_unresolved() {
        let mut ctx = CalculationAlgorithmContextBase::new();
        let external_task = Id::<SatisfiableCalculationTask>::new(3);

        ctx.init_task_process_context(11, external_task);

        assert_eq!(ctx.process_context, 11);
        assert_eq!(ctx.sat_calc_task, external_task);
        assert_eq!(ctx.base.used_sat_calc_task, external_task);
        assert_eq!(ctx.processing_data_box, INVALID);
    }

    #[test]
    fn init_calculation_algorithm_context_copies_strategy_factory_cache_handles() {
        let mut ctx = CalculationAlgorithmContextBase::new();
        let concept_strategy = ConceptProcessingPriorityStrategy::new_concrete_operator();
        let individual_strategy =
            IndividualProcessingPriorityStrategy::new_ancestor_depth_maximum();
        let task_strategy = TaskProcessingPriorityStrategy::new_equal_depth_cache_orientated();
        let unsat_retrieval =
            UnsatisfiableCacheRetrievalStrategy::new_generative_non_deterministic();
        let node_manager = Id::<IndividualNodeManager>::new(5);
        let clash_factory = Id::<ClashDescriptorFactory>::new(6);
        let dep_factory = Id::<DependencyFactory>::new(7);
        let unsat_cache = Id::<UnsatisfiableCacheHandler>::new(8);
        let sat_exp_cache = Id::<SatisfiableExpanderCacheHandler>::new(9);
        let sat_node_exp_cache = Id::<SaturationNodeExpansionCacheHandler>::new(10);

        ctx.init_calculation_algorithm_context(
            101,
            concept_strategy,
            individual_strategy,
            task_strategy,
            unsat_retrieval,
            node_manager,
            clash_factory,
            dep_factory,
            unsat_cache,
            sat_exp_cache,
            sat_node_exp_cache,
        );

        assert_eq!(ctx.task_processor_context, 101);
        assert!(matches!(
            ctx.concept_priority_strategy,
            Some(ConceptProcessingPriorityStrategy::ConcreteOperator(_))
        ));
        assert!(matches!(
            ctx.individual_priority_strategy,
            Some(IndividualProcessingPriorityStrategy::AncestorDepthMaximum(
                _
            ))
        ));
        assert!(matches!(
            ctx.task_priority_strategy,
            Some(TaskProcessingPriorityStrategy::EqualDepthCacheOrientated(_))
        ));
        assert!(matches!(
            ctx.unsat_cach_ret_strategy,
            Some(UnsatisfiableCacheRetrievalStrategy::GenerativeNonDeterministic(_))
        ));
        assert_eq!(ctx.indi_node_manager, node_manager);
        assert_eq!(ctx.clash_descriptor_factory, clash_factory);
        assert_eq!(ctx.dep_factory, dep_factory);
        assert_eq!(ctx.unsat_cache_handler, unsat_cache);
        assert_eq!(ctx.sat_exp_cache_handler, sat_exp_cache);
        assert_eq!(ctx.sat_node_exp_cache_handler, sat_node_exp_cache);

        assert_eq!(ctx.base.used_task_processor_context, 101);
        assert!(matches!(
            ctx.base.used_concept_priority_strategy,
            Some(ConceptProcessingPriorityStrategy::ConcreteOperator(_))
        ));
        assert!(matches!(
            ctx.base.used_concept_priority_strategy(),
            Some(ConceptProcessingPriorityStrategy::ConcreteOperator(_))
        ));
        assert!(matches!(
            ctx.base.used_individual_priority_strategy,
            Some(IndividualProcessingPriorityStrategy::AncestorDepthMaximum(
                _
            ))
        ));
        assert!(matches!(
            ctx.base.used_individual_priority_strategy(),
            Some(IndividualProcessingPriorityStrategy::AncestorDepthMaximum(
                _
            ))
        ));
        assert!(matches!(
            ctx.base.used_task_priority_strategy,
            Some(TaskProcessingPriorityStrategy::EqualDepthCacheOrientated(_))
        ));
        assert!(matches!(
            ctx.base.used_task_priority_strategy(),
            Some(TaskProcessingPriorityStrategy::EqualDepthCacheOrientated(_))
        ));
        assert!(matches!(
            ctx.base.used_unsat_cach_ret_strategy,
            Some(UnsatisfiableCacheRetrievalStrategy::GenerativeNonDeterministic(_))
        ));
        assert!(matches!(
            ctx.base.used_unsatisfiable_cache_retrieval_strategy(),
            Some(UnsatisfiableCacheRetrievalStrategy::GenerativeNonDeterministic(_))
        ));
        assert_eq!(ctx.base.used_individual_node_manager, node_manager);
        assert_eq!(ctx.base.used_clash_descriptor_factory, clash_factory);
        assert_eq!(ctx.base.used_dep_factory, dep_factory);
        assert_eq!(ctx.base.used_unsat_cache_handler, unsat_cache);
        assert_eq!(ctx.base.used_sat_exp_cache_handler, sat_exp_cache);
        assert_eq!(ctx.base.used_sat_node_exp_cache_handler, sat_node_exp_cache);
    }

    #[test]
    fn node_switch_forwarders_mirror_handle_task_switch_sequence() {
        let mut ctx = CalculationAlgorithmContextBase::new();
        let node = ctx
            .process_context_mut()
            .alloc_node(IndividualProcessNode::new(ProcessContextId::NONE));
        ctx.process_context_mut()
            .node_mut(node)
            .set_individual_node_id(42)
            .set_individual_ancestor_depth(7);

        let history = ctx.node_switch_history(true);
        ctx.add_node_switch_for_individual(node);

        assert_eq!(
            ctx.process_context()
                .used_process_tagger()
                .get_current_node_switch_tag(),
            1
        );
        assert_eq!(ctx.base.min_modification_individual_id(), 42);
        assert_eq!(ctx.base.min_modification_ancestor_depth(), 7);
        assert!(!ctx.base.is_min_modification_updated());
        assert_eq!(
            ctx.process_context()
                .node_switch_history(history)
                .get_min_individual_ancestor_depth_and_node_id(0),
            (true, 7, 42)
        );

        ctx.base.min_modification_ancestor_depth = 3;
        ctx.base.min_modification_individual_id = 12;
        ctx.base.min_modification_updated = true;
        ctx.update_latest_node_switch_from_min_modification(history);

        assert_eq!(
            ctx.process_context()
                .node_switch_history(history)
                .get_min_individual_ancestor_depth_and_node_id(0),
            (true, 3, 12)
        );
    }

    #[test]
    fn get_new_branch_tree_node_forces_creation_through_branching_tree() {
        let mut ctx = CalculationAlgorithmContextBase::new();
        let task_id = ctx
            .base
            .alloc_sat_calc_task(SatisfiableCalculationTask::new());
        ctx.init_task_process_context(7, task_id);
        let branch_tree = ctx.processing_data_box().use_branching_tree;
        let root = ctx.branch_tree_node();

        let forced = ctx.get_new_branch_tree_node();

        assert_ne!(forced, root);
        assert_eq!(ctx.branch_tree_node(), forced);
        assert_eq!(ctx.base.used_branch_tree_node(), forced);
        assert_eq!(
            ctx.process_context().branching_tree(branch_tree).curr_node,
            forced
        );
        assert_eq!(
            ctx.process_context().branch_node(forced).parent_node(),
            root
        );
        assert_eq!(
            ctx.process_context().branch_node(forced).get_root_node(),
            root
        );
        assert_eq!(
            ctx.process_context()
                .branch_node(forced)
                .get_satisfiable_calculation_task(),
            task_id.raw
        );
    }

    #[test]
    fn node_switch_history_min_bounds_applies_konclude_flooring() {
        let mut ctx = CalculationAlgorithmContextBase::new();
        let mut history = NodeSwitchHistory::new(INVALID);
        history
            .add_individual_process_node_switch(4, 8, 1)
            .add_individual_process_node_switch(2, 5, 3);
        let history = ctx.process_context_mut().alloc_node_switch_history(history);

        assert_eq!(ctx.node_switch_history_min_bounds(history, 1, 0, 0), (5, 2));
        assert_eq!(
            ctx.node_switch_history_min_bounds(history, 3, 1, 0),
            (Cint64::MAX, Cint64::MAX)
        );
    }

    #[test]
    fn next_saturation_resolved_successor_extension_id_uses_resolved_ontology_counts() {
        let mut ctx = CalculationAlgorithmContextBase::new();
        assert_eq!(
            ctx.processing_data_box()
                .next_sat_res_succ_ext_individual_node_id,
            -1
        );
        ctx.processing_data_box_mut()
            .individual_saturation_process_node_vector(true)
            .expect("create=true yields CIndividualSaturationProcessNodeVector")
            .set_data(2, Id::new(0));
        ctx.ontology_arenas_mut()
            .alloc_individual(Individual::new(0));
        ctx.ontology_arenas_mut()
            .alloc_individual(Individual::new(1));
        ctx.ontology_arenas_mut()
            .set_max_triples_indexed_individual_id(8);

        assert_eq!(
            ctx.next_saturation_resolved_successor_extension_individual_node_id(false),
            8
        );
        assert_eq!(
            ctx.next_saturation_resolved_successor_extension_individual_node_id(true),
            8
        );
        assert_eq!(
            ctx.next_saturation_resolved_successor_extension_individual_node_id(false),
            9
        );
    }

    #[test]
    fn saturation_successor_extension_queue_forwarder_allocates_and_reports_work() {
        let mut ctx = CalculationAlgorithmContextBase::new();

        assert_eq!(
            ctx.saturation_sucessor_extension_individual_node_processing_queue(false),
            Id::NONE
        );
        let queue = ctx.saturation_sucessor_extension_individual_node_processing_queue(true);
        assert!(queue.is_some());
        assert_eq!(
            ctx.saturation_sucessor_extension_individual_node_processing_queue(true),
            queue
        );
        assert!(ctx
            .process_context()
            .sat_succ_ext_ind_node_proc_queue(queue)
            .is_empty());

        let sat_node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(17));
        ctx.process_context_mut()
            .sat_succ_ext_ind_node_proc_queue_mut(queue)
            .insert_process_individual(sat_node, 17);

        assert!(!ctx
            .process_context()
            .sat_succ_ext_ind_node_proc_queue(queue)
            .is_empty());
    }

    #[test]
    fn saturation_critical_individual_queue_forwarder_allocates_and_reports_work() {
        let mut ctx = CalculationAlgorithmContextBase::new();

        assert_eq!(
            ctx.saturation_critical_individual_node_processing_queue(false),
            Id::NONE
        );
        let queue = ctx.saturation_critical_individual_node_processing_queue(true);
        assert!(queue.is_some());
        assert_eq!(
            ctx.saturation_critical_individual_node_processing_queue(true),
            queue
        );
        assert!(ctx
            .process_context()
            .sat_critical_ind_node_proc_queue(queue)
            .is_empty());

        let sat_node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(19));
        ctx.process_context_mut()
            .sat_critical_ind_node_proc_queue_mut(queue)
            .insert_process_individual(sat_node, 19);

        assert!(!ctx
            .process_context()
            .sat_critical_ind_node_proc_queue(queue)
            .is_empty());
    }

    #[test]
    fn saturation_critical_individual_node_concept_test_set_forwarder_tracks_pairs() {
        let mut ctx = CalculationAlgorithmContextBase::new();

        assert_eq!(
            ctx.saturation_critical_individual_node_concept_test_set(false),
            Id::NONE
        );
        let set = ctx.saturation_critical_individual_node_concept_test_set(true);
        assert!(set.is_some());
        assert_eq!(
            ctx.saturation_critical_individual_node_concept_test_set(true),
            set
        );

        let sat_node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(29));
        let concept = crate::konclude_ht::model::ConceptId::new(31);
        assert!(!ctx
            .process_context()
            .sat_critical_ind_node_con_test_set(set)
            .is_concept_tested_for_individual(concept, sat_node));

        ctx.process_context_mut()
            .sat_critical_ind_node_con_test_set_mut(set)
            .insert_concept_tested_for_individual(concept, sat_node);

        assert!(ctx
            .process_context()
            .sat_critical_ind_node_con_test_set(set)
            .is_concept_tested_for_individual(concept, sat_node));
    }

    #[test]
    fn saturation_influenced_nominal_set_forwarder_allocates_and_tracks_membership() {
        let mut ctx = CalculationAlgorithmContextBase::new();

        assert_eq!(ctx.saturation_influenced_nominal_set(false), Id::NONE);
        let set = ctx.saturation_influenced_nominal_set(true);
        assert!(set.is_some());
        assert_eq!(ctx.saturation_influenced_nominal_set(true), set);
        assert!(!ctx
            .process_context()
            .sat_influenced_nominal_set(set)
            .is_nominal_influenced(23));

        assert!(ctx
            .process_context_mut()
            .sat_influenced_nominal_set_mut(set)
            .set_nominal_influenced(23));

        assert!(ctx
            .process_context()
            .sat_influenced_nominal_set(set)
            .is_nominal_influenced(23));
    }

    #[test]
    fn saturation_nominal_dependent_node_hash_forwarder_allocates_and_prepends() {
        let mut ctx = CalculationAlgorithmContextBase::new();

        assert_eq!(ctx.saturation_nominal_dependent_node_hash(false), Id::NONE);
        let hash = ctx.saturation_nominal_dependent_node_hash(true);
        assert!(hash.is_some());
        assert_eq!(ctx.saturation_nominal_dependent_node_hash(true), hash);

        let first = ctx
            .process_context_mut()
            .sat_nominal_dependent_node_hash_add_nominal_dependent_node(
            hash,
            5,
            Id::new(1),
            crate::konclude_ht::process::stubs::SaturationNominalConnectionType::ValueConnection,
        );
        let second = ctx
            .process_context_mut()
            .sat_nominal_dependent_node_hash_add_nominal_dependent_node(
            hash,
            5,
            Id::new(2),
            crate::konclude_ht::process::stubs::SaturationNominalConnectionType::NominalConnection,
        );

        assert_eq!(
            ctx.process_context()
                .sat_nominal_dependent_node_hash(hash)
                .get_nominal_dependent_node_data(5),
            second
        );
        assert_eq!(
            ctx.process_context()
                .sat_nominal_dependent_node_data(second)
                .get_next_nominal_connection_type_data(),
            first
        );
    }
}
