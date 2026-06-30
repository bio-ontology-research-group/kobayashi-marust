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

use super::super::model::ontology::OntologyArenas;
use super::super::model::substrate::{Arena, Cint64, Id, INVALID};
use super::super::process::context::ProcessContext;
use super::super::task::adapters::SatisfiableTaskIncrementalConsistencyTestingAdapter;
use super::super::process::databox::ProcessingDataBox;
use super::super::process::{BranchNodeId, DependencyId, NodeId};
use super::clash::CalcSignal;
use super::stubs::{
    ClashDescriptorFactory, ConceptProcessingPriorityStrategy, DependencyFactory,
    IndividualNodeManager, IndividualProcessingPriorityStrategy, ProcessTagger,
    ProcessingStatisticGathering, SatisfiableCalculationTask, SatisfiableExpanderCacheHandler,
    SaturationNodeExpansionCacheHandler, TaskProcessingPriorityStrategy, UnsatisfiableCacheHandler,
    UnsatisfiableCacheRetrievalStrategy,
};

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
    pub used_concept_priority_strategy: Id<ConceptProcessingPriorityStrategy>,
    /// `CIndividualProcessingPriorityStrategy* mUsedIndividualPriorityStrategy`.
    pub used_individual_priority_strategy: Id<IndividualProcessingPriorityStrategy>,
    /// `CProcessingDataBox* mUsedProcessingDataBox` — the OWNED per-test state box.
    pub used_processing_data_box: ProcessingDataBox,
    /// `CSatisfiableCalculationTask* mUsedSatCalcTask`.
    pub used_sat_calc_task: Id<SatisfiableCalculationTask>,
    /// `CTaskProcessorContext* mUsedTaskProcessorContext`. [api] opaque (scheduler).
    pub used_task_processor_context: Cint64,
    /// `CTaskProcessingPriorityStrategy* mUsedTaskPriorityStrategy`.
    pub used_task_priority_strategy: Id<TaskProcessingPriorityStrategy>,
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
    /// `CIndividualNodeManager* mUsedIndividualNodeManager`.
    pub used_individual_node_manager: Id<IndividualNodeManager>,
    /// `CClashDescriptorFactory* mUsedClashDescriptorFactory`.
    pub used_clash_descriptor_factory: Id<ClashDescriptorFactory>,
    /// `CUnsatisfiableCacheRetrievalStrategy* mUsedUnsatCachRetStrategy`.
    pub used_unsat_cach_ret_strategy: Id<UnsatisfiableCacheRetrievalStrategy>,
    /// `CDependencyFactory* mUsedDepFactory`.
    pub used_dep_factory: Id<DependencyFactory>,
    /// `CSatisfiableExpanderCacheHandler* mUsedSatExpCacheHandler`.
    pub used_sat_exp_cache_handler: Id<SatisfiableExpanderCacheHandler>,
    /// `cint64 mMaxCompletionGraphCachedIndiNodeID`.
    pub max_completion_graph_cached_indi_node_id: Cint64,
    /// `CIndividualProcessNode* mCurrentIndiNode`.
    pub current_indi_node: NodeId,
    /// `cint64 mCompletionGraphCachedLocalizationTag`.
    pub completion_graph_cached_localization_tag: Cint64,
    /// `CSaturationNodeExpansionCacheHandler* mUsedSatNodeExpCacheHandler`.
    pub used_sat_node_exp_cache_handler: Id<SaturationNodeExpansionCacheHandler>,

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
            used_concept_priority_strategy: Id::NONE,
            used_individual_priority_strategy: Id::NONE,
            used_process_context: ProcessContext::new(),
            ontology_arenas: OntologyArenas::new(),
            used_processing_data_box: ProcessingDataBox::new(),
            used_sat_calc_task: Id::NONE,
            used_task_processor_context: INVALID,
            used_task_priority_strategy: Id::NONE,
            used_process_stat_gath: Id::NONE,
            used_branch_tree_node: Id::NONE,
            used_base_dep_node: Id::NONE,
            min_modification_ancestor_depth: 0,
            min_modification_individual_id: 0,
            min_modification_updated: false,
            used_unsat_cache_handler: Id::NONE,
            used_individual_node_manager: Id::NONE,
            used_clash_descriptor_factory: Id::NONE,
            used_unsat_cach_ret_strategy: Id::NONE,
            used_dep_factory: Id::NONE,
            used_sat_exp_cache_handler: Id::NONE,
            max_completion_graph_cached_indi_node_id: 0,
            current_indi_node: Id::NONE,
            completion_graph_cached_localization_tag: 0,
            used_sat_node_exp_cache_handler: Id::NONE,
            pending_signal: CalcSignal::Continue,
            sat_calc_task_arena: Arena::new(),
            inc_cons_testing_adapter_arena: Arena::new(),
        }
    }

    /// Resolve a satisfiable task id (the `mSatCalcTask` / `mUsedSatCalcTask` target).
    pub fn sat_calc_task(&self, id: Id<SatisfiableCalculationTask>) -> &SatisfiableCalculationTask {
        self.sat_calc_task_arena.get(id)
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

    /// Port of `getUsedProcessingDataBox`.
    pub fn used_processing_data_box(&self) -> &ProcessingDataBox { &self.used_processing_data_box }
    /// Mutable access to the owned databox (the `getUsedProcessingDataBox` target).
    pub fn used_processing_data_box_mut(&mut self) -> &mut ProcessingDataBox {
        &mut self.used_processing_data_box
    }
    /// Port of `getUsedProcessContext` — the owned per-test arena container.
    pub fn used_process_context(&self) -> &ProcessContext { &self.used_process_context }
    /// Mutable access to the owned process context (the id-allocation path).
    pub fn used_process_context_mut(&mut self) -> &mut ProcessContext {
        &mut self.used_process_context
    }
    /// The static read-shared terminology arenas.
    pub fn ontology_arenas(&self) -> &OntologyArenas { &self.ontology_arenas }
    /// Mutable terminology access (construction time only).
    pub fn ontology_arenas_mut(&mut self) -> &mut OntologyArenas { &mut self.ontology_arenas }
    /// Port of `getCurrentIndividualNode`.
    pub fn current_individual_node(&self) -> NodeId { self.current_indi_node }
    /// Port of `setCurrentIndividualNode`.
    pub fn set_current_individual_node(&mut self, n: NodeId) -> &mut Self {
        self.current_indi_node = n;
        self
    }
    /// Port of `getUsedBranchTreeNode`.
    pub fn used_branch_tree_node(&self) -> BranchNodeId { self.used_branch_tree_node }
    /// Port of `getUsedBaseDependencyNode`.
    pub fn used_base_dependency_node(&self) -> DependencyId { self.used_base_dep_node }
    /// Port of `isMinModificationUpdated`.
    pub fn is_min_modification_updated(&self) -> bool { self.min_modification_updated }
    /// Port of `getMinModificationAncestorDepth`.
    pub fn min_modification_ancestor_depth(&self) -> Cint64 { self.min_modification_ancestor_depth }
    /// Port of `getMinModificationIndividualID`.
    pub fn min_modification_individual_id(&self) -> Cint64 { self.min_modification_individual_id }
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
    fn default() -> Self { Self::new() }
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
    pub concept_priority_strategy: Id<ConceptProcessingPriorityStrategy>,
    /// `CIndividualProcessingPriorityStrategy* mIndividualPriorityStrategy`.
    pub individual_priority_strategy: Id<IndividualProcessingPriorityStrategy>,
    /// `CTaskProcessingPriorityStrategy* mTaskPriorityStrategy`.
    pub task_priority_strategy: Id<TaskProcessingPriorityStrategy>,
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
    /// `CIndividualNodeManager* mIndiNodeManager`.
    pub indi_node_manager: Id<IndividualNodeManager>,
    /// `CUnsatisfiableCacheHandler* mUnsatCacheHandler`.
    pub unsat_cache_handler: Id<UnsatisfiableCacheHandler>,
    /// `CClashDescriptorFactory* mClashDescriptorFactory`.
    pub clash_descriptor_factory: Id<ClashDescriptorFactory>,
    /// `CUnsatisfiableCacheRetrievalStrategy* mUnsatCachRetStrategy`.
    pub unsat_cach_ret_strategy: Id<UnsatisfiableCacheRetrievalStrategy>,
    /// `CDependencyFactory* mDepFactory`.
    pub dep_factory: Id<DependencyFactory>,
    /// `CSatisfiableExpanderCacheHandler* mSatExpCacheHandler`.
    pub sat_exp_cache_handler: Id<SatisfiableExpanderCacheHandler>,
    /// `CSaturationNodeExpansionCacheHandler* mSatNodeExpCacheHandler`.
    pub sat_node_exp_cache_handler: Id<SaturationNodeExpansionCacheHandler>,
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
            concept_priority_strategy: Id::NONE,
            individual_priority_strategy: Id::NONE,
            task_priority_strategy: Id::NONE,
            processing_data_box: INVALID,
            sat_calc_task: Id::NONE,
            task_processor_context: INVALID,
            proc_stat_gath: Id::NONE,
            branch_tree_node: Id::NONE,
            base_dep_node: Id::NONE,
            indi_node_manager: Id::NONE,
            unsat_cache_handler: Id::NONE,
            clash_descriptor_factory: Id::NONE,
            unsat_cach_ret_strategy: Id::NONE,
            dep_factory: Id::NONE,
            sat_exp_cache_handler: Id::NONE,
            sat_node_exp_cache_handler: Id::NONE,
        }
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
    pub fn process_context(&self) -> &ProcessContext { &self.base.used_process_context }
    /// Mutable owned process-context access.
    pub fn process_context_mut(&mut self) -> &mut ProcessContext {
        &mut self.base.used_process_context
    }
    /// The static terminology arenas (live in `base`).
    pub fn ontology_arenas(&self) -> &OntologyArenas { &self.base.ontology_arenas }
    /// Mutable terminology access.
    pub fn ontology_arenas_mut(&mut self) -> &mut OntologyArenas {
        &mut self.base.ontology_arenas
    }
    /// Port of `getBranchTreeNode`.
    pub fn branch_tree_node(&self) -> BranchNodeId { self.branch_tree_node }
    /// Port of `getBaseDependencyNode`.
    pub fn base_dependency_node(&self) -> DependencyId { self.base_dep_node }

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
}

impl Default for CalculationAlgorithmContextBase {
    fn default() -> Self { Self::new() }
}
