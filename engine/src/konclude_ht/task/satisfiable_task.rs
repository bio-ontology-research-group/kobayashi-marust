//! `task::satisfiable_task` — THE central work item.
//!
//! Ports the MEMBER FIELDS of Konclude
//! `Source/Reasoner/Kernel/Task/CSatisfiableCalculationTask.h`
//! (`: public CTask, public CSatisfiableCalculationJobInstantiation`) plus the
//! trivial `CSatisfiableCalculationJobInstantiation` mixin and the
//! `TaskSettings.h` `PWORKBACKTRACKINGWORK` constant. This is the unit of work a
//! worker thread dereferences in `handleTask(...)`: it owns the per-test process
//! context + databox, the configuration, the stats collector, and the 16 adapter
//! back-pointers, and holds the boolean (SAT/UNSAT) result + task status.
//!
//! Struct-definition wave; the lifecycle method bodies (`initTask` /
//! `initSatisfiableCalculationTask` / `initBranchDependedSatisfiableCalculationTask`
//! / `initUndependedSatisfiableCalculationTask` / `makeTaskReference` /
//! `completeTask` / the type discriminants / the adapter set+get pairs) are the
//! `// W6-TASK method-batch` unit.

#![allow(dead_code)]

use super::super::model::substrate::{Cint64, Id};
use super::super::process::databox::ProcessingDataBox;
use super::adapters::{
    SatisfiableTaskAnswererBindingPropagationAdapter,
    SatisfiableTaskAnswererInstancePropagationMessageAdapter,
    SatisfiableTaskAnswererQueryingMaterializationAdapter,
    SatisfiableTaskAnswererSubsumptionMessageAdapter, SatisfiableTaskCancellationAdapter,
    SatisfiableTaskClassificationMessageAdapter,
    SatisfiableTaskClassificationRoleMarkedMessageAdapter,
    SatisfiableTaskIncrementalConsistencyTestingAdapter,
    SatisfiableTaskIndividualDependenceTrackingAdapter,
    SatisfiableTaskRealizationMarkedCandidatesMessageAdapter,
    SatisfiableTaskRealizationPossibleAssertionCollectingAdapter,
    SatisfiableTaskRealizationPossibleInstancesMergingAdapter,
    SatisfiableTaskRepresentativeBackendUpdatingAdapter, SaturationIndividualsAnalysingAdapter,
    SaturationOccurrenceStatisticsCollectingAdapter, TaskPreyingAdapter,
};
use super::calculation_job::SatisfiableCalculationJobConceptAssertion;
use super::config::CalculationConfigurationExtension;
use super::scheduler::{BooleanTaskResult, Task, TaskId, TaskStatus};
use super::stats::CalculationStatisticsCollector;

/// Port of `TaskSettings.h` `PWORKBACKTRACKINGWORK` (a task priority).
pub const PWORKBACKTRACKINGWORK: Cint64 = 1000;

/// `CSatisfiableCalculationTask*` → `SatTaskId` (a node in the branch task tree).
pub type SatTaskId = Id<SatisfiableCalculationTask>;

/// Port of `CSatisfiableCalculationTask::CALCULATIONTABLEAUCOMPLETIONTASK`.
pub const CALCULATIONTABLEAUCOMPLETIONTASK: Cint64 = 0;
/// Port of `CSatisfiableCalculationTask::CALCULATIONTABLEAUAPPROXIMATEDSATURATIONTASK`.
pub const CALCULATIONTABLEAUAPPROXIMATEDSATURATIONTASK: Cint64 = 1;

/// Port of `Reasoner::Kernel::Task::CSatisfiableCalculationJobInstantiation`
/// (trivial mixin; `getInstatiation()` returns `this`, no data members).
#[derive(Debug, Default, Clone)]
pub struct SatisfiableCalculationJobInstantiation;

impl SatisfiableCalculationJobInstantiation {
    /// Port of `CSatisfiableCalculationJobInstantiation::CSatisfiableCalculationJobInstantiation`.
    pub fn new() -> Self {
        SatisfiableCalculationJobInstantiation
    }

    /// Port of `CSatisfiableCalculationJobInstantiation::getInstatiation`
    /// (`return this;`).
    pub fn get_instatiation(&self) -> &Self {
        self
    }
}

/// Port of `Reasoner::Kernel::Task::CSatisfiableCalculationTask`.
///
/// `: public CTask, public CSatisfiableCalculationJobInstantiation` — the two
/// bases fold in as the `base` + `job_instantiation` fields (Rust no-inheritance
/// idiom). `mTaskType` (on `CTask`) routes between the two `taskType`
/// discriminants (completion vs approximate-saturation), same class.
pub struct SatisfiableCalculationTask {
    /// `CTask` base.
    pub base: Task,
    /// `CSatisfiableCalculationJobInstantiation` base.
    pub job_instantiation: SatisfiableCalculationJobInstantiation,
    /// `CSortedLinkerBase<CTask*,CTask,CTask>::next` for the branch-task list.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: the only concrete task arena in this port is
    /// `Arena<SatisfiableCalculationTask>`, so the inherited `CTask*` next-link is
    /// represented as the typed satisfiable-task id used by the branch creators.
    pub next: SatTaskId,
    /// Port-side ordered concept assertions expanded from the query calculation job.
    pub concept_assertions: Vec<SatisfiableCalculationJobConceptAssertion>,

    /// `CBooleanTaskResult mBoolTaskResult` (by value; the SAT/UNSAT result).
    pub bool_task_result: BooleanTaskResult,
    /// `CTaskStatus mDefaultTaskResult` (by value; named `*Result` in C++ but
    /// typed `CTaskStatus`).
    pub default_task_result: TaskStatus,

    /// `CProcessContextBase* mProcessContext`.
    ///
    /// KONCLUDE-PORT-NOTE[memory-pool]: the per-test process context is lazily
    /// allocated from the task memory pool and back-pointed here. Ported as an
    /// opaque `Cint64` handle resolving to the context-owned `ProcessContext`
    /// arena root (the W3.5 "context owns the arenas" decision); `INVALID` ==
    /// `nullptr` / not-yet-allocated. Branch tasks share the parent's handle.
    pub process_context: Cint64,
    /// `CProcessingDataBox* mProcessingDataBox`. [memory-pool] opaque handle, same
    /// scheme as `process_context`; branch tasks share the parent's databox.
    pub processing_data_box: Cint64,
    /// Rust-owned state for `mProcessingDataBox` when a task is materialized in
    /// this arena. The numeric pointer alias above is preserved for existing call
    /// sites; this optional value is the dereference target for exact-port code
    /// that needs the task's databox.
    pub processing_data_box_state: Option<ProcessingDataBox>,

    /// `CCalculationConfigurationExtension* mCalculationConfig`.
    pub calculation_config: Id<CalculationConfigurationExtension>,
    /// `CCalculationStatisticsCollector* mCalcStatColl`.
    pub calc_stat_coll: Id<CalculationStatisticsCollector>,

    // --- the 16 adapter back-pointers (.h 190-205) ---
    /// `CTaskPreyingAdapter* mConsAdapter`.
    pub cons_adapter: Id<TaskPreyingAdapter>,
    /// `CSaturationIndividualsAnalysingAdapter* mIndiAnalAdapter`.
    pub indi_anal_adapter: Id<SaturationIndividualsAnalysingAdapter>,
    /// `CSatisfiableTaskClassificationMessageAdapter* mClassMessAdapter`.
    pub class_mess_adapter: Id<SatisfiableTaskClassificationMessageAdapter>,
    /// `CSatisfiableTaskRealizationMarkedCandidatesMessageAdapter* mRealMessAdapter`.
    pub real_mess_adapter: Id<SatisfiableTaskRealizationMarkedCandidatesMessageAdapter>,
    /// `CSatisfiableTaskIncrementalConsistencyTestingAdapter* mSatIncConsTestingAdapter`.
    pub sat_inc_cons_testing_adapter: Id<SatisfiableTaskIncrementalConsistencyTestingAdapter>,
    /// `CSatisfiableTaskIndividualDependenceTrackingAdapter* mSatIndDepTrackAdapter`.
    pub sat_ind_dep_track_adapter: Id<SatisfiableTaskIndividualDependenceTrackingAdapter>,
    /// `CSatisfiableTaskRealizationPossibleAssertionCollectingAdapter* mPossAssCollAdapter`.
    pub poss_ass_coll_adapter: Id<SatisfiableTaskRealizationPossibleAssertionCollectingAdapter>,
    /// `CSatisfiableTaskClassificationRoleMarkedMessageAdapter* mClassRoleMarkedMessageAdapter`.
    pub class_role_marked_message_adapter:
        Id<SatisfiableTaskClassificationRoleMarkedMessageAdapter>,
    /// `CSatisfiableTaskAnswererSubsumptionMessageAdapter* mAnswererSubsumptionMessageAdapter`.
    pub answerer_subsumption_message_adapter: Id<SatisfiableTaskAnswererSubsumptionMessageAdapter>,
    /// `CSatisfiableTaskAnswererBindingPropagationAdapter* mAnswererBindingPropagationAdapter`.
    pub answerer_binding_propagation_adapter: Id<SatisfiableTaskAnswererBindingPropagationAdapter>,
    /// `CSatisfiableTaskRealizationPossibleInstancesMergingAdapter* mSatisfiablePossibleInstancesMergingAdapter`.
    pub satisfiable_possible_instances_merging_adapter:
        Id<SatisfiableTaskRealizationPossibleInstancesMergingAdapter>,
    /// `CSatisfiableTaskAnswererInstancePropagationMessageAdapter* mAnswererInstancePropagationMessageAdapter`.
    pub answerer_instance_propagation_message_adapter:
        Id<SatisfiableTaskAnswererInstancePropagationMessageAdapter>,
    /// `CSatisfiableTaskRepresentativeBackendUpdatingAdapter* mRepresentativeBackendUpdatingAdapter`.
    pub representative_backend_updating_adapter:
        Id<SatisfiableTaskRepresentativeBackendUpdatingAdapter>,
    /// `CSaturationOccurrenceStatisticsCollectingAdapter* mOccurrenceStatisticsCollectingAdapter`.
    pub occurrence_statistics_collecting_adapter:
        Id<SaturationOccurrenceStatisticsCollectingAdapter>,
    /// `CSatisfiableTaskAnswererQueryingMaterializationAdapter* mAnswererMaterializationAdapter`.
    pub answerer_materialization_adapter: Id<SatisfiableTaskAnswererQueryingMaterializationAdapter>,
    /// `CSatisfiableTaskCancellationAdapter* mCancellationAdapter`.
    pub cancellation_adapter: Id<SatisfiableTaskCancellationAdapter>,
}

impl Default for SatisfiableCalculationTask {
    fn default() -> Self {
        SatisfiableCalculationTask {
            base: Task::default(),
            job_instantiation: SatisfiableCalculationJobInstantiation,
            next: Id::NONE,
            concept_assertions: Vec::new(),
            bool_task_result: BooleanTaskResult::default(),
            default_task_result: TaskStatus::default(),
            process_context: -1,
            processing_data_box: -1,
            processing_data_box_state: None,
            calculation_config: Id::NONE,
            calc_stat_coll: Id::NONE,
            cons_adapter: Id::NONE,
            indi_anal_adapter: Id::NONE,
            class_mess_adapter: Id::NONE,
            real_mess_adapter: Id::NONE,
            sat_inc_cons_testing_adapter: Id::NONE,
            sat_ind_dep_track_adapter: Id::NONE,
            poss_ass_coll_adapter: Id::NONE,
            class_role_marked_message_adapter: Id::NONE,
            answerer_subsumption_message_adapter: Id::NONE,
            answerer_binding_propagation_adapter: Id::NONE,
            satisfiable_possible_instances_merging_adapter: Id::NONE,
            answerer_instance_propagation_message_adapter: Id::NONE,
            representative_backend_updating_adapter: Id::NONE,
            occurrence_statistics_collecting_adapter: Id::NONE,
            answerer_materialization_adapter: Id::NONE,
            cancellation_adapter: Id::NONE,
        }
    }
}

impl SatisfiableCalculationTask {
    /// Port of `CSatisfiableCalculationTask::CSatisfiableCalculationTask`.
    pub fn new() -> Self {
        SatisfiableCalculationTask::default()
    }

    /// Port of `CSatisfiableCalculationJobInstantiation::getInstatiation`
    /// (`return this;` — the co-inherited instantiation mixin).
    pub fn get_instatiation(&self) -> &Self {
        self
    }

    /// Port of the inherited `CSortedLinkerBase::getNext`.
    pub fn get_next(&self) -> SatTaskId {
        self.next
    }

    /// Port of the inherited `CSortedLinkerBase::setNext`.
    pub fn set_next(&mut self, next: SatTaskId) -> &mut Self {
        self.next = next;
        self
    }

    /// Port-side append for one calculation-job concept assertion.
    pub fn add_satisfiable_calculation_job_concept_assertion(
        &mut self,
        assertion: SatisfiableCalculationJobConceptAssertion,
    ) -> &mut Self {
        self.concept_assertions.push(assertion);
        self
    }

    /// Replace the ordered calculation-job concept assertions.
    pub fn set_satisfiable_calculation_job_concept_assertions(
        &mut self,
        assertions: Vec<SatisfiableCalculationJobConceptAssertion>,
    ) -> &mut Self {
        self.concept_assertions = assertions;
        self
    }

    /// Ordered assertions expanded from the query calculation job.
    pub fn get_satisfiable_calculation_job_concept_assertions(
        &self,
    ) -> &[SatisfiableCalculationJobConceptAssertion] {
        &self.concept_assertions
    }

    /// Port of `CSatisfiableCalculationTask::getTaskContext`
    /// (`return getProcessContext(context);`).
    pub fn get_task_context(&mut self) -> Cint64 {
        self.get_process_context()
    }

    /// Port of `CSatisfiableCalculationTask::getProcessContext`.
    ///
    /// W6-DEFER[api]: lazily bump-allocates a `CProcessContextBase` from the task
    /// pool on first call and back-points `mProcessContext` (+ `mTaskContext`),
    /// else `updateContext`. The alloc needs the `CTaskHandleContext` + memory pool
    /// ([memory-pool]); the handle resolves to the context-owned `ProcessContext`
    /// arena root (the W3.5 decision).
    pub fn get_process_context(&mut self) -> Cint64 {
        // if !mProcessContext { mProcessContext = new CProcessContextBase(this,context); mTaskContext = mProcessContext; }
        // else { mProcessContext->updateContext(context); }
        self.process_context
    }

    /// Port of `CSatisfiableCalculationTask::getProcessingDataBox`.
    pub fn get_processing_data_box(&self) -> Cint64 {
        self.processing_data_box
    }

    /// Port-facing dereference of `mProcessingDataBox`.
    pub fn processing_data_box_state(&self) -> Option<&ProcessingDataBox> {
        self.processing_data_box_state.as_ref()
    }

    /// Install the Rust-owned databox state for this task.
    pub fn set_processing_data_box_state(&mut self, data_box: ProcessingDataBox) -> &mut Self {
        self.processing_data_box_state = Some(data_box);
        self
    }

    /// Port of `CSatisfiableCalculationTask::makeTaskReference`.
    ///
    /// W6-DEFER[api]: chains to `CTask::makeTaskReference`, then shares this task's
    /// databox + process context INTO the depended (branch) task
    /// (`initProcessingDataBox` / `referenceProcessContext`) and COPIES the 16
    /// adapter pointers down. The depended task is a `SatTaskId`; resolving it +
    /// the databox/context share need the (not-yet-ported) task arena.
    pub fn make_task_reference(&mut self, depended_task: SatTaskId) -> &mut Self {
        self.base.make_task_reference(Id::new(depended_task.raw));
        // depSatCalcTask->mProcessingDataBox->initProcessingDataBox(mProcessingDataBox);
        // depSatCalcTask->mProcessContext->referenceProcessContext(mProcessContext);
        // depSatCalcTask->m*Adapter = m*Adapter;  // all 16 adapters copied down
        self
    }

    /// Port of `CSatisfiableCalculationTask::initTask`.
    ///
    /// Resets the adapter back-pointers (real; note `mSatIndDepTrackAdapter` is the
    /// ONE adapter `initTask` does NOT reset — faithful), then (W6-DEFER[api])
    /// allocates the process context + databox from the task pool and chains to
    /// `CTask::initTask`.
    pub fn init_task(&mut self, parent_task: TaskId) -> &mut Self {
        self.process_context = -1;
        self.processing_data_box = -1;
        self.processing_data_box_state = None;
        self.concept_assertions.clear();
        self.cons_adapter = Id::NONE;
        self.indi_anal_adapter = Id::NONE;
        self.occurrence_statistics_collecting_adapter = Id::NONE;
        self.class_mess_adapter = Id::NONE;
        self.real_mess_adapter = Id::NONE;
        self.poss_ass_coll_adapter = Id::NONE;
        self.class_role_marked_message_adapter = Id::NONE;
        self.answerer_subsumption_message_adapter = Id::NONE;
        self.answerer_instance_propagation_message_adapter = Id::NONE;
        self.representative_backend_updating_adapter = Id::NONE;
        self.answerer_binding_propagation_adapter = Id::NONE;
        self.satisfiable_possible_instances_merging_adapter = Id::NONE;
        self.cancellation_adapter = Id::NONE;
        self.answerer_materialization_adapter = Id::NONE;
        self.sat_inc_cons_testing_adapter = Id::NONE;
        // getProcessContext(context);  // W6-DEFER[api] alloc context
        // mProcessingDataBox = alloc CProcessingDataBox(mProcessContext);  // [memory-pool]
        self.base.init_task(parent_task);
        self
    }

    /// Port of `CSatisfiableCalculationTask::initSatisfiableCalculationTask`.
    ///
    /// The ROOT (un-parented) satisfiable task: `initTask(nullptr)`, null ALL 16
    /// adapters, set the config + stats collector, then (W6-DEFER[api])
    /// `mProcessingDataBox->initProcessingDataBox(ontology)`. `ontology`
    /// (`CConcreteOntology*`) is opaque [api].
    pub fn init_satisfiable_calculation_task(
        &mut self,
        _ontology: Cint64,
        calculation_config: Id<CalculationConfigurationExtension>,
        calc_stat_collector: Id<CalculationStatisticsCollector>,
    ) -> &mut Self {
        self.init_task(Id::NONE);
        self.cons_adapter = Id::NONE;
        self.indi_anal_adapter = Id::NONE;
        self.occurrence_statistics_collecting_adapter = Id::NONE;
        self.class_mess_adapter = Id::NONE;
        self.real_mess_adapter = Id::NONE;
        self.poss_ass_coll_adapter = Id::NONE;
        self.class_role_marked_message_adapter = Id::NONE;
        self.answerer_subsumption_message_adapter = Id::NONE;
        self.answerer_instance_propagation_message_adapter = Id::NONE;
        self.representative_backend_updating_adapter = Id::NONE;
        self.answerer_binding_propagation_adapter = Id::NONE;
        self.satisfiable_possible_instances_merging_adapter = Id::NONE;
        self.cancellation_adapter = Id::NONE;
        self.sat_inc_cons_testing_adapter = Id::NONE;
        self.answerer_materialization_adapter = Id::NONE;
        self.sat_ind_dep_track_adapter = Id::NONE;
        self.calc_stat_coll = calc_stat_collector;
        self.calculation_config = calculation_config;
        // mProcessingDataBox->initProcessingDataBox(ontology);  // W6-DEFER[api]
        self
    }

    /// Port of `CSatisfiableCalculationTask::initUndependedSatisfiableCalculationTask`.
    ///
    /// A fresh root task that REUSES `baseTask`'s databox + process context but is
    /// independent in the task tree (`initTask(nullptr)`). Copies the task type +
    /// config/stats; (W6-DEFER[api]) `initProcessingDataBox(baseTask->mProcessingDataBox)`
    /// + `referenceProcessContext(baseTask->mProcessContext)`.
    pub fn init_undepended_satisfiable_calculation_task(
        &mut self,
        base_task: &SatisfiableCalculationTask,
        calculation_config: Id<CalculationConfigurationExtension>,
        calc_stat_collector: Id<CalculationStatisticsCollector>,
    ) -> &mut Self {
        self.init_task(Id::NONE);
        self.cons_adapter = Id::NONE;
        self.indi_anal_adapter = Id::NONE;
        self.occurrence_statistics_collecting_adapter = Id::NONE;
        self.class_mess_adapter = Id::NONE;
        self.real_mess_adapter = Id::NONE;
        self.sat_inc_cons_testing_adapter = Id::NONE;
        self.sat_ind_dep_track_adapter = Id::NONE;
        self.class_role_marked_message_adapter = Id::NONE;
        self.answerer_subsumption_message_adapter = Id::NONE;
        self.answerer_binding_propagation_adapter = Id::NONE;
        self.answerer_instance_propagation_message_adapter = Id::NONE;
        self.representative_backend_updating_adapter = Id::NONE;
        self.answerer_materialization_adapter = Id::NONE;
        self.satisfiable_possible_instances_merging_adapter = Id::NONE;
        self.cancellation_adapter = Id::NONE;
        self.calc_stat_coll = calc_stat_collector;
        self.calculation_config = calculation_config;
        // mProcessingDataBox->initProcessingDataBox(baseTask->mProcessingDataBox);  // W6-DEFER[api]
        // mProcessContext->referenceProcessContext(baseTask->mProcessContext);      // W6-DEFER[api]
        self.base.task_type = base_task.base.task_type;
        self
    }

    /// Port of `CSatisfiableCalculationTask::initBranchDependedSatisfiableCalculationTask`.
    ///
    /// A branch (child) task in the OR task-tree: `initTask(dependedTask)` (shares
    /// the parent databox/context + copies adapters via `makeTaskReference`) then
    /// inherits the depended task's config/stats/type.
    ///
    /// KONCLUDE-PORT-NOTE[api]: the caller supplies BOTH the depended task's id (for
    /// the parent linkage that `init_task` defers) and its value (for the field
    /// copies), since this port has no task arena to resolve one from the other.
    pub fn init_branch_depended_satisfiable_calculation_task(
        &mut self,
        depended_task_id: TaskId,
        depended_task: &SatisfiableCalculationTask,
    ) -> &mut Self {
        self.init_task(depended_task_id);
        self.calc_stat_coll = depended_task.calc_stat_coll;
        self.calculation_config = depended_task.calculation_config;
        self.base.task_type = depended_task.base.task_type;
        self
    }

    /// Port of `CSatisfiableCalculationTask::getSatisfiableCalculationTaskResult`
    /// (`return &mBoolTaskResult;`).
    pub fn get_satisfiable_calculation_task_result(&mut self) -> &mut BooleanTaskResult {
        &mut self.bool_task_result
    }

    /// Port of `CSatisfiableCalculationTask::getCalculationConfiguration`.
    pub fn get_calculation_configuration(&self) -> Id<CalculationConfigurationExtension> {
        self.calculation_config
    }

    /// Port of `CSatisfiableCalculationTask::completeTask`.
    ///
    /// W6-DEFER[api]: when statistics gathering is on, flushes the gathered
    /// processing statistics either UP to the parent's process context or, at the
    /// root, into `mCalcStatColl` (`addProcessingStatistics`); then chains to
    /// `CTask::completeTask`. The statistics gather/flush derefs the opaque process
    /// context + the (not-yet-ported) `CProcessingStatistics` registry.
    pub fn complete_task(&mut self) -> &mut Self {
        // #ifndef KONCLUDE_FORCE_STATISTIC_DEACTIVATED ... flush stats up/to collector
        self.base.complete_task();
        self
    }

    /// Port of `CSatisfiableCalculationTask::isCalculationTableauCompletionTask`.
    pub fn is_calculation_tableau_completion_task(&self) -> bool {
        self.base.get_task_type() == CALCULATIONTABLEAUCOMPLETIONTASK
    }

    /// Port of `CSatisfiableCalculationTask::isCalculationTableauSaturationTask`.
    pub fn is_calculation_tableau_saturation_task(&self) -> bool {
        self.base.get_task_type() == CALCULATIONTABLEAUAPPROXIMATEDSATURATIONTASK
    }

    /// Port of `CSatisfiableCalculationTask::setCalculationTaskType`.
    pub fn set_calculation_task_type(&mut self, task_type: Cint64) -> &mut Self {
        self.base.task_type = task_type;
        self
    }

    /// Port of `CSatisfiableCalculationTask::getCalculationTaskType`
    /// (`return getTaskType();`).
    pub fn get_calculation_task_type(&self) -> Cint64 {
        self.base.get_task_type()
    }

    /// Port of `CSatisfiableCalculationTask::createTaskResult`
    /// (`return &mBoolTaskResult;`).
    pub fn create_task_result(&mut self) -> &mut BooleanTaskResult {
        &mut self.bool_task_result
    }

    /// Port of `CSatisfiableCalculationTask::createTaskStatus`
    /// (`return &mDefaultTaskResult;`).
    pub fn create_task_status(&mut self) -> &mut TaskStatus {
        &mut self.default_task_result
    }

    // --- the 16 adapter set*/get* pairs (CSatisfiableCalculationTask.cpp) ---

    /// Port of `CSatisfiableCalculationTask::setConsistenceAdapter`.
    pub fn set_consistence_adapter(
        &mut self,
        consistence_adapter: Id<TaskPreyingAdapter>,
    ) -> &mut Self {
        self.cons_adapter = consistence_adapter;
        self
    }
    /// Port of `CSatisfiableCalculationTask::getConsistenceAdapter`.
    pub fn get_consistence_adapter(&self) -> Id<TaskPreyingAdapter> {
        self.cons_adapter
    }

    /// Port of `CSatisfiableCalculationTask::setSaturationIndividualsAnalysationObserver`.
    pub fn set_saturation_individuals_analysation_observer(
        &mut self,
        indi_anal_adapter: Id<SaturationIndividualsAnalysingAdapter>,
    ) -> &mut Self {
        self.indi_anal_adapter = indi_anal_adapter;
        self
    }
    /// Port of `CSatisfiableCalculationTask::getSaturationIndividualsAnalysationObserver`.
    pub fn get_saturation_individuals_analysation_observer(
        &self,
    ) -> Id<SaturationIndividualsAnalysingAdapter> {
        self.indi_anal_adapter
    }

    /// Port of `CSatisfiableCalculationTask::setOccurrenceStatisticsCollectingAdapter`.
    pub fn set_occurrence_statistics_collecting_adapter(
        &mut self,
        coll_adapter: Id<SaturationOccurrenceStatisticsCollectingAdapter>,
    ) -> &mut Self {
        self.occurrence_statistics_collecting_adapter = coll_adapter;
        self
    }
    /// Port of `CSatisfiableCalculationTask::getOccurrenceStatisticsCollectingAdapter`.
    pub fn get_occurrence_statistics_collecting_adapter(
        &self,
    ) -> Id<SaturationOccurrenceStatisticsCollectingAdapter> {
        self.occurrence_statistics_collecting_adapter
    }

    /// Port of `CSatisfiableCalculationTask::setClassificationMessageAdapter`.
    pub fn set_classification_message_adapter(
        &mut self,
        class_mess_adapter: Id<SatisfiableTaskClassificationMessageAdapter>,
    ) -> &mut Self {
        self.class_mess_adapter = class_mess_adapter;
        self
    }
    /// Port of `CSatisfiableCalculationTask::getClassificationMessageAdapter`.
    pub fn get_classification_message_adapter(
        &self,
    ) -> Id<SatisfiableTaskClassificationMessageAdapter> {
        self.class_mess_adapter
    }

    /// Port of `CSatisfiableCalculationTask::setRealizationMarkedCandidatesMessageAdapter`.
    pub fn set_realization_marked_candidates_message_adapter(
        &mut self,
        real_mess_observer: Id<SatisfiableTaskRealizationMarkedCandidatesMessageAdapter>,
    ) -> &mut Self {
        self.real_mess_adapter = real_mess_observer;
        self
    }
    /// Port of `CSatisfiableCalculationTask::getRealizationMarkedCandidatesMessageAdapter`.
    pub fn get_realization_marked_candidates_message_adapter(
        &self,
    ) -> Id<SatisfiableTaskRealizationMarkedCandidatesMessageAdapter> {
        self.real_mess_adapter
    }

    /// Port of `CSatisfiableCalculationTask::setSatisfiableTaskIncrementalConsistencyTestingAdapter`.
    pub fn set_satisfiable_task_incremental_consistency_testing_adapter(
        &mut self,
        inc_cons_test_adaptor: Id<SatisfiableTaskIncrementalConsistencyTestingAdapter>,
    ) -> &mut Self {
        self.sat_inc_cons_testing_adapter = inc_cons_test_adaptor;
        self
    }
    /// Port of `CSatisfiableCalculationTask::getSatisfiableTaskIncrementalConsistencyTestingAdapter`.
    pub fn get_satisfiable_task_incremental_consistency_testing_adapter(
        &self,
    ) -> Id<SatisfiableTaskIncrementalConsistencyTestingAdapter> {
        self.sat_inc_cons_testing_adapter
    }

    /// Port of `CSatisfiableCalculationTask::setSatisfiableTaskIndividualDependenceTrackingAdapter`.
    pub fn set_satisfiable_task_individual_dependence_tracking_adapter(
        &mut self,
        ind_dep_track_adaptor: Id<SatisfiableTaskIndividualDependenceTrackingAdapter>,
    ) -> &mut Self {
        self.sat_ind_dep_track_adapter = ind_dep_track_adaptor;
        self
    }
    /// Port of `CSatisfiableCalculationTask::getSatisfiableTaskIndividualDependenceTrackingAdapter`.
    pub fn get_satisfiable_task_individual_dependence_tracking_adapter(
        &self,
    ) -> Id<SatisfiableTaskIndividualDependenceTrackingAdapter> {
        self.sat_ind_dep_track_adapter
    }

    /// Port of `CSatisfiableCalculationTask::setPossibleAssertionCollectionAdapter`.
    pub fn set_possible_assertion_collection_adapter(
        &mut self,
        poss_ass_coll_adapter: Id<SatisfiableTaskRealizationPossibleAssertionCollectingAdapter>,
    ) -> &mut Self {
        self.poss_ass_coll_adapter = poss_ass_coll_adapter;
        self
    }
    /// Port of `CSatisfiableCalculationTask::getPossibleAssertionCollectionAdapter`.
    pub fn get_possible_assertion_collection_adapter(
        &self,
    ) -> Id<SatisfiableTaskRealizationPossibleAssertionCollectingAdapter> {
        self.poss_ass_coll_adapter
    }

    /// Port of `CSatisfiableCalculationTask::setSatisfiableClassificationRoleMarkedMessageAdapter`.
    pub fn set_satisfiable_classification_role_marked_message_adapter(
        &mut self,
        class_role_marked_message_adapter: Id<
            SatisfiableTaskClassificationRoleMarkedMessageAdapter,
        >,
    ) -> &mut Self {
        self.class_role_marked_message_adapter = class_role_marked_message_adapter;
        self
    }
    /// Port of `CSatisfiableCalculationTask::getSatisfiableClassificationRoleMarkedMessageAdapter`.
    pub fn get_satisfiable_classification_role_marked_message_adapter(
        &self,
    ) -> Id<SatisfiableTaskClassificationRoleMarkedMessageAdapter> {
        self.class_role_marked_message_adapter
    }

    /// Port of `CSatisfiableCalculationTask::setSatisfiableAnswererSubsumptionMessageAdapter`.
    pub fn set_satisfiable_answerer_subsumption_message_adapter(
        &mut self,
        answerer_message_adapter: Id<SatisfiableTaskAnswererSubsumptionMessageAdapter>,
    ) -> &mut Self {
        self.answerer_subsumption_message_adapter = answerer_message_adapter;
        self
    }
    /// Port of `CSatisfiableCalculationTask::getSatisfiableAnswererSubsumptionMessageAdapter`.
    pub fn get_satisfiable_answerer_subsumption_message_adapter(
        &self,
    ) -> Id<SatisfiableTaskAnswererSubsumptionMessageAdapter> {
        self.answerer_subsumption_message_adapter
    }

    /// Port of `CSatisfiableCalculationTask::setSatisfiableAnswererBindingPropagationAdapter`.
    pub fn set_satisfiable_answerer_binding_propagation_adapter(
        &mut self,
        answerer_message_adapter: Id<SatisfiableTaskAnswererBindingPropagationAdapter>,
    ) -> &mut Self {
        self.answerer_binding_propagation_adapter = answerer_message_adapter;
        self
    }
    /// Port of `CSatisfiableCalculationTask::getSatisfiableAnswererBindingPropagationAdapter`.
    pub fn get_satisfiable_answerer_binding_propagation_adapter(
        &self,
    ) -> Id<SatisfiableTaskAnswererBindingPropagationAdapter> {
        self.answerer_binding_propagation_adapter
    }

    /// Port of `CSatisfiableCalculationTask::setSatisfiablePossibleInstancesMergingAdapter`.
    pub fn set_satisfiable_possible_instances_merging_adapter(
        &mut self,
        poss_inst_merging_adapter: Id<SatisfiableTaskRealizationPossibleInstancesMergingAdapter>,
    ) -> &mut Self {
        self.satisfiable_possible_instances_merging_adapter = poss_inst_merging_adapter;
        self
    }
    /// Port of `CSatisfiableCalculationTask::getSatisfiablePossibleInstancesMergingAdapter`.
    pub fn get_satisfiable_possible_instances_merging_adapter(
        &self,
    ) -> Id<SatisfiableTaskRealizationPossibleInstancesMergingAdapter> {
        self.satisfiable_possible_instances_merging_adapter
    }

    /// Port of `CSatisfiableCalculationTask::setSatisfiableAnswererInstancePropagationMessageAdapter`.
    pub fn set_satisfiable_answerer_instance_propagation_message_adapter(
        &mut self,
        answerer_message_adapter: Id<SatisfiableTaskAnswererInstancePropagationMessageAdapter>,
    ) -> &mut Self {
        self.answerer_instance_propagation_message_adapter = answerer_message_adapter;
        self
    }
    /// Port of `CSatisfiableCalculationTask::getSatisfiableAnswererInstancePropagationMessageAdapter`.
    pub fn get_satisfiable_answerer_instance_propagation_message_adapter(
        &self,
    ) -> Id<SatisfiableTaskAnswererInstancePropagationMessageAdapter> {
        self.answerer_instance_propagation_message_adapter
    }

    /// Port of `CSatisfiableCalculationTask::setSatisfiableRepresentativeBackendCacheUpdatingAdapter`.
    pub fn set_satisfiable_representative_backend_cache_updating_adapter(
        &mut self,
        representative_backend_updating_adapter: Id<
            SatisfiableTaskRepresentativeBackendUpdatingAdapter,
        >,
    ) -> &mut Self {
        self.representative_backend_updating_adapter = representative_backend_updating_adapter;
        self
    }
    /// Port of `CSatisfiableCalculationTask::getSatisfiableRepresentativeBackendCacheUpdatingAdapter`.
    pub fn get_satisfiable_representative_backend_cache_updating_adapter(
        &self,
    ) -> Id<SatisfiableTaskRepresentativeBackendUpdatingAdapter> {
        self.representative_backend_updating_adapter
    }

    /// Port of `CSatisfiableCalculationTask::setSatisfiableAnswererMaterializationAdapter`.
    pub fn set_satisfiable_answerer_materialization_adapter(
        &mut self,
        coll_adapter: Id<SatisfiableTaskAnswererQueryingMaterializationAdapter>,
    ) -> &mut Self {
        self.answerer_materialization_adapter = coll_adapter;
        self
    }
    /// Port of `CSatisfiableCalculationTask::getSatisfiableAnswererMaterializationAdapter`.
    pub fn get_satisfiable_answerer_materialization_adapter(
        &self,
    ) -> Id<SatisfiableTaskAnswererQueryingMaterializationAdapter> {
        self.answerer_materialization_adapter
    }

    /// Port of `CSatisfiableCalculationTask::setCancellationAdapter`.
    pub fn set_cancellation_adapter(
        &mut self,
        cancel_adapter: Id<SatisfiableTaskCancellationAdapter>,
    ) -> &mut Self {
        self.cancellation_adapter = cancel_adapter;
        self
    }
    /// Port of `CSatisfiableCalculationTask::getCancellationAdapter`.
    pub fn get_cancellation_adapter(&self) -> Id<SatisfiableTaskCancellationAdapter> {
        self.cancellation_adapter
    }
}
