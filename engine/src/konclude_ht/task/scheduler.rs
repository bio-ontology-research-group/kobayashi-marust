//! `task::scheduler` — the small `Scheduler/` base port the Task layer extends.
//!
//! Ports the MEMBER FIELDS of the scheduler base classes that
//! `CSatisfiableCalculationTask` and the two communicators derive from
//! (`Source/Scheduler/`): `CTask`, `CTaskStatus`, `CTaskResult`,
//! `CBooleanTaskResult`, `CTaskHandleContext`, `CTaskCallbackExecuter`,
//! `CTaskStatusPropagator`. This is the struct-definition wave (manifest 10,
//! the `scheduler/` prerequisite folded into `task/`); method bodies are the
//! `// W6-TASK method-batch` units.
//!
//! KONCLUDE-PORT-NOTE[ownership]: `CTask` is allocated from the per-thread task
//! memory pool (`CMemoryPoolContainer`); the port holds it by value / behind a
//! typed `Id<Task>` (`TaskId`). The three abstract bases (`CTaskResult`,
//! `CTaskHandleContext`, `CTaskCallbackExecuter`, `CTaskStatusPropagator`) carry
//! no data members, so they become zero-size markers a derived struct embeds as
//! a `base` field (the Rust no-inheritance idiom used across the port).

#![allow(dead_code)]

use super::super::model::substrate::{Cint64, Id, NegLink, INVALID};

/// `CTask*` → `TaskId` (a node in the per-branch task tree).
pub type TaskId = Id<Task>;
/// `CTaskStatus*` → `TaskStatusId`.
pub type TaskStatusId = Id<TaskStatus>;

/// Port of `CTaskStatus::TASKSTATE`.
///
/// KONCLUDE-PORT-NOTE[overload]: variant names mirror the C++ `TS*` enumerators
/// verbatim as port anchors.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[allow(non_camel_case_types)]
pub enum TaskState {
    TsUninitialized,
    TsQueued,
    TsProcessing,
    TsScheduling,
    TsFinished,
    TsCompleted,
}

impl Default for TaskState {
    fn default() -> Self {
        TaskState::TsUninitialized
    }
}

/// Port of `Scheduler::CTaskStatus`. The per-task lifecycle/cancel/error flags.
#[derive(Debug, Default, Clone)]
pub struct TaskStatus {
    /// `TASKSTATE mTaskState`.
    pub task_state: TaskState,
    /// `bool mCanceledFlag`.
    pub canceled_flag: bool,
    /// `bool mFinishedFlag`.
    pub finished_flag: bool,
    /// `bool mReleaseable`.
    pub releaseable: bool,
    /// `bool mErrorFlag`.
    pub error_flag: bool,
    /// `cint64 mErrorCode`.
    pub error_code: Cint64,
}

impl TaskStatus {
    /// Port of `CTaskStatus::CTaskStatus`.
    pub fn new() -> Self {
        TaskStatus::default()
    }
    /// Port of `CTaskStatus::getTaskState`.
    pub fn get_task_state(&self) -> TaskState {
        self.task_state
    }

    /// Port of `CTaskStatus::setTaskState`.
    pub fn set_task_state(&mut self, task_state: TaskState) -> &mut Self {
        self.task_state = task_state;
        self
    }

    /// Port of `CTaskStatus::setCanceled`.
    pub fn set_canceled(&mut self, canceled: bool) -> &mut Self {
        self.canceled_flag = canceled;
        self
    }

    /// Port of `CTaskStatus::setFinished`.
    pub fn set_finished(&mut self, finished: bool) -> &mut Self {
        self.finished_flag = finished;
        self
    }

    /// Port of `CTaskStatus::setError`.
    pub fn set_error(&mut self, error: bool, error_code: Cint64) -> &mut Self {
        self.error_flag = error;
        self.error_code = error_code;
        self
    }

    /// Port of `CTaskStatus::setMemoryReleaseable`.
    pub fn set_memory_releaseable(&mut self, releaseable: bool) -> &mut Self {
        self.releaseable = releaseable;
        self
    }

    /// Port of `CTaskStatus::isFinished`.
    pub fn is_finished(&self) -> bool {
        self.finished_flag
    }

    /// Port of `CTaskStatus::isCanceled`.
    pub fn is_canceled(&self) -> bool {
        self.canceled_flag
    }

    /// Port of `CTaskStatus::isError`.
    pub fn is_error(&self) -> bool {
        self.error_flag
    }

    /// Port of `CTaskStatus::isProcessable`.
    pub fn is_processable(&self) -> bool {
        !self.canceled_flag && !self.finished_flag && !self.error_flag
    }

    /// Port of `CTaskStatus::getErrorCode`.
    pub fn get_error_code(&self) -> Cint64 {
        self.error_code
    }

    /// Port of `CTaskStatus::isTaskState`.
    ///
    /// KONCLUDE-PORT-NOTE[unclear]: the C++ body is `return mTaskState = taskState;`
    /// — an assignment (`=`) not a comparison (`==`), a known typo in the source.
    /// Ported bug-faithfully: it mutates `task_state` and returns the assigned
    /// value coerced to bool (non-`TsUninitialized`).
    pub fn is_task_state(&mut self, task_state: TaskState) -> bool {
        self.task_state = task_state;
        (self.task_state as i64) != 0
    }

    /// Port of `CTaskStatus::hasOneTaskState`.
    ///
    /// KONCLUDE-PORT-NOTE[overload]: C++ does a bitwise AND on the `TASKSTATE`
    /// enum treated as an int; ported by casting the enum discriminants to `i64`.
    pub fn has_one_task_state(&self, task_state_combination: TaskState) -> bool {
        ((self.task_state as i64) & (task_state_combination as i64)) != 0
    }

    /// Port of `CTaskStatus::setTaskQUEUEDState`.
    pub fn set_task_queued_state(&mut self) -> &mut Self {
        self.task_state = TaskState::TsQueued;
        self
    }

    /// Port of `CTaskStatus::setTaskPROCESSINGState`.
    pub fn set_task_processing_state(&mut self) -> &mut Self {
        self.task_state = TaskState::TsProcessing;
        self
    }

    /// Port of `CTaskStatus::setTaskSCHEDULINGState`.
    pub fn set_task_scheduling_state(&mut self) -> &mut Self {
        self.task_state = TaskState::TsScheduling;
        self
    }

    /// Port of `CTaskStatus::setTaskCOMPLETEDState`.
    pub fn set_task_completed_state(&mut self) -> &mut Self {
        self.task_state = TaskState::TsCompleted;
        self
    }

    /// Port of `CTaskStatus::setTaskFINISHEDState`.
    pub fn set_task_finished_state(&mut self) -> &mut Self {
        self.task_state = TaskState::TsFinished;
        self
    }

    /// Port of `CTaskStatus::isTaskStateQUEUED`.
    pub fn is_task_state_queued(&self) -> bool {
        self.task_state == TaskState::TsQueued
    }

    /// Port of `CTaskStatus::isTaskStatePROCESSING`.
    pub fn is_task_state_processing(&self) -> bool {
        self.task_state == TaskState::TsProcessing
    }

    /// Port of `CTaskStatus::isTaskStateSCHEDULING`.
    pub fn is_task_state_scheduling(&self) -> bool {
        self.task_state == TaskState::TsScheduling
    }

    /// Port of `CTaskStatus::isTaskStateFINISHED`.
    pub fn is_task_state_finished(&self) -> bool {
        self.task_state == TaskState::TsFinished
    }

    /// Port of `CTaskStatus::isTaskStateCOMPLETED`.
    pub fn is_task_state_completed(&self) -> bool {
        self.task_state == TaskState::TsCompleted
    }

    /// Port of `CTaskStatus::isTaskStateUNINITIALIZED`.
    pub fn is_task_state_uninitialized(&self) -> bool {
        self.task_state == TaskState::TsUninitialized
    }

    /// Port of `CTaskStatus::isMemoryReleaseable`.
    pub fn is_memory_releaseable(&self) -> bool {
        self.releaseable
    }
}

/// Port of `Scheduler::CTaskResult` (the abstract result base; `hasResult()` is
/// pure virtual, no data members).
///
/// KONCLUDE-PORT-NOTE[ownership]: zero-size marker; `CBooleanTaskResult` is the
/// concrete derived result the task holds by value.
#[derive(Debug, Default, Clone)]
pub struct TaskResult;

/// Port of `Scheduler::CBooleanTaskResult`. The SAT/UNSAT boolean a satisfiable
/// task installs; `: public CTaskResult` folded in as `base`.
#[derive(Debug, Default, Clone)]
pub struct BooleanTaskResult {
    /// `CTaskResult` base.
    pub base: TaskResult,
    /// `bool mValidResult`.
    pub valid_result: bool,
    /// `bool mResultValue`.
    pub result_value: bool,
}

impl BooleanTaskResult {
    /// Port of `CBooleanTaskResult::CBooleanTaskResult`.
    pub fn new() -> Self {
        BooleanTaskResult::default()
    }
    /// Port of `CBooleanTaskResult::hasResult`.
    pub fn has_result(&self) -> bool {
        self.valid_result
    }

    /// Port of `CBooleanTaskResult::getResultValue`.
    pub fn get_result_value(&self) -> bool {
        self.result_value
    }

    /// Port of `CBooleanTaskResult::hasResultValue` (`testValue` defaults to `true`).
    pub fn has_result_value(&self, test_value: bool) -> bool {
        self.result_value == test_value
    }

    /// Port of `CBooleanTaskResult::setResultValue`.
    pub fn set_result_value(&mut self, result_value: bool) -> &mut Self {
        self.result_value = result_value;
        self
    }

    /// Port of `CBooleanTaskResult::setValidResult`.
    pub fn set_valid_result(&mut self, valid_result: bool) -> &mut Self {
        self.valid_result = valid_result;
        self
    }

    /// Port of `CBooleanTaskResult::installResult`.
    ///
    /// KONCLUDE-PORT-NOTE[threading]: this is the single-writer result install,
    /// guarded by `has_result()` checks in the status propagator
    /// (first-finisher-wins). Faithful inline port; under the worker pool it runs
    /// under the scheduler's per-task serialization.
    pub fn install_result(&mut self, result_value: bool) -> &mut Self {
        self.result_value = result_value;
        self.valid_result = true;
        self
    }
}

/// Port of `Scheduler::CTaskHandleContext` (abstract `: public CContext`;
/// `getTaskHandleMemoryAllocationManager()` is pure virtual, no data members).
#[derive(Debug, Default, Clone)]
pub struct TaskHandleContext;

/// Port of `Scheduler::CTaskCallbackExecuter` (abstract; `executeCallback()` is
/// pure virtual, no data members).
#[derive(Debug, Default, Clone)]
pub struct TaskCallbackExecuter;

/// Port of `Scheduler::CTaskStatusPropagator` (abstract; `updateTaskStatus()` /
/// `completeTaskStatus()` are pure virtual, no data members).
#[derive(Debug, Default, Clone)]
pub struct TaskStatusPropagator;

/// Port of `Scheduler::CTask`.
///
/// The base work item: a node in the per-branch task tree. `: public
/// CSortedLinkerBase<CTask*,CTask,CTask>, public CMemoryPoolContainer, public
/// CDeletionContainer` — the linker/pool/deletion mixins are the scheduler's
/// intrusive plumbing and carry no calculus-relevant data here, so only the
/// declared protected member fields are ported.
pub struct Task {
    /// `cint64 mTaskID`.
    pub task_id: Cint64,
    /// `cint64 mTaskType`.
    pub task_type: Cint64,
    /// `double mTaskPriority`.
    pub task_priority: f64,
    /// `bool mTaskRelevant`.
    pub task_relevant: bool,
    /// `bool mTaskDispensMarked`.
    pub task_dispens_marked: bool,

    /// `CTaskStatus* mTaskStatus`. [pointer-alias] → the derived task's by-value
    /// status (set in `createTaskStatus`).
    pub task_status: TaskStatusId,
    /// `CTaskResult* mTaskResult`. [pointer-alias] opaque handle pointing at the
    /// derived task's by-value `CBooleanTaskResult` (`INVALID` == `nullptr`).
    pub task_result: Cint64,

    /// `CTaskContext* mTaskContext`. [api] opaque — `CTaskContext` is scheduler
    /// plumbing (not yet ported).
    pub task_context: Cint64,
    /// `CTaskOwner* mTaskOwner`. [api] opaque.
    pub task_owner: Cint64,

    /// `CTask* mParentTask`.
    pub parent_task: TaskId,
    /// `CTask* mRootTask`.
    pub root_task: TaskId,

    /// `cint64 mActiveTaskReferenceCount`.
    ///
    /// KONCLUDE-PORT-NOTE[threading]: in the concurrent scheduler this is an
    /// atomic counter (`incActiveReferenceCount`/`dec...`) the scheduler uses to
    /// know when a subtree is done. Single-thread-first: kept as a plain
    /// `Cint64`; it promotes to `AtomicI64` when the worker pool lands. Only the
    /// status propagator races on it, under per-task serialization.
    pub active_task_reference_count: Cint64,
    /// `cint64 mDependedStatusUpdatesCount`. [threading] sibling atomic of
    /// `active_task_reference_count`; same single-thread-first note.
    pub depended_status_updates_count: Cint64,

    /// `cint64 mTaskDepth`.
    pub task_depth: Cint64,

    /// `CXNegLinker<CTask*>* mReferencedTaskLinker`. [ownership] intrusive neg-linker
    /// chain → owned `Vec<NegLink<TaskId>>`, head-at-front (CLinker convention).
    pub referenced_task_linker: Vec<NegLink<TaskId>>,
    /// `CNegator* mCompletionNegator`. [api] opaque.
    pub completion_negator: Cint64,
    /// `CCallbackData* mCallbackLinker`. [api] opaque head-front callback linker.
    pub callback_linker: Cint64,

    /// `bool mCompletionRequested`.
    pub completion_requested: bool,
}

impl Default for Task {
    fn default() -> Self {
        Task {
            task_id: -1,
            task_type: -1,
            task_priority: 0.0,
            task_relevant: false,
            task_dispens_marked: false,
            task_status: Id::NONE,
            task_result: -1,
            task_context: -1,
            task_owner: -1,
            parent_task: Id::NONE,
            root_task: Id::NONE,
            active_task_reference_count: 0,
            depended_status_updates_count: 0,
            task_depth: 0,
            referenced_task_linker: Vec::new(),
            completion_negator: -1,
            callback_linker: -1,
            completion_requested: false,
        }
    }
}

impl Task {
    /// Port of `CTask::CTask`.
    pub fn new() -> Self {
        Task::default()
    }
    /// Port of `CTask::setTaskID`.
    pub fn set_task_id(&mut self, id: Cint64) -> &mut Self {
        self.task_id = id;
        self
    }

    /// Port of `CTask::getTaskID`.
    pub fn get_task_id(&self) -> Cint64 {
        self.task_id
    }

    /// Port of `CTask::setTaskDepth`.
    pub fn set_task_depth(&mut self, task_depth: Cint64) -> &mut Self {
        self.task_depth = task_depth;
        self
    }

    /// Port of `CTask::getTaskDepth`.
    pub fn get_task_depth(&self) -> Cint64 {
        self.task_depth
    }

    /// Port of `CTask::setTaskType`.
    pub fn set_task_type(&mut self, task_type: Cint64) -> &mut Self {
        self.task_type = task_type;
        self
    }

    /// Port of `CTask::getTaskType`.
    pub fn get_task_type(&self) -> Cint64 {
        self.task_type
    }

    /// Port of `CTask::getTaskPriority`.
    pub fn get_task_priority(&self) -> f64 {
        self.task_priority
    }

    /// Port of `CTask::setTaskPriority`.
    pub fn set_task_priority(&mut self, task_priority: f64) -> &mut Self {
        self.task_priority = task_priority;
        self
    }

    /// Port of `CTask::getParentTask`.
    pub fn get_parent_task(&self) -> TaskId {
        self.parent_task
    }

    /// Port of `CTask::getRootTask`.
    pub fn get_root_task(&self) -> TaskId {
        self.root_task
    }

    /// Port of `CTask::setParentTask`.
    pub fn set_parent_task(&mut self, parent_task: TaskId) -> &mut Self {
        self.parent_task = parent_task;
        self
    }

    /// Port of `CTask::setRootTask`.
    pub fn set_root_task(&mut self, root_task: TaskId) -> &mut Self {
        self.root_task = root_task;
        self
    }

    /// Port of `CTask::getTaskResult`. [pointer-alias] opaque handle into the
    /// derived task's by-value `CBooleanTaskResult` (`INVALID` == `nullptr`).
    pub fn get_task_result(&self) -> Cint64 {
        self.task_result
    }

    /// Port of `CTask::getTaskStatus`.
    pub fn get_task_status(&self) -> TaskStatusId {
        self.task_status
    }

    /// Port of `CTask::getTaskContext`.
    ///
    /// W6-DEFER[api]: bump-allocates a `CTaskContextBase` from the task pool on
    /// first call (`CTaskMemoryPoolAllocationManager::allocateMemoryToContainer`)
    /// and back-points `mTaskContext`, else `updateContext`. Needs the
    /// `CTaskHandleContext` + memory pool (scheduler plumbing, [memory-pool]); the
    /// derived `CSatisfiableCalculationTask` overrides this to the process context.
    pub fn get_task_context(&mut self) -> Cint64 {
        // if !mTaskContext { mTaskContext = new CTaskContextBase(this,context); }
        // else { mTaskContext->updateContext(context); }
        // return mTaskContext;
        self.task_context
    }

    /// Port of `CTask::decActiveReferenceCount` (`decCount` defaults to 1).
    ///
    /// KONCLUDE-PORT-NOTE[threading]: an atomic counter in the concurrent
    /// scheduler (`AtomicI64`); single-thread-first kept as a plain `Cint64`.
    pub fn dec_active_reference_count(&mut self, dec_count: Cint64) -> &mut Self {
        self.active_task_reference_count -= dec_count;
        self
    }

    /// Port of `CTask::incActiveReferenceCount` (`incCount` defaults to 1).
    /// [threading] — see `dec_active_reference_count`.
    pub fn inc_active_reference_count(&mut self, inc_count: Cint64) -> &mut Self {
        self.active_task_reference_count += inc_count;
        self
    }

    /// Port of `CTask::getActiveReferenceCount`.
    pub fn get_active_reference_count(&self) -> Cint64 {
        self.active_task_reference_count
    }

    /// Port of `CTask::hasActiveReferencedTask`.
    pub fn has_active_referenced_task(&self) -> bool {
        self.active_task_reference_count > 0
    }

    /// Port of `CTask::decDependedStatusUpdatesCount` (`decCount` defaults to 1).
    /// [threading] — see `dec_active_reference_count`.
    pub fn dec_depended_status_updates_count(&mut self, dec_count: Cint64) -> &mut Self {
        self.depended_status_updates_count -= dec_count;
        self
    }

    /// Port of `CTask::incDependedStatusUpdatesCount` (`incCount` defaults to 1).
    /// [threading] — see `dec_active_reference_count`.
    pub fn inc_depended_status_updates_count(&mut self, inc_count: Cint64) -> &mut Self {
        self.depended_status_updates_count += inc_count;
        self
    }

    /// Port of `CTask::getDependedStatusUpdatesCount`.
    pub fn get_depended_status_updates_count(&self) -> Cint64 {
        self.depended_status_updates_count
    }

    /// Port of `CTask::hasDependedStatusUpdates`.
    pub fn has_depended_status_updates(&self) -> bool {
        self.depended_status_updates_count > 0
    }

    /// Port of `CTask::hasDependedStatusUpdatesOrActiveReferencedTasks`.
    pub fn has_depended_status_updates_or_active_referenced_tasks(&self) -> bool {
        self.has_depended_status_updates() || self.has_active_referenced_task()
    }

    /// Port of `CTask::makeTaskReference`.
    ///
    /// W6-DEFER[api]: links `dependedTask` as a child (set its parent/root/depth),
    /// bumps `mActiveTaskReferenceCount`, allocates a child `CXNegLinker` from the
    /// task context's memory allocator and prepends it to `mReferencedTaskLinker`,
    /// and wires the depended task's completion-negator connector. The depended
    /// task is a `TaskId`; resolving it needs the (not-yet-ported) task arena, and
    /// the linker alloc needs the task pool ([memory-pool]).
    pub fn make_task_reference(&mut self, _depended_task: TaskId) -> &mut Self {
        // dependedTask->setParentTask(this); dependedTask->setRootTask(mRootTask);
        // dependedTask->setTaskDepth(mTaskDepth+1); mActiveTaskReferenceCount++;
        // CTaskContext* taskContext = getTaskContext(handlerContext);
        // childNegLinker = alloc CXNegLinker; mReferencedTaskLinker = childNegLinker->init(dependedTask,true,mReferencedTaskLinker);
        // dependedTask->setCompletionNegatorConnector(childNegLinker);
        self.active_task_reference_count += 1;
        self
    }

    /// Port of `CTask::initTask`.
    ///
    /// W6-DEFER[api]: resets the per-task fields (done below), creates the task
    /// status + result via the virtual factories, and, when a parent exists, calls
    /// `parentTask->makeTaskReference(this)` + copies the parent root. The factory
    /// calls + the parent linkage + `mRootTask = this` (self's own id) need the
    /// task arena/handler context; the field resets are real.
    pub fn init_task(&mut self, parent_task: TaskId) -> &mut Self {
        // initLinker(this,nullptr);
        self.task_status = Id::NONE; // mTaskStatus = nullptr
        self.task_result = INVALID; // mTaskResult = nullptr
                                    // mRootTask = this;  // W6-DEFER[api]: needs self's own TaskId
        self.parent_task = Id::NONE;
        self.task_context = INVALID;
        self.completion_negator = INVALID;
        self.referenced_task_linker = Vec::new();
        self.callback_linker = INVALID;
        self.task_owner = INVALID;
        self.task_id = 0;
        self.task_priority = 0.;
        self.active_task_reference_count = 0;
        self.depended_status_updates_count = 0;
        self.task_depth = 0;
        self.completion_requested = false;
        self.task_relevant = false;
        self.task_dispens_marked = false;
        self.task_type = 0;
        // mTaskStatus = createTaskStatus(handlerContext);  // virtual, derived-owned
        // mTaskResult = createTaskResult(handlerContext);  // virtual, derived-owned
        // if (parentTask) { parentTask->makeTaskReference(this); mRootTask = parentTask->getRootTask(); }
        let _ = parent_task;
        self
    }

    /// Port of `CTask::getReferencedTaskLinker`. Head→tail order (CLinker
    /// head-front convention).
    pub fn get_referenced_task_linker(&self) -> &[NegLink<TaskId>] {
        &self.referenced_task_linker
    }

    /// Port of `CTask::setReferencedTaskLinker`.
    pub fn set_referenced_task_linker(
        &mut self,
        referenced_task_linker: Vec<NegLink<TaskId>>,
    ) -> &mut Self {
        self.referenced_task_linker = referenced_task_linker;
        self
    }

    /// Port of `CTask::appendReferencedTaskLinker`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: C++ splices the passed chain in FRONT
    /// (`linker->getLastListLink()->setNext(mReferencedTaskLinker)`); head-front
    /// Vec ⇒ prepend the chain, keeping its head as the new head.
    pub fn append_referenced_task_linker(
        &mut self,
        mut referenced_task_linker: Vec<NegLink<TaskId>>,
    ) -> &mut Self {
        referenced_task_linker.append(&mut self.referenced_task_linker);
        self.referenced_task_linker = referenced_task_linker;
        self
    }

    /// Port of `CTask::setCompletionNegatorConnector`.
    pub fn set_completion_negator_connector(&mut self, negator: Cint64) -> &mut Self {
        self.completion_negator = negator;
        self
    }

    /// Port of `CTask::completeTask`.
    ///
    /// W6-DEFER[api]: `if (mCompletionNegator) mCompletionNegator->setNegation(false);`
    /// — the completion negator is an opaque scheduler `CNegator*`; the
    /// `setNegation(false)` deref is deferred.
    pub fn complete_task(&mut self) -> &mut Self {
        // if (mCompletionNegator) { mCompletionNegator->setNegation(false); }
        self
    }

    /// Port of `CTask::getCallbackLinker`. [api] opaque head-front callback linker.
    pub fn get_callback_linker(&self) -> Cint64 {
        self.callback_linker
    }

    /// Port of `CTask::setCallbackLinker`.
    pub fn set_callback_linker(&mut self, callback: Cint64) -> &mut Self {
        self.callback_linker = callback;
        self
    }

    /// Port of `CTask::addCallbackLinker`.
    ///
    /// W6-DEFER[api]: `mCallbackLinker = callback->getLastListLink()->setNext(mCallbackLinker)`
    /// — front-splices the callback chain; the `CCallbackData*` deref is opaque
    /// until the callback subtree is ported. Set the field as the new head.
    pub fn add_callback_linker(&mut self, callback: Cint64) -> &mut Self {
        // mCallbackLinker = callback->getLastListLink()->setNext(mCallbackLinker);
        self.callback_linker = callback;
        self
    }

    /// Port of `CTask::getTaskOwner`. [api] opaque `CTaskOwner*`.
    pub fn get_task_owner(&self) -> Cint64 {
        self.task_owner
    }

    /// Port of `CTask::setTaskOwner`.
    pub fn set_task_owner(&mut self, task_owner: Cint64) -> &mut Self {
        self.task_owner = task_owner;
        self
    }

    /// Port of `CTask::clearTaskOwner`.
    pub fn clear_task_owner(&mut self) -> &mut Self {
        self.task_owner = INVALID;
        self
    }

    /// Port of `CTask::hasTaskOwner(CTaskOwner*)`.
    pub fn has_task_owner_eq(&self, task_owner: Cint64) -> bool {
        self.task_owner == task_owner
    }

    /// Port of `CTask::hasTaskOwner()` (`return mTaskOwner;` — non-null pointer).
    pub fn has_task_owner(&self) -> bool {
        self.task_owner >= 0
    }

    /// Port of `CTask::hasNoTaskOwnerAndNoParentTask`.
    pub fn has_no_task_owner_and_no_parent_task(&self) -> bool {
        self.task_owner == INVALID && self.parent_task.is_none()
    }

    /// Port of `CTask::clearUninitializedReferenceTasks`.
    ///
    /// W6-DEFER[api]: walks `mReferencedTaskLinker`, un-negates entries whose
    /// referenced task is still `TSUNINITIALIZED` and decrements
    /// `mActiveTaskReferenceCount`. The per-entry status test
    /// (`getData()->getTaskStatus()->isTaskStateUNINITIALIZED()`) derefs the
    /// referenced `TaskId` + its status, needing the (not-yet-ported) task arena.
    pub fn clear_uninitialized_reference_tasks(&mut self) -> bool {
        // bool clearedRefTasks = false;
        // for refTaskIt in &mut mReferencedTaskLinker {
        //   if (refTaskIt.isNegated() && refTaskIt.getData()->getTaskStatus()->isTaskStateUNINITIALIZED()) {
        //     refTaskIt.setNegation(false); --mActiveTaskReferenceCount; clearedRefTasks = true; } }
        false
    }

    /// Port of `CTask::setCompletionRequested`.
    pub fn set_completion_requested(&mut self, requested: bool) -> &mut Self {
        self.completion_requested = requested;
        self
    }

    /// Port of `CTask::getCompletionRequested`.
    pub fn get_completion_requested(&self) -> bool {
        self.completion_requested
    }

    /// Port of `CTask::isCompletionRequested`.
    pub fn is_completion_requested(&self) -> bool {
        self.completion_requested
    }

    /// Port of `CTask::isTaskRelevant`.
    pub fn is_task_relevant(&self) -> bool {
        self.task_relevant
    }

    /// Port of `CTask::setTaskRelevant`.
    pub fn set_task_relevant(&mut self, relevant: bool) -> &mut Self {
        self.task_relevant = relevant;
        self
    }

    /// Port of `CTask::isTaskDispenseMarked`.
    pub fn is_task_dispense_marked(&self) -> bool {
        self.task_dispens_marked
    }

    /// Port of `CTask::setTaskDispenseMarked`.
    pub fn set_task_dispense_marked(&mut self, dispenseable: bool) -> &mut Self {
        self.task_dispens_marked = dispenseable;
        self
    }

    /// Port of `CTask::sortedLinkerDataCompare` (the priority sort predicate; a
    /// `static inline` comparing two tasks' priorities, `before >= data2`).
    /// [pointer-alias] takes the two priorities directly (the caller resolves the
    /// `CTask*`s through the arena).
    pub fn sorted_linker_data_compare(before_priority: f64, data2_priority: f64) -> bool {
        before_priority >= data2_priority
    }

    // createTaskStatus / createTaskResult are pure-virtual factories on the C++
    // base (`= 0`); the concrete bodies live on the deriving
    // `CSatisfiableCalculationTask` (see `satisfiable_task.rs`), so the base has no
    // body to port here (the Rust no-inheritance idiom dispatches them on the
    // derived struct directly).
}
