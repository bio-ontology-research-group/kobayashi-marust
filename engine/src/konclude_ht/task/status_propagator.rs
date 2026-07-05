//! `task::status_propagator` — the up/down result OR-collapse rule.
//!
//! Ports Konclude
//! `Source/Reasoner/Kernel/Task/CSatisfiableCalculationTaskStatusPropagator.h`
//! (`: public CTaskStatusPropagator`). The event-driven up/down result
//! propagation rule: on a child task finishing, propagate SAT(`true`) UP to the
//! parent (OR-semantics: any satisfiable child ⇒ parent satisfiable), cancel
//! sibling tasks once the parent has resolved, and propagate error/cancel state.
//! The core of how the branch task-tree collapses to one boolean.
//!
//! The base declares no data members and the propagator adds none; only the
//! `updateTaskStatus` / `completeTaskStatus` control-flow bodies (the interesting
//! logic of the layer) — deferred to the `// W6-TASK method-batch` unit.

#![allow(dead_code)]

use super::satisfiable_task::SatisfiableCalculationTask;
use super::scheduler::TaskStatusPropagator;

/// Port of `Reasoner::Kernel::Task::CSatisfiableCalculationTaskStatusPropagator`.
#[derive(Debug, Default, Clone)]
pub struct SatisfiableCalculationTaskStatusPropagator {
    /// `CTaskStatusPropagator` base (abstract; no data members).
    pub base: TaskStatusPropagator,
}

impl SatisfiableCalculationTaskStatusPropagator {
    /// Port of `CSatisfiableCalculationTaskStatusPropagator::CSatisfiableCalculationTaskStatusPropagator`.
    pub fn new() -> Self {
        SatisfiableCalculationTaskStatusPropagator::default()
    }
    /// Port of `CSatisfiableCalculationTaskStatusPropagator::updateTaskStatus`.
    ///
    /// The event-driven OR-collapse: an UNSAT child (or a parent already
    /// resolved/canceled/errored) cancels this subtree; an errored task pushes the
    /// error up; the FIRST satisfiable (SAT) child installs `true` on the parent and
    /// finishes — the first-finisher-wins rule that collapses the branch task-tree
    /// to one boolean.
    ///
    /// KONCLUDE-PORT-NOTE[pointer-alias]: C++ takes a `CTask*` and down-casts to
    /// `CSatisfiableCalculationTask*`; the port takes the satisfiable task directly.
    /// `getTaskStatus()` / `getSatisfiableCalculationTaskResult()` resolve to the
    /// task's by-value `default_task_result` / `bool_task_result` (createTaskStatus
    /// returns `&mDefaultTaskResult`, createTaskResult returns `&mBoolTaskResult`),
    /// so they are read/written in place.
    ///
    /// KONCLUDE-PORT-NOTE[threading]: `parent_task` is `satCalcTask->getParentTask()`
    /// resolved through the (not-yet-ported) task arena by the caller and passed in
    /// (W6-DEFER[api] at the call site). The first-finisher-wins install is guarded
    /// by `has_result()` and runs under the scheduler's per-task serialization, so
    /// the atomic reference counters need no extra locking here.
    pub fn update_task_status(
        &mut self,
        sat_calc_task: &mut SatisfiableCalculationTask,
        mut parent_task: Option<&mut SatisfiableCalculationTask>,
        more_down_propagation: &mut bool,
        more_up_propagation: &mut bool,
    ) -> bool {
        if sat_calc_task.default_task_result.is_processable()
            || sat_calc_task.default_task_result.is_error()
        {
            let mut cancel_tasks = false;

            if sat_calc_task.bool_task_result.has_result()
                && !sat_calc_task.bool_task_result.get_result_value()
            {
                cancel_tasks = true;
            }

            if !cancel_tasks {
                if let Some(parent) = &parent_task {
                    if parent.default_task_result.is_error()
                        || parent.default_task_result.is_canceled()
                        || (parent.bool_task_result.has_result()
                            && parent.bool_task_result.get_result_value())
                    {
                        cancel_tasks = true;
                    }
                }
            }

            if cancel_tasks {
                sat_calc_task.default_task_result.set_canceled(true);
                *more_down_propagation = true;
                return true;
            } else {
                if sat_calc_task.default_task_result.is_error() {
                    let error_code = sat_calc_task.default_task_result.get_error_code();
                    if let Some(parent) = &mut parent_task {
                        parent.default_task_result.set_error(true, error_code);
                    }
                    *more_down_propagation = true;
                    return true;
                } else if sat_calc_task.bool_task_result.has_result()
                    && sat_calc_task.bool_task_result.get_result_value()
                {
                    sat_calc_task.default_task_result.set_finished(true);

                    if let Some(parent) = &mut parent_task {
                        if !parent.bool_task_result.has_result() {
                            parent.bool_task_result.install_result(true);
                            *more_up_propagation = true;
                        }
                    }

                    *more_down_propagation = true;
                    return true;
                }
            }
        }
        false
    }

    /// Port of `CSatisfiableCalculationTaskStatusPropagator::completeTaskStatus`.
    ///
    /// Final completion of a task: an error propagates up to a non-errored parent;
    /// a SAT result finishes and installs `true` on the parent (first-finisher);
    /// a task that completed with NO result is the UNSAT verdict — install `false`
    /// and finish. See `update_task_status` for the [pointer-alias] / [threading]
    /// resolution of the by-value status/result and the caller-supplied parent.
    pub fn complete_task_status(
        &mut self,
        sat_calc_task: &mut SatisfiableCalculationTask,
        mut parent_task: Option<&mut SatisfiableCalculationTask>,
        more_up_propagation: &mut bool,
    ) -> bool {
        if sat_calc_task.default_task_result.is_processable()
            || sat_calc_task.default_task_result.is_error()
        {
            if sat_calc_task.default_task_result.is_error() {
                let error_code = sat_calc_task.default_task_result.get_error_code();
                if let Some(parent) = &mut parent_task {
                    if !parent.default_task_result.is_error() {
                        parent.default_task_result.set_error(true, error_code);
                        *more_up_propagation = true;
                        return true;
                    }
                }
            } else if sat_calc_task.bool_task_result.has_result() {
                sat_calc_task.default_task_result.set_finished(true);
                if sat_calc_task.bool_task_result.get_result_value() {
                    if let Some(parent) = &mut parent_task {
                        if !parent.bool_task_result.has_result() {
                            parent.bool_task_result.install_result(true);
                            *more_up_propagation = true;
                        }
                    }
                }
            } else {
                sat_calc_task.bool_task_result.install_result(false);
                sat_calc_task.default_task_result.set_finished(true);
            }
            return true;
        }
        false
    }
}
