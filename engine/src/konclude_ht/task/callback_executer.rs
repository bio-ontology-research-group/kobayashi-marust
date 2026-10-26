// SPDX-License-Identifier: LGPL-3.0-only
//
// This file is part of Kobayashi-MaRust (KM). It is a Rust translation of
// source code from the reasoning system Konclude, Copyright (C) by the
// Konclude Developer Team (<http://konclude.com/>,
// <https://github.com/konclude/Konclude>), which is licensed under version 3
// of the GNU Lesser General Public License (LGPLv3). As a derivative work it
// is distributed under the same licence.
// Translation Copyright (C) 2026 Robert Hoehndorf and the Bio-Ontology
// Research Group, KAUST.
//
// This file is free software: you can redistribute it and/or modify it under
// the terms of version 3 of the GNU Lesser General Public License as published
// by the Free Software Foundation. It is distributed in the hope that it will
// be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser
// General Public License for more details. Copies of the LGPLv3 and GPLv3
// accompany this repository as LICENSE-LGPL-3.0.txt and LICENSE-GPL-3.0.txt;
// see also <https://www.gnu.org/licenses/>.

//! `task::callback_executer` — the job-callback hand-back seam.
//!
//! Ports Konclude
//! `Source/Reasoner/Kernel/Task/CSatisfiableCalculationTaskJobCallbackExecuter.h`
//! (`: public CTaskCallbackExecuter`). `executeCallback(task, cb)` fires the
//! job's `CJobSatisfiableCallbackContextData` with the final boolean when the
//! root task completes — the hand-back to the query/consistency caller.
//!
//! The base declares no data members and the executer adds none; only the
//! `executeCallback` body — deferred to the `// W6-TASK method-batch` unit (it
//! depends on the Query `CJobSatisfiableCallbackContextData`, opaque until the
//! Query subtree is ported).

#![allow(dead_code)]

use super::super::model::substrate::Cint64;
use super::satisfiable_task::SatisfiableCalculationTask;
use super::scheduler::TaskCallbackExecuter;

/// Port of `Reasoner::Kernel::Task::CSatisfiableCalculationTaskJobCallbackExecuter`.
#[derive(Debug, Default, Clone)]
pub struct SatisfiableCalculationTaskJobCallbackExecuter {
    /// `CTaskCallbackExecuter` base (abstract; no data members).
    pub base: TaskCallbackExecuter,
}

impl SatisfiableCalculationTaskJobCallbackExecuter {
    /// Port of `CSatisfiableCalculationTaskJobCallbackExecuter::CSatisfiableCalculationTaskJobCallbackExecuter`.
    pub fn new() -> Self {
        SatisfiableCalculationTaskJobCallbackExecuter::default()
    }
    /// Port of `CSatisfiableCalculationTaskJobCallbackExecuter::executeCallback`.
    ///
    /// On a completion task, pull the boolean (SAT/UNSAT) or the error code off the
    /// finished task and hand it back to the job's satisfiable-callback context,
    /// then fire the callback — the hand-back to the query/consistency caller.
    ///
    /// KONCLUDE-PORT-NOTE[pointer-alias]: C++ down-casts the `CTask*` to
    /// `CSatisfiableCalculationTask*`; the port takes it directly (the result/status
    /// reads are real). `getTaskStatus()` resolves to the task's by-value
    /// `default_task_result`.
    ///
    /// W6-DEFER[api]: `callbackData` is the scheduler `CCallbackData*` carrying a
    /// Query `CJobSatisfiableCallbackContextData`; `getCallbackDataContext()`,
    /// `setCalculationError` / `setSatisfiable`, and `doCallback()` are opaque until
    /// the Query + callback subtrees are ported, so only their target reads are
    /// resolved here.
    pub fn execute_callback(
        &self,
        sat_calc_task: &mut SatisfiableCalculationTask,
        _callback_data: Cint64,
    ) -> bool {
        if sat_calc_task.is_calculation_tableau_completion_task() {
            // CJobSatisfiableCallbackContextData* satCallbackData = (...)callbackData->getCallbackDataContext();
            if sat_calc_task
                .get_satisfiable_calculation_task_result()
                .has_result()
            {
                // satCallbackData->setCalculationError(false,0);
                let _result_value = sat_calc_task
                    .get_satisfiable_calculation_task_result()
                    .get_result_value();
                // satCallbackData->setSatisfiable(_result_value);
            } else {
                let _error_code = sat_calc_task.default_task_result.get_error_code();
                // satCallbackData->setCalculationError(true,_error_code);
            }
        }
        // callbackData->doCallback();  // W6-DEFER[api]
        true
    }
}
