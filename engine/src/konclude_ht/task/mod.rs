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

//! `task` — the Task/ scheduler + satisfiable-task subtree (Konclude
//! `Source/Reasoner/Kernel/Task/`): the cooperative task scheduler, the
//! `CSatisfiableCalculationTask` carrying the per-job calculation state, the
//! observer/message adapter bag, the configuration extension, and the status
//! propagation / callback seams that the calculation environment drives.
//!
//! Struct-definition wave (W6) — method bodies that touch the deferred
//! realization/answering machinery are stubbed behind `// W6-DEFER` markers.
//! Wired into `konclude_ht/mod.rs` alongside `calculation`.

#![allow(dead_code)]

pub mod adapters; // the 18 observer/message adapter markers
pub mod calculation_job; // CSatisfiableCalculationJob (Query-layer job adapter holder)
pub mod callback_executer; // CSatisfiableCalculationTaskJobCallbackExecuter
pub mod config; // CCalculationConfigurationExtension
pub mod satisfiable_task; // CSatisfiableCalculationTask (the per-job task)
pub mod scheduler; // CTaskScheduler + Task/TaskStatus/TaskResult bases
pub mod stats;
pub mod status_propagator; // CSatisfiableCalculationTaskStatusPropagator
pub mod task_data; // CTaskData variants (consistence/saturation/incremental) // CCalculationStatisticsCollector
