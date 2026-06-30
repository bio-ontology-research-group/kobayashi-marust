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

pub mod scheduler;          // CTaskScheduler + Task/TaskStatus/TaskResult bases
pub mod config;             // CCalculationConfigurationExtension
pub mod satisfiable_task;   // CSatisfiableCalculationTask (the per-job task)
pub mod task_data;          // CTaskData variants (consistence/saturation/incremental)
pub mod adapters;           // the 18 observer/message adapter markers
pub mod status_propagator;  // CSatisfiableCalculationTaskStatusPropagator
pub mod callback_executer;  // CSatisfiableCalculationTaskJobCallbackExecuter
pub mod stats;              // CCalculationStatisticsCollector
