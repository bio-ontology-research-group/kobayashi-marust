//! `calculation::manager` — the calculation-manager controllers (the ENTRY point).
//!
//! Ports Konclude:
//!   * `Source/Reasoner/Kernel/Calculation/CCalculationManager.h`
//!     (`CCalculationManager`, abstract — no members), and
//!   * `Source/Reasoner/Kernel/Calculation/CConcurrentTaskCalculationManager.h`
//!     (`CConcurrentTaskCalculationManager`, the concrete ENTRY-POINT controller
//!     that drives calculation: posts satisfiability tasks to the scheduler thread
//!     and collects per-thread statistics).
//!
//! Struct-definition unit only (wave W4): `calculateJob(s)` / `calculateTask` /
//! `initializeManager` / the statistics + error-string getters are deferred to the
//! `// W4-CALC method-batch` below.
//!
//! KONCLUDE-PORT-NOTE[ownership]: the entry-point manager does NOT hold the two
//! `TaskHandleAlgorithm`s (completion + saturation) by value or by Id. Per the C++
//! `.h`, it holds the calculation ENVIRONMENT (`mTaskCalcEn`); each per-thread
//! processor unit inside that environment builds + owns its own private
//! `CTaskHandleAlgorithm` instance via the `TaskHandleAlgorithmBuilder` seam (see
//! `CConfigDependedCalculationEnvironmentFactory::createCalculationContext`). So
//! the completion/saturation algorithms are reached transitively
//! manager → environment → (opaque [threading]) processor unit → algorithm. The
//! builder is the only place the choice of completion-vs-saturation is made.

#![allow(dead_code)]

use std::collections::HashMap;

use super::environment::ConcurrentTaskCalculationEnvironment;
use super::env_factory::ConfigDependedCalculationEnvironmentFactory;
use super::super::model::substrate::{Cint64, INVALID};

/// Port of `CCalculationManager`.
///
/// Abstract base — no member variables in the C++ `.h`. The concrete
/// `ConcurrentTaskCalculationManager` folds it in as `base`.
#[derive(Default)]
pub struct CalculationManager {
    // No member variables (abstract base).
}

impl CalculationManager {
    /// Port of `CCalculationManager::CCalculationManager`.
    pub fn new() -> Self {
        CalculationManager {}
    }

    /// Port of `CCalculationManager::calculateJobs`.
    ///
    /// The abstract-base default: iterate the job/callback list and dispatch each
    /// pair through the (pure-virtual) `calculateJob`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: `CCalculationJob*` / `CCallbackData*` are `Query/`
    /// subtree types → opaque `Cint64`. `calculateJob` is pure virtual on this base;
    /// the single-inheritance port cannot dispatch to the derived override from the
    /// base struct, and the concrete `ConcurrentTaskCalculationManager` overrides
    /// `calculate_jobs` outright, so this base loop is never the live path.
    pub fn calculate_jobs(&mut self, job_callback_list: &[(Cint64, Cint64)]) -> &mut Self {
        for &(job, callback_data) in job_callback_list.iter() {
            // W6-DEFER[api]: calculateJob(job, callbackData) — pure-virtual dispatch.
            let _ = (job, callback_data);
        }
        self
    }
}

/// Port of `CConcurrentTaskCalculationManager`.
///
/// The concrete, event-driven calculation entry-point controller. `calculateTask`
/// posts a `CSatisfiableCalculationTask` to the scheduler unit's event handler; a
/// worker thread then runs its private `CTaskHandleAlgorithm::handleTask` (the
/// saturation pre-pass or the full completion handler).
///
/// W4-CALC method-batch (filled): `calculate_jobs`, `calculate_job`,
/// `calculate_task`, `initialize_manager`, `get_calculation_context`,
/// `get_calculation_error_string`, `get_calculation_statistics`,
/// `get_updated_calculation_statistics`,
/// `get_calculation_approximated_remaining_tasks_count`.
pub struct ConcurrentTaskCalculationManager {
    /// The folded-in `CCalculationManager` base (no members; kept for
    /// method-by-method diffability with the C++ inheritance).
    pub base: CalculationManager,

    /// `CCalculationEnviroment* calcContext` (.h 89).
    /// KONCLUDE-PORT-NOTE[ownership]: in C++ `calcContext` and `mTaskCalcEn` are
    /// two pointers (base-typed and derived-typed) to the SAME owned environment.
    /// The port holds the concrete env BY VALUE in `task_calc_en` (single owner,
    /// the idiom `completion/context.rs` uses for its by-value databox); this
    /// `calc_context` is the opaque `Cint64` ALIAS of that base view
    /// (`INVALID` == `nullptr`).
    pub calc_context: Cint64,
    /// `CConcurrentTaskCalculationEnvironment* mTaskCalcEn` (.h 90).
    /// KONCLUDE-PORT-NOTE[ownership]: the manager OWNS the environment (newed by
    /// the env factory and handed over), so it is held here by value.
    pub task_calc_en: ConcurrentTaskCalculationEnvironment,
    /// `CGeneratorTaskHandleContextBase* mGenTaskHandleContext` (.h 91).
    /// KONCLUDE-PORT-NOTE[api]: cross-subtree (`Generator/`) → opaque `Cint64`.
    pub gen_task_handle_context: Cint64,
    /// `CMemoryTemporaryAllocationManager* mTemMemMan` (.h 92).
    /// KONCLUDE-PORT-NOTE[memory-pool]: pool allocator → opaque `Cint64`.
    pub tem_mem_man: Cint64,
}

impl ConcurrentTaskCalculationManager {
    /// Port of
    /// `CConcurrentTaskCalculationManager::CConcurrentTaskCalculationManager`
    /// (`CWatchDog* watchDog = 0`).
    /// KONCLUDE-PORT-NOTE[threading]: the ctor `CWatchDog*` argument is not stored
    /// as a member in the C++ `.h`, so the port takes no watchdog field.
    /// The environment is empty until `initialize_manager` populates it.
    pub fn new() -> Self {
        ConcurrentTaskCalculationManager {
            base: CalculationManager::new(),
            calc_context: INVALID,
            task_calc_en: ConcurrentTaskCalculationEnvironment::new(),
            gen_task_handle_context: INVALID,
            tem_mem_man: INVALID,
        }
    }

    /// Port of `CConcurrentTaskCalculationManager::calculateTask`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: `CSatisfiableCalculationTask*` is a `Task/` subtree
    /// type → opaque `Cint64`. The C++ `if (mTaskCalcEn)` null-guard maps to the
    /// `calc_context` opaque alias (`INVALID` == `nullptr`).
    pub fn calculate_task(&mut self, task: Cint64) -> &mut Self {
        if self.calc_context != INVALID {
            // W6-DEFER[threading]: CTaskEventCommunicator::postSendTaskScheduleEvent(
            //   mTaskCalcEn->getSchedulerTaskProcessorUnit()->getEventHandler(),
            //   task, mTemMemMan) posts the satisfiability task to the scheduler
            // unit's event handler; the Scheduler/ + Task/ event machinery (live OS
            // threads) is opaque.
            let _scheduler_unit = self.task_calc_en.scheduler_unit;
            let _ = (task, self.tem_mem_man);
        }
        self
    }

    /// Port of `CConcurrentTaskCalculationManager::calculateJob`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: the `CSatisfiableCalculationTaskFromCalculationJobGenerator`
    /// (`Generator/` subtree) that turns a `job`+`callbackData` into a
    /// `CSatisfiableCalculationTask*` is opaque; the produced task is `Cint64`.
    pub fn calculate_job(&mut self, job: Cint64, callback_data: Cint64) -> &mut Self {
        // W6-DEFER[api]: gen(mGenTaskHandleContext).createSatisfiableCalculationTask(job, callbackData)
        let task: Cint64 = INVALID;
        let _ = (job, callback_data, self.gen_task_handle_context);
        if task != INVALID {
            self.calculate_task(task);
        }
        self
    }

    /// Port of `CConcurrentTaskCalculationManager::calculateJobs` (override).
    ///
    /// Builds one task per job via the generator, splicing them into a single task
    /// linker chain, then schedules the chain head.
    /// KONCLUDE-PORT-NOTE[api]: generator + `CSatisfiableCalculationTask` are opaque.
    pub fn calculate_jobs(&mut self, job_callback_list: &[(Cint64, Cint64)]) -> &mut Self {
        let mut task_linker: Cint64 = INVALID;
        // W6-DEFER[api]: CSatisfiableCalculationTaskFromCalculationJobGenerator gen(mGenTaskHandleContext)
        for &(job, callback_data) in job_callback_list.iter() {
            // W6-DEFER[api]: gen.createSatisfiableCalculationTask(job, callbackData)
            let task: Cint64 = INVALID;
            let _ = (job, callback_data, self.gen_task_handle_context);
            if task != INVALID {
                // taskLinker = (CSatisfiableCalculationTask*)task->append(taskLinker)
                // CLinker head-front prepend; opaque chain (the new task becomes head).
                task_linker = task;
            }
        }
        if task_linker != INVALID {
            self.calculate_task(task_linker);
        }
        self
    }

    /// Port of `CConcurrentTaskCalculationManager::initializeManager`.
    ///
    /// Builds the calculation environment via the env factory, then sets up the
    /// task-handle generator context + its temporary memory allocation manager.
    /// KONCLUDE-PORT-NOTE[ownership]: the C++ `dynamic_cast<CConcurrentTaskCalculationEnvironment*>`
    /// is a no-op in the port — the env factory already returns the concrete env,
    /// held here BY VALUE in `task_calc_en`; `calc_context` is the opaque base-view
    /// alias (`0` == a live non-null pointer).
    pub fn initialize_manager(
        &mut self,
        context_factory: &mut ConfigDependedCalculationEnvironmentFactory,
        configuration_provider: Cint64,
    ) -> &mut Self {
        self.task_calc_en = context_factory.create_calculation_context(configuration_provider);
        self.calc_context = 0;
        // W6-DEFER[api]: CGeneratorTaskHandleContextBase (Generator/ subtree) and its
        // getTaskHandleMemoryAllocationManager() ([memory-pool]) are opaque.
        self.gen_task_handle_context = 0;
        self.tem_mem_man = 0;
        self
    }

    /// Port of `CConcurrentTaskCalculationManager::getCalculationContext`.
    /// Returns the base-view alias of the owned environment (`INVALID` == nullptr).
    pub fn get_calculation_context(&self) -> Cint64 {
        self.calc_context
    }

    /// Port of `CConcurrentTaskCalculationManager::getCalculationErrorString`.
    /// KONCLUDE-PORT-NOTE[api]: `QString` → owned `String`. The "Unknow fatal error."
    /// spelling is preserved verbatim from the C++.
    pub fn get_calculation_error_string(&self, error_code: Cint64) -> String {
        match error_code {
            1 => String::from("Nominal couldn't be resolved."),
            2 => String::from(
                "Memory allocation failed / out of memory / memory allocation limit reached.",
            ),
            3 => String::from("Unknow fatal error."),
            _ => String::from("Unknown error."),
        }
    }

    /// Port of `CConcurrentTaskCalculationManager::getCalculationStatistics`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: `QHash<QString,cint64>*` → owned `HashMap<String,Cint64>`.
    /// The C++ `dynamic_cast` always succeeds here (we own the concrete env), so the
    /// guard is the `calc_context` opaque-alias null check.
    pub fn get_calculation_statistics(&mut self) -> HashMap<String, Cint64> {
        let mut stat_hash: HashMap<String, Cint64> = HashMap::new();
        if self.calc_context != INVALID {
            let con_task_env = &self.task_calc_en;
            stat_hash.insert(
                String::from("calculation-computing-time"),
                con_task_env.get_calculation_compution_time(),
            );
            stat_hash.insert(
                String::from("calculation-blocking-time"),
                con_task_env.get_calculation_blocking_time(),
            );
            stat_hash.insert(
                String::from("calculation-memory-consumption"),
                con_task_env.get_calculation_memory_consumption(),
            );
            stat_hash.insert(
                String::from("calculation-memory-reservation"),
                con_task_env.get_calculation_memory_reserved(),
            );

            stat_hash.insert(
                String::from("calculation-tasks-processed-count"),
                con_task_env.get_calculation_statistic_tasks_processed_count(),
            );
            stat_hash.insert(
                String::from("calculation-tasks-created-count"),
                con_task_env.get_calculation_statistic_tasks_created_count(),
            );
            stat_hash.insert(
                String::from("calculation-tasks-added-count"),
                con_task_env.get_calculation_statistic_tasks_added_count(),
            );
            stat_hash.insert(
                String::from("calculation-tasks-updated-count"),
                con_task_env.get_calculation_statistic_tasks_updated_count(),
            );
            stat_hash.insert(
                String::from("calculation-tasks-completed-count"),
                con_task_env.get_calculation_statistic_tasks_completed_count(),
            );
            stat_hash.insert(
                String::from("calculation-tasks-requested-count"),
                con_task_env.get_calculation_statistic_tasks_requested_count(),
            );
            stat_hash.insert(
                String::from("calculation-threads-blocking-count"),
                con_task_env.get_calculation_statistic_threads_blocked_count(),
            );
            stat_hash.insert(
                String::from("calculation-threads-events-processed-count"),
                con_task_env.get_calculation_statistic_events_processed_count(),
            );
        }
        stat_hash
    }

    /// Port of `CConcurrentTaskCalculationManager::getUpdatedCalculationStatistics`.
    /// Subtracts the supplied baseline from the live counters (the time/task deltas;
    /// the memory figures are reported absolute, matching the C++).
    pub fn get_updated_calculation_statistics(
        &mut self,
        stat: &HashMap<String, Cint64>,
    ) -> HashMap<String, Cint64> {
        let mut stat_hash: HashMap<String, Cint64> = HashMap::new();
        if self.calc_context != INVALID {
            let con_task_env = &self.task_calc_en;
            stat_hash.insert(
                String::from("calculation-computing-time"),
                con_task_env.get_calculation_compution_time()
                    - stat.get("calculation-computing-time").copied().unwrap_or(0),
            );
            stat_hash.insert(
                String::from("calculation-blocking-time"),
                con_task_env.get_calculation_blocking_time()
                    - stat.get("calculation-blocking-time").copied().unwrap_or(0),
            );
            stat_hash.insert(
                String::from("calculation-memory-consumption"),
                con_task_env.get_calculation_memory_consumption(),
            );
            stat_hash.insert(
                String::from("calculation-memory-reservation"),
                con_task_env.get_calculation_memory_reserved(),
            );

            stat_hash.insert(
                String::from("calculation-tasks-processed-count"),
                con_task_env.get_calculation_statistic_tasks_processed_count()
                    - stat.get("calculation-tasks-processed-count").copied().unwrap_or(0),
            );
            stat_hash.insert(
                String::from("calculation-tasks-created-count"),
                con_task_env.get_calculation_statistic_tasks_created_count()
                    - stat.get("calculation-tasks-created-count").copied().unwrap_or(0),
            );
            stat_hash.insert(
                String::from("calculation-tasks-added-count"),
                con_task_env.get_calculation_statistic_tasks_added_count()
                    - stat.get("calculation-tasks-added-count").copied().unwrap_or(0),
            );
            stat_hash.insert(
                String::from("calculation-tasks-updated-count"),
                con_task_env.get_calculation_statistic_tasks_updated_count()
                    - stat.get("calculation-tasks-updated-count").copied().unwrap_or(0),
            );
            stat_hash.insert(
                String::from("calculation-tasks-completed-count"),
                con_task_env.get_calculation_statistic_tasks_completed_count()
                    - stat.get("calculation-tasks-completed-count").copied().unwrap_or(0),
            );
            stat_hash.insert(
                String::from("calculation-tasks-requested-count"),
                con_task_env.get_calculation_statistic_tasks_requested_count()
                    - stat.get("calculation-tasks-requested-count").copied().unwrap_or(0),
            );
            stat_hash.insert(
                String::from("calculation-threads-blocking-count"),
                con_task_env.get_calculation_statistic_threads_blocked_count()
                    - stat.get("calculation-threads-blocking-count").copied().unwrap_or(0),
            );
            stat_hash.insert(
                String::from("calculation-threads-events-processed-count"),
                con_task_env.get_calculation_statistic_events_processed_count()
                    - stat.get("calculation-threads-events-processed-count").copied().unwrap_or(0),
            );
        }
        stat_hash
    }

    /// Port of `CConcurrentTaskCalculationManager::getCalculationApproximatedRemainingTasksCount`.
    pub fn get_calculation_approximated_remaining_tasks_count(&mut self) -> f64 {
        if self.calc_context != INVALID {
            return self
                .task_calc_en
                .get_calculation_approximated_remaining_tasks_count();
        }
        0.0
    }
}

impl Default for ConcurrentTaskCalculationManager {
    fn default() -> Self {
        Self::new()
    }
}
