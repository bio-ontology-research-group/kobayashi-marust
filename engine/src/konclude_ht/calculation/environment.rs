//! `calculation::environment` — the calculation environment controllers.
//!
//! Ports Konclude:
//!   * `Source/Reasoner/Kernel/Calculation/CCalculationEnviroment.h`
//!     (`CCalculationEnviroment`, abstract base — no members), and
//!   * `Source/Reasoner/Kernel/Calculation/CConcurrentTaskCalculationEnvironment.h`
//!     (`CConcurrentTaskCalculationEnvironment`, the concrete env that holds the
//!     processor-unit/thread pool + callback executer + status propagator).
//!
//! Struct-definition unit only (wave W4): the `init*`/`append*`/`get*` method
//! bodies are deferred to the `// W4-CALC method-batch` below.
//!
//! KONCLUDE-PORT-NOTE[threading]: every processor-unit / scheduler / completor /
//! worker-thread handle (`CSingleThreadTaskProcessorUnit*`,
//! `CTaskEventHandlerBasedScheduler*`, `CTaskEventHandlerBasedCompletor*`,
//! `CTaskProcessorThreadBase*`, `CTaskEventHandlerBasedProcessor*`) and the two
//! task callback/status objects live in the `Scheduler/` + `Task/` subtrees and
//! own live OS threads; they are opaque `Cint64` (`INVALID` == `nullptr`).
//! KONCLUDE-PORT-NOTE[memory-pool]: `CCentralizedAllocationLimitation*` is the
//! shared per-thread-pool memory limiter → opaque `Cint64`.

#![allow(dead_code)]

use super::super::model::substrate::{Cint64, INVALID};

/// Port of `CTaskProcessingStatistics::VECCOUNTERSIZE`
/// (`Scheduler/CTaskProcessingStatistics.h`, `const static cint64 = 10000`): the
/// fixed per-depth statistics counter-vector length.
pub const VECCOUNTERSIZE: usize = 10000;

/// Port of `CCalculationEnviroment`.
///
/// Abstract base — no member variables in the C++ `.h`. The concrete
/// `ConcurrentTaskCalculationEnvironment` folds it in as `base`.
#[derive(Default)]
pub struct CalculationEnviroment {
    // No member variables (abstract base).
}

impl CalculationEnviroment {
    /// Port of `CCalculationEnviroment::CCalculationEnviroment`.
    pub fn new() -> Self {
        CalculationEnviroment {}
    }
}

/// Port of `CConcurrentTaskCalculationEnvironment`.
///
/// The concrete calculation environment: it holds the scheduler/completor/worker
/// processor units (each owning a private `CTaskHandleAlgorithm` + memory pool),
/// the callback executer, the status propagator, the shared allocation limiter,
/// and the per-depth task-count statistics vectors.
///
/// W4-CALC method-batch (filled): `init_single_task_processor`,
/// `init_multi_task_processor`, `append_multi_task_processor`,
/// `init_callback_executer`, `init_status_propagator`, the `get*` processor-unit /
/// statistic accessors, `get/set_allocation_limitation`,
/// `get_calculation_approximated_remaining_tasks_count`.
pub struct ConcurrentTaskCalculationEnvironment {
    /// The folded-in `CCalculationEnviroment` base (no members; kept for
    /// method-by-method diffability with the C++ inheritance).
    pub base: CalculationEnviroment,

    // --- processor units (.h 122–124) ---
    /// `CSingleThreadTaskProcessorUnit* mProcessUnit`. [threading] opaque.
    pub process_unit: Cint64,
    /// `CTaskEventHandlerBasedScheduler* mSchedulerUnit`. [threading] opaque.
    pub scheduler_unit: Cint64,
    /// `CTaskEventHandlerBasedCompletor* mCompletorUnit`. [threading] opaque.
    pub completor_unit: Cint64,

    // --- thread / processor unit lists (.h 125–126) ---
    /// `QList<CTaskProcessorThreadBase*> mThreadUnitList`. [threading] each entry
    /// opaque (a worker-thread handle).
    pub thread_unit_list: Vec<Cint64>,
    /// `QList<CTaskEventHandlerBasedProcessor*> mProcessorUnitList`. [threading].
    pub processor_unit_list: Vec<Cint64>,

    // --- callback / status (.h 127–128) ---
    /// `CSatisfiableCalculationTaskJobCallbackExecuter* mCallbackExecuter`.
    /// [threading] opaque (Task-subtree callback executer).
    pub callback_executer: Cint64,
    /// `CSatisfiableCalculationTaskStatusPropagator* mStatusPropagator`.
    /// [threading] opaque.
    pub status_propagator: Cint64,

    // --- shared memory allocation limiter (.h 130) ---
    /// `CCentralizedAllocationLimitation* mAllocationLimitation`. [memory-pool]
    /// opaque (shared bound across the per-thread pools).
    pub allocation_limitation: Cint64,

    // --- per-depth task-count statistics (.h 132–135) ---
    /// `QVector<cint64> mTaskCreatedDepthCountVec`.
    pub task_created_depth_count_vec: Vec<Cint64>,
    /// `QVector<cint64> mTaskProcessedDepthCountVec`.
    pub task_processed_depth_count_vec: Vec<Cint64>,
    /// `QVector<double> mTaskRelativeIncreaseTaskPerDepthVec`.
    pub task_relative_increase_task_per_depth_vec: Vec<f64>,
    /// `QVector<double> mTaskTotalIncreaseTaskPerDepthVec`.
    pub task_total_increase_task_per_depth_vec: Vec<f64>,
}

impl ConcurrentTaskCalculationEnvironment {
    /// Port of
    /// `CConcurrentTaskCalculationEnvironment::CConcurrentTaskCalculationEnvironment`.
    /// KONCLUDE-PORT-NOTE[uninit]: the C++ ctor leaves the unit handles unset
    /// (filled by `init*`/`append*`); the port starts every handle `INVALID` and
    /// every collection empty.
    pub fn new() -> Self {
        ConcurrentTaskCalculationEnvironment {
            base: CalculationEnviroment::new(),
            process_unit: INVALID,
            scheduler_unit: INVALID,
            completor_unit: INVALID,
            thread_unit_list: Vec::new(),
            processor_unit_list: Vec::new(),
            callback_executer: INVALID,
            status_propagator: INVALID,
            allocation_limitation: INVALID,
            task_created_depth_count_vec: Vec::new(),
            task_processed_depth_count_vec: Vec::new(),
            task_relative_increase_task_per_depth_vec: Vec::new(),
            task_total_increase_task_per_depth_vec: Vec::new(),
        }
    }

    /// Port of `CConcurrentTaskCalculationEnvironment::initSingleTaskProcessor`.
    /// The single-thread unit serves as scheduler AND completor.
    /// KONCLUDE-PORT-NOTE[threading]: `CSingleThreadTaskProcessorUnit*` opaque.
    pub fn init_single_task_processor(&mut self, process_unit: Cint64) -> &mut Self {
        self.process_unit = process_unit;
        self.scheduler_unit = self.process_unit;
        self.completor_unit = self.process_unit;
        self.processor_unit_list.push(self.process_unit);
        self
    }

    /// Port of `CConcurrentTaskCalculationEnvironment::initMultiTaskProcessor`.
    /// KONCLUDE-PORT-NOTE[threading]: scheduler/completor thread handles opaque.
    pub fn init_multi_task_processor(
        &mut self,
        scheduler_unit: Cint64,
        completor_unit: Cint64,
    ) -> &mut Self {
        self.process_unit = INVALID;
        self.scheduler_unit = scheduler_unit;
        self.completor_unit = completor_unit;
        self.processor_unit_list.push(scheduler_unit);
        self.processor_unit_list.push(completor_unit);
        self.thread_unit_list.push(scheduler_unit);
        self.thread_unit_list.push(completor_unit);
        self
    }

    /// Port of `CConcurrentTaskCalculationEnvironment::appendMultiTaskProcessor`.
    pub fn append_multi_task_processor(&mut self, processor_unit: Cint64) -> &mut Self {
        self.processor_unit_list.push(processor_unit);
        self.thread_unit_list.push(processor_unit);
        self
    }

    /// Port of `CConcurrentTaskCalculationEnvironment::initCallbackExecuter`.
    pub fn init_callback_executer(&mut self, callback_executer: Cint64) -> &mut Self {
        self.callback_executer = callback_executer;
        self
    }

    /// Port of `CConcurrentTaskCalculationEnvironment::initStatusPropagator`.
    pub fn init_status_propagator(&mut self, status_propagator: Cint64) -> &mut Self {
        self.status_propagator = status_propagator;
        self
    }

    /// Port of `CConcurrentTaskCalculationEnvironment::setAllocationLimitation`.
    pub fn set_allocation_limitation(&mut self, allocation_limitation: Cint64) -> &mut Self {
        self.allocation_limitation = allocation_limitation;
        self
    }

    /// Port of `CConcurrentTaskCalculationEnvironment::getSatisfiableCalculationTaskJobCallbackExecuter`.
    pub fn get_satisfiable_calculation_task_job_callback_executer(&self) -> Cint64 {
        self.callback_executer
    }

    /// Port of `CConcurrentTaskCalculationEnvironment::getSatisfiableCalculationTaskStatusPropagator`.
    pub fn get_satisfiable_calculation_task_status_propagator(&self) -> Cint64 {
        self.status_propagator
    }

    /// Port of `CConcurrentTaskCalculationEnvironment::getSingleTaskProcessorUnit`.
    pub fn get_single_task_processor_unit(&self) -> Cint64 {
        self.process_unit
    }

    /// Port of `CConcurrentTaskCalculationEnvironment::getSchedulerTaskProcessorUnit`.
    pub fn get_scheduler_task_processor_unit(&self) -> Cint64 {
        self.scheduler_unit
    }

    /// Port of `CConcurrentTaskCalculationEnvironment::getCompletorTaskProcessorUnit`.
    pub fn get_completor_task_processor_unit(&self) -> Cint64 {
        self.completor_unit
    }

    /// Port of `CConcurrentTaskCalculationEnvironment::getTaskProcessorUnitList`.
    pub fn get_task_processor_unit_list(&self) -> Vec<Cint64> {
        self.processor_unit_list.clone()
    }

    /// Port of `CConcurrentTaskCalculationEnvironment::getAllocationLimitation`.
    pub fn get_allocation_limitation(&self) -> Cint64 {
        self.allocation_limitation
    }

    /// Port of `CConcurrentTaskCalculationEnvironment::getCalculationComputionTime`.
    /// KONCLUDE-PORT-NOTE[threading]: the per-unit `getStatisticComputionTime()`
    /// reads cross into the opaque `Scheduler/` thread handles; deferred (contributes 0).
    pub fn get_calculation_compution_time(&self) -> Cint64 {
        let mut comp_time: Cint64 = 0;
        if self.process_unit != INVALID {
            // W6-DEFER[threading]: mProcessUnit->getStatisticComputionTime()
            comp_time += 0;
        }
        for &thread_unit in self.thread_unit_list.iter() {
            // W6-DEFER[threading]: threadUnit->getStatisticComputionTime()
            let _ = thread_unit;
            comp_time += 0;
        }
        comp_time
    }

    /// Port of `CConcurrentTaskCalculationEnvironment::getCalculationBlockingTime`.
    pub fn get_calculation_blocking_time(&self) -> Cint64 {
        let mut comp_time: Cint64 = 0;
        if self.process_unit != INVALID {
            // W6-DEFER[threading]: mProcessUnit->getStatisticBlockingTime()
            comp_time += 0;
        }
        for &thread_unit in self.thread_unit_list.iter() {
            // W6-DEFER[threading]: threadUnit->getStatisticBlockingTime()
            let _ = thread_unit;
            comp_time += 0;
        }
        comp_time
    }

    /// Port of `CConcurrentTaskCalculationEnvironment::getCalculationMemoryConsumption`.
    /// KONCLUDE-PORT-NOTE[memory-pool]: `mAllocationLimitation->getAllocatedMemorySizeMaximum()`
    /// reads the opaque shared limiter; deferred.
    pub fn get_calculation_memory_consumption(&self) -> Cint64 {
        // W6-DEFER[memory-pool]: mAllocationLimitation->getAllocatedMemorySizeMaximum()
        let _ = self.allocation_limitation;
        0
    }

    /// Port of `CConcurrentTaskCalculationEnvironment::getCalculationMemoryReserved`.
    pub fn get_calculation_memory_reserved(&self) -> Cint64 {
        // W6-DEFER[memory-pool]: mAllocationLimitation->getReservedMemorySizeMaximum()
        let _ = self.allocation_limitation;
        0
    }

    /// Port of `CConcurrentTaskCalculationEnvironment::getCalculationStatisticTasksProcessedCount`.
    /// KONCLUDE-PORT-NOTE[threading]: every per-unit `getTaskProcessingStatistics()->...`
    /// crosses into opaque thread handles; deferred (contributes 0).
    pub fn get_calculation_statistic_tasks_processed_count(&self) -> Cint64 {
        self.accumulate_task_statistic()
    }

    /// Port of `CConcurrentTaskCalculationEnvironment::getCalculationStatisticTasksAddedCount`.
    pub fn get_calculation_statistic_tasks_added_count(&self) -> Cint64 {
        self.accumulate_task_statistic()
    }

    /// Port of `CConcurrentTaskCalculationEnvironment::getCalculationStatisticTasksCreatedCount`.
    pub fn get_calculation_statistic_tasks_created_count(&self) -> Cint64 {
        self.accumulate_task_statistic()
    }

    /// Port of `CConcurrentTaskCalculationEnvironment::getCalculationStatisticTasksCompletedCount`.
    pub fn get_calculation_statistic_tasks_completed_count(&self) -> Cint64 {
        self.accumulate_task_statistic()
    }

    /// Port of `CConcurrentTaskCalculationEnvironment::getCalculationStatisticTasksUpdatedCount`.
    pub fn get_calculation_statistic_tasks_updated_count(&self) -> Cint64 {
        self.accumulate_task_statistic()
    }

    /// Port of `CConcurrentTaskCalculationEnvironment::getCalculationStatisticEventsProcessedCount`.
    pub fn get_calculation_statistic_events_processed_count(&self) -> Cint64 {
        self.accumulate_task_statistic()
    }

    /// Port of `CConcurrentTaskCalculationEnvironment::getCalculationStatisticTasksRequestedCount`.
    pub fn get_calculation_statistic_tasks_requested_count(&self) -> Cint64 {
        self.accumulate_task_statistic()
    }

    /// Port of `CConcurrentTaskCalculationEnvironment::getCalculationStatisticThreadsBlockedCount`.
    pub fn get_calculation_statistic_threads_blocked_count(&self) -> Cint64 {
        self.accumulate_task_statistic()
    }

    /// Shared `mProcessUnit + foreach(mThreadUnitList)` accumulation skeleton used by
    /// the eight `getCalculationStatistic*Count` getters above. Each C++ getter sums
    /// a distinct `getTaskProcessingStatistics()->getStatistic*Count()` field; all are
    /// deferred (opaque thread handles), so every variant contributes 0 identically.
    /// KONCLUDE-PORT-NOTE[threading]: collapses eight identical iteration skeletons.
    fn accumulate_task_statistic(&self) -> Cint64 {
        let mut stat_val: Cint64 = 0;
        if self.process_unit != INVALID {
            // W6-DEFER[threading]: mProcessUnit->getTaskProcessingStatistics()->getStatistic*Count()
            stat_val += 0;
        }
        for &thread_unit in self.thread_unit_list.iter() {
            // W6-DEFER[threading]: threadUnit->getTaskProcessingStatistics()->getStatistic*Count()
            let _ = thread_unit;
            stat_val += 0;
        }
        stat_val
    }

    /// Port of `CConcurrentTaskCalculationEnvironment::getCalculationApproximatedRemainingTasksCount`.
    ///
    /// Recomputes the per-depth task-creation/processing rates and projects the
    /// remaining-task estimate. The local per-depth vectors are owned; the per-unit
    /// created/processed depth vectors are read from the opaque thread statistics.
    /// KONCLUDE-PORT-NOTE[uninit]: the C++ ctor pre-sizes the four vectors to
    /// `VECCOUNTERSIZE`; the port's ctor leaves them empty ([uninit] note there), so
    /// this method first ensures the size, equivalent to the C++ ctor + the leading
    /// reset loop.
    /// KONCLUDE-PORT-NOTE[threading]: the `getStatisticTasksCreated/ProcessedDepthCountVector()`
    /// reads cross into opaque thread handles; deferred (createdVec/processedVec add 0).
    pub fn get_calculation_approximated_remaining_tasks_count(&mut self) -> f64 {
        let mut remaining_tasks_count: f64 = 0.0;

        self.task_created_depth_count_vec.resize(VECCOUNTERSIZE, 0);
        self.task_processed_depth_count_vec
            .resize(VECCOUNTERSIZE, 0);
        self.task_relative_increase_task_per_depth_vec
            .resize(VECCOUNTERSIZE, 0.0);
        self.task_total_increase_task_per_depth_vec
            .resize(VECCOUNTERSIZE, 1.0);
        for i in 0..VECCOUNTERSIZE {
            self.task_created_depth_count_vec[i] = 0;
            self.task_processed_depth_count_vec[i] = 0;
            self.task_relative_increase_task_per_depth_vec[i] = 0.0;
            self.task_total_increase_task_per_depth_vec[i] = 1.0;
        }

        if self.process_unit != INVALID {
            // W6-DEFER[threading]: mProcessUnit->getTaskProcessingStatistics()
            //   ->getStatisticTasksCreated/ProcessedDepthCountVector(); both add 0.
        }
        for &thread_unit in self.thread_unit_list.iter() {
            // W6-DEFER[threading]: threadUnit->getTaskProcessingStatistics()
            //   ->getStatisticTasksCreated/ProcessedDepthCountVector(); both add 0.
            let _ = thread_unit;
        }

        for i in 0..VECCOUNTERSIZE - 1 {
            let mut processed_task_count = self.task_processed_depth_count_vec[i];
            let next_depth_created_count = self.task_created_depth_count_vec[i + 1];
            let mut rel_inc_task_rate: f64 = 0.0;
            if next_depth_created_count != 0 {
                if processed_task_count < 1 {
                    processed_task_count = 1;
                    self.task_processed_depth_count_vec[i] = processed_task_count;
                }
                rel_inc_task_rate = next_depth_created_count as f64 / processed_task_count as f64;
            }
            self.task_relative_increase_task_per_depth_vec[i] = rel_inc_task_rate;
        }

        for i in (0..VECCOUNTERSIZE).rev() {
            let rel_inc_value = self.task_relative_increase_task_per_depth_vec[i];
            if rel_inc_value > 0.0 {
                let next_tot_inc_value = self.task_total_increase_task_per_depth_vec[i + 1];
                if next_tot_inc_value > 0.0 {
                    self.task_total_increase_task_per_depth_vec[i] =
                        1.0 + next_tot_inc_value * rel_inc_value;
                } else {
                    self.task_total_increase_task_per_depth_vec[i] = rel_inc_value;
                }
            }
        }

        for i in 0..VECCOUNTERSIZE - 1 {
            let open_task_count =
                self.task_created_depth_count_vec[i] - self.task_processed_depth_count_vec[i];
            if open_task_count > 0 {
                remaining_tasks_count +=
                    open_task_count as f64 * self.task_total_increase_task_per_depth_vec[i];
            }
        }

        // KONCLUDE-PORT-NOTE[api]: the trailing per-depth QString debug list is
        // debug-only and its result is discarded in the C++; dropped here.

        remaining_tasks_count
    }
}

impl Default for ConcurrentTaskCalculationEnvironment {
    fn default() -> Self {
        Self::new()
    }
}
