//! `calculation::env_factory` — the environment factory controllers.
//!
//! Ports Konclude:
//!   * `Source/Reasoner/Kernel/Calculation/CCalculationEnvironmentFactory.h`
//!     (`CCalculationEnvironmentFactory`, abstract — no members), and
//!   * `Source/Reasoner/Kernel/Calculation/CConfigDependedCalculationEnvironmentFactory.h`
//!     (`CConfigDependedCalculationEnvironmentFactory`, the concrete factory that
//!     reads ProcessorCount/Memory config and wires the per-thread thread pool).
//!
//! Struct-definition unit only (wave W4): `createCalculationContext` (the cpp 42–148
//! threading-model wiring) is deferred to the `// W4-CALC method-batch` below.

#![allow(dead_code)]

use super::super::model::substrate::{Cint64, Id, INVALID};
use super::builder::TaskHandleAlgorithmBuilder;
use super::environment::ConcurrentTaskCalculationEnvironment;

/// Port of `CCalculationEnvironmentFactory`.
///
/// Abstract base — no member variables in the C++ `.h`. The concrete
/// `ConfigDependedCalculationEnvironmentFactory` folds it in as `base`.
#[derive(Default)]
pub struct CalculationEnvironmentFactory {
    // No member variables (abstract base).
}

impl CalculationEnvironmentFactory {
    /// Port of `CCalculationEnvironmentFactory::CCalculationEnvironmentFactory`.
    pub fn new() -> Self {
        CalculationEnvironmentFactory {}
    }
}

/// Port of `CConfigDependedCalculationEnvironmentFactory`.
///
/// The concrete environment factory: `createCalculationContext` reads
/// `Konclude.Calculation.ProcessorCount` / `.Memory`, builds the worker thread
/// pool, and installs a fresh `CTaskHandleAlgorithm` (via `mTaskHandleAlgBuilder`)
/// + a fresh per-thread memory pool on each unit.
///
/// W4-CALC method-batch (filled): `create_calculation_context`.
pub struct ConfigDependedCalculationEnvironmentFactory {
    /// The folded-in `CCalculationEnvironmentFactory` base (no members; kept for
    /// method-by-method diffability with the C++ inheritance).
    pub base: CalculationEnvironmentFactory,

    /// `CTaskHandleAlgorithmBuilder* mTaskHandleAlgBuilder` (.h 85).
    /// KONCLUDE-PORT-NOTE[ownership]: ctor-INJECTED, externally owned — this
    /// factory does not own the builder, it only invokes
    /// `createTaskHandleAlgorithm()` on it per worker thread. Modelled as a
    /// non-owning handle `Id<TaskHandleAlgorithmBuilder>` (`Id::NONE` == `nullptr`).
    pub task_handle_alg_builder: Id<TaskHandleAlgorithmBuilder>,
}

impl ConfigDependedCalculationEnvironmentFactory {
    /// Port of
    /// `CConfigDependedCalculationEnvironmentFactory::CConfigDependedCalculationEnvironmentFactory`
    /// (`CTaskHandleAlgorithmBuilder* taskHandleAlgBuilder`).
    pub fn new(task_handle_alg_builder: Id<TaskHandleAlgorithmBuilder>) -> Self {
        ConfigDependedCalculationEnvironmentFactory {
            base: CalculationEnvironmentFactory::new(),
            task_handle_alg_builder,
        }
    }

    /// Port of `CConfigDependedCalculationEnvironmentFactory::createCalculationContext`.
    ///
    /// Reads `Konclude.Calculation.ProcessorCount` / `.Memory`, builds the worker
    /// thread pool, and installs a freshly built `CTaskHandleAlgorithm` (via the
    /// injected builder) + a fresh per-thread memory pool on each processor unit.
    ///
    /// KONCLUDE-PORT-NOTE[api]: the C++ returns a `CCalculationEnviroment*` base
    /// pointer that the manager `dynamic_cast`s to the concrete env. Since the only
    /// modelled manager string is `ConcurrentTaskCalculationManager` (the C++ folds
    /// every branch to `taskCalcManager = true`), the port returns the concrete
    /// `ConcurrentTaskCalculationEnvironment` BY VALUE; the manager holds it directly.
    /// KONCLUDE-PORT-NOTE[threading]: the `Scheduler/` processor units (single /
    /// scheduler / completor / worker threads) own live OS threads → opaque `Cint64`.
    /// KONCLUDE-PORT-NOTE[memory-pool]: the centralized allocation limiter + per-thread
    /// `CNewCentralizedLimitedAllocationMemoryPoolProvider`s → opaque.
    /// KONCLUDE-PORT-NOTE[api]: `Config/` reads (`CConfigDataReader`) → deferred; the
    /// single-thread-first precedent (PORT.md W3/W4) defaults `ProcessorCount` to 1.
    pub fn create_calculation_context(
        &mut self,
        config_provider: Cint64,
    ) -> ConcurrentTaskCalculationEnvironment {
        // W6-DEFER[api]: config = configProvider->getCurrentConfiguration()
        let _ = config_provider;

        // W6-DEFER[api]: readConfigString("Konclude.Execution.CalculationManager");
        // every C++ branch sets taskCalcManager = true.
        let task_calc_manager = true;

        let mut task_context = ConcurrentTaskCalculationEnvironment::new();
        if task_calc_manager {
            // W6-DEFER[api]: readConfigString("Konclude.Calculation.ProcessorCount");
            // "AUTO" → CThread::idealThreadCount(). [threading] single-thread-first
            // precedent: default to 1.
            let mut task_processor_count: i64 = 1;

            // W6-DEFER[memory-pool]: CCentralizedAllocationConfigProvidedDependendLimitation(
            //   configProvider, "Konclude.Calculation.Memory")
            let alloc_limitation: Cint64 = INVALID;
            task_context.set_allocation_limitation(alloc_limitation);

            // W6-DEFER[threading]: Task/ callback executer + status propagator.
            let callback_executer: Cint64 = INVALID;
            task_context.init_callback_executer(callback_executer);
            let task_status_propagator: Cint64 = INVALID;
            task_context.init_status_propagator(task_status_propagator);

            if task_processor_count <= 1 {
                // The builder seam: each processor unit gets a freshly built
                // TaskHandleAlgorithm (the completion+saturation chooser).
                // W6-DEFER[api]: mTaskHandleAlgBuilder is a non-owning Id with no
                // arena to resolve it here, so createTaskHandleAlgorithm() and its
                // opaque CTaskHandleAlgorithm* product are deferred.
                let _builder = self.task_handle_alg_builder;
                let task_handle_alg: Cint64 = INVALID;
                // W6-DEFER[memory-pool]: CNewCentralizedLimitedAllocationMemoryPoolProvider(
                //   allocLimitation->getLimitator())
                let mem_prov: Cint64 = INVALID;
                // W6-DEFER[threading]: CSingleThreadTaskProcessorUnit(taskHandleAlg, memProv)
                //   ->startProcessing()
                let single_process_unit: Cint64 = INVALID;
                let _ = (task_handle_alg, mem_prov);
                task_context.init_single_task_processor(single_process_unit);
                // W6-DEFER[threading]: singlePocessUnit->installCallbackExecuter(callbackExecuter)
                //   + installStatusPropagator(taskStatusPropagator)
                let _ = (callback_executer, task_status_propagator);
            } else {
                // Multi-thread path (faithful structure; not reached under the
                // single-thread-first default).
                // W6-DEFER[api]/[threading]: two builder-built TaskHandleAlgorithms +
                // their per-thread pools feed the completor + scheduler threads.
                let _completor_task_handle_alg: Cint64 = INVALID;
                let _scheduler_task_handle_alg: Cint64 = INVALID;
                let _comp_mem_prov: Cint64 = INVALID;
                let _sched_mem_prov: Cint64 = INVALID;
                // W6-DEFER[threading]: CTaskProcessorCompletorThread + CTaskProcessorSchedulerThread,
                //   installScheduler / installCallbackExecuter / installStatusPropagator,
                //   completorUnit->startProcessing(); schedulerUnit->startProcessing().
                let completor_unit: Cint64 = INVALID;
                let scheduler_unit: Cint64 = INVALID;
                task_context.init_multi_task_processor(scheduler_unit, completor_unit);

                // while (taskProcessorCount-- > 2): append the remaining workers,
                // each with its own builder-built algorithm + per-thread pool.
                while {
                    let cont = task_processor_count > 2;
                    task_processor_count -= 1;
                    cont
                } {
                    // W6-DEFER[api]: mTaskHandleAlgBuilder->createTaskHandleAlgorithm()
                    let _worker_task_handle_alg: Cint64 = INVALID;
                    // W6-DEFER[memory-pool]: per-thread limited allocation pool provider.
                    let _worker_mem_prov: Cint64 = INVALID;
                    // W6-DEFER[threading]: CTaskProcessorThread(taskHandleAlg, completorUnit, memProv)
                    //   ->installScheduler/installCallbackExecuter/installStatusPropagator->startProcessing()
                    let task_processor: Cint64 = INVALID;
                    task_context.append_multi_task_processor(task_processor);
                }
            }
        }
        task_context
    }
}
