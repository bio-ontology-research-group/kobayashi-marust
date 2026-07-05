//! `calculation::factory` — the calculation-manager factory controllers.
//!
//! Ports Konclude:
//!   * `Source/Reasoner/Kernel/Calculation/CCalculationFactory.h`
//!     (`CCalculationFactory`, abstract — no members), and
//!   * `Source/Reasoner/Kernel/Calculation/CConfigDependedCalculationFactory.h`
//!     (`CConfigDependedCalculationFactory`, the concrete factory that creates a
//!     `CConcurrentTaskCalculationManager` + env factory from config).
//!
//! Struct-definition unit only (wave W4): `createCalculationManager` /
//! `initializeManager` are deferred to the `// W4-CALC method-batch` below.

#![allow(dead_code)]

use super::super::model::substrate::{Cint64, Id};
use super::builder::TaskHandleAlgorithmBuilder;
use super::env_factory::ConfigDependedCalculationEnvironmentFactory;
use super::manager::ConcurrentTaskCalculationManager;

/// Port of `CCalculationFactory`.
///
/// Abstract base — no member variables in the C++ `.h`. The concrete
/// `ConfigDependedCalculationFactory` folds it in as `base`.
#[derive(Default)]
pub struct CalculationFactory {
    // No member variables (abstract base).
}

impl CalculationFactory {
    /// Port of `CCalculationFactory::CCalculationFactory`.
    pub fn new() -> Self {
        CalculationFactory {}
    }
}

/// Port of `CConfigDependedCalculationFactory`.
///
/// The concrete calculation factory: `createCalculationManager` builds a
/// `ConcurrentTaskCalculationManager` and `initializeManager` hands it a
/// `ConfigDependedCalculationEnvironmentFactory` constructed with the injected
/// task-handle-algorithm builder.
///
/// W4-CALC method-batch (filled): `create_calculation_manager`,
/// `initialize_manager`.
pub struct ConfigDependedCalculationFactory {
    /// The folded-in `CCalculationFactory` base (no members; kept for
    /// method-by-method diffability with the C++ inheritance).
    pub base: CalculationFactory,

    /// `CTaskHandleAlgorithmBuilder* mTaskHandleAlgBuilder` (.h 82).
    /// KONCLUDE-PORT-NOTE[ownership]: ctor-INJECTED, externally owned (the same
    /// builder is threaded into the env factory it creates). Non-owning handle
    /// `Id<TaskHandleAlgorithmBuilder>` (`Id::NONE` == `nullptr`).
    pub task_handle_alg_builder: Id<TaskHandleAlgorithmBuilder>,
}

impl ConfigDependedCalculationFactory {
    /// Port of
    /// `CConfigDependedCalculationFactory::CConfigDependedCalculationFactory`
    /// (`CTaskHandleAlgorithmBuilder* taskHandleAlgBuilder`).
    pub fn new(task_handle_alg_builder: Id<TaskHandleAlgorithmBuilder>) -> Self {
        ConfigDependedCalculationFactory {
            base: CalculationFactory::new(),
            task_handle_alg_builder,
        }
    }

    /// Port of `CConfigDependedCalculationFactory::createCalculationManager`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: the C++ returns a `CCalculationManager*` that is null
    /// unless `taskCalcManager`; every config branch sets `taskCalcManager = true`, so
    /// the port always returns the concrete `ConcurrentTaskCalculationManager` by value.
    /// The `CWatchDog*` ctor argument is not stored as a member (see manager.rs).
    pub fn create_calculation_manager(
        &self,
        configuration_provider: Cint64,
    ) -> ConcurrentTaskCalculationManager {
        // W6-DEFER[api]: config = configurationProvider->getCurrentConfiguration()
        let _ = configuration_provider;
        // W6-DEFER[api]: readConfigString("Konclude.Execution.CalculationManager");
        // every branch yields taskCalcManager = true.
        let task_calc_manager = true;
        let _ = task_calc_manager;
        // new CConcurrentTaskCalculationManager(watchDog)
        ConcurrentTaskCalculationManager::new()
    }

    /// Port of `CConfigDependedCalculationFactory::initializeManager`.
    ///
    /// Builds a `ConfigDependedCalculationEnvironmentFactory` carrying the injected
    /// task-handle-algorithm builder, then drives the manager's `initializeManager`.
    /// KONCLUDE-PORT-NOTE[ownership]: the C++ `new`s the env factory and lets the
    /// manager use it transiently; the port stack-allocates it and passes `&mut`.
    pub fn initialize_manager(
        &self,
        calculation_manager: &mut ConcurrentTaskCalculationManager,
        configuration_provider: Cint64,
    ) {
        let mut calc_context_factory =
            ConfigDependedCalculationEnvironmentFactory::new(self.task_handle_alg_builder);
        calculation_manager.initialize_manager(&mut calc_context_factory, configuration_provider);
    }
}
