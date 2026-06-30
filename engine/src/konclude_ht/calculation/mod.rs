//! `calculation` — the Calculation/ entry controllers (Konclude
//! `Source/Reasoner/Kernel/Calculation/`): the manager / environment / factory /
//! builder classes that drive the two `CTaskHandleAlgorithm`s — the full tableau
//! completion (`completion::algorithm::CompletionTaskHandleAlgorithm`) and the
//! approximate-saturation pre-pass (`saturation::algorithm::SaturationTaskHandleAlgorithm`).
//!
//! Control flow (cpp): `ConfigDependedCalculationFactory::createCalculationManager`
//! → `ConcurrentTaskCalculationManager`; `initializeManager` hands it a
//! `ConfigDependedCalculationEnvironmentFactory` (carrying a
//! `TaskHandleAlgorithmBuilder`); `createCalculationContext` builds the
//! `ConcurrentTaskCalculationEnvironment` thread pool, each worker thread getting
//! its OWN freshly built task-handle algorithm + per-thread memory pool. Per job,
//! `calculateTask` posts a satisfiability task to the scheduler thread.
//!
//! Struct-definition wave (W4) only — every method body is deferred behind a
//! `// W4-CALC method-batch` marker. NOT yet wired into `konclude_ht/mod.rs`.

#![allow(dead_code)]

use super::model::substrate::Id;

pub mod builder;      // CTaskHandleAlgorithmBuilder (the completion/saturation seam)
pub mod environment;  // CCalculationEnviroment + CConcurrentTaskCalculationEnvironment
pub mod env_factory;  // CCalculationEnvironmentFactory + CConfigDependedCalculationEnvironmentFactory
pub mod factory;      // CCalculationFactory + CConfigDependedCalculationFactory
pub mod manager;      // CCalculationManager + CConcurrentTaskCalculationManager (the ENTRY point)

// --- calculation-layer ids ---
/// `CTaskHandleAlgorithmBuilder*` → `TaskHandleAlgorithmBuilderId`.
/// KONCLUDE-PORT-NOTE[ownership]: a non-owning, ctor-injected handle (the builder
/// is owned by the caller that wires the calculation factory).
pub type TaskHandleAlgorithmBuilderId = Id<builder::TaskHandleAlgorithmBuilder>;
