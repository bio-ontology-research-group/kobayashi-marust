//! `calculation::builder` — the task-handle-algorithm injection seam.
//!
//! Ports Konclude `Source/Reasoner/Kernel/Calculation/CTaskHandleAlgorithmBuilder.h`
//! (`CTaskHandleAlgorithmBuilder`, abstract). Struct-definition unit only (wave W4):
//! the `createTaskHandleAlgorithm` factory method is deferred to the
//! `// W4-CALC method-batch` below.
//!
//! KONCLUDE-PORT-NOTE[ownership]: this abstract base is the SEAM that selects which
//! reasoning core the per-thread processor units run: a concrete subclass'
//! `createTaskHandleAlgorithm()` yields EITHER a
//! `completion::algorithm::CompletionTaskHandleAlgorithm` (the full backtracking
//! tableau completion) OR a `saturation::algorithm::SaturationTaskHandleAlgorithm`
//! (the approximate-saturation pre-pass). The two concrete builders live OUTSIDE
//! `Calculation/` (in the algorithm subtree); here the product is the
//! `Scheduler/`-layer base `CTaskHandleAlgorithm*` (cross-subtree → opaque). So the
//! calculation controllers never hold the two algorithms by value/Id — they hold
//! THIS builder and let each worker thread build + own its private instance (see
//! `CConfigDependedCalculationEnvironmentFactory::createCalculationContext`).

#![allow(dead_code)]

use super::super::completion::algorithm::CompletionTaskHandleAlgorithm;
use super::super::saturation::algorithm::SaturationTaskHandleAlgorithm;
use super::super::model::substrate::{Cint64, INVALID};

/// Port of `CTaskHandleAlgorithmBuilder`.
///
/// Abstract base — no member variables in the C++ `.h`. Concrete subclasses
/// override `createTaskHandleAlgorithm()` to produce the completion or saturation
/// `CTaskHandleAlgorithm`.
#[derive(Default)]
pub struct TaskHandleAlgorithmBuilder {
    // No member variables (abstract base).
}

impl TaskHandleAlgorithmBuilder {
    /// Port of `CTaskHandleAlgorithmBuilder::CTaskHandleAlgorithmBuilder`.
    pub fn new() -> Self {
        TaskHandleAlgorithmBuilder {}
    }

    /// Port of `CTaskHandleAlgorithmBuilder::createTaskHandleAlgorithm` (the
    /// completion-vs-saturation selection seam).
    ///
    /// In C++ this is pure virtual (`= 0`). The ONLY concrete override in the whole
    /// codebase is `CReasonerManagerThread::createTaskHandleAlgorithm`
    /// (`Reasoner/Kernel/Manager/`, wave W6). That override builds BOTH reasoning
    /// cores and hands them to the runtime chooser:
    ///
    /// ```text
    /// approxSat = new CCalculationTableauApproximationSaturationTaskHandleAlgorithm(
    ///                 backendAssCacheHandler, satTaskOccStatCollector);
    /// comp      = new CCalculationTableauCompletionTaskHandleAlgorithm(
    ///                 unsat, satExp, reuse, satNode, compCons, backend, occStats);
    /// return new CCalculationChooseTaskHandleAlgorithm(comp, approxSat);
    /// ```
    ///
    /// The choice of completion vs saturation is therefore NOT made here at build
    /// time: both cores are constructed, and the `CCalculationChooseTaskHandleAlgorithm`
    /// wrapper picks between them per task at `handleTask` time (saturation pre-pass
    /// first, complete tableau on the flagged-critical residue).
    ///
    /// The selection is ported faithfully below: both cores are constructed (they
    /// live in scope, `completion::algorithm` + `saturation::algorithm`). Their
    /// cache-handler constructor arguments come from the Manager's caches (W6) and
    /// are deferred (`Id::NONE` inside each `new`). The `CCalculationChooseTaskHandleAlgorithm`
    /// wrapper itself lives in the `Algorithm/` subtree (cross-subtree, not yet
    /// ported), so the returned product `CTaskHandleAlgorithm*` is opaque.
    pub fn create_task_handle_algorithm(&self) -> Cint64 {
        let _approx_sat = SaturationTaskHandleAlgorithm::new();
        let _completion = CompletionTaskHandleAlgorithm::new();
        // W6-DEFER[api]: CCalculationChooseTaskHandleAlgorithm(comp, approxSat) is a
        // cross-subtree Algorithm/ product (Scheduler/ base CTaskHandleAlgorithm*);
        // opaque handle, ownership handed to the per-thread processor unit.
        INVALID
    }
}
