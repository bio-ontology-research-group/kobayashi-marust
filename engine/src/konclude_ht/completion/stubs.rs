//! `completion::stubs` — the shared home for not-yet-ported **Algorithm-layer**
//! placeholder marker types referenced by `context.rs` + `algorithm.rs`.
//!
//! KONCLUDE-PORT-NOTE[api]: the completion engine's per-thread context and the
//! task-handle algorithm point at a large family of Algorithm/Strategy/Cache
//! helper classes that are scheduled for later waves (the priority strategies,
//! the dependency/clash factories, the ~14 cache handlers, the 8 satisfiable-task
//! message analysers, the configuration extension). Each is declared here ONCE as
//! a zero-size marker; a pointer field becomes an `Id<Marker>` into its eventual
//! per-thread arena (`Id::NONE` == the C++ `nullptr`), and a by-value member (the
//! analysers) holds the marker struct directly. When a class is really ported it
//! relocates to its own module and these stubs reconcile to it.
//!
//! This is the Algorithm-layer twin of `process::stubs` (the Process-layer queue/
//! hash/linker markers); the two never collide — completion fields that point at
//! a Process-layer container reuse the `process::stubs` markers, while the
//! Algorithm-layer strategies/handlers/factories/analysers live here.

#![allow(dead_code)]

/// Declare zero-size marker structs (used inline as `Id<Marker>` for pointer
/// fields, or held by value for the by-value analyser members).
macro_rules! stub {
    ($($(#[$m:meta])* $name:ident),* $(,)?) => {
        $( $(#[$m])* #[derive(Debug, Default, Clone)] pub struct $name; )*
    };
}

// ===========================================================================
// Priority strategies (`Reasoner/Kernel/Strategy/`).
// ===========================================================================
stub! {
    /// Port of `CConceptProcessingPriorityStrategy`.
    ConceptProcessingPriorityStrategy,
    /// Port of `CIndividualProcessingPriorityStrategy`.
    IndividualProcessingPriorityStrategy,
    /// Port of `CTaskProcessingPriorityStrategy`.
    TaskProcessingPriorityStrategy,
    /// Port of `CUnsatisfiableCacheRetrievalStrategy`.
    UnsatisfiableCacheRetrievalStrategy,
    /// Port of `CIndividualAncestorDepthMaximumConceptProcessingPriorityStrategy`.
    IndividualAncestorDepthMaximumConceptProcessingPriorityStrategy,
}

// ===========================================================================
// Factories / managers (`Reasoner/Kernel/Algorithm/`).
// ===========================================================================
stub! {
    /// Port of `CClashDescriptorFactory`.
    ClashDescriptorFactory,
    /// Port of `CDependencyFactory`.
    DependencyFactory,
    /// Port of `CIndividualNodeManager`.
    IndividualNodeManager,
}

// ===========================================================================
// Cache / expansion handlers (`Reasoner/Kernel/Algorithm/` + `Cache/`).
// ===========================================================================
stub! {
    /// Port of `CUnsatisfiableCacheHandler`.
    UnsatisfiableCacheHandler,
    /// Port of `CSatisfiableExpanderCacheHandler`.
    SatisfiableExpanderCacheHandler,
    /// Port of `CCompletionGraphCacheHandler`.
    CompletionGraphCacheHandler,
    /// Port of `CReuseCompletionGraphCacheHandler`.
    ReuseCompletionGraphCacheHandler,
    /// Port of `CConceptNominalSchemaGroundingHandler`.
    ConceptNominalSchemaGroundingHandler,
    /// Port of `CSaturationNodeExpansionCacheHandler`.
    SaturationNodeExpansionCacheHandler,
    /// Port of `CDatatypeIndividualProcessNodeHandler`.
    DatatypeIndividualProcessNodeHandler,
    /// Port of `CComputedConsequencesCacheHandler`.
    ComputedConsequencesCacheHandler,
    /// Port of `CIndividualNodeBackendCacheHandler`.
    IndividualNodeBackendCacheHandler,
    /// Port of `CIncrementalCompletionGraphCompatibleExpansionHandler`.
    IncrementalCompletionGraphCompatibleExpansionHandler,
    /// Port of `COccurrenceStatisticsCacheHandler`.
    OccurrenceStatisticsCacheHandler,
}

// ===========================================================================
// Context-layer back-references (`Process/` + `Scheduler/` + `Task/`).
// ===========================================================================
stub! {
    /// Port of `CProcessTagger`.
    ProcessTagger,
    /// Port of `CProcessingStatisticGathering`.
    ProcessingStatisticGathering,
}

// `CSatisfiableCalculationTask` is now fully ported in the `task` subtree (W6); the
// completion layer's placeholder marker is replaced by a re-export so every
// `Id<SatisfiableCalculationTask>` in completion points at the real task (carrying
// the 16 adapter handles, incl. the incremental-consistency adapter). Re-aliasing a
// stub onto the real struct is the established reconcile pattern (W2.7 / W3b).
pub use super::super::task::satisfiable_task::SatisfiableCalculationTask;

// ===========================================================================
// Configuration extension (`Task/CCalculationConfigurationExtension`).
// ===========================================================================
stub! {
    /// Port of `CCalculationConfigurationExtension`.
    CalculationConfigurationExtension,
}

// ===========================================================================
// Satisfiable-task message analysers (`Reasoner/Kernel/Algorithm/`).
// KONCLUDE-PORT-NOTE[api]: these are held BY VALUE in the C++ algorithm (not
// pointers); the port holds the zero-size marker by value until they are ported.
// ===========================================================================
stub! {
    /// Port of `CSatisfiableTaskConsistencyPreyingAnalyser`.
    SatisfiableTaskConsistencyPreyingAnalyser,
    /// Port of `CSatisfiableTaskIncrementalConsistencyPreyingAnalyser`.
    SatisfiableTaskIncrementalConsistencyPreyingAnalyser,
    /// Port of `CSatisfiableTaskClassificationMessageAnalyser`.
    SatisfiableTaskClassificationMessageAnalyser,
    /// Port of `CSatisfiableTaskMarkerIndividualPropagationAnalyser`.
    SatisfiableTaskMarkerIndividualPropagationAnalyser,
    /// Port of `CSatisfiableTaskPossibleAssertionCollectingAnalyser`.
    SatisfiableTaskPossibleAssertionCollectingAnalyser,
    /// Port of `CSatisfiableTaskPropertyClassificationMessageAnalyser`.
    SatisfiableTaskPropertyClassificationMessageAnalyser,
    /// Port of `CSatisfiableTaskComplexAnsweringMessageAnalyser`.
    SatisfiableTaskComplexAnsweringMessageAnalyser,
    /// Port of `CSatisfiableTaskPropagationBindingAnsweringMessageAnalyser`.
    SatisfiableTaskPropagationBindingAnsweringMessageAnalyser,
}
