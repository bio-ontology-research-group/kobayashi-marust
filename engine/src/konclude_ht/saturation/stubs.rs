//! `saturation::stubs` — the shared home for not-yet-ported **saturation-layer**
//! placeholder marker types referenced by `saturation/algorithm.rs`.
//!
//! KONCLUDE-PORT-NOTE[api]: the approximate-saturation task-handle algorithm holds
//! a handful of saturation-specific helper classes that are scheduled for later
//! waves (the two satisfiable-task saturation message analysers, the occurrence
//! statistics collector, and the backend-association cache handler that hands the
//! saturated node labels off to the consistency/classification phase). Each is
//! declared here ONCE as a zero-size marker; a by-value member (the analysers)
//! holds the marker struct directly, while a pointer field becomes an
//! `Id<Marker>` into its eventual per-thread arena (`Id::NONE` == the C++
//! `nullptr`). When a class is really ported it relocates to its own module and
//! these stubs reconcile to it.
//!
//! This is the saturation-layer twin of `completion::stubs` (Algorithm-layer
//! strategies/handlers/analysers) and `process::stubs` (Process-layer queue/hash/
//! linker markers). Saturation reuses those where the referenced class already has
//! a marker there (`CCalculationConfigurationExtension`,
//! `CSatisfiableCalculationTask` from `completion::stubs`; `CIndividualProcessNodeVector`
//! from `process::stubs`); only the genuinely saturation-specific classes below
//! live here.

#![allow(dead_code)]

/// Declare zero-size marker structs (used inline as `Id<Marker>` for pointer
/// fields, or held by value for the by-value analyser members).
macro_rules! stub {
    ($($(#[$m:meta])* $name:ident),* $(,)?) => {
        $( $(#[$m])* #[derive(Debug, Default, Clone)] pub struct $name; )*
    };
}

// ===========================================================================
// Satisfiable-task saturation message analysers (`Reasoner/Kernel/Algorithm/`).
// KONCLUDE-PORT-NOTE[api]: these are held BY VALUE in the C++ algorithm (not
// pointers); the port holds the zero-size marker by value until they are ported.
// ===========================================================================
stub! {
    /// Port of `CSatisfiableTaskSaturationPreyingAnalyser`.
    SatisfiableTaskSaturationPreyingAnalyser,
    /// Port of `CSatisfiableTaskSaturationIndividualsAnalyser`.
    SatisfiableTaskSaturationIndividualsAnalyser,
}

// ===========================================================================
// Saturation collectors / cache handlers (`Reasoner/Kernel/Algorithm/`).
// KONCLUDE-PORT-NOTE[api]: pointer members in the C++ algorithm (ctor-injected);
// the port holds them as `Id<Marker>` (`Id::NONE` == `nullptr`).
// ===========================================================================
stub! {
    /// Port of `CSatisfiableTaskSaturationOccurrenceStatisticsCollector`.
    SatisfiableTaskSaturationOccurrenceStatisticsCollector,
    /// Port of `CSaturationNodeBackendAssociationCacheHandler`.
    SaturationNodeBackendAssociationCacheHandler,
}
