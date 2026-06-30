//! `task::adapters` — the satisfiable-task observer/message adapter bag.
//!
//! Ports the 16 observer/answer adapters the algorithm pulls off
//! `CSatisfiableCalculationTask` as call-out seams (Konclude
//! `Source/Reasoner/Kernel/Task/CSatisfiableTask*Adapter.h` + `CTaskPreying*.h`
//! + `CSaturation*Adapter.h`), plus the preying-listener interface and the
//! answerer querying-propagation base in the same subtree.
//!
//! KONCLUDE-PORT-NOTE[api]: these are independent holder structs co-owned by the
//! task (18 distinct `m*Adapter` pointer fields), each a different observer
//! interface set/got independently and serving a different phase. They are NOT a
//! polymorphic family, so they stay separate structs (NOT one enum). For this
//! struct wave each is a ZERO-SIZE marker — a task field becomes an `Id<Marker>`
//! (`Id::NONE` == the C++ `nullptr`). Real bodies (ctor + getters + the few flag
//! / counter members, notably `CSatisfiableTaskRepresentativeBackendUpdatingAdapter`
//! with its unsat-computed / expansion-limit / propagation-cut state) are
//! deferred to the realization/answering wave — exactly as `completion::stubs`
//! defers the 8 message analysers.

#![allow(dead_code)]

/// Declare zero-size adapter marker structs.
macro_rules! adapter {
    ($($(#[$m:meta])* $name:ident),* $(,)?) => {
        $( $(#[$m])* #[derive(Debug, Default, Clone)] pub struct $name; )*
    };
}

adapter! {
    /// Port of `CTaskPreyingAdapter` (consistency/saturation observer bridge; the
    /// task's `mConsAdapter`).
    TaskPreyingAdapter,
    /// Port of `CTaskPreyingListner` (notified when a preyed task's data is ready).
    TaskPreyingListner,
    /// Port of `CSaturationIndividualsAnalysingAdapter` (`mIndiAnalAdapter`).
    SaturationIndividualsAnalysingAdapter,
    /// Port of `CSatisfiableTaskClassificationMessageAdapter` (`mClassMessAdapter`).
    SatisfiableTaskClassificationMessageAdapter,
    /// Port of `CSatisfiableTaskRealizationMarkedCandidatesMessageAdapter`
    /// (`mRealMessAdapter`).
    SatisfiableTaskRealizationMarkedCandidatesMessageAdapter,
    /// Port of `CSatisfiableTaskIndividualDependenceTrackingAdapter`
    /// (`mSatIndDepTrackAdapter`).
    SatisfiableTaskIndividualDependenceTrackingAdapter,
    /// Port of `CSatisfiableTaskRealizationPossibleAssertionCollectingAdapter`
    /// (`mPossAssCollAdapter`).
    SatisfiableTaskRealizationPossibleAssertionCollectingAdapter,
    /// Port of `CSatisfiableTaskClassificationRoleMarkedMessageAdapter`
    /// (`mClassRoleMarkedMessageAdapter`).
    SatisfiableTaskClassificationRoleMarkedMessageAdapter,
    /// Port of `CSatisfiableTaskAnswererSubsumptionMessageAdapter`
    /// (`mAnswererSubsumptionMessageAdapter`).
    SatisfiableTaskAnswererSubsumptionMessageAdapter,
    /// Port of `CSatisfiableTaskAnswererBindingPropagationAdapter`
    /// (`mAnswererBindingPropagationAdapter`).
    SatisfiableTaskAnswererBindingPropagationAdapter,
    /// Port of `CSatisfiableTaskRealizationPossibleInstancesMergingAdapter`
    /// (`mSatisfiablePossibleInstancesMergingAdapter`).
    SatisfiableTaskRealizationPossibleInstancesMergingAdapter,
    /// Port of `CSatisfiableTaskAnswererInstancePropagationMessageAdapter`
    /// (`mAnswererInstancePropagationMessageAdapter`).
    SatisfiableTaskAnswererInstancePropagationMessageAdapter,
    /// Port of `CSatisfiableTaskRepresentativeBackendUpdatingAdapter`
    /// (`mRepresentativeBackendUpdatingAdapter`; the most-used adapter — 12 algo
    /// call sites — and the only one with non-trivial state, deferred here).
    SatisfiableTaskRepresentativeBackendUpdatingAdapter,
    /// Port of `CSaturationOccurrenceStatisticsCollectingAdapter`
    /// (`mOccurrenceStatisticsCollectingAdapter`).
    SaturationOccurrenceStatisticsCollectingAdapter,
    /// Port of `CSatisfiableTaskAnswererQueryingMaterializationAdapter`
    /// (`mAnswererMaterializationAdapter`).
    SatisfiableTaskAnswererQueryingMaterializationAdapter,
    /// Port of `CSatisfiableTaskCancellationAdapter` (`mCancellationAdapter`).
    SatisfiableTaskCancellationAdapter,
    /// Port of `CSatisfiableTaskAnswererQueryingPropagationAdapter` (the base of
    /// the binding/instance propagation adapters; not held directly by the task).
    SatisfiableTaskAnswererQueryingPropagationAdapter,
}

use super::super::model::substrate::Cint64;

/// Port of `CSatisfiableTaskIncrementalConsistencyTestingAdapter`
/// (`Source/Reasoner/Kernel/Task/CSatisfiableTaskIncrementalConsistencyTestingAdapter.{h,cpp}`;
/// the task's `mSatIncConsTestingAdapter`).
///
/// The incremental-consistency seam: it carries the ontology being (re)tested, the
/// previous consistent ontology whose completion graph the run incrementally
/// updates, the consistence observer to notify, and the incremental revision id
/// that stamps the change set. `handleTask` (u01) keys the incremental-expansion
/// seeding on the mere PRESENCE of this adapter; the realization/answering waves
/// read the four handles.
///
/// KONCLUDE-PORT-NOTE[api]: `CConcreteOntology*` (testing + previous-consistent) and
/// `CConsistenceObserver*` are upstream ontology/observer objects outside the
/// kernel port; they stay opaque `Cint64` handles (`0` == the C++ `nullptr`
/// default). `mPrevConsOntology` is "the prev-completion-graph handle" the
/// incremental retest diffs against. Only `mIncrementalRevisionID` is concrete.
#[derive(Debug, Default, Clone)]
pub struct SatisfiableTaskIncrementalConsistencyTestingAdapter {
    /// `CConcreteOntology* mOntology` — the ontology being tested. [api] opaque.
    pub ontology: Cint64,
    /// `CConcreteOntology* mPrevConsOntology` — the previous consistent ontology
    /// (its completion graph is incrementally re-used). [api] opaque.
    pub prev_cons_ontology: Cint64,
    /// `CConsistenceObserver* mConsObserver`. [api] opaque.
    pub cons_observer: Cint64,
    /// `cint64 mIncrementalRevisionID`.
    pub incremental_revision_id: Cint64,
}

impl SatisfiableTaskIncrementalConsistencyTestingAdapter {
    /// Port of the ctor
    /// `CSatisfiableTaskIncrementalConsistencyTestingAdapter(testingOntology,
    /// prevConsOntology, incRevID, observer)`.
    pub fn new(
        testing_ontology: Cint64,
        prev_cons_ontology: Cint64,
        inc_rev_id: Cint64,
        observer: Cint64,
    ) -> Self {
        SatisfiableTaskIncrementalConsistencyTestingAdapter {
            ontology: testing_ontology,
            prev_cons_ontology,
            cons_observer: observer,
            incremental_revision_id: inc_rev_id,
        }
    }

    /// Port of `getTestingOntology`.
    pub fn get_testing_ontology(&self) -> Cint64 { self.ontology }
    /// Port of `getPreviousConsistentOntology`.
    pub fn get_previous_consistent_ontology(&self) -> Cint64 { self.prev_cons_ontology }
    /// Port of `getConsistenceObserver`.
    pub fn get_consistence_observer(&self) -> Cint64 { self.cons_observer }
    /// Port of `getIncrementalRevisionID`.
    pub fn get_incremental_revision_id(&self) -> Cint64 { self.incremental_revision_id }
}
