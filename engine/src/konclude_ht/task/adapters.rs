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
//! struct wave most are ZERO-SIZE markers — a task field becomes an `Id<Marker>`
//! (`Id::NONE` == the C++ `nullptr`). Real bodies (ctor + getters + the few flag
//! / counter members) are added as call sites become live; the classification and
//! incremental-consistency adapters already carry their Konclude state.

#![allow(dead_code)]

use std::collections::HashMap;
use std::sync::Arc;

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
    /// Port of `CSatisfiableTaskRealizationMarkedCandidatesMessageAdapter`
    /// (`mRealMessAdapter`).
    SatisfiableTaskRealizationMarkedCandidatesMessageAdapter,
    /// Port of `CSatisfiableTaskRealizationPossibleAssertionCollectingAdapter`
    /// (`mPossAssCollAdapter`).
    SatisfiableTaskRealizationPossibleAssertionCollectingAdapter,
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

use super::super::model::substrate::{Cint64, Id, INVALID};
use super::super::model::{ConceptId, IndividualId, RoleId};
use super::super::process::referred_tracking::ReferredIndividualTrackingVectorId;
use super::task_data::TaskDataId;

/// Port of the `CSatisfiableTaskClassificationMessageAdapter` extraction flag
/// constants.
pub const EFEXTRACTSUBSUMERSROOTNODE: Cint64 = 1 << 0;
pub const EFEXTRACTSUBSUMERSOTHERNODES: Cint64 = 1 << 1;
pub const EFEXTRACTPOSSIBLESUBSUMERSROOTNODE: Cint64 = 1 << 2;
pub const EFEXTRACTPOSSIBLESUBSUMERSOTHERNODES: Cint64 = 1 << 3;
pub const EFEXTRACTIDENTIFIERPSEUDOMODEL: Cint64 = 1 << 4;
pub const EFEXTRACTOTHERNODESSINGLEDEPENDENCY: Cint64 = 1 << 5;
pub const EFEXTRACTOTHERNODESMULTIPLEDEPENDENCY: Cint64 = 1 << 6;
pub const EFEXTRACTALL: Cint64 = EFEXTRACTSUBSUMERSROOTNODE
    | EFEXTRACTSUBSUMERSOTHERNODES
    | EFEXTRACTPOSSIBLESUBSUMERSROOTNODE
    | EFEXTRACTPOSSIBLESUBSUMERSOTHERNODES
    | EFEXTRACTIDENTIFIERPSEUDOMODEL
    | EFEXTRACTOTHERNODESMULTIPLEDEPENDENCY;

/// Port of `CIndividualDependenceTrackingCollector`
/// (`Source/Reasoner/Consistiser/CIndividualDependenceTrackingCollector.{h,cpp}`).
///
/// The C++ class implements `CIndividualDependenceTrackingObserver` with a single
/// `QAtomicPointer<CIndividualDependenceTracking>` slot. The only concrete
/// dependence-tracking payload currently ported is
/// `CReferredIndividualTrackingVector`, so the slot is the typed arena id for
/// that vector. `install*` preserves the first installed vector exactly like the
/// C++ `testAndSetOrdered(nullptr, indDepTrack)` path.
#[derive(Debug, Clone)]
pub struct IndividualDependenceTrackingCollector {
    /// `QAtomicPointer<CIndividualDependenceTracking> mIndiDepTrackingPointer`.
    individual_dependence_tracking: ReferredIndividualTrackingVectorId,
}

pub type IndividualDependenceTrackingCollectorId = Id<IndividualDependenceTrackingCollector>;

impl Default for IndividualDependenceTrackingCollector {
    fn default() -> Self {
        Self {
            individual_dependence_tracking: ReferredIndividualTrackingVectorId::NONE,
        }
    }
}

impl IndividualDependenceTrackingCollector {
    /// Port of the constructor.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `getExtendingIndividualDependenceTracking`.
    pub fn get_extending_individual_dependence_tracking(
        &self,
    ) -> ReferredIndividualTrackingVectorId {
        self.individual_dependence_tracking
    }

    /// Port of `installIndividualDependenceTracking`.
    pub fn install_individual_dependence_tracking(
        &mut self,
        individual_dependence_tracking: ReferredIndividualTrackingVectorId,
    ) -> ReferredIndividualTrackingVectorId {
        if self.individual_dependence_tracking.is_none() {
            self.individual_dependence_tracking = individual_dependence_tracking;
        }
        self.individual_dependence_tracking
    }
}

/// Port of the `CIndividualDependenceTrackingMarker` payload implemented by the
/// classifier testing items
/// (`COptimizedSubClassSatisfiableTestingItem::{set,has}IndividualDependenceTracked`
/// and `COptimizedKPSetClassTestingItem::{set,has}IndividualDependenceTracked`).
///
/// Both concrete C++ implementations only mutate/read `bool mIndiDepTracked`.
/// The surrounding classifier item fields are ported later with the classifier
/// callers; this typed target keeps the task adapter marker side concrete instead
/// of an opaque integer.
#[derive(Debug, Default, Clone)]
pub struct IndividualDependenceTrackingMarker {
    /// `bool mIndiDepTracked`.
    individual_dependence_tracked: bool,
}

pub type IndividualDependenceTrackingMarkerId = Id<IndividualDependenceTrackingMarker>;

impl IndividualDependenceTrackingMarker {
    /// Port of the constructor-side default (`mIndiDepTracked = false`).
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `setIndividualDependenceTracked`.
    pub fn set_individual_dependence_tracked(&mut self) -> &mut Self {
        self.individual_dependence_tracked = true;
        self
    }

    /// Port of `hasIndividualDependenceTracked`.
    pub fn has_individual_dependence_tracked(&self) -> bool {
        self.individual_dependence_tracked
    }
}

/// Port of `CSatisfiableTaskIndividualDependenceTrackingAdapter`
/// (`Source/Reasoner/Kernel/Task/CSatisfiableTaskIndividualDependenceTrackingAdapter.{h,cpp}`;
/// the task's `mSatIndDepTrackAdapter`).
///
/// The adapter itself only stores two external Consistiser interface pointers:
/// `CIndividualDependenceTrackingObserver*` and
/// `CIndividualDependenceTrackingMarker*`. The observer is the concrete
/// `CIndividualDependenceTrackingCollector` port; the marker target is the
/// shared boolean payload implemented by the classifier testing items.
#[derive(Debug, Clone)]
pub struct SatisfiableTaskIndividualDependenceTrackingAdapter {
    /// `CIndividualDependenceTrackingObserver* mIndiDepTrackObserver`.
    pub individual_dependence_tracking_observer: IndividualDependenceTrackingCollectorId,
    /// `CIndividualDependenceTrackingMarker* mIndiDepTrackMarker`.
    pub individual_dependence_tracking_marker: IndividualDependenceTrackingMarkerId,
}

impl Default for SatisfiableTaskIndividualDependenceTrackingAdapter {
    fn default() -> Self {
        Self {
            individual_dependence_tracking_observer: IndividualDependenceTrackingCollectorId::NONE,
            individual_dependence_tracking_marker: IndividualDependenceTrackingMarkerId::NONE,
        }
    }
}

impl SatisfiableTaskIndividualDependenceTrackingAdapter {
    /// Port of the constructor.
    pub fn new(
        individual_dependence_tracking_observer: IndividualDependenceTrackingCollectorId,
        individual_dependence_tracking_marker: IndividualDependenceTrackingMarkerId,
    ) -> Self {
        Self {
            individual_dependence_tracking_observer,
            individual_dependence_tracking_marker,
        }
    }

    /// Port of `setIndividualDependenceTrackingObserver`.
    pub fn set_individual_dependence_tracking_observer(
        &mut self,
        individual_dependence_tracking_observer: IndividualDependenceTrackingCollectorId,
    ) -> &mut Self {
        self.individual_dependence_tracking_observer = individual_dependence_tracking_observer;
        self
    }

    /// Port of `getIndividualDependenceTrackingObserver`.
    pub fn get_individual_dependence_tracking_observer(
        &self,
    ) -> IndividualDependenceTrackingCollectorId {
        self.individual_dependence_tracking_observer
    }

    /// Port of `setIndividualDependenceTrackingMarker`.
    pub fn set_individual_dependence_tracking_marker(
        &mut self,
        individual_dependence_tracking_marker: IndividualDependenceTrackingMarkerId,
    ) -> &mut Self {
        self.individual_dependence_tracking_marker = individual_dependence_tracking_marker;
        self
    }

    /// Port of `getIndividualDependenceTrackingMarker`.
    pub fn get_individual_dependence_tracking_marker(
        &self,
    ) -> IndividualDependenceTrackingMarkerId {
        self.individual_dependence_tracking_marker
    }
}

/// Port of `CSatisfiableTaskClassificationMessageAdapter`
/// (`Source/Reasoner/Kernel/Task/CSatisfiableTaskClassificationMessageAdapter.{h,cpp}`;
/// the task's `mClassMessAdapter`).
///
/// The ontology/observer fields stay opaque handles until the corresponding KM
/// outer objects are ported. W219 adds the typed classifier-side
/// `CClassificationMessageDataObserver` call surface, but this adapter still
/// preserves the C++ pointer as an opaque handle until ontology/thread event
/// routing is wired. The concept-reference-linking hash carries the C++
/// `QHash<CConcept*, CClassificationSatisfiableCalculationConceptReferenceLinking*>`
/// as `ConceptId -> classifier reference handle`.
#[derive(Debug, Clone)]
pub struct SatisfiableTaskClassificationMessageAdapter {
    /// `CConcept* mTestingConcept`.
    pub testing_concept: ConceptId,
    /// `CConcreteOntology* mOntology`. [api] opaque.
    pub testing_ontology: Cint64,
    /// `CClassificationMessageDataObserver* mMessageObserver`. [api] opaque.
    pub classification_message_data_observer: Cint64,
    /// `QHash<CConcept*,CClassificationSatisfiableCalculationConceptReferenceLinking*>* mConRefLinkDataHash`.
    pub concept_reference_linking_data_hash: Arc<HashMap<ConceptId, Cint64>>,
    /// `cint64 mExtractionFlags`.
    pub extraction_flags: Cint64,
}

impl Default for SatisfiableTaskClassificationMessageAdapter {
    fn default() -> Self {
        Self {
            testing_concept: ConceptId::NONE,
            testing_ontology: INVALID,
            classification_message_data_observer: INVALID,
            concept_reference_linking_data_hash: Arc::new(HashMap::new()),
            extraction_flags: 0,
        }
    }
}

impl SatisfiableTaskClassificationMessageAdapter {
    /// Port of the ctor with the currently concrete fields.
    pub fn new(testing_concept: ConceptId, extraction_flags: Cint64) -> Self {
        Self {
            testing_concept,
            testing_ontology: INVALID,
            classification_message_data_observer: INVALID,
            concept_reference_linking_data_hash: Arc::new(HashMap::new()),
            extraction_flags,
        }
    }

    /// Port of the full C++ constructor shape.
    pub fn new_with_handles(
        testing_concept: ConceptId,
        testing_ontology: Cint64,
        classification_message_data_observer: Cint64,
        concept_reference_linking_data_hash: HashMap<ConceptId, Cint64>,
        extraction_flags: Cint64,
    ) -> Self {
        Self {
            testing_concept,
            testing_ontology,
            classification_message_data_observer,
            concept_reference_linking_data_hash: Arc::new(concept_reference_linking_data_hash),
            extraction_flags,
        }
    }

    /// Construct an adapter over an immutable ontology-wide reference table.
    /// Classification jobs only read this table, so sharing it mirrors the C++
    /// adapter's pointer semantics and avoids copying it for every job.
    pub fn new_with_shared_handles(
        testing_concept: ConceptId,
        testing_ontology: Cint64,
        classification_message_data_observer: Cint64,
        concept_reference_linking_data_hash: Arc<HashMap<ConceptId, Cint64>>,
        extraction_flags: Cint64,
    ) -> Self {
        Self {
            testing_concept,
            testing_ontology,
            classification_message_data_observer,
            concept_reference_linking_data_hash,
            extraction_flags,
        }
    }

    /// Port of `getTestingConcept`.
    pub fn get_testing_concept(&self) -> ConceptId {
        self.testing_concept
    }

    /// Port of the testing-concept setter.
    pub fn set_testing_concept(&mut self, concept: ConceptId) -> &mut Self {
        self.testing_concept = concept;
        self
    }

    /// Port of `getTestingOntology`.
    pub fn get_testing_ontology(&self) -> Cint64 {
        self.testing_ontology
    }

    /// Port-facing setter for the opaque testing ontology handle.
    pub fn set_testing_ontology(&mut self, ontology: Cint64) -> &mut Self {
        self.testing_ontology = ontology;
        self
    }

    /// Port of `getClassificationMessageDataObserver`.
    pub fn get_classification_message_data_observer(&self) -> Cint64 {
        self.classification_message_data_observer
    }

    /// Port-facing setter for the opaque message observer handle.
    pub fn set_classification_message_data_observer(&mut self, observer: Cint64) -> &mut Self {
        self.classification_message_data_observer = observer;
        self
    }

    /// Port of `getConceptReferenceLinkingDataHash`.
    pub fn get_concept_reference_linking_data_hash(&self) -> &HashMap<ConceptId, Cint64> {
        &self.concept_reference_linking_data_hash
    }

    pub fn get_concept_reference_linking_data_hash_mut(
        &mut self,
    ) -> &mut HashMap<ConceptId, Cint64> {
        Arc::make_mut(&mut self.concept_reference_linking_data_hash)
    }

    pub fn set_concept_reference_linking_data_hash(
        &mut self,
        con_ref_linking_hash: HashMap<ConceptId, Cint64>,
    ) -> &mut Self {
        self.concept_reference_linking_data_hash = Arc::new(con_ref_linking_hash);
        self
    }

    /// Port of `getExtractionFlags`.
    pub fn get_extraction_flags(&self) -> Cint64 {
        self.extraction_flags
    }

    /// Port of `setExtractionFlags`.
    pub fn set_extraction_flags(&mut self, flags: Cint64) -> &mut Self {
        self.extraction_flags = flags;
        self
    }

    /// Port of additive extraction flag setup.
    pub fn add_extraction_flags(&mut self, flags: Cint64) -> &mut Self {
        self.extraction_flags |= flags;
        self
    }

    /// Port of `hasExtractionFlags`.
    pub fn has_extraction_flags(&self, flags: Cint64) -> bool {
        (self.extraction_flags & flags) != 0
    }
}

/// Port of `CSatisfiableTaskClassificationRoleMarkedMessageAdapter`
/// (`Source/Reasoner/Kernel/Task/CSatisfiableTaskClassificationRoleMarkedMessageAdapter.{h,cpp}`;
/// the task's `mClassRoleMarkedMessageAdapter`).
#[derive(Debug, Clone)]
pub struct SatisfiableTaskClassificationRoleMarkedMessageAdapter {
    /// `CRole* mTestingRole`.
    testing_role: RoleId,
    /// `CIndividual* mPropagationIndividual`.
    propagation_individual: IndividualId,
    /// `CIndividual* mMarkerIndividual`.
    marker_individual: IndividualId,
    /// `CConcreteOntology* mOntology`. [api] opaque.
    testing_ontology: Cint64,
    /// `CRoleClassificationMessageDataObserver* mMessageObserver`. [api] opaque.
    classification_message_data_observer: Cint64,
}

impl Default for SatisfiableTaskClassificationRoleMarkedMessageAdapter {
    fn default() -> Self {
        Self {
            testing_role: RoleId::NONE,
            propagation_individual: IndividualId::NONE,
            marker_individual: IndividualId::NONE,
            testing_ontology: INVALID,
            classification_message_data_observer: INVALID,
        }
    }
}

impl SatisfiableTaskClassificationRoleMarkedMessageAdapter {
    /// Port of the constructor.
    pub fn new(
        testing_role: RoleId,
        propagation_individual: IndividualId,
        marker_individual: IndividualId,
        testing_ontology: Cint64,
        classification_message_data_observer: Cint64,
    ) -> Self {
        Self {
            testing_role,
            propagation_individual,
            marker_individual,
            testing_ontology,
            classification_message_data_observer,
        }
    }

    /// Port of `getTestingRole`.
    pub fn get_testing_role(&self) -> RoleId {
        self.testing_role
    }

    /// Port of `getPropagationIndividual`.
    pub fn get_propagation_individual(&self) -> IndividualId {
        self.propagation_individual
    }

    /// Port of `getMarkerIndividual`.
    pub fn get_marker_individual(&self) -> IndividualId {
        self.marker_individual
    }

    /// Port of `getTestingOntology`.
    pub fn get_testing_ontology(&self) -> Cint64 {
        self.testing_ontology
    }

    /// Port of `getClassificationMessageDataObserver`.
    pub fn get_classification_message_data_observer(&self) -> Cint64 {
        self.classification_message_data_observer
    }
}

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
#[derive(Debug, Clone)]
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
    /// Rust-owned bridge for `getPreviousConsistentOntology()->getConsistence()
    /// ->getConsistenceModelData()` when that model data is already available.
    pub previous_consistence_data: TaskDataId,
}

impl Default for SatisfiableTaskIncrementalConsistencyTestingAdapter {
    fn default() -> Self {
        Self {
            ontology: 0,
            prev_cons_ontology: 0,
            cons_observer: 0,
            incremental_revision_id: 0,
            previous_consistence_data: TaskDataId::NONE,
        }
    }
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
            previous_consistence_data: TaskDataId::NONE,
        }
    }

    /// Port of `getTestingOntology`.
    pub fn get_testing_ontology(&self) -> Cint64 {
        self.ontology
    }
    /// Port of `getPreviousConsistentOntology`.
    pub fn get_previous_consistent_ontology(&self) -> Cint64 {
        self.prev_cons_ontology
    }
    /// Port of `getConsistenceObserver`.
    pub fn get_consistence_observer(&self) -> Cint64 {
        self.cons_observer
    }
    /// Port of `getIncrementalRevisionID`.
    pub fn get_incremental_revision_id(&self) -> Cint64 {
        self.incremental_revision_id
    }
    /// Port-facing typed previous-consistence-data bridge.
    pub fn get_previous_consistence_data(&self) -> TaskDataId {
        self.previous_consistence_data
    }
    /// Port-facing typed previous-consistence-data setter.
    pub fn set_previous_consistence_data(&mut self, task_data: TaskDataId) -> &mut Self {
        self.previous_consistence_data = task_data;
        self
    }
}

#[cfg(test)]
mod tests {
    use super::super::super::model::concept;
    use super::super::super::model::substrate::Id;
    use super::*;

    #[test]
    fn classification_message_adapter_tracks_testing_concept_and_flags() {
        let concept = Id::<concept::Concept>::new(3);
        let mut adapter = SatisfiableTaskClassificationMessageAdapter::default();

        assert!(adapter.get_testing_concept().is_none());
        assert_eq!(adapter.get_testing_ontology(), INVALID);
        assert_eq!(adapter.get_classification_message_data_observer(), INVALID);
        assert!(adapter.get_concept_reference_linking_data_hash().is_empty());
        assert_eq!(adapter.get_extraction_flags(), 0);
        assert!(!adapter.has_extraction_flags(EFEXTRACTSUBSUMERSROOTNODE));

        adapter
            .set_testing_concept(concept)
            .add_extraction_flags(EFEXTRACTSUBSUMERSROOTNODE);

        assert_eq!(adapter.get_testing_concept(), concept);
        assert!(adapter.has_extraction_flags(EFEXTRACTSUBSUMERSROOTNODE));

        adapter.set_extraction_flags(0);
        assert!(!adapter.has_extraction_flags(EFEXTRACTSUBSUMERSROOTNODE));
    }

    #[test]
    fn classification_message_adapter_ports_full_constructor_and_any_flag_test() {
        let concept = Id::<concept::Concept>::new(5);
        let linked_concept = Id::<concept::Concept>::new(7);
        let mut con_ref_hash = HashMap::new();
        con_ref_hash.insert(linked_concept, 97);

        let mut adapter = SatisfiableTaskClassificationMessageAdapter::new_with_handles(
            concept,
            11,
            13,
            con_ref_hash,
            EFEXTRACTIDENTIFIERPSEUDOMODEL | EFEXTRACTPOSSIBLESUBSUMERSROOTNODE,
        );

        assert_eq!(adapter.get_testing_concept(), concept);
        assert_eq!(adapter.get_testing_ontology(), 11);
        assert_eq!(adapter.get_classification_message_data_observer(), 13);
        assert_eq!(
            adapter
                .get_concept_reference_linking_data_hash()
                .get(&linked_concept),
            Some(&97)
        );
        assert!(adapter.has_extraction_flags(EFEXTRACTIDENTIFIERPSEUDOMODEL));
        assert!(adapter.has_extraction_flags(EFEXTRACTALL));
        assert!(adapter.has_extraction_flags(
            EFEXTRACTIDENTIFIERPSEUDOMODEL | EFEXTRACTOTHERNODESSINGLEDEPENDENCY
        ));
        assert!(!adapter.has_extraction_flags(EFEXTRACTOTHERNODESSINGLEDEPENDENCY));

        adapter
            .set_testing_ontology(17)
            .set_classification_message_data_observer(19)
            .get_concept_reference_linking_data_hash_mut()
            .insert(concept, 101);

        assert_eq!(adapter.get_testing_ontology(), 17);
        assert_eq!(adapter.get_classification_message_data_observer(), 19);
        assert_eq!(
            adapter
                .get_concept_reference_linking_data_hash()
                .get(&concept),
            Some(&101)
        );
    }

    #[test]
    fn classification_message_adapter_shares_immutable_reference_table() {
        let concept = Id::<concept::Concept>::new(5);
        let linked_concept = Id::<concept::Concept>::new(7);
        let shared = Arc::new(HashMap::from([(linked_concept, 97)]));
        let mut adapter = SatisfiableTaskClassificationMessageAdapter::new_with_shared_handles(
            concept,
            11,
            13,
            shared.clone(),
            EFEXTRACTALL,
        );

        assert!(Arc::ptr_eq(&shared, &adapter.concept_reference_linking_data_hash));
        adapter
            .get_concept_reference_linking_data_hash_mut()
            .insert(concept, 101);
        assert!(!shared.contains_key(&concept));
        assert_eq!(
            adapter
                .get_concept_reference_linking_data_hash()
                .get(&concept),
            Some(&101)
        );
    }

    #[test]
    fn role_marked_classification_message_adapter_tracks_constructor_payload() {
        let role = RoleId::new(7);
        let propagation_individual = IndividualId::new(11);
        let marker_individual = IndividualId::new(13);

        let default_adapter = SatisfiableTaskClassificationRoleMarkedMessageAdapter::default();
        assert!(default_adapter.get_testing_role().is_none());
        assert!(default_adapter.get_propagation_individual().is_none());
        assert!(default_adapter.get_marker_individual().is_none());
        assert_eq!(default_adapter.get_testing_ontology(), INVALID);
        assert_eq!(
            default_adapter.get_classification_message_data_observer(),
            INVALID
        );

        let adapter = SatisfiableTaskClassificationRoleMarkedMessageAdapter::new(
            role,
            propagation_individual,
            marker_individual,
            17,
            19,
        );
        assert_eq!(adapter.get_testing_role(), role);
        assert_eq!(adapter.get_propagation_individual(), propagation_individual);
        assert_eq!(adapter.get_marker_individual(), marker_individual);
        assert_eq!(adapter.get_testing_ontology(), 17);
        assert_eq!(adapter.get_classification_message_data_observer(), 19);
    }
}
