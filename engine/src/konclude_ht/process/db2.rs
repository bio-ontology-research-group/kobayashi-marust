//! `process/db2.rs` — method-batch unit **DB-2**: the `CProcessingDataBox`
//! localised lazy-alloc getters, id counters, and the individual
//! processing-queue / process-node-vector / ontology accessors.
//!
//! Port of `Source/Reasoner/Kernel/Process/CProcessingDataBox.cpp` lines 600–781.
//! These are mechanical: each `getX(forceLocalisation)` lazily localises a
//! buffered slot (allocate-fresh + reference/init the parent's + set
//! `use = loc`); the `getNextXID` family hands out a counter and optionally
//! bumps it; the rest are plain field accessors.
//!
//! Skipped (already defined elsewhere, NOT re-ported here to avoid duplicates):
//!   - `getOntologyTopConcept`        (.cpp 771) → `ontology_top_concept` in databox.rs
//!   - `getOntologyTopDataRangeConcept` (.cpp 775) → `ontology_top_data_range_concept` in databox.rs
//!
//! KONCLUDE-PORT-NOTE[api]: every localising getter allocates a fresh container
//! via `CObjectParameterizingAllocator<…, CProcessContext*>` and seeds it from
//! the parent buffer (`referenceVector` / `initX`). The pool allocator and those
//! container classes are not yet ported, so the allocation + seed step is left as
//! a `W2-DEFER[api]` no-op and `mLocX` stays `Id::NONE` (the db1.rs convention).
//! The surrounding branch structure and the `mUseX = mLocX` assignment are ported
//! faithfully so the control flow diffs against the C++ method-by-method.

#![allow(dead_code)]

use super::super::model::substrate::{Cint64, Id};
use super::databox::ProcessingDataBox;
use super::node_resolution::IndividualProcessNodeVector;
use super::stubs::{
    ConceptNominalSchemaGroundingHash, ConceptVector,
    IndividualProcessingQueue, MarkerIndividualNodeHash, NominalCachingLossReactivationHash,
    RepresentativeJoiningHash, RepresentativeVariableBindingPathHash,
    RepresentativeVariableBindingPathJoiningKeyHash, RepresentativeVariableBindingPathSetHash,
    VariableBindingPathMergingHash,
};

impl ProcessingDataBox {
    /// Port of `CProcessingDataBox::getExtendedConceptVector`. `.cpp` 600–607.
    pub fn extended_concept_vector(&mut self, force_localisation: bool) -> Id<ConceptVector> {
        if force_localisation && self.loc_extended_concept_vector.is_none() {
            // W2-DEFER[api]: mLocExtendedConceptVector =
            //   CObjectParameterizingAllocator<CConceptVector,CContext*>::allocate…(mProcessContext);
            //   mLocExtendedConceptVector->referenceVector(mUseExtendedConceptVector);
            // (per-test arena alloc + seed owned by the not-yet-ported CProcessContext) — loc stays Id::NONE.
            self.use_extended_concept_vector = self.loc_extended_concept_vector; // 604
        }
        self.use_extended_concept_vector // 606
    }

    /// Port of `CProcessingDataBox::getConceptNominalSchemaGroundingHash`. `.cpp` 610–617.
    pub fn concept_nominal_schema_grounding_hash(
        &mut self,
        force_localisation: bool,
    ) -> Id<ConceptNominalSchemaGroundingHash> {
        if force_localisation && self.loc_grounding_hash.is_none() {
            // W2-DEFER[api]: alloc CConceptNominalSchemaGroundingHash +
            //   mLocGroundingHash->initConceptNominalSchemaGroundingHash(mUseGroundingHash);
            self.use_grounding_hash = self.loc_grounding_hash; // 614
        }
        self.use_grounding_hash // 616
    }

    /// Port of `CProcessingDataBox::getVariableBindingPathMergingHash`. `.cpp` 621–628.
    pub fn variable_binding_path_merging_hash(
        &mut self,
        force_localisation: bool,
    ) -> Id<VariableBindingPathMergingHash> {
        if force_localisation && self.loc_var_binding_path_merging_hash.is_none() {
            // W2-DEFER[api]: alloc CVariableBindingPathMergingHash +
            //   mLocVarBindingPathMergingHash->initVariableBindingPathMergingHash(mUseVarBindingPathMergingHash);
            self.use_var_binding_path_merging_hash = self.loc_var_binding_path_merging_hash; // 625
        }
        self.use_var_binding_path_merging_hash // 627
    }

    /// Port of `CProcessingDataBox::getRepresentativeVariableBindingPathSetHash`. `.cpp` 631–638.
    pub fn representative_variable_binding_path_set_hash(
        &mut self,
        force_localisation: bool,
    ) -> Id<RepresentativeVariableBindingPathSetHash> {
        if force_localisation && self.loc_rep_var_bind_path_set_hash.is_none() {
            // W2-DEFER[api]: alloc CRepresentativeVariableBindingPathSetHash +
            //   mLocRepVarBindPathSetHash->initRepresentativeVariableBindingPathSetHash(mUseRepVarBindPathSetHash);
            self.use_rep_var_bind_path_set_hash = self.loc_rep_var_bind_path_set_hash; // 635
        }
        self.use_rep_var_bind_path_set_hash // 637
    }

    /// Port of `CProcessingDataBox::getRepresentativeVariableBindingPathHash`. `.cpp` 640–647.
    pub fn representative_variable_binding_path_hash(
        &mut self,
        force_localisation: bool,
    ) -> Id<RepresentativeVariableBindingPathHash> {
        if force_localisation && self.loc_rep_var_bind_path_hash.is_none() {
            // W2-DEFER[api]: alloc CRepresentativeVariableBindingPathHash +
            //   mLocRepVarBindPathHash->initRepresentativeVariableBindingPathHash(mUseRepVarBindPathHash);
            self.use_rep_var_bind_path_hash = self.loc_rep_var_bind_path_hash; // 644
        }
        self.use_rep_var_bind_path_hash // 646
    }

    /// Port of `CProcessingDataBox::getRepresentativeVariableBindingPathJoiningKeyHash`. `.cpp` 651–658.
    pub fn representative_variable_binding_path_joining_key_hash(
        &mut self,
        force_localisation: bool,
    ) -> Id<RepresentativeVariableBindingPathJoiningKeyHash> {
        if force_localisation && self.loc_rep_var_bind_path_joining_key_hash.is_none() {
            // W2-DEFER[api]: alloc CRepresentativeVariableBindingPathJoiningKeyHash +
            //   mLocRepVarBindPathJoiningKeyHash->initRepresentativeVariableBindingPathJoiningKeyHash(mUseRepVarBindPathJoiningKeyHash);
            self.use_rep_var_bind_path_joining_key_hash = self.loc_rep_var_bind_path_joining_key_hash; // 655
        }
        self.use_rep_var_bind_path_joining_key_hash // 657
    }

    /// Port of `CProcessingDataBox::getRepresentativeJoiningHash`. `.cpp` 660–667.
    pub fn representative_joining_hash(
        &mut self,
        force_localisation: bool,
    ) -> Id<RepresentativeJoiningHash> {
        if force_localisation && self.loc_rep_joining_hash.is_none() {
            // W2-DEFER[api]: alloc CRepresentativeJoiningHash +
            //   mLocRepJoiningHash->initRepresentativeJoiningHash(mUseRepJoiningHash);
            self.use_rep_joining_hash = self.loc_rep_joining_hash; // 664
        }
        self.use_rep_joining_hash // 666
    }

    /// Port of `CProcessingDataBox::getNominalCachingLossReactivationHash`. `.cpp` 670–677.
    pub fn nominal_caching_loss_reactivation_hash(
        &mut self,
        create_or_force_localisation: bool,
    ) -> Id<NominalCachingLossReactivationHash> {
        if create_or_force_localisation && self.loc_nom_caching_loss_react_hash.is_none() {
            // W2-DEFER[api]: alloc CNominalCachingLossReactivationHash +
            //   mLocNomCachingLossReactHash->initNominalDependentNodeHash(mUseNomCachingLossReactHash);
            self.use_nom_caching_loss_react_hash = self.loc_nom_caching_loss_react_hash; // 674
        }
        self.use_nom_caching_loss_react_hash // 676
    }

    /// Port of `CProcessingDataBox::getMarkerIndividualNodeHash`. `.cpp` 680–687.
    pub fn marker_individual_node_hash(
        &mut self,
        create_or_force_localisation: bool,
    ) -> Id<MarkerIndividualNodeHash> {
        if create_or_force_localisation && self.loc_marker_indi_node_hash.is_none() {
            // W2-DEFER[api]: alloc CMarkerIndividualNodeHash +
            //   mLocMarkerIndiNodeHash->initMarkerIndividualNodeHash(mUseMarkerIndiNodeHash);
            self.use_marker_indi_node_hash = self.loc_marker_indi_node_hash; // 683
        }
        self.use_marker_indi_node_hash // 686
    }

    /// Port of `CProcessingDataBox::getNextSaturationResolvedSuccessorExtensionIndividualNodeID`.
    /// `.cpp` 690–704.
    pub fn next_saturation_resolved_successor_extension_individual_node_id(
        &mut self,
        increment_next_id: bool,
    ) -> Cint64 {
        if self.next_sat_res_succ_ext_individual_node_id == -1 {
            // W2-DEFER[api]: mNextSatResSuccExtIndividualNodeID = mIndiSaturationProcessVector->getItemCount();
            //   then qMax against mOntology->getABox()->getIndividualCount() and, if present,
            //   mOntology->getOntologyTriplesData()->getTripleAssertionAccessor()->getMaxIndexedIndividualId().
            // (saturation vector / ABox / triples accessor not yet ported) — left at -1.
        }
        let next_prop_id = self.next_sat_res_succ_ext_individual_node_id; // 699
        if increment_next_id {
            self.next_sat_res_succ_ext_individual_node_id += 1; // 701
        }
        next_prop_id // 703
    }

    /// Port of `CProcessingDataBox::getNextIndividualNodeID`. `.cpp` 706–712.
    pub fn next_individual_node_id(&mut self, increment_next_id: bool) -> Cint64 {
        let next_prop_id = self.next_individual_node_id; // 707
        if increment_next_id {
            self.next_individual_node_id += 1; // 709
        }
        next_prop_id // 711
    }

    /// Port of `CProcessingDataBox::setFirstPossibleIndividualNodeID`. `.cpp` 714–717.
    pub fn set_first_possible_individual_node_id(&mut self, indi_id: Cint64) -> &mut Self {
        self.next_individual_node_id = indi_id; // 715
        self
    }

    /// Port of `CProcessingDataBox::getNextBindingPropagationID`. `.cpp` 720–726.
    pub fn next_binding_propagation_id(&mut self, increment_next_id: bool) -> Cint64 {
        let next_prop_id = self.next_propagation_id; // 721
        if increment_next_id {
            self.next_propagation_id += 1; // 723
        }
        next_prop_id // 725
    }

    /// Port of `CProcessingDataBox::getNextVariableBindingPathID`. `.cpp` 728–734.
    pub fn next_variable_binding_path_id(&mut self, increment_next_id: bool) -> Cint64 {
        let next_prop_id = self.next_variable_id; // 729
        if increment_next_id {
            self.next_variable_id += 1; // 731
        }
        next_prop_id // 733
    }

    /// Port of `CProcessingDataBox::getNextRepresentativeVariableBindingPathID`. `.cpp` 736–742.
    pub fn next_representative_variable_binding_path_id(&mut self, increment_next_id: bool) -> Cint64 {
        let next_prop_id = self.next_rep_variable_id; // 737
        if increment_next_id {
            self.next_rep_variable_id += 1; // 739
        }
        next_prop_id // 741
    }

    /// Port of `CProcessingDataBox::getIndividualProcessingQueue`. `.cpp` 744–751.
    ///
    /// KONCLUDE-PORT-NOTE[api]: the C++ `bool create` parameter is unused in the
    /// method body (the lazy-alloc is gated only by `!mLocIndiProcessQueue`);
    /// kept as `_create` for signature fidelity.
    pub fn individual_processing_queue(&mut self, _create: bool) -> Id<IndividualProcessingQueue> {
        if self.loc_indi_process_queue.is_none() {
            // W2-DEFER[api]: alloc CIndividualProcessingQueue +
            //   mLocIndiProcessQueue->initProcessingQueue(mUseIndiProcessQueue);
            self.use_indi_process_queue = self.loc_indi_process_queue; // 748
        }
        self.use_indi_process_queue // 750
    }

    /// Port of `CProcessingDataBox::clearIndividualProcessingQueue`. `.cpp` 754–758.
    pub fn clear_individual_processing_queue(&mut self) -> &mut Self {
        self.use_indi_process_queue = Id::NONE; // 755
        self.loc_indi_process_queue = Id::NONE; // 756
        self
    }

    /// Port of `CProcessingDataBox::getIndividualProcessNodeVector`. `.cpp` 761–763.
    /// Returns a borrow of the owned vector (the C++ returns the `mIndiProcessVector`
    /// pointer; the port holds it by value).
    pub fn individual_process_node_vector(&self) -> &IndividualProcessNodeVector {
        &self.indi_process_vector
    }

    /// Mutable access to the owned node vector (the `setLocalData` / merge path).
    pub fn individual_process_node_vector_mut(&mut self) -> &mut IndividualProcessNodeVector {
        &mut self.indi_process_vector
    }

    /// Port of `CProcessingDataBox::setIndividualProcessNodeVector`. `.cpp` 765–768.
    /// Replaces the owned vector by value (the C++ swaps the pointer).
    pub fn set_individual_process_node_vector(
        &mut self,
        indi_node_vec: IndividualProcessNodeVector,
    ) -> &mut Self {
        self.indi_process_vector = indi_node_vec; // 766
        self
    }

    // `getOntologyTopConcept` (.cpp 771–773) and `getOntologyTopDataRangeConcept`
    // (.cpp 775–777) are already defined in `databox.rs` — NOT re-ported here.

    /// Port of `CProcessingDataBox::getOntology`. `.cpp` 779–781.
    ///
    /// KONCLUDE-PORT-NOTE[api]: `CConcreteOntology*` is a not-yet-ported upstream
    /// layer; the field is an opaque `Cint64` handle (per DB-1).
    pub fn ontology(&self) -> Cint64 {
        self.ontology
    }
}
