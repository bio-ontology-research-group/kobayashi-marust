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
//! KONCLUDE-PORT-NOTE[ownership]: every localising getter allocates a fresh
//! container via `CObjectParameterizingAllocator<…, CProcessContext*>` and seeds
//! it from the parent buffer (`referenceVector` / `initX`). The arena port
//! threads `ProcessContext` into the getters whose target containers are already
//! ported. Getters whose target payload is still only an opaque stub keep their
//! explicit `W2-DEFER[api]` marker.

#![allow(dead_code)]

use super::super::model::substrate::{Cint64, Id};
use super::context::ProcessContext;
use super::databox::ProcessingDataBox;
use super::grounding_hash::ConceptNominalSchemaGroundingHash;
use super::marker_hash::MarkerIndividualNodeHash;
use super::node_resolution::IndividualProcessNodeVector;
use super::reactivation::NominalCachingLossReactivationHash;
use super::stubs::{
    ConceptVector, IndividualProcessingQueue, RepresentativeJoiningHash,
    RepresentativeVariableBindingPathHash, RepresentativeVariableBindingPathJoiningKeyHash,
    RepresentativeVariableBindingPathSetHash,
};
use super::varbind::VariableBindingPathMergingHash;

impl ProcessingDataBox {
    /// Port of `CProcessingDataBox::getExtendedConceptVector`. `.cpp` 600–607.
    pub fn extended_concept_vector(&mut self, force_localisation: bool) -> Id<ConceptVector> {
        if force_localisation && self.loc_extended_concept_vector.is_none() {
            // W2-DEFER[api]: mLocExtendedConceptVector =
            //   CObjectParameterizingAllocator<CConceptVector,CContext*>::allocate…(mProcessContext);
            //   mLocExtendedConceptVector->referenceVector(mUseExtendedConceptVector);
            // (per-test arena alloc + seed owned by the not-yet-ported CProcessContext) — loc stays Id::NONE.
            self.use_extended_concept_vector = self.loc_extended_concept_vector;
            // 604
        }
        self.use_extended_concept_vector // 606
    }

    /// Port of `CProcessingDataBox::getConceptNominalSchemaGroundingHash`. `.cpp` 610–617.
    pub fn concept_nominal_schema_grounding_hash(
        &mut self,
        ctx: &mut ProcessContext,
        force_localisation: bool,
    ) -> Id<ConceptNominalSchemaGroundingHash> {
        ctx.processing_data_box_concept_nominal_schema_grounding_hash(self, force_localisation)
    }

    /// Port of `CProcessingDataBox::getVariableBindingPathMergingHash`. `.cpp` 621–628.
    pub fn variable_binding_path_merging_hash(
        &mut self,
        ctx: &mut ProcessContext,
        force_localisation: bool,
    ) -> Id<VariableBindingPathMergingHash> {
        ctx.processing_data_box_variable_binding_path_merging_hash(self, force_localisation)
    }

    /// Port of `CProcessingDataBox::getRepresentativeVariableBindingPathSetHash`. `.cpp` 631–638.
    pub fn representative_variable_binding_path_set_hash(
        &mut self,
        ctx: &mut ProcessContext,
        force_localisation: bool,
    ) -> Id<RepresentativeVariableBindingPathSetHash> {
        ctx.processing_data_box_representative_variable_binding_path_set_hash(
            self,
            force_localisation,
        )
    }

    /// Port of `CProcessingDataBox::getRepresentativeVariableBindingPathHash`. `.cpp` 640–647.
    pub fn representative_variable_binding_path_hash(
        &mut self,
        ctx: &mut ProcessContext,
        force_localisation: bool,
    ) -> Id<RepresentativeVariableBindingPathHash> {
        ctx.processing_data_box_representative_variable_binding_path_hash(self, force_localisation)
    }

    /// Port of `CProcessingDataBox::getRepresentativeVariableBindingPathJoiningKeyHash`. `.cpp` 651–658.
    pub fn representative_variable_binding_path_joining_key_hash(
        &mut self,
        ctx: &mut ProcessContext,
        force_localisation: bool,
    ) -> Id<RepresentativeVariableBindingPathJoiningKeyHash> {
        ctx.processing_data_box_representative_variable_binding_path_joining_key_hash(
            self,
            force_localisation,
        )
    }

    /// Port of `CProcessingDataBox::getRepresentativeJoiningHash`. `.cpp` 660–667.
    pub fn representative_joining_hash(
        &mut self,
        ctx: &mut ProcessContext,
        force_localisation: bool,
    ) -> Id<RepresentativeJoiningHash> {
        ctx.processing_data_box_representative_joining_hash(self, force_localisation)
    }

    /// Port of `CProcessingDataBox::getNominalCachingLossReactivationHash`. `.cpp` 670–677.
    pub fn nominal_caching_loss_reactivation_hash(
        &mut self,
        ctx: &mut ProcessContext,
        create_or_force_localisation: bool,
    ) -> Id<NominalCachingLossReactivationHash> {
        ctx.processing_data_box_nominal_caching_loss_reactivation_hash(
            self,
            create_or_force_localisation,
        )
    }

    /// Port of `CProcessingDataBox::getMarkerIndividualNodeHash`. `.cpp` 680–687.
    pub fn marker_individual_node_hash(
        &mut self,
        ctx: &mut ProcessContext,
        create_or_force_localisation: bool,
    ) -> Id<MarkerIndividualNodeHash> {
        ctx.processing_data_box_marker_individual_node_hash(self, create_or_force_localisation)
    }

    /// Port of `CProcessingDataBox::getNextSaturationResolvedSuccessorExtensionIndividualNodeID`.
    /// `.cpp` 690–704.
    pub fn next_saturation_resolved_successor_extension_individual_node_id(
        &mut self,
        increment_next_id: bool,
    ) -> Cint64 {
        if self.next_sat_res_succ_ext_individual_node_id == -1 {
            // KONCLUDE-PORT-NOTE[api]: the exact port needs the ontology ABox and
            // triples accessor. Use the resolved overload below or
            // `CalculationAlgorithmContextBase::next_saturation_resolved_successor_extension_individual_node_id`.
        }
        let next_prop_id = self.next_sat_res_succ_ext_individual_node_id; // 699
        if increment_next_id {
            self.next_sat_res_succ_ext_individual_node_id += 1; // 701
        }
        next_prop_id // 703
    }

    /// Resolved port of
    /// `CProcessingDataBox::getNextSaturationResolvedSuccessorExtensionIndividualNodeID`.
    /// `.cpp` 690-704.
    ///
    /// This is the exact call shape once the opaque `CConcreteOntology*` has been
    /// resolved by the caller: initialize the counter lazily to
    /// `qMax(mIndiSaturationProcessVector->getItemCount(),
    /// mOntology->getABox()->getIndividualCount(),
    /// triplesAccessor->getMaxIndexedIndividualId())`, then return and
    /// optionally increment it.
    pub fn next_saturation_resolved_successor_extension_individual_node_id_resolved(
        &mut self,
        ontology_individual_count: Cint64,
        max_triples_indexed_individual_id: Option<Cint64>,
        increment_next_id: bool,
    ) -> Cint64 {
        if self.next_sat_res_succ_ext_individual_node_id == -1 {
            let vector_count = self
                .indi_saturation_process_vector
                .as_ref()
                .map_or(0, |vec| vec.get_item_count());
            self.next_sat_res_succ_ext_individual_node_id =
                vector_count.max(ontology_individual_count);
            if let Some(max_indexed_individual_id) = max_triples_indexed_individual_id {
                self.next_sat_res_succ_ext_individual_node_id = self
                    .next_sat_res_succ_ext_individual_node_id
                    .max(max_indexed_individual_id);
            }
        }
        let next_prop_id = self.next_sat_res_succ_ext_individual_node_id;
        if increment_next_id {
            self.next_sat_res_succ_ext_individual_node_id += 1;
        }
        next_prop_id
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
    pub fn next_representative_variable_binding_path_id(
        &mut self,
        increment_next_id: bool,
    ) -> Cint64 {
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
    pub fn individual_processing_queue(
        &mut self,
        ctx: &mut ProcessContext,
        _create: bool,
    ) -> Id<IndividualProcessingQueue> {
        if self.loc_indi_process_queue.is_none() {
            self.loc_indi_process_queue =
                ctx.alloc_individual_processing_queue_from_prev(self.use_indi_process_queue);
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

#[cfg(test)]
mod tests {
    use super::super::node::IndividualProcessNodePriority;
    use super::*;

    #[test]
    fn db2_context_threaded_hash_wrappers_allocate_and_reuse() {
        let mut ctx = ProcessContext::new();
        let mut data_box = ProcessingDataBox::new();

        assert_eq!(
            data_box.concept_nominal_schema_grounding_hash(&mut ctx, false),
            Id::NONE
        );
        let grounding = data_box.concept_nominal_schema_grounding_hash(&mut ctx, true);
        assert!(grounding.is_some());
        assert_eq!(
            data_box.concept_nominal_schema_grounding_hash(&mut ctx, true),
            grounding
        );

        let merging = data_box.variable_binding_path_merging_hash(&mut ctx, true);
        assert!(merging.is_some());
        assert_eq!(
            data_box.variable_binding_path_merging_hash(&mut ctx, true),
            merging
        );

        let rep_set = data_box.representative_variable_binding_path_set_hash(&mut ctx, true);
        assert!(rep_set.is_some());
        assert_eq!(
            data_box.representative_variable_binding_path_set_hash(&mut ctx, true),
            rep_set
        );

        let rep_path = data_box.representative_variable_binding_path_hash(&mut ctx, true);
        assert!(rep_path.is_some());
        assert_eq!(
            data_box.representative_variable_binding_path_hash(&mut ctx, true),
            rep_path
        );

        let joining_key =
            data_box.representative_variable_binding_path_joining_key_hash(&mut ctx, true);
        assert!(joining_key.is_some());
        assert_eq!(
            data_box.representative_variable_binding_path_joining_key_hash(&mut ctx, true),
            joining_key
        );

        let joining = data_box.representative_joining_hash(&mut ctx, true);
        assert!(joining.is_some());
        assert_eq!(
            data_box.representative_joining_hash(&mut ctx, true),
            joining
        );

        let marker = data_box.marker_individual_node_hash(&mut ctx, true);
        assert!(marker.is_some());
        assert_eq!(data_box.marker_individual_node_hash(&mut ctx, true), marker);

        let nominal_reactivation = data_box.nominal_caching_loss_reactivation_hash(&mut ctx, true);
        assert!(nominal_reactivation.is_some());
        assert_eq!(
            data_box.nominal_caching_loss_reactivation_hash(&mut ctx, true),
            nominal_reactivation
        );
    }

    #[test]
    fn nominal_caching_loss_reactivation_hash_localizes_and_creates_data_from_previous() {
        let mut ctx = ProcessContext::new();
        let mut data_box = ProcessingDataBox::new();

        let prev_hash = ctx.alloc_nominal_caching_loss_reactivation_hash(
            NominalCachingLossReactivationHash::new(0),
        );
        let prev_data = ctx.nominal_caching_loss_reactivation_hash_get_data(prev_hash, 41, true);
        ctx.nominal_caching_loss_reactivation_data_mut(prev_data)
            .set_reactivated(true)
            .add_reactivation_individual_node(super::super::NodeId::new(7));
        data_box.use_nom_caching_loss_react_hash = prev_hash;

        let localized = data_box.nominal_caching_loss_reactivation_hash(&mut ctx, true);
        assert!(localized.is_some());
        assert_ne!(localized, prev_hash);
        assert_eq!(data_box.loc_nom_caching_loss_react_hash, localized);
        assert_eq!(data_box.use_nom_caching_loss_react_hash, localized);

        assert_eq!(
            ctx.nominal_caching_loss_reactivation_hash_get_data(localized, 41, false),
            prev_data
        );
        let localized_data =
            ctx.nominal_caching_loss_reactivation_hash_get_data(localized, 41, true);
        assert!(localized_data.is_some());
        assert_ne!(localized_data, prev_data);
        assert!(ctx
            .nominal_caching_loss_reactivation_data(localized_data)
            .has_reactivated());
        assert_eq!(
            ctx.nominal_caching_loss_reactivation_data(localized_data)
                .get_reactivation_individual_node_linker(),
            &[super::super::NodeId::new(7)]
        );
        assert_eq!(
            ctx.nominal_caching_loss_reactivation_hash_get_data(localized, 41, false),
            localized_data
        );
    }

    #[test]
    fn db2_individual_processing_queue_localizes_once_and_clear_resets() {
        let mut ctx = ProcessContext::new();
        let mut data_box = ProcessingDataBox::new();

        let queue = data_box.individual_processing_queue(&mut ctx, false);
        assert!(queue.is_some());
        assert_eq!(data_box.individual_processing_queue(&mut ctx, true), queue);

        data_box.clear_individual_processing_queue();
        assert_eq!(data_box.use_indi_process_queue, Id::NONE);
        assert_eq!(data_box.loc_indi_process_queue, Id::NONE);

        let relocalized_queue = data_box.individual_processing_queue(&mut ctx, false);
        assert!(relocalized_queue.is_some());
        assert_ne!(relocalized_queue, queue);
    }

    #[test]
    fn db2_individual_processing_queue_localization_copies_previous_queue_payload() {
        let mut ctx = ProcessContext::new();
        let mut data_box = ProcessingDataBox::new();
        let prev_queue = ctx.alloc_individual_processing_queue_from_prev(Id::NONE);
        let mut priority = IndividualProcessNodePriority::default();
        priority.set_priority(3.0, 5.0);

        {
            let queue = ctx.indi_proc_queue_mut(prev_queue);
            queue.indi_pro_des_count = 1;
            queue.indi_des_priority_hash.insert(17, priority);
            queue.has_max_indi_priority = true;
            queue.max_indi_priority = priority;
        }
        data_box.use_indi_process_queue = prev_queue;

        let localized_queue = data_box.individual_processing_queue(&mut ctx, false);
        assert!(localized_queue.is_some());
        assert_ne!(localized_queue, prev_queue);
        assert_eq!(data_box.loc_indi_process_queue, localized_queue);
        assert_eq!(data_box.use_indi_process_queue, localized_queue);

        let localized = ctx.indi_proc_queue(localized_queue);
        assert_eq!(localized.indi_pro_des_count, 1);
        assert_eq!(localized.indi_des_priority_hash.get(&17), Some(&priority));
        assert!(
            !localized.has_max_indi_priority,
            "Konclude initProcessingQueue copies queue entries but resets cached max priority"
        );
        assert_eq!(
            localized.max_indi_priority,
            IndividualProcessNodePriority::default()
        );

        let previous = ctx.indi_proc_queue(prev_queue);
        assert_eq!(previous.indi_pro_des_count, 1);
        assert_eq!(previous.indi_des_priority_hash.get(&17), Some(&priority));
        assert!(previous.has_max_indi_priority);
    }

    #[test]
    fn db2_id_getters_return_current_value_and_increment_only_when_requested() {
        let mut data_box = ProcessingDataBox::new();

        data_box.set_first_possible_individual_node_id(41);
        assert_eq!(data_box.next_individual_node_id(false), 41);
        assert_eq!(data_box.next_individual_node_id(true), 41);
        assert_eq!(data_box.next_individual_node_id(false), 42);

        data_box.next_propagation_id = 7;
        assert_eq!(data_box.next_binding_propagation_id(false), 7);
        assert_eq!(data_box.next_binding_propagation_id(true), 7);
        assert_eq!(data_box.next_binding_propagation_id(false), 8);

        data_box.next_variable_id = 11;
        assert_eq!(data_box.next_variable_binding_path_id(false), 11);
        assert_eq!(data_box.next_variable_binding_path_id(true), 11);
        assert_eq!(data_box.next_variable_binding_path_id(false), 12);

        data_box.next_rep_variable_id = 13;
        assert_eq!(
            data_box.next_representative_variable_binding_path_id(false),
            13
        );
        assert_eq!(
            data_box.next_representative_variable_binding_path_id(true),
            13
        );
        assert_eq!(
            data_box.next_representative_variable_binding_path_id(false),
            14
        );
    }

    #[test]
    fn db2_resolved_saturation_successor_extension_id_initializes_from_vector_abox_and_triples() {
        let mut data_box = ProcessingDataBox::new();
        data_box.next_sat_res_succ_ext_individual_node_id = -1;
        data_box
            .individual_saturation_process_node_vector(true)
            .expect("create=true yields CIndividualSaturationProcessNodeVector")
            .set_data(4, Id::new(0));

        assert_eq!(
            data_box.next_saturation_resolved_successor_extension_individual_node_id_resolved(
                7,
                Some(9),
                false
            ),
            9
        );
        assert_eq!(
            data_box.next_saturation_resolved_successor_extension_individual_node_id_resolved(
                1,
                Some(2),
                true
            ),
            9
        );
        assert_eq!(
            data_box.next_saturation_resolved_successor_extension_individual_node_id_resolved(
                100,
                Some(101),
                false
            ),
            10
        );
    }
}
