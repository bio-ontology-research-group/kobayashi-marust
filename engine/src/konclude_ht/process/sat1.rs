//! `process::sat1` (method unit **SAT-1**) — the logic-bearing method bodies of
//! `CIndividualSaturationProcessNode`
//! (`Source/Reasoner/Kernel/Process/CIndividualSaturationProcessNode.cpp`,
//! lines 35–700).
//!
//! Faithful, function-by-function port. The struct + `new`/`Default` + the
//! trivial one-line accessors already live in `process::sat_node` (unit SD-4);
//! this file fills the remaining init / lazy-getter / linker-chain / status-flag
//! methods. Konclude pointers become arena `Id`s and `CXLinker`/`CXNegLinker`
//! chains become `Vec`s, per `PORT.md` and the field decisions in `sat_node.rs`.
//!
//! KONCLUDE-PORT-NOTE[api]: legacy no-context compatibility methods keep local
//! fallbacks when the exact arena-threaded operation needs `ProcessContext`; the
//! context-backed companions carry the faithful allocation/copy behavior.

#![allow(dead_code)]

use super::super::model::substrate::{Cint64, Id, NegLink, INVALID};
use super::super::model::{ConceptId, IndividualId, RoleId};
use super::super::saturation::satellites::{
    CriticalPredecessorRoleCardinalityHashId, LinkedDataValueAssertionSaturationDataId,
    LinkedRoleSaturationSuccessorHashId, ReapplyConceptSaturationLabelSet,
    SaturationAtmostSuccessorMergingDataId, SaturationDisjunctCommonConceptExtractionDataId,
    SaturationIndividualNodeAllConceptsExtensionDataId, SaturationIndividualNodeDatatypeDataId,
    SaturationIndividualNodeSuccessorExtensionDataId, SaturationSuccessorRoleAssertionLinkerId,
};
use super::context::ProcessContext;
use super::nominal_conn::{
    SaturationIndividualNodeNominalHandlingDataId, SuccessorConnectedNominalSetId,
};
use super::sat_node::{
    IndividualSaturationProcessNode, IndividualSaturationProcessNodeStatusFlags,
};
use super::sat_queue::CriticalSaturationConceptTypeQueuesId;
use super::stubs::{
    BackwardSaturationPropagationLinkId, ConceptSaturationDescriptorId,
    ConceptSaturationProcessLinkerId, ExtendedConceptReferenceLinkingDataId,
    IndividualSaturationProcessNodeCacheDataId, IndividualSaturationProcessNodeExtensionDataId,
    IndividualSaturationProcessNodeLinker, IndividualSaturationProcessNodeLinkerId,
    IndividualSaturationReferenceLinkingDataId, ReapplyConceptSaturationLabelSetId,
    RoleBackwardSaturationPropagationHashId,
};
use super::SatNodeId;

// ---------------------------------------------------------------------------
// Status-flag helpers (the bit accessors `is*/set*` call through).
// ---------------------------------------------------------------------------

impl IndividualSaturationProcessNodeStatusFlags {
    /// Port of `hasInitializedFlag`.
    fn has_initialized_flag(&self) -> bool {
        self.has_flags_code(Self::INDSATFLAGINITIALIZED, false)
    }
    /// Port of `setInitializedFlag`.
    fn set_initialized_flag(&mut self, value: bool) {
        self.set_flags(Self::INDSATFLAGINITIALIZED, value);
    }
    /// Port of `hasCompletedFlag`.
    fn has_completed_flag(&self) -> bool {
        self.has_flags_code(Self::INDSATFLAGCOMPLETED, false)
    }
    /// Port of `setCompletedFlag`.
    fn set_completed_flag(&mut self, value: bool) {
        self.set_flags(Self::INDSATFLAGCOMPLETED, value);
    }
}

// ---------------------------------------------------------------------------
// CIndividualSaturationProcessNode — SAT-1 method bodies
// ---------------------------------------------------------------------------

impl IndividualSaturationProcessNode {
    /// Port of `initIndividualSaturationProcessNode`.
    pub fn init_individual_saturation_process_node(
        &mut self,
        individual_id: Cint64,
        con_sat_ref_link_data: ExtendedConceptReferenceLinkingDataId,
        ind_sat_ref_link_data: IndividualSaturationReferenceLinkingDataId,
    ) -> &mut Self {
        self.role_back_prop_hash = Id::NONE;
        self.reapply_con_sat_label_set = Id::NONE;
        self.indi_process_linker = Id::NONE;
        self.concept_saturation_process_linker = Id::NONE;
        self.substitute_indi_node = Id::NONE;
        self.copy_indi_node = Id::NONE;
        self.required_back_prop = false;

        self.depending_indi_node_linker.clear();
        self.dep_saturation_indi_node = Id::NONE;
        self.direct_saturation_indi_node = Id::NONE;
        self.non_inverse_connected_indi_node_linker.clear();
        self.multiple_cardinality_ancestor_nodes_linker.clear();

        self.indi_id = individual_id;
        self.init_backward_prop_links = Id::NONE;
        self.reference_indi_node = Id::NONE;
        self.indi_extension_data = Id::NONE;
        self.clashed_con_sat_des_linker = Id::NONE;
        self.indi_completion_linker = Id::NONE;
        self.reference_mode = 0;
        self.concept_saturation_link_ref_data = con_sat_ref_link_data;
        self.individual_saturation_link_ref_data = ind_sat_ref_link_data;
        self.integrated_nominal_indi = Id::NONE;
        self.data_value_applied = false;
        self.cache_data = Id::NONE;
        self.nominal_indi = Id::NONE;
        self.separated_saturation = false;
        self.abox_individual_representation_node = false;
        // KONCLUDE-PORT-NOTE[int-width]: C++ assigns `mMaxAtmostCardinality = false`
        // and `mMaxAtleastCardinality = false` to its `cint64` fields (i.e. 0);
        // ported verbatim as `0`.
        self.max_atmost_cardinality = 0;
        self.max_atleast_cardinality = 0;

        self.nominal_indi_triples_assertions = false;
        self.loaded_nominal_indi_triples_assertions = false;
        self.occurrence_statistics_collecting_required = false;
        self.occurrence_statistics_collected = false;
        self
    }

    /// Port of `getSaturationConceptReferenceLinking`.
    pub fn get_saturation_concept_reference_linking(
        &self,
    ) -> ExtendedConceptReferenceLinkingDataId {
        self.concept_saturation_link_ref_data
    }

    /// Port of `getSaturationIndividualReferenceLinking`.
    pub fn get_saturation_individual_reference_linking(
        &self,
    ) -> IndividualSaturationReferenceLinkingDataId {
        self.individual_saturation_link_ref_data
    }

    /// Port of `initRootIndividualSaturationProcessNode`.
    pub fn init_root_individual_saturation_process_node(&mut self) -> &mut Self {
        self
    }

    /// Port of `initCopingIndividualSaturationProcessNode`.
    pub fn init_coping_individual_saturation_process_node(
        &mut self,
        indi_node: &Self,
        try_flat_label_copy: bool,
    ) -> &mut Self {
        if indi_node.role_back_prop_hash.is_some() {
            // KONCLUDE-PORT-NOTE[api]: the exact arena-backed copy is
            // `ProcessContext::sat_node_init_coping_individual_saturation_process_node`.
            // This compatibility accessor cannot allocate or copy linker chains
            // without the process context.
            let _ = self.get_role_backward_propagation_hash(true);
        }
        if indi_node.reapply_con_sat_label_set.is_some() {
            // KONCLUDE-PORT-NOTE[api]: the exact arena-backed copy is
            // `ProcessContext::copy_reapply_concept_saturation_label_set`.
            // This compatibility accessor cannot mutate the source/target
            // label-set arena entries.
            let _ = self.get_reapply_concept_saturation_label_set(true);
            let _ = try_flat_label_copy;
        }
        // KONCLUDE-PORT-NOTE[api]: the exact arena-backed copy is
        // `ProcessContext::sat_node_init_coping_individual_saturation_process_node`.
        // This compatibility accessor cannot allocate/copy the nominal-handling
        // substructure without the process context.

        self.integrated_nominal_indi = indi_node.integrated_nominal_indi;
        if indi_node.nominal_indi.is_some() {
            self.integrated_nominal_indi = indi_node.nominal_indi;
        }
        if self.nominal_indi.is_some() {
            self.integrated_nominal_indi = self.nominal_indi;
        }
        self.data_value_applied = indi_node.data_value_applied;

        // KONCLUDE-PORT-NOTE[api]: the exact arena-backed datatype-data copy is
        // `ProcessContext::sat_node_init_coping_individual_saturation_process_node`.
        // This compatibility accessor cannot dereference the source node's
        // extension-data arena without the process context.

        // KONCLUDE-PORT-NOTE[api]: the exact arena-backed copy-dependency linker
        // install is `ProcessContext::sat_node_init_coping_individual_saturation_process_node`.
        // This compatibility accessor cannot know this node's arena id or mutate
        // the source node.
        self
    }

    /// Port of `initSubstituitingIndividualSaturationProcessNode`.
    pub fn init_substituiting_individual_saturation_process_node(
        &mut self,
        indi_node: &Self,
    ) -> &mut Self {
        self.direct_status_flags = indi_node.direct_status_flags;
        self.indirect_status_flags = indi_node.indirect_status_flags;
        self
    }

    /// Port of `getReapplyConceptSaturationLabelSet`.
    pub fn get_reapply_concept_saturation_label_set(
        &mut self,
        create: bool,
    ) -> ReapplyConceptSaturationLabelSetId {
        if create && self.reapply_con_sat_label_set.is_none() {
            // KONCLUDE-PORT-NOTE[api]: the arena-owning faithful port is
            // `ProcessContext::sat_node_reapply_concept_saturation_label_set`.
            // This compatibility accessor cannot allocate without the context.
        }
        self.reapply_con_sat_label_set
    }

    /// Port of `getIndividualExtensionData`.
    pub fn get_individual_extension_data(
        &mut self,
        create: bool,
    ) -> IndividualSaturationProcessNodeExtensionDataId {
        if create && self.indi_extension_data.is_none() {
            // KONCLUDE-PORT-NOTE[api]: the arena-owning faithful port is
            // `get_individual_extension_data_in_context`. This compatibility
            // accessor cannot allocate without the context.
        }
        self.indi_extension_data
    }

    /// Context-threaded port of `getIndividualExtensionData`.
    ///
    /// Konclude allocates `CIndividualSaturationProcessNodeExtensionData` from
    /// `mMemAllocMan`, then calls `initIndividualExtensionData(this)`. The Rust
    /// process arena owns that allocation, so callers with only `&mut self` keep
    /// the compatibility read above and exact creation goes through this method.
    pub fn get_individual_extension_data_in_context(
        context: &mut ProcessContext,
        node: SatNodeId,
        create: bool,
    ) -> IndividualSaturationProcessNodeExtensionDataId {
        context.sat_node_individual_extension_data(node, create)
    }

    /// Port of `getDisjunctCommonConceptExtractionData`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: use
    /// `get_disjunct_common_concept_extraction_data_in_context` when the caller
    /// can supply `ProcessContext`; this compatibility method cannot resolve or
    /// allocate the arena-backed extension data by itself.
    pub fn get_disjunct_common_concept_extraction_data(&mut self, create: bool) -> Cint64 {
        if create {
            let _ = self.get_individual_extension_data(true);
            return INVALID;
        }
        if self.indi_extension_data.is_some() {
            return INVALID;
        }
        INVALID
    }

    /// Context-threaded port of `getDisjunctCommonConceptExtractionData`.
    pub fn get_disjunct_common_concept_extraction_data_in_context(
        context: &mut ProcessContext,
        node: SatNodeId,
        create: bool,
    ) -> SaturationDisjunctCommonConceptExtractionDataId {
        context.sat_node_ext_disjunct_common_concept_extraction_data(node, create)
    }

    /// Port of `getRoleBackwardPropagationHash`.
    pub fn get_role_backward_propagation_hash(
        &mut self,
        create: bool,
    ) -> RoleBackwardSaturationPropagationHashId {
        if create && self.role_back_prop_hash.is_none() {
            // KONCLUDE-PORT-NOTE[api]: the arena-owning faithful port is
            // `get_role_backward_propagation_hash_in_context`. This
            // compatibility accessor cannot allocate without the context.
        }
        self.role_back_prop_hash
    }

    /// Context-threaded port of `getRoleBackwardPropagationHash`.
    ///
    /// The direct self method above intentionally keeps the old SAT-1 signature,
    /// but faithful allocation requires the arena-owning `ProcessContext`.
    pub fn get_role_backward_propagation_hash_in_context(
        context: &mut ProcessContext,
        node: SatNodeId,
        create: bool,
    ) -> RoleBackwardSaturationPropagationHashId {
        context.sat_node_role_backward_propagation_hash(node, create)
    }

    /// Port of `getSuccessorConnectedNominalSet`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: `CSuccessorConnectedNominalSet*` is un-ported;
    /// returned as an opaque `Cint64` handle.
    pub fn get_successor_connected_nominal_set(&mut self, create: bool) -> Cint64 {
        let nominal_handling_data = self.get_nominal_handling_data(create);
        if nominal_handling_data != INVALID {
            // KONCLUDE-PORT-NOTE[api]: the typed arena-backed implementation is
            // `get_successor_connected_nominal_set_in_context`.
        }
        INVALID
    }

    /// Context-threaded port of `getSuccessorConnectedNominalSet`.
    pub fn get_successor_connected_nominal_set_in_context(
        context: &mut ProcessContext,
        node: SatNodeId,
        create: bool,
    ) -> SuccessorConnectedNominalSetId {
        context.sat_node_successor_connected_nominal_set(node, create)
    }

    /// Port of `getLinkedDataValueAssertionData`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: use
    /// `get_linked_data_value_assertion_data_in_context` when the context is
    /// available.
    pub fn get_linked_data_value_assertion_data(&mut self, create: bool) -> Cint64 {
        if create {
            let _ = self.get_individual_extension_data(true);
            return INVALID;
        }
        if self.indi_extension_data.is_some() {
            return INVALID;
        }
        INVALID
    }

    /// Context-threaded port of `getLinkedDataValueAssertionData`.
    pub fn get_linked_data_value_assertion_data_in_context(
        context: &mut ProcessContext,
        node: SatNodeId,
        create: bool,
    ) -> LinkedDataValueAssertionSaturationDataId {
        context.sat_node_ext_linked_data_value_assertion_data(node, create)
    }

    /// Port of `getCriticalPredecessorRoleCardinalityHash`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: use
    /// `get_critical_predecessor_role_cardinality_hash_in_context` when the
    /// caller can supply `ProcessContext`; this compatibility method cannot
    /// resolve or allocate the arena-backed extension data by itself.
    pub fn get_critical_predecessor_role_cardinality_hash(&mut self, create: bool) -> Cint64 {
        if create {
            let _ = self.get_individual_extension_data(true);
            return INVALID;
        }
        if self.indi_extension_data.is_some() {
            return INVALID;
        }
        INVALID
    }

    /// Context-threaded port of `getCriticalPredecessorRoleCardinalityHash`.
    pub fn get_critical_predecessor_role_cardinality_hash_in_context(
        context: &mut ProcessContext,
        node: SatNodeId,
        create: bool,
    ) -> CriticalPredecessorRoleCardinalityHashId {
        context.sat_node_ext_critical_predecessor_role_cardinality_hash(node, create)
    }

    /// Port of `getLinkedRoleSuccessorHash`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: opaque `Cint64` handle for the un-ported
    /// `CLinkedRoleSaturationSuccessorHash*`.
    pub fn get_linked_role_successor_hash(&mut self, create: bool) -> Cint64 {
        if create {
            // KONCLUDE-PORT-NOTE[api]: the typed arena-backed implementation is
            // `get_linked_role_successor_hash_in_context`.
            let _ = self.get_individual_extension_data(true);
            return INVALID;
        }
        if self.indi_extension_data.is_some() {
            // KONCLUDE-PORT-NOTE[api]: use
            // `get_linked_role_successor_hash_in_context` when the context is
            // available.
            return INVALID;
        }
        INVALID
    }

    /// Context-threaded port of `getLinkedRoleSuccessorHash`.
    pub fn get_linked_role_successor_hash_in_context(
        context: &mut ProcessContext,
        node: SatNodeId,
        create: bool,
    ) -> LinkedRoleSaturationSuccessorHashId {
        context.sat_node_ext_linked_role_successor_hash(node, create)
    }

    /// Port of `getCriticalConceptTypeQueues`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: use
    /// `get_critical_concept_type_queues_in_context` when the context is
    /// available.
    pub fn get_critical_concept_type_queues(&mut self, create: bool) -> Cint64 {
        if create {
            let _ = self.get_individual_extension_data(true);
            return INVALID;
        }
        if self.indi_extension_data.is_some() {
            return INVALID;
        }
        INVALID
    }

    /// Context-threaded port of `getCriticalConceptTypeQueues`.
    pub fn get_critical_concept_type_queues_in_context(
        context: &mut ProcessContext,
        node: SatNodeId,
        create: bool,
    ) -> CriticalSaturationConceptTypeQueuesId {
        context.sat_node_ext_critical_concept_type_queues(node, create)
    }

    /// Port of `getSuccessorExtensionData`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: use `get_successor_extension_data_in_context`
    /// when the caller can supply `ProcessContext`; this compatibility method
    /// cannot resolve or allocate the arena-backed extension data by itself.
    pub fn get_successor_extension_data(&mut self, create: bool) -> Cint64 {
        if create {
            let _ = self.get_individual_extension_data(true);
            return INVALID;
        }
        if self.indi_extension_data.is_some() {
            return INVALID;
        }
        INVALID
    }

    /// Context-threaded port of `getSuccessorExtensionData`.
    pub fn get_successor_extension_data_in_context(
        context: &mut ProcessContext,
        node: SatNodeId,
        create: bool,
    ) -> SaturationIndividualNodeSuccessorExtensionDataId {
        context.sat_node_ext_successor_extension_data(node, create)
    }

    /// Port of `getNominalHandlingData`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: opaque `Cint64` handle for the un-ported
    /// `CSaturationIndividualNodeNominalHandlingData*`.
    pub fn get_nominal_handling_data(&mut self, create: bool) -> Cint64 {
        if create {
            // KONCLUDE-PORT-NOTE[api]: the typed arena-backed implementation is
            // `get_nominal_handling_data_in_context`.
            let _ = self.get_individual_extension_data(true);
            return INVALID;
        }
        if self.indi_extension_data.is_some() {
            // KONCLUDE-PORT-NOTE[api]: use
            // `get_nominal_handling_data_in_context` when the context is
            // available.
            return INVALID;
        }
        INVALID
    }

    /// Context-threaded port of `getNominalHandlingData`.
    pub fn get_nominal_handling_data_in_context(
        context: &mut ProcessContext,
        node: SatNodeId,
        create: bool,
    ) -> SaturationIndividualNodeNominalHandlingDataId {
        context.sat_node_nominal_handling_data(node, create)
    }

    /// Port of `getAppliedDatatypeData`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: use `get_applied_datatype_data_in_context` when
    /// the context is available.
    pub fn get_applied_datatype_data(&mut self, create: bool) -> Cint64 {
        if create {
            let _ = self.get_individual_extension_data(true);
            return INVALID;
        }
        if self.indi_extension_data.is_some() {
            return INVALID;
        }
        INVALID
    }

    /// Context-threaded port of `getAppliedDatatypeData`.
    pub fn get_applied_datatype_data_in_context(
        context: &mut ProcessContext,
        node: SatNodeId,
        create: bool,
    ) -> SaturationIndividualNodeDatatypeDataId {
        context.sat_node_ext_applied_datatype_data(node, create)
    }

    /// Port of `getATMOSTSuccessorMergingData`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: use
    /// `get_atmost_successor_merging_data_in_context` when the caller can supply
    /// `ProcessContext`; this compatibility method cannot resolve or allocate
    /// the arena-backed extension data by itself.
    pub fn get_atmost_successor_merging_data(&mut self, create: bool) -> Cint64 {
        if create {
            let _ = self.get_individual_extension_data(true);
            return INVALID;
        }
        if self.indi_extension_data.is_some() {
            return INVALID;
        }
        INVALID
    }

    /// Context-threaded port of `getATMOSTSuccessorMergingData`.
    pub fn get_atmost_successor_merging_data_in_context(
        context: &mut ProcessContext,
        node: SatNodeId,
        create: bool,
    ) -> SaturationAtmostSuccessorMergingDataId {
        context.sat_node_ext_atmost_successor_merging_data(node, create)
    }

    /// Port of `getIndividualSaturationProcessNodeLinker`.
    pub fn get_individual_saturation_process_node_linker(
        &self,
    ) -> IndividualSaturationProcessNodeLinkerId {
        self.indi_process_linker
    }

    /// Port of `setIndividualSaturationProcessNodeLinker`.
    pub fn set_individual_saturation_process_node_linker(
        &mut self,
        process_node_linker: IndividualSaturationProcessNodeLinkerId,
    ) -> &mut Self {
        self.indi_process_linker = process_node_linker;
        self
    }

    /// Port of `getConceptSaturationProcessLinker`.
    pub fn get_concept_saturation_process_linker(&self) -> ConceptSaturationProcessLinkerId {
        self.concept_saturation_process_linker
    }

    /// Port of `takeConceptSaturationProcessLinker`.
    pub fn take_concept_saturation_process_linker(
        &mut self,
        process_context: &ProcessContext,
    ) -> ConceptSaturationProcessLinkerId {
        let con_proc_linker = self.concept_saturation_process_linker;
        if self.concept_saturation_process_linker.is_some() {
            self.concept_saturation_process_linker = process_context
                .con_sat_proc_linker(con_proc_linker)
                .get_next();
        }
        con_proc_linker
    }

    /// Port of `setConceptSaturationProcessLinker`.
    pub fn set_concept_saturation_process_linker(
        &mut self,
        con_process_linker: ConceptSaturationProcessLinkerId,
    ) -> &mut Self {
        self.concept_saturation_process_linker = con_process_linker;
        self
    }

    /// Port of `addConceptSaturationProcessLinker`.
    pub fn add_concept_saturation_process_linker(
        &mut self,
        process_context: &mut ProcessContext,
        con_process_linker: ConceptSaturationProcessLinkerId,
    ) -> &mut Self {
        self.concept_saturation_process_linker = process_context
            .append_concept_saturation_process_linker_chain(
                con_process_linker,
                self.concept_saturation_process_linker,
            );
        self
    }

    /// Port of `clearConceptSaturationProcessLinker`.
    pub fn clear_concept_saturation_process_linker(&mut self) -> &mut Self {
        self.concept_saturation_process_linker = Id::NONE;
        self
    }

    /// Port of `getRoleAssertionLinker`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: use `get_role_assertion_linker_in_context` when
    /// the caller can supply `ProcessContext`; this compatibility method cannot
    /// resolve the arena-backed extension-data pointer by itself.
    pub fn get_role_assertion_linker(&self) -> Cint64 {
        if self.indi_extension_data.is_some() {
            return INVALID;
        }
        INVALID
    }

    /// Context-threaded port of `getRoleAssertionLinker`.
    pub fn get_role_assertion_linker_in_context(
        context: &ProcessContext,
        node: SatNodeId,
    ) -> SaturationSuccessorRoleAssertionLinkerId {
        context.sat_node_ext_role_assertion_linker(node)
    }

    /// Port of `addRoleAssertionLinker`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: use `add_role_assertion_linker_in_context` when
    /// the caller can supply `ProcessContext`; this compatibility method cannot
    /// mutate the arena-backed extension data by itself.
    pub fn add_role_assertion_linker(&mut self, role_assertion_linker: Cint64) -> &mut Self {
        let _ = self.get_individual_extension_data(true);
        let _ = role_assertion_linker;
        self
    }

    /// Context-threaded port of `addRoleAssertionLinker`.
    pub fn add_role_assertion_linker_in_context(
        context: &mut ProcessContext,
        node: SatNodeId,
        role_assertion_linker: SaturationSuccessorRoleAssertionLinkerId,
    ) -> SatNodeId {
        context.sat_node_ext_add_role_assertion_linker(node, role_assertion_linker);
        node
    }

    /// Port of `addRoleAssertion`.
    pub fn add_role_assertion(
        &mut self,
        destination_node: SatNodeId,
        role: RoleId,
        role_negation: bool,
    ) -> &mut Self {
        let _ = self.get_individual_extension_data(true);
        let _ = (destination_node, role, role_negation);
        self
    }

    /// Context-threaded port of `addRoleAssertion`.
    pub fn add_role_assertion_in_context(
        context: &mut ProcessContext,
        node: SatNodeId,
        destination_node: SatNodeId,
        role: RoleId,
        role_negation: bool,
    ) -> SatNodeId {
        context.sat_node_ext_add_role_assertion(node, destination_node, role, role_negation);
        node
    }

    /// Port of `hasSubstituteIndividualNode`.
    pub fn has_substitute_individual_node(&self) -> bool {
        self.substitute_indi_node.is_some()
    }

    /// Port of `getSubstituteIndividualNode`.
    pub fn get_substitute_individual_node(&self) -> SatNodeId {
        self.substitute_indi_node
    }

    /// Port of `setSubstituteIndividualNode`.
    pub fn set_substitute_individual_node(&mut self, indi_node: SatNodeId) -> &mut Self {
        self.substitute_indi_node = indi_node;
        self
    }

    /// Port of `hasCopyIndividualNode`.
    pub fn has_copy_individual_node(&self) -> bool {
        self.copy_indi_node.is_some()
    }

    /// Port of `getCopyIndividualNode`.
    pub fn get_copy_individual_node(&self) -> SatNodeId {
        self.copy_indi_node
    }

    /// Port of `setCopyIndividualNode`.
    pub fn set_copy_individual_node(&mut self, indi_node: SatNodeId) -> &mut Self {
        self.copy_indi_node = indi_node;
        self
    }

    /// Port of `hasCopyDependingIndividualNodeLinker`.
    pub fn has_copy_depending_individual_node_linker(&self) -> bool {
        !self.depending_indi_node_linker.is_empty()
    }

    /// Port of `getCopyDependingIndividualNodeLinker`.
    pub fn get_copy_depending_individual_node_linker(&self) -> &[NegLink<SatNodeId>] {
        &self.depending_indi_node_linker
    }

    /// Port of `setCopyDependingIndividualNodeLinker`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: the C++ replaces the `CXNegLinker` chain head;
    /// the Vec model replaces the whole list.
    pub fn set_copy_depending_individual_node_linker(
        &mut self,
        indi_linker: Vec<NegLink<SatNodeId>>,
    ) -> &mut Self {
        self.depending_indi_node_linker = indi_linker;
        self
    }

    /// Port of `addCopyDependingIndividualNodeLinker`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: C++ prepends a `CXNegLinker` node onto the
    /// chain; modelled as pushing one `NegLink` entry (these node linkers are used
    /// as an unordered set).
    pub fn add_copy_depending_individual_node_linker(
        &mut self,
        indi_link: NegLink<SatNodeId>,
    ) -> &mut Self {
        if indi_link.target.is_some() {
            self.depending_indi_node_linker.push(indi_link);
        }
        self
    }

    /// Port of `hasDependingSaturationIndividualNode`.
    pub fn has_depending_saturation_individual_node(&self) -> bool {
        self.dep_saturation_indi_node.is_some()
    }

    /// Port of `getDependingSaturationIndividualNode`.
    pub fn get_depending_saturation_individual_node(&self) -> SatNodeId {
        self.dep_saturation_indi_node
    }

    /// Port of `setDependingSaturationIndividualNode`.
    pub fn set_depending_saturation_individual_node(&mut self, indi_node: SatNodeId) -> &mut Self {
        self.dep_saturation_indi_node = indi_node;
        self
    }

    /// Port of `hasDirectSaturationIndividualNode`.
    pub fn has_direct_saturation_individual_node(&self) -> bool {
        self.direct_saturation_indi_node.is_some()
    }

    /// Port of `getDirectSaturationIndividualNode`.
    pub fn get_direct_saturation_individual_node(&self) -> SatNodeId {
        self.direct_saturation_indi_node
    }

    /// Port of `setDirectSaturationIndividualNode`.
    pub fn set_direct_saturation_individual_node(&mut self, indi_node: SatNodeId) -> &mut Self {
        self.direct_saturation_indi_node = indi_node;
        self
    }

    /// Port of `isInitialized`.
    pub fn is_initialized(&self) -> bool {
        self.direct_status_flags.has_initialized_flag()
    }

    /// Port of `setInitialized`.
    pub fn set_initialized(&mut self, initialized: bool) -> &mut Self {
        self.direct_status_flags.set_initialized_flag(initialized);
        self.indirect_status_flags.set_initialized_flag(initialized);
        self
    }

    /// Port of `isCompleted`.
    pub fn is_completed(&self) -> bool {
        self.direct_status_flags.has_completed_flag()
    }

    /// Port of `setCompleted`.
    pub fn set_completed(&mut self, completed: bool) -> &mut Self {
        self.direct_status_flags.set_completed_flag(completed);
        self.indirect_status_flags.set_completed_flag(completed);
        self
    }

    /// Port of `getInitializingBackwardPropagationLinks`.
    pub fn get_initializing_backward_propagation_links(
        &self,
    ) -> BackwardSaturationPropagationLinkId {
        self.init_backward_prop_links
    }

    /// Port of `setInitializingBackwardPropagationLinks`.
    pub fn set_initializing_backward_propagation_links(
        &mut self,
        backward_prop_links: BackwardSaturationPropagationLinkId,
    ) -> &mut Self {
        self.init_backward_prop_links = backward_prop_links;
        self
    }

    /// Port of `addInitializingBackwardPropagationLinks`.
    pub fn add_initializing_backward_propagation_links(
        &mut self,
        process_context: &mut ProcessContext,
        backward_prop_links: BackwardSaturationPropagationLinkId,
    ) -> &mut Self {
        if backward_prop_links.is_some() {
            self.init_backward_prop_links = process_context
                .append_backward_saturation_propagation_link_chain(
                    backward_prop_links,
                    self.init_backward_prop_links,
                );
        }
        self
    }

    /// Port of `getReferenceIndividualSaturationProcessNode`.
    pub fn get_reference_individual_saturation_process_node(&self) -> SatNodeId {
        self.reference_indi_node
    }

    /// Port of `setReferenceIndividualSaturationProcessNode`.
    pub fn set_reference_individual_saturation_process_node(
        &mut self,
        ref_node: SatNodeId,
    ) -> &mut Self {
        self.reference_indi_node = ref_node;
        self
    }

    /// Port of `getDirectStatusFlags`.
    pub fn get_direct_status_flags(&mut self) -> &mut IndividualSaturationProcessNodeStatusFlags {
        &mut self.direct_status_flags
    }

    /// Port of `getIndirectStatusFlags`.
    pub fn get_indirect_status_flags(&mut self) -> &mut IndividualSaturationProcessNodeStatusFlags {
        &mut self.indirect_status_flags
    }

    /// Port of `hasClashedConceptSaturationDescriptorLinker`.
    pub fn has_clashed_concept_saturation_descriptor_linker(&self) -> bool {
        self.clashed_con_sat_des_linker.is_some()
    }

    /// Port of `getClashedConceptSaturationDescriptorLinker`.
    pub fn get_clashed_concept_saturation_descriptor_linker(
        &self,
    ) -> ConceptSaturationDescriptorId {
        self.clashed_con_sat_des_linker
    }

    /// Port of `addClashedConceptSaturationDescriptorLinker`.
    pub fn add_clashed_concept_saturation_descriptor_linker(
        &mut self,
        process_context: &mut ProcessContext,
        clash_con_sat_des: ConceptSaturationDescriptorId,
    ) -> &mut Self {
        self.clashed_con_sat_des_linker = process_context
            .append_concept_saturation_descriptor_chain(
                clash_con_sat_des,
                self.clashed_con_sat_des_linker,
            );
        self
    }

    /// Port of `hasNonInverseConnectedIndividualNodeLinker`.
    pub fn has_non_inverse_connected_individual_node_linker(&self) -> bool {
        !self.non_inverse_connected_indi_node_linker.is_empty()
    }

    /// Port of `getNonInverseConnectedIndividualNodeLinker`.
    pub fn get_non_inverse_connected_individual_node_linker(&self) -> &[SatNodeId] {
        &self.non_inverse_connected_indi_node_linker
    }

    /// Port of `setNonInverseConnectedIndividualNodeLinker`.
    pub fn set_non_inverse_connected_individual_node_linker(
        &mut self,
        indi_linker: Vec<SatNodeId>,
    ) -> &mut Self {
        self.non_inverse_connected_indi_node_linker = indi_linker;
        self
    }

    /// Port of `addNonInverseConnectedIndividualNodeLinker`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: C++ prepends a `CXLinker` node; modelled as
    /// pushing the connected node id.
    pub fn add_non_inverse_connected_individual_node_linker(
        &mut self,
        indi_link: SatNodeId,
    ) -> &mut Self {
        if indi_link.is_some() {
            self.non_inverse_connected_indi_node_linker.push(indi_link);
        }
        self
    }

    /// Port of `hasNominalIntegrated`.
    pub fn has_nominal_integrated(&self) -> bool {
        self.integrated_nominal_indi.is_some()
    }

    /// Port of `setIntegratedNominal`.
    pub fn set_integrated_nominal(&mut self, nominal_indi: IndividualId) -> &mut Self {
        self.integrated_nominal_indi = nominal_indi;
        self
    }

    /// Port of `getIntegratedNominalIndividual`.
    pub fn get_integrated_nominal_individual(&self) -> IndividualId {
        self.integrated_nominal_indi
    }

    /// Port of `hasDataValueApplied`.
    pub fn has_data_value_applied(&self) -> bool {
        self.data_value_applied
    }

    /// Port of `setDataValueApplied`.
    pub fn set_data_value_applied(&mut self, data_applied: bool) -> &mut Self {
        self.data_value_applied = data_applied;
        self
    }

    /// Port of `hasMultipleCardinalityAncestorNodesLinker`.
    pub fn has_multiple_cardinality_ancestor_nodes_linker(&self) -> bool {
        !self.multiple_cardinality_ancestor_nodes_linker.is_empty()
    }

    /// Port of `getMultipleCardinalityAncestorNodesLinker`.
    pub fn get_multiple_cardinality_ancestor_nodes_linker(&self) -> &[SatNodeId] {
        &self.multiple_cardinality_ancestor_nodes_linker
    }

    /// Port of `setMultipleCardinalityAncestorNodesLinker`.
    pub fn set_multiple_cardinality_ancestor_nodes_linker(
        &mut self,
        indi_linker: Vec<SatNodeId>,
    ) -> &mut Self {
        self.multiple_cardinality_ancestor_nodes_linker = indi_linker;
        self
    }

    /// Port of `addMultipleCardinalityAncestorNodesLinker`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: C++ prepends a `CXLinker` node; modelled as
    /// pushing the ancestor node id.
    pub fn add_multiple_cardinality_ancestor_nodes_linker(
        &mut self,
        indi_link: SatNodeId,
    ) -> &mut Self {
        if indi_link.is_some() {
            self.multiple_cardinality_ancestor_nodes_linker
                .push(indi_link);
        }
        self
    }

    /// Port of `getNominalIndividual`.
    pub fn get_nominal_individual(&self) -> IndividualId {
        self.nominal_indi
    }

    /// Port of `setNominalIndividual`.
    pub fn set_nominal_individual(&mut self, nominal_indi: IndividualId) -> &mut Self {
        self.nominal_indi = nominal_indi;
        self.integrated_nominal_indi = self.nominal_indi;
        self
    }

    /// Port of `setIndividualSaturationCompletionNodeLinker`.
    pub fn set_individual_saturation_completion_node_linker(
        &mut self,
        process_node_linker: IndividualSaturationProcessNodeLinkerId,
    ) -> &mut Self {
        self.indi_completion_linker = process_node_linker;
        self
    }

    /// Port of `getCacheExpansionData`.
    pub fn get_cache_expansion_data(&self) -> IndividualSaturationProcessNodeCacheDataId {
        self.cache_data
    }

    /// Port of `setCacheExpansionData`.
    pub fn set_cache_expansion_data(
        &mut self,
        cache_data: IndividualSaturationProcessNodeCacheDataId,
    ) -> &mut Self {
        self.cache_data = cache_data;
        self
    }

    /// Port of `isABoxIndividualRepresentationNode`.
    pub fn is_abox_individual_representation_node(&self) -> bool {
        self.abox_individual_representation_node
    }

    /// Port of `setABoxIndividualRepresentationNode`.
    pub fn set_abox_individual_representation_node(
        &mut self,
        abox_individual_representation_node: bool,
    ) -> &mut Self {
        self.abox_individual_representation_node = abox_individual_representation_node;
        self
    }

    /// Port of `addMaxAtleastCardinalityCandidate`.
    pub fn add_max_atleast_cardinality_candidate(&mut self, atleast_cardinality: Cint64) -> bool {
        if atleast_cardinality > self.max_atleast_cardinality {
            self.max_atleast_cardinality = atleast_cardinality;
            return true;
        }
        false
    }

    /// Port of `addMaxAtmostCardinalityCandidate`.
    pub fn add_max_atmost_cardinality_candidate(&mut self, atmost_cardinality: Cint64) -> bool {
        if atmost_cardinality > self.max_atmost_cardinality {
            self.max_atmost_cardinality = atmost_cardinality;
            return true;
        }
        false
    }

    /// Port of `hasNominalIndividualTriplesAssertions`.
    pub fn has_nominal_individual_triples_assertions(&self) -> bool {
        self.nominal_indi_triples_assertions
    }

    /// Port of `setNominalIndividualTriplesAssertions`.
    pub fn set_nominal_individual_triples_assertions(
        &mut self,
        has_nominal_assertions: bool,
    ) -> &mut Self {
        self.nominal_indi_triples_assertions = has_nominal_assertions;
        self
    }

    /// Port of `areNominalIndividualTriplesAssertionsLoaded`.
    pub fn are_nominal_individual_triples_assertions_loaded(&self) -> bool {
        self.loaded_nominal_indi_triples_assertions
    }

    /// Port of `setNominalIndividualTriplesAssertionsLoaded`.
    pub fn set_nominal_individual_triples_assertions_loaded(&mut self, loaded: bool) -> &mut Self {
        self.loaded_nominal_indi_triples_assertions = loaded;
        self
    }

    /// Port of `isOccurrenceStatisticsCollectingRequired`.
    pub fn is_occurrence_statistics_collecting_required(&self) -> bool {
        self.occurrence_statistics_collecting_required
    }

    /// Port of `setOccurrenceStatisticsCollectingRequired`.
    pub fn set_occurrence_statistics_collecting_required(
        &mut self,
        collecting_required: bool,
    ) -> &mut Self {
        self.occurrence_statistics_collecting_required = collecting_required;
        self
    }

    /// Port of `isOccurrenceStatisticsCollected`.
    pub fn is_occurrence_statistics_collected(&self) -> bool {
        self.occurrence_statistics_collected
    }

    /// Port of `setOccurrenceStatisticsCollected`.
    pub fn set_occurrence_statistics_collected(&mut self, collected: bool) -> &mut Self {
        self.occurrence_statistics_collected = collected;
        self
    }
}

impl ProcessContext {
    /// Context-threaded port of
    /// `CIndividualSaturationProcessNode::getReapplyConceptSaturationLabelSet`.
    pub fn sat_node_reapply_concept_saturation_label_set(
        &mut self,
        node: SatNodeId,
        create: bool,
    ) -> ReapplyConceptSaturationLabelSetId {
        if node.is_none() {
            return ReapplyConceptSaturationLabelSetId::NONE;
        }
        if create && self.sat_node(node).reapply_con_sat_label_set.is_none() {
            let process_context = self.sat_node(node).process_context;
            let mut label_set = ReapplyConceptSaturationLabelSet::new(process_context);
            label_set.init_reapply_concept_saturation_label_set();
            let label_set = self.alloc_reapply_con_sat_label_set(label_set);
            self.sat_node_mut(node).reapply_con_sat_label_set = label_set;
        }
        self.sat_node(node).reapply_con_sat_label_set
    }

    /// Context-threaded port of
    /// `CIndividualSaturationProcessNode::getIndividualSaturationProcessNodeLinker`
    /// followed by `CIndividualSaturationProcessNodeLinker::isProcessingQueued`.
    pub fn sat_node_individual_saturation_process_node_linker_queued(
        &self,
        node: SatNodeId,
    ) -> bool {
        if node.is_none() {
            return false;
        }
        let linker = self.sat_node(node).indi_process_linker;
        linker.is_some()
            && self
                .indi_sat_process_node_linker(linker)
                .is_processing_queued()
    }

    /// Context-threaded port of
    /// `CIndividualSaturationProcessNode::getIndividualSaturationProcessNodeLinker`.
    pub fn sat_node_individual_saturation_process_node_linker(
        &mut self,
        node: SatNodeId,
        create: bool,
    ) -> IndividualSaturationProcessNodeLinkerId {
        if node.is_none() {
            return IndividualSaturationProcessNodeLinkerId::NONE;
        }
        if self.sat_node(node).indi_process_linker.is_none() && create {
            let mut linker = IndividualSaturationProcessNodeLinker::new();
            linker.init_process_node_linker(node, false);
            let linker = self.alloc_indi_sat_process_node_linker(linker);
            self.sat_node_mut(node).indi_process_linker = linker;
        }
        self.sat_node(node).indi_process_linker
    }

    /// Context-threaded port of
    /// `CIndividualSaturationProcessNodeLinker::setProcessingQueued` for a node's
    /// main saturation processing linker.
    pub fn sat_node_set_individual_saturation_process_node_linker_queued(
        &mut self,
        node: SatNodeId,
        processing_queued: bool,
    ) {
        let linker = self.sat_node_individual_saturation_process_node_linker(node, true);
        if linker.is_some() {
            self.indi_sat_process_node_linker_mut(linker)
                .set_processing_queued(processing_queued);
        }
    }

    /// Context-threaded port of
    /// `CIndividualSaturationProcessNode::isIndividualSaturationCompletionNodeLinkerQueued`.
    pub fn sat_node_individual_saturation_completion_node_linker_queued(
        &self,
        node: SatNodeId,
    ) -> bool {
        if node.is_none() {
            return false;
        }
        let linker = self.sat_node(node).indi_completion_linker;
        linker.is_some()
            && self
                .indi_sat_process_node_linker(linker)
                .is_processing_queued()
    }

    /// Context-threaded port of
    /// `CIndividualSaturationProcessNode::getIndividualSaturationCompletionNodeLinker`.
    pub fn sat_node_individual_saturation_completion_node_linker(
        &mut self,
        node: SatNodeId,
        create: bool,
    ) -> IndividualSaturationProcessNodeLinkerId {
        if node.is_none() {
            return IndividualSaturationProcessNodeLinkerId::NONE;
        }
        if self.sat_node(node).indi_completion_linker.is_none() && create {
            let mut linker = IndividualSaturationProcessNodeLinker::new();
            linker.init_process_node_linker(node, false);
            let linker = self.alloc_indi_sat_process_node_linker(linker);
            self.sat_node_mut(node).indi_completion_linker = linker;
        }
        self.sat_node(node).indi_completion_linker
    }

    /// Context-threaded port of
    /// `CIndividualSaturationProcessNodeLinker::setProcessingQueued` for a node's
    /// completion linker.
    pub fn sat_node_set_individual_saturation_completion_node_linker_queued(
        &mut self,
        node: SatNodeId,
        processing_queued: bool,
    ) {
        let linker = self.sat_node_individual_saturation_completion_node_linker(node, true);
        if linker.is_some() {
            self.indi_sat_process_node_linker_mut(linker)
                .set_processing_queued(processing_queued);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::super::model::concept::Concept;
    use super::super::super::model::ontology::OntologyArenas;
    use super::super::super::saturation::satellites::{
        BackwardSaturationPropagationLink, BackwardSaturationPropagationReapplyDescriptor,
        ConceptSaturationDescriptor, ConceptSaturationDescriptorReapplyData,
        ConceptSaturationProcessLinker, CriticalPredecessorRoleCardinalityDataId,
        CriticalPredecessorRoleCardinalityHash, CriticalPredecessorRoleCardinalityHashId,
        DataValueRoleAssertionLinkerId, ImplicationReapplyConceptSaturationDescriptorId,
        LinkedDataValueAssertionSaturationData, LinkedDataValueAssertionSaturationDataId,
        RoleBackwardSaturationPropagationHashData, SaturationAtmostSuccessorMergingDataId,
        SaturationAtmostSuccessorMergingHash, SaturationAtmostSuccessorMergingHashId,
        SaturationDisjunctCommonConceptExtractionDataId, SaturationDisjunctExtractionLinker,
        SaturationDisjunctExtractionLinkerId, SaturationIndividualNodeDatatypeDataId,
        SaturationSuccessorData, SaturationSuccessorRoleAssertionLinker,
        SaturationSuccessorRoleAssertionLinkerId,
    };
    use super::*;

    #[test]
    fn sat1_role_backward_propagation_hash_create_false_preserves_null() {
        let mut ctx = ProcessContext::new();
        let node = ctx.alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));

        let hash = IndividualSaturationProcessNode::get_role_backward_propagation_hash_in_context(
            &mut ctx, node, false,
        );

        assert!(hash.is_none());
        assert_eq!(ctx.sat_node(node).role_back_prop_hash, hash);
    }

    #[test]
    fn sat1_role_backward_propagation_hash_create_allocates_and_initializes() {
        let mut ctx = ProcessContext::new();
        let node = ctx.alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));

        let hash = IndividualSaturationProcessNode::get_role_backward_propagation_hash_in_context(
            &mut ctx, node, true,
        );

        assert!(hash.is_some());
        assert_eq!(ctx.sat_node(node).role_back_prop_hash, hash);
        let hash_ref = ctx.role_backward_sat_prop_hash(hash);
        assert!(hash_ref.role_back_prop_data_hash.is_empty());
        assert!(!hash_ref.self_connected);
    }

    #[test]
    fn sat1_role_backward_propagation_hash_reuses_existing_hash() {
        let mut ctx = ProcessContext::new();
        let node = ctx.alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));

        let first = IndividualSaturationProcessNode::get_role_backward_propagation_hash_in_context(
            &mut ctx, node, true,
        );
        let second = IndividualSaturationProcessNode::get_role_backward_propagation_hash_in_context(
            &mut ctx, node, true,
        );

        assert!(first.is_some());
        assert_eq!(second, first);
        assert_eq!(ctx.sat_node(node).role_back_prop_hash, first);
    }

    #[test]
    fn sat1_coping_node_copies_role_backward_hash_and_successor_nominals() {
        let mut ctx = ProcessContext::new();
        let source = ctx.alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));
        let target = ctx.alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));
        let role = RoleId::new(23);
        let other_role = RoleId::new(29);

        let source_hash = ctx.sat_node_role_backward_propagation_hash(source, true);
        let mut reapply = BackwardSaturationPropagationReapplyDescriptor::new();
        reapply
            .init_backward_propagation_reapply_descriptor(ConceptSaturationDescriptorId::new(101));
        let reapply = ctx.alloc_backward_sat_prop_reapply_desc(reapply);
        ctx.role_backward_sat_prop_hash_mut(source_hash)
            .role_back_prop_data_hash
            .entry(role)
            .or_insert_with(RoleBackwardSaturationPropagationHashData::new)
            .reapply_linker = reapply;

        assert_eq!(
            ctx.sat_node_add_self_connected_backward_propagation_link(source, role, source),
            reapply
        );
        assert!(ctx
            .sat_node_add_backward_propagation_link(source, other_role, source)
            .is_none());
        assert!(ctx.sat_node_add_successor_connected_nominal(source, 7001));
        assert!(ctx.sat_node_add_successor_connected_nominal(source, 7002));
        let source_self_link = ctx
            .role_backward_sat_prop_hash(source_hash)
            .role_back_prop_data_hash
            .get(&role)
            .unwrap()
            .link_linker;
        assert!(source_self_link.is_some());

        ctx.sat_node_init_coping_individual_saturation_process_node(target, source, false);

        let target_hash = ctx.sat_node(target).role_back_prop_hash;
        assert!(target_hash.is_some());
        assert_ne!(target_hash, source_hash);
        assert!(ctx.role_backward_sat_prop_hash(target_hash).self_connected);
        let target_data = ctx
            .role_backward_sat_prop_hash(target_hash)
            .role_back_prop_data_hash
            .get(&role)
            .unwrap();
        assert_eq!(target_data.reapply_linker, reapply);
        assert!(target_data.self_connected);
        let target_self_link = target_data.link_linker;
        assert!(target_self_link.is_some());
        assert_ne!(target_self_link, source_self_link);
        assert_eq!(
            ctx.backward_sat_prop_link(target_self_link)
                .get_source_individual(),
            target
        );
        assert_eq!(
            ctx.backward_sat_prop_link(target_self_link).get_link_role(),
            role
        );
        assert!(ctx
            .backward_sat_prop_link(target_self_link)
            .get_next()
            .is_none());

        let copied_other_data = ctx
            .role_backward_sat_prop_hash(target_hash)
            .role_back_prop_data_hash
            .get(&other_role)
            .unwrap();
        assert!(copied_other_data.link_linker.is_none());
        assert!(!copied_other_data.self_connected);

        let source_nominal_set = ctx.sat_node_successor_connected_nominal_set_existing(source);
        let target_nominal_set = ctx.sat_node_successor_connected_nominal_set_existing(target);
        assert!(source_nominal_set.is_some());
        assert!(target_nominal_set.is_some());
        assert_ne!(source_nominal_set, target_nominal_set);
        assert!(ctx
            .nominal_conn_set(target_nominal_set)
            .has_successor_connected_nominal(7001));
        assert!(ctx
            .nominal_conn_set(target_nominal_set)
            .has_successor_connected_nominal(7002));
        assert_eq!(ctx.nominal_conn_set(target_nominal_set).count(), 2);
        assert!(ctx
            .nominal_conn_set_mut(source_nominal_set)
            .add_successor_connected_nominal(7003));
        assert!(!ctx
            .nominal_conn_set(target_nominal_set)
            .has_successor_connected_nominal(7003));
    }

    #[test]
    fn sat1_coping_context_copies_reapply_concept_saturation_label_set() {
        let mut ctx = ProcessContext::new();
        let source = ctx.alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));
        let target = ctx.alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));

        let source_label_set = ctx.sat_node_reapply_concept_saturation_label_set(source, true);
        {
            let label_set = ctx.reapply_con_sat_label_set_mut(source_label_set);
            label_set.concept_count = 3;
            label_set.totel_count = 5;
            label_set.concept_flags = 7;
            label_set.concept_sat_des_linker = ConceptSaturationDescriptorId::new(11);
            label_set.last_nominal_indep_con_sat_des = ConceptSaturationDescriptorId::new(13);
            label_set.concept_des_dep_hash.insert(
                17,
                ConceptSaturationDescriptorReapplyData {
                    con_sat_des: ConceptSaturationDescriptorId::new(19),
                    imp_reapply_con_sat_des: ImplicationReapplyConceptSaturationDescriptorId::new(
                        23,
                    ),
                },
            );
        }

        ctx.sat_node_init_coping_individual_saturation_process_node(target, source, false);

        let target_label_set = ctx.sat_node(target).reapply_con_sat_label_set;
        assert!(target_label_set.is_some());
        assert_ne!(target_label_set, source_label_set);
        let copied = ctx.reapply_con_sat_label_set(target_label_set);
        assert_eq!(copied.concept_count, 3);
        assert_eq!(copied.totel_count, 5);
        assert_eq!(copied.concept_flags, 7);
        assert_eq!(
            copied.concept_sat_des_linker,
            ConceptSaturationDescriptorId::new(11)
        );
        assert_eq!(
            copied.last_nominal_indep_con_sat_des,
            ConceptSaturationDescriptorId::new(13)
        );
        assert_eq!(
            copied.concept_des_dep_hash.get(&17).unwrap().con_sat_des,
            ConceptSaturationDescriptorId::new(19)
        );
        assert!(!copied.has_additional_concept_des_dep_hash);
    }

    #[test]
    fn sat1_coping_context_flat_copy_moves_source_main_to_additional() {
        let mut ctx = ProcessContext::new();
        let source = ctx.alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));
        let target = ctx.alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));

        let source_label_set = ctx.sat_node_reapply_concept_saturation_label_set(source, true);
        {
            let label_set = ctx.reapply_con_sat_label_set_mut(source_label_set);
            label_set.concept_count = 1;
            label_set.totel_count = 2;
            label_set.concept_des_dep_hash.insert(
                31,
                ConceptSaturationDescriptorReapplyData {
                    con_sat_des: ConceptSaturationDescriptorId::new(37),
                    imp_reapply_con_sat_des: ImplicationReapplyConceptSaturationDescriptorId::NONE,
                },
            );
        }

        ctx.sat_node_init_coping_individual_saturation_process_node(target, source, true);

        let source_after = ctx.reapply_con_sat_label_set(source_label_set);
        assert!(source_after.concept_des_dep_hash.is_empty());
        assert!(source_after.has_additional_concept_des_dep_hash);
        assert_eq!(
            source_after
                .additional_concept_des_dep_hash
                .get(&31)
                .unwrap()
                .con_sat_des,
            ConceptSaturationDescriptorId::new(37)
        );

        let target_label_set = ctx.sat_node(target).reapply_con_sat_label_set;
        let target_after = ctx.reapply_con_sat_label_set(target_label_set);
        assert!(target_after.concept_des_dep_hash.is_empty());
        assert!(target_after.has_additional_concept_des_dep_hash);
        assert!(std::sync::Arc::ptr_eq(
            &source_after.additional_concept_des_dep_hash,
            &target_after.additional_concept_des_dep_hash,
        ));
        assert_eq!(
            target_after
                .additional_concept_des_dep_hash
                .get(&31)
                .unwrap()
                .con_sat_des,
            ConceptSaturationDescriptorId::new(37)
        );
    }

    #[test]
    fn sat1_initialized_and_completed_use_konclude_status_flag_masks() {
        let mut node = IndividualSaturationProcessNode::new(INVALID);

        node.set_initialized(true);
        assert!(node.is_initialized());
        assert_eq!(
            node.direct_status_flags.get_flags(),
            IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINITIALIZED
        );
        assert_eq!(
            node.indirect_status_flags.get_flags(),
            IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINITIALIZED
        );

        node.set_completed(true);
        let expected = IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINITIALIZED
            | IndividualSaturationProcessNodeStatusFlags::INDSATFLAGCOMPLETED;
        assert!(node.is_completed());
        assert_eq!(node.direct_status_flags.get_flags(), expected);
        assert_eq!(node.indirect_status_flags.get_flags(), expected);

        node.set_initialized(false);
        assert!(!node.is_initialized());
        assert_eq!(
            node.direct_status_flags.get_flags(),
            IndividualSaturationProcessNodeStatusFlags::INDSATFLAGCOMPLETED
        );
        assert_eq!(
            node.indirect_status_flags.get_flags(),
            IndividualSaturationProcessNodeStatusFlags::INDSATFLAGCOMPLETED
        );
    }

    #[test]
    fn sat1_insufficient_and_clashed_use_konclude_status_flag_masks() {
        let mut flags = IndividualSaturationProcessNodeStatusFlags::default();

        assert!(!flags.has_insufficient_flag());
        assert!(!flags.has_clashed_flag());
        assert_eq!(
            IndividualSaturationProcessNodeStatusFlags::INDSATFLAGCLASHED,
            0x0001
        );
        assert_eq!(
            IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT,
            0x0004
        );

        flags.add_flags_code(IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT);
        assert!(flags.has_insufficient_flag());
        assert!(!flags.has_clashed_flag());

        flags.set_flags(
            IndividualSaturationProcessNodeStatusFlags::INDSATFLAGCLASHED,
            true,
        );
        assert!(flags.has_clashed_flag());
        assert!(flags.has_flags_code(
            IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT
                | IndividualSaturationProcessNodeStatusFlags::INDSATFLAGCLASHED,
            true,
        ));

        flags.clear_flags(IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT);
        assert!(!flags.has_insufficient_flag());
        assert!(flags.has_clashed_flag());
    }

    #[test]
    fn sat1_individual_extension_data_context_allocates_and_reuses() {
        let mut ctx = ProcessContext::new();
        let node = ctx.alloc_sat_node(IndividualSaturationProcessNode::new(777));

        let missing = IndividualSaturationProcessNode::get_individual_extension_data_in_context(
            &mut ctx, node, false,
        );
        assert_eq!(
            missing,
            IndividualSaturationProcessNodeExtensionDataId::NONE
        );
        assert_eq!(ctx.indi_sat_node_ext_data_count(), 0);

        let ext = IndividualSaturationProcessNode::get_individual_extension_data_in_context(
            &mut ctx, node, true,
        );
        assert!(ext.is_some());
        assert_eq!(ctx.sat_node(node).indi_extension_data, ext);
        assert_eq!(ctx.indi_sat_node_ext_data_count(), 1);
        assert_eq!(ctx.indi_sat_node_ext_data(ext).indi_node, node);
        assert_eq!(
            ctx.indi_sat_node_ext_data(ext).linked_role_succ_hash,
            LinkedRoleSaturationSuccessorHashId::NONE
        );
        assert_eq!(
            ctx.indi_sat_node_ext_data(ext).successor_extension_data,
            SaturationIndividualNodeSuccessorExtensionDataId::NONE
        );
        assert_eq!(
            ctx.indi_sat_node_ext_data(ext).nominal_handling_data,
            SaturationIndividualNodeNominalHandlingDataId::NONE
        );

        let ext_again = IndividualSaturationProcessNode::get_individual_extension_data_in_context(
            &mut ctx, node, true,
        );
        assert_eq!(ext_again, ext);
        assert_eq!(ctx.indi_sat_node_ext_data_count(), 1);
    }

    #[test]
    fn sat1_successor_extension_data_context_create_false_preserves_null() {
        let mut ctx = ProcessContext::new();
        let node = ctx.alloc_sat_node(IndividualSaturationProcessNode::new(887));

        let missing = IndividualSaturationProcessNode::get_successor_extension_data_in_context(
            &mut ctx, node, false,
        );
        assert_eq!(
            missing,
            SaturationIndividualNodeSuccessorExtensionDataId::NONE
        );
        assert_eq!(ctx.indi_sat_node_ext_data_count(), 0);
        assert_eq!(ctx.sat_indi_node_succ_ext_data_count(), 0);
    }

    #[test]
    fn sat1_successor_extension_data_context_create_allocates_and_initializes() {
        let mut ctx = ProcessContext::new();
        let node = ctx.alloc_sat_node(IndividualSaturationProcessNode::new(889));

        let succ_ext = IndividualSaturationProcessNode::get_successor_extension_data_in_context(
            &mut ctx, node, true,
        );
        assert!(succ_ext.is_some());
        assert_eq!(ctx.indi_sat_node_ext_data_count(), 1);
        assert_eq!(ctx.sat_indi_node_succ_ext_data_count(), 1);

        let ext = ctx.sat_node(node).indi_extension_data;
        assert!(ext.is_some());
        assert_eq!(
            ctx.indi_sat_node_ext_data(ext)
                .get_successor_extension_data(),
            succ_ext
        );

        let data = ctx.sat_indi_node_succ_ext_data(succ_ext);
        assert_eq!(data.indi_process_node, node);
        assert!(!data.is_extension_processing_queued());
        assert!(data.get_extension_resolve_data().is_none());
        assert!(data.get_base_extension_resolve_data().is_none());
        assert!(data.get_ancestor_successor_merge_resolve_data().is_none());
        assert_eq!(
            data.get_all_concepts_extension_data(),
            SaturationIndividualNodeAllConceptsExtensionDataId::NONE
        );
        assert!(data.get_functional_concepts_extension_data().is_none());
    }

    #[test]
    fn sat1_successor_extension_data_context_reuses_existing_data() {
        let mut ctx = ProcessContext::new();
        let node = ctx.alloc_sat_node(IndividualSaturationProcessNode::new(890));

        let succ_ext = IndividualSaturationProcessNode::get_successor_extension_data_in_context(
            &mut ctx, node, true,
        );
        let succ_ext_again =
            IndividualSaturationProcessNode::get_successor_extension_data_in_context(
                &mut ctx, node, true,
            );

        assert_eq!(succ_ext_again, succ_ext);
        assert_eq!(ctx.indi_sat_node_ext_data_count(), 1);
        assert_eq!(ctx.sat_indi_node_succ_ext_data_count(), 1);
    }

    #[test]
    fn sat1_successor_extension_data_setters_and_getters_preserve_values() {
        let mut ctx = ProcessContext::new();
        let node = ctx.alloc_sat_node(IndividualSaturationProcessNode::new(891));
        let succ_ext = IndividualSaturationProcessNode::get_successor_extension_data_in_context(
            &mut ctx, node, true,
        );
        let resolve_data = ctx.alloc_sat_indi_node_ext_resolve_data(Default::default());

        ctx.sat_indi_node_succ_ext_data_mut(succ_ext)
            .set_extension_processing_queued(true)
            .set_extension_resolve_data(resolve_data);
        assert!(ctx
            .sat_indi_node_succ_ext_data(succ_ext)
            .is_extension_processing_queued());
        assert_eq!(
            ctx.sat_indi_node_succ_ext_data(succ_ext)
                .get_extension_resolve_data(),
            resolve_data
        );
        assert_eq!(
            ctx.sat_indi_node_succ_ext_data(succ_ext)
                .get_base_extension_resolve_data(),
            resolve_data
        );

        ctx.sat_indi_node_succ_ext_data_mut(succ_ext)
            .init_extension_data(node);
        assert!(!ctx
            .sat_indi_node_succ_ext_data(succ_ext)
            .is_extension_processing_queued());
        assert!(ctx
            .sat_indi_node_succ_ext_data(succ_ext)
            .get_extension_resolve_data()
            .is_none());
    }

    #[test]
    fn sat1_critical_predecessor_role_cardinality_hash_context_allocates_through_extension_data() {
        let mut ctx = ProcessContext::new();
        let node = ctx.alloc_sat_node(IndividualSaturationProcessNode::new(895));

        let missing =
            IndividualSaturationProcessNode::get_critical_predecessor_role_cardinality_hash_in_context(
                &mut ctx, node, false,
            );
        assert_eq!(missing, CriticalPredecessorRoleCardinalityHashId::NONE);
        assert_eq!(ctx.indi_sat_node_ext_data_count(), 0);
        assert_eq!(ctx.critical_pred_role_card_hash_count(), 0);

        let hash =
            IndividualSaturationProcessNode::get_critical_predecessor_role_cardinality_hash_in_context(
                &mut ctx, node, true,
            );
        assert!(hash.is_some());
        let ext = ctx.sat_node(node).indi_extension_data;
        assert!(ext.is_some());
        assert_eq!(
            ctx.indi_sat_node_ext_data(ext)
                .get_critical_predecessor_role_cardinality_hash(),
            hash
        );
        assert!(ctx
            .critical_pred_role_card_hash(hash)
            .critical_predecessor_role_data_hash
            .is_empty());

        let hash_again =
            IndividualSaturationProcessNode::get_critical_predecessor_role_cardinality_hash_in_context(
                &mut ctx, node, true,
            );
        assert_eq!(hash_again, hash);
        assert_eq!(ctx.critical_pred_role_card_hash_count(), 1);
    }

    #[test]
    fn sat1_critical_predecessor_role_cardinality_add_prepends_and_copy_is_shallow() {
        let mut ctx = ProcessContext::new();
        let node = ctx.alloc_sat_node(IndividualSaturationProcessNode::new(896));
        let hash =
            IndividualSaturationProcessNode::get_critical_predecessor_role_cardinality_hash_in_context(
                &mut ctx, node, true,
            );
        let role = RoleId::new(41);
        let concept_a = ConceptId::new(101);
        let concept_b = ConceptId::new(102);

        assert_eq!(
            ctx.critical_predecessor_role_cardinality_hash_data(hash, role, false),
            CriticalPredecessorRoleCardinalityDataId::NONE
        );
        ctx.critical_predecessor_role_cardinality_hash_add_cardinality(
            hash, role, concept_a, false,
        );
        let data = ctx.critical_predecessor_role_cardinality_hash_data(hash, role, false);
        assert!(data.is_some());
        assert_eq!(ctx.critical_pred_role_card_data_count(), 1);
        assert_eq!(
            ctx.critical_pred_role_card_data(data)
                .get_unproblematic_concept_linker(),
            &[NegLink {
                target: concept_a,
                negated: false
            }]
        );

        ctx.critical_predecessor_role_cardinality_hash_add_cardinality(hash, role, concept_b, true);
        assert_eq!(
            ctx.critical_pred_role_card_data(data)
                .get_unproblematic_concept_linker(),
            &[
                NegLink {
                    target: concept_b,
                    negated: true
                },
                NegLink {
                    target: concept_a,
                    negated: false
                }
            ]
        );

        let mut source = CriticalPredecessorRoleCardinalityHash::new(INVALID);
        source
            .critical_predecessor_role_data_hash
            .insert(role, data);
        let mut target = CriticalPredecessorRoleCardinalityHash::new(INVALID);
        target.copy_critical_predecessor_role_cardinality_hash(&source);
        assert_eq!(
            target.get_critical_predecessor_role_cardinality_data(role),
            source.get_critical_predecessor_role_cardinality_data(role)
        );
    }

    #[test]
    fn sat1_disjunct_common_concept_extraction_data_context_allocates_through_extension_data() {
        let mut ctx = ProcessContext::new();
        let node = ctx.alloc_sat_node(IndividualSaturationProcessNode::new(897));

        let missing =
            IndividualSaturationProcessNode::get_disjunct_common_concept_extraction_data_in_context(
                &mut ctx, node, false,
            );
        assert_eq!(
            missing,
            SaturationDisjunctCommonConceptExtractionDataId::NONE
        );
        assert_eq!(ctx.indi_sat_node_ext_data_count(), 0);
        assert_eq!(ctx.sat_disjunct_common_concept_extraction_data_count(), 0);

        let data =
            IndividualSaturationProcessNode::get_disjunct_common_concept_extraction_data_in_context(
                &mut ctx, node, true,
            );
        assert!(data.is_some());
        let ext = ctx.sat_node(node).indi_extension_data;
        assert!(ext.is_some());
        assert_eq!(
            ctx.indi_sat_node_ext_data(ext)
                .get_disjunct_common_concept_extraction_data(),
            data
        );
        let data_ref = ctx.sat_disjunct_common_concept_extraction_data(data);
        assert!(data_ref
            .get_saturation_disjunct_common_concept_count_hash()
            .get_common_concept_count_hash()
            .is_empty());
        assert_eq!(
            data_ref.get_disjunct_individual_node_extraction_linker(),
            SaturationDisjunctExtractionLinkerId::NONE
        );
        assert_eq!(
            ctx.indi_sat_process_node_linker(data_ref.get_extraction_continue_process_linker())
                .get_processing_individual(),
            node
        );
        assert!(!ctx
            .indi_sat_process_node_linker(data_ref.get_extraction_continue_process_linker())
            .is_processing_queued());

        let data_again =
            IndividualSaturationProcessNode::get_disjunct_common_concept_extraction_data_in_context(
                &mut ctx, node, true,
            );
        assert_eq!(data_again, data);
        assert_eq!(ctx.sat_disjunct_common_concept_extraction_data_count(), 1);
    }

    #[test]
    fn sat1_disjunct_common_concept_count_hash_counts_and_negation_match() {
        let mut onto = OntologyArenas::new();
        let concept = onto.alloc_concept(Concept::new());
        onto.concept_mut(concept).set_concept_tag(7001);

        let mut pos_a = ConceptSaturationDescriptor::new();
        pos_a.init_concept_saturation_descriptor(concept, false);
        let mut pos_b = ConceptSaturationDescriptor::new();
        pos_b.init_concept_saturation_descriptor(concept, false);
        let mut neg = ConceptSaturationDescriptor::new();
        neg.init_concept_saturation_descriptor(concept, true);

        let mut ctx = ProcessContext::new();
        let node = ctx.alloc_sat_node(IndividualSaturationProcessNode::new(898));
        let data =
            IndividualSaturationProcessNode::get_disjunct_common_concept_extraction_data_in_context(
                &mut ctx, node, true,
            );
        let count_hash = ctx
            .sat_disjunct_common_concept_extraction_data_mut(data)
            .get_saturation_disjunct_common_concept_count_hash_mut();
        count_hash.set_disjunct_count(2);

        assert!(!count_hash.inc_common_concept_count_return_max_reached(&pos_a, &onto));
        assert!(count_hash.inc_common_concept_count_return_max_reached(&pos_b, &onto));
        assert!(!count_hash.inc_common_concept_count_return_max_reached(&neg, &onto));

        let entry = count_hash.get_common_concept_count_data_for_concept(concept, &onto);
        assert_eq!(entry.concept_count, 2);
        assert_eq!(entry.concept, concept);
        assert!(!entry.negation);

        count_hash.remove_common_concept_data(&pos_a, &onto);
        assert!(count_hash.get_common_concept_count_hash().is_empty());
    }

    #[test]
    fn sat1_disjunct_extraction_linker_prepends_and_tracks_last_examined() {
        let mut ctx = ProcessContext::new();
        let owner = ctx.alloc_sat_node(IndividualSaturationProcessNode::new(899));
        let disj_a = ctx.alloc_sat_node(IndividualSaturationProcessNode::new(900));
        let disj_b = ctx.alloc_sat_node(IndividualSaturationProcessNode::new(901));
        let data =
            IndividualSaturationProcessNode::get_disjunct_common_concept_extraction_data_in_context(
                &mut ctx, owner, true,
            );

        let con_a = ctx.alloc_con_sat_desc(ConceptSaturationDescriptor::new());
        let con_b = ctx.alloc_con_sat_desc(ConceptSaturationDescriptor::new());
        let mut linker_a = SaturationDisjunctExtractionLinker::new();
        linker_a.init_saturation_disjunct_extraction_linker(disj_a, con_a);
        let linker_a = ctx.alloc_sat_disjunct_extraction_linker(linker_a);
        ctx.sat_disjunct_common_concept_extraction_data_add_linker(data, linker_a);

        assert_eq!(
            ctx.sat_disjunct_common_concept_extraction_data(data)
                .get_disjunct_individual_node_extraction_linker(),
            linker_a
        );
        assert_eq!(
            ctx.sat_disjunct_extraction_linker(linker_a)
                .get_disjunct_individual_saturation_process_node(),
            disj_a
        );
        assert_eq!(
            ctx.sat_disjunct_extraction_linker(linker_a)
                .get_last_examined_concept_saturation_descriptor(),
            con_a
        );
        assert_eq!(
            ctx.sat_disjunct_extraction_linker(linker_a).get_next(),
            SaturationDisjunctExtractionLinkerId::NONE
        );

        let mut linker_b = SaturationDisjunctExtractionLinker::new();
        linker_b.init_saturation_disjunct_extraction_linker(disj_b, con_b);
        let linker_b = ctx.alloc_sat_disjunct_extraction_linker(linker_b);
        ctx.sat_disjunct_common_concept_extraction_data_add_linker(data, linker_b);
        assert_eq!(
            ctx.sat_disjunct_common_concept_extraction_data(data)
                .get_disjunct_individual_node_extraction_linker(),
            linker_b
        );
        assert_eq!(
            ctx.sat_disjunct_extraction_linker(linker_b).get_next(),
            linker_a
        );

        ctx.sat_disjunct_extraction_linker_mut(linker_b)
            .set_last_examined_concept_saturation_descriptor(con_a);
        assert_eq!(
            ctx.sat_disjunct_extraction_linker(linker_b)
                .get_last_examined_concept_saturation_descriptor(),
            con_a
        );
        assert_eq!(ctx.sat_disjunct_extraction_linker_count(), 2);
    }

    #[test]
    fn sat1_atmost_successor_merging_data_context_allocates_through_extension_data() {
        let mut ctx = ProcessContext::new();
        let node = ctx.alloc_sat_node(IndividualSaturationProcessNode::new(902));

        let missing = IndividualSaturationProcessNode::get_atmost_successor_merging_data_in_context(
            &mut ctx, node, false,
        );
        assert_eq!(missing, SaturationAtmostSuccessorMergingDataId::NONE);
        assert_eq!(ctx.indi_sat_node_ext_data_count(), 0);
        assert_eq!(ctx.sat_atmost_successor_merging_data_count(), 0);

        let data = IndividualSaturationProcessNode::get_atmost_successor_merging_data_in_context(
            &mut ctx, node, true,
        );
        assert!(data.is_some());
        let ext = ctx.sat_node(node).indi_extension_data;
        assert!(ext.is_some());
        assert_eq!(
            ctx.indi_sat_node_ext_data(ext)
                .get_atmost_successor_merging_data(),
            data
        );
        let data_ref = ctx.sat_atmost_successor_merging_data(data);
        assert_eq!(
            data_ref
                .get_merging_individual_process_linker()
                .get_processing_individual(),
            node
        );
        assert!(!data_ref.is_merging_processing_queued());
        assert_eq!(
            data_ref.get_merging_concept_linker(),
            ConceptSaturationProcessLinkerId::NONE
        );
        assert_eq!(
            data_ref.get_atmost_concept_merging_data_hash(),
            SaturationAtmostSuccessorMergingHashId::NONE
        );
        assert_eq!(
            data_ref.get_merged_linked_role_saturation_successor_hash(),
            LinkedRoleSaturationSuccessorHashId::NONE
        );
        assert!(data_ref
            .get_remaining_mergeable_cardinality_hash()
            .is_none());
        assert!(data_ref.get_merging_distinct_hash().is_none());
        assert!(data_ref.get_merging_distinct_set().is_none());

        let data_again =
            IndividualSaturationProcessNode::get_atmost_successor_merging_data_in_context(
                &mut ctx, node, true,
            );
        assert_eq!(data_again, data);
        assert_eq!(ctx.sat_atmost_successor_merging_data_count(), 1);
    }

    #[test]
    fn sat1_atmost_successor_merging_hash_creates_defaults_and_copies() {
        let mut ctx = ProcessContext::new();
        let node = ctx.alloc_sat_node(IndividualSaturationProcessNode::new(903));
        let data = IndividualSaturationProcessNode::get_atmost_successor_merging_data_in_context(
            &mut ctx, node, true,
        );
        let con_a = ctx.alloc_con_sat_desc(ConceptSaturationDescriptor::new());
        let con_b = ctx.alloc_con_sat_desc(ConceptSaturationDescriptor::new());

        assert_eq!(
            ctx.sat_atmost_successor_merging_data_concept_merging_hash(data, false),
            SaturationAtmostSuccessorMergingHashId::NONE
        );
        {
            let entry = ctx
                .sat_atmost_successor_merging_data_atmost_concept_merging_data(data, con_a)
                .expect("ATMOST concept merging data should be created");
            assert!(!entry.initialized);
            assert!(!entry.queued);
            assert_eq!(entry.successor_link_merging_linker, Id::NONE);
            assert_eq!(entry.last_successor_node, SatNodeId::NONE);
            assert_eq!(entry.last_successor_creation_role_linker, Vec::new());
            assert_eq!(entry.found_cardinality, 0);
            assert_eq!(entry.mergeable_cardinality, 0);
            assert_eq!(entry.min_cardinality, 0);
            entry.initialized = true;
            entry.found_cardinality = 2;
        }
        let hash = ctx.sat_atmost_successor_merging_data_concept_merging_hash(data, false);
        assert!(hash.is_some());
        assert_eq!(ctx.sat_atmost_successor_merging_hash_count(), 1);
        ctx.sat_atmost_successor_merging_hash_mut(hash)
            .get_atmost_concept_merging_data(con_b)
            .queued = true;

        let mut copy = SaturationAtmostSuccessorMergingHash::new(INVALID);
        copy.init_atmost_concept_descriptor_merging_hash(Some(
            ctx.sat_atmost_successor_merging_hash(hash),
        ));
        assert_eq!(copy.atmost_concept_merging_data_hash.len(), 2);
        assert!(
            copy.atmost_concept_merging_data_hash
                .get(&con_a)
                .unwrap()
                .initialized
        );
        assert!(
            copy.atmost_concept_merging_data_hash
                .get(&con_b)
                .unwrap()
                .queued
        );
    }

    #[test]
    fn sat1_atmost_successor_merging_concept_linker_prepends_and_takes_next() {
        let mut ctx = ProcessContext::new();
        let node = ctx.alloc_sat_node(IndividualSaturationProcessNode::new(904));
        let data = IndividualSaturationProcessNode::get_atmost_successor_merging_data_in_context(
            &mut ctx, node, true,
        );
        let con_a = ctx.alloc_con_sat_desc(ConceptSaturationDescriptor::new());
        let con_b = ctx.alloc_con_sat_desc(ConceptSaturationDescriptor::new());

        ctx.sat_atmost_successor_merging_data_add_merging_processing_concept(data, con_a);
        let first = ctx
            .sat_atmost_successor_merging_data(data)
            .get_merging_concept_linker();
        assert!(first.is_some());
        assert_eq!(
            ctx.con_sat_proc_linker(first)
                .get_concept_saturation_descriptor(),
            con_a
        );
        assert_eq!(
            ctx.con_sat_proc_linker(first).get_next(),
            ConceptSaturationProcessLinkerId::NONE
        );

        ctx.sat_atmost_successor_merging_data_add_merging_processing_concept(data, con_b);
        let second = ctx
            .sat_atmost_successor_merging_data(data)
            .get_merging_concept_linker();
        assert_ne!(second, first);
        assert_eq!(
            ctx.con_sat_proc_linker(second)
                .get_concept_saturation_descriptor(),
            con_b
        );
        assert_eq!(ctx.con_sat_proc_linker(second).get_next(), first);

        let after_take =
            ctx.sat_atmost_successor_merging_data_take_next_merging_concept_linker(data);
        assert_eq!(after_take, first);
        assert_eq!(
            ctx.sat_atmost_successor_merging_data(data)
                .get_merging_concept_linker(),
            first
        );
    }

    #[test]
    fn sat1_atmost_successor_merging_lazily_materializes_helper_hashes() {
        let mut ctx = ProcessContext::new();
        let node = ctx.alloc_sat_node(IndividualSaturationProcessNode::new(905));
        let data = IndividualSaturationProcessNode::get_atmost_successor_merging_data_in_context(
            &mut ctx, node, true,
        );
        let succ_a = ctx.alloc_sat_succ_data(SaturationSuccessorData::new());
        let succ_b = ctx.alloc_sat_succ_data(SaturationSuccessorData::new());

        assert_eq!(
            ctx.sat_atmost_successor_merging_data_merged_linked_role_successor_hash(data, false),
            LinkedRoleSaturationSuccessorHashId::NONE
        );
        let merged_hash =
            ctx.sat_atmost_successor_merging_data_merged_linked_role_successor_hash(data, true);
        assert!(merged_hash.is_some());
        assert!(ctx
            .linked_role_sat_succ_hash(merged_hash)
            .role_succ_data_hash
            .is_empty());
        assert_eq!(ctx.linked_role_sat_succ_hash_count(), 1);

        assert!(ctx
            .sat_atmost_successor_merging_data_remaining_mergeable_cardinality_hash(data, false)
            .is_none());
        ctx.sat_atmost_successor_merging_data_remaining_mergeable_cardinality_hash(data, true)
            .unwrap()
            .insert(succ_a, 3);
        assert_eq!(
            ctx.sat_atmost_successor_merging_data(data)
                .get_remaining_mergeable_cardinality_hash()
                .unwrap()
                .get(&succ_a),
            Some(&3)
        );

        assert!(ctx
            .sat_atmost_successor_merging_data_merging_distinct_hash(data, false)
            .is_none());
        ctx.sat_atmost_successor_merging_data_merging_distinct_hash(data, true)
            .unwrap()
            .insert(succ_a, succ_b);
        assert_eq!(
            ctx.sat_atmost_successor_merging_data(data)
                .get_merging_distinct_hash()
                .unwrap()
                .get(&succ_a),
            Some(&succ_b)
        );

        assert!(ctx
            .sat_atmost_successor_merging_data_merging_distinct_set(data, false)
            .is_none());
        ctx.sat_atmost_successor_merging_data_merging_distinct_set(data, true)
            .unwrap()
            .insert((succ_a, succ_b));
        assert!(ctx
            .sat_atmost_successor_merging_data(data)
            .get_merging_distinct_set()
            .unwrap()
            .contains(&(succ_a, succ_b)));
    }

    #[test]
    fn sat1_linked_role_successor_hash_context_allocates_through_extension_data() {
        let mut ctx = ProcessContext::new();
        let node = ctx.alloc_sat_node(IndividualSaturationProcessNode::new(888));

        let missing = IndividualSaturationProcessNode::get_linked_role_successor_hash_in_context(
            &mut ctx, node, false,
        );
        assert_eq!(missing, LinkedRoleSaturationSuccessorHashId::NONE);
        assert_eq!(ctx.indi_sat_node_ext_data_count(), 0);

        let hash = IndividualSaturationProcessNode::get_linked_role_successor_hash_in_context(
            &mut ctx, node, true,
        );
        assert!(hash.is_some());
        let ext = ctx.sat_node(node).indi_extension_data;
        assert!(ext.is_some());
        assert_eq!(ctx.indi_sat_node_ext_data(ext).linked_role_succ_hash, hash);
        assert!(ctx
            .linked_role_sat_succ_hash(hash)
            .role_succ_data_hash
            .is_empty());

        let hash_again = IndividualSaturationProcessNode::get_linked_role_successor_hash_in_context(
            &mut ctx, node, true,
        );
        assert_eq!(hash_again, hash);
        assert_eq!(ctx.linked_role_sat_succ_hash_count(), 1);
    }

    #[test]
    fn sat1_linked_role_successor_hash_adds_and_deactivates_extension_successors() {
        let mut ctx = ProcessContext::new();
        let node = ctx.alloc_sat_node(IndividualSaturationProcessNode::new(889));
        let succ_node = ctx.alloc_sat_node(IndividualSaturationProcessNode::new(890));
        let role = RoleId::new(31);
        let creation_role = RoleId::new(37);

        let hash = IndividualSaturationProcessNode::get_linked_role_successor_hash_in_context(
            &mut ctx, node, true,
        );
        let succ_data = ctx.linked_role_successor_hash_add_extension_successor(
            hash,
            role,
            succ_node,
            creation_role,
            1,
        );

        assert!(succ_data.is_some());
        assert!(ctx.linked_role_successor_hash_has_active_linked_successor(
            hash, role, succ_node, None, 1
        ));
        let role_succ_data = ctx.linked_role_successor_data(hash, role, false);
        let succ_key = ctx.sat_node(succ_node).get_individual_id();
        assert_eq!(
            ctx.linked_role_sat_succ_data(role_succ_data)
                .succ_node_data_map
                .get(&succ_key)
                .copied(),
            Some(succ_data)
        );
        assert_eq!(
            ctx.sat_succ_data(succ_data).get_successor_individual_node(),
            succ_node
        );
        assert_eq!(ctx.sat_succ_data(succ_data).get_successor_count(), 1);
        assert_eq!(ctx.sat_succ_data(succ_data).get_active_count(), 1);
        assert!(ctx.sat_succ_data(succ_data).extension);
        assert_eq!(
            ctx.sat_succ_data(succ_data).creation_role_linker,
            vec![NegLink {
                target: creation_role,
                negated: false
            }]
        );

        assert!(ctx.linked_role_successor_hash_deactivate_linked_successor(
            hash,
            role,
            succ_node,
            creation_role
        ));
        assert!(!ctx.linked_role_successor_hash_has_active_linked_successor(
            hash, role, succ_node, None, 1
        ));
        assert_eq!(ctx.sat_succ_data(succ_data).get_successor_count(), 0);
        assert_eq!(ctx.sat_succ_data(succ_data).get_active_count(), 0);
        assert_eq!(
            ctx.sat_succ_data(succ_data).creation_role_linker,
            vec![NegLink {
                target: creation_role,
                negated: true
            }]
        );
    }

    #[test]
    fn sat1_linked_data_value_assertion_data_context_allocates_through_extension_data() {
        let mut ctx = ProcessContext::new();
        let node = ctx.alloc_sat_node(IndividualSaturationProcessNode::new(890));

        let missing =
            IndividualSaturationProcessNode::get_linked_data_value_assertion_data_in_context(
                &mut ctx, node, false,
            );
        assert_eq!(missing, LinkedDataValueAssertionSaturationDataId::NONE);
        assert_eq!(ctx.indi_sat_node_ext_data_count(), 0);
        assert_eq!(ctx.linked_data_value_assertion_data_count(), 0);

        let data = IndividualSaturationProcessNode::get_linked_data_value_assertion_data_in_context(
            &mut ctx, node, true,
        );
        assert!(data.is_some());
        let ext = ctx.sat_node(node).indi_extension_data;
        assert!(ext.is_some());
        assert_eq!(
            ctx.indi_sat_node_ext_data(ext)
                .linked_data_value_assertion_data,
            data
        );
        assert_eq!(
            ctx.linked_data_value_assertion_data(data)
                .get_data_value_role_assertion_linker(),
            DataValueRoleAssertionLinkerId::NONE
        );

        let data_again =
            IndividualSaturationProcessNode::get_linked_data_value_assertion_data_in_context(
                &mut ctx, node, true,
            );
        assert_eq!(data_again, data);
        assert_eq!(ctx.linked_data_value_assertion_data_count(), 1);
    }

    #[test]
    fn sat1_data_value_assertion_add_prepends_roles_and_copy_is_shallow() {
        let mut ctx = ProcessContext::new();
        let node = ctx.alloc_sat_node(IndividualSaturationProcessNode::new(891));
        let data = IndividualSaturationProcessNode::get_linked_data_value_assertion_data_in_context(
            &mut ctx, node, true,
        );
        let role_a = RoleId::new(17);
        let role_b = RoleId::new(23);

        ctx.linked_data_value_assertion_data_add_data_value_assertion(data, role_a, 1001);
        let first_head = ctx
            .linked_data_value_assertion_data(data)
            .get_data_value_role_assertion_linker();
        assert_eq!(
            ctx.data_value_role_assertion_linker(first_head).get_role(),
            role_a
        );
        assert_eq!(
            ctx.data_value_role_assertion_linker(first_head).get_next(),
            DataValueRoleAssertionLinkerId::NONE
        );

        ctx.linked_data_value_assertion_data_add_data_value_assertion(data, role_b, 1002);
        let second_head = ctx
            .linked_data_value_assertion_data(data)
            .get_data_value_role_assertion_linker();
        assert_eq!(
            ctx.data_value_role_assertion_linker(second_head).get_role(),
            role_b
        );
        assert_eq!(
            ctx.data_value_role_assertion_linker(second_head).get_next(),
            first_head
        );
        assert_eq!(ctx.data_value_role_assertion_linker_count(), 2);

        let mut source = LinkedDataValueAssertionSaturationData::new(INVALID);
        source.data_role_linker = second_head;
        let mut target = LinkedDataValueAssertionSaturationData::new(INVALID);
        target.copy_data_value_assertion_data(&source);
        assert_eq!(
            target.get_data_value_role_assertion_linker(),
            source.get_data_value_role_assertion_linker()
        );
    }

    #[test]
    fn sat1_role_assertion_linker_context_prepends_and_allocates() {
        let mut ctx = ProcessContext::new();
        let source = ctx.alloc_sat_node(IndividualSaturationProcessNode::new(892));
        let dest_a = ctx.alloc_sat_node(IndividualSaturationProcessNode::new(893));
        let dest_b = ctx.alloc_sat_node(IndividualSaturationProcessNode::new(894));

        assert_eq!(
            IndividualSaturationProcessNode::get_role_assertion_linker_in_context(&ctx, source),
            SaturationSuccessorRoleAssertionLinkerId::NONE
        );
        assert_eq!(ctx.indi_sat_node_ext_data_count(), 0);

        let mut external_linker = SaturationSuccessorRoleAssertionLinker::new();
        external_linker.init_saturation_successor_role_assertion_linker(
            dest_a,
            RoleId::new(31),
            false,
        );
        let external_linker = ctx.alloc_sat_succ_role_assertion_linker(external_linker);
        IndividualSaturationProcessNode::add_role_assertion_linker_in_context(
            &mut ctx,
            source,
            external_linker,
        );

        let first_head =
            IndividualSaturationProcessNode::get_role_assertion_linker_in_context(&ctx, source);
        assert_eq!(first_head, external_linker);
        assert_eq!(
            ctx.sat_succ_role_assertion_linker(first_head)
                .get_assertion_destination_node(),
            dest_a
        );
        assert_eq!(
            ctx.sat_succ_role_assertion_linker(first_head)
                .get_assertion_role(),
            RoleId::new(31)
        );
        assert!(!ctx
            .sat_succ_role_assertion_linker(first_head)
            .get_assertion_role_negation());
        assert_eq!(
            ctx.sat_succ_role_assertion_linker(first_head).get_next(),
            SaturationSuccessorRoleAssertionLinkerId::NONE
        );

        IndividualSaturationProcessNode::add_role_assertion_in_context(
            &mut ctx,
            source,
            dest_b,
            RoleId::new(37),
            true,
        );
        let second_head =
            IndividualSaturationProcessNode::get_role_assertion_linker_in_context(&ctx, source);
        assert_ne!(second_head, first_head);
        assert_eq!(
            ctx.sat_succ_role_assertion_linker(second_head)
                .get_assertion_destination_node(),
            dest_b
        );
        assert_eq!(
            ctx.sat_succ_role_assertion_linker(second_head)
                .get_assertion_role(),
            RoleId::new(37)
        );
        assert!(ctx
            .sat_succ_role_assertion_linker(second_head)
            .get_assertion_role_negation());
        assert_eq!(
            ctx.sat_succ_role_assertion_linker(second_head).get_next(),
            first_head
        );
        assert_eq!(ctx.sat_succ_role_assertion_linker_count(), 2);
        assert_eq!(ctx.indi_sat_node_ext_data_count(), 1);

        IndividualSaturationProcessNode::add_role_assertion_linker_in_context(
            &mut ctx,
            source,
            SaturationSuccessorRoleAssertionLinkerId::NONE,
        );
        assert_eq!(
            IndividualSaturationProcessNode::get_role_assertion_linker_in_context(&ctx, source),
            second_head
        );
        assert_eq!(ctx.sat_succ_role_assertion_linker_count(), 2);
    }

    #[test]
    fn sat1_critical_concept_type_queues_context_allocates_through_extension_data() {
        let mut ctx = ProcessContext::new();
        let node = ctx.alloc_sat_node(IndividualSaturationProcessNode::new(889));

        let missing = IndividualSaturationProcessNode::get_critical_concept_type_queues_in_context(
            &mut ctx, node, false,
        );
        assert_eq!(missing, CriticalSaturationConceptTypeQueuesId::NONE);
        assert_eq!(ctx.indi_sat_node_ext_data_count(), 0);

        let queues = IndividualSaturationProcessNode::get_critical_concept_type_queues_in_context(
            &mut ctx, node, true,
        );
        assert!(queues.is_some());
        let ext = ctx.sat_node(node).indi_extension_data;
        assert!(ext.is_some());
        assert_eq!(
            ctx.indi_sat_node_ext_data(ext).critical_concept_type_queues,
            queues
        );
        assert_eq!(ctx.critical_sat_concept_type_queues(queues).indi_node, node);
        assert!(
            !ctx.critical_sat_concept_type_queues_has_critical_saturation_concepts_queued(queues)
        );

        let queues_again =
            IndividualSaturationProcessNode::get_critical_concept_type_queues_in_context(
                &mut ctx, node, true,
            );
        assert_eq!(queues_again, queues);
    }

    #[test]
    fn sat1_applied_datatype_data_context_allocates_through_extension_data() {
        let mut ctx = ProcessContext::new();
        let node = ctx.alloc_sat_node(IndividualSaturationProcessNode::new(890));

        let missing = IndividualSaturationProcessNode::get_applied_datatype_data_in_context(
            &mut ctx, node, false,
        );
        assert_eq!(missing, SaturationIndividualNodeDatatypeDataId::NONE);
        assert_eq!(ctx.indi_sat_node_ext_data_count(), 0);

        let data = IndividualSaturationProcessNode::get_applied_datatype_data_in_context(
            &mut ctx, node, true,
        );
        assert!(data.is_some());
        let ext = ctx.sat_node(node).indi_extension_data;
        assert!(ext.is_some());
        assert_eq!(ctx.indi_sat_node_ext_data(ext).applied_datatype_data, data);
        assert_eq!(
            ctx.sat_indi_node_datatype_data(data).process_context,
            INVALID
        );
        assert_eq!(
            ctx.sat_indi_node_datatype_data(data)
                .get_applied_data_literal(),
            INVALID
        );
        assert_eq!(
            ctx.sat_indi_node_datatype_data(data).get_applied_datatype(),
            INVALID
        );

        ctx.sat_indi_node_datatype_data_mut(data)
            .set_applied_data_literal(41)
            .set_applied_datatype(43);
        assert_eq!(
            ctx.sat_indi_node_datatype_data(data)
                .get_applied_data_literal(),
            41
        );
        assert_eq!(
            ctx.sat_indi_node_datatype_data(data).get_applied_datatype(),
            43
        );

        let data_again = IndividualSaturationProcessNode::get_applied_datatype_data_in_context(
            &mut ctx, node, true,
        );
        assert_eq!(data_again, data);
        assert_eq!(ctx.sat_indi_node_datatype_data_count(), 1);
    }

    #[test]
    fn sat1_coping_context_copies_applied_datatype_data() {
        let mut ctx = ProcessContext::new();
        let source = ctx.alloc_sat_node(IndividualSaturationProcessNode::new(891));
        let target = ctx.alloc_sat_node(IndividualSaturationProcessNode::new(892));

        let source_data = IndividualSaturationProcessNode::get_applied_datatype_data_in_context(
            &mut ctx, source, true,
        );
        ctx.sat_indi_node_datatype_data_mut(source_data)
            .set_applied_data_literal(101)
            .set_applied_datatype(103);
        ctx.sat_node_mut(source).set_data_value_applied(true);

        ctx.sat_node_init_coping_individual_saturation_process_node(target, source, false);

        assert!(ctx.sat_node(target).has_data_value_applied());
        let target_data = IndividualSaturationProcessNode::get_applied_datatype_data_in_context(
            &mut ctx, target, false,
        );
        assert!(target_data.is_some());
        assert_ne!(target_data, source_data);
        assert_eq!(
            ctx.sat_indi_node_datatype_data(target_data)
                .get_applied_data_literal(),
            101
        );
        assert_eq!(
            ctx.sat_indi_node_datatype_data(target_data)
                .get_applied_datatype(),
            103
        );
    }

    #[test]
    fn sat1_coping_context_adds_copy_dependency_linker_to_source() {
        let mut ctx = ProcessContext::new();
        let source = ctx.alloc_sat_node(IndividualSaturationProcessNode::new(893));
        let target_a = ctx.alloc_sat_node(IndividualSaturationProcessNode::new(894));
        let target_b = ctx.alloc_sat_node(IndividualSaturationProcessNode::new(895));

        assert!(!ctx
            .sat_node(source)
            .has_copy_depending_individual_node_linker());

        ctx.sat_node_init_coping_individual_saturation_process_node(target_a, source, false);
        ctx.sat_node_init_coping_individual_saturation_process_node(target_b, source, false);

        assert_eq!(
            ctx.sat_node(source)
                .get_copy_depending_individual_node_linker(),
            &[
                NegLink {
                    target: target_a,
                    negated: true,
                },
                NegLink {
                    target: target_b,
                    negated: true,
                },
            ]
        );
    }

    #[test]
    fn sat1_nominal_and_successor_connected_context_getters_follow_konclude_chain() {
        let mut ctx = ProcessContext::new();
        let node = ctx.alloc_sat_node(IndividualSaturationProcessNode::new(999));

        let missing_nominal = IndividualSaturationProcessNode::get_nominal_handling_data_in_context(
            &mut ctx, node, false,
        );
        assert_eq!(
            missing_nominal,
            SaturationIndividualNodeNominalHandlingDataId::NONE
        );

        let nominal = IndividualSaturationProcessNode::get_nominal_handling_data_in_context(
            &mut ctx, node, true,
        );
        assert!(nominal.is_some());
        assert_eq!(ctx.sat_nominal_handling_data(nominal).indi_node, node);

        let missing_set =
            IndividualSaturationProcessNode::get_successor_connected_nominal_set_in_context(
                &mut ctx, node, false,
            );
        assert_eq!(missing_set, SuccessorConnectedNominalSetId::NONE);

        let set = IndividualSaturationProcessNode::get_successor_connected_nominal_set_in_context(
            &mut ctx, node, true,
        );
        assert!(set.is_some());
        assert!(ctx.nominal_conn_set(set).is_empty());
        assert_eq!(
            ctx.sat_nominal_handling_data(nominal)
                .succ_connected_nominal_set,
            set
        );

        let set_again =
            IndividualSaturationProcessNode::get_successor_connected_nominal_set_in_context(
                &mut ctx, node, true,
            );
        assert_eq!(set_again, set);
    }

    #[test]
    fn sat1_concept_saturation_process_linker_direct_methods_preserve_chain() {
        let mut ctx = ProcessContext::new();
        let first = ctx.alloc_con_sat_proc_linker(ConceptSaturationProcessLinker::new());
        let second = ctx.alloc_con_sat_proc_linker(ConceptSaturationProcessLinker::new());
        ctx.con_sat_proc_linker_mut(first).set_next(second);
        let old_head = ctx.alloc_con_sat_proc_linker(ConceptSaturationProcessLinker::new());

        let mut node = IndividualSaturationProcessNode::new(INVALID);
        node.set_concept_saturation_process_linker(old_head);
        node.add_concept_saturation_process_linker(&mut ctx, first);

        assert_eq!(node.get_concept_saturation_process_linker(), first);
        assert_eq!(ctx.con_sat_proc_linker(first).get_next(), second);
        assert_eq!(ctx.con_sat_proc_linker(second).get_next(), old_head);

        assert_eq!(node.take_concept_saturation_process_linker(&ctx), first);
        assert_eq!(node.get_concept_saturation_process_linker(), second);
        assert_eq!(node.take_concept_saturation_process_linker(&ctx), second);
        assert_eq!(node.get_concept_saturation_process_linker(), old_head);
        assert_eq!(node.take_concept_saturation_process_linker(&ctx), old_head);
        assert_eq!(
            node.get_concept_saturation_process_linker(),
            ConceptSaturationProcessLinkerId::NONE
        );
    }

    #[test]
    fn sat1_context_concept_saturation_process_linker_helpers_preserve_chain() {
        let mut ctx = ProcessContext::new();
        let node = ctx.alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));
        let old_head = ctx.alloc_con_sat_proc_linker(ConceptSaturationProcessLinker::new());
        let first = ctx.alloc_con_sat_proc_linker(ConceptSaturationProcessLinker::new());
        let second = ctx.alloc_con_sat_proc_linker(ConceptSaturationProcessLinker::new());
        ctx.con_sat_proc_linker_mut(first).set_next(second);
        ctx.sat_node_mut(node)
            .set_concept_saturation_process_linker(old_head);

        ctx.sat_node_add_concept_saturation_process_linker(node, first);

        assert_eq!(
            ctx.sat_node(node).get_concept_saturation_process_linker(),
            first
        );
        assert_eq!(ctx.con_sat_proc_linker(first).get_next(), second);
        assert_eq!(ctx.con_sat_proc_linker(second).get_next(), old_head);

        assert_eq!(
            ctx.sat_node_take_concept_saturation_process_linker(node),
            first
        );
        assert_eq!(
            ctx.sat_node_take_concept_saturation_process_linker(node),
            second
        );
        assert_eq!(
            ctx.sat_node_take_concept_saturation_process_linker(node),
            old_head
        );
        assert_eq!(
            ctx.sat_node_take_concept_saturation_process_linker(node),
            ConceptSaturationProcessLinkerId::NONE
        );
    }

    #[test]
    fn sat1_initializing_backward_propagation_links_append_like_konclude() {
        let mut ctx = ProcessContext::new();
        let old_head = ctx.alloc_backward_sat_prop_link(BackwardSaturationPropagationLink::new());
        let first = ctx.alloc_backward_sat_prop_link(BackwardSaturationPropagationLink::new());
        let second = ctx.alloc_backward_sat_prop_link(BackwardSaturationPropagationLink::new());
        ctx.backward_sat_prop_link_mut(first).set_next(second);

        let mut node = IndividualSaturationProcessNode::new(INVALID);
        node.set_initializing_backward_propagation_links(old_head);
        node.add_initializing_backward_propagation_links(&mut ctx, first);

        assert_eq!(node.get_initializing_backward_propagation_links(), first);
        assert_eq!(ctx.backward_sat_prop_link(first).get_next(), second);
        assert_eq!(ctx.backward_sat_prop_link(second).get_next(), old_head);
    }

    #[test]
    fn sat1_clashed_concept_saturation_descriptor_linker_appends_chain() {
        let mut ctx = ProcessContext::new();
        let old_head = ctx.alloc_con_sat_desc(ConceptSaturationDescriptor::new());
        let first = ctx.alloc_con_sat_desc(ConceptSaturationDescriptor::new());
        let second = ctx.alloc_con_sat_desc(ConceptSaturationDescriptor::new());
        ctx.con_sat_desc_mut(first).set_next(second);

        let mut node = IndividualSaturationProcessNode::new(INVALID);
        node.add_clashed_concept_saturation_descriptor_linker(&mut ctx, old_head);
        node.add_clashed_concept_saturation_descriptor_linker(&mut ctx, first);

        assert!(node.has_clashed_concept_saturation_descriptor_linker());
        assert_eq!(
            node.get_clashed_concept_saturation_descriptor_linker(),
            first
        );
        assert_eq!(ctx.con_sat_desc(first).get_next_concept_desciptor(), second);
        assert_eq!(
            ctx.con_sat_desc(second).get_next_concept_desciptor(),
            old_head
        );
    }

    #[test]
    fn sat1_completion_node_linker_context_allocates_and_tracks_queue_flag() {
        let mut ctx = ProcessContext::new();
        let node = ctx.alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));

        assert_eq!(
            ctx.sat_node_individual_saturation_completion_node_linker(node, false),
            IndividualSaturationProcessNodeLinkerId::NONE
        );
        assert!(!ctx.sat_node_individual_saturation_completion_node_linker_queued(node));
        assert_eq!(ctx.indi_sat_process_node_linker_count(), 0);

        let linker = ctx.sat_node_individual_saturation_completion_node_linker(node, true);
        assert!(linker.is_some());
        assert_eq!(ctx.sat_node(node).indi_completion_linker, linker);
        assert_eq!(ctx.indi_sat_process_node_linker_count(), 1);
        assert_eq!(
            ctx.indi_sat_process_node_linker(linker)
                .get_processing_individual(),
            node
        );
        assert!(!ctx
            .indi_sat_process_node_linker(linker)
            .is_processing_queued());

        ctx.sat_node_set_individual_saturation_completion_node_linker_queued(node, true);
        assert!(ctx.sat_node_individual_saturation_completion_node_linker_queued(node));
        assert!(ctx
            .indi_sat_process_node_linker(linker)
            .is_processing_queued());

        let linker_again = ctx.sat_node_individual_saturation_completion_node_linker(node, true);
        assert_eq!(linker_again, linker);
        assert_eq!(ctx.indi_sat_process_node_linker_count(), 1);

        ctx.sat_node_set_individual_saturation_completion_node_linker_queued(node, false);
        assert!(!ctx.sat_node_individual_saturation_completion_node_linker_queued(node));
    }

    #[test]
    fn sat1_reapply_concept_saturation_label_set_false_does_not_allocate() {
        let mut ctx = ProcessContext::new();
        let node = ctx.alloc_sat_node(IndividualSaturationProcessNode::new(123));

        let label_set = ctx.sat_node_reapply_concept_saturation_label_set(node, false);

        assert_eq!(label_set, ReapplyConceptSaturationLabelSetId::NONE);
        assert_eq!(ctx.sat_node(node).reapply_con_sat_label_set, label_set);
        assert_eq!(ctx.reapply_con_sat_label_set_count(), 0);
    }

    #[test]
    fn sat1_reapply_concept_saturation_label_set_true_allocates_and_initializes_once() {
        let mut ctx = ProcessContext::new();
        let node = ctx.alloc_sat_node(IndividualSaturationProcessNode::new(456));

        let label_set = ctx.sat_node_reapply_concept_saturation_label_set(node, true);

        assert!(label_set.is_some());
        assert_eq!(ctx.sat_node(node).reapply_con_sat_label_set, label_set);
        assert_eq!(ctx.reapply_con_sat_label_set_count(), 1);
        let allocated = ctx.reapply_con_sat_label_set(label_set);
        assert_eq!(allocated.process_context, 456);
        assert!(allocated.concept_des_dep_hash.is_empty());
        assert!(allocated.additional_concept_des_dep_hash.is_empty());
        assert!(!allocated.has_additional_concept_des_dep_hash);
        assert_eq!(
            allocated.concept_sat_des_linker,
            ConceptSaturationDescriptorId::NONE
        );
        assert_eq!(
            allocated.last_nominal_indep_con_sat_des,
            ConceptSaturationDescriptorId::NONE
        );
        assert_eq!(allocated.concept_flags, 0);
        assert_eq!(allocated.concept_count, 0);
        assert_eq!(allocated.totel_count, 0);
        assert!(allocated.modified_update_linker.is_none());

        let label_set_again = ctx.sat_node_reapply_concept_saturation_label_set(node, true);
        assert_eq!(label_set_again, label_set);
        assert_eq!(ctx.reapply_con_sat_label_set_count(), 1);
    }

    #[test]
    fn sat1_reapply_concept_saturation_label_set_none_node_returns_none() {
        let mut ctx = ProcessContext::new();

        let label_set = ctx.sat_node_reapply_concept_saturation_label_set(SatNodeId::NONE, true);

        assert_eq!(label_set, ReapplyConceptSaturationLabelSetId::NONE);
        assert_eq!(ctx.reapply_con_sat_label_set_count(), 0);
    }
}
