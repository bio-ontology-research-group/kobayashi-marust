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
//! Several method bodies reach into not-yet-ported classes (the per-test arena
//! allocator, the saturation sub-struct copy routines, the linker `append`/
//! `getNext`/`isProcessingQueued`/`initProcessNodeLinker` surface, the extension
//! data accessors, the status-flag masks). Those calls are marked
//! `// W2-DEFER[api]: <call>` with a minimal stub that preserves control flow.

#![allow(dead_code)]

use super::super::model::substrate::{Cint64, Id, NegLink, INVALID};
use super::super::model::{IndividualId, RoleId};
use super::sat_node::{
    IndividualSaturationProcessNode, IndividualSaturationProcessNodeStatusFlags,
};
use super::stubs::{
    BackwardSaturationPropagationLinkId, ConceptSaturationDescriptorId,
    ConceptSaturationProcessLinkerId, ExtendedConceptReferenceLinkingDataId,
    IndividualSaturationProcessNodeCacheDataId, IndividualSaturationProcessNodeExtensionDataId,
    IndividualSaturationProcessNodeLinkerId, IndividualSaturationReferenceLinkingDataId,
    ReapplyConceptSaturationLabelSetId, RoleBackwardSaturationPropagationHashId,
};
use super::SatNodeId;

// ---------------------------------------------------------------------------
// Status-flag helpers (the bit accessors `is*/set*` call through).
// ---------------------------------------------------------------------------

impl IndividualSaturationProcessNodeStatusFlags {
    // W2-DEFER[api]: the concrete saturation status-flag bit masks
    // (`CIndividualSaturationProcessNodeStatusFlags::hasInitializedFlag`/`…Completed…`)
    // land with the status-flag port unit; these placeholder bits keep a node's
    // own init/complete state self-consistent in the meantime.
    const INITIALIZED_FLAG: Cint64 = 0x1;
    const COMPLETED_FLAG: Cint64 = 0x2;

    /// Port of `hasInitializedFlag`.
    fn has_initialized_flag(&self) -> bool {
        (self.flags & Self::INITIALIZED_FLAG) != 0
    }
    /// Port of `setInitializedFlag`.
    fn set_initialized_flag(&mut self, value: bool) {
        if value {
            self.flags |= Self::INITIALIZED_FLAG;
        } else {
            self.flags &= !Self::INITIALIZED_FLAG;
        }
    }
    /// Port of `hasCompletedFlag`.
    fn has_completed_flag(&self) -> bool {
        (self.flags & Self::COMPLETED_FLAG) != 0
    }
    /// Port of `setCompletedFlag`.
    fn set_completed_flag(&mut self, value: bool) {
        if value {
            self.flags |= Self::COMPLETED_FLAG;
        } else {
            self.flags &= !Self::COMPLETED_FLAG;
        }
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
    pub fn get_saturation_concept_reference_linking(&self) -> ExtendedConceptReferenceLinkingDataId {
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
            // W2-DEFER[api]: getRoleBackwardPropagationHash(true)->copyRoleBackwardSaturationPropagationHash(indiNode->getRoleBackwardPropagationHash(false),this)
            // (CRoleBackwardSaturationPropagationHash copy not yet ported)
            let _ = self.get_role_backward_propagation_hash(true);
        }
        if indi_node.reapply_con_sat_label_set.is_some() {
            // W2-DEFER[api]: getReapplyConceptSaturationLabelSet(true)->copyReapplyConceptSaturationLabelSet(indiNode->getReapplyConceptSaturationLabelSet(false),tryFlatLabelCopy)
            // (CReapplyConceptSaturationLabelSet copy lands with the LS unit)
            let _ = self.get_reapply_concept_saturation_label_set(true);
            let _ = try_flat_label_copy;
        }
        // W2-DEFER[api]: if (indiNode->getSuccessorConnectedNominalSet(false)) getSuccessorConnectedNominalSet(true)->copySuccessorConnectedNominalSet(...)
        // (delegates through the not-yet-ported nominal-handling extension data)

        self.integrated_nominal_indi = indi_node.integrated_nominal_indi;
        if indi_node.nominal_indi.is_some() {
            self.integrated_nominal_indi = indi_node.nominal_indi;
        }
        if self.nominal_indi.is_some() {
            self.integrated_nominal_indi = self.nominal_indi;
        }
        self.data_value_applied = indi_node.data_value_applied;

        // W2-DEFER[api]: if (indiNode->getAppliedDatatypeData(false)) { getAppliedDatatypeData(true)->setAppliedDataLiteral(...); getAppliedDatatypeData(true)->setAppliedDatatype(...); }
        // (CSaturationIndividualNodeDatatypeData not yet ported)

        // W2-DEFER[api]: depCopyLinker = CObjectAllocator<CXNegLinker<...>>::allocateAndConstruct(mMemAllocMan); depCopyLinker->initNegLinker(this,true); indiNode->addCopyDependingIndividualNodeLinker(depCopyLinker)
        // (needs this node's own SatNodeId + a &mut source node; the cross-node
        // depend-linker install lands with the arena-aware saturation driver)
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
            // W2-DEFER[api]: CObjectParameterizingAllocator<CReapplyConceptSaturationLabelSet,...>::allocateAndConstructAndParameterize + initReapplyConceptSaturationLabelSet()
            // (arena allocation + the LS unit not yet ported)
        }
        self.reapply_con_sat_label_set
    }

    /// Port of `getIndividualExtensionData`.
    pub fn get_individual_extension_data(
        &mut self,
        create: bool,
    ) -> IndividualSaturationProcessNodeExtensionDataId {
        if create && self.indi_extension_data.is_none() {
            // W2-DEFER[api]: CObjectParameterizingAllocator<CIndividualSaturationProcessNodeExtensionData,...>::allocateAndConstructAndParameterize + initIndividualExtensionData(this)
            // (extension-data class + arena allocation not yet ported)
        }
        self.indi_extension_data
    }

    /// Port of `getDisjunctCommonConceptExtractionData`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: returns `CSaturationDisjunctCommonConceptExtractionData*`,
    /// an un-ported extension sub-struct; modelled as an opaque `Cint64` handle
    /// (`INVALID` == `nullptr`) until the extension data lands.
    pub fn get_disjunct_common_concept_extraction_data(&mut self, create: bool) -> Cint64 {
        if create {
            // W2-DEFER[api]: getIndividualExtensionData(true)->getDisjunctCommonConceptExtractionData(true)
            let _ = self.get_individual_extension_data(true);
            return INVALID;
        }
        if self.indi_extension_data.is_some() {
            // W2-DEFER[api]: mIndiExtensionData->getDisjunctCommonConceptExtractionData(false)
            return INVALID;
        }
        INVALID
    }

    /// Port of `getRoleBackwardPropagationHash`.
    pub fn get_role_backward_propagation_hash(
        &mut self,
        create: bool,
    ) -> RoleBackwardSaturationPropagationHashId {
        if create && self.role_back_prop_hash.is_none() {
            // W2-DEFER[api]: CObjectParameterizingAllocator<CRoleBackwardSaturationPropagationHash,...>::allocateAndConstructAndParameterize + initRoleBackwardSaturationPropagationHash()
            // (arena allocation + the RS-style hash not yet ported)
        }
        self.role_back_prop_hash
    }

    /// Port of `getSuccessorConnectedNominalSet`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: `CSuccessorConnectedNominalSet*` is un-ported;
    /// returned as an opaque `Cint64` handle.
    pub fn get_successor_connected_nominal_set(&mut self, create: bool) -> Cint64 {
        let mut succ_connected_nominal_set: Cint64 = INVALID;
        let nominal_handling_data = self.get_nominal_handling_data(create);
        if nominal_handling_data != INVALID {
            // W2-DEFER[api]: nominalHandlingData->getSuccessorConnectedNominalSet(create)
            succ_connected_nominal_set = INVALID;
        }
        succ_connected_nominal_set
    }

    /// Port of `getLinkedDataValueAssertionData`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: opaque `Cint64` handle for the un-ported
    /// `CLinkedDataValueAssertionSaturationData*`.
    pub fn get_linked_data_value_assertion_data(&mut self, create: bool) -> Cint64 {
        if create {
            // W2-DEFER[api]: getIndividualExtensionData(true)->getLinkedDataValueAssertionData(true)
            let _ = self.get_individual_extension_data(true);
            return INVALID;
        }
        if self.indi_extension_data.is_some() {
            // W2-DEFER[api]: mIndiExtensionData->getLinkedDataValueAssertionData(false)
            return INVALID;
        }
        INVALID
    }

    /// Port of `getCriticalPredecessorRoleCardinalityHash`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: opaque `Cint64` handle for the un-ported
    /// `CCriticalPredecessorRoleCardinalityHash*`.
    pub fn get_critical_predecessor_role_cardinality_hash(&mut self, create: bool) -> Cint64 {
        if create {
            // W2-DEFER[api]: getIndividualExtensionData(true)->getCriticalPredecessorRoleCardinalityHash(true)
            let _ = self.get_individual_extension_data(true);
            return INVALID;
        }
        if self.indi_extension_data.is_some() {
            // W2-DEFER[api]: mIndiExtensionData->getCriticalPredecessorRoleCardinalityHash(false)
            return INVALID;
        }
        INVALID
    }

    /// Port of `getLinkedRoleSuccessorHash`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: opaque `Cint64` handle for the un-ported
    /// `CLinkedRoleSaturationSuccessorHash*`.
    pub fn get_linked_role_successor_hash(&mut self, create: bool) -> Cint64 {
        if create {
            // W2-DEFER[api]: getIndividualExtensionData(true)->getLinkedRoleSuccessorHash(true)
            let _ = self.get_individual_extension_data(true);
            return INVALID;
        }
        if self.indi_extension_data.is_some() {
            // W2-DEFER[api]: mIndiExtensionData->getLinkedRoleSuccessorHash(false)
            return INVALID;
        }
        INVALID
    }

    /// Port of `getCriticalConceptTypeQueues`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: opaque `Cint64` handle for the un-ported
    /// `CCriticalSaturationConceptTypeQueues*`.
    pub fn get_critical_concept_type_queues(&mut self, create: bool) -> Cint64 {
        if create {
            // W2-DEFER[api]: getIndividualExtensionData(true)->getCriticalConceptTypeQueues(true)
            let _ = self.get_individual_extension_data(true);
            return INVALID;
        }
        if self.indi_extension_data.is_some() {
            // W2-DEFER[api]: mIndiExtensionData->getCriticalConceptTypeQueues(false)
            return INVALID;
        }
        INVALID
    }

    /// Port of `getSuccessorExtensionData`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: opaque `Cint64` handle for the un-ported
    /// `CSaturationIndividualNodeSuccessorExtensionData*`.
    pub fn get_successor_extension_data(&mut self, create: bool) -> Cint64 {
        if create {
            // W2-DEFER[api]: getIndividualExtensionData(true)->getSuccessorExtensionData(true)
            let _ = self.get_individual_extension_data(true);
            return INVALID;
        }
        if self.indi_extension_data.is_some() {
            // W2-DEFER[api]: mIndiExtensionData->getSuccessorExtensionData(false)
            return INVALID;
        }
        INVALID
    }

    /// Port of `getNominalHandlingData`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: opaque `Cint64` handle for the un-ported
    /// `CSaturationIndividualNodeNominalHandlingData*`.
    pub fn get_nominal_handling_data(&mut self, create: bool) -> Cint64 {
        if create {
            // W2-DEFER[api]: getIndividualExtensionData(true)->getNominalHandlingData(true)
            let _ = self.get_individual_extension_data(true);
            return INVALID;
        }
        if self.indi_extension_data.is_some() {
            // W2-DEFER[api]: mIndiExtensionData->getNominalHandlingData(false)
            return INVALID;
        }
        INVALID
    }

    /// Port of `getAppliedDatatypeData`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: opaque `Cint64` handle for the un-ported
    /// `CSaturationIndividualNodeDatatypeData*`.
    pub fn get_applied_datatype_data(&mut self, create: bool) -> Cint64 {
        if create {
            // W2-DEFER[api]: getIndividualExtensionData(true)->getAppliedDatatypeData(true)
            let _ = self.get_individual_extension_data(true);
            return INVALID;
        }
        if self.indi_extension_data.is_some() {
            // W2-DEFER[api]: mIndiExtensionData->getAppliedDatatypeData(false)
            return INVALID;
        }
        INVALID
    }

    /// Port of `getATMOSTSuccessorMergingData`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: opaque `Cint64` handle for the un-ported
    /// `CSaturationATMOSTSuccessorMergingData*`.
    pub fn get_atmost_successor_merging_data(&mut self, create: bool) -> Cint64 {
        if create {
            // W2-DEFER[api]: getIndividualExtensionData(true)->getATMOSTSuccessorMergingData(true)
            let _ = self.get_individual_extension_data(true);
            return INVALID;
        }
        if self.indi_extension_data.is_some() {
            // W2-DEFER[api]: mIndiExtensionData->getATMOSTSuccessorMergingData(false)
            return INVALID;
        }
        INVALID
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
    pub fn take_concept_saturation_process_linker(&mut self) -> ConceptSaturationProcessLinkerId {
        let con_proc_linker = self.concept_saturation_process_linker;
        if self.concept_saturation_process_linker.is_some() {
            // W2-DEFER[api]: mConceptSaturationProcessLinker = mConceptSaturationProcessLinker->getNext()
            // (CConceptSaturationProcessLinker chain not yet ported; minimal stub
            // drops the head)
            self.concept_saturation_process_linker = Id::NONE;
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
        con_process_linker: ConceptSaturationProcessLinkerId,
    ) -> &mut Self {
        // W2-DEFER[api]: mConceptSaturationProcessLinker = conProcessLinker->append(mConceptSaturationProcessLinker)
        // (linker chain `append` not yet ported; minimal stub installs the new head)
        self.concept_saturation_process_linker = con_process_linker;
        self
    }

    /// Port of `clearConceptSaturationProcessLinker`.
    pub fn clear_concept_saturation_process_linker(&mut self) -> &mut Self {
        self.concept_saturation_process_linker = Id::NONE;
        self
    }

    /// Port of `getRoleAssertionLinker`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: opaque `Cint64` handle for the un-ported
    /// `CSaturationSuccessorRoleAssertionLinker*`.
    pub fn get_role_assertion_linker(&self) -> Cint64 {
        if self.indi_extension_data.is_some() {
            // W2-DEFER[api]: mIndiExtensionData->getRoleAssertionLinker()
            return INVALID;
        }
        INVALID
    }

    /// Port of `addRoleAssertionLinker`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: `roleAssertionLinker` is the un-ported
    /// `CSaturationSuccessorRoleAssertionLinker*`, taken as an opaque `Cint64`.
    pub fn add_role_assertion_linker(&mut self, role_assertion_linker: Cint64) -> &mut Self {
        let _ = self.get_individual_extension_data(true);
        // W2-DEFER[api]: getIndividualExtensionData(true)->addRoleAssertionLinker(roleAssertionLinker)
        let _ = role_assertion_linker;
        self
    }

    /// Port of `addRoleAssertion`.
    pub fn add_role_assertion(
        &mut self,
        destination_node: SatNodeId,
        role: RoleId,
        role_negation: bool,
    ) -> &mut Self {
        let _ = self.get_individual_extension_data(true);
        // W2-DEFER[api]: getIndividualExtensionData(true)->addRoleAssertion(destinationNode,role,roleNegation)
        let _ = (destination_node, role, role_negation);
        self
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
    pub fn get_initializing_backward_propagation_links(&self) -> BackwardSaturationPropagationLinkId {
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
        backward_prop_links: BackwardSaturationPropagationLinkId,
    ) -> &mut Self {
        if backward_prop_links.is_some() {
            // W2-DEFER[api]: mInitBackwardPropLinks = backwardPropLinks->append(mInitBackwardPropLinks)
            // (CBackwardSaturationPropagationLink chain `append` not yet ported)
            self.init_backward_prop_links = backward_prop_links;
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
    pub fn get_clashed_concept_saturation_descriptor_linker(&self) -> ConceptSaturationDescriptorId {
        self.clashed_con_sat_des_linker
    }

    /// Port of `addClashedConceptSaturationDescriptorLinker`.
    pub fn add_clashed_concept_saturation_descriptor_linker(
        &mut self,
        clash_con_sat_des: ConceptSaturationDescriptorId,
    ) -> &mut Self {
        // W2-DEFER[api]: mClashedConSatDesLinker = clashConSatDes->append(mClashedConSatDesLinker)
        // (CConceptSaturationDescriptor chain `append` not yet ported)
        self.clashed_con_sat_des_linker = clash_con_sat_des;
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
            self.multiple_cardinality_ancestor_nodes_linker.push(indi_link);
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

    /// Port of `isIndividualSaturationCompletionNodeLinkerQueued`.
    pub fn is_individual_saturation_completion_node_linker_queued(&self) -> bool {
        if self.indi_completion_linker.is_some() {
            // W2-DEFER[api]: mIndiCompletionLinker->isProcessingQueued()
            // (CIndividualSaturationProcessNodeLinker not yet ported)
            return false;
        }
        false
    }

    /// Port of `getIndividualSaturationCompletionNodeLinker`.
    pub fn get_individual_saturation_completion_node_linker(
        &mut self,
        create: bool,
    ) -> IndividualSaturationProcessNodeLinkerId {
        if self.indi_completion_linker.is_none() && create {
            // W2-DEFER[api]: CObjectAllocator<CIndividualSaturationProcessNodeLinker>::allocateAndConstruct(mMemAllocMan) + initProcessNodeLinker(this,false)
            // (arena allocation + linker init not yet ported)
        }
        self.indi_completion_linker
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
