//! `saturation::satellites` (port unit W4.5) — the per-test **saturation-layer
//! satellites** the approximate-saturation engine (`s02..s12`) allocates and
//! threads, ported from Konclude `Source/Reasoner/Kernel/Process/`.
//!
//! These are the saturation twins of the completion-layer `Process/` satellites:
//! the concept/role process linkers the per-node saturation queue is built from,
//! the negated-concept saturation descriptor chain, the backward-propagation
//! links, the linked-role-successor hash + its per-role data + per-successor
//! data, the per-node extension data, and the saturation reapply label set. They
//! were stubbed as zero-size markers in `process::stubs` (the SD-4 block) so the
//! struct waves could compile; this unit replaces those markers with the real
//! structs (the `process::stubs` ids re-alias here, the W2.7/W3b reconcile
//! pattern) and adds the matching per-test `Arena<T>` pools to `ProcessContext`.
//!
//! Konclude sources (one Rust struct per C++ class, same-named methods):
//! - `CConceptSaturationDescriptor` (`CNegLinkerBase<CConcept*,Self>`)
//! - `CConceptSaturationProcessLinker` (`CLinkerBase<CConceptSaturationDescriptor*,Self>`)
//! - `CRoleSaturationProcessLinker` (`CLinkerBase<CRole*,Self>`)
//! - `CBackwardSaturationPropagationLink` (`CLinkerBase<CRole*,Self>` + source)
//! - `CSaturationSuccessorData`
//! - `CLinkedRoleSaturationSuccessorData`
//! - `CLinkedRoleSaturationSuccessorHash`
//! - `CIndividualSaturationProcessNodeExtensionData`
//! - `CReapplyConceptSaturationLabelSet` (+ `CConceptSaturationDescriptorReapplyData`)
//!
//! KONCLUDE-PORT-NOTE[ownership]: every `CXxx*` member becomes a typed `Id<T>`
//! into the matching per-test arena on `ProcessContext` (`Id::NONE` == the C++
//! `nullptr`); the intrusive `CLinker`/`CNegLinker` self-chains become an explicit
//! `next: Id<Self>` link field (head-at-front, the canonical PORT.md §6 linker
//! convention); a `CXNegLinker<CRole*>*` chain becomes `Vec<NegLink<RoleId>>`;
//! a `CPROCESSHASH`/`CPROCESSMAP` becomes an owned `HashMap`. Behaviour is
//! identical; only the representation differs.
//!
//! KONCLUDE-PORT-NOTE[api]: the deeper saturation sub-structs these containers
//! reach into (`CSaturationSuccessorExtensionData`,
//! the ATMOST merging data and `CConceptSetFlags`) are NOT ported in this wave;
//! they stay opaque `Cint64` (`INVALID` == `nullptr`). The complex
//! container method bodies that walk them (`addLinkedSuccessor`, the lazy
//! create-getters, modified-update-linker mutation, …) keep their faithful C++
//! transcription as `W4.5-DEFER` markers and land when those sub-structs port.

#![allow(dead_code)]

use std::collections::{HashMap, HashSet};

use super::super::model::ontology::OntologyArenas;
use super::super::model::substrate::{Arena, Cint64, Id, NegLink, INVALID};
use super::super::model::{ConceptId, RoleId};
use super::super::process::nominal_conn::SaturationIndividualNodeNominalHandlingDataId;
use super::super::process::sat_linker::{
    IndividualSaturationProcessNodeLinker, IndividualSaturationProcessNodeLinkerId,
};
use super::super::process::sat_queue::CriticalSaturationConceptTypeQueuesId;
use super::super::process::SatNodeId;

// ===========================================================================
// Id aliases (the `CXxx*` → `Id<Xxx>` arena handles). The `process::stubs`
// SD-4 ids that were zero-size markers re-alias to these (see process/stubs.rs).
// ===========================================================================
/// `CConceptSaturationDescriptor*`.
pub type ConceptSaturationDescriptorId = Id<ConceptSaturationDescriptor>;
/// `CConceptSaturationProcessLinker*`.
pub type ConceptSaturationProcessLinkerId = Id<ConceptSaturationProcessLinker>;
/// `CRoleSaturationProcessLinker*`.
pub type RoleSaturationProcessLinkerId = Id<RoleSaturationProcessLinker>;
/// `CBackwardSaturationPropagationLink*`.
pub type BackwardSaturationPropagationLinkId = Id<BackwardSaturationPropagationLink>;
/// `CBackwardSaturationPropagationReapplyDescriptor*`.
pub type BackwardSaturationPropagationReapplyDescriptorId =
    Id<BackwardSaturationPropagationReapplyDescriptor>;
/// `CRoleBackwardSaturationPropagationHash*`.
pub type RoleBackwardSaturationPropagationHashId = Id<RoleBackwardSaturationPropagationHash>;
/// `CSaturationSuccessorData*`.
pub type SaturationSuccessorDataId = Id<SaturationSuccessorData>;
/// `CSaturationSuccessorExtensionData*`.
pub type SaturationSuccessorExtensionDataId = Id<SaturationSuccessorExtensionData>;
/// `CIndividualSaturationSuccessorLinkDataLinker*`.
pub type IndividualSaturationSuccessorLinkDataLinkerId =
    Id<IndividualSaturationSuccessorLinkDataLinker>;
/// `CLinkedRoleSaturationSuccessorData*`.
pub type LinkedRoleSaturationSuccessorDataId = Id<LinkedRoleSaturationSuccessorData>;
/// `CLinkedRoleSaturationSuccessorHash*`.
pub type LinkedRoleSaturationSuccessorHashId = Id<LinkedRoleSaturationSuccessorHash>;
/// `CIndividualSaturationProcessNodeExtensionData*`.
pub type IndividualSaturationProcessNodeExtensionDataId =
    Id<IndividualSaturationProcessNodeExtensionData>;
/// `CSaturationIndividualNodeSuccessorExtensionData*`.
pub type SaturationIndividualNodeSuccessorExtensionDataId =
    Id<SaturationIndividualNodeSuccessorExtensionData>;
/// `CSaturationIndividualNodeALLConceptsExtensionData*`.
pub type SaturationIndividualNodeAllConceptsExtensionDataId =
    Id<SaturationIndividualNodeAllConceptsExtensionData>;
/// `CSaturationLinkedSuccessorIndividualALLConceptsExtensionData*`.
pub type SaturationLinkedSuccessorIndividualAllConceptsExtensionDataId =
    Id<SaturationLinkedSuccessorIndividualAllConceptsExtensionData>;
/// `CSaturationSuccessorALLConceptExtensionData*`.
pub type SaturationSuccessorAllConceptExtensionDataId =
    Id<SaturationSuccessorAllConceptExtensionData>;
/// `CSaturationIndividualNodeExtensionResolveData*`.
pub type SaturationIndividualNodeExtensionResolveDataId =
    Id<SaturationIndividualNodeExtensionResolveData>;
/// `CSaturationIndividualNodeExtensionResolveHash*`.
pub type SaturationIndividualNodeExtensionResolveHashId =
    Id<SaturationIndividualNodeExtensionResolveHash>;
/// Temporary `CPROCESSINGHASH<cint64,CConceptNegationPair>*`.
pub type SaturationConceptExtensionMapId = Id<SaturationConceptExtensionMap>;
/// `CSaturationSuccessorConceptExtensionMap*`.
pub type SaturationSuccessorConceptExtensionMapId = Id<SaturationSuccessorConceptExtensionMap>;
/// `CSaturationIndividualNodeFUNCTIONALConceptsExtensionData*`.
pub type SaturationIndividualNodeFunctionalConceptsExtensionDataId =
    Id<SaturationIndividualNodeFunctionalConceptsExtensionData>;
/// `CSaturationSuccessorFUNCTIONALConceptExtensionData*`.
pub type SaturationSuccessorFunctionalConceptExtensionDataId =
    Id<SaturationSuccessorFunctionalConceptExtensionData>;
/// `CLinkedDataValueAssertionSaturationData*`.
pub type LinkedDataValueAssertionSaturationDataId = Id<LinkedDataValueAssertionSaturationData>;
/// `CXLinker<CRole*>*` used by `CLinkedDataValueAssertionSaturationData`.
pub type DataValueRoleAssertionLinkerId = Id<DataValueRoleAssertionLinker>;
/// `CSaturationSuccessorRoleAssertionLinker*`.
pub type SaturationSuccessorRoleAssertionLinkerId = Id<SaturationSuccessorRoleAssertionLinker>;
/// `CCriticalPredecessorRoleCardinalityData*`.
pub type CriticalPredecessorRoleCardinalityDataId = Id<CriticalPredecessorRoleCardinalityData>;
/// `CCriticalPredecessorRoleCardinalityHash*`.
pub type CriticalPredecessorRoleCardinalityHashId = Id<CriticalPredecessorRoleCardinalityHash>;
/// `CSaturationDisjunctCommonConceptCountHashData*` (map value in the C++ hash).
pub type SaturationDisjunctCommonConceptCountHashDataId =
    Id<SaturationDisjunctCommonConceptCountHashData>;
/// `CSaturationDisjunctExtractionLinker*`.
pub type SaturationDisjunctExtractionLinkerId = Id<SaturationDisjunctExtractionLinker>;
/// `CSaturationDisjunctCommonConceptExtractionData*`.
pub type SaturationDisjunctCommonConceptExtractionDataId =
    Id<SaturationDisjunctCommonConceptExtractionData>;
/// `CSaturationATMOSTSuccessorMergingHashData*` (map value in the C++ hash).
pub type SaturationAtmostSuccessorMergingHashDataId = Id<SaturationAtmostSuccessorMergingHashData>;
/// `CSaturationATMOSTSuccessorMergingHash*`.
pub type SaturationAtmostSuccessorMergingHashId = Id<SaturationAtmostSuccessorMergingHash>;
/// `CSaturationATMOSTSuccessorMergingData*`.
pub type SaturationAtmostSuccessorMergingDataId = Id<SaturationAtmostSuccessorMergingData>;
/// `CSaturationIndividualNodeDatatypeData*`.
pub type SaturationIndividualNodeDatatypeDataId = Id<SaturationIndividualNodeDatatypeData>;
/// `CReapplyConceptSaturationLabelSet*`.
pub type ReapplyConceptSaturationLabelSetId = Id<ReapplyConceptSaturationLabelSet>;
/// `CImplicationReapplyConceptSaturationDescriptor*`.
pub type ImplicationReapplyConceptSaturationDescriptorId =
    Id<ImplicationReapplyConceptSaturationDescriptor>;
/// `CSaturationModifiedProcessUpdateLinker*`.
pub type SaturationModifiedProcessUpdateLinkerId = Id<SaturationModifiedProcessUpdateLinker>;

// ===========================================================================
// CConceptSaturationDescriptor  (CNegLinkerBase<CConcept*,Self>)
// ===========================================================================

/// Port of `CConceptSaturationDescriptor`.
///
/// A negated-concept occurrence in a saturation node's label / clash chain. The
/// `CNegLinkerBase<CConcept*,Self>` base carries the concept (`getData()`), a
/// negation bit, and the intrusive self next-link.
pub struct ConceptSaturationDescriptor {
    /// `CNegLinkerBase` data (the described concept).
    pub concept: ConceptId,
    /// `CNegLinkerBase` negation bit.
    pub negated: bool,
    /// `CNegLinkerBase` intrusive next link (`getNextConceptDesciptor`).
    pub next: ConceptSaturationDescriptorId,
}

impl Default for ConceptSaturationDescriptor {
    fn default() -> Self {
        ConceptSaturationDescriptor {
            concept: ConceptId::NONE,
            negated: false,
            next: ConceptSaturationDescriptorId::NONE,
        }
    }
}

impl ConceptSaturationDescriptor {
    /// Port of `CConceptSaturationDescriptor::CConceptSaturationDescriptor`.
    pub fn new() -> Self {
        Self::default()
    }
    /// Port of `initConceptSaturationDescriptor` (`initNegLinker(concept,negated)`).
    pub fn init_concept_saturation_descriptor(
        &mut self,
        concept: ConceptId,
        negated: bool,
    ) -> &mut Self {
        self.concept = concept;
        self.negated = negated;
        self
    }
    /// Port of `getConcept` (`return getData()`).
    pub fn get_concept(&self) -> ConceptId {
        self.concept
    }
    /// `CNegLinkerBase` negation bit (`getNegation`).
    pub fn get_negation(&self) -> bool {
        self.negated
    }
    /// Port of `getConceptTag` (`return getData()->getConceptTag()`).
    pub fn get_concept_tag(&self, onto: &OntologyArenas) -> Cint64 {
        onto.concept(self.concept).get_concept_tag()
    }
    /// Port of `getTerminologyTag` (`return getData()->getTerminologyTag()`).
    pub fn get_terminology_tag(&self, onto: &OntologyArenas) -> Cint64 {
        onto.concept(self.concept).get_terminology_tag()
    }
    /// Port of `getNextConceptDesciptor` (`return getNext()`).
    pub fn get_next_concept_desciptor(&self) -> ConceptSaturationDescriptorId {
        self.next
    }
    /// `CNegLinkerBase::setNext`.
    pub fn set_next(&mut self, next: ConceptSaturationDescriptorId) -> &mut Self {
        self.next = next;
        self
    }
}

// ===========================================================================
// CConceptSaturationProcessLinker  (CLinkerBase<CConceptSaturationDescriptor*,Self>)
// ===========================================================================

/// Port of `CConceptSaturationProcessLinker`.
///
/// A queued concept-application linker carrying the concept saturation
/// descriptor to (re)apply. The `CLinkerBase` base carries the descriptor
/// (`getData()`) and the intrusive self next-link.
pub struct ConceptSaturationProcessLinker {
    /// `CLinkerBase` data (the carried concept saturation descriptor).
    pub data: ConceptSaturationDescriptorId,
    /// `CLinkerBase` intrusive next link.
    pub next: ConceptSaturationProcessLinkerId,
}

impl Default for ConceptSaturationProcessLinker {
    fn default() -> Self {
        ConceptSaturationProcessLinker {
            data: ConceptSaturationDescriptorId::NONE,
            next: ConceptSaturationProcessLinkerId::NONE,
        }
    }
}

impl ConceptSaturationProcessLinker {
    /// Port of `CConceptSaturationProcessLinker::CConceptSaturationProcessLinker`.
    pub fn new() -> Self {
        Self::default()
    }
    /// Port of `initConceptSaturationProcessLinker` (`initLinker(conPilDes)`).
    pub fn init_concept_saturation_process_linker(
        &mut self,
        con_pil_des: ConceptSaturationDescriptorId,
    ) -> &mut Self {
        self.data = con_pil_des;
        self
    }
    /// Port of `getConceptSaturationDescriptor` (`return getData()`).
    pub fn get_concept_saturation_descriptor(&self) -> ConceptSaturationDescriptorId {
        self.data
    }
    /// `CLinkerBase::getNext`.
    pub fn get_next(&self) -> ConceptSaturationProcessLinkerId {
        self.next
    }
    /// `CLinkerBase::setNext`.
    pub fn set_next(&mut self, next: ConceptSaturationProcessLinkerId) -> &mut Self {
        self.next = next;
        self
    }
}

// ===========================================================================
// CRoleSaturationProcessLinker  (CLinkerBase<CRole*,Self>)
// ===========================================================================

/// Port of `CRoleSaturationProcessLinker`.
///
/// A queued role-application linker carrying the role to (re)process.
pub struct RoleSaturationProcessLinker {
    /// `CLinkerBase` data (the carried role).
    pub data: RoleId,
    /// `CLinkerBase` intrusive next link.
    pub next: RoleSaturationProcessLinkerId,
}

impl Default for RoleSaturationProcessLinker {
    fn default() -> Self {
        RoleSaturationProcessLinker {
            data: RoleId::NONE,
            next: RoleSaturationProcessLinkerId::NONE,
        }
    }
}

impl RoleSaturationProcessLinker {
    /// Port of `CRoleSaturationProcessLinker::CRoleSaturationProcessLinker`.
    pub fn new() -> Self {
        Self::default()
    }
    /// Port of `initRoleProcessLinker` (`initLinker(role)`).
    pub fn init_role_process_linker(&mut self, role: RoleId) -> &mut Self {
        self.data = role;
        self
    }
    /// Port of `getRole` (`return getData()`).
    pub fn get_role(&self) -> RoleId {
        self.data
    }
    /// `CLinkerBase::getNext`.
    pub fn get_next(&self) -> RoleSaturationProcessLinkerId {
        self.next
    }
    /// `CLinkerBase::setNext`.
    pub fn set_next(&mut self, next: RoleSaturationProcessLinkerId) -> &mut Self {
        self.next = next;
        self
    }
}

// ===========================================================================
// CBackwardSaturationPropagationLink  (CLinkerBase<CRole*,Self> + source)
// ===========================================================================

/// Port of `CBackwardSaturationPropagationLink`.
///
/// An inverse-side propagation edge: the role (`getData()`) plus the source
/// saturation node the propagation came from.
pub struct BackwardSaturationPropagationLink {
    /// `CLinkerBase` data (the link role).
    pub role: RoleId,
    /// `mSourceIndividual`.
    pub source_individual: SatNodeId,
    /// `CLinkerBase` intrusive next link.
    pub next: BackwardSaturationPropagationLinkId,
}

impl Default for BackwardSaturationPropagationLink {
    fn default() -> Self {
        BackwardSaturationPropagationLink {
            role: RoleId::NONE,
            source_individual: SatNodeId::NONE,
            next: BackwardSaturationPropagationLinkId::NONE,
        }
    }
}

impl BackwardSaturationPropagationLink {
    /// Port of `CBackwardSaturationPropagationLink::CBackwardSaturationPropagationLink`
    /// (`mSourceIndividual = nullptr`).
    pub fn new() -> Self {
        Self::default()
    }
    /// Port of `initBackwardPropagationLink` (`setData(role); mSourceIndividual = sourceIndividual`).
    pub fn init_backward_propagation_link(
        &mut self,
        source_individual: SatNodeId,
        role: RoleId,
    ) -> &mut Self {
        self.role = role;
        self.source_individual = source_individual;
        self
    }
    /// Port of `getLinkRole` (`return getData()`).
    pub fn get_link_role(&self) -> RoleId {
        self.role
    }
    /// Port of `setLinkRole` (`setData(role)`).
    pub fn set_link_role(&mut self, role: RoleId) -> &mut Self {
        self.role = role;
        self
    }
    /// Port of `getSourceIndividual` (`return mSourceIndividual`).
    pub fn get_source_individual(&self) -> SatNodeId {
        self.source_individual
    }
    /// `CLinkerBase::getNext`.
    pub fn get_next(&self) -> BackwardSaturationPropagationLinkId {
        self.next
    }
    /// `CLinkerBase::setNext`.
    pub fn set_next(&mut self, next: BackwardSaturationPropagationLinkId) -> &mut Self {
        self.next = next;
        self
    }
}

// ===========================================================================
// CBackwardSaturationPropagationReapplyDescriptor
// ===========================================================================

/// Port of `CBackwardSaturationPropagationReapplyDescriptor`.
///
/// The reapply descriptor chain is carried by
/// `CRoleBackwardSaturationPropagationHashData`. The W132 updater slice only
/// needs the hash's backward-propagation link chain, but the descriptor is part of
/// the same Konclude data record and is ported here as the faithful satellite.
pub struct BackwardSaturationPropagationReapplyDescriptor {
    /// `CLinkerBase` data.
    pub concept_saturation_descriptor: ConceptSaturationDescriptorId,
    /// `CLinkerBase` intrusive next link.
    pub next: BackwardSaturationPropagationReapplyDescriptorId,
}

impl Default for BackwardSaturationPropagationReapplyDescriptor {
    fn default() -> Self {
        Self {
            concept_saturation_descriptor: ConceptSaturationDescriptorId::NONE,
            next: BackwardSaturationPropagationReapplyDescriptorId::NONE,
        }
    }
}

impl BackwardSaturationPropagationReapplyDescriptor {
    /// Port of `CBackwardSaturationPropagationReapplyDescriptor::CBackwardSaturationPropagationReapplyDescriptor`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `initBackwardPropagationReapplyDescriptor(CConceptSaturationDescriptor*)`.
    pub fn init_backward_propagation_reapply_descriptor(
        &mut self,
        con_des: ConceptSaturationDescriptorId,
    ) -> &mut Self {
        self.concept_saturation_descriptor = con_des;
        self.next = Self::default().next;
        self
    }

    /// Port of `initBackwardPropagationReapplyDescriptor(CBackwardSaturationPropagationReapplyDescriptor*)`.
    pub fn init_backward_propagation_reapply_descriptor_copy(
        &mut self,
        reapply_des: &BackwardSaturationPropagationReapplyDescriptor,
    ) -> &mut Self {
        self.concept_saturation_descriptor = reapply_des.concept_saturation_descriptor;
        self.next = reapply_des.next;
        self
    }

    /// Port of `getReapplyConceptSaturationDescriptor`.
    pub fn get_reapply_concept_saturation_descriptor(&self) -> ConceptSaturationDescriptorId {
        self.concept_saturation_descriptor
    }

    /// `CLinkerBase::getNext`.
    pub fn get_next(&self) -> BackwardSaturationPropagationReapplyDescriptorId {
        self.next
    }

    /// `CLinkerBase::setNext`.
    pub fn set_next(
        &mut self,
        next: BackwardSaturationPropagationReapplyDescriptorId,
    ) -> &mut Self {
        self.next = next;
        self
    }
}

// ===========================================================================
// CRoleBackwardSaturationPropagationHash(Data)
// ===========================================================================

/// Port of `CRoleBackwardSaturationPropagationHashData`.
#[derive(Clone)]
pub struct RoleBackwardSaturationPropagationHashData {
    /// `CBackwardSaturationPropagationLink* mLinkLinker`.
    pub link_linker: BackwardSaturationPropagationLinkId,
    /// `CBackwardSaturationPropagationReapplyDescriptor* mReapplyLinker`.
    pub reapply_linker: BackwardSaturationPropagationReapplyDescriptorId,
    /// `bool mSelfConnected`.
    pub self_connected: bool,
    /// `mutable bool mRoleALLConceptsProcessingQueued`.
    pub role_all_concepts_processing_queued: bool,
    /// `mutable bool mRolePredecessorMergingQueuingRequired`.
    pub role_predecessor_merging_queuing_required: bool,
    /// `mutable bool mRolePredecessorMergingProcessingQueued`.
    pub role_predecessor_merging_processing_queued: bool,
}

impl Default for RoleBackwardSaturationPropagationHashData {
    fn default() -> Self {
        Self {
            link_linker: BackwardSaturationPropagationLinkId::NONE,
            reapply_linker: BackwardSaturationPropagationReapplyDescriptorId::NONE,
            self_connected: false,
            role_all_concepts_processing_queued: false,
            role_predecessor_merging_queuing_required: false,
            role_predecessor_merging_processing_queued: false,
        }
    }
}

impl RoleBackwardSaturationPropagationHashData {
    /// Port of `CRoleBackwardSaturationPropagationHashData::CRoleBackwardSaturationPropagationHashData`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of the C++ copy constructor.
    pub fn copy_without_links(data: &Self) -> Self {
        Self {
            link_linker: BackwardSaturationPropagationLinkId::NONE,
            reapply_linker: data.reapply_linker,
            self_connected: data.self_connected,
            role_all_concepts_processing_queued: false,
            role_predecessor_merging_queuing_required: false,
            role_predecessor_merging_processing_queued: false,
        }
    }
}

/// Port of `CRoleBackwardSaturationPropagationHash`.
pub struct RoleBackwardSaturationPropagationHash {
    /// `CProcessContext* mContext`.
    pub context: Cint64,
    /// `CPROCESSHASH<CRole*, CRoleBackwardSaturationPropagationHashData>`.
    pub role_back_prop_data_hash: HashMap<RoleId, RoleBackwardSaturationPropagationHashData>,
    /// `bool mSelfConnected`.
    pub self_connected: bool,
}

impl Default for RoleBackwardSaturationPropagationHash {
    fn default() -> Self {
        Self {
            context: INVALID,
            role_back_prop_data_hash: HashMap::new(),
            self_connected: false,
        }
    }
}

impl RoleBackwardSaturationPropagationHash {
    /// Port of `CRoleBackwardSaturationPropagationHash::CRoleBackwardSaturationPropagationHash`.
    pub fn new(context: Cint64) -> Self {
        Self {
            context,
            ..Default::default()
        }
    }

    /// Port of `initRoleBackwardSaturationPropagationHash`.
    pub fn init_role_backward_saturation_propagation_hash(&mut self) -> &mut Self {
        self.role_back_prop_data_hash.clear();
        self.self_connected = false;
        self
    }

    /// Port of `getBackwardPropagationBackwardPropagationConceptDescriptor`.
    pub fn get_backward_propagation_backward_propagation_concept_descriptor(
        &self,
        role: RoleId,
    ) -> BackwardSaturationPropagationReapplyDescriptorId {
        self.role_back_prop_data_hash
            .get(&role)
            .map(|data| data.reapply_linker)
            .unwrap_or(BackwardSaturationPropagationReapplyDescriptorId::NONE)
    }

    /// Port of `getRoleBackwardPropagationDataHash`.
    pub fn get_role_backward_propagation_data_hash(
        &self,
    ) -> &HashMap<RoleId, RoleBackwardSaturationPropagationHashData> {
        &self.role_back_prop_data_hash
    }

    /// Mutable counterpart of `getRoleBackwardPropagationDataHash`.
    pub fn get_role_backward_propagation_data_hash_mut(
        &mut self,
    ) -> &mut HashMap<RoleId, RoleBackwardSaturationPropagationHashData> {
        &mut self.role_back_prop_data_hash
    }
}

// ===========================================================================
// CSaturationSuccessorData
// ===========================================================================

/// Port of `CSaturationSuccessorData`.
///
/// A per-successor record in a `CLinkedRoleSaturationSuccessorData`'s
/// successor-node map: counts, the successor saturation node, the creation-role
/// chain (`CXNegLinker<CRole*>*` → `Vec<NegLink<RoleId>>`), and the intrusive
/// next-link in the per-role bucket.
pub struct SaturationSuccessorData {
    /// `mSuccCount`.
    pub succ_count: Cint64,
    /// `mActiveCount` (declared `cint64`; the ctor seeds it `false` → `0`).
    pub active_count: Cint64,
    /// `mExtension`.
    pub extension: bool,
    /// `mVALUENominalConnection`.
    pub value_nominal_connection: bool,
    /// `mVALUENominalID`.
    pub value_nominal_id: Cint64,
    /// `mSuccIndiNode`.
    pub succ_indi_node: SatNodeId,
    /// `mNextLink`.
    pub next_link: SaturationSuccessorDataId,
    /// `mCreationRoleLinker` (`CXNegLinker<CRole*>*` → negated-role chain).
    pub creation_role_linker: Vec<NegLink<RoleId>>,
}

impl Default for SaturationSuccessorData {
    fn default() -> Self {
        SaturationSuccessorData {
            succ_count: 0,
            active_count: 0,
            extension: false,
            value_nominal_connection: false,
            value_nominal_id: 0,
            succ_indi_node: SatNodeId::NONE,
            next_link: SaturationSuccessorDataId::NONE,
            creation_role_linker: Vec::new(),
        }
    }
}

impl SaturationSuccessorData {
    /// Port of `CSaturationSuccessorData::CSaturationSuccessorData`.
    pub fn new() -> Self {
        Self::default()
    }
    /// Port of `getSuccessorIndividualNode`.
    pub fn get_successor_individual_node(&self) -> SatNodeId {
        self.succ_indi_node
    }
    /// Port of `setSuccessorIndividualNode`.
    pub fn set_successor_individual_node(&mut self, succ_indi_node: SatNodeId) -> &mut Self {
        self.succ_indi_node = succ_indi_node;
        self
    }
    /// Port of `getSuccessorCount`.
    pub fn get_successor_count(&self) -> Cint64 {
        self.succ_count
    }
    /// Port of `setSuccessorCount`.
    pub fn set_successor_count(&mut self, succ_count: Cint64) -> &mut Self {
        self.succ_count = succ_count;
        self
    }
    /// Port of `getActiveCount`.
    pub fn get_active_count(&self) -> Cint64 {
        self.active_count
    }
    /// Port of `setActiveCount`.
    pub fn set_active_count(&mut self, active_count: Cint64) -> &mut Self {
        self.active_count = active_count;
        self
    }
    /// Port of `isActive`.
    pub fn is_active(&self) -> bool {
        self.active_count > 0
    }
    /// Port of `getNext`.
    pub fn get_next(&self) -> SaturationSuccessorDataId {
        self.next_link
    }
    /// Port of `setNext`.
    pub fn set_next(&mut self, next_link: SaturationSuccessorDataId) -> &mut Self {
        self.next_link = next_link;
        self
    }
}

/// Port of `CIndividualSaturationSuccessorLinkDataLinker`.
///
/// Konclude's linker is `CLinkerBase<CSaturationSuccessorData*, ...>`: the data
/// payload is a successor-data record and the base next pointer chains linkers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IndividualSaturationSuccessorLinkDataLinker {
    /// `CLinkerBase` data.
    pub successor_link_data: SaturationSuccessorDataId,
    /// Intrusive next pointer.
    pub next: IndividualSaturationSuccessorLinkDataLinkerId,
}

impl Default for IndividualSaturationSuccessorLinkDataLinker {
    fn default() -> Self {
        Self {
            successor_link_data: SaturationSuccessorDataId::NONE,
            next: IndividualSaturationSuccessorLinkDataLinkerId::NONE,
        }
    }
}

impl IndividualSaturationSuccessorLinkDataLinker {
    /// Port of `CIndividualSaturationSuccessorLinkDataLinker::CIndividualSaturationSuccessorLinkDataLinker`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `initSuccessorLinkDataLinker`.
    pub fn init_successor_link_data_linker(
        &mut self,
        succ_link_data: SaturationSuccessorDataId,
    ) -> &mut Self {
        self.successor_link_data = succ_link_data;
        self.next = IndividualSaturationSuccessorLinkDataLinkerId::NONE;
        self
    }

    /// Port of `CLinkerBase::getData`.
    pub fn get_data(&self) -> SaturationSuccessorDataId {
        self.successor_link_data
    }

    /// Port of `CLinkerBase::getNext`.
    pub fn get_next(&self) -> IndividualSaturationSuccessorLinkDataLinkerId {
        self.next
    }

    /// Port of `CLinkerBase::setNext`.
    pub fn set_next(&mut self, next: IndividualSaturationSuccessorLinkDataLinkerId) -> &mut Self {
        self.next = next;
        self
    }

    /// Port of `CLinkerBase::clearNext`.
    pub fn clear_next(&mut self) -> &mut Self {
        self.next = IndividualSaturationSuccessorLinkDataLinkerId::NONE;
        self
    }
}

// ===========================================================================
// CLinkedRoleSaturationSuccessorData
// ===========================================================================

/// Port of `CLinkedRoleSaturationSuccessorData`.
///
/// The per-role bucket in a `CLinkedRoleSaturationSuccessorHash`: a
/// `CPROCESSMAP<cint64,CSaturationSuccessorData*>` keyed by successor node id,
/// the last successor link, the count, the (opaque) successor extension data,
/// and the ALL/FUNCTIONAL processing-queue flags.
pub struct LinkedRoleSaturationSuccessorData {
    /// `mSuccNodeDataMap` (`CPROCESSMAP<cint64,CSaturationSuccessorData*>`).
    pub succ_node_data_map: HashMap<Cint64, SaturationSuccessorDataId>,
    /// `mLastLink`.
    pub last_link: SaturationSuccessorDataId,
    /// `mSuccCount`.
    pub succ_count: Cint64,
    /// `mExtensionData`.
    pub extension_data: SaturationSuccessorExtensionDataId,
    /// `mRoleALLConceptsProcessingQueued`.
    pub role_all_concepts_processing_queued: bool,
    /// `mRoleFUNCTIONALConceptsProcessingQueued`.
    pub role_functional_concepts_processing_queued: bool,
    /// `mRoleFUNCTIONALConceptsQueuingRequired`.
    pub role_functional_concepts_queuing_required: bool,
    /// `mRoleALLConceptsQueuingRequired`.
    pub role_all_concepts_queuing_required: bool,
}

impl Default for LinkedRoleSaturationSuccessorData {
    fn default() -> Self {
        LinkedRoleSaturationSuccessorData {
            succ_node_data_map: HashMap::new(),
            last_link: SaturationSuccessorDataId::NONE,
            succ_count: 0,
            extension_data: SaturationSuccessorExtensionDataId::NONE,
            role_all_concepts_processing_queued: false,
            role_functional_concepts_processing_queued: false,
            role_functional_concepts_queuing_required: false,
            role_all_concepts_queuing_required: false,
        }
    }
}

impl LinkedRoleSaturationSuccessorData {
    /// Port of `CLinkedRoleSaturationSuccessorData::CLinkedRoleSaturationSuccessorData`.
    pub fn new() -> Self {
        Self::default()
    }
    /// Port of `getSuccessorNodeDataMap` (`return &mSuccNodeDataMap`).
    pub fn get_successor_node_data_map(&self) -> &HashMap<Cint64, SaturationSuccessorDataId> {
        &self.succ_node_data_map
    }
    /// Mutable accessor for the successor-node map (`create == true` path).
    pub fn get_successor_node_data_map_mut(
        &mut self,
    ) -> &mut HashMap<Cint64, SaturationSuccessorDataId> {
        &mut self.succ_node_data_map
    }
    /// Port of `getLastSuccessorLinkData` (`return mLastLink`).
    pub fn get_last_successor_link_data(&self) -> SaturationSuccessorDataId {
        self.last_link
    }
    /// Port of `getSuccessorCount` (`return mSuccCount`).
    pub fn get_successor_count(&self) -> Cint64 {
        self.succ_count
    }
    /// Port of `setSuccessorCount`.
    pub fn set_successor_count(&mut self, succ_count: Cint64) -> &mut Self {
        self.succ_count = succ_count;
        self
    }
    /// Port of `setLastSuccessorLinkData`.
    pub fn set_last_successor_link_data(
        &mut self,
        last_link: SaturationSuccessorDataId,
    ) -> &mut Self {
        self.last_link = last_link;
        self
    }
    /// Port of `getSucessorExtensionData` (`return mExtensionData`).
    pub fn get_sucessor_extension_data(&self) -> SaturationSuccessorExtensionDataId {
        self.extension_data
    }
}

// ===========================================================================
// CSaturationSuccessorExtensionData
// ===========================================================================

/// Port of `CSaturationSuccessorExtensionData`.
pub struct SaturationSuccessorExtensionData {
    /// `mProcessContext`.
    pub process_context: Cint64,
    /// `mLastExaminedLinkLinker`.
    pub last_examined_link_linker: SaturationSuccessorDataId,
    /// `mLastExaminedALLConReaDes`.
    pub last_examined_all_concept_reapply_descriptor:
        BackwardSaturationPropagationReapplyDescriptorId,
}

impl Default for SaturationSuccessorExtensionData {
    fn default() -> Self {
        Self {
            process_context: INVALID,
            last_examined_link_linker: SaturationSuccessorDataId::NONE,
            last_examined_all_concept_reapply_descriptor:
                BackwardSaturationPropagationReapplyDescriptorId::NONE,
        }
    }
}

impl SaturationSuccessorExtensionData {
    /// Port of `CSaturationSuccessorExtensionData(CProcessContext*)`.
    pub fn new(process_context: Cint64) -> Self {
        Self {
            process_context,
            ..Default::default()
        }
    }

    /// Port of `initSuccessorExtensionData`.
    pub fn init_successor_extension_data(&mut self) -> &mut Self {
        self.last_examined_all_concept_reapply_descriptor =
            BackwardSaturationPropagationReapplyDescriptorId::NONE;
        self.last_examined_link_linker = SaturationSuccessorDataId::NONE;
        self
    }

    /// Port of `getLastExaminedALLConceptReapplyDescriptor`.
    pub fn get_last_examined_all_concept_reapply_descriptor(
        &self,
    ) -> BackwardSaturationPropagationReapplyDescriptorId {
        self.last_examined_all_concept_reapply_descriptor
    }

    /// Port of `setLastExaminedALLConceptReapplyDescriptor`.
    pub fn set_last_examined_all_concept_reapply_descriptor(
        &mut self,
        rea_des: BackwardSaturationPropagationReapplyDescriptorId,
    ) -> &mut Self {
        self.last_examined_all_concept_reapply_descriptor = rea_des;
        self
    }

    /// Port of `getLastExaminedLinkLinker`.
    pub fn get_last_examined_link_linker(&self) -> SaturationSuccessorDataId {
        self.last_examined_link_linker
    }

    /// Port of `setLastExaminedLinkLinker`.
    pub fn set_last_examined_link_linker(
        &mut self,
        link_linker: SaturationSuccessorDataId,
    ) -> &mut Self {
        self.last_examined_link_linker = link_linker;
        self
    }
}

// ===========================================================================
// CLinkedRoleSaturationSuccessorHash
// ===========================================================================

/// Port of `CLinkedRoleSaturationSuccessorHash`.
///
/// The per-node role→successor-bucket hash
/// (`CPROCESSHASH<CRole*,CLinkedRoleSaturationSuccessorData*>`) plus the
/// last-examined concept-descriptor / role-assertion-linker cursors.
///
/// KONCLUDE-PORT-NOTE[api]: the mutating successor-management surface
/// (`addLinkedSuccessor`, `hasActiveLinkedSuccessor`, `deactivateLinkedSuccessor`,
/// `reduceLinkedSuccessorCount`, …) walks the (opaque) `CSaturationSuccessorExtensionData`
/// / `CSaturationSuccessorRoleAssertionLinker` and allocates `CSaturationSuccessorData`
/// from the pool; those bodies are `W4.5-DEFER` until the extension/assertion-linker
/// sub-structs port. The struct + ctor + map/cursor accessors are ported here so
/// the per-node extension data and the s-units can hold and thread the hash.
pub struct LinkedRoleSaturationSuccessorHash {
    /// `mRoleSuccDataHash` (`CPROCESSHASH<CRole*,CLinkedRoleSaturationSuccessorData*>`).
    pub role_succ_data_hash: HashMap<RoleId, LinkedRoleSaturationSuccessorDataId>,
    /// `mLastExaminedConDes`.
    pub last_examined_con_des: ConceptSaturationDescriptorId,
    /// `mLastExaminedRoleAssLinker` (`CSaturationSuccessorRoleAssertionLinker*`, opaque).
    pub last_examined_role_ass_linker: Cint64,
}

impl Default for LinkedRoleSaturationSuccessorHash {
    fn default() -> Self {
        LinkedRoleSaturationSuccessorHash {
            role_succ_data_hash: HashMap::new(),
            last_examined_con_des: ConceptSaturationDescriptorId::NONE,
            last_examined_role_ass_linker: INVALID,
        }
    }
}

impl LinkedRoleSaturationSuccessorHash {
    /// Port of `CLinkedRoleSaturationSuccessorHash::CLinkedRoleSaturationSuccessorHash`.
    pub fn new() -> Self {
        Self::default()
    }
    /// Port of `initRoleSuccessorHash` (clears the per-test state).
    pub fn init_role_successor_hash(&mut self) -> &mut Self {
        self.role_succ_data_hash.clear();
        self.last_examined_con_des = ConceptSaturationDescriptorId::NONE;
        self.last_examined_role_ass_linker = INVALID;
        self
    }
    /// Port of `copyRoleSuccessorHash` (copy-construct the per-test state).
    pub fn copy_role_successor_hash(
        &mut self,
        copy: &LinkedRoleSaturationSuccessorHash,
    ) -> &mut Self {
        self.role_succ_data_hash = copy.role_succ_data_hash.clone();
        self.last_examined_con_des = copy.last_examined_con_des;
        self.last_examined_role_ass_linker = copy.last_examined_role_ass_linker;
        self
    }
    /// Port of `getLinkedRoleSuccessorHash` (`return &mRoleSuccDataHash`).
    pub fn get_linked_role_successor_hash(
        &self,
    ) -> &HashMap<RoleId, LinkedRoleSaturationSuccessorDataId> {
        &self.role_succ_data_hash
    }
    /// Port of `hasLinkedRoleSuccessorData` (`return mRoleSuccDataHash.contains(role)`).
    pub fn has_linked_role_successor_data(&self, role: RoleId) -> bool {
        self.role_succ_data_hash.contains_key(&role)
    }
    /// Port of `getLinkedRoleSuccessorData(role,false)`.
    ///
    /// The `create == true` overload allocates through `ProcessContext`; see
    /// `ProcessContext::linked_role_successor_data`.
    pub fn get_linked_role_successor_data(
        &self,
        role: RoleId,
    ) -> LinkedRoleSaturationSuccessorDataId {
        self.role_succ_data_hash
            .get(&role)
            .copied()
            .unwrap_or(LinkedRoleSaturationSuccessorDataId::NONE)
    }
    /// Port of `getLastExaminedConceptDescriptor` (`return mLastExaminedConDes`).
    pub fn get_last_examined_concept_descriptor(&self) -> ConceptSaturationDescriptorId {
        self.last_examined_con_des
    }
    /// Port of `setLastExaminedConceptDescriptor` (`mLastExaminedConDes = conDes`).
    pub fn set_last_examined_concept_descriptor(
        &mut self,
        con_des: ConceptSaturationDescriptorId,
    ) -> &mut Self {
        self.last_examined_con_des = con_des;
        self
    }
    /// Port of `getLastExaminedRoleAssertionLinker` (`return mLastExaminedRoleAssLinker`).
    pub fn get_last_examined_role_assertion_linker(&self) -> Cint64 {
        self.last_examined_role_ass_linker
    }
    /// Port of `setLastExaminedRoleAssertionLinker` (`mLastExaminedRoleAssLinker = roleAssLinker`).
    pub fn set_last_examined_role_assertion_linker(
        &mut self,
        role_ass_linker: Cint64,
    ) -> &mut Self {
        self.last_examined_role_ass_linker = role_ass_linker;
        self
    }

    // W4.5-DEFER[api]: the mutating successor-management surface
    // (`getLinkedRoleSuccessorData(role,create)`, `hasLinkedSuccessor`,
    // `hasActiveLinkedSuccessor`, `addLinkedSuccessor`, `addLinkedVALUESuccessor`,
    // `deactivateLinkedSuccessor`, `reduceLinkedSuccessorCount`,
    // `increaseLinkedSuccessorCount`, `addExtensionSuccessor`,
    // `setSuccessorMergedCreation`, `hasActiveCreationRole`) needs the
    // `CSaturationSuccessorExtensionData` port + `&mut ProcessContext` to allocate
    // `CSaturationSuccessorData`. Faithful bodies land with those sub-structs.
}

// ===========================================================================
// CLinkedDataValueAssertionSaturationData
// ===========================================================================

/// Port of the anonymous `CXLinker<CRole*>` chain owned by
/// `CLinkedDataValueAssertionSaturationData`.
pub struct DataValueRoleAssertionLinker {
    /// `CLinkerBase` data (`CRole*`).
    pub data: RoleId,
    /// Intrusive next link.
    pub next: DataValueRoleAssertionLinkerId,
}

impl Default for DataValueRoleAssertionLinker {
    fn default() -> Self {
        DataValueRoleAssertionLinker {
            data: RoleId::NONE,
            next: DataValueRoleAssertionLinkerId::NONE,
        }
    }
}

impl DataValueRoleAssertionLinker {
    /// Port of `CXLinker<CRole*>::CXLinker`.
    pub fn new() -> Self {
        Self::default()
    }
    /// Port of `initLinker(dataRole)`.
    pub fn init_linker(&mut self, data_role: RoleId) -> &mut Self {
        self.data = data_role;
        self.next = DataValueRoleAssertionLinkerId::NONE;
        self
    }
    /// Port of `getData()`.
    pub fn get_data(&self) -> RoleId {
        self.data
    }
    /// Typed convenience alias for the carried `CRole*`.
    pub fn get_role(&self) -> RoleId {
        self.data
    }
    /// Port of `getNext()`.
    pub fn get_next(&self) -> DataValueRoleAssertionLinkerId {
        self.next
    }
    /// Port of `setNext(next)`.
    pub fn set_next(&mut self, next: DataValueRoleAssertionLinkerId) -> &mut Self {
        self.next = next;
        self
    }
}

/// Port of `CLinkedDataValueAssertionSaturationData`.
///
/// Konclude stores only a role-linker chain here. The `CDataLiteral*` parameter
/// of `addDataValueAssertion` is unused in the C++ implementation; the Rust
/// context helper keeps it as an opaque `Cint64` argument and ignores it
/// likewise.
pub struct LinkedDataValueAssertionSaturationData {
    /// `mContext` (opaque per-test owner handle).
    pub process_context: Cint64,
    /// `mDataRoleLinker`.
    pub data_role_linker: DataValueRoleAssertionLinkerId,
}

impl Default for LinkedDataValueAssertionSaturationData {
    fn default() -> Self {
        LinkedDataValueAssertionSaturationData {
            process_context: INVALID,
            data_role_linker: DataValueRoleAssertionLinkerId::NONE,
        }
    }
}

impl LinkedDataValueAssertionSaturationData {
    /// Port of `CLinkedDataValueAssertionSaturationData(CProcessContext*)`.
    pub fn new(process_context: Cint64) -> Self {
        LinkedDataValueAssertionSaturationData {
            process_context,
            ..Default::default()
        }
    }
    /// Port of `initDataValueAssertionData`.
    pub fn init_data_value_assertion_data(&mut self) -> &mut Self {
        self.data_role_linker = DataValueRoleAssertionLinkerId::NONE;
        self
    }
    /// Port of `copyDataValueAssertionData`.
    ///
    /// The C++ copy is shallow: it copies the head pointer and does not clone the
    /// linker chain.
    pub fn copy_data_value_assertion_data(
        &mut self,
        copy_data_value_assertion_data: &Self,
    ) -> &mut Self {
        self.data_role_linker = copy_data_value_assertion_data.data_role_linker;
        self
    }
    /// Port of `getDataValueRoleAssertionLinker`.
    pub fn get_data_value_role_assertion_linker(&self) -> DataValueRoleAssertionLinkerId {
        self.data_role_linker
    }
}

// ===========================================================================
// CSaturationSuccessorRoleAssertionLinker
// ===========================================================================

/// Port of `CSaturationSuccessorRoleAssertionLinker`.
pub struct SaturationSuccessorRoleAssertionLinker {
    /// `CLinkerBase` data (`CIndividualSaturationProcessNode*`).
    pub destination_node: SatNodeId,
    /// `CLinkerBase` intrusive next link.
    pub next: SaturationSuccessorRoleAssertionLinkerId,
    /// `mRole`.
    pub role: RoleId,
    /// `mRoleNegation`.
    pub role_negation: bool,
}

impl Default for SaturationSuccessorRoleAssertionLinker {
    fn default() -> Self {
        SaturationSuccessorRoleAssertionLinker {
            destination_node: SatNodeId::NONE,
            next: SaturationSuccessorRoleAssertionLinkerId::NONE,
            role: RoleId::NONE,
            role_negation: false,
        }
    }
}

impl SaturationSuccessorRoleAssertionLinker {
    /// Port of `CSaturationSuccessorRoleAssertionLinker::CSaturationSuccessorRoleAssertionLinker`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `initSaturationSuccessorRoleAssertionLinker`.
    pub fn init_saturation_successor_role_assertion_linker(
        &mut self,
        indi_sat_node: SatNodeId,
        role: RoleId,
        role_negation: bool,
    ) -> &mut Self {
        self.destination_node = indi_sat_node;
        self.next = SaturationSuccessorRoleAssertionLinkerId::NONE;
        self.role = role;
        self.role_negation = role_negation;
        self
    }

    /// Port of `getAssertionRole`.
    pub fn get_assertion_role(&self) -> RoleId {
        self.role
    }

    /// Port of `getAssertionRoleNegation`.
    pub fn get_assertion_role_negation(&self) -> bool {
        self.role_negation
    }

    /// Port of `getAssertionDestinationNode`.
    pub fn get_assertion_destination_node(&self) -> SatNodeId {
        self.destination_node
    }

    /// Port of `getNext`.
    pub fn get_next(&self) -> SaturationSuccessorRoleAssertionLinkerId {
        self.next
    }

    /// Port of `setNext`.
    pub fn set_next(&mut self, next: SaturationSuccessorRoleAssertionLinkerId) -> &mut Self {
        self.next = next;
        self
    }
}

// ===========================================================================
// CCriticalPredecessorRoleCardinalityData / Hash
// ===========================================================================

/// Port of `CCriticalPredecessorRoleCardinalityData`.
pub struct CriticalPredecessorRoleCardinalityData {
    /// `mUnproblematicConceptLinker` (`CXNegLinker<CConcept*>*`).
    pub unproblematic_concept_linker: Vec<NegLink<ConceptId>>,
}

impl Default for CriticalPredecessorRoleCardinalityData {
    fn default() -> Self {
        CriticalPredecessorRoleCardinalityData {
            unproblematic_concept_linker: Vec::new(),
        }
    }
}

impl CriticalPredecessorRoleCardinalityData {
    /// Port of `CCriticalPredecessorRoleCardinalityData::CCriticalPredecessorRoleCardinalityData`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port-facing read of `mUnproblematicConceptLinker`.
    pub fn get_unproblematic_concept_linker(&self) -> &[NegLink<ConceptId>] {
        &self.unproblematic_concept_linker
    }
}

/// Port of `CCriticalPredecessorRoleCardinalityHash`.
pub struct CriticalPredecessorRoleCardinalityHash {
    /// `mContext`.
    pub process_context: Cint64,
    /// `mCriticalPredecessorRoleDataHash`.
    pub critical_predecessor_role_data_hash:
        HashMap<RoleId, CriticalPredecessorRoleCardinalityDataId>,
}

impl Default for CriticalPredecessorRoleCardinalityHash {
    fn default() -> Self {
        CriticalPredecessorRoleCardinalityHash {
            process_context: INVALID,
            critical_predecessor_role_data_hash: HashMap::new(),
        }
    }
}

impl CriticalPredecessorRoleCardinalityHash {
    /// Port of `CCriticalPredecessorRoleCardinalityHash(CProcessContext*)`.
    pub fn new(process_context: Cint64) -> Self {
        CriticalPredecessorRoleCardinalityHash {
            process_context,
            ..Default::default()
        }
    }

    /// Port of `initCriticalPredecessorRoleCardinalityHash`.
    pub fn init_critical_predecessor_role_cardinality_hash(&mut self) -> &mut Self {
        self.critical_predecessor_role_data_hash.clear();
        self
    }

    /// Port of `copyCriticalPredecessorRoleCardinalityHash`.
    pub fn copy_critical_predecessor_role_cardinality_hash(
        &mut self,
        copy_role_succ_hash: &Self,
    ) -> &mut Self {
        self.critical_predecessor_role_data_hash = copy_role_succ_hash
            .critical_predecessor_role_data_hash
            .clone();
        self
    }

    /// Port of `getCriticalPredecessorRoleCardinalityData`.
    pub fn get_critical_predecessor_role_cardinality_data(
        &self,
        role: RoleId,
    ) -> CriticalPredecessorRoleCardinalityDataId {
        self.critical_predecessor_role_data_hash
            .get(&role)
            .copied()
            .unwrap_or(CriticalPredecessorRoleCardinalityDataId::NONE)
    }
}

// ===========================================================================
// CSaturationDisjunctCommonConceptCountHash / Extraction data
// ===========================================================================

/// Port of `CSaturationDisjunctCommonConceptCountHashData`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SaturationDisjunctCommonConceptCountHashData {
    /// `mConceptCount`.
    pub concept_count: Cint64,
    /// `mConcept`.
    pub concept: ConceptId,
    /// `mNegation`.
    pub negation: bool,
}

impl Default for SaturationDisjunctCommonConceptCountHashData {
    fn default() -> Self {
        SaturationDisjunctCommonConceptCountHashData {
            concept_count: 0,
            concept: ConceptId::NONE,
            negation: false,
        }
    }
}

impl SaturationDisjunctCommonConceptCountHashData {
    /// Port of `CSaturationDisjunctCommonConceptCountHashData::CSaturationDisjunctCommonConceptCountHashData`.
    pub fn new() -> Self {
        Self::default()
    }
}

/// Port of `CSaturationDisjunctCommonConceptCountHash`.
pub struct SaturationDisjunctCommonConceptCountHash {
    /// `mProcessContext`.
    pub process_context: Cint64,
    /// `mCommonConceptCountHash`.
    pub common_concept_count_hash: HashMap<Cint64, SaturationDisjunctCommonConceptCountHashData>,
    /// `mDisjunctCount`.
    pub disjunct_count: Cint64,
}

impl Default for SaturationDisjunctCommonConceptCountHash {
    fn default() -> Self {
        SaturationDisjunctCommonConceptCountHash {
            process_context: INVALID,
            common_concept_count_hash: HashMap::new(),
            disjunct_count: 0,
        }
    }
}

impl SaturationDisjunctCommonConceptCountHash {
    /// Port of `CSaturationDisjunctCommonConceptCountHash(CProcessContext*)`.
    pub fn new(process_context: Cint64) -> Self {
        SaturationDisjunctCommonConceptCountHash {
            process_context,
            ..Default::default()
        }
    }

    /// Port of `initCommonConceptCountHash`.
    pub fn init_common_concept_count_hash(&mut self) -> &mut Self {
        self.common_concept_count_hash.clear();
        self.disjunct_count = 0;
        self
    }

    /// Port of `setDisjunctCount`.
    pub fn set_disjunct_count(&mut self, disjunct_count: Cint64) -> &mut Self {
        self.disjunct_count = disjunct_count;
        self
    }

    /// Port of `getCommonConceptCountHash`.
    pub fn get_common_concept_count_hash(
        &self,
    ) -> &HashMap<Cint64, SaturationDisjunctCommonConceptCountHashData> {
        &self.common_concept_count_hash
    }

    /// Port of `getCommonConceptCountData(cint64 conceptTag)`.
    pub fn get_common_concept_count_data_by_tag(
        &mut self,
        concept_tag: Cint64,
    ) -> &mut SaturationDisjunctCommonConceptCountHashData {
        self.common_concept_count_hash
            .entry(concept_tag)
            .or_insert_with(SaturationDisjunctCommonConceptCountHashData::new)
    }

    /// Port of `getCommonConceptCountData(CConcept* concept)`.
    pub fn get_common_concept_count_data_for_concept(
        &mut self,
        concept: ConceptId,
        onto: &OntologyArenas,
    ) -> &mut SaturationDisjunctCommonConceptCountHashData {
        let concept_tag = onto.concept(concept).get_concept_tag();
        self.get_common_concept_count_data_by_tag(concept_tag)
    }

    /// Port of `getCommonConceptCountData(CConceptSaturationDescriptor*)`.
    pub fn get_common_concept_count_data_for_descriptor(
        &mut self,
        con_sat_des: &ConceptSaturationDescriptor,
        onto: &OntologyArenas,
    ) -> &mut SaturationDisjunctCommonConceptCountHashData {
        self.get_common_concept_count_data_by_tag(con_sat_des.get_concept_tag(onto))
    }

    /// Port of `removeCommonConceptData`.
    pub fn remove_common_concept_data(
        &mut self,
        con_sat_des: &ConceptSaturationDescriptor,
        onto: &OntologyArenas,
    ) -> &mut Self {
        self.common_concept_count_hash
            .remove(&con_sat_des.get_concept_tag(onto));
        self
    }

    /// Port of `incCommonConceptCountReturnMaxReached`.
    pub fn inc_common_concept_count_return_max_reached(
        &mut self,
        con_sat_des: &ConceptSaturationDescriptor,
        onto: &OntologyArenas,
    ) -> bool {
        let concept_tag = con_sat_des.get_concept_tag(onto);
        let hash_data = self
            .common_concept_count_hash
            .entry(concept_tag)
            .or_insert_with(SaturationDisjunctCommonConceptCountHashData::new);
        if hash_data.concept.is_none() {
            hash_data.concept = con_sat_des.get_concept();
            hash_data.negation = con_sat_des.get_negation();
        }
        if hash_data.negation != con_sat_des.get_negation() {
            return false;
        }
        hash_data.concept_count += 1;
        hash_data.concept_count >= self.disjunct_count
    }
}

/// Port of `CSaturationDisjunctExtractionLinker`.
pub struct SaturationDisjunctExtractionLinker {
    /// `CLinkerBase` data (`CIndividualSaturationProcessNode*`).
    pub disjunct_node: SatNodeId,
    /// `CLinkerBase` intrusive next link.
    pub next: SaturationDisjunctExtractionLinkerId,
    /// `mLastExaminedConSatDes`.
    pub last_examined_con_sat_des: ConceptSaturationDescriptorId,
}

impl Default for SaturationDisjunctExtractionLinker {
    fn default() -> Self {
        SaturationDisjunctExtractionLinker {
            disjunct_node: SatNodeId::NONE,
            next: SaturationDisjunctExtractionLinkerId::NONE,
            last_examined_con_sat_des: ConceptSaturationDescriptorId::NONE,
        }
    }
}

impl SaturationDisjunctExtractionLinker {
    /// Port of `CSaturationDisjunctExtractionLinker::CSaturationDisjunctExtractionLinker`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `initSaturationDisjunctExtractionLinker`.
    pub fn init_saturation_disjunct_extraction_linker(
        &mut self,
        disj_node: SatNodeId,
        last_examined_con_sat_des: ConceptSaturationDescriptorId,
    ) -> &mut Self {
        self.last_examined_con_sat_des = last_examined_con_sat_des;
        self.disjunct_node = disj_node;
        self.next = SaturationDisjunctExtractionLinkerId::NONE;
        self
    }

    /// Port of `getLastExaminedConceptSaturationDescriptor`.
    pub fn get_last_examined_concept_saturation_descriptor(&self) -> ConceptSaturationDescriptorId {
        self.last_examined_con_sat_des
    }

    /// Port of `getDisjunctIndividualSaturationProcessNode`.
    pub fn get_disjunct_individual_saturation_process_node(&self) -> SatNodeId {
        self.disjunct_node
    }

    /// Port of `setLastExaminedConceptSaturationDescriptor`.
    pub fn set_last_examined_concept_saturation_descriptor(
        &mut self,
        con_sat_des: ConceptSaturationDescriptorId,
    ) -> &mut Self {
        self.last_examined_con_sat_des = con_sat_des;
        self
    }

    /// Port of `getNext`.
    pub fn get_next(&self) -> SaturationDisjunctExtractionLinkerId {
        self.next
    }

    /// Port of `setNext`.
    pub fn set_next(&mut self, next: SaturationDisjunctExtractionLinkerId) -> &mut Self {
        self.next = next;
        self
    }
}

/// Port of `CSaturationDisjunctCommonConceptExtractionData`.
pub struct SaturationDisjunctCommonConceptExtractionData {
    /// `mProcessContext`.
    pub process_context: Cint64,
    /// `mCommonConceptCountHash`.
    pub common_concept_count_hash: SaturationDisjunctCommonConceptCountHash,
    /// `mDisjunctExtractionLinker`.
    pub disjunct_extraction_linker: SaturationDisjunctExtractionLinkerId,
    /// `mExtConIndiProcessLinker`.
    pub ext_con_indi_process_linker: IndividualSaturationProcessNodeLinkerId,
}

impl Default for SaturationDisjunctCommonConceptExtractionData {
    fn default() -> Self {
        SaturationDisjunctCommonConceptExtractionData {
            process_context: INVALID,
            common_concept_count_hash: SaturationDisjunctCommonConceptCountHash::new(INVALID),
            disjunct_extraction_linker: SaturationDisjunctExtractionLinkerId::NONE,
            ext_con_indi_process_linker: IndividualSaturationProcessNodeLinkerId::NONE,
        }
    }
}

impl SaturationDisjunctCommonConceptExtractionData {
    /// Port of `CSaturationDisjunctCommonConceptExtractionData(CProcessContext*)`.
    pub fn new(process_context: Cint64) -> Self {
        SaturationDisjunctCommonConceptExtractionData {
            process_context,
            common_concept_count_hash: SaturationDisjunctCommonConceptCountHash::new(
                process_context,
            ),
            ..Default::default()
        }
    }

    /// Port of `initExtractionData`.
    pub fn init_extraction_data(&mut self, disjunction_indi_process_node: SatNodeId) -> &mut Self {
        self.common_concept_count_hash
            .init_common_concept_count_hash();
        let _ = disjunction_indi_process_node;
        self.ext_con_indi_process_linker = IndividualSaturationProcessNodeLinkerId::NONE;
        self.disjunct_extraction_linker = SaturationDisjunctExtractionLinkerId::NONE;
        self
    }

    /// Port of `getSaturationDisjunctCommonConceptCountHash`.
    pub fn get_saturation_disjunct_common_concept_count_hash(
        &self,
    ) -> &SaturationDisjunctCommonConceptCountHash {
        &self.common_concept_count_hash
    }

    /// Mutable counterpart for the in-place C++ hash reference.
    pub fn get_saturation_disjunct_common_concept_count_hash_mut(
        &mut self,
    ) -> &mut SaturationDisjunctCommonConceptCountHash {
        &mut self.common_concept_count_hash
    }

    /// Port of `getDisjunctIndividualNodeExtractionLinker`.
    pub fn get_disjunct_individual_node_extraction_linker(
        &self,
    ) -> SaturationDisjunctExtractionLinkerId {
        self.disjunct_extraction_linker
    }

    /// Port of `addDisjunctIndividualNodeExtractionLinker`.
    pub fn set_disjunct_individual_node_extraction_linker(
        &mut self,
        dis_node_ext_linker: SaturationDisjunctExtractionLinkerId,
    ) -> &mut Self {
        self.disjunct_extraction_linker = dis_node_ext_linker;
        self
    }

    /// Port of `getExtractionContinueProcessLinker`.
    pub fn get_extraction_continue_process_linker(
        &self,
    ) -> IndividualSaturationProcessNodeLinkerId {
        self.ext_con_indi_process_linker
    }

    /// Port-facing setter for `mExtConIndiProcessLinker`.
    pub fn set_extraction_continue_process_linker(
        &mut self,
        linker: IndividualSaturationProcessNodeLinkerId,
    ) -> &mut Self {
        self.ext_con_indi_process_linker = linker;
        self
    }

    /// Port of `isExtractionContinueProcessingQueued`.
    pub fn is_extraction_continue_processing_queued(
        &self,
        linkers: &Arena<IndividualSaturationProcessNodeLinker>,
    ) -> bool {
        self.ext_con_indi_process_linker.is_some()
            && linkers
                .get(self.ext_con_indi_process_linker)
                .is_processing_queued()
    }
}

// ===========================================================================
// CSaturationATMOSTSuccessorMergingHash / Data
// ===========================================================================

/// Port of `CSaturationATMOSTSuccessorMergingHashData`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SaturationAtmostSuccessorMergingHashData {
    /// `mInitialized`.
    pub initialized: bool,
    /// `mQueued`.
    pub queued: bool,
    /// `mSuccessorLinkMergingLinker`.
    pub successor_link_merging_linker: IndividualSaturationSuccessorLinkDataLinkerId,
    /// `mLastSuccessorNode`.
    pub last_successor_node: SatNodeId,
    /// `mLastSuccessorCreationRoleLinker` (`CXNegLinker<CRole*>*`).
    pub last_successor_creation_role_linker: Vec<NegLink<RoleId>>,
    /// `mFoundCardinality`.
    pub found_cardinality: Cint64,
    /// `mMergeableCardinality`.
    pub mergeable_cardinality: Cint64,
    /// `mMinCardinality`.
    pub min_cardinality: Cint64,
}

impl Default for SaturationAtmostSuccessorMergingHashData {
    fn default() -> Self {
        SaturationAtmostSuccessorMergingHashData {
            initialized: false,
            queued: false,
            successor_link_merging_linker: IndividualSaturationSuccessorLinkDataLinkerId::NONE,
            last_successor_node: SatNodeId::NONE,
            last_successor_creation_role_linker: Vec::new(),
            found_cardinality: 0,
            mergeable_cardinality: 0,
            min_cardinality: 0,
        }
    }
}

impl SaturationAtmostSuccessorMergingHashData {
    /// Port of `CSaturationATMOSTSuccessorMergingHashData::CSaturationATMOSTSuccessorMergingHashData`.
    pub fn new() -> Self {
        Self::default()
    }
}

/// Port of `CSaturationATMOSTSuccessorMergingHash`.
pub struct SaturationAtmostSuccessorMergingHash {
    /// `mProcessContext`.
    pub process_context: Cint64,
    /// `CPROCESSHASH<CConceptSaturationDescriptor*, CSaturationATMOSTSuccessorMergingHashData>`.
    pub atmost_concept_merging_data_hash:
        HashMap<ConceptSaturationDescriptorId, SaturationAtmostSuccessorMergingHashData>,
}

impl Default for SaturationAtmostSuccessorMergingHash {
    fn default() -> Self {
        SaturationAtmostSuccessorMergingHash {
            process_context: INVALID,
            atmost_concept_merging_data_hash: HashMap::new(),
        }
    }
}

impl SaturationAtmostSuccessorMergingHash {
    /// Port of `CSaturationATMOSTSuccessorMergingHash(CProcessContext*)`.
    pub fn new(process_context: Cint64) -> Self {
        SaturationAtmostSuccessorMergingHash {
            process_context,
            ..Default::default()
        }
    }

    /// Port of `initATMOSTConceptDescriptorMergingHash`.
    pub fn init_atmost_concept_descriptor_merging_hash(
        &mut self,
        prev_hash: Option<&Self>,
    ) -> &mut Self {
        self.atmost_concept_merging_data_hash.clear();
        if let Some(prev_hash) = prev_hash {
            self.atmost_concept_merging_data_hash
                .clone_from(&prev_hash.atmost_concept_merging_data_hash);
        }
        self
    }

    /// Port of `getATMOSTConceptMergingData`.
    pub fn get_atmost_concept_merging_data(
        &mut self,
        con_sat_des: ConceptSaturationDescriptorId,
    ) -> &mut SaturationAtmostSuccessorMergingHashData {
        self.atmost_concept_merging_data_hash
            .entry(con_sat_des)
            .or_insert_with(SaturationAtmostSuccessorMergingHashData::new)
    }
}

/// Port of `CSaturationATMOSTSuccessorMergingData`.
pub struct SaturationAtmostSuccessorMergingData {
    /// `mProcessContext`.
    pub process_context: Cint64,
    /// `mNewSuccessorHash`.
    pub new_successor_hash: LinkedRoleSaturationSuccessorHashId,
    /// `mMergingIndiProcessLinker`.
    pub merging_indi_process_linker: IndividualSaturationProcessNodeLinker,
    /// `mMergingConceptLinker`.
    pub merging_concept_linker: ConceptSaturationProcessLinkerId,
    /// `mConceptMergingDataHash`.
    pub concept_merging_data_hash: SaturationAtmostSuccessorMergingHashId,
    /// `mRemainMergeableCardHash`.
    pub remain_mergeable_card_hash: HashMap<SaturationSuccessorDataId, Cint64>,
    /// `mMergeDistintHash`.
    pub merge_distinct_hash: HashMap<SaturationSuccessorDataId, SaturationSuccessorDataId>,
    /// `mMergeDistintSet`.
    pub merge_distinct_set: HashSet<(SaturationSuccessorDataId, SaturationSuccessorDataId)>,
    /// Whether `mRemainMergeableCardHash` has been lazily materialized.
    pub has_remain_mergeable_card_hash: bool,
    /// Whether `mMergeDistintHash` has been lazily materialized.
    pub has_merge_distinct_hash: bool,
    /// Whether `mMergeDistintSet` has been lazily materialized.
    pub has_merge_distinct_set: bool,
}

impl Default for SaturationAtmostSuccessorMergingData {
    fn default() -> Self {
        SaturationAtmostSuccessorMergingData {
            process_context: INVALID,
            new_successor_hash: LinkedRoleSaturationSuccessorHashId::NONE,
            merging_indi_process_linker: IndividualSaturationProcessNodeLinker::new(),
            merging_concept_linker: ConceptSaturationProcessLinkerId::NONE,
            concept_merging_data_hash: SaturationAtmostSuccessorMergingHashId::NONE,
            remain_mergeable_card_hash: HashMap::new(),
            merge_distinct_hash: HashMap::new(),
            merge_distinct_set: HashSet::new(),
            has_remain_mergeable_card_hash: false,
            has_merge_distinct_hash: false,
            has_merge_distinct_set: false,
        }
    }
}

impl SaturationAtmostSuccessorMergingData {
    /// Port of `CSaturationATMOSTSuccessorMergingData(CProcessContext*)`.
    pub fn new(process_context: Cint64) -> Self {
        SaturationAtmostSuccessorMergingData {
            process_context,
            ..Default::default()
        }
    }

    /// Port of `initSuccessorMergingData`.
    pub fn init_successor_merging_data(&mut self, indi_process_node: SatNodeId) -> &mut Self {
        self.new_successor_hash = LinkedRoleSaturationSuccessorHashId::NONE;
        self.merging_indi_process_linker
            .init_process_node_linker(indi_process_node, false);
        self.concept_merging_data_hash = SaturationAtmostSuccessorMergingHashId::NONE;
        self.merging_concept_linker = ConceptSaturationProcessLinkerId::NONE;
        self.remain_mergeable_card_hash.clear();
        self.merge_distinct_hash.clear();
        self.merge_distinct_set.clear();
        self.has_remain_mergeable_card_hash = false;
        self.has_merge_distinct_hash = false;
        self.has_merge_distinct_set = false;
        self
    }

    /// Port of `getMergingIndividualProcessLinker`.
    pub fn get_merging_individual_process_linker(&self) -> &IndividualSaturationProcessNodeLinker {
        &self.merging_indi_process_linker
    }

    /// Mutable counterpart for `getMergingIndividualProcessLinker`.
    pub fn get_merging_individual_process_linker_mut(
        &mut self,
    ) -> &mut IndividualSaturationProcessNodeLinker {
        &mut self.merging_indi_process_linker
    }

    /// Port of `isMergingProcessingQueued`.
    pub fn is_merging_processing_queued(&self) -> bool {
        self.merging_indi_process_linker.is_processing_queued()
    }

    /// Port of `getMergingConceptLinker`.
    pub fn get_merging_concept_linker(&self) -> ConceptSaturationProcessLinkerId {
        self.merging_concept_linker
    }

    /// Port of `setMergingConceptLinker`.
    pub fn set_merging_concept_linker(
        &mut self,
        concept_linker: ConceptSaturationProcessLinkerId,
    ) -> &mut Self {
        self.merging_concept_linker = concept_linker;
        self
    }

    /// Port-facing read for `getATMOSTConceptMergingDataHash(false)`.
    pub fn get_atmost_concept_merging_data_hash(&self) -> SaturationAtmostSuccessorMergingHashId {
        self.concept_merging_data_hash
    }

    /// Port-facing read for `getMergedLinkedRoleSaturationSuccessorHash(false)`.
    pub fn get_merged_linked_role_saturation_successor_hash(
        &self,
    ) -> LinkedRoleSaturationSuccessorHashId {
        self.new_successor_hash
    }

    /// Port-facing read for `getRemainingMergeableCardinalityHash(false)`.
    pub fn get_remaining_mergeable_cardinality_hash(
        &self,
    ) -> Option<&HashMap<SaturationSuccessorDataId, Cint64>> {
        self.has_remain_mergeable_card_hash
            .then_some(&self.remain_mergeable_card_hash)
    }

    /// Mutable counterpart for `getRemainingMergeableCardinalityHash`.
    pub fn get_remaining_mergeable_cardinality_hash_mut(
        &mut self,
    ) -> Option<&mut HashMap<SaturationSuccessorDataId, Cint64>> {
        self.has_remain_mergeable_card_hash
            .then_some(&mut self.remain_mergeable_card_hash)
    }

    /// Port-facing read for `getMergingDistintHash(false)`.
    pub fn get_merging_distinct_hash(
        &self,
    ) -> Option<&HashMap<SaturationSuccessorDataId, SaturationSuccessorDataId>> {
        self.has_merge_distinct_hash
            .then_some(&self.merge_distinct_hash)
    }

    /// Mutable counterpart for `getMergingDistintHash`.
    pub fn get_merging_distinct_hash_mut(
        &mut self,
    ) -> Option<&mut HashMap<SaturationSuccessorDataId, SaturationSuccessorDataId>> {
        self.has_merge_distinct_hash
            .then_some(&mut self.merge_distinct_hash)
    }

    /// Port-facing read for `getMergingDistintSet(false)`.
    pub fn get_merging_distinct_set(
        &self,
    ) -> Option<&HashSet<(SaturationSuccessorDataId, SaturationSuccessorDataId)>> {
        self.has_merge_distinct_set
            .then_some(&self.merge_distinct_set)
    }

    /// Mutable counterpart for `getMergingDistintSet`.
    pub fn get_merging_distinct_set_mut(
        &mut self,
    ) -> Option<&mut HashSet<(SaturationSuccessorDataId, SaturationSuccessorDataId)>> {
        self.has_merge_distinct_set
            .then_some(&mut self.merge_distinct_set)
    }
}

// ===========================================================================
// CIndividualSaturationProcessNodeExtensionData
// ===========================================================================

/// Port of `CIndividualSaturationProcessNodeExtensionData`.
///
/// The per-node lazily-allocated extension-data block: the linked-role-successor
/// hash (ported), the linked data-value assertion data (ported), plus a family
/// of opaque saturation sub-structs (disjunct
/// common-concept extraction, critical-concept-type queues, successor / nominal
/// handling / datatype / ATMOST-merging data, the neighbour-role-assertion hash,
/// the successor-role-assertion linker).
///
/// KONCLUDE-PORT-NOTE[api]: `mLinkedRoleSuccHash`,
/// `mLinkedDataValueAssertionData`, and `mRoleAssertionLinker` resolve to real
/// ported types; the remaining `mXxx*` members stay opaque `Cint64`
/// (`INVALID` == `nullptr`). Their lazy create-getters are `W4.5-DEFER`.
pub struct IndividualSaturationProcessNodeExtensionData {
    /// `mProcessContext` (opaque per-test owner handle).
    pub process_context: Cint64,
    /// `mMemAllocMan` (opaque pool handle).
    pub mem_alloc_man: Cint64,
    /// `mIndiNode`.
    pub indi_node: SatNodeId,
    /// `mDisComConExtData` (`CSaturationDisjunctCommonConceptExtractionData*`).
    pub dis_com_con_ext_data: SaturationDisjunctCommonConceptExtractionDataId,
    /// `mLinkedRoleSuccHash` (`CLinkedRoleSaturationSuccessorHash*`, ported).
    pub linked_role_succ_hash: LinkedRoleSaturationSuccessorHashId,
    /// `mCriticalConceptTypeQueues` (`CCriticalSaturationConceptTypeQueues*`).
    pub critical_concept_type_queues: CriticalSaturationConceptTypeQueuesId,
    /// `mSuccessorExtensionData` (`CSaturationIndividualNodeSuccessorExtensionData*`).
    pub successor_extension_data: SaturationIndividualNodeSuccessorExtensionDataId,
    /// `mNominalHandlingData` (`CSaturationIndividualNodeNominalHandlingData*`).
    pub nominal_handling_data: SaturationIndividualNodeNominalHandlingDataId,
    /// `mATMOSTSuccessorMergingData` (`CSaturationATMOSTSuccessorMergingData*`).
    pub atmost_successor_merging_data: SaturationAtmostSuccessorMergingDataId,
    /// `mCriticalPredRoleCardHash` (`CCriticalPredecessorRoleCardinalityHash*`).
    pub critical_pred_role_card_hash: CriticalPredecessorRoleCardinalityHashId,
    /// `mRoleAssertionLinker` (`CSaturationSuccessorRoleAssertionLinker*`).
    pub role_assertion_linker: SaturationSuccessorRoleAssertionLinkerId,
    /// `mAppliedDatatypeData` (`CSaturationIndividualNodeDatatypeData*`).
    pub applied_datatype_data: SaturationIndividualNodeDatatypeDataId,
    /// `mLinkedNeighbourRoleAssertionHash` (`CLinkedNeighbourRoleAssertionSaturationHash*`, opaque).
    pub linked_neighbour_role_assertion_hash: Cint64,
    /// `mLinkedDataValueAssertionData` (`CLinkedDataValueAssertionSaturationData*`).
    pub linked_data_value_assertion_data: LinkedDataValueAssertionSaturationDataId,
}

impl Default for IndividualSaturationProcessNodeExtensionData {
    fn default() -> Self {
        IndividualSaturationProcessNodeExtensionData {
            process_context: INVALID,
            mem_alloc_man: INVALID,
            indi_node: SatNodeId::NONE,
            dis_com_con_ext_data: SaturationDisjunctCommonConceptExtractionDataId::NONE,
            linked_role_succ_hash: LinkedRoleSaturationSuccessorHashId::NONE,
            critical_concept_type_queues: CriticalSaturationConceptTypeQueuesId::NONE,
            successor_extension_data: SaturationIndividualNodeSuccessorExtensionDataId::NONE,
            nominal_handling_data: SaturationIndividualNodeNominalHandlingDataId::NONE,
            atmost_successor_merging_data: SaturationAtmostSuccessorMergingDataId::NONE,
            critical_pred_role_card_hash: CriticalPredecessorRoleCardinalityHashId::NONE,
            role_assertion_linker: SaturationSuccessorRoleAssertionLinkerId::NONE,
            applied_datatype_data: SaturationIndividualNodeDatatypeDataId::NONE,
            linked_neighbour_role_assertion_hash: INVALID,
            linked_data_value_assertion_data: LinkedDataValueAssertionSaturationDataId::NONE,
        }
    }
}

impl IndividualSaturationProcessNodeExtensionData {
    /// Port of the `CIndividualSaturationProcessNodeExtensionData(CProcessContext*)` ctor.
    pub fn new(process_context: Cint64) -> Self {
        IndividualSaturationProcessNodeExtensionData {
            process_context,
            ..Default::default()
        }
    }
    /// Port of `initIndividualExtensionData` (`mIndiNode = indiNode; …` reset).
    pub fn init_individual_extension_data(&mut self, indi_node: SatNodeId) -> &mut Self {
        self.indi_node = indi_node;
        self.dis_com_con_ext_data = SaturationDisjunctCommonConceptExtractionDataId::NONE;
        self.linked_role_succ_hash = LinkedRoleSaturationSuccessorHashId::NONE;
        self.critical_concept_type_queues = CriticalSaturationConceptTypeQueuesId::NONE;
        self.successor_extension_data = SaturationIndividualNodeSuccessorExtensionDataId::NONE;
        self.nominal_handling_data = SaturationIndividualNodeNominalHandlingDataId::NONE;
        self.atmost_successor_merging_data = SaturationAtmostSuccessorMergingDataId::NONE;
        self.critical_pred_role_card_hash = CriticalPredecessorRoleCardinalityHashId::NONE;
        self.role_assertion_linker = SaturationSuccessorRoleAssertionLinkerId::NONE;
        self.applied_datatype_data = SaturationIndividualNodeDatatypeDataId::NONE;
        self.linked_neighbour_role_assertion_hash = INVALID;
        self.linked_data_value_assertion_data = LinkedDataValueAssertionSaturationDataId::NONE;
        self
    }
    /// `create == false` read of the linked-role-successor hash (`return mLinkedRoleSuccHash`).
    /// The `create == true` lazy-alloc path is the context-threaded
    /// `ProcessContext::sat_node_ext_linked_role_successor_hash` getter.
    pub fn get_linked_role_successor_hash(&self) -> LinkedRoleSaturationSuccessorHashId {
        self.linked_role_succ_hash
    }
    /// `create == false` read of the linked data-value assertion data
    /// (`return mLinkedDataValueAssertionData`). The `create == true` lazy-alloc
    /// path is `ProcessContext::sat_node_ext_linked_data_value_assertion_data`.
    pub fn get_linked_data_value_assertion_data(&self) -> LinkedDataValueAssertionSaturationDataId {
        self.linked_data_value_assertion_data
    }
    /// `create == false` read of the successor-extension data
    /// (`return mSuccessorExtensionData`). The `create == true` lazy-alloc path
    /// is `ProcessContext::sat_node_ext_successor_extension_data`.
    pub fn get_successor_extension_data(&self) -> SaturationIndividualNodeSuccessorExtensionDataId {
        self.successor_extension_data
    }
    /// `create == false` read of the disjunct common-concept extraction data
    /// (`return mDisComConExtData`). The `create == true` lazy-alloc path is
    /// `ProcessContext::sat_node_ext_disjunct_common_concept_extraction_data`.
    pub fn get_disjunct_common_concept_extraction_data(
        &self,
    ) -> SaturationDisjunctCommonConceptExtractionDataId {
        self.dis_com_con_ext_data
    }
    /// Port of `getRoleAssertionLinker` (`return mRoleAssertionLinker`).
    pub fn get_role_assertion_linker(&self) -> SaturationSuccessorRoleAssertionLinkerId {
        self.role_assertion_linker
    }

    /// `create == false` read of the critical predecessor role-cardinality hash
    /// (`return mCriticalPredRoleCardHash`). The `create == true` lazy-alloc path
    /// is `ProcessContext::sat_node_ext_critical_predecessor_role_cardinality_hash`.
    pub fn get_critical_predecessor_role_cardinality_hash(
        &self,
    ) -> CriticalPredecessorRoleCardinalityHashId {
        self.critical_pred_role_card_hash
    }

    /// `create == false` read of the ATMOST successor-merging data
    /// (`return mATMOSTSuccessorMergingData`). The `create == true` lazy-alloc
    /// path is `ProcessContext::sat_node_ext_atmost_successor_merging_data`.
    pub fn get_atmost_successor_merging_data(&self) -> SaturationAtmostSuccessorMergingDataId {
        self.atmost_successor_merging_data
    }

    // W4.5-DEFER[api]: the lazy create-getters for the opaque sub-structs
    // (`getCriticalConceptTypeQueues`, `getNominalHandlingData`,
    // `getLinkedNeighbourRoleAssertionHash`) land with those sub-structs.
}

// ===========================================================================
// CSaturationIndividualNodeSuccessorExtensionData
// ===========================================================================

/// Value of C++ `CConceptNegationPair`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ConceptNegationPair {
    pub concept: ConceptId,
    pub negation: bool,
}

impl ConceptNegationPair {
    pub fn new(concept: ConceptId, negation: bool) -> Self {
        Self { concept, negation }
    }
}

/// Port-facing temporary map for
/// `CPROCESSINGHASH<cint64,CConceptNegationPair>`.
pub struct SaturationConceptExtensionMap {
    pub concept_extension_map: HashMap<Cint64, ConceptNegationPair>,
}

impl Default for SaturationConceptExtensionMap {
    fn default() -> Self {
        Self {
            concept_extension_map: HashMap::new(),
        }
    }
}

impl SaturationConceptExtensionMap {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn insert(&mut self, concept_tag: Cint64, pair: ConceptNegationPair) -> &mut Self {
        self.concept_extension_map.insert(concept_tag, pair);
        self
    }
    pub fn iter(&self) -> impl Iterator<Item = (&Cint64, &ConceptNegationPair)> {
        self.concept_extension_map.iter()
    }
    pub fn is_empty(&self) -> bool {
        self.concept_extension_map.is_empty()
    }
}

/// Port of `CSaturationSuccessorConceptExtensionMapData`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SaturationSuccessorConceptExtensionMapData {
    /// `mConcept`.
    pub concept: ConceptId,
    /// `mPositive`.
    pub positive: bool,
    /// `mNegative`.
    pub negative: bool,
}

impl Default for SaturationSuccessorConceptExtensionMapData {
    fn default() -> Self {
        Self {
            concept: ConceptId::NONE,
            positive: false,
            negative: false,
        }
    }
}

impl SaturationSuccessorConceptExtensionMapData {
    /// Port of `CSaturationSuccessorConceptExtensionMapData::CSaturationSuccessorConceptExtensionMapData`.
    pub fn new() -> Self {
        Self::default()
    }
}

/// Port of `CSaturationSuccessorConceptExtensionMap`.
pub struct SaturationSuccessorConceptExtensionMap {
    /// `mConceptExtensionMap`.
    pub concept_extension_map: HashMap<Cint64, SaturationSuccessorConceptExtensionMapData>,
}

impl Default for SaturationSuccessorConceptExtensionMap {
    fn default() -> Self {
        Self {
            concept_extension_map: HashMap::new(),
        }
    }
}

impl SaturationSuccessorConceptExtensionMap {
    /// Port of `CSaturationSuccessorConceptExtensionMap::CSaturationSuccessorConceptExtensionMap`.
    pub fn new() -> Self {
        Self::default()
    }
    /// Port of `initSuccessorConceptExtensionMap`.
    pub fn init_successor_concept_extension_map(&mut self) -> &mut Self {
        self.concept_extension_map.clear();
        self
    }
    /// Port-facing accessor for `getSuccessorConceptExtensionMap`.
    pub fn get_successor_concept_extension_map(
        &self,
    ) -> &HashMap<Cint64, SaturationSuccessorConceptExtensionMapData> {
        &self.concept_extension_map
    }
    /// Mutable port-facing accessor for `getSuccessorConceptExtensionMap`.
    pub fn get_successor_concept_extension_map_mut(
        &mut self,
    ) -> &mut HashMap<Cint64, SaturationSuccessorConceptExtensionMapData> {
        &mut self.concept_extension_map
    }
    /// Port of `addExtensionConcept`.
    pub fn add_extension_concept(
        &mut self,
        concept: ConceptId,
        negation: bool,
        concept_tag: Cint64,
    ) -> bool {
        let data = self.concept_extension_map.entry(concept_tag).or_default();
        data.concept = concept;
        let modified = if negation {
            !data.negative
        } else {
            !data.positive
        };
        if negation {
            data.negative = true;
        } else {
            data.positive = true;
        }
        modified
    }
    pub fn iter(
        &self,
    ) -> impl Iterator<Item = (&Cint64, &SaturationSuccessorConceptExtensionMapData)> {
        self.concept_extension_map.iter()
    }
    pub fn is_empty(&self) -> bool {
        self.concept_extension_map.is_empty()
    }
}

// ===========================================================================
// CSaturationSuccessorALLConceptExtensionData
// ===========================================================================

/// Port of `CSaturationSuccessorALLConceptExtensionData`.
///
/// C++ derives from `CLinkerBase<bool,Self>`: the boolean payload is the
/// extension-processing queued flag and the intrusive next pointer chains the
/// node-level ALL extension process queue.
pub struct SaturationSuccessorAllConceptExtensionData {
    /// `CLinkerBase` data (`isExtensionProcessingQueued`).
    pub extension_processing_queued: bool,
    /// `CLinkerBase` next.
    pub next: SaturationSuccessorAllConceptExtensionDataId,
    /// `mRole`.
    pub role: RoleId,
    /// `mConceptsUpdatedFlag`.
    pub concepts_updated_flag: bool,
    /// `mSuccessorCardinalityUpdatedFlag`.
    pub successor_cardinality_updated_flag: bool,
    /// `mRequiredSuccCount`.
    pub required_successor_count: Cint64,
    /// `mLastConnectedSuccCount`.
    pub last_connected_successor_count: Cint64,
    /// `mIndiProcSatNode`.
    pub indi_proc_sat_node: SatNodeId,
    /// `mLastResolvedIndiProcSatNode`.
    pub last_resolved_indi_proc_sat_node: SatNodeId,
    /// `mConceptExtensionMap`.
    pub concept_extension_map: SaturationSuccessorConceptExtensionMapId,
}

impl Default for SaturationSuccessorAllConceptExtensionData {
    fn default() -> Self {
        Self {
            extension_processing_queued: false,
            next: SaturationSuccessorAllConceptExtensionDataId::NONE,
            role: RoleId::NONE,
            concepts_updated_flag: false,
            successor_cardinality_updated_flag: false,
            required_successor_count: 0,
            last_connected_successor_count: 0,
            indi_proc_sat_node: SatNodeId::NONE,
            last_resolved_indi_proc_sat_node: SatNodeId::NONE,
            concept_extension_map: SaturationSuccessorConceptExtensionMapId::NONE,
        }
    }
}

impl SaturationSuccessorAllConceptExtensionData {
    /// Port of `CSaturationSuccessorALLConceptExtensionData(CProcessContext*)`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `initSuccessorConceptExtensionData`.
    pub fn init_successor_concept_extension_data(
        &mut self,
        role: RoleId,
        indi_proc_sat_node: SatNodeId,
        concept_extension_map: SaturationSuccessorConceptExtensionMapId,
    ) -> &mut Self {
        self.extension_processing_queued = false;
        self.next = SaturationSuccessorAllConceptExtensionDataId::NONE;
        self.role = role;
        self.indi_proc_sat_node = indi_proc_sat_node;
        self.last_resolved_indi_proc_sat_node = SatNodeId::NONE;
        self.required_successor_count = 0;
        self.last_connected_successor_count = 0;
        self.successor_cardinality_updated_flag = false;
        self.concepts_updated_flag = false;
        self.concept_extension_map = concept_extension_map;
        self
    }

    /// Port of `isExtensionProcessingQueued`.
    pub fn is_extension_processing_queued(&self) -> bool {
        self.extension_processing_queued
    }

    /// Port of `setExtensionProcessingQueued`.
    pub fn set_extension_processing_queued(&mut self, queued: bool) -> &mut Self {
        self.extension_processing_queued = queued;
        self
    }

    /// Port of `getSuccessorConceptExtensionMap`.
    pub fn get_successor_concept_extension_map(&self) -> SaturationSuccessorConceptExtensionMapId {
        self.concept_extension_map
    }

    /// Port of `getRole`.
    pub fn get_role(&self) -> RoleId {
        self.role
    }

    /// Port of `getIndividualNode`.
    pub fn get_individual_node(&self) -> SatNodeId {
        self.indi_proc_sat_node
    }

    /// Port of `getLastResolvedIndividualNode`.
    pub fn get_last_resolved_individual_node(&self) -> SatNodeId {
        self.last_resolved_indi_proc_sat_node
    }

    /// Port of `setLastResolvedIndividualNode`.
    pub fn set_last_resolved_individual_node(&mut self, indi_node: SatNodeId) -> &mut Self {
        self.last_resolved_indi_proc_sat_node = indi_node;
        self
    }

    /// Port of `getRequiredSuccessorCardinality`.
    pub fn get_required_successor_cardinality(&self) -> Cint64 {
        self.required_successor_count
    }

    /// Port of `setRequiredSuccessorCardinality`.
    pub fn set_required_successor_cardinality(&mut self, succ_card: Cint64) -> &mut Self {
        self.required_successor_count = succ_card;
        self
    }

    /// Port of `getLastConnectedSuccessorCardinality`.
    pub fn get_last_connected_successor_cardinality(&self) -> Cint64 {
        self.last_connected_successor_count
    }

    /// Port of `setLastConnectedSuccessorCardinality`.
    pub fn set_last_connected_successor_cardinality(&mut self, succ_card: Cint64) -> &mut Self {
        self.last_connected_successor_count = succ_card;
        self
    }

    /// Port of `addRequiredSuccessorCardinality`.
    pub fn add_required_successor_cardinality(&mut self, succ_card: Cint64) -> bool {
        if self.required_successor_count < succ_card {
            self.required_successor_count = succ_card;
            self.successor_cardinality_updated_flag = true;
        }
        self.successor_cardinality_updated_flag
    }

    /// Port of `hasSuccessorCardinalityUpdatedFlag`.
    ///
    /// Konclude's implementation returns `mConceptsUpdatedFlag`; this preserves
    /// that exact behaviour.
    pub fn has_successor_cardinality_updated_flag(&self) -> bool {
        self.concepts_updated_flag
    }

    /// Port of `hasConceptsUpdatedFlag`.
    ///
    /// Konclude's implementation returns `mSuccessorCardinalityUpdatedFlag`; this
    /// preserves that exact behaviour.
    pub fn has_concepts_updated_flag(&self) -> bool {
        self.successor_cardinality_updated_flag
    }

    /// Port of `clearUpdatedFlags`.
    pub fn clear_updated_flags(&mut self) -> &mut Self {
        self.concepts_updated_flag = false;
        self.successor_cardinality_updated_flag = false;
        self
    }

    /// Port of linker `clearNext`.
    pub fn clear_next(&mut self) -> &mut Self {
        self.next = SaturationSuccessorAllConceptExtensionDataId::NONE;
        self
    }
}

// ===========================================================================
// CSaturationLinkedSuccessorIndividualALLConceptsExtensionData
// ===========================================================================

/// Port of `CSaturationLinkedSuccessorIndividualALLConceptsExtensionData`.
pub struct SaturationLinkedSuccessorIndividualAllConceptsExtensionData {
    /// `mIndiProcSatNode`.
    pub indi_proc_sat_node: SatNodeId,
    /// `mRoleConceptExtensionHash`.
    pub role_concept_extension_hash: HashMap<RoleId, SaturationSuccessorAllConceptExtensionDataId>,
    /// `mOnlyRole`.
    pub only_role: RoleId,
    /// `mOnlyAllConceptExtData`.
    pub only_all_concept_ext_data: SaturationSuccessorAllConceptExtensionDataId,
}

impl Default for SaturationLinkedSuccessorIndividualAllConceptsExtensionData {
    fn default() -> Self {
        Self {
            indi_proc_sat_node: SatNodeId::NONE,
            role_concept_extension_hash: HashMap::new(),
            only_role: RoleId::NONE,
            only_all_concept_ext_data: SaturationSuccessorAllConceptExtensionDataId::NONE,
        }
    }
}

impl SaturationLinkedSuccessorIndividualAllConceptsExtensionData {
    /// Port of `CSaturationLinkedSuccessorIndividualALLConceptsExtensionData`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `initLinkedSuccessorIndividualALLConceptsExtensionData`.
    pub fn init_linked_successor_individual_all_concepts_extension_data(
        &mut self,
        indi_proc_sat_node: SatNodeId,
    ) -> &mut Self {
        self.indi_proc_sat_node = indi_proc_sat_node;
        self.role_concept_extension_hash.clear();
        self.only_role = RoleId::NONE;
        self.only_all_concept_ext_data = SaturationSuccessorAllConceptExtensionDataId::NONE;
        self
    }
}

// ===========================================================================
// CSaturationLinkedSuccessorIndividualALLConceptsExtensionHash
// ===========================================================================

/// Port of `CSaturationLinkedSuccessorIndividualALLConceptsExtensionHash`.
pub struct SaturationLinkedSuccessorIndividualAllConceptsExtensionHash {
    /// `mLinkedSuccIndiALLConceptExtHash`.
    pub linked_successor_individual_all_concepts_extension_hash:
        HashMap<SatNodeId, SaturationLinkedSuccessorIndividualAllConceptsExtensionDataId>,
}

impl Default for SaturationLinkedSuccessorIndividualAllConceptsExtensionHash {
    fn default() -> Self {
        Self {
            linked_successor_individual_all_concepts_extension_hash: HashMap::new(),
        }
    }
}

impl SaturationLinkedSuccessorIndividualAllConceptsExtensionHash {
    /// Port of `CSaturationLinkedSuccessorIndividualALLConceptsExtensionHash`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `initLinkedSuccessorIndividualALLConceptsExtensionHash`.
    pub fn init_linked_successor_individual_all_concepts_extension_hash(&mut self) -> &mut Self {
        self.linked_successor_individual_all_concepts_extension_hash
            .clear();
        self
    }
}

/// Port of `CSaturationIndividualNodeExtensionResolveHashData`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SaturationIndividualNodeExtensionResolveHashData {
    /// `mResolveData`.
    pub resolve_data: SaturationIndividualNodeExtensionResolveDataId,
}

impl Default for SaturationIndividualNodeExtensionResolveHashData {
    fn default() -> Self {
        Self {
            resolve_data: SaturationIndividualNodeExtensionResolveDataId::NONE,
        }
    }
}

impl SaturationIndividualNodeExtensionResolveHashData {
    pub fn new() -> Self {
        Self::default()
    }
}

/// Port of `CSaturationIndividualNodeExtensionResolveHash`.
pub struct SaturationIndividualNodeExtensionResolveHash {
    /// Concept-key slice of
    /// `CPROCESSHASH<QPair<void*,bool>,CSaturationIndividualNodeExtensionResolveHashData>`.
    pub concept_resolve_hash:
        HashMap<(ConceptId, bool), SaturationIndividualNodeExtensionResolveHashData>,
    /// Individual-node-key slice.
    pub individual_resolve_hash:
        HashMap<SatNodeId, SaturationIndividualNodeExtensionResolveHashData>,
    /// Role-key slice.
    pub role_resolve_hash: HashMap<RoleId, SaturationIndividualNodeExtensionResolveHashData>,
    /// Neighbour-key slice (`nullptr,true`).
    pub neighbour_resolve_data: SaturationIndividualNodeExtensionResolveHashData,
}

impl Default for SaturationIndividualNodeExtensionResolveHash {
    fn default() -> Self {
        Self {
            concept_resolve_hash: HashMap::new(),
            individual_resolve_hash: HashMap::new(),
            role_resolve_hash: HashMap::new(),
            neighbour_resolve_data: SaturationIndividualNodeExtensionResolveHashData::new(),
        }
    }
}

impl SaturationIndividualNodeExtensionResolveHash {
    pub fn new() -> Self {
        Self::default()
    }
    /// Port of `initIndividualNodeExtensionResolveHash`.
    pub fn init_individual_node_extension_resolve_hash(&mut self) -> &mut Self {
        self.concept_resolve_hash.clear();
        self.individual_resolve_hash.clear();
        self.role_resolve_hash.clear();
        self.neighbour_resolve_data = SaturationIndividualNodeExtensionResolveHashData::new();
        self
    }
    /// Port of `getIndividualNodeExtensionResolveHash`.
    pub fn get_individual_node_extension_resolve_hash(
        &self,
    ) -> &HashMap<(ConceptId, bool), SaturationIndividualNodeExtensionResolveHashData> {
        &self.concept_resolve_hash
    }
    /// Port of `getResolvedIndividualNodeExtensionData(CConcept*, bool)`.
    pub fn get_resolved_individual_node_extension_data(
        &mut self,
        concept: ConceptId,
        negation: bool,
    ) -> &mut SaturationIndividualNodeExtensionResolveHashData {
        self.concept_resolve_hash
            .entry((concept, negation))
            .or_insert_with(SaturationIndividualNodeExtensionResolveHashData::new)
    }
    /// Port of `getNonCreatingResolvedIndividualNodeExtensionData(CConcept*, bool)`.
    pub fn get_non_creating_resolved_individual_node_extension_data(
        &self,
        concept: ConceptId,
        negation: bool,
    ) -> SaturationIndividualNodeExtensionResolveHashData {
        self.concept_resolve_hash
            .get(&(concept, negation))
            .copied()
            .unwrap_or_default()
    }
    /// Port of `getResolvedIndividualNodeExtensionData(CIndividualSaturationProcessNode*)`.
    pub fn get_resolved_individual_node_extension_data_for_node(
        &mut self,
        extension_node: SatNodeId,
    ) -> &mut SaturationIndividualNodeExtensionResolveHashData {
        self.individual_resolve_hash
            .entry(extension_node)
            .or_insert_with(SaturationIndividualNodeExtensionResolveHashData::new)
    }
    /// Port of `getNonCreatingResolvedIndividualNodeExtensionData(CIndividualSaturationProcessNode*)`.
    pub fn get_non_creating_resolved_individual_node_extension_data_for_node(
        &self,
        extension_node: SatNodeId,
    ) -> SaturationIndividualNodeExtensionResolveHashData {
        self.individual_resolve_hash
            .get(&extension_node)
            .copied()
            .unwrap_or_default()
    }
}

/// Port of `CSaturationIndividualNodeExtensionResolveData`.
pub struct SaturationIndividualNodeExtensionResolveData {
    /// `mExtensionResolveHash`.
    pub extension_resolve_hash: SaturationIndividualNodeExtensionResolveHashId,
    /// `mIndiNode`.
    pub indi_node: SatNodeId,
    /// `mIndiID`.
    pub indi_id: Cint64,
}

impl Default for SaturationIndividualNodeExtensionResolveData {
    fn default() -> Self {
        Self {
            extension_resolve_hash: SaturationIndividualNodeExtensionResolveHashId::NONE,
            indi_node: SatNodeId::NONE,
            indi_id: 0,
        }
    }
}

impl SaturationIndividualNodeExtensionResolveData {
    /// Port of `CSaturationIndividualNodeExtensionResolveData(CProcessContext*)`.
    pub fn new() -> Self {
        Self::default()
    }
    /// Port of `initExtensionResolveData(CIndividualSaturationProcessNode*)`.
    pub fn init_extension_resolve_data_for_node(
        &mut self,
        indi_process_node: SatNodeId,
        indi_id: Cint64,
    ) -> &mut Self {
        self.indi_node = indi_process_node;
        self.indi_id = indi_id;
        self.extension_resolve_hash = SaturationIndividualNodeExtensionResolveHashId::NONE;
        self
    }
    /// Port of `initExtensionResolveData(cint64)`.
    pub fn init_extension_resolve_data_for_id(&mut self, indi_id: Cint64) -> &mut Self {
        self.indi_node = SatNodeId::NONE;
        self.indi_id = indi_id;
        self.extension_resolve_hash = SaturationIndividualNodeExtensionResolveHashId::NONE;
        self
    }
    /// Port of `setProcessingIndividualNode`.
    pub fn set_processing_individual_node(&mut self, indi_process_node: SatNodeId) -> &mut Self {
        self.indi_node = indi_process_node;
        self
    }
    /// Port of `getProcessingIndividualNode`.
    pub fn get_processing_individual_node(&self) -> SatNodeId {
        self.indi_node
    }
    /// Port of `getProcessingIndividualNodeID`.
    pub fn get_processing_individual_node_id(&self) -> Cint64 {
        self.indi_id
    }
    /// Port of `hasProcessingIndividualNode`.
    pub fn has_processing_individual_node(&self) -> bool {
        self.indi_node.is_some()
    }
}

/// Port of `CSaturationIndividualNodeSuccessorExtensionData`.
///
/// The owning successor-extension satellite for one saturation node. Its direct
/// state and ownership boundary are ported here; the dependent resolve / ALL /
/// FUNCTIONAL extension records are not ported yet and therefore remain opaque
/// `Cint64` handles (`INVALID` == `nullptr`).
pub struct SaturationIndividualNodeSuccessorExtensionData {
    /// `mProcessContext`.
    pub process_context: Cint64,
    /// `mExtensionProcessingQueued`.
    extension_processing_queued: bool,
    /// `mIndiProcessNode`.
    pub indi_process_node: SatNodeId,
    /// `mExtensionResolveData` (`CSaturationIndividualNodeExtensionResolveData*`).
    extension_resolve_data: SaturationIndividualNodeExtensionResolveDataId,
    /// `mAncSuccMergeResolveData` (`CSaturationIndividualNodeExtensionResolveData*`).
    anc_succ_merge_resolve_data: SaturationIndividualNodeExtensionResolveDataId,
    /// `mALLConceptsExtensionData` (`CSaturationIndividualNodeALLConceptsExtensionData*`).
    all_concepts_extension_data: SaturationIndividualNodeAllConceptsExtensionDataId,
    /// `mFUNCTIONALConceptsExtensionData`
    /// (`CSaturationIndividualNodeFUNCTIONALConceptsExtensionData*`).
    functional_concepts_extension_data: SaturationIndividualNodeFunctionalConceptsExtensionDataId,
}

impl Default for SaturationIndividualNodeSuccessorExtensionData {
    fn default() -> Self {
        SaturationIndividualNodeSuccessorExtensionData {
            process_context: INVALID,
            extension_processing_queued: false,
            indi_process_node: SatNodeId::NONE,
            extension_resolve_data: SaturationIndividualNodeExtensionResolveDataId::NONE,
            anc_succ_merge_resolve_data: SaturationIndividualNodeExtensionResolveDataId::NONE,
            all_concepts_extension_data: SaturationIndividualNodeAllConceptsExtensionDataId::NONE,
            functional_concepts_extension_data:
                SaturationIndividualNodeFunctionalConceptsExtensionDataId::NONE,
        }
    }
}

impl SaturationIndividualNodeSuccessorExtensionData {
    /// Port of `CSaturationIndividualNodeSuccessorExtensionData(CProcessContext*)`.
    pub fn new(process_context: Cint64) -> Self {
        SaturationIndividualNodeSuccessorExtensionData {
            process_context,
            ..Default::default()
        }
    }

    /// Port of `initExtensionData`.
    pub fn init_extension_data(&mut self, indi_process_node: SatNodeId) -> &mut Self {
        self.extension_resolve_data = SaturationIndividualNodeExtensionResolveDataId::NONE;
        self.indi_process_node = indi_process_node;
        self.all_concepts_extension_data = SaturationIndividualNodeAllConceptsExtensionDataId::NONE;
        self.functional_concepts_extension_data =
            SaturationIndividualNodeFunctionalConceptsExtensionDataId::NONE;
        self.anc_succ_merge_resolve_data = SaturationIndividualNodeExtensionResolveDataId::NONE;
        self.extension_processing_queued = false;
        self
    }

    /// Port of `getExtensionResolveData`.
    pub fn get_extension_resolve_data(&self) -> SaturationIndividualNodeExtensionResolveDataId {
        self.extension_resolve_data
    }

    /// Port of `setExtensionResolveData`.
    pub fn set_extension_resolve_data(
        &mut self,
        resolve_data: SaturationIndividualNodeExtensionResolveDataId,
    ) -> &mut Self {
        self.extension_resolve_data = resolve_data;
        self
    }

    /// Port of `isExtensionProcessingQueued`.
    pub fn is_extension_processing_queued(&self) -> bool {
        self.extension_processing_queued
    }

    /// Port of `setExtensionProcessingQueued`.
    pub fn set_extension_processing_queued(&mut self, queued: bool) -> &mut Self {
        self.extension_processing_queued = queued;
        self
    }

    /// `create == false` read for `getAncestorSuccessorMergeResolveData`.
    pub fn get_ancestor_successor_merge_resolve_data(
        &self,
    ) -> SaturationIndividualNodeExtensionResolveDataId {
        self.anc_succ_merge_resolve_data
    }

    /// `create == false` read for `getBaseExtensionResolveData`.
    pub fn get_base_extension_resolve_data(
        &self,
    ) -> SaturationIndividualNodeExtensionResolveDataId {
        self.extension_resolve_data
    }

    /// `create == false` read for `getALLConceptsExtensionData`.
    pub fn get_all_concepts_extension_data(
        &self,
    ) -> SaturationIndividualNodeAllConceptsExtensionDataId {
        self.all_concepts_extension_data
    }

    /// Port-facing setter for the context-threaded `getALLConceptsExtensionData(true)`.
    pub fn set_all_concepts_extension_data(
        &mut self,
        data: SaturationIndividualNodeAllConceptsExtensionDataId,
    ) -> &mut Self {
        self.all_concepts_extension_data = data;
        self
    }

    /// `create == false` read for `getFUNCTIONALConceptsExtensionData`.
    pub fn get_functional_concepts_extension_data(
        &self,
    ) -> SaturationIndividualNodeFunctionalConceptsExtensionDataId {
        self.functional_concepts_extension_data
    }

    /// Port-facing setter for the context-threaded `getFUNCTIONALConceptsExtensionData(true)`.
    pub fn set_functional_concepts_extension_data(
        &mut self,
        data: SaturationIndividualNodeFunctionalConceptsExtensionDataId,
    ) -> &mut Self {
        self.functional_concepts_extension_data = data;
        self
    }
}

// ===========================================================================
// CSaturationIndividualNodeALLConceptsExtensionData
// ===========================================================================

/// Port of `CSaturationIndividualNodeALLConceptsExtensionData`.
///
/// This is the node-level ALL-concepts successor-extension worklist.
pub struct SaturationIndividualNodeAllConceptsExtensionData {
    /// `mSuccessorExtensionInitialized`.
    pub successor_extension_initialized: bool,
    /// `mExtensionProcessingQueued`.
    pub extension_processing_queued: bool,
    /// `mIndiProcessNode`.
    pub indi_process_node: SatNodeId,
    /// `mRoleProcessLinker`.
    pub role_process_linker: RoleSaturationProcessLinkerId,
    /// `mLinkedSuccIdnALLConceptExtHash`.
    pub linked_successor_individual_all_concepts_extension_hash:
        SaturationLinkedSuccessorIndividualAllConceptsExtensionHash,
    /// `mExtensionProcessLinker`.
    pub extension_process_linker: SaturationSuccessorAllConceptExtensionDataId,
}

impl Default for SaturationIndividualNodeAllConceptsExtensionData {
    fn default() -> Self {
        Self {
            successor_extension_initialized: false,
            extension_processing_queued: false,
            indi_process_node: SatNodeId::NONE,
            role_process_linker: RoleSaturationProcessLinkerId::NONE,
            linked_successor_individual_all_concepts_extension_hash:
                SaturationLinkedSuccessorIndividualAllConceptsExtensionHash::new(),
            extension_process_linker: SaturationSuccessorAllConceptExtensionDataId::NONE,
        }
    }
}

impl SaturationIndividualNodeAllConceptsExtensionData {
    /// Port of `CSaturationIndividualNodeALLConceptsExtensionData(CProcessContext*)`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `initALLConceptsExtensionData`.
    pub fn init_all_concepts_extension_data(&mut self, indi_process_node: SatNodeId) -> &mut Self {
        self.successor_extension_initialized = false;
        self.extension_processing_queued = false;
        self.indi_process_node = indi_process_node;
        self.role_process_linker = RoleSaturationProcessLinkerId::NONE;
        self.linked_successor_individual_all_concepts_extension_hash
            .init_linked_successor_individual_all_concepts_extension_hash();
        self.extension_process_linker = SaturationSuccessorAllConceptExtensionDataId::NONE;
        self
    }

    /// Port of `isSuccessorExtensionInitialized`.
    pub fn is_successor_extension_initialized(&self) -> bool {
        self.successor_extension_initialized
    }

    /// Port of `setSuccessorExtensionInitialized`.
    pub fn set_successor_extension_initialized(&mut self, initialized: bool) -> &mut Self {
        self.successor_extension_initialized = initialized;
        self
    }

    /// Port of `isExtensionProcessingQueued`.
    pub fn is_extension_processing_queued(&self) -> bool {
        self.extension_processing_queued
    }

    /// Port of `setExtensionProcessingQueued`.
    pub fn set_extension_processing_queued(&mut self, queued: bool) -> &mut Self {
        self.extension_processing_queued = queued;
        self
    }

    /// Port of `getRoleProcessLinker`.
    pub fn get_role_process_linker(&self) -> RoleSaturationProcessLinkerId {
        self.role_process_linker
    }

    /// Port of `getLinkedSuccessorIndividualALLConceptsExtensionHash`.
    pub fn get_linked_successor_individual_all_concepts_extension_hash(
        &self,
    ) -> &SaturationLinkedSuccessorIndividualAllConceptsExtensionHash {
        &self.linked_successor_individual_all_concepts_extension_hash
    }

    /// Mutable port-facing access to `mLinkedSuccIdnALLConceptExtHash`.
    pub fn linked_successor_individual_all_concepts_extension_hash_mut(
        &mut self,
    ) -> &mut SaturationLinkedSuccessorIndividualAllConceptsExtensionHash {
        &mut self.linked_successor_individual_all_concepts_extension_hash
    }

    /// Port of `hasExtensionProcessData`.
    pub fn has_extension_process_data(&self) -> bool {
        self.extension_process_linker.is_some()
    }

    /// Port of `getExtensionProcessDataLinker`.
    pub fn get_extension_process_data_linker(
        &self,
    ) -> SaturationSuccessorAllConceptExtensionDataId {
        self.extension_process_linker
    }

    /// Port of `addExtensionProcessData`.
    ///
    /// The caller passes the previous head after setting `process_data.next`, which
    /// mirrors `processData->append(mExtensionProcessLinker)`.
    pub fn add_extension_process_data(
        &mut self,
        process_data: SaturationSuccessorAllConceptExtensionDataId,
    ) -> &mut Self {
        self.extension_process_linker = process_data;
        self
    }
}

// ===========================================================================
// CSaturationSuccessorFUNCTIONALConceptExtensionData
// ===========================================================================

/// Port of `CSaturationSuccessorFUNCTIONALConceptExtensionData`.
///
/// C++ derives from `CLinkerBase<bool,Self>`: the boolean payload is the
/// extension-processing-queued flag and the intrusive next pointer chains
/// successor extension process data.
pub struct SaturationSuccessorFunctionalConceptExtensionData {
    /// `CLinkerBase` data (`isExtensionProcessingQueued`).
    pub extension_processing_queued: bool,
    /// `CLinkerBase` next.
    pub next: SaturationSuccessorFunctionalConceptExtensionDataId,
    /// `mRole`.
    pub role: RoleId,
    /// `mLastResolvedIndiProcSatNode`.
    pub last_resolved_indi_proc_sat_node: SatNodeId,
    /// `mLastExaminedLinkedSucc`.
    pub last_examined_linked_succ: SaturationSuccessorDataId,
}

impl Default for SaturationSuccessorFunctionalConceptExtensionData {
    fn default() -> Self {
        Self {
            extension_processing_queued: false,
            next: SaturationSuccessorFunctionalConceptExtensionDataId::NONE,
            role: RoleId::NONE,
            last_resolved_indi_proc_sat_node: SatNodeId::NONE,
            last_examined_linked_succ: SaturationSuccessorDataId::NONE,
        }
    }
}

impl SaturationSuccessorFunctionalConceptExtensionData {
    /// Port of `CSaturationSuccessorFUNCTIONALConceptExtensionData(CProcessContext*)`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `initSuccessorConceptExtensionData`.
    pub fn init_successor_concept_extension_data(&mut self, role: RoleId) -> &mut Self {
        self.extension_processing_queued = false;
        self.next = SaturationSuccessorFunctionalConceptExtensionDataId::NONE;
        self.role = role;
        self.last_resolved_indi_proc_sat_node = SatNodeId::NONE;
        self.last_examined_linked_succ = SaturationSuccessorDataId::NONE;
        self
    }

    /// Port of `isExtensionProcessingQueued`.
    pub fn is_extension_processing_queued(&self) -> bool {
        self.extension_processing_queued
    }

    /// Port of `setExtensionProcessingQueued`.
    pub fn set_extension_processing_queued(&mut self, queued: bool) -> &mut Self {
        self.extension_processing_queued = queued;
        self
    }

    /// Port of `getRole`.
    pub fn get_role(&self) -> RoleId {
        self.role
    }

    /// Port of `getLastResolvedIndividualNode`.
    pub fn get_last_resolved_individual_node(&self) -> SatNodeId {
        self.last_resolved_indi_proc_sat_node
    }

    /// Port of `setLastResolvedIndividualNode`.
    pub fn set_last_resolved_individual_node(&mut self, indi_node: SatNodeId) -> &mut Self {
        self.last_resolved_indi_proc_sat_node = indi_node;
        self
    }

    /// Port of `getLastExaminedLinkedSuccessorData`.
    pub fn get_last_examined_linked_successor_data(&self) -> SaturationSuccessorDataId {
        self.last_examined_linked_succ
    }

    /// Port of `setLastExaminedLinkedSuccessorData`.
    pub fn set_last_examined_linked_successor_data(
        &mut self,
        last_examined_linked_succ: SaturationSuccessorDataId,
    ) -> &mut Self {
        self.last_examined_linked_succ = last_examined_linked_succ;
        self
    }

    /// Port of linker `clearNext`.
    pub fn clear_next(&mut self) -> &mut Self {
        self.next = SaturationSuccessorFunctionalConceptExtensionDataId::NONE;
        self
    }
}

// ===========================================================================
// CSaturationLinkedSuccessorRoleFUNCTIONALConceptsExtensionHash
// ===========================================================================

/// Port of `CSaturationLinkedSuccessorRoleFUNCTIONALConceptsExtensionHash`.
pub struct SaturationLinkedSuccessorRoleFunctionalConceptsExtensionHash {
    /// `mLinkedSuccRoleFUNCTIONALConceptExtHash`.
    pub linked_succ_role_functional_concept_ext_hash:
        HashMap<RoleId, SaturationSuccessorFunctionalConceptExtensionDataId>,
}

impl Default for SaturationLinkedSuccessorRoleFunctionalConceptsExtensionHash {
    fn default() -> Self {
        Self {
            linked_succ_role_functional_concept_ext_hash: HashMap::new(),
        }
    }
}

impl SaturationLinkedSuccessorRoleFunctionalConceptsExtensionHash {
    /// Port of `CSaturationLinkedSuccessorRoleFUNCTIONALConceptsExtensionHash`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `initLinkedSuccessorRoleFUNCTIONALConceptsExtensionHash`.
    pub fn init_linked_successor_role_functional_concepts_extension_hash(&mut self) -> &mut Self {
        self.linked_succ_role_functional_concept_ext_hash.clear();
        self
    }

    /// Port of `getLinkedSuccessorIndividualFUNCTIONALConceptsExtensionHash`.
    pub fn get_linked_successor_individual_functional_concepts_extension_hash(
        &self,
    ) -> &HashMap<RoleId, SaturationSuccessorFunctionalConceptExtensionDataId> {
        &self.linked_succ_role_functional_concept_ext_hash
    }

    /// Port of `getSuccessorFunctionalConceptsExtensionData(role,false)`.
    pub fn get_successor_functional_concepts_extension_data(
        &self,
        role: RoleId,
    ) -> SaturationSuccessorFunctionalConceptExtensionDataId {
        self.linked_succ_role_functional_concept_ext_hash
            .get(&role)
            .copied()
            .unwrap_or(SaturationSuccessorFunctionalConceptExtensionDataId::NONE)
    }
}

// ===========================================================================
// CSaturationIndividualNodeFUNCTIONALConceptsExtensionData
// ===========================================================================

/// Port of `CSaturationIndividualNodeFUNCTIONALConceptsExtensionData`.
///
/// W489 ports the successor-facing role-extension data surface used by SAT-6.
/// Predecessor queues, qualified-atmost queues, and forwarding hashes remain
/// represented by typed/opaque fields until their callers are ported.
pub struct SaturationIndividualNodeFunctionalConceptsExtensionData {
    /// `mSuccessorExtensionInitialized`.
    pub successor_extension_initialized: bool,
    /// `mExtensionProcessingQueued`.
    pub extension_processing_queued: bool,
    /// `mIndiProcessNode`.
    pub indi_process_node: SatNodeId,
    /// `mLinkedSuccRoleFUNCTIONALConceptExtHash`.
    pub linked_succ_role_functional_concept_ext_hash:
        SaturationLinkedSuccessorRoleFunctionalConceptsExtensionHash,
    /// `mSuccessorExtensionProcessLinker`.
    pub successor_extension_process_linker: SaturationSuccessorFunctionalConceptExtensionDataId,
    /// `mLinkedSuccessorAddedRoleProcessLinker`.
    pub linked_successor_added_role_process_linker: RoleSaturationProcessLinkerId,
    /// `mFunctionalityAddedRoleProcessLinker`.
    pub functionality_added_role_process_linker: RoleSaturationProcessLinkerId,
    /// `mCopyingInitializingRoleProcessLinker`.
    pub copying_initializing_role_process_linker: RoleSaturationProcessLinkerId,
    /// `mQualFuncAtmostConProcessLinker`.
    pub qual_func_atmost_con_process_linker: ConceptSaturationProcessLinkerId,
    /// `mLinkedPredecessorAddedRoleProcessLinker`.
    pub linked_predecessor_added_role_process_linker: RoleSaturationProcessLinkerId,
    /// `mPredecessorExtensionProcessLinker` (`CSaturationPredecessorFUNCTIONALConceptExtensionData*`, not yet ported).
    pub predecessor_extension_process_linker: Cint64,
    /// `mForwardingPredMergedHash` (`CPROCESSHASH<CIndividualSaturationProcessNode*,CRole*>*`).
    pub forwarding_pred_merged_hash: HashMap<SatNodeId, HashSet<RoleId>>,
    /// `mQualifiedFunctionalAtmostConceptProcessSet` (`CPROCESSSET<CConceptSaturationDescriptor*>*`, not yet ported).
    pub qualified_functional_atmost_concept_process_set: Cint64,
}

impl Default for SaturationIndividualNodeFunctionalConceptsExtensionData {
    fn default() -> Self {
        Self {
            successor_extension_initialized: false,
            extension_processing_queued: false,
            indi_process_node: SatNodeId::NONE,
            linked_succ_role_functional_concept_ext_hash:
                SaturationLinkedSuccessorRoleFunctionalConceptsExtensionHash::new(),
            successor_extension_process_linker:
                SaturationSuccessorFunctionalConceptExtensionDataId::NONE,
            linked_successor_added_role_process_linker: RoleSaturationProcessLinkerId::NONE,
            functionality_added_role_process_linker: RoleSaturationProcessLinkerId::NONE,
            copying_initializing_role_process_linker: RoleSaturationProcessLinkerId::NONE,
            qual_func_atmost_con_process_linker: ConceptSaturationProcessLinkerId::NONE,
            linked_predecessor_added_role_process_linker: RoleSaturationProcessLinkerId::NONE,
            predecessor_extension_process_linker: INVALID,
            forwarding_pred_merged_hash: HashMap::new(),
            qualified_functional_atmost_concept_process_set: INVALID,
        }
    }
}

impl SaturationIndividualNodeFunctionalConceptsExtensionData {
    /// Port of `CSaturationIndividualNodeFUNCTIONALConceptsExtensionData(CProcessContext*)`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `initFUNCTIONALConceptsExtensionData`.
    pub fn init_functional_concepts_extension_data(
        &mut self,
        indi_process_node: SatNodeId,
    ) -> &mut Self {
        self.linked_succ_role_functional_concept_ext_hash
            .init_linked_successor_role_functional_concepts_extension_hash();
        self.indi_process_node = indi_process_node;
        self.linked_successor_added_role_process_linker = RoleSaturationProcessLinkerId::NONE;
        self.linked_predecessor_added_role_process_linker = RoleSaturationProcessLinkerId::NONE;
        self.qual_func_atmost_con_process_linker = ConceptSaturationProcessLinkerId::NONE;
        self.functionality_added_role_process_linker = RoleSaturationProcessLinkerId::NONE;
        self.copying_initializing_role_process_linker = RoleSaturationProcessLinkerId::NONE;
        self.successor_extension_initialized = false;
        self.extension_processing_queued = false;
        self.successor_extension_process_linker =
            SaturationSuccessorFunctionalConceptExtensionDataId::NONE;
        self.predecessor_extension_process_linker = INVALID;
        self.forwarding_pred_merged_hash.clear();
        self.qualified_functional_atmost_concept_process_set = INVALID;
        self
    }

    /// Port of `isSuccessorExtensionInitialized`.
    pub fn is_successor_extension_initialized(&self) -> bool {
        self.successor_extension_initialized
    }

    /// Port of `setSuccessorExtensionInitialized`.
    pub fn set_successor_extension_initialized(&mut self, initialized: bool) -> &mut Self {
        self.successor_extension_initialized = initialized;
        self
    }

    /// Port of `isExtensionProcessingQueued`.
    pub fn is_extension_processing_queued(&self) -> bool {
        self.extension_processing_queued
    }

    /// Port of `setExtensionProcessingQueued`.
    pub fn set_extension_processing_queued(&mut self, queued: bool) -> &mut Self {
        self.extension_processing_queued = queued;
        self
    }

    /// Port of `getLinkedSuccessorRoleFUNCTIONALConceptsExtensionHash`.
    pub fn get_linked_successor_role_functional_concepts_extension_hash(
        &self,
    ) -> &SaturationLinkedSuccessorRoleFunctionalConceptsExtensionHash {
        &self.linked_succ_role_functional_concept_ext_hash
    }

    /// Mutable port-facing access to the embedded linked-successor role hash.
    pub fn linked_successor_role_functional_concepts_extension_hash_mut(
        &mut self,
    ) -> &mut SaturationLinkedSuccessorRoleFunctionalConceptsExtensionHash {
        &mut self.linked_succ_role_functional_concept_ext_hash
    }

    /// Port of `hasSuccessorExtensionProcessData`.
    pub fn has_successor_extension_process_data(&self) -> bool {
        self.successor_extension_process_linker.is_some()
    }

    /// Port of `getSuccessorExtensionProcessDataLinker`.
    pub fn get_successor_extension_process_data_linker(
        &self,
    ) -> SaturationSuccessorFunctionalConceptExtensionDataId {
        self.successor_extension_process_linker
    }

    /// Port-facing append for `addSuccessorExtensionProcessData`.
    pub fn add_successor_extension_process_data(
        &mut self,
        process_data: SaturationSuccessorFunctionalConceptExtensionDataId,
        next: SaturationSuccessorFunctionalConceptExtensionDataId,
    ) -> &mut Self {
        if process_data.is_some() {
            self.successor_extension_process_linker = process_data;
            let _ = next;
        }
        self
    }

    /// Port of `getForwardingPredecessorMergedHash`.
    ///
    /// The Rust `HashMap` is allocated with the parent struct, so `create` is a
    /// no-op preserved for the port-facing signature.
    pub fn get_forwarding_predecessor_merged_hash(
        &mut self,
        create: bool,
    ) -> &mut HashMap<SatNodeId, HashSet<RoleId>> {
        let _ = create;
        &mut self.forwarding_pred_merged_hash
    }

    /// Port of `hasIndividualNodeForwardingPredecessorMerged(indiNode)`.
    pub fn has_individual_node_forwarding_predecessor_merged_node(
        &self,
        indi_node: SatNodeId,
    ) -> bool {
        self.forwarding_pred_merged_hash.contains_key(&indi_node)
    }

    /// Port of `hasIndividualNodeForwardingPredecessorMerged(indiNode,role)`.
    pub fn has_individual_node_forwarding_predecessor_merged(
        &self,
        indi_node: SatNodeId,
        role: RoleId,
    ) -> bool {
        self.forwarding_pred_merged_hash
            .get(&indi_node)
            .map(|roles| roles.contains(&role))
            .unwrap_or(false)
    }

    /// Port of `setIndividualNodeForwardingPredecessorMerged`.
    pub fn set_individual_node_forwarding_predecessor_merged(
        &mut self,
        indi_node: SatNodeId,
        role: RoleId,
    ) -> &mut Self {
        if indi_node.is_some() && role.is_some() {
            self.forwarding_pred_merged_hash
                .entry(indi_node)
                .or_default()
                .insert(role);
        }
        self
    }
}

// ===========================================================================
// CSaturationIndividualNodeDatatypeData
// ===========================================================================

/// Port of `CSaturationIndividualNodeDatatypeData`.
pub struct SaturationIndividualNodeDatatypeData {
    /// `mProcessContext`.
    pub process_context: Cint64,
    /// `mAppliedDataLiteral` (`CDataLiteral*`, opaque).
    applied_data_literal: Cint64,
    /// `mAppliedDatatype` (`CDatatype*`, opaque).
    applied_datatype: Cint64,
}

impl Default for SaturationIndividualNodeDatatypeData {
    fn default() -> Self {
        SaturationIndividualNodeDatatypeData {
            process_context: INVALID,
            applied_data_literal: INVALID,
            applied_datatype: INVALID,
        }
    }
}

impl SaturationIndividualNodeDatatypeData {
    /// Port of `CSaturationIndividualNodeDatatypeData(CProcessContext*)`.
    pub fn new(process_context: Cint64) -> Self {
        SaturationIndividualNodeDatatypeData {
            process_context,
            ..Default::default()
        }
    }

    /// Port of `initExtensionData`.
    pub fn init_extension_data(&mut self, _indi_process_node: SatNodeId) -> &mut Self {
        self.applied_datatype = INVALID;
        self.applied_data_literal = INVALID;
        self
    }

    /// Port of `getAppliedDataLiteral`.
    pub fn get_applied_data_literal(&self) -> Cint64 {
        self.applied_data_literal
    }

    /// Port of `getAppliedDatatype`.
    pub fn get_applied_datatype(&self) -> Cint64 {
        self.applied_datatype
    }

    /// Port of `setAppliedDataLiteral`.
    pub fn set_applied_data_literal(&mut self, data_literal: Cint64) -> &mut Self {
        self.applied_data_literal = data_literal;
        self
    }

    /// Port of `setAppliedDatatype`.
    pub fn set_applied_datatype(&mut self, datatype: Cint64) -> &mut Self {
        self.applied_datatype = datatype;
        self
    }
}

// ===========================================================================
// CImplicationReapplyConceptSaturationDescriptor
// ===========================================================================

/// Port of `CImplicationReapplyConceptSaturationDescriptor`.
///
/// `CLinkerBase<CConcept*,Self>` stores the implication concept as its data and
/// the intrusive self-chain next pointer. `mNextTriggerConcept` points into the
/// remaining `CSortedNegLinker<CConcept*>` trigger suffix; the Rust port owns the
/// suffix as a head-to-tail vector.
pub struct ImplicationReapplyConceptSaturationDescriptor {
    /// `CLinkerBase` data (`getData()`): the implication concept.
    pub implication_concept: ConceptId,
    /// `mNextTriggerConcept`.
    pub next_trigger_concept: Option<Vec<NegLink<ConceptId>>>,
    /// `CLinkerBase` intrusive next link.
    pub next: ImplicationReapplyConceptSaturationDescriptorId,
}

impl Default for ImplicationReapplyConceptSaturationDescriptor {
    fn default() -> Self {
        ImplicationReapplyConceptSaturationDescriptor {
            implication_concept: ConceptId::NONE,
            next_trigger_concept: None,
            next: ImplicationReapplyConceptSaturationDescriptorId::NONE,
        }
    }
}

impl ImplicationReapplyConceptSaturationDescriptor {
    /// Port of `CImplicationReapplyConceptSaturationDescriptor::CImplicationReapplyConceptSaturationDescriptor`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `initImplicationReapllyConceptSaturationDescriptor`.
    pub fn init_implication_reaplly_concept_saturation_descriptor(
        &mut self,
        impl_concept: ConceptId,
        next_trigger_concept: Option<&[NegLink<ConceptId>]>,
    ) -> &mut Self {
        self.implication_concept = impl_concept;
        self.next_trigger_concept = next_trigger_concept.map(|linker| linker.to_vec());
        self
    }

    /// Port of `getImplicationConcept`.
    pub fn get_implication_concept(&self) -> ConceptId {
        self.implication_concept
    }

    /// Port of `getNextTriggerConcept`.
    pub fn get_next_trigger_concept(&self) -> Option<&[NegLink<ConceptId>]> {
        self.next_trigger_concept.as_deref()
    }

    /// Port of `getNext`.
    pub fn get_next(&self) -> ImplicationReapplyConceptSaturationDescriptorId {
        self.next
    }

    /// Port of `setNext`.
    pub fn set_next(&mut self, next: ImplicationReapplyConceptSaturationDescriptorId) -> &mut Self {
        self.next = next;
        self
    }
}

// ===========================================================================
// CSaturationModifiedProcessUpdateLinker
// ===========================================================================

/// Port of `CSaturationModifiedProcessUpdateLinker::MODIFICATIONPROCESSUPDATETYPE`.
///
/// Konclude defines one value here:
/// `UPDATEPDISJUNCTCOMMONCONCEPTSEXTRACTION`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SaturationModificationProcessUpdateType {
    UpdateDisjunctCommonConceptExtraction,
}

/// Port of `CSaturationModifiedProcessUpdateLinker`.
pub struct SaturationModifiedProcessUpdateLinker {
    /// `CLinkerBase` data (`CIndividualSaturationProcessNode*`).
    pub processing_individual: SatNodeId,
    /// `CLinkerBase` intrusive next link.
    pub next: SaturationModifiedProcessUpdateLinkerId,
    /// `mUpdateType`.
    pub update_type: SaturationModificationProcessUpdateType,
}

impl Default for SaturationModifiedProcessUpdateLinker {
    fn default() -> Self {
        SaturationModifiedProcessUpdateLinker {
            processing_individual: SatNodeId::NONE,
            next: SaturationModifiedProcessUpdateLinkerId::NONE,
            update_type:
                SaturationModificationProcessUpdateType::UpdateDisjunctCommonConceptExtraction,
        }
    }
}

impl SaturationModifiedProcessUpdateLinker {
    /// Port of `CSaturationModifiedProcessUpdateLinker::CSaturationModifiedProcessUpdateLinker`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `initProcessUpdateLinker`.
    pub fn init_process_update_linker(
        &mut self,
        individual: SatNodeId,
        update_type: SaturationModificationProcessUpdateType,
    ) -> &mut Self {
        self.processing_individual = individual;
        self.update_type = update_type;
        self.next = SaturationModifiedProcessUpdateLinkerId::NONE;
        self
    }

    /// Port of `setProcessingIndividual`.
    pub fn set_processing_individual(&mut self, individual: SatNodeId) -> &mut Self {
        self.processing_individual = individual;
        self
    }

    /// Port of `getProcessingIndividual`.
    pub fn get_processing_individual(&self) -> SatNodeId {
        self.processing_individual
    }

    /// Port of `getUpdateType`.
    pub fn get_update_type(&self) -> SaturationModificationProcessUpdateType {
        self.update_type
    }

    /// Port of `setUpdateType`.
    pub fn set_update_type(
        &mut self,
        update_type: SaturationModificationProcessUpdateType,
    ) -> &mut Self {
        self.update_type = update_type;
        self
    }

    /// Port of `getNext`.
    pub fn get_next(&self) -> SaturationModifiedProcessUpdateLinkerId {
        self.next
    }

    /// Port of `setNext`.
    pub fn set_next(&mut self, next: SaturationModifiedProcessUpdateLinkerId) -> &mut Self {
        self.next = next;
        self
    }
}

// ===========================================================================
// CConceptSaturationDescriptorReapplyData  (by-value map value)
// ===========================================================================

/// Port of `CConceptSaturationDescriptorReapplyData`.
///
/// The value stored in `CReapplyConceptSaturationLabelSet`'s concept-dep hashes:
/// the concept saturation descriptor and the implication-reapply descriptor.
#[derive(Clone, Copy)]
pub struct ConceptSaturationDescriptorReapplyData {
    /// `mConSatDes`.
    pub con_sat_des: ConceptSaturationDescriptorId,
    /// `mImpReapplyConSatDes`.
    pub imp_reapply_con_sat_des: ImplicationReapplyConceptSaturationDescriptorId,
}

impl Default for ConceptSaturationDescriptorReapplyData {
    fn default() -> Self {
        ConceptSaturationDescriptorReapplyData {
            con_sat_des: ConceptSaturationDescriptorId::NONE,
            imp_reapply_con_sat_des: ImplicationReapplyConceptSaturationDescriptorId::NONE,
        }
    }
}

impl ConceptSaturationDescriptorReapplyData {
    /// Port of `CConceptSaturationDescriptorReapplyData::CConceptSaturationDescriptorReapplyData`.
    pub fn new() -> Self {
        Self::default()
    }
}

/// Snapshot entry for `CReapplyConceptSaturationLabelSetIterator`.
#[derive(Clone, Copy)]
pub struct ReapplyConceptSaturationLabelSetIteratorEntry {
    pub key: Cint64,
    pub data: ConceptSaturationDescriptorReapplyData,
}

/// Port of `CReapplyConceptSaturationLabelSetIterator`.
pub struct ReapplyConceptSaturationLabelSetIterator {
    entries: Vec<ReapplyConceptSaturationLabelSetIteratorEntry>,
    pos: usize,
    iterate_con_sat_des: bool,
    iterate_reapplies: bool,
}

impl ReapplyConceptSaturationLabelSetIterator {
    pub fn new(
        entries: Vec<ReapplyConceptSaturationLabelSetIteratorEntry>,
        iterate_con_sat_des: bool,
        iterate_reapplies: bool,
    ) -> Self {
        let mut it = Self {
            entries,
            pos: 0,
            iterate_con_sat_des,
            iterate_reapplies,
        };
        it.skip_invalid();
        it
    }

    fn is_iterator_valid_data(&self, data: &ConceptSaturationDescriptorReapplyData) -> bool {
        (data.con_sat_des.is_some() && self.iterate_con_sat_des)
            || (data.imp_reapply_con_sat_des.is_some() && self.iterate_reapplies)
    }

    fn skip_invalid(&mut self) {
        while self.pos != self.entries.len()
            && !self.is_iterator_valid_data(&self.entries[self.pos].data)
        {
            self.pos += 1;
        }
    }

    /// Port of `getDataTag`.
    pub fn get_data_tag(&self) -> Cint64 {
        if self.pos != self.entries.len() {
            self.entries[self.pos].key
        } else {
            INVALID
        }
    }

    /// Port of `getConceptSaturationDescriptor`.
    pub fn get_concept_saturation_descriptor(&self) -> ConceptSaturationDescriptorId {
        if self.pos != self.entries.len() {
            self.entries[self.pos].data.con_sat_des
        } else {
            ConceptSaturationDescriptorId::NONE
        }
    }

    /// Port of `getImplicationReapplyConceptSaturationDescriptor`.
    pub fn get_implication_reapply_concept_saturation_descriptor(
        &self,
    ) -> ImplicationReapplyConceptSaturationDescriptorId {
        if self.pos != self.entries.len() {
            self.entries[self.pos].data.imp_reapply_con_sat_des
        } else {
            ImplicationReapplyConceptSaturationDescriptorId::NONE
        }
    }

    /// Port of `hasNext`.
    pub fn has_next(&self) -> bool {
        self.pos != self.entries.len()
    }

    /// Port of `moveNext`.
    pub fn move_next(&mut self) -> &mut Self {
        if self.pos != self.entries.len() {
            self.pos += 1;
            self.skip_invalid();
        }
        self
    }
}

// ===========================================================================
// CReapplyConceptSaturationLabelSet
// ===========================================================================

/// Port of `CReapplyConceptSaturationLabelSet`.
///
/// The saturation twin of `CReapplyConceptLabelSet`: the per-node saturated
/// concept label, addressed by two concept-tag → reapply-data hashes (the main
/// + an additional overflow copy), the head of the concept-saturation-descriptor
/// chain, the last nominal-independent descriptor, the concept-set flags
/// (opaque), the counts, and the modified-update-linker chain.
///
/// KONCLUDE-PORT-NOTE[api]: the insertion / clash / implication-reapply insertion
/// surface is live as `ProcessContext` helpers because it mutates label-set map
/// state and descriptor arenas together. Iterator/copy/flag helpers still walk
/// opaque `CConceptSetFlags` payloads and stay deferred. The struct + ctor +
/// init/copy + count/linker accessors + the simple `hasConcept`/`containsConcept`
/// lookups are ported here so the s-units can hold and read the label set.
pub struct ReapplyConceptSaturationLabelSet {
    /// `mConceptDesDepHash` (`CPROCESSHASH<cint64,CConceptSaturationDescriptorReapplyData>`).
    pub concept_des_dep_hash: HashMap<Cint64, ConceptSaturationDescriptorReapplyData>,
    /// `mAdditionalConceptDesDepHash` (the overflow copy, allocated lazily in C++).
    pub additional_concept_des_dep_hash: HashMap<Cint64, ConceptSaturationDescriptorReapplyData>,
    /// Whether the additional overflow hash has been allocated (`mAdditional… != nullptr`).
    pub has_additional_concept_des_dep_hash: bool,
    /// `mConceptSatDesLinker` (head of the concept-saturation-descriptor chain).
    pub concept_sat_des_linker: ConceptSaturationDescriptorId,
    /// `mLastNominalIndepConSatDes`.
    pub last_nominal_indep_con_sat_des: ConceptSaturationDescriptorId,
    /// `mConceptFlags` (`CConceptSetFlags`, by value → opaque flag word).
    pub concept_flags: Cint64,
    /// `mConceptCount`.
    pub concept_count: Cint64,
    /// `mTotelCount` (C++ spelling preserved).
    pub totel_count: Cint64,
    /// `mModifiedUpdateLinker` (`CSaturationModifiedProcessUpdateLinker*`).
    pub modified_update_linker: SaturationModifiedProcessUpdateLinkerId,
    /// `mProcessContext` (opaque per-test owner handle).
    pub process_context: Cint64,
}

impl ReapplyConceptSaturationLabelSet {
    /// `ADDITIONALCOPYSIZE` (`const static cint64 = 300`).
    pub const ADDITIONALCOPYSIZE: Cint64 = 300;

    /// Port of the `CReapplyConceptSaturationLabelSet(CProcessContext*)` ctor.
    pub fn new(process_context: Cint64) -> Self {
        ReapplyConceptSaturationLabelSet {
            concept_des_dep_hash: HashMap::new(),
            additional_concept_des_dep_hash: HashMap::new(),
            has_additional_concept_des_dep_hash: false,
            concept_sat_des_linker: ConceptSaturationDescriptorId::NONE,
            last_nominal_indep_con_sat_des: ConceptSaturationDescriptorId::NONE,
            concept_flags: 0,
            concept_count: 0,
            totel_count: 0,
            modified_update_linker: SaturationModifiedProcessUpdateLinkerId::NONE,
            process_context,
        }
    }
    /// Port of `initReapplyConceptSaturationLabelSet` (reset the per-test state).
    pub fn init_reapply_concept_saturation_label_set(&mut self) -> &mut Self {
        self.concept_des_dep_hash.clear();
        self.additional_concept_des_dep_hash.clear();
        self.has_additional_concept_des_dep_hash = false;
        self.concept_sat_des_linker = ConceptSaturationDescriptorId::NONE;
        self.last_nominal_indep_con_sat_des = ConceptSaturationDescriptorId::NONE;
        self.concept_flags = 0;
        self.concept_count = 0;
        self.totel_count = 0;
        self.modified_update_linker = SaturationModifiedProcessUpdateLinkerId::NONE;
        self
    }
    /// Port of `getConceptCount` (`return mConceptCount`).
    pub fn get_concept_count(&self) -> Cint64 {
        self.concept_count
    }
    /// Port of `getTotalCount` (`return mTotelCount`).
    pub fn get_total_count(&self) -> Cint64 {
        self.totel_count
    }
    /// Port of `getConceptSaturationDescriptionLinker` (`return mConceptSatDesLinker`).
    pub fn get_concept_saturation_description_linker(&self) -> ConceptSaturationDescriptorId {
        self.concept_sat_des_linker
    }
    /// Port of `getLastNominalIndependentConceptSaturationDescriptorLinker`
    /// (`return mLastNominalIndepConSatDes`).
    pub fn get_last_nominal_independent_concept_saturation_descriptor_linker(
        &self,
    ) -> ConceptSaturationDescriptorId {
        self.last_nominal_indep_con_sat_des
    }
    /// Port of `setLastNominalIndependentConceptSaturationDescriptorLinker`
    /// (`mLastNominalIndepConSatDes = conSatDes`).
    pub fn set_last_nominal_independent_concept_saturation_descriptor_linker(
        &mut self,
        con_sat_des: ConceptSaturationDescriptorId,
    ) -> &mut Self {
        self.last_nominal_indep_con_sat_des = con_sat_des;
        self
    }
    /// Port of `hasModifiedUpdateLinkers` (`return mModifiedUpdateLinker != nullptr`).
    pub fn has_modified_update_linkers(&self) -> bool {
        self.modified_update_linker.is_some()
    }
    /// Port of `getModifiedUpdateLinker` (`return mModifiedUpdateLinker`).
    pub fn get_modified_update_linker(&self) -> SaturationModifiedProcessUpdateLinkerId {
        self.modified_update_linker
    }
    /// Port of `setModifiedUpdateLinker` (`mModifiedUpdateLinker = modUpdateLinker`).
    pub fn set_modified_update_linker(
        &mut self,
        mod_update_linker: SaturationModifiedProcessUpdateLinkerId,
    ) -> &mut Self {
        self.modified_update_linker = mod_update_linker;
        self
    }
    /// Port of `getConceptFlags` (`return &mConceptFlags`).
    pub fn get_concept_flags(&self) -> Cint64 {
        self.concept_flags
    }
    /// Port of `containsConceptOrReapllyQueue(conTag)` — concept present in either
    /// hash (C++ spelling of "Reapply" preserved).
    pub fn contains_concept_or_reaplly_queue(&self, con_tag: Cint64) -> bool {
        self.concept_des_dep_hash.contains_key(&con_tag)
            || (self.has_additional_concept_des_dep_hash
                && self.additional_concept_des_dep_hash.contains_key(&con_tag))
    }

    /// Port of `getConceptSaturationDescriptor(cint64, ...)`.
    pub fn get_concept_saturation_descriptor_by_tag(
        &self,
        con_tag: Cint64,
        con_sat_des: &mut ConceptSaturationDescriptorId,
        imp_reapply_con_sat_des: &mut ImplicationReapplyConceptSaturationDescriptorId,
    ) -> bool {
        let mut data = self.concept_des_dep_hash.get(&con_tag);
        let mut contained = data.is_some();
        if data.is_none() && self.has_additional_concept_des_dep_hash {
            data = self.additional_concept_des_dep_hash.get(&con_tag);
            contained = data.is_some();
        }
        if contained {
            let data = data.unwrap();
            *con_sat_des = data.con_sat_des;
            if con_sat_des.is_some() {
                *imp_reapply_con_sat_des = data.imp_reapply_con_sat_des;
            } else {
                *imp_reapply_con_sat_des = ImplicationReapplyConceptSaturationDescriptorId::NONE;
            }
            contained &= con_sat_des.is_some();
        }
        contained
    }

    /// Port of `getConceptDescriptorAndReapplyQueue(cint64, ...)`.
    ///
    /// Unlike `getConceptSaturationDescriptor`, this returns whether the concept
    /// tag has an entry at all, including an implication-reapply entry whose
    /// direct concept descriptor is null.
    pub fn get_concept_descriptor_and_reapply_queue_by_tag(
        &self,
        con_tag: Cint64,
        con_sat_des: &mut ConceptSaturationDescriptorId,
        imp_reapply_con_sat_des: &mut ImplicationReapplyConceptSaturationDescriptorId,
    ) -> bool {
        let mut data = self.concept_des_dep_hash.get(&con_tag);
        if data.is_none() && self.has_additional_concept_des_dep_hash {
            data = self.additional_concept_des_dep_hash.get(&con_tag);
        }
        if let Some(data) = data {
            *con_sat_des = data.con_sat_des;
            *imp_reapply_con_sat_des = data.imp_reapply_con_sat_des;
            true
        } else {
            *con_sat_des = ConceptSaturationDescriptorId::NONE;
            *imp_reapply_con_sat_des = ImplicationReapplyConceptSaturationDescriptorId::NONE;
            false
        }
    }

    /// Port of `hasConcept(cint64, bool)`.
    pub fn has_concept_by_tag(
        &self,
        con_tag: Cint64,
        negated: bool,
        con_sat_descs: &super::super::model::substrate::Arena<ConceptSaturationDescriptor>,
    ) -> bool {
        let mut con_sat_des = ConceptSaturationDescriptorId::NONE;
        let mut imp_reapply = ImplicationReapplyConceptSaturationDescriptorId::NONE;
        if !self.get_concept_saturation_descriptor_by_tag(
            con_tag,
            &mut con_sat_des,
            &mut imp_reapply,
        ) {
            return false;
        }
        con_sat_des.is_some()
            && con_sat_des.index() < con_sat_descs.len()
            && con_sat_descs.get(con_sat_des).get_negation() == negated
    }

    /// Port of `getIterator(bool iterateConSatDes, bool iterateReapplies)`.
    pub fn get_iterator(
        &self,
        iterate_con_sat_des: bool,
        iterate_reapplies: bool,
    ) -> ReapplyConceptSaturationLabelSetIterator {
        let mut entries: Vec<_> = self
            .concept_des_dep_hash
            .iter()
            .map(
                |(key, data)| ReapplyConceptSaturationLabelSetIteratorEntry {
                    key: *key,
                    data: *data,
                },
            )
            .collect();
        if self.has_additional_concept_des_dep_hash {
            entries.extend(
                self.additional_concept_des_dep_hash
                    .iter()
                    .map(
                        |(key, data)| ReapplyConceptSaturationLabelSetIteratorEntry {
                            key: *key,
                            data: *data,
                        },
                    ),
            );
        }
        entries.sort_by_key(|entry| entry.key);
        ReapplyConceptSaturationLabelSetIterator::new(
            entries,
            iterate_con_sat_des,
            iterate_reapplies,
        )
    }

    // W4.5-DEFER[api]: the remaining polarity-sensitive iterator/flag lookups
    // (`getConceptDescriptorAndReapplyQueue`, `hasConceptSaturationDescriptor`,
    // `containsConceptSaturationDescriptor`), `copyReapplyConceptSaturationLabelSet`,
    // `areAllConceptsInAdditionalHash`, and the concept-flag mutators need the
    // `CConceptSetFlags` port + `&mut ProcessContext` to read descriptor negation/tag
    // and allocate. The insertion and modified-update-linker equivalents are live as
    // ProcessContext helpers because they mutate label-set map/linker state and
    // descriptor/linker arenas together.
}

impl Default for ReapplyConceptSaturationLabelSet {
    fn default() -> Self {
        Self::new(INVALID)
    }
}
