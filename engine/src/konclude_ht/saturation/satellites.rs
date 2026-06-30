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
//! `CSaturationSuccessorRoleAssertionLinker`, `CSaturationDisjunctCommonConceptExtractionData`,
//! the critical-concept-type queues, the nominal-handling / datatype / ATMOST
//! merging data, `CImplicationReapplyConceptSaturationDescriptor`,
//! `CSaturationModifiedProcessUpdateLinker`, `CConceptSetFlags`) are NOT ported in
//! this wave; they stay opaque `Cint64` (`INVALID` == `nullptr`). The complex
//! container method bodies that walk them (`addLinkedSuccessor`,
//! `insertConceptReturnClashed`, the lazy create-getters, …) keep their faithful
//! C++ transcription as `W4.5-DEFER` markers and land when those sub-structs port.

#![allow(dead_code)]

use std::collections::HashMap;

use super::super::model::ontology::OntologyArenas;
use super::super::model::substrate::{Cint64, Id, NegLink, INVALID};
use super::super::model::{ConceptId, RoleId};
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
/// `CSaturationSuccessorData*`.
pub type SaturationSuccessorDataId = Id<SaturationSuccessorData>;
/// `CLinkedRoleSaturationSuccessorData*`.
pub type LinkedRoleSaturationSuccessorDataId = Id<LinkedRoleSaturationSuccessorData>;
/// `CLinkedRoleSaturationSuccessorHash*`.
pub type LinkedRoleSaturationSuccessorHashId = Id<LinkedRoleSaturationSuccessorHash>;
/// `CIndividualSaturationProcessNodeExtensionData*`.
pub type IndividualSaturationProcessNodeExtensionDataId =
    Id<IndividualSaturationProcessNodeExtensionData>;
/// `CReapplyConceptSaturationLabelSet*`.
pub type ReapplyConceptSaturationLabelSetId = Id<ReapplyConceptSaturationLabelSet>;

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
    /// `mExtensionData` (`CSaturationSuccessorExtensionData*`, not yet ported).
    /// KONCLUDE-PORT-NOTE[api]: opaque `Cint64` (`INVALID` == `nullptr`).
    pub extension_data: Cint64,
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
            extension_data: INVALID,
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
    /// Port of `getSucessorExtensionData` (`return mExtensionData`).
    pub fn get_sucessor_extension_data(&self) -> Cint64 {
        self.extension_data
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
    pub fn copy_role_successor_hash(&mut self, copy: &LinkedRoleSaturationSuccessorHash) -> &mut Self {
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
    pub fn set_last_examined_role_assertion_linker(&mut self, role_ass_linker: Cint64) -> &mut Self {
        self.last_examined_role_ass_linker = role_ass_linker;
        self
    }

    // W4.5-DEFER[api]: the mutating successor-management surface
    // (`getLinkedRoleSuccessorData(role,create)`, `hasLinkedSuccessor`,
    // `hasActiveLinkedSuccessor`, `addLinkedSuccessor`, `addLinkedVALUESuccessor`,
    // `deactivateLinkedSuccessor`, `reduceLinkedSuccessorCount`,
    // `increaseLinkedSuccessorCount`, `addExtensionSuccessor`,
    // `setSuccessorMergedCreation`, `hasActiveCreationRole`) needs the
    // `CSaturationSuccessorExtensionData` / `CSaturationSuccessorRoleAssertionLinker`
    // ports + `&mut ProcessContext` to allocate `CSaturationSuccessorData`. Faithful
    // bodies land with those sub-structs.
}

// ===========================================================================
// CIndividualSaturationProcessNodeExtensionData
// ===========================================================================

/// Port of `CIndividualSaturationProcessNodeExtensionData`.
///
/// The per-node lazily-allocated extension-data block: the linked-role-successor
/// hash (ported), plus a family of opaque saturation sub-structs (disjunct
/// common-concept extraction, critical-concept-type queues, successor / nominal
/// handling / datatype / ATMOST-merging data, the neighbour-role-assertion hash,
/// the data-value-assertion data, the successor-role-assertion linker).
///
/// KONCLUDE-PORT-NOTE[api]: only `mLinkedRoleSuccHash` resolves to a real ported
/// type this wave; the remaining `mXxx*` members stay opaque `Cint64`
/// (`INVALID` == `nullptr`). Their lazy create-getters are `W4.5-DEFER`.
pub struct IndividualSaturationProcessNodeExtensionData {
    /// `mProcessContext` (opaque per-test owner handle).
    pub process_context: Cint64,
    /// `mMemAllocMan` (opaque pool handle).
    pub mem_alloc_man: Cint64,
    /// `mIndiNode`.
    pub indi_node: SatNodeId,
    /// `mDisComConExtData` (`CSaturationDisjunctCommonConceptExtractionData*`, opaque).
    pub dis_com_con_ext_data: Cint64,
    /// `mLinkedRoleSuccHash` (`CLinkedRoleSaturationSuccessorHash*`, ported).
    pub linked_role_succ_hash: LinkedRoleSaturationSuccessorHashId,
    /// `mCriticalConceptTypeQueues` (`CCriticalSaturationConceptTypeQueues*`, opaque).
    pub critical_concept_type_queues: Cint64,
    /// `mSuccessorExtensionData` (`CSaturationIndividualNodeSuccessorExtensionData*`, opaque).
    pub successor_extension_data: Cint64,
    /// `mNominalHandlingData` (`CSaturationIndividualNodeNominalHandlingData*`, opaque).
    pub nominal_handling_data: Cint64,
    /// `mATMOSTSuccessorMergingData` (`CSaturationATMOSTSuccessorMergingData*`, opaque).
    pub atmost_successor_merging_data: Cint64,
    /// `mCriticalPredRoleCardHash` (`CCriticalPredecessorRoleCardinalityHash*`, opaque).
    pub critical_pred_role_card_hash: Cint64,
    /// `mRoleAssertionLinker` (`CSaturationSuccessorRoleAssertionLinker*`, opaque).
    pub role_assertion_linker: Cint64,
    /// `mAppliedDatatypeData` (`CSaturationIndividualNodeDatatypeData*`, opaque).
    pub applied_datatype_data: Cint64,
    /// `mLinkedNeighbourRoleAssertionHash` (`CLinkedNeighbourRoleAssertionSaturationHash*`, opaque).
    pub linked_neighbour_role_assertion_hash: Cint64,
    /// `mLinkedDataValueAssertionData` (`CLinkedDataValueAssertionSaturationData*`, opaque).
    pub linked_data_value_assertion_data: Cint64,
}

impl Default for IndividualSaturationProcessNodeExtensionData {
    fn default() -> Self {
        IndividualSaturationProcessNodeExtensionData {
            process_context: INVALID,
            mem_alloc_man: INVALID,
            indi_node: SatNodeId::NONE,
            dis_com_con_ext_data: INVALID,
            linked_role_succ_hash: LinkedRoleSaturationSuccessorHashId::NONE,
            critical_concept_type_queues: INVALID,
            successor_extension_data: INVALID,
            nominal_handling_data: INVALID,
            atmost_successor_merging_data: INVALID,
            critical_pred_role_card_hash: INVALID,
            role_assertion_linker: INVALID,
            applied_datatype_data: INVALID,
            linked_neighbour_role_assertion_hash: INVALID,
            linked_data_value_assertion_data: INVALID,
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
        self.dis_com_con_ext_data = INVALID;
        self.linked_role_succ_hash = LinkedRoleSaturationSuccessorHashId::NONE;
        self.critical_concept_type_queues = INVALID;
        self.successor_extension_data = INVALID;
        self.nominal_handling_data = INVALID;
        self.atmost_successor_merging_data = INVALID;
        self.critical_pred_role_card_hash = INVALID;
        self.role_assertion_linker = INVALID;
        self.applied_datatype_data = INVALID;
        self.linked_neighbour_role_assertion_hash = INVALID;
        self.linked_data_value_assertion_data = INVALID;
        self
    }
    /// `create == false` read of the linked-role-successor hash (`return mLinkedRoleSuccHash`).
    /// The `create == true` lazy-alloc path is the context-threaded
    /// `ProcessContext::sat_node_ext_linked_role_successor_hash` getter.
    pub fn get_linked_role_successor_hash(&self) -> LinkedRoleSaturationSuccessorHashId {
        self.linked_role_succ_hash
    }
    /// Port of `getRoleAssertionLinker` (`return mRoleAssertionLinker`).
    pub fn get_role_assertion_linker(&self) -> Cint64 {
        self.role_assertion_linker
    }

    // W4.5-DEFER[api]: the lazy create-getters for the opaque sub-structs
    // (`getDisjunctCommonConceptExtractionData`, `getCriticalConceptTypeQueues`,
    // `getSuccessorExtensionData`, `getNominalHandlingData`,
    // `getCriticalPredecessorRoleCardinalityHash`, `getAppliedDatatypeData`,
    // `getATMOSTSuccessorMergingData`, `getLinkedNeighbourRoleAssertionHash`,
    // `getLinkedDataValueAssertionData`) and the assertion-linker mutators
    // (`addRoleAssertionLinker`, `addRoleAssertion`) land with those sub-structs.
}

// ===========================================================================
// CConceptSaturationDescriptorReapplyData  (by-value map value)
// ===========================================================================

/// Port of `CConceptSaturationDescriptorReapplyData`.
///
/// The value stored in `CReapplyConceptSaturationLabelSet`'s concept-dep hashes:
/// the concept saturation descriptor and the (opaque) implication-reapply
/// descriptor.
#[derive(Clone)]
pub struct ConceptSaturationDescriptorReapplyData {
    /// `mConSatDes`.
    pub con_sat_des: ConceptSaturationDescriptorId,
    /// `mImpReapplyConSatDes` (`CImplicationReapplyConceptSaturationDescriptor*`, opaque).
    pub imp_reapply_con_sat_des: Cint64,
}

impl Default for ConceptSaturationDescriptorReapplyData {
    fn default() -> Self {
        ConceptSaturationDescriptorReapplyData {
            con_sat_des: ConceptSaturationDescriptorId::NONE,
            imp_reapply_con_sat_des: INVALID,
        }
    }
}

impl ConceptSaturationDescriptorReapplyData {
    /// Port of `CConceptSaturationDescriptorReapplyData::CConceptSaturationDescriptorReapplyData`.
    pub fn new() -> Self {
        Self::default()
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
/// (opaque), the counts, and the modified-update-linker (opaque).
///
/// KONCLUDE-PORT-NOTE[api]: the insertion / clash / iterator surface
/// (`insertConceptReturnClashed`, `insertConceptReapplicationReturnTriggered`,
/// `getConceptDescriptorAndReapplyQueue`, `getIterator`, …) walks the (opaque)
/// `CImplicationReapplyConceptSaturationDescriptor` /
/// `CSaturationModifiedProcessUpdateLinker` / `CConceptSetFlags` and allocates
/// descriptors from the pool; those bodies are `W4.5-DEFER` until those
/// sub-structs port. The struct + ctor + init/copy + count/linker accessors +
/// the simple `hasConcept`/`containsConcept` lookups are ported here so the s-units
/// can hold and read the label set.
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
    /// `mModifiedUpdateLinker` (`CSaturationModifiedProcessUpdateLinker*`, opaque).
    pub modified_update_linker: Cint64,
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
            modified_update_linker: INVALID,
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
        self.modified_update_linker = INVALID;
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
        self.modified_update_linker != INVALID
    }
    /// Port of `getModifiedUpdateLinker` (`return mModifiedUpdateLinker`).
    pub fn get_modified_update_linker(&self) -> Cint64 {
        self.modified_update_linker
    }
    /// Port of `setModifiedUpdateLinker` (`mModifiedUpdateLinker = modUpdateLinker`).
    pub fn set_modified_update_linker(&mut self, mod_update_linker: Cint64) -> &mut Self {
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

    // W4.5-DEFER[api]: the polarity-sensitive lookups (`hasConcept`,
    // `containsConcept`, `getConceptSaturationDescriptor`,
    // `getConceptDescriptorAndReapplyQueue`, `hasConceptSaturationDescriptor`,
    // `containsConceptSaturationDescriptor`), the insertion surface
    // (`insertConceptReturnClashed`, `insertConceptReapplicationReturnTriggered`),
    // `copyReapplyConceptSaturationLabelSet`, the iterator (`getIterator`),
    // `areAllConceptsInAdditionalHash`, and the modified-update-linker chain
    // mutators need the `CImplicationReapplyConceptSaturationDescriptor` /
    // `CSaturationModifiedProcessUpdateLinker` / `CConceptSetFlags` ports + `&mut
    // ProcessContext` to read descriptor negation/tag and allocate. Faithful bodies
    // land with those sub-structs.
}

impl Default for ReapplyConceptSaturationLabelSet {
    fn default() -> Self {
        Self::new(INVALID)
    }
}
