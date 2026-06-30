//! `process::sat_node` (port unit SD-4) — the saturation-phase completion-graph
//! node `CIndividualSaturationProcessNode`
//! (`Source/Reasoner/Kernel/Process/CIndividualSaturationProcessNode.{h,cpp}`).
//!
//! The lightweight twin of `CIndividualProcessNode` used by the cheap
//! non-branching saturation pre-pass. Unlike the full process node it carries
//! **no `mX`/`mUseX`/`mPrev` triple-buffers** — saturation is monotone, so there
//! is no branch save/restore here (per `manifest/05-process-units.md` SD-4).
//!
//! Complex method bodies (`initCopingIndividualSaturationProcessNode`,
//! `addRoleAssertion`, the lazy sub-struct getters, …) are DEFERRED to method
//! unit **SAT-1**; this unit defines the struct + `new`/`Default` + trivial
//! field accessors only.

#![allow(dead_code)]

use super::super::model::substrate::{Cint64, Id, NegLink, INVALID};
use super::super::model::IndividualId;
use super::SatNodeId;
// KONCLUDE-PORT-NOTE[api]: the not-yet-ported saturation extension/linker/cache
// classes (`CExtendedConceptReferenceLinkingData`,
// `CIndividualSaturationReferenceLinkingData`, the saturation satellites, the
// `CConceptSaturationDescriptor` shared with the databox, …) live as shared
// marker stubs in `process::stubs`; field types stay exact via their `Id<T>`
// aliases.
use super::stubs::{
    BackwardSaturationPropagationLinkId, ConceptSaturationDescriptorId,
    ConceptSaturationProcessLinkerId, ExtendedConceptReferenceLinkingDataId,
    IndividualSaturationProcessNodeCacheDataId, IndividualSaturationProcessNodeExtensionDataId,
    IndividualSaturationProcessNodeLinkerId, IndividualSaturationReferenceLinkingDataId,
    ReapplyConceptSaturationLabelSetId, RoleBackwardSaturationPropagationHashId,
};

/// Port of `CIndividualSaturationProcessNodeStatusFlags` (placeholder, by value).
/// A small flag word held inline (direct + indirect status); the concrete flag
/// masks land with the saturation status-flag unit.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct IndividualSaturationProcessNodeStatusFlags {
    pub flags: Cint64,
}

// ---------------------------------------------------------------------------
// CIndividualSaturationProcessNode
// ---------------------------------------------------------------------------

/// Port of `CIndividualSaturationProcessNode`
/// (`: public CIndividualProcessNodeReference`).
///
/// KONCLUDE-PORT-NOTE[ownership]: every `CXxx*` member becomes a typed `Id` into
/// the corresponding per-test arena (`Id::NONE` == the C++ `nullptr`); the two
/// `CXLinker<…>*` chains become `Vec`s and the one `CXNegLinker<…>*` chain a
/// `Vec<NegLink<…>>`. Behaviour is identical; only the representation differs.
///
/// KONCLUDE-PORT-NOTE[api]: the base `CIndividualProcessNodeReference`
/// (→ `CProcessReference`) has **no data members** (pure identity/context
/// handle), so it contributes no fields here; the context handle it abstracts is
/// stored directly as `process_context` below.
pub struct IndividualSaturationProcessNode {
    // --- context / allocator -------------------------------------------------
    // KONCLUDE-PORT-NOTE[ownership]: `CProcessContext*` is the ambient per-test
    // owner of all arenas, not itself an arena object; kept as an opaque
    // `Cint64` handle (sentinel `INVALID` == `nullptr`).
    pub process_context: Cint64, // CProcessContext* mProcessContext
    // KONCLUDE-PORT-NOTE[memory-pool]: `CMemoryAllocationManager*` — the bump/pool
    // allocator; the arena substrate replaces it, kept as an opaque handle.
    pub mem_alloc_man: Cint64, // CMemoryAllocationManager* mMemAllocMan

    // --- reference / linking data (owned sub-structs by pointer) -------------
    pub concept_saturation_link_ref_data: ExtendedConceptReferenceLinkingDataId, // mConceptSaturationLinkRefData
    pub individual_saturation_link_ref_data: IndividualSaturationReferenceLinkingDataId, // mIndividualSaturationLinkRefData
    pub role_back_prop_hash: RoleBackwardSaturationPropagationHashId, // mRoleBackPropHash
    pub reapply_con_sat_label_set: ReapplyConceptSaturationLabelSetId, // mReapplyConSatLabelSet
    pub indi_extension_data: IndividualSaturationProcessNodeExtensionDataId, // mIndiExtensionData
    pub indi_process_linker: IndividualSaturationProcessNodeLinkerId, // mIndiProcessLinker
    pub indi_completion_linker: IndividualSaturationProcessNodeLinkerId, // mIndiCompletionLinker
    pub concept_saturation_process_linker: ConceptSaturationProcessLinkerId, // mConceptSaturationProcessLinker

    // --- related saturation nodes (back-pointers → SatNodeId) ----------------
    pub substitute_indi_node: SatNodeId, // mSubstituteIndiNode
    pub copy_indi_node: SatNodeId,       // mCopyIndiNode

    // --- status flags (inline, by value) ------------------------------------
    pub direct_status_flags: IndividualSaturationProcessNodeStatusFlags, // mDirectStatusFlags
    pub indirect_status_flags: IndividualSaturationProcessNodeStatusFlags, // mIndirectStatusFlags

    // --- scalar / bool state -------------------------------------------------
    pub required_back_prop: bool,  // mRequiredBackProp
    pub data_value_applied: bool,  // mDataValueApplied
    pub clashed_con_sat_des_linker: ConceptSaturationDescriptorId, // mClashedConSatDesLinker (chain head)

    // --- dependency / connection linkers (intrusive chains → Vec) ------------
    // KONCLUDE-PORT-NOTE[ownership]: `CXNegLinker<CIndividualSaturationProcessNode*>*`
    // → `Vec<NegLink<SatNodeId>>` (each entry carries a negation bit).
    pub depending_indi_node_linker: Vec<NegLink<SatNodeId>>, // mDependingIndiNodeLinker
    // KONCLUDE-PORT-NOTE[ownership]: `CXLinker<CIndividualSaturationProcessNode*>*`
    // → `Vec<SatNodeId>` (plain intrusive node chain).
    pub non_inverse_connected_indi_node_linker: Vec<SatNodeId>, // mNonInverseConnectedIndiNodeLinker
    pub multiple_cardinality_ancestor_nodes_linker: Vec<SatNodeId>, // mMultipleCardinalityAncestorNodesLinker

    pub dep_saturation_indi_node: SatNodeId,    // mDepSaturationIndiNode
    pub direct_saturation_indi_node: SatNodeId, // mDirectSaturationIndiNode

    pub indi_id: Cint64, // mIndiID
    pub init_backward_prop_links: BackwardSaturationPropagationLinkId, // mInitBackwardPropLinks (chain head)

    pub nominal_indi_triples_assertions: bool,        // mNominalIndiTriplesAssertions
    pub loaded_nominal_indi_triples_assertions: bool, // mLoadedNominalIndiTriplesAssertions
    pub nominal_indi: IndividualId,            // mNominalIndi
    pub integrated_nominal_indi: IndividualId, // mIntegratedNominalIndi

    pub cache_data: IndividualSaturationProcessNodeCacheDataId, // mCacheData

    pub reference_indi_node: SatNodeId, // mReferenceIndiNode
    pub reference_mode: Cint64,         // mReferenceMode

    pub separated_saturation: bool,             // mSeparatedSaturation
    pub abox_individual_representation_node: bool, // mABoxIndividualRepresentationNode

    pub occurrence_statistics_collecting_required: bool, // mOccurrenceStatisticsCollectingRequired
    pub occurrence_statistics_collected: bool,           // mOccurrenceStatisticsCollected

    pub max_atleast_cardinality: Cint64, // mMaxAtleastCardinality
    pub max_atmost_cardinality: Cint64,  // mMaxAtmostCardinality
}

impl Default for IndividualSaturationProcessNode {
    /// Port of `CIndividualSaturationProcessNode::CIndividualSaturationProcessNode`
    /// (the default-constructed / freshly-allocated state, before `init*`).
    fn default() -> Self {
        IndividualSaturationProcessNode {
            process_context: INVALID,
            mem_alloc_man: INVALID,
            concept_saturation_link_ref_data: Id::NONE,
            individual_saturation_link_ref_data: Id::NONE,
            role_back_prop_hash: Id::NONE,
            reapply_con_sat_label_set: Id::NONE,
            indi_extension_data: Id::NONE,
            indi_process_linker: Id::NONE,
            indi_completion_linker: Id::NONE,
            concept_saturation_process_linker: Id::NONE,
            substitute_indi_node: Id::NONE,
            copy_indi_node: Id::NONE,
            direct_status_flags: IndividualSaturationProcessNodeStatusFlags::default(),
            indirect_status_flags: IndividualSaturationProcessNodeStatusFlags::default(),
            required_back_prop: false,
            data_value_applied: false,
            clashed_con_sat_des_linker: Id::NONE,
            depending_indi_node_linker: Vec::new(),
            non_inverse_connected_indi_node_linker: Vec::new(),
            multiple_cardinality_ancestor_nodes_linker: Vec::new(),
            dep_saturation_indi_node: Id::NONE,
            direct_saturation_indi_node: Id::NONE,
            indi_id: INVALID,
            init_backward_prop_links: Id::NONE,
            nominal_indi_triples_assertions: false,
            loaded_nominal_indi_triples_assertions: false,
            nominal_indi: Id::NONE,
            integrated_nominal_indi: Id::NONE,
            cache_data: Id::NONE,
            reference_indi_node: Id::NONE,
            reference_mode: INVALID,
            separated_saturation: false,
            abox_individual_representation_node: false,
            occurrence_statistics_collecting_required: false,
            occurrence_statistics_collected: false,
            max_atleast_cardinality: 0,
            max_atmost_cardinality: 0,
        }
    }
}

impl IndividualSaturationProcessNode {
    /// Port of the `CIndividualSaturationProcessNode(CProcessContext*)` ctor.
    pub fn new(process_context: Cint64) -> Self {
        IndividualSaturationProcessNode {
            process_context,
            ..Default::default()
        }
    }

    // --- trivial accessors (the C++ one-line getters/setters) ----------------

    /// Port of `getIndividualID`.
    pub fn get_individual_id(&self) -> Cint64 {
        self.indi_id
    }
    /// Port of `setIndividualID`.
    pub fn set_individual_id(&mut self, indi_id: Cint64) -> &mut Self {
        self.indi_id = indi_id;
        self
    }
    /// Port of `getReferenceMode`.
    pub fn get_reference_mode(&self) -> Cint64 {
        self.reference_mode
    }
    /// Port of `setReferenceMode`.
    pub fn set_reference_mode(&mut self, reference_mode: Cint64) -> &mut Self {
        self.reference_mode = reference_mode;
        self
    }
    /// Port of `getRequiredBackwardPropagation`.
    pub fn get_required_backward_propagation(&self) -> bool {
        self.required_back_prop
    }
    /// Port of `setRequiredBackwardPropagation`.
    pub fn set_required_backward_propagation(&mut self, required_back_prop: bool) -> &mut Self {
        self.required_back_prop = required_back_prop;
        self
    }
    /// Port of `isSeparated`.
    pub fn is_separated(&self) -> bool {
        self.separated_saturation
    }
    /// Port of `setSeparated`.
    pub fn set_separated(&mut self, separated: bool) -> &mut Self {
        self.separated_saturation = separated;
        self
    }
    /// Port of `getMaxAtleastCardinalityCandidate`.
    pub fn get_max_atleast_cardinality_candidate(&self) -> Cint64 {
        self.max_atleast_cardinality
    }
    /// Port of `getMaxAtmostCardinalityCandidate`.
    pub fn get_max_atmost_cardinality_candidate(&self) -> Cint64 {
        self.max_atmost_cardinality
    }

    // DEFER (SAT-1): initIndividualSaturationProcessNode, initRootIndividual…,
    // initCopingIndividualSaturationProcessNode (the only logic-bearing init, the
    // flat/label copy), initSubstituiting…, the lazy `get…(create)` sub-struct
    // allocators, the linker take/add/clear chains, addRoleAssertion, and the
    // status-flag handling. See `manifest/05-process-units.md` unit SAT-1.
}
