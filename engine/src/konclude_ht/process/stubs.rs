//! `process::stubs` — the SINGLE shared home for every not-yet-ported `Process/`
//! placeholder marker type and its `Id<T>` alias.
//!
//! KONCLUDE-PORT-NOTE[api]: the `Process/` layer references a large family of
//! helper / container / linker / cache classes that have not been ported yet
//! (the processing queues, blocking/saturation/backend hashes, the per-node
//! satellite extension structs, the assertion linker chains, …). Each SD struct
//! unit (`edge`/`descriptor`/`node`/`sat_node`/`satellites`/`databox`/
//! `dependency`) independently needed these as strongly-typed fields, so before
//! consolidation each file declared its own private markers — which duplicated
//! and (for `ConceptSaturationDescriptor`) diverged across files. This module is
//! the W2 coherence anchor: ONE canonical zero-size marker per not-yet-ported
//! class, addressed by an `Id<T>` into its eventual per-test arena
//! (`Id::NONE` == the C++ `nullptr`). When a class is really ported it relocates
//! from here to its own module and these stubs reconcile to it.
//!
//! The value-typed placeholders that a struct holds *by value* rather than by
//! pointer (e.g. `CReapplyQueue`, `CConceptSetSignature`, the
//! saturation-status-flag word) stay in their using module — only pointer-target
//! (`Id<T>`) markers live here.

#![allow(dead_code)]

use super::super::model::substrate::Id;

/// Declare a marker struct + its named `Id<T>` alias.
macro_rules! stub_id {
    ($($(#[$m:meta])* $name:ident => $id:ident),* $(,)?) => {
        $(
            $(#[$m])*
            #[derive(Debug, Default)]
            pub struct $name;
            pub type $id = Id<$name>;
        )*
    };
}

/// Declare marker structs only (used inline as `Id<Marker>` at the call site).
macro_rules! stub {
    ($($(#[$m:meta])* $name:ident),* $(,)?) => {
        $( $(#[$m])* #[derive(Debug, Default)] pub struct $name; )*
    };
}

// ===========================================================================
// SD-3 `CIndividualProcessNode` field targets (from `node.rs`).
// ===========================================================================
stub_id! {
    /// `CProcessContext*` — the ambient per-test owner. KONCLUDE-PORT-NOTE[ownership]:
    /// in the port this is the `&mut` context threaded through methods, not a real
    /// arena object; kept here as a back-handle field to mirror the C++ member.
    ProcessContext => ProcessContextId,
    /// `CMemoryAllocationManager*`. KONCLUDE-PORT-NOTE[memory-pool]: the arena model
    /// replaces the pool allocator; the field is retained for layout fidelity.
    MemoryAllocationManager => MemAllocId,
    ConceptProcessingQueue => ConceptProcessingQueueId,
    SuccessorRoleHash => SuccRoleHashId,
    // W2.7 reconcile: ConnectionSuccessorSet / DistinctHash / DisjointSuccessorRoleHash
    // relocated to `process::distinct`; their ids re-alias below.
    IndividualNodeSaturationBlockingData => IndiSatBlockDataId,
    // W2.7 reconcile: IndividualNodeBlockData relocated to
    // `process::reapply_sat::IndividualNodeBlockingTestData`; id re-aliases below.
    BlockingVariableBindingsAnalogousPropagationData => VarPropBlockDataId,
    IndividualNodeUnsatisfiableCacheRetrievalData => UnsatCacheRetId,
    IndividualNodeAnalizedConceptExpansionData => AnalizedConExpDataId,
    // W3.5b reconcile: SignatureBlockingIndividualNodeConceptExpansionData relocated to
    // `process::blocking_hash`; its `SigBlockConExpDataId` re-aliases below.
    ReusingIndividualNodeConceptExpansionData => ReusingConExpDataId,
    BlockingFollowSet => BlockingFollowSetId,
    // W3b reconcile: ConceptPropagationBindingSetHash / ConceptVariableBindingPathSetHash
    // relocated to `process::binding_hash`; their ids re-alias below.
    ConceptRepresentativePropagationSetHash => ConceptRepPropSetHashId,
    IndividualNodeModelData => IndividualNodeModelDataId,
    IndividualNodeSatisfiableCacheRetrievalData => SatCacheRetDataId,
    IndividualNodeSatisfiableCacheStoringData => SatCacheStoringDataId,
    IndividualNodeBackendCacheSynchronisationData => BackendSyncDataId,
    ReapplyConceptDescriptor => ReapplyConDescId,
    RoleBackwardPropagationHash => RoleBackPropHashId,
    IndividualProcessNodeLinker => IndividualProcessNodeLinkerId,
    ConceptProcessLinker => ConceptProcessLinkerId,
    NominalCachingLossReactivationData => ReactivationDataId,
    SuccessorIndividualATMOSTReactivationData => ATMOSTReactivationDataId,
    SuccessorConnectedNominalSet => NominalConnectionSetId,
    DatatypesValueSpaceData => DatatypesValueSpaceDataId,
    // W2.7 reconcile: IndividualNodeIncrementalExpansionData relocated to
    // `process::reapply_sat`; id re-aliases below.
    IndividualMergingHash => IndividualMergingHashId,
    // intrusive ontology-side assertion linker chain heads.
    // KONCLUDE-PORT-NOTE[ownership]: kept as single head-of-chain ids here; PN-2
    // decides whether to materialise each as a `Vec`.
    ConceptAssertionLinker => ConceptAssertionLinkerId,
    DataAssertionLinker => DataAssertionLinkerId,
    RoleAssertionLinker => RoleAssertionLinkerId,
    ReverseRoleAssertionLinker => ReverseRoleAssertionLinkerId,
    AdditionalProcessRoleAssertionsLinker => AdditionalRoleAssertionsLinkerId,
    AdditionalProcessDataAssertionsLinker => AdditionalDataAssertionsLinkerId,
    ProcessAssertedDataLiteralLinker => ProcessAssertedDataLiteralLinkerId,
}

// ===========================================================================
// W2.7 RECONCILE: the five W2 stub ids whose marker structs were ported for
// real now RE-ALIAS to their real targets. The alias NAME is unchanged (so the
// `node.rs` field types + every `use super::stubs::{…}` call site keep
// resolving); only the pointed-at type changes (stub marker → real struct).
// ===========================================================================
/// `CConnectionSuccessorSet*` — now `process::distinct::ConnectionSuccessorSet`.
pub type ConnSuccSetId = super::distinct::ConnectionSuccessorSetId;
/// `CDistinctHash*` — now `process::distinct::DistinctHash`.
pub type DistinctHashId = super::distinct::DistinctHashId;
/// `CDisjointSuccessorRoleHash*` — now `process::distinct::DisjointSuccessorRoleHash`.
pub type DisjointSuccRoleHashId = super::distinct::DisjointSuccessorRoleHashId;
/// `CIndividualNodeBlockData*` — runtime object is the derived
/// `process::reapply_sat::IndividualNodeBlockingTestData`.
pub type IndiBlockDataId = super::reapply_sat::BlockingTestDataId;
/// `CIndividualNodeIncrementalExpansionData*` — now
/// `process::reapply_sat::IndividualNodeIncrementalExpansionData`.
pub type IncExpDataId = super::reapply_sat::IncrementalExpansionDataId;
/// `CConceptPropagationBindingSetHash*` — now `process::binding_hash::ConceptPropagationBindingSetHash`.
pub type ConceptPropBindingSetHashId = super::binding_hash::ConceptPropagationBindingSetHashId;
/// `CConceptVariableBindingPathSetHash*` — now `process::binding_hash::ConceptVariableBindingPathSetHash`.
pub type ConceptVarBindPathSetHashId = super::binding_hash::ConceptVariableBindingPathSetHashId;
/// W3.5b reconcile: `CSignatureBlockingIndividualNodeConceptExpansionData*` — now
/// `process::blocking_hash::SignatureBlockingIndividualNodeConceptExpansionData`.
/// The alias NAME (`SigBlockConExpDataId`) is unchanged, so `node.rs`'s
/// `sig_block_con_exp_data` field + `pn4.rs` getters keep resolving.
pub type SigBlockConExpDataId =
    super::blocking_hash::SignatureBlockingIndividualNodeConceptExpansionDataId;

// ===========================================================================
// SD-4 `CIndividualSaturationProcessNode` field targets (from `sat_node.rs`).
// (`ConceptSaturationDescriptor` is shared with the databox — see below.)
// ===========================================================================
stub_id! {
    /// Port of `CExtendedConceptReferenceLinkingData`.
    ExtendedConceptReferenceLinkingData => ExtendedConceptReferenceLinkingDataId,
    /// Port of `CIndividualSaturationReferenceLinkingData`.
    IndividualSaturationReferenceLinkingData => IndividualSaturationReferenceLinkingDataId,
    /// Port of `CRoleBackwardSaturationPropagationHash`.
    RoleBackwardSaturationPropagationHash => RoleBackwardSaturationPropagationHashId,
    // W4.5 reconcile: ReapplyConceptSaturationLabelSet / IndividualSaturationProcessNodeExtensionData /
    // ConceptSaturationProcessLinker / BackwardSaturationPropagationLink relocated to
    // `saturation::satellites`; their ids + struct names re-alias / re-export below.
    /// Port of `CIndividualSaturationProcessNodeLinker`.
    IndividualSaturationProcessNodeLinker => IndividualSaturationProcessNodeLinkerId,
    /// Port of `CIndividualSaturationProcessNodeCacheData`.
    IndividualSaturationProcessNodeCacheData => IndividualSaturationProcessNodeCacheDataId,
}

// ===========================================================================
// W4.5 RECONCILE: the SD-4 saturation-satellite markers ported for real in
// `saturation::satellites` now RE-ALIAS (id) + RE-EXPORT (struct name) to their
// real targets. The alias / struct NAMES are unchanged, so every
// `use super::stubs::{…}` site (`sat_node.rs`, `db5.rs`, the s-units) keeps
// resolving; only the pointed-at type changes (stub marker → real struct).
// ===========================================================================
pub use super::super::saturation::satellites::{
    BackwardSaturationPropagationLink, ConceptSaturationDescriptor, ConceptSaturationProcessLinker,
    IndividualSaturationProcessNodeExtensionData, ReapplyConceptSaturationLabelSet,
};
/// `CConceptSaturationDescriptor*` — now `saturation::satellites::ConceptSaturationDescriptor`.
pub type ConceptSaturationDescriptorId =
    super::super::saturation::satellites::ConceptSaturationDescriptorId;
/// `CConceptSaturationProcessLinker*` — now `saturation::satellites::ConceptSaturationProcessLinker`.
pub type ConceptSaturationProcessLinkerId =
    super::super::saturation::satellites::ConceptSaturationProcessLinkerId;
/// `CBackwardSaturationPropagationLink*` — now `saturation::satellites::BackwardSaturationPropagationLink`.
pub type BackwardSaturationPropagationLinkId =
    super::super::saturation::satellites::BackwardSaturationPropagationLinkId;
/// `CReapplyConceptSaturationLabelSet*` — now `saturation::satellites::ReapplyConceptSaturationLabelSet`.
pub type ReapplyConceptSaturationLabelSetId =
    super::super::saturation::satellites::ReapplyConceptSaturationLabelSetId;
/// `CIndividualSaturationProcessNodeExtensionData*` — now
/// `saturation::satellites::IndividualSaturationProcessNodeExtensionData`.
pub type IndividualSaturationProcessNodeExtensionDataId =
    super::super::saturation::satellites::IndividualSaturationProcessNodeExtensionDataId;

// ===========================================================================
// SD-4 satellite (`satellites.rs`): the branching-merging candidate linker.
// ===========================================================================
stub_id! {
    /// Port of `CBranchingMergingIndividualNodeCandidateLinker` (intrusive
    /// candidate-node linker chain, not yet ported).
    BranchingMergingIndividualNodeCandidateLinker => CandidateLinkerId,
}

// ===========================================================================
// Shared between `sat_node.rs` and `databox.rs`.
// KONCLUDE-PORT-NOTE[api]: `CConceptSaturationDescriptor` was independently
// declared in both SD units (sat_node as `ConceptSaturationDescriptorId`,
// databox as `Id<ConceptSaturationDescriptor>`); W4.5 ports it for real in
// `saturation::satellites` — the struct + id re-export/re-alias is in the W4.5
// RECONCILE block above (so `Id<ConceptSaturationDescriptor>` in both sites now
// resolves to the real arena struct).
// ===========================================================================

// ===========================================================================
// SD-2 `CProcessingDataBox` field targets (from `databox.rs`). Used inline as
// `Id<Marker>` at the call site, so only the marker structs are needed.
// ===========================================================================
stub! {
    /// Port of `CIndividualVector`.
    IndividualVector,
    /// Port of `CIndividualProcessingQueue`.
    IndividualProcessingQueue,
    // `CIndividualProcessNodeVector` relocated to `process::node_resolution` (real
    // ported type, held by value on the databox) — no longer a stub marker.
    /// Port of `CIndividualUnsortedProcessingQueue`.
    IndividualUnsortedProcessingQueue,
    /// Port of `CIndividualLinkerRotationProcessingQueue`.
    IndividualLinkerRotationProcessingQueue,
    /// Port of `CIndividualDepthProcessingQueue`.
    IndividualDepthProcessingQueue,
    /// Port of `CIndividualConceptBatchProcessingQueue`.
    IndividualConceptBatchProcessingQueue,
    /// Port of `CIndividualCustomPriorityProcessingQueue`.
    IndividualCustomPriorityProcessingQueue,
    // W3.5b/W2.7 reconcile: `CSignatureBlockingCandidateHash` is the real ported
    // struct in `process::reapply_sat` (databox/db4 now hold `Id<reapply_sat::…>`).
    /// Port of `CSignatureBlockingReviewSet`.
    SignatureBlockingReviewSet,
    /// Port of `CIndividualReactivationProcessingQueue`.
    IndividualReactivationProcessingQueue,
    /// Port of `CReusingReviewData`.
    ReusingReviewData,
    // W3.5b reconcile: `CBlockingIndividualNodeCandidateHash` is the real ported
    // struct in `process::blocking_hash` (databox now holds `Id<blocking_hash::…>`).
    /// Port of `CBlockingIndividualNodeLinkedCandidateHash`.
    BlockingIndividualNodeLinkedCandidateHash,
    /// Port of `CNodeSwitchHistory`.
    NodeSwitchHistory,
    /// Port of `CBranchingTree`.
    BranchingTree,
    /// Port of `CConceptVector`.
    ConceptVector,
    /// Port of `CConceptNominalSchemaGroundingHash`.
    ConceptNominalSchemaGroundingHash,
    /// Port of `CVariableBindingPathMergingHash`.
    VariableBindingPathMergingHash,
    /// Port of `CRepresentativeVariableBindingPathSetHash`.
    RepresentativeVariableBindingPathSetHash,
    /// Port of `CRepresentativeVariableBindingPathJoiningKeyHash`.
    RepresentativeVariableBindingPathJoiningKeyHash,
    /// Port of `CRepresentativeJoiningHash`.
    RepresentativeJoiningHash,
    /// Port of `CRepresentativeVariableBindingPathHash`.
    RepresentativeVariableBindingPathHash,
    /// Port of `CNominalCachingLossReactivationHash`.
    NominalCachingLossReactivationHash,
    /// Port of `CMarkerIndividualNodeHash`.
    MarkerIndividualNodeHash,
    /// Port of `CIndividualRepresentativeBackendCacheLoadedAssociationHash`.
    IndividualRepresentativeBackendCacheLoadedAssociationHash,
    /// Port of `CIndividualRepresentativeBackendCacheConceptSetLabelProcessingHash`.
    IndividualRepresentativeBackendCacheConceptSetLabelProcessingHash,
    /// Port of `CIndividualDelayedBackendInitializationProcessingQueue`.
    IndividualDelayedBackendInitializationProcessingQueue,
    /// Port of `CBackendNeighbourExpansionControllingData`.
    BackendNeighbourExpansionControllingData,
    /// Port of `CBackendNeighbourExpansionQueue`.
    BackendNeighbourExpansionQueue,
    /// Port of `CIndividualSaturationProcessNodeVector`.
    IndividualSaturationProcessNodeVector,
    /// Port of `CCriticalIndividualNodeProcessingQueue`.
    CriticalIndividualNodeProcessingQueue,
    /// Port of `CCriticalIndividualNodeConceptTestSet`.
    CriticalIndividualNodeConceptTestSet,
    /// Port of `CSaturationNominalDependentNodeHash`.
    SaturationNominalDependentNodeHash,
    /// Port of `CSaturationInfluencedNominalSet`.
    SaturationInfluencedNominalSet,
    /// Port of `CSaturationSuccessorExtensionIndividualNodeProcessingQueue`.
    SaturationSuccessorExtensionIndividualNodeProcessingQueue,
    /// Port of `CReferredIndividualTrackingVector`.
    ReferredIndividualTrackingVector,
    /// Payload of `CIndividualSaturationSuccessorLinkDataLinker`.
    IndividualSaturationSuccessorLinkData,
    /// Payload of `CConceptSaturationProcessLinker`.
    ConceptSaturationProcess,
    /// Payload of `CRoleSaturationProcessLinker`.
    RoleSaturationProcess,
}
