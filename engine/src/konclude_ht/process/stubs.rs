//! `process::stubs` — the SINGLE shared home for every not-yet-ported `Process/`
//! placeholder marker type and its `Id<T>` alias.
//!
//! KONCLUDE-PORT-NOTE[api]: the `Process/` layer references a large family of
//! helper / container / linker / cache classes that have not been ported yet
//! (remaining processing queues, blocking/saturation/backend hashes, and the
//! per-node satellite extension structs). Each SD struct
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

use super::super::model::substrate::{Arena, Cint64, Id};
pub use super::analized_concept_expansion::IndividualNodeAnalizedConceptExpansionData;
pub use super::backend_control::BackendNeighbourExpansionControllingData;
use super::edge::IndividualLinkEdge;
use super::node::IndividualProcessNode;
use super::{EdgeId, NodeId, TrackPointId};
pub type AnalizedConExpDataId =
    super::analized_concept_expansion::IndividualNodeAnalizedConceptExpansionDataId;
pub type BackendNeighbourExpansionControllingDataId =
    super::backend_control::BackendNeighbourExpansionControllingDataId;
pub use super::blocking_hash::ReusingReviewData;
pub type ReusingReviewDataId = super::blocking_hash::ReusingReviewDataId;
pub use super::referred_tracking::ReferredIndividualTrackingVector;
pub type ReferredIndividualTrackingVectorId =
    super::referred_tracking::ReferredIndividualTrackingVectorId;
pub use super::reactivation::NominalCachingLossReactivationHash;
pub use super::sat_nominal::{
    SaturationInfluencedNominalSet, SaturationNominalConnectionType,
    SaturationNominalDependentNodeData, SaturationNominalDependentNodeHash,
    SaturationNominalDependentNodeHashData,
};
pub use super::sat_queue::{
    CriticalIndividualNodeConceptTestSet, CriticalIndividualNodeProcessingQueue,
    CriticalSaturationConceptQueue, CriticalSaturationConceptQueueType,
    CriticalSaturationConceptTypeQueues, SaturationIndividualNodeProcessingQueue,
    SaturationSuccessorExtensionIndividualNodeProcessingQueue,
};
pub type SaturationInfluencedNominalSetId = super::sat_nominal::SaturationInfluencedNominalSetId;
pub type SaturationNominalDependentNodeDataId =
    super::sat_nominal::SaturationNominalDependentNodeDataId;
pub type SaturationNominalDependentNodeHashId =
    super::sat_nominal::SaturationNominalDependentNodeHashId;
pub type CriticalIndividualNodeProcessingQueueId =
    super::sat_queue::CriticalIndividualNodeProcessingQueueId;
pub type CriticalIndividualNodeConceptTestSetId =
    super::sat_queue::CriticalIndividualNodeConceptTestSetId;
pub type SaturationIndividualNodeProcessingQueueId =
    super::sat_queue::SaturationIndividualNodeProcessingQueueId;
pub type SaturationSuccessorExtensionIndividualNodeProcessingQueueId =
    super::sat_queue::SaturationSuccessorExtensionIndividualNodeProcessingQueueId;
pub type CriticalSaturationConceptQueueId = super::sat_queue::CriticalSaturationConceptQueueId;
pub type CriticalSaturationConceptTypeQueuesId =
    super::sat_queue::CriticalSaturationConceptTypeQueuesId;

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
    // queue-port reconcile: ConceptProcessingQueue relocated to `process::queues`
    // (real ported per-node concept queue); its `ConceptProcessingQueueId`
    // re-aliases below.
    // u15 reconcile: SuccessorRoleHash relocated to `process::succ_role_hash`
    // (real ported backend); its `SuccRoleHashId` re-aliases below.
    // W2.7 reconcile: ConnectionSuccessorSet / DistinctHash / DisjointSuccessorRoleHash
    // relocated to `process::distinct`; their ids re-alias below.
    // W136 reconcile: IndividualNodeSaturationBlockingData relocated to
    // `process::sat_block`; its id re-aliases below.
    // W2.7 reconcile: IndividualNodeBlockData relocated to
    // `process::reapply_sat::IndividualNodeBlockingTestData`; id re-aliases below.
    BlockingVariableBindingsAnalogousPropagationData => VarPropBlockDataId,
    // W118 reconcile: IndividualNodeUnsatisfiableCacheRetrievalData relocated to
    // `process::unsat_retrieval::IndividualNodeUnsatisfiableOccurenceCacheRetrievalData`;
    // id re-aliases below.
    // PN-4 W2 reconcile: IndividualNodeAnalizedConceptExpansionData relocated to
    // `process::analized_concept_expansion`; id re-aliases above.
    // W3.5b reconcile: SignatureBlockingIndividualNodeConceptExpansionData relocated to
    // `process::blocking_hash`; its `SigBlockConExpDataId` re-aliases below.
    // W167 reconcile: ReusingIndividualNodeConceptExpansionData relocated to
    // `process::blocking_hash`; its `ReusingConExpDataId` re-aliases below.
    // W144 reconcile: BlockingFollowSet relocated to `process::blocking_follow`;
    // its id re-aliases below.
    // W3b reconcile: ConceptPropagationBindingSetHash / ConceptVariableBindingPathSetHash
    // relocated to `process::binding_hash`; their ids re-alias below.
    // W50 reconcile: ConceptRepresentativePropagationSetHash relocated to
    // `process::representative`; its id re-aliases below.
    IndividualNodeModelData => IndividualNodeModelDataId,
    IndividualNodeSatisfiableCacheRetrievalData => SatCacheRetDataId,
    IndividualNodeSatisfiableCacheStoringData => SatCacheStoringDataId,
    // W319 reconcile: IndividualNodeBackendCacheSynchronisationData relocated to
    // `process::backend_sync`; its id re-aliases below.
    ReapplyConceptDescriptor => ReapplyConDescId,
    RoleBackwardPropagationHash => RoleBackPropHashId,
    ConceptProcessLinker => ConceptProcessLinkerId,
    // W142 reconcile: NominalCachingLossReactivationData relocated to
    // `process::reactivation`; its id re-aliases below.
    SuccessorIndividualATMOSTReactivationData => ATMOSTReactivationDataId,
    DatatypesValueSpaceData => DatatypesValueSpaceDataId,
    // W2.7 reconcile: IndividualNodeIncrementalExpansionData relocated to
    // `process::reapply_sat`; id re-aliases below.
    // u15 reconcile: IndividualMergingHash relocated to `process::merging_hash`
    // (real ported hash); its `IndividualMergingHashId` re-aliases below.
    // intrusive ontology-side assertion linker chain heads.
    // KONCLUDE-PORT-NOTE[ownership]: kept as single head-of-chain ids here; PN-2
    // decides whether to materialise each as a `Vec`.
    ConceptAssertionLinker => ConceptAssertionLinkerId,
    DataAssertionLinker => DataAssertionLinkerId,
    RoleAssertionLinker => RoleAssertionLinkerId,
    ReverseRoleAssertionLinker => ReverseRoleAssertionLinkerId,
}

impl SuccessorIndividualATMOSTReactivationData {
    /// Port placeholder for `initSuccessorIndividualATMOSTReactivationData(prev)`.
    pub fn init_successor_individual_atmost_reactivation_data(
        &mut self,
        _prev: Option<&Self>,
    ) -> &mut Self {
        self
    }
}

impl DatatypesValueSpaceData {
    /// Port placeholder for `initDatatypesValueSpaceData(prev)`.
    pub fn init_datatypes_value_space_data(&mut self, _prev: Option<&Self>) -> &mut Self {
        self
    }
}

/// Port of `CProcessAssertedDataLiteralLinker`.
#[derive(Debug, Clone)]
pub struct ProcessAssertedDataLiteralLinker {
    next: ProcessAssertedDataLiteralLinkerId,
    data_literal: Cint64,
    dependency_track_point: TrackPointId,
}

pub type ProcessAssertedDataLiteralLinkerId = Id<ProcessAssertedDataLiteralLinker>;

impl Default for ProcessAssertedDataLiteralLinker {
    fn default() -> Self {
        Self::new()
    }
}

impl ProcessAssertedDataLiteralLinker {
    pub fn new() -> Self {
        Self {
            next: ProcessAssertedDataLiteralLinkerId::NONE,
            data_literal: 0,
            dependency_track_point: TrackPointId::NONE,
        }
    }

    /// Port of `CProcessAssertedDataLiteralLinker::initProcessDataLiteralLinker`.
    pub fn init_process_data_literal_linker(
        &mut self,
        data_literal: Cint64,
        dep_track_point: TrackPointId,
    ) -> &mut Self {
        self.data_literal = data_literal;
        self.dependency_track_point = dep_track_point;
        self
    }

    /// Port of `CProcessAssertedDataLiteralLinker::getDataLiteral`.
    pub fn data_literal(&self) -> Cint64 {
        self.data_literal
    }

    pub fn dependency_track_point(&self) -> TrackPointId {
        self.dependency_track_point
    }

    pub fn next(&self) -> ProcessAssertedDataLiteralLinkerId {
        self.next
    }

    pub fn set_next(&mut self, next: ProcessAssertedDataLiteralLinkerId) -> &mut Self {
        self.next = next;
        self
    }
}

/// Port of `CAdditionalProcessRoleAssertionsLinker`.
#[derive(Debug, Clone)]
pub struct AdditionalProcessRoleAssertionsLinker {
    next: AdditionalRoleAssertionsLinkerId,
    individual: Cint64,
    role_assertion_linker: RoleAssertionLinkerId,
    reverse_role_assertion_linker: ReverseRoleAssertionLinkerId,
    dependency_track_point: TrackPointId,
}

pub type AdditionalRoleAssertionsLinkerId = Id<AdditionalProcessRoleAssertionsLinker>;

impl Default for AdditionalProcessRoleAssertionsLinker {
    fn default() -> Self {
        Self::new()
    }
}

impl AdditionalProcessRoleAssertionsLinker {
    pub fn new() -> Self {
        Self {
            next: AdditionalRoleAssertionsLinkerId::NONE,
            individual: 0,
            role_assertion_linker: RoleAssertionLinkerId::NONE,
            reverse_role_assertion_linker: ReverseRoleAssertionLinkerId::NONE,
            dependency_track_point: TrackPointId::NONE,
        }
    }

    /// Port of `CAdditionalProcessRoleAssertionsLinker::initAdditionalProcessRoleAssertionsLinker`.
    pub fn init_additional_process_role_assertions_linker(
        &mut self,
        individual: Cint64,
        role_assertion_linker: RoleAssertionLinkerId,
        reverse_role_assertion_linker: ReverseRoleAssertionLinkerId,
        dep_track_point: TrackPointId,
    ) -> &mut Self {
        self.individual = individual;
        self.role_assertion_linker = role_assertion_linker;
        self.reverse_role_assertion_linker = reverse_role_assertion_linker;
        self.dependency_track_point = dep_track_point;
        self
    }

    /// Port of `CAdditionalProcessRoleAssertionsLinker::getIndividual`.
    pub fn individual(&self) -> Cint64 {
        self.individual
    }

    /// Port of `CAdditionalProcessRoleAssertionsLinker::getRoleAssertionLinker`.
    pub fn role_assertion_linker(&self) -> RoleAssertionLinkerId {
        self.role_assertion_linker
    }

    /// Port of `CAdditionalProcessRoleAssertionsLinker::getReverseRoleAssertionLinker`.
    pub fn reverse_role_assertion_linker(&self) -> ReverseRoleAssertionLinkerId {
        self.reverse_role_assertion_linker
    }

    pub fn dependency_track_point(&self) -> TrackPointId {
        self.dependency_track_point
    }

    pub fn next(&self) -> AdditionalRoleAssertionsLinkerId {
        self.next
    }

    pub fn set_next(&mut self, next: AdditionalRoleAssertionsLinkerId) -> &mut Self {
        self.next = next;
        self
    }
}

/// Port of `CAdditionalProcessDataAssertionsLinker`.
#[derive(Debug, Clone)]
pub struct AdditionalProcessDataAssertionsLinker {
    next: AdditionalDataAssertionsLinkerId,
    individual: Cint64,
    data_assertion_linker: DataAssertionLinkerId,
    dependency_track_point: TrackPointId,
}

pub type AdditionalDataAssertionsLinkerId = Id<AdditionalProcessDataAssertionsLinker>;

impl Default for AdditionalProcessDataAssertionsLinker {
    fn default() -> Self {
        Self::new()
    }
}

impl AdditionalProcessDataAssertionsLinker {
    pub fn new() -> Self {
        Self {
            next: AdditionalDataAssertionsLinkerId::NONE,
            individual: 0,
            data_assertion_linker: DataAssertionLinkerId::NONE,
            dependency_track_point: TrackPointId::NONE,
        }
    }

    /// Port of `CAdditionalProcessDataAssertionsLinker::initAdditionalProcessDataAssertionsLinker`.
    pub fn init_additional_process_data_assertions_linker(
        &mut self,
        individual: Cint64,
        data_assertion_linker: DataAssertionLinkerId,
        dep_track_point: TrackPointId,
    ) -> &mut Self {
        self.individual = individual;
        self.data_assertion_linker = data_assertion_linker;
        self.dependency_track_point = dep_track_point;
        self
    }

    /// Port of `CAdditionalProcessDataAssertionsLinker::getIndividual`.
    pub fn individual(&self) -> Cint64 {
        self.individual
    }

    /// Port of `CAdditionalProcessDataAssertionsLinker::getDataAssertionLinker`.
    pub fn data_assertion_linker(&self) -> DataAssertionLinkerId {
        self.data_assertion_linker
    }

    pub fn dependency_track_point(&self) -> TrackPointId {
        self.dependency_track_point
    }

    pub fn next(&self) -> AdditionalDataAssertionsLinkerId {
        self.next
    }

    pub fn set_next(&mut self, next: AdditionalDataAssertionsLinkerId) -> &mut Self {
        self.next = next;
        self
    }
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
/// `CIndividualNodeRepresentativeMemoryBackendCacheSynchronisationData*` —
/// now `process::backend_sync::IndividualNodeBackendCacheSynchronisationData`.
pub type BackendSyncDataId = super::backend_sync::BackendSyncDataId;
/// `CIndividualNodeSaturationBlockingData*` — now
/// `process::sat_block::IndividualNodeSaturationBlockingData`.
pub type IndiSatBlockDataId = Id<super::sat_block::IndividualNodeSaturationBlockingData>;
/// `CSuccessorConnectedNominalSet*` — now `process::nominal_conn::SuccessorConnectedNominalSet`.
pub type NominalConnectionSetId = super::nominal_conn::SuccessorConnectedNominalSetId;
/// `CBlockingFollowSet*` — now `process::blocking_follow::BlockingFollowSet`.
pub type BlockingFollowSetId = super::blocking_follow::BlockingFollowSetId;
/// `CNominalCachingLossReactivationData*` — now
/// `process::reactivation::NominalCachingLossReactivationData`.
pub type ReactivationDataId = super::reactivation::NominalCachingLossReactivationDataId;
/// `CNominalCachingLossReactivationHash*` — now
/// `process::reactivation::NominalCachingLossReactivationHash`.
pub type NominalCachingLossReactivationHashId =
    super::reactivation::NominalCachingLossReactivationHashId;
/// `CConceptPropagationBindingSetHash*` — now `process::binding_hash::ConceptPropagationBindingSetHash`.
pub type ConceptPropBindingSetHashId = super::binding_hash::ConceptPropagationBindingSetHashId;
/// `CConceptVariableBindingPathSetHash*` — now `process::binding_hash::ConceptVariableBindingPathSetHash`.
pub type ConceptVarBindPathSetHashId = super::binding_hash::ConceptVariableBindingPathSetHashId;
/// `CConceptRepresentativePropagationSetHash*` — now
/// `process::representative::ConceptRepresentativePropagationSetHash`.
pub type ConceptRepPropSetHashId = super::representative::ConceptRepresentativePropagationSetHashId;
/// W3.5b reconcile: `CSignatureBlockingIndividualNodeConceptExpansionData*` — now
/// `process::blocking_hash::SignatureBlockingIndividualNodeConceptExpansionData`.
/// The alias NAME (`SigBlockConExpDataId`) is unchanged, so `node.rs`'s
/// `sig_block_con_exp_data` field + `pn4.rs` getters keep resolving.
pub type SigBlockConExpDataId =
    super::blocking_hash::SignatureBlockingIndividualNodeConceptExpansionDataId;
/// `CReusingIndividualNodeConceptExpansionData*` — now
/// `process::blocking_hash::ReusingIndividualNodeConceptExpansionData`.
pub type ReusingConExpDataId = super::blocking_hash::ReusingIndividualNodeConceptExpansionDataId;
pub use super::blocking_hash::ReusingIndividualNodeConceptExpansionData;
pub use super::blocking_hash::SignatureBlockingReviewSet;
/// `CSignatureBlockingReviewSet*` — now `process::blocking_hash::SignatureBlockingReviewSet`.
pub type SignatureBlockingReviewSetId = super::blocking_hash::SignatureBlockingReviewSetId;
/// u15 reconcile: `CSuccessorRoleHash*` — now `process::succ_role_hash::SuccessorRoleHash`.
/// The alias NAME (`SuccRoleHashId`) is unchanged, so `node.rs`'s
/// `succ_role_hash` / `use_` / `prev_` fields + pn3's getters keep resolving.
pub type SuccRoleHashId = super::succ_role_hash::SuccessorRoleHashId;
/// u15 reconcile: `CIndividualMergingHash*` — now `process::merging_hash::IndividualMergingHash`.
/// The alias NAME (`IndividualMergingHashId`) is unchanged, so `node.rs`'s
/// `use_individual_merging_hash` / `loc_` fields + pn6's getter keep resolving.
pub type IndividualMergingHashId = super::merging_hash::IndividualMergingHashId;
/// W118 reconcile: `CIndividualNodeUnsatisfiableCacheRetrievalData*` — runtime
/// object is the occurrence-cache derived
/// `process::unsat_retrieval::IndividualNodeUnsatisfiableOccurenceCacheRetrievalData`.
/// The alias NAME (`UnsatCacheRetId`) is unchanged, so `node.rs`'s
/// `indi_unsat_cache_ret` / `prev_indi_unsat_cache_ret` fields + pn4's getters
/// keep resolving.
pub type UnsatCacheRetId =
    super::unsat_retrieval::IndividualNodeUnsatisfiableOccurenceCacheRetrievalDataId;
/// `CNodeSwitchHistory*` — now `process::node_switch_history::NodeSwitchHistory`.
pub type NodeSwitchHistoryId = super::node_switch_history::NodeSwitchHistoryId;
pub use super::node_switch_history::NodeSwitchHistory;
/// `CBranchingTree*` — now `process::branching_tree::BranchingTree`.
pub type BranchingTreeId = super::branching_tree::BranchingTreeId;
pub use super::branching_tree::BranchingTree;

// ===========================================================================
// queue-port RECONCILE: the three workhorse individual queues + the per-node
// concept queue are ported for real in `process::queues`. The struct NAMES are
// re-exported (so `databox.rs` / `db3.rs` `use super::stubs::{…}` sites keep
// resolving) and the ids re-alias — only the pointed-at type changes (stub
// marker → real queue struct).
// ===========================================================================
pub use super::queues::{
    ConceptProcessingQueue, IndividualConceptBatchProcessingQueue,
    IndividualCustomPriorityProcessingQueue, IndividualDepthProcessingQueue,
    IndividualLinkerRotationProcessingQueue, IndividualProcessNodeDescriptor,
    IndividualProcessingQueue, IndividualReactivationProcessingQueue,
    IndividualUnsortedProcessingQueue,
};
/// `CConceptProcessingQueue*` — now `process::queues::ConceptProcessingQueue`.
pub type ConceptProcessingQueueId = super::queues::ConceptProcessingQueueId;
/// `CIndividualConceptBatchProcessingQueue*` — now `process::queues::IndividualConceptBatchProcessingQueue`.
pub type IndividualConceptBatchProcessingQueueId =
    super::queues::IndividualConceptBatchProcessingQueueId;
/// `CIndividualCustomPriorityProcessingQueue*` — now `process::queues::IndividualCustomPriorityProcessingQueue`.
pub type IndividualCustomPriorityProcessingQueueId =
    super::queues::IndividualCustomPriorityProcessingQueueId;
/// `CIndividualReactivationProcessingQueue*` — now `process::queues::IndividualReactivationProcessingQueue`.
pub type IndividualReactivationProcessingQueueId =
    super::queues::IndividualReactivationProcessingQueueId;
/// `CIndividualProcessNodeDescriptor*` — now `process::queues::IndividualProcessNodeDescriptor`.
pub type IndividualProcessNodeDescriptorId = super::queues::IndividualProcessNodeDescriptorId;
/// `CIndividualProcessingQueue*` — now `process::queues::IndividualProcessingQueue`.
pub type IndividualProcessingQueueId = super::queues::IndividualProcessingQueueId;

// ===========================================================================
// SD-4 `CIndividualSaturationProcessNode` field targets (from `sat_node.rs`).
// (`ConceptSaturationDescriptor` is shared with the databox — see below.)
// ===========================================================================
stub_id! {
    /// Port of `CIndividualSaturationReferenceLinkingData`.
    IndividualSaturationReferenceLinkingData => IndividualSaturationReferenceLinkingDataId,
    // W4.5 reconcile: ReapplyConceptSaturationLabelSet / IndividualSaturationProcessNodeExtensionData /
    // ConceptSaturationProcessLinker / BackwardSaturationPropagationLink relocated to
    // `saturation::satellites`; their ids + struct names re-alias / re-export below.
    // W429 reconcile: IndividualSaturationProcessNodeLinker relocated to
    // `process::sat_linker`; its id + struct name re-alias / re-export below.
    /// Port of `CIndividualSaturationProcessNodeCacheData`.
    IndividualSaturationProcessNodeCacheData => IndividualSaturationProcessNodeCacheDataId,
}

// W137 reconcile: ExtendedConceptReferenceLinkingData relocated to
// `process::sat_ref`; its id + struct name re-alias / re-export here.
pub use super::sat_ref::ExtendedConceptReferenceLinkingData;
pub type ExtendedConceptReferenceLinkingDataId =
    super::sat_ref::ExtendedConceptReferenceLinkingDataId;

// W429 reconcile: real `CIndividualSaturationProcessNodeLinker`.
pub use super::sat_linker::IndividualSaturationProcessNodeLinker;
pub type IndividualSaturationProcessNodeLinkerId =
    super::sat_linker::IndividualSaturationProcessNodeLinkerId;

// ===========================================================================
// W4.5 RECONCILE: the SD-4 saturation-satellite markers ported for real in
// `saturation::satellites` now RE-ALIAS (id) + RE-EXPORT (struct name) to their
// real targets. The alias / struct NAMES are unchanged, so every
// `use super::stubs::{…}` site (`sat_node.rs`, `db5.rs`, the s-units) keeps
// resolving; only the pointed-at type changes (stub marker → real struct).
// ===========================================================================
pub use super::super::saturation::satellites::{
    BackwardSaturationPropagationLink, ConceptSaturationDescriptor, ConceptSaturationProcessLinker,
    CriticalPredecessorRoleCardinalityData, CriticalPredecessorRoleCardinalityHash,
    IndividualSaturationProcessNodeExtensionData, IndividualSaturationSuccessorLinkDataLinker,
    LinkedDataValueAssertionSaturationData, ReapplyConceptSaturationLabelSet,
    RoleBackwardSaturationPropagationHash, SaturationAtmostSuccessorMergingData,
    SaturationAtmostSuccessorMergingHash, SaturationAtmostSuccessorMergingHashData,
    SaturationDisjunctCommonConceptCountHashData, SaturationDisjunctCommonConceptExtractionData,
    SaturationDisjunctExtractionLinker, SaturationIndividualNodeDatatypeData,
    SaturationIndividualNodeSuccessorExtensionData, SaturationSuccessorRoleAssertionLinker,
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
/// `CRoleBackwardSaturationPropagationHash*` — now
/// `saturation::satellites::RoleBackwardSaturationPropagationHash`.
pub type RoleBackwardSaturationPropagationHashId =
    super::super::saturation::satellites::RoleBackwardSaturationPropagationHashId;
/// `CIndividualSaturationProcessNodeExtensionData*` — now
/// `saturation::satellites::IndividualSaturationProcessNodeExtensionData`.
pub type IndividualSaturationProcessNodeExtensionDataId =
    super::super::saturation::satellites::IndividualSaturationProcessNodeExtensionDataId;
/// `CSaturationDisjunctCommonConceptExtractionData*` — now
/// `saturation::satellites::SaturationDisjunctCommonConceptExtractionData`.
pub type SaturationDisjunctCommonConceptExtractionDataId =
    super::super::saturation::satellites::SaturationDisjunctCommonConceptExtractionDataId;
/// `CSaturationDisjunctExtractionLinker*` — now
/// `saturation::satellites::SaturationDisjunctExtractionLinker`.
pub type SaturationDisjunctExtractionLinkerId =
    super::super::saturation::satellites::SaturationDisjunctExtractionLinkerId;
/// `CSaturationDisjunctCommonConceptCountHashData*` — now represented by
/// `saturation::satellites::SaturationDisjunctCommonConceptCountHashData`.
pub type SaturationDisjunctCommonConceptCountHashDataId =
    super::super::saturation::satellites::SaturationDisjunctCommonConceptCountHashDataId;
/// `CSaturationATMOSTSuccessorMergingData*` — now
/// `saturation::satellites::SaturationAtmostSuccessorMergingData`.
pub type SaturationAtmostSuccessorMergingDataId =
    super::super::saturation::satellites::SaturationAtmostSuccessorMergingDataId;
/// `CSaturationATMOSTSuccessorMergingHash*` — now
/// `saturation::satellites::SaturationAtmostSuccessorMergingHash`.
pub type SaturationAtmostSuccessorMergingHashId =
    super::super::saturation::satellites::SaturationAtmostSuccessorMergingHashId;
/// `CSaturationATMOSTSuccessorMergingHashData*` — now represented by
/// `saturation::satellites::SaturationAtmostSuccessorMergingHashData`.
pub type SaturationAtmostSuccessorMergingHashDataId =
    super::super::saturation::satellites::SaturationAtmostSuccessorMergingHashDataId;
/// `CLinkedDataValueAssertionSaturationData*` — now
/// `saturation::satellites::LinkedDataValueAssertionSaturationData`.
pub type LinkedDataValueAssertionSaturationDataId =
    super::super::saturation::satellites::LinkedDataValueAssertionSaturationDataId;
/// `CSaturationIndividualNodeSuccessorExtensionData*` — now
/// `saturation::satellites::SaturationIndividualNodeSuccessorExtensionData`.
pub type SaturationIndividualNodeSuccessorExtensionDataId =
    super::super::saturation::satellites::SaturationIndividualNodeSuccessorExtensionDataId;
/// `CSaturationIndividualNodeDatatypeData*` — now
/// `saturation::satellites::SaturationIndividualNodeDatatypeData`.
pub type SaturationIndividualNodeDatatypeDataId =
    super::super::saturation::satellites::SaturationIndividualNodeDatatypeDataId;
/// `CSaturationSuccessorRoleAssertionLinker*` — now
/// `saturation::satellites::SaturationSuccessorRoleAssertionLinker`.
pub type SaturationSuccessorRoleAssertionLinkerId =
    super::super::saturation::satellites::SaturationSuccessorRoleAssertionLinkerId;
/// `CIndividualSaturationSuccessorLinkDataLinker*` — now
/// `saturation::satellites::IndividualSaturationSuccessorLinkDataLinker`.
pub type IndividualSaturationSuccessorLinkDataLinkerId =
    super::super::saturation::satellites::IndividualSaturationSuccessorLinkDataLinkerId;
/// `CCriticalPredecessorRoleCardinalityData*` — now
/// `saturation::satellites::CriticalPredecessorRoleCardinalityData`.
pub type CriticalPredecessorRoleCardinalityDataId =
    super::super::saturation::satellites::CriticalPredecessorRoleCardinalityDataId;
/// `CCriticalPredecessorRoleCardinalityHash*` — now
/// `saturation::satellites::CriticalPredecessorRoleCardinalityHash`.
pub type CriticalPredecessorRoleCardinalityHashId =
    super::super::saturation::satellites::CriticalPredecessorRoleCardinalityHashId;

// ===========================================================================
// SD-4 satellite (`satellites.rs`): branching-merging candidate linker.
// ===========================================================================

/// Port of `CBranchingMergingIndividualNodeCandidateLinker`.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct BranchingMergingIndividualNodeCandidateLinker {
    /// `CLinkerBase::mNext`.
    pub next: CandidateLinkerId,
    /// `mMergingIndiNodeCandidate`.
    pub merging_indi_node_candidate: NodeId,
    /// `mMergingLink`.
    pub merging_link: EdgeId,
}

pub type CandidateLinkerId = Id<BranchingMergingIndividualNodeCandidateLinker>;

impl Default for BranchingMergingIndividualNodeCandidateLinker {
    fn default() -> Self {
        Self {
            next: CandidateLinkerId::NONE,
            merging_indi_node_candidate: NodeId::NONE,
            merging_link: EdgeId::NONE,
        }
    }
}

impl BranchingMergingIndividualNodeCandidateLinker {
    /// Port of `CBranchingMergingIndividualNodeCandidateLinker::CBranchingMergingIndividualNodeCandidateLinker`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `initBranchingMergingIndividualNodeCandidate(prevRest)`.
    pub fn init_branching_merging_individual_node_candidate_from(
        &mut self,
        prev_rest: Option<&Self>,
    ) -> &mut Self {
        self.next = CandidateLinkerId::NONE;
        if let Some(prev_rest) = prev_rest {
            self.merging_indi_node_candidate = prev_rest.merging_indi_node_candidate;
            self.merging_link = prev_rest.merging_link;
        } else {
            self.merging_indi_node_candidate = NodeId::NONE;
            self.merging_link = EdgeId::NONE;
        }
        self
    }

    /// Port of `initBranchingMergingIndividualNodeCandidate(mergingIndiNodeCand, mergingLink)`.
    pub fn init_branching_merging_individual_node_candidate(
        &mut self,
        merging_indi_node_cand: NodeId,
        merging_link: EdgeId,
    ) -> &mut Self {
        self.next = CandidateLinkerId::NONE;
        self.merging_link = merging_link;
        self.merging_indi_node_candidate = merging_indi_node_cand;
        self
    }

    /// Port of `getMergingIndividualNodeCandidate`.
    pub fn get_merging_individual_node_candidate(&self) -> NodeId {
        self.merging_indi_node_candidate
    }

    /// Port of `setMergingIndividualNodeCandidate`.
    pub fn set_merging_individual_node_candidate(
        &mut self,
        merging_indi_node_cand: NodeId,
    ) -> &mut Self {
        self.merging_indi_node_candidate = merging_indi_node_cand;
        self
    }

    /// Port of `getMergingIndividualLink`.
    pub fn get_merging_individual_link(&self) -> EdgeId {
        self.merging_link
    }

    /// Port of `setMergingIndividualLink`.
    pub fn set_merging_individual_link(&mut self, merging_link: EdgeId) -> &mut Self {
        self.merging_link = merging_link;
        self
    }

    /// Port of `CLinkerBase::getNext`.
    pub fn get_next(&self) -> CandidateLinkerId {
        self.next
    }

    /// Port of `CLinkerBase::clearNext`.
    pub fn clear_next(&mut self) -> &mut Self {
        self.next = CandidateLinkerId::NONE;
        self
    }

    /// Port-facing equivalent of `linker->append(appendingList)`.
    pub fn append(
        linkers: &mut Arena<Self>,
        linker: CandidateLinkerId,
        appending_list: CandidateLinkerId,
    ) -> CandidateLinkerId {
        if linker.is_none() {
            return appending_list;
        }
        let mut last = linker;
        loop {
            let next = linkers.get(last).next;
            if next.is_none() {
                break;
            }
            last = next;
        }
        linkers.get_mut(last).next = appending_list;
        linker
    }

    /// Port of `isCandidateBlockableAndCreator`.
    pub fn is_candidate_blockable_and_creator(
        &self,
        nodes: &Arena<IndividualProcessNode>,
        edges: &Arena<IndividualLinkEdge>,
    ) -> bool {
        self.merging_indi_node_candidate.is_some()
            && self.merging_link.is_some()
            && nodes
                .get(self.merging_indi_node_candidate)
                .is_blockable_individual()
            && edges.get(self.merging_link).get_creator_individual()
                == self.merging_indi_node_candidate
    }

    /// Port of `operator<=`.
    pub fn leq(&self, _other: &Self) -> bool {
        true
    }
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
    // queue-port reconcile: `CIndividualProcessingQueue` relocated to
    // `process::queues` (real ported queue); re-exported above.
    // `CIndividualProcessNodeVector` relocated to `process::node_resolution` (real
    // ported type, held by value on the databox) — no longer a stub marker.
    // queue-port reconcile: CIndividualUnsortedProcessingQueue /
    // CIndividualLinkerRotationProcessingQueue / CIndividualDepthProcessingQueue
    // relocated to `process::queues` (real ported queues); re-exported below.
    // queue-port reconcile: `CIndividualConceptBatchProcessingQueue` relocated to
    // `process::queues` (real ported queue); re-exported below.
    // W3.5b/W2.7 reconcile: `CSignatureBlockingCandidateHash` is the real ported
    // struct in `process::reapply_sat` (databox/db4 now hold `Id<reapply_sat::…>`).
    // W165 reconcile: `CSignatureBlockingReviewSet` relocated to
    // `process::blocking_hash`; its id re-aliases above.
    // queue-port reconcile: `CIndividualReactivationProcessingQueue` relocated to
    // `process::queues` (real ported queue); re-exported above.
    // W166 reconcile: `CReusingReviewData` relocated to
    // `process::blocking_hash`; its id re-aliases above.
    // W3.5b reconcile: `CBlockingIndividualNodeCandidateHash` is the real ported
    // struct in `process::blocking_hash` (databox now holds `Id<blocking_hash::…>`).
    /// Port of `CBlockingIndividualNodeLinkedCandidateHash`.
    BlockingIndividualNodeLinkedCandidateHash,
    // W306 reconcile: `CNodeSwitchHistory` relocated to
    // `process::node_switch_history` (real ported type); re-exported above.
    // W307 reconcile: `CBranchingTree` relocated to
    // `process::branching_tree` (real ported type); re-exported above.
    /// Port of `CConceptVector`.
    ConceptVector,
    /// Port of `CConceptNominalSchemaGroundingHash`.
    ConceptNominalSchemaGroundingHash,
    /// Port of `CVariableBindingPathMergingHash`.
    VariableBindingPathMergingHash,
    // W453 reconcile: `CNominalCachingLossReactivationHash` relocated to
    // `process::reactivation`; its id re-aliases above.
    /// Port of `CMarkerIndividualNodeHash`.
    MarkerIndividualNodeHash,
    /// Port of `CIndividualRepresentativeBackendCacheLoadedAssociationHash`.
    IndividualRepresentativeBackendCacheLoadedAssociationHash,
    /// Port of `CIndividualRepresentativeBackendCacheConceptSetLabelProcessingHash`.
    IndividualRepresentativeBackendCacheConceptSetLabelProcessingHash,
    /// Port of `CIndividualDelayedBackendInitializationProcessingQueue`.
    IndividualDelayedBackendInitializationProcessingQueue,
    // W168 reconcile: `CBackendNeighbourExpansionControllingData` relocated to
    // `process::backend_control`; its id re-aliases above.
    /// Port of `CBackendNeighbourExpansionQueue`.
    BackendNeighbourExpansionQueue,
    /// Port of `CIndividualSaturationProcessNodeVector`.
    IndividualSaturationProcessNodeVector,
    // W449 reconcile: `CSaturationIndividualNodeProcessingQueue` and
    // `CCriticalIndividualNodeProcessingQueue` relocated to `process::sat_queue`;
    // their ids re-alias above.
    // W452 reconcile: `CCriticalIndividualNodeConceptTestSet` relocated to
    // `process::sat_queue`; its id re-aliases above.
    // W451 reconcile: `CSaturationNominalDependentNode{Data,Hash,HashData}`
    // relocated to `process::sat_nominal`; ids re-alias above.
    // W450 reconcile: `CSaturationInfluencedNominalSet` relocated to
    // `process::sat_nominal`; its id re-aliases above.
    // W448 reconcile: `CSaturationSuccessorExtensionIndividualNodeProcessingQueue`
    // relocated to `process::sat_queue`; its id re-aliases above.
    /// Payload of `CIndividualSaturationSuccessorLinkDataLinker`.
    IndividualSaturationSuccessorLinkData,
    /// Payload of `CConceptSaturationProcessLinker`.
    ConceptSaturationProcess,
    /// Payload of `CRoleSaturationProcessLinker`.
    RoleSaturationProcess,
}

// W53 reconcile: `CRepresentativeVariableBindingPathSetHash` relocated to the
// real representative subsystem. Re-export the struct name so existing databox
// imports keep resolving while the pointed-at type becomes the ported hash.
pub use super::representative::RepresentativeVariableBindingPathSetHash;
pub type RepresentativeVariableBindingPathSetHashId =
    super::representative::RepresentativeVariableBindingPathSetHashId;

// DB-2 reconcile: `CRepresentativeVariableBindingPathHash` relocated to the
// real representative subsystem. Re-export the struct name so databox imports
// keep resolving while the pointed-at type becomes the ported hash.
pub use super::representative::RepresentativeVariableBindingPathHash;
pub type RepresentativeVariableBindingPathHashId =
    super::representative::RepresentativeVariableBindingPathHashId;

// W63 reconcile: `CRepresentativeJoiningHash` relocated to the real
// representative subsystem. Re-export the struct name so databox imports keep
// resolving while the pointed-at type becomes the ported hash.
pub use super::representative::RepresentativeJoiningHash;
pub type RepresentativeJoiningHashId = super::representative::RepresentativeJoiningHashId;

// W64 reconcile: `CRepresentativeVariableBindingPathJoiningKeyHash` relocated to
// the real representative subsystem. Re-export the struct name so databox imports
// keep resolving while the pointed-at type becomes the ported interning hash.
pub use super::representative::RepresentativeVariableBindingPathJoiningKeyHash;
pub type RepresentativeVariableBindingPathJoiningKeyHashId =
    super::representative::RepresentativeVariableBindingPathJoiningKeyHashId;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::konclude_ht::model::substrate::Arena;
    use crate::konclude_ht::process::edge::IndividualLinkEdge;
    use crate::konclude_ht::process::node::{IndividualProcessNode, IndividualType};
    use crate::konclude_ht::process::TrackPointId;

    #[test]
    fn branching_merging_candidate_linker_initializes_and_copies_payload() {
        let node = NodeId::new(7);
        let edge = EdgeId::new(11);
        let mut linker = BranchingMergingIndividualNodeCandidateLinker::new();

        linker.init_branching_merging_individual_node_candidate(node, edge);
        assert_eq!(linker.get_merging_individual_node_candidate(), node);
        assert_eq!(linker.get_merging_individual_link(), edge);
        assert_eq!(linker.get_next(), CandidateLinkerId::NONE);

        let mut copied = BranchingMergingIndividualNodeCandidateLinker::new();
        copied.init_branching_merging_individual_node_candidate_from(Some(&linker));
        assert_eq!(copied.get_merging_individual_node_candidate(), node);
        assert_eq!(copied.get_merging_individual_link(), edge);
        assert_eq!(copied.get_next(), CandidateLinkerId::NONE);

        copied.init_branching_merging_individual_node_candidate_from(None);
        assert_eq!(copied.get_merging_individual_node_candidate(), NodeId::NONE);
        assert_eq!(copied.get_merging_individual_link(), EdgeId::NONE);
    }

    #[test]
    fn branching_merging_candidate_linker_appends_chain_to_existing_head() {
        let mut linkers = Arena::new();
        let first = linkers.push(BranchingMergingIndividualNodeCandidateLinker::new());
        let second = linkers.push(BranchingMergingIndividualNodeCandidateLinker::new());
        let old_head = linkers.push(BranchingMergingIndividualNodeCandidateLinker::new());
        linkers.get_mut(first).next = second;

        let head =
            BranchingMergingIndividualNodeCandidateLinker::append(&mut linkers, first, old_head);

        assert_eq!(head, first);
        assert_eq!(linkers.get(first).get_next(), second);
        assert_eq!(linkers.get(second).get_next(), old_head);
        linkers.get_mut(first).clear_next();
        assert_eq!(linkers.get(first).get_next(), CandidateLinkerId::NONE);
    }

    #[test]
    fn branching_merging_candidate_linker_detects_blockable_creator() {
        let mut nodes = Arena::new();
        let mut edges = Arena::new();
        let mut node = IndividualProcessNode::default();
        node.set_individual_type(IndividualType::Blockable);
        let node_id = nodes.push(node);

        let mut edge = IndividualLinkEdge::new();
        edge.init_individual_link_edge(
            node_id,
            node_id,
            NodeId::NONE,
            crate::konclude_ht::model::RoleId::NONE,
            TrackPointId::NONE,
        );
        let edge_id = edges.push(edge);

        let mut linker = BranchingMergingIndividualNodeCandidateLinker::new();
        linker.init_branching_merging_individual_node_candidate(node_id, edge_id);
        assert!(linker.is_candidate_blockable_and_creator(&nodes, &edges));

        nodes
            .get_mut(node_id)
            .set_individual_type(IndividualType::Nominal);
        assert!(!linker.is_candidate_blockable_and_creator(&nodes, &edges));
    }
}
