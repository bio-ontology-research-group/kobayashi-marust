//! `process::context` — the per-satisfiability-test arena-owning container.
//!
//! Port of Konclude `Source/Reasoner/Kernel/Process/CProcessContext.{h,cpp}`
//! (`CProcessContext : public CTaskContext`) and its concrete
//! `CProcessContextBase`. In Konclude this object IS the per-test ownership root:
//! it holds `CProcessMemoryPoolAllocationManager* mUsedMemMan`, the pool from
//! which EVERY per-test object (`CIndividualProcessNode`, the descriptors, the
//! dependency nodes, the satellites, …) is bump-allocated, plus the process
//! tagger and the statistics gatherer. The `CProcessingDataBox`'s
//! `mIndividualProcessNodeVector` and friends only TRACK (hold `*`s into) those
//! pooled objects — they are not the storage. When a test ends the pool is reset
//! and every object dies at once; backtracking rewinds to a saved watermark.
//!
//! The static `CConcept`/`CRole`/`CIndividual`/`CVariable` do NOT live here:
//! they are the terminology (TBox/RBox), shared read-only across all tests. They
//! get their own `OntologyArenas` (see `model::ontology`).
//!
//! KONCLUDE-PORT-NOTE[ownership]: this is the concrete realisation of the global
//! substrate decision (`model/substrate.rs`) and of the deferred "task context
//! owns the arenas" note. Konclude's single typeless memory pool becomes one
//! typed `Arena<T>` per per-test object kind, each indexed by the matching
//! `Id<T>` already aliased in `process/mod.rs`. A raw `CXxx*` is an `Id<T>`; a
//! pool allocation is `Arena::push`; a pool reset / backtrack is
//! `Arena::truncate_to(watermark)`.
//!
//! KONCLUDE-PORT-NOTE[memory-pool]: the C++ `mUsedMemMan` pool allocator is gone
//! as a runtime object; the `Arena<T>` fields ARE the pool, split by type so the
//! port keeps the typed-id safety. The tagger / stats / scheduler handles that
//! `CProcessContext` also carries stay opaque `Cint64` for now (filled when those
//! subsystems are ported).
//!
//! ## Accessor convention (the C++ pointer-deref replacement)
//!
//! Every C++ `obj->method()` where `obj` is a pool pointer becomes, in the port,
//! a two-step `ctx.<arena>(id).method()`: resolve the `Id<T>` against the arena
//! to borrow the object, then call the method on it. Each arena exposes a trio:
//!
//! | C++                              | Rust (port)                          |
//! |----------------------------------|--------------------------------------|
//! | `indi->getX()`                   | `ctx.node(id).get_x()`               |
//! | `indi->setX(v)` (mutating)       | `ctx.node_mut(id).set_x(v)`          |
//! | `new CIndividualProcessNode(…)`  | `ctx.alloc_node(IndividualProcessNode::new(…))` |
//!
//! The trio names per arena are `node/node_mut/alloc_node`,
//! `con_desc/con_desc_mut/alloc_con_desc`, `dep_node/dep_node_mut/alloc_dep_node`,
//! and so on (one consistent stem per object kind, listed in the impl below).

#![allow(dead_code)]

use std::collections::HashMap;

use super::super::model::substrate::{Arena, Cint64, Id, NegLink, INVALID};
use super::super::model::{ConceptId, RoleId};

use super::analized_concept_expansion::{
    AnalizedConceptExpansionLinker, AnalizedConceptExpansionLinkerId,
    IndividualNodeAnalizedConceptExpansionData, IndividualNodeAnalizedConceptExpansionDataId,
};
use super::backend_sync::{BackendSyncDataId, IndividualNodeBackendCacheSynchronisationData};
use super::dependency::{
    BranchTreeNode, BranchingInstruction, DependencyLink, DependencyNode, DependencyTrackPoint,
};
use super::descriptor::{ClashDescriptor, ConceptDescriptor, ConceptProcessDescriptor};
use super::edge::{DisjointEdge, DistinctEdge, IndividualLinkEdge};
use super::grounding_hash::{
    ConceptNominalSchemaGroundingData, ConceptNominalSchemaGroundingDataId,
    ConceptNominalSchemaGroundingHash, ConceptNominalSchemaGroundingHashId,
};
use super::individual_process_linker::{
    IndividualProcessNodeLinker, IndividualProcessNodeLinkerId,
};
use super::marker_hash::{
    MarkerIndividualNodeData, MarkerIndividualNodeDataId, MarkerIndividualNodeHash,
    MarkerIndividualNodeHashData, MarkerIndividualNodeHashId,
};
use super::node::IndividualProcessNode;
use super::node_resolution::ProcessTagger;
use super::node_switch_history::{NodeSwitchHistory, NodeSwitchHistoryId};
use super::rs1::{RoleSuccessorIterator, RoleSuccessorLinkIterator};
use super::sat_block::IndividualNodeSaturationBlockingData;
use super::sat_exp_store::{
    IndividualNodeSatisfiableExpandingCacheStoringData,
    IndividualNodeSatisfiableExpandingCacheStoringDataId,
};
use super::sat_linker::{
    IndividualSaturationProcessNodeLinker, IndividualSaturationProcessNodeLinkerId,
};
use super::sat_node::IndividualSaturationProcessNode;
use super::sat_nominal::{
    SaturationInfluencedNominalSet, SaturationInfluencedNominalSetId,
    SaturationNominalConnectionType, SaturationNominalDependentNodeData,
    SaturationNominalDependentNodeDataId, SaturationNominalDependentNodeHash,
    SaturationNominalDependentNodeHashId,
};
use super::sat_queue::{
    CriticalIndividualNodeConceptTestSet, CriticalIndividualNodeConceptTestSetId,
    CriticalIndividualNodeProcessingQueue, CriticalIndividualNodeProcessingQueueId,
    CriticalSaturationConceptQueue, CriticalSaturationConceptQueueId,
    CriticalSaturationConceptQueueType, CriticalSaturationConceptTypeQueues,
    CriticalSaturationConceptTypeQueuesId,
    SaturationSuccessorExtensionIndividualNodeProcessingQueue,
    SaturationSuccessorExtensionIndividualNodeProcessingQueueId,
};
use super::sat_ref::ExtendedConceptReferenceLinkingData;
use super::satellites::{
    AdditionalDesDepMapRef, AdditionalMapSlot, BranchingMergingProcessingRestrictionSpecification,
    ConceptDescriptorDependencyReapplyData, CoreConceptDescriptor, CoreConceptDescriptorId,
    LabelSetMapAlias, ReapplyConceptLabelSet, ReapplyRoleSuccessorHash,
};
use super::stubs::{
    ATMOSTReactivationDataId, AdditionalDataAssertionsLinkerId,
    AdditionalProcessDataAssertionsLinker, AdditionalProcessRoleAssertionsLinker,
    AdditionalRoleAssertionsLinkerId, BranchingMergingIndividualNodeCandidateLinker,
    CandidateLinkerId, DatatypesValueSpaceData, DatatypesValueSpaceDataId, IndiSatBlockDataId,
    ProcessAssertedDataLiteralLinker, ProcessAssertedDataLiteralLinkerId,
    SuccessorIndividualATMOSTReactivationData,
};
use super::{
    BranchInstrId, BranchNodeId, ClashDescId, ConDescId, ConProcDescId, DepLinkId, DependencyId,
    DisjointEdgeId, DistinctEdgeId, EdgeId, LabelSetId, NodeId, RestrictionSpecId, RoleSuccHashId,
    SatNodeId, TrackPointId,
};

// --- W2.7 satellite arenas: variable-binding-path subsystem ---
use super::varbind::{
    VarBindingDescriptorId, VarBindingId, VarBindingPathDescriptorId, VarBindingPathId,
    VarBindingPathJoiningDataId, VarBindingPathSetId, VarBindingTriggerLinkerId, VariableBinding,
    VariableBindingDescriptor, VariableBindingPath, VariableBindingPathDescriptor,
    VariableBindingPathJoiningData, VariableBindingPathJoiningHash,
    VariableBindingPathJoiningHashId, VariableBindingPathMergingHash,
    VariableBindingPathMergingHashId, VariableBindingPathSet, VariableBindingTriggerHash,
    VariableBindingTriggerHashId, VariableBindingTriggerLinker,
};
// --- W2.7 satellite arenas: distinct / connection-successor / disjoint-role ---
use super::distinct::{
    ConnectionSuccessorCorrectionHash, ConnectionSuccessorCorrectionHashId, ConnectionSuccessorSet,
    ConnectionSuccessorSetId, ConnectionSuccessorSetIterator, DisjointSuccessorRoleHash,
    DisjointSuccessorRoleHashId, DistinctHash, DistinctHashId,
};
// --- W2.7 satellite arenas: reapply / signature-blocking / incremental-expansion ---
use super::reapply_sat::{
    BlockingAltDataId, BlockingAlternativeSignatureBlockingCandidateData, BlockingTestDataId,
    CondensedReapplyConceptDescriptor, CondensedReapplyConceptDescriptorId,
    CondensedReapplyQueueIterator, IncrementalExpansionDataId, IndividualNodeBlockingTestData,
    IndividualNodeIncrementalExpansionData, LabelSetMapEntry, ReapplyConceptDescriptor,
    ReapplyConceptDescriptorId, SigBlockCandHashId, SignatureBlockingCandidateHash,
};
use super::rs1::ReapplyQueueIterator;
// --- u15 merge / nominal-expansion satellites ---
use super::distinct::DisjointSuccessorRoleIterator;
use super::merging_hash::{IndividualMergingHash, IndividualMergingHashId};
use super::nominal_conn::{
    SaturationIndividualNodeNominalHandlingData, SaturationIndividualNodeNominalHandlingDataId,
    SuccessorConnectedNominalSet, SuccessorConnectedNominalSetId,
};
use super::queues::{
    ConceptProcessingQueue, ConceptProcessingQueueId, IndividualConceptBatchProcessingQueue,
    IndividualConceptBatchProcessingQueueId, IndividualCustomPriorityProcessingQueue,
    IndividualCustomPriorityProcessingQueueId, IndividualDepthProcessingQueue,
    IndividualDepthProcessingQueueId, IndividualLinkerRotationProcessingQueue,
    IndividualLinkerRotationProcessingQueueId, IndividualProcessNodeDescriptor,
    IndividualProcessNodeDescriptorId, IndividualProcessingQueue, IndividualProcessingQueueId,
    IndividualReactivationProcessingQueue, IndividualReactivationProcessingQueueId,
    IndividualUnsortedProcessingQueue, IndividualUnsortedProcessingQueueId,
};
use super::reactivation::{
    NominalCachingLossReactivationData, NominalCachingLossReactivationDataId,
    NominalCachingLossReactivationHash, NominalCachingLossReactivationHashId,
};
use super::referred_tracking::{
    ReferredIndividualTrackingVector, ReferredIndividualTrackingVectorId,
};
use super::role_backward_prop::{
    BackwardPropagationLink, BackwardPropagationLinkId, BackwardPropagationReapplyDescriptor,
    BackwardPropagationReapplyDescriptorId, RoleBackwardPropagationHash,
    RoleBackwardPropagationHashData, RoleBackwardPropagationHashId,
};
use super::succ_role_hash::{
    SuccessorIterator, SuccessorRoleHash, SuccessorRoleHashId, SuccessorRoleIterator,
};
use super::unsat_retrieval::{
    IndividualNodeUnsatisfiableOccurenceCacheRetrievalData,
    IndividualNodeUnsatisfiableOccurenceCacheRetrievalDataId,
};
// --- W3b node-owned binding-set container hashes ---
use super::backend_control::{
    BackendNeighbourExpansionControllingData, BackendNeighbourExpansionControllingDataId,
};
use super::binding_hash::{
    ConceptPropagationBindingSetHash, ConceptPropagationBindingSetHashId,
    ConceptVariableBindingPathSetHash, ConceptVariableBindingPathSetHashId,
};
use super::blocking_follow::{BlockingFollowSet, BlockingFollowSetId};
use super::branching_tree::{BranchingTree, BranchingTreeId};
use super::concept_process_linker::{ConceptProcessLinker, ConceptProcessLinkerId};
// --- W3c propagation-binding subsystem arenas (propagation_binding.rs) ---
use super::propagation_binding::{
    PropagationBinding, PropagationBindingDescriptor, PropagationBindingDescriptorId,
    PropagationBindingId, PropagationBindingReapplyConceptDescriptor,
    PropagationBindingReapplyConceptDescriptorId, PropagationBindingReapplyConceptHash,
    PropagationBindingReapplyConceptHashId, PropagationBindingSet, PropagationBindingSetId,
    PropagationRepresentativeTransitionExtension, PropagationRepresentativeTransitionExtensionId,
    PropagationVariableBindingTransitionExtension, PropagationVariableBindingTransitionExtensionId,
};
// --- W3.5r representative variable-binding-path-set subsystem arenas (representative.rs) ---
use super::representative::{
    ConceptRepresentativePropagationSetHash, ConceptRepresentativePropagationSetHashId,
    RepresentativeJoiningData, RepresentativeJoiningDataId, RepresentativeJoiningHash,
    RepresentativeJoiningHashData, RepresentativeJoiningHashId,
    RepresentativePropagationDescriptor, RepresentativePropagationDescriptorId,
    RepresentativePropagationSet, RepresentativePropagationSetId,
    RepresentativeVariableBindingPathHash, RepresentativeVariableBindingPathHashId,
    RepresentativeVariableBindingPathJoiningKeyData,
    RepresentativeVariableBindingPathJoiningKeyDataId,
    RepresentativeVariableBindingPathJoiningKeyHash,
    RepresentativeVariableBindingPathJoiningKeyHashData,
    RepresentativeVariableBindingPathJoiningKeyHashId, RepresentativeVariableBindingPathSetData,
    RepresentativeVariableBindingPathSetDataId, RepresentativeVariableBindingPathSetHash,
    RepresentativeVariableBindingPathSetHashId, RepresentativeVariableBindingPathSetJoiningData,
    RepresentativeVariableBindingPathSetJoiningDataId,
    RepresentativeVariableBindingPathSetJoiningHash,
    RepresentativeVariableBindingPathSetJoiningHashId,
    RepresentativeVariableBindingPathSetMigrateData,
    RepresentativeVariableBindingPathSetMigrateDataId,
};
// --- W3.5b blocking-individual-node candidate + signature-blocking concept-expansion (blocking_hash.rs) ---
use super::blocking_hash::{
    BlockingCandidateHashData, BlockingIndividualNodeCandidateData,
    BlockingIndividualNodeCandidateDataId, BlockingIndividualNodeCandidateHash,
    BlockingIndividualNodeCandidateHashId, BlockingIndividualNodeLinkedCandidateData,
    BlockingIndividualNodeLinkedCandidateDataId, BlockingIndividualNodeLinkedCandidateHash,
    BlockingIndividualNodeLinkedCandidateHashId, BlockingIndividualNodeLinker,
    BlockingIndividualNodeLinkerId, ReusingIndividualNodeConceptExpansionData,
    ReusingIndividualNodeConceptExpansionDataId, ReusingReviewData, ReusingReviewDataId,
    SignatureBlockingIndividualNodeConceptExpansionData,
    SignatureBlockingIndividualNodeConceptExpansionDataId, SignatureBlockingReviewSet,
    SignatureBlockingReviewSetId,
};
// --- W4.5 saturation-layer per-test satellites (saturation::satellites) ---
use super::super::saturation::satellites::{
    BackwardSaturationPropagationLink, BackwardSaturationPropagationLinkId,
    BackwardSaturationPropagationReapplyDescriptor,
    BackwardSaturationPropagationReapplyDescriptorId, ConceptSaturationDescriptor,
    ConceptSaturationDescriptorId, ConceptSaturationDescriptorReapplyData,
    ConceptSaturationProcessLinker, ConceptSaturationProcessLinkerId,
    CriticalPredecessorRoleCardinalityData, CriticalPredecessorRoleCardinalityDataId,
    CriticalPredecessorRoleCardinalityHash, CriticalPredecessorRoleCardinalityHashId,
    DataValueRoleAssertionLinker, DataValueRoleAssertionLinkerId,
    ImplicationReapplyConceptSaturationDescriptor, ImplicationReapplyConceptSaturationDescriptorId,
    IndividualSaturationProcessNodeExtensionData, IndividualSaturationProcessNodeExtensionDataId,
    IndividualSaturationSuccessorLinkDataLinker, IndividualSaturationSuccessorLinkDataLinkerId,
    LinkedDataValueAssertionSaturationData, LinkedDataValueAssertionSaturationDataId,
    LinkedRoleSaturationSuccessorData, LinkedRoleSaturationSuccessorDataId,
    LinkedRoleSaturationSuccessorHash, LinkedRoleSaturationSuccessorHashId,
    ReapplyConceptSaturationLabelSet, ReapplyConceptSaturationLabelSetId,
    RoleBackwardSaturationPropagationHash, RoleBackwardSaturationPropagationHashData,
    RoleBackwardSaturationPropagationHashId, RoleSaturationProcessLinker,
    RoleSaturationProcessLinkerId, SaturationAtmostSuccessorMergingData,
    SaturationAtmostSuccessorMergingDataId, SaturationAtmostSuccessorMergingHash,
    SaturationAtmostSuccessorMergingHashId, SaturationConceptExtensionMap,
    SaturationConceptExtensionMapId, SaturationDisjunctCommonConceptExtractionData,
    SaturationDisjunctCommonConceptExtractionDataId, SaturationDisjunctExtractionLinker,
    SaturationDisjunctExtractionLinkerId, SaturationIndividualNodeAllConceptsExtensionData,
    SaturationIndividualNodeAllConceptsExtensionDataId, SaturationIndividualNodeDatatypeData,
    SaturationIndividualNodeDatatypeDataId, SaturationIndividualNodeExtensionResolveData,
    SaturationIndividualNodeExtensionResolveDataId, SaturationIndividualNodeExtensionResolveHash,
    SaturationIndividualNodeExtensionResolveHashId,
    SaturationIndividualNodeFunctionalConceptsExtensionData,
    SaturationIndividualNodeFunctionalConceptsExtensionDataId,
    SaturationIndividualNodeSuccessorExtensionData,
    SaturationIndividualNodeSuccessorExtensionDataId,
    SaturationLinkedSuccessorIndividualAllConceptsExtensionData,
    SaturationLinkedSuccessorIndividualAllConceptsExtensionDataId,
    SaturationModifiedProcessUpdateLinker, SaturationModifiedProcessUpdateLinkerId,
    SaturationSuccessorAllConceptExtensionData, SaturationSuccessorAllConceptExtensionDataId,
    SaturationSuccessorConceptExtensionMap, SaturationSuccessorConceptExtensionMapId,
    SaturationSuccessorData, SaturationSuccessorDataId, SaturationSuccessorExtensionData,
    SaturationSuccessorExtensionDataId, SaturationSuccessorFunctionalConceptExtensionData,
    SaturationSuccessorFunctionalConceptExtensionDataId, SaturationSuccessorRoleAssertionLinker,
    SaturationSuccessorRoleAssertionLinkerId,
};

/// Generate the `get / get_mut / alloc` accessor trio for one arena field.
///
/// `obj->method()` (C++) ≡ `ctx.$get(id).method()` (Rust);
/// `obj->mutate()`       ≡ `ctx.$get_mut(id).mutate()`;
/// `new CXxx(…)`         ≡ `ctx.$alloc(Xxx::new(…))`.
macro_rules! arena_accessors {
    ($field:ident, $ty:ty, $id:ty, $get:ident, $get_mut:ident, $alloc:ident) => {
        /// Resolve an id to a shared borrow (the `obj->` read path).
        #[inline]
        pub fn $get(&self, id: $id) -> &$ty {
            self.$field.get(id)
        }
        /// Resolve an id to a mutable borrow (the `obj->` mutate path).
        /// Routed through the branch-epoch journal: under an open epoch the
        /// first mutation of a pre-epoch slot saves a rollback clone
        /// (zero-cost when no epoch is open).
        #[inline]
        pub fn $get_mut(&mut self, id: $id) -> &mut $ty {
            self.$field.get_mut_journaled(id)
        }
        /// Pool-allocate a new object, returning its stable id (`new CXxx(…)`).
        #[inline]
        pub fn $alloc(&mut self, v: $ty) -> $id {
            self.$field.push(v)
        }
    };
}

/// Port of `CProcessContext` / `CProcessContextBase`.
///
/// The per-test arena-owning container. One `Arena<T>` per per-test object kind
/// (the typed split of Konclude's single per-task memory pool); plus the opaque
/// tagger / stats / scheduler handles `CProcessContext` declares.
///
/// Field order groups the arenas by subsystem (nodes, edges, descriptors,
/// dependency spine, satellites) for readability; allocation order within a test
/// is whatever the completion engine drives, not the field order.
pub struct ProcessContext {
    /// Open branch-epoch count (in-process COW; see `push_branch_epoch`).
    branch_epoch_depth: usize,
    // --- graph nodes ---
    /// `CIndividualProcessNode` pool. The databox's `individual_process_node_vector`
    /// holds `NodeId`s into THIS arena (it tracks; this owns).
    nodes: Arena<IndividualProcessNode>,
    /// `CIndividualSaturationProcessNode` pool.
    sat_nodes: Arena<IndividualSaturationProcessNode>,

    // --- the three edge kinds ---
    /// `CIndividualLinkEdge` pool (role link edges).
    edges: Arena<IndividualLinkEdge>,
    /// `CDistinctEdge` pool (differentFrom edges).
    distinct_edges: Arena<DistinctEdge>,
    /// `CNegationDisjointEdge` pool (negated-disjoint edges).
    disjoint_edges: Arena<DisjointEdge>,

    // --- the three descriptor kinds ---
    /// `CConceptDescriptor` pool.
    con_descs: Arena<ConceptDescriptor>,
    /// `CConceptProcessDescriptor` pool.
    con_proc_descs: Arena<ConceptProcessDescriptor>,
    /// clash-descriptor pool.
    clash_descs: Arena<ClashDescriptor>,

    // --- the dependency spine ---
    /// `CDependencyNode` pool (the tagged enum).
    dep_nodes: Arena<DependencyNode>,
    /// `CDependencyTrackPoint` pool.
    track_points: Arena<DependencyTrackPoint>,
    /// dependency-link pool.
    dep_links: Arena<DependencyLink>,
    /// `CBranchTreeNode` pool.
    branch_nodes: Arena<BranchTreeNode>,
    /// branching-instruction pool.
    branch_instrs: Arena<BranchingInstruction>,

    // --- the satellites ---
    /// `CReapplyConceptLabelSet` pool.
    // KONCLUDE-PORT-NOTE[cow]: the two HEAVY per-node satellites (concept
    // label set + concept processing queue) are Arc-wrapped — the per-node
    // COW localization of Konclude's task-fork shape. A branch-epoch journal
    // save is then an O(1) Arc clone; the deep copy happens only when an
    // alternative actually WRITES the shared object (`Arc::make_mut` in the
    // `label_set_mut`/`concept_proc_queue_mut` accessors — Konclude's
    // `getLocalizedIndividual` copy-on-first-write, one deep copy per
    // (object, alternative-that-mutates-it)). Untouched-but-journaled slots
    // never deep-copy; this is what makes own-epoch OR branch points
    // affordable (measured before: uniform journaling re-cloned the touched
    // set every backtrack cycle — 12653 classify 0.9s -> 260s).
    label_sets: Arena<std::sync::Arc<ReapplyConceptLabelSet>>,
    /// `CCoreConceptDescriptor` pool.
    core_con_descs: Arena<CoreConceptDescriptor>,
    /// `CReapplyRoleSuccessorHash` pool.
    // Arc-COW like `label_sets` (see the KONCLUDE-PORT-NOTE[cow] above): the
    // per-node role-successor hash is the third heavy journaled satellite.
    role_succ_hashes: Arena<std::sync::Arc<ReapplyRoleSuccessorHash>>,
    /// `CBranchingMergingProcessingRestrictionSpecification` pool.
    restriction_specs: Arena<BranchingMergingProcessingRestrictionSpecification>,
    /// `CBranchingMergingIndividualNodeCandidateLinker` pool.
    branching_merging_candidate_linkers: Arena<BranchingMergingIndividualNodeCandidateLinker>,
    /// `CIndividualNodeSaturationBlockingData` pool.
    indi_sat_block_datas: Arena<IndividualNodeSaturationBlockingData>,
    /// `CIndividualNodeSatisfiableExpandingCacheStoringData` pool.
    sat_exp_storing_datas: Arena<IndividualNodeSatisfiableExpandingCacheStoringData>,
    /// `CExtendedConceptReferenceLinkingData` / `CSaturationConceptDataItem` pool.
    extended_con_ref_linking_datas: Arena<ExtendedConceptReferenceLinkingData>,
    /// `CProcessAssertedDataLiteralLinker` pool.
    process_asserted_data_literal_linkers: Arena<ProcessAssertedDataLiteralLinker>,
    /// `CAdditionalProcessRoleAssertionsLinker` pool.
    additional_role_assertion_linkers: Arena<AdditionalProcessRoleAssertionsLinker>,
    /// `CAdditionalProcessDataAssertionsLinker` pool.
    additional_data_assertion_linkers: Arena<AdditionalProcessDataAssertionsLinker>,

    // --- W2.7 variable-binding-path satellites (varbind.rs) ---
    /// `CVariableBinding` pool.
    var_bindings: Arena<VariableBinding>,
    /// `CVariableBindingDescriptor` pool.
    var_binding_descs: Arena<VariableBindingDescriptor>,
    /// `CVariableBindingPath` pool.
    var_binding_paths: Arena<VariableBindingPath>,
    /// `CVariableBindingPathDescriptor` pool.
    var_binding_path_descs: Arena<VariableBindingPathDescriptor>,
    /// `CVariableBindingPathSet` pool.
    var_binding_path_sets: Arena<VariableBindingPathSet>,
    /// `CVariableBindingPathJoiningData` pool.
    var_binding_path_join_datas: Arena<VariableBindingPathJoiningData>,
    /// `CVariableBindingPathJoiningHash` pool.
    var_binding_path_join_hashes: Arena<VariableBindingPathJoiningHash>,
    /// `CVariableBindingPathMergingHash` pool.
    var_binding_path_merging_hashes: Arena<VariableBindingPathMergingHash>,
    /// `CVariableBindingTriggerLinker` pool.
    var_binding_trigger_linkers: Arena<VariableBindingTriggerLinker>,
    /// `CVariableBindingTriggerHash` pool.
    var_binding_trigger_hashes: Arena<VariableBindingTriggerHash>,
    /// `CConceptNominalSchemaGroundingData` pool.
    concept_nominal_schema_grounding_datas: Arena<ConceptNominalSchemaGroundingData>,
    /// `CConceptNominalSchemaGroundingHash` pool.
    concept_nominal_schema_grounding_hashes: Arena<ConceptNominalSchemaGroundingHash>,

    // --- W2.7 distinct / connection-successor / disjoint-role satellites (distinct.rs) ---
    /// `CDistinctHash` pool.
    // Arc-COW like `label_sets` (see the KONCLUDE-PORT-NOTE[cow] there).
    distinct_hashes: Arena<std::sync::Arc<DistinctHash>>,
    /// `CConnectionSuccessorSet` pool.
    conn_succ_sets: Arena<ConnectionSuccessorSet>,
    /// `CConnectionSuccessorCorrectionHash` pool.
    conn_succ_corr_hashes: Arena<ConnectionSuccessorCorrectionHash>,
    /// `CDisjointSuccessorRoleHash` pool.
    disjoint_succ_role_hashes: Arena<DisjointSuccessorRoleHash>,
    /// `CSuccessorConnectedNominalSet` pool.
    nominal_conn_sets: Arena<SuccessorConnectedNominalSet>,
    /// `CBlockingFollowSet` pool.
    blocking_follow_sets: Arena<BlockingFollowSet>,
    /// `CIndividualNodeAnalizedConceptExpansionData` pool.
    analized_con_exp_datas: Arena<IndividualNodeAnalizedConceptExpansionData>,
    /// `CAnalizedConceptExpansionLinker` pool.
    analized_con_exp_linkers: Arena<AnalizedConceptExpansionLinker>,
    /// `CSaturationIndividualNodeNominalHandlingData` pool.
    sat_nominal_handling_datas: Arena<SaturationIndividualNodeNominalHandlingData>,
    /// `CNominalCachingLossReactivationData` pool.
    nominal_caching_loss_reactivation_datas: Arena<NominalCachingLossReactivationData>,
    /// `CNominalCachingLossReactivationHash` pool.
    nominal_caching_loss_reactivation_hashes: Arena<NominalCachingLossReactivationHash>,
    /// `CSaturationSuccessorExtensionIndividualNodeProcessingQueue` pool.
    sat_succ_ext_ind_node_proc_queues:
        Arena<SaturationSuccessorExtensionIndividualNodeProcessingQueue>,
    /// `CCriticalIndividualNodeProcessingQueue` pool.
    sat_critical_ind_node_proc_queues: Arena<CriticalIndividualNodeProcessingQueue>,
    /// `CCriticalIndividualNodeConceptTestSet` pool.
    sat_critical_ind_node_con_test_sets: Arena<CriticalIndividualNodeConceptTestSet>,
    /// `CCriticalSaturationConceptQueue` pool.
    critical_sat_concept_queues: Arena<CriticalSaturationConceptQueue>,
    /// `CCriticalSaturationConceptTypeQueues` pool.
    critical_sat_concept_type_queues: Arena<CriticalSaturationConceptTypeQueues>,
    /// `CSaturationInfluencedNominalSet` pool.
    sat_influenced_nominal_sets: Arena<SaturationInfluencedNominalSet>,
    /// `CSaturationNominalDependentNodeHash` pool.
    sat_nominal_dependent_node_hashes: Arena<SaturationNominalDependentNodeHash>,
    /// `CSaturationNominalDependentNodeData` pool.
    sat_nominal_dependent_node_datas: Arena<SaturationNominalDependentNodeData>,
    /// `CSuccessorIndividualATMOSTReactivationData` pool.
    successor_individual_atmost_reactivation_datas:
        Arena<SuccessorIndividualATMOSTReactivationData>,
    /// `CDatatypesValueSpaceData` pool.
    datatypes_value_space_datas: Arena<DatatypesValueSpaceData>,

    // --- W2.7 reapply / signature-blocking / incremental-expansion satellites (reapply_sat.rs) ---
    /// `CSignatureBlockingCandidateHash` pool.
    sig_block_cand_hashes: Arena<SignatureBlockingCandidateHash>,
    /// `CIndividualNodeBlockingTestData` pool.
    blocking_test_datas: Arena<IndividualNodeBlockingTestData>,
    /// `CBlockingAlternativeSignatureBlockingCandidateData` pool.
    blocking_alt_datas: Arena<BlockingAlternativeSignatureBlockingCandidateData>,
    /// `CIndividualNodeIncrementalExpansionData` pool.
    inc_exp_datas: Arena<IndividualNodeIncrementalExpansionData>,
    /// `CCondensedReapplyConceptDescriptor` pool (the condensed reapply-queue chain).
    cond_reapply_con_descs: Arena<CondensedReapplyConceptDescriptor>,
    /// `CReapplyConceptDescriptor` pool (role reapply-queue chains).
    reapply_con_descs: Arena<ReapplyConceptDescriptor>,

    // --- W3b node-owned binding-set container hashes (binding_hash.rs) ---
    /// `CConceptVariableBindingPathSetHash` pool.
    con_var_bind_path_set_hashes: Arena<ConceptVariableBindingPathSetHash>,
    /// `CConceptPropagationBindingSetHash` pool.
    con_prop_binding_set_hashes: Arena<ConceptPropagationBindingSetHash>,

    // --- W3c propagation-binding subsystem pools (propagation_binding.rs) ---
    /// `CPropagationBinding` pool.
    prop_bindings: Arena<PropagationBinding>,
    /// `CPropagationBindingDescriptor` pool.
    prop_binding_descs: Arena<PropagationBindingDescriptor>,
    /// `CPropagationBindingReapplyConceptDescriptor` pool.
    prop_binding_reapply_con_descs: Arena<PropagationBindingReapplyConceptDescriptor>,
    /// `CPropagationBindingReapplyConceptHash` pool.
    prop_binding_reapply_con_hashes: Arena<PropagationBindingReapplyConceptHash>,
    /// `CPropagationBindingSet` pool.
    prop_binding_sets: Arena<PropagationBindingSet>,
    /// `CPropagationVariableBindingTransitionExtension` pool.
    prop_var_bind_trans_exts: Arena<PropagationVariableBindingTransitionExtension>,
    /// `CPropagationRepresentativeTransitionExtension` pool.
    prop_rep_trans_exts: Arena<PropagationRepresentativeTransitionExtension>,

    // --- W3.5r representative variable-binding-path-set subsystem pools (representative.rs) ---
    /// `CRepresentativeVariableBindingPathSetData` pool.
    rep_var_bind_path_set_datas: Arena<RepresentativeVariableBindingPathSetData>,
    /// `CRepresentativeVariableBindingPathSetMigrateData` pool.
    rep_var_bind_path_set_migrate_datas: Arena<RepresentativeVariableBindingPathSetMigrateData>,
    /// `CRepresentativeVariableBindingPathJoiningKeyData` pool.
    rep_var_bind_path_joining_key_datas: Arena<RepresentativeVariableBindingPathJoiningKeyData>,
    /// `CRepresentativeVariableBindingPathJoiningKeyHash` pool.
    rep_var_bind_path_joining_key_hashes: Arena<RepresentativeVariableBindingPathJoiningKeyHash>,
    /// `CRepresentativeVariableBindingPathSetHash` pool.
    rep_var_bind_path_set_hashes: Arena<RepresentativeVariableBindingPathSetHash>,
    /// `CRepresentativeVariableBindingPathHash` pool.
    rep_var_bind_path_hashes: Arena<RepresentativeVariableBindingPathHash>,
    /// `CRepresentativeVariableBindingPathSetJoiningData` pool.
    rep_var_bind_path_set_joining_datas: Arena<RepresentativeVariableBindingPathSetJoiningData>,
    /// `CRepresentativeVariableBindingPathSetJoiningHash` pool.
    rep_var_bind_path_set_joining_hashes: Arena<RepresentativeVariableBindingPathSetJoiningHash>,
    /// `CRepresentativeJoiningData` pool.
    rep_joining_datas: Arena<RepresentativeJoiningData>,
    /// `CRepresentativeJoiningHash` pool.
    rep_joining_hashes: Arena<RepresentativeJoiningHash>,
    /// `CRepresentativePropagationDescriptor` pool.
    rep_prop_descs: Arena<RepresentativePropagationDescriptor>,
    /// `CRepresentativePropagationSet` pool.
    rep_prop_sets: Arena<RepresentativePropagationSet>,
    /// `CConceptRepresentativePropagationSetHash` pool.
    con_rep_prop_set_hashes: Arena<ConceptRepresentativePropagationSetHash>,

    // --- backend-neighbour expansion controlling data (backend_control.rs) ---
    /// `CBackendNeighbourExpansionControllingData` pool.
    backend_neighbour_expansion_controlling_datas: Arena<BackendNeighbourExpansionControllingData>,
    /// `CIndividualNodeRepresentativeMemoryBackendCacheSynchronisationData` pool.
    backend_sync_datas: Arena<IndividualNodeBackendCacheSynchronisationData>,

    // --- W3.5b blocking-individual-node candidate + signature-blocking concept-expansion pools (blocking_hash.rs) ---
    /// `CBlockingIndividualNodeCandidateHash` pool.
    blocking_indi_node_cand_hashes: Arena<BlockingIndividualNodeCandidateHash>,
    /// `CBlockingIndividualNodeCandidateData` pool.
    blocking_indi_node_cand_datas: Arena<BlockingIndividualNodeCandidateData>,
    /// `CBlockingIndividualNodeLinkedCandidateHash` pool.
    blocking_indi_node_linked_cand_hashes: Arena<BlockingIndividualNodeLinkedCandidateHash>,
    /// `CBlockingIndividualNodeLinkedCandidateData` pool.
    blocking_indi_node_linked_cand_datas: Arena<BlockingIndividualNodeLinkedCandidateData>,
    /// `CBlockingIndividualNodeLinker` pool.
    blocking_indi_node_linkers: Arena<BlockingIndividualNodeLinker>,
    /// `CSignatureBlockingIndividualNodeConceptExpansionData` pool.
    sig_block_con_exp_datas: Arena<SignatureBlockingIndividualNodeConceptExpansionData>,
    /// `CReusingIndividualNodeConceptExpansionData` pool.
    reusing_con_exp_datas: Arena<ReusingIndividualNodeConceptExpansionData>,
    /// `CSignatureBlockingReviewSet` pool.
    signature_blocking_review_sets: Arena<SignatureBlockingReviewSet>,
    /// `CReusingReviewData` pool.
    reusing_review_datas: Arena<ReusingReviewData>,
    /// `CNodeSwitchHistory` pool.
    node_switch_histories: Arena<NodeSwitchHistory>,
    /// `CBranchingTree` pool.
    branching_trees: Arena<BranchingTree>,
    /// `CMarkerIndividualNodeHash` pool.
    marker_indi_node_hashes: Arena<MarkerIndividualNodeHash>,
    /// `CMarkerIndividualNodeData` pool.
    marker_indi_node_datas: Arena<MarkerIndividualNodeData>,
    /// `CIndividualNodeUnsatisfiableOccurenceCacheRetrievalData` pool.
    unsat_cache_ret_datas: Arena<IndividualNodeUnsatisfiableOccurenceCacheRetrievalData>,
    /// `CReferredIndividualTrackingVector` pool.
    referred_individual_tracking_vectors: Arena<ReferredIndividualTrackingVector>,
    /// `CConceptProcessLinker` pool.
    concept_process_linkers: Arena<ConceptProcessLinker>,
    /// `CIndividualProcessNodeLinker` pool.
    individual_process_node_linkers: Arena<IndividualProcessNodeLinker>,
    /// `CBackwardPropagationLink` pool.
    backward_prop_links: Arena<BackwardPropagationLink>,
    /// `CBackwardPropagationReapplyDescriptor` pool.
    backward_prop_reapply_descs: Arena<BackwardPropagationReapplyDescriptor>,
    /// `CRoleBackwardPropagationHash` pool.
    role_backward_prop_hashes: Arena<RoleBackwardPropagationHash>,

    // --- W4.5 saturation-layer per-test satellite pools (saturation::satellites.rs) ---
    /// `CConceptSaturationDescriptor` pool.
    con_sat_descs: Arena<ConceptSaturationDescriptor>,
    /// `CConceptSaturationProcessLinker` pool.
    con_sat_proc_linkers: Arena<ConceptSaturationProcessLinker>,
    /// `CRoleSaturationProcessLinker` pool.
    role_sat_proc_linkers: Arena<RoleSaturationProcessLinker>,
    /// `CBackwardSaturationPropagationLink` pool.
    backward_sat_prop_links: Arena<BackwardSaturationPropagationLink>,
    /// `CBackwardSaturationPropagationReapplyDescriptor` pool.
    backward_sat_prop_reapply_descs: Arena<BackwardSaturationPropagationReapplyDescriptor>,
    /// `CRoleBackwardSaturationPropagationHash` pool.
    role_backward_sat_prop_hashes: Arena<RoleBackwardSaturationPropagationHash>,
    /// `CSaturationSuccessorData` pool.
    sat_succ_datas: Arena<SaturationSuccessorData>,
    /// `CSaturationSuccessorExtensionData` pool.
    sat_succ_ext_datas: Arena<SaturationSuccessorExtensionData>,
    /// `CIndividualSaturationSuccessorLinkDataLinker` pool.
    indi_sat_succ_link_data_linkers: Arena<IndividualSaturationSuccessorLinkDataLinker>,
    /// `CLinkedRoleSaturationSuccessorData` pool.
    linked_role_sat_succ_datas: Arena<LinkedRoleSaturationSuccessorData>,
    /// `CLinkedRoleSaturationSuccessorHash` pool.
    linked_role_sat_succ_hashes: Arena<LinkedRoleSaturationSuccessorHash>,
    /// `CIndividualSaturationProcessNodeExtensionData` pool.
    indi_sat_node_ext_datas: Arena<IndividualSaturationProcessNodeExtensionData>,
    /// `CSaturationIndividualNodeSuccessorExtensionData` pool.
    sat_indi_node_succ_ext_datas: Arena<SaturationIndividualNodeSuccessorExtensionData>,
    /// `CSaturationIndividualNodeALLConceptsExtensionData` pool.
    sat_indi_node_all_concept_ext_datas: Arena<SaturationIndividualNodeAllConceptsExtensionData>,
    /// `CSaturationLinkedSuccessorIndividualALLConceptsExtensionData` pool.
    sat_linked_succ_indi_all_concept_ext_datas:
        Arena<SaturationLinkedSuccessorIndividualAllConceptsExtensionData>,
    /// `CSaturationSuccessorALLConceptExtensionData` pool.
    sat_successor_all_concept_ext_datas: Arena<SaturationSuccessorAllConceptExtensionData>,
    /// `CSaturationIndividualNodeExtensionResolveData` pool.
    sat_indi_node_ext_resolve_datas: Arena<SaturationIndividualNodeExtensionResolveData>,
    /// `CSaturationIndividualNodeExtensionResolveHash` pool.
    sat_indi_node_ext_resolve_hashes: Arena<SaturationIndividualNodeExtensionResolveHash>,
    /// Temporary `CPROCESSINGHASH<cint64,CConceptNegationPair>` pool.
    sat_concept_extension_maps: Arena<SaturationConceptExtensionMap>,
    /// `CSaturationSuccessorConceptExtensionMap` pool.
    sat_successor_concept_extension_maps: Arena<SaturationSuccessorConceptExtensionMap>,
    /// `CSaturationIndividualNodeFUNCTIONALConceptsExtensionData` pool.
    sat_indi_node_functional_concept_ext_datas:
        Arena<SaturationIndividualNodeFunctionalConceptsExtensionData>,
    /// `CSaturationSuccessorFUNCTIONALConceptExtensionData` pool.
    sat_successor_functional_concept_ext_datas:
        Arena<SaturationSuccessorFunctionalConceptExtensionData>,
    /// `CSaturationDisjunctCommonConceptExtractionData` pool.
    sat_disjunct_common_concept_extraction_datas:
        Arena<SaturationDisjunctCommonConceptExtractionData>,
    /// `CSaturationDisjunctExtractionLinker` pool.
    sat_disjunct_extraction_linkers: Arena<SaturationDisjunctExtractionLinker>,
    /// `CSaturationATMOSTSuccessorMergingData` pool.
    sat_atmost_successor_merging_datas: Arena<SaturationAtmostSuccessorMergingData>,
    /// `CSaturationATMOSTSuccessorMergingHash` pool.
    sat_atmost_successor_merging_hashes: Arena<SaturationAtmostSuccessorMergingHash>,
    /// `CLinkedDataValueAssertionSaturationData` pool.
    linked_data_value_assertion_datas: Arena<LinkedDataValueAssertionSaturationData>,
    /// `CXLinker<CRole*>` pool for linked data-value role assertions.
    data_value_role_assertion_linkers: Arena<DataValueRoleAssertionLinker>,
    /// `CSaturationIndividualNodeDatatypeData` pool.
    sat_indi_node_datatype_datas: Arena<SaturationIndividualNodeDatatypeData>,
    /// `CSaturationSuccessorRoleAssertionLinker` pool.
    sat_succ_role_assertion_linkers: Arena<SaturationSuccessorRoleAssertionLinker>,
    /// `CCriticalPredecessorRoleCardinalityData` pool.
    critical_pred_role_card_datas: Arena<CriticalPredecessorRoleCardinalityData>,
    /// `CCriticalPredecessorRoleCardinalityHash` pool.
    critical_pred_role_card_hashes: Arena<CriticalPredecessorRoleCardinalityHash>,
    /// `CReapplyConceptSaturationLabelSet` pool.
    reapply_con_sat_label_sets: Arena<ReapplyConceptSaturationLabelSet>,
    /// `CImplicationReapplyConceptSaturationDescriptor` pool.
    imp_reapply_con_sat_descs: Arena<ImplicationReapplyConceptSaturationDescriptor>,
    /// `CSaturationModifiedProcessUpdateLinker` pool.
    sat_modified_process_update_linkers: Arena<SaturationModifiedProcessUpdateLinker>,
    /// `CIndividualSaturationProcessNodeLinker` pool.
    indi_sat_process_node_linkers: Arena<IndividualSaturationProcessNodeLinker>,

    // --- u15 merge / nominal-expansion satellite pools ---
    /// `CIndividualMergingHash` pool (per-node merge hash).
    individual_merging_hashes: Arena<IndividualMergingHash>,
    /// `CSuccessorRoleHash` pool (per-node successor-role hash backend).
    // Arc-COW like `label_sets` (see the KONCLUDE-PORT-NOTE[cow] there).
    // (`disjoint_succ_role_hashes` stays plain: disjoint-role content is rare
    // and small, the journal clone is already cheap.)
    succ_role_hashes: Arena<std::sync::Arc<SuccessorRoleHash>>,

    // --- processing-queue subsystem pools (queues.rs) ---
    /// `CIndividualUnsortedProcessingQueue` pool.
    indi_unsorted_proc_queues: Arena<IndividualUnsortedProcessingQueue>,
    /// `CIndividualLinkerRotationProcessingQueue` pool.
    indi_rotation_proc_queues: Arena<IndividualLinkerRotationProcessingQueue>,
    /// `CIndividualDepthProcessingQueue` pool.
    indi_depth_proc_queues: Arena<IndividualDepthProcessingQueue>,
    /// `CIndividualProcessNodeDescriptor` pool.
    indi_proc_node_descs: Arena<IndividualProcessNodeDescriptor>,
    /// `CIndividualProcessingQueue` pool.
    indi_proc_queues: Arena<IndividualProcessingQueue>,
    /// `CIndividualCustomPriorityProcessingQueue` pool.
    indi_custom_priority_proc_queues: Arena<IndividualCustomPriorityProcessingQueue>,
    /// `CIndividualConceptBatchProcessingQueue` pool.
    indi_concept_batch_proc_queues: Arena<IndividualConceptBatchProcessingQueue>,
    /// `CIndividualReactivationProcessingQueue` pool.
    indi_reactivation_proc_queues: Arena<IndividualReactivationProcessingQueue>,
    /// `CConceptProcessingQueue` pool (per-node concept-descriptor queue).
    // Arc-COW like `label_sets` (see the KONCLUDE-PORT-NOTE[cow] there).
    concept_proc_queues: Arena<std::sync::Arc<ConceptProcessingQueue>>,

    // --- the opaque CProcessContext handles (filled when those subsystems land) ---
    /// `CProcessMemoryPoolAllocationManager* mUsedMemMan`.
    /// KONCLUDE-PORT-NOTE[memory-pool]: the pool is replaced by the typed arenas
    /// above; this stays opaque (`INVALID` == `nullptr`) until/if a real handle is
    /// needed.
    pub used_mem_man: Cint64,
    /// `CProcessTagger* mUsedProcessTagger`. Held BY VALUE now: the real tagger
    /// (the W3-DEFER opaque `Cint64` placeholder is superseded). The node-resolution
    /// keystone reads `get_current_localization_tag()` off it.
    pub used_process_tagger: ProcessTagger,
    /// `CProcessingStatisticGathering* mUsedProcessStatGath`. [api] opaque.
    pub used_process_stat_gath: Cint64,
}

impl ProcessContext {
    /// Port of `CProcessContext::CProcessContext` (+ the concrete base ctor):
    /// every arena empty, every handle `nullptr`.
    pub fn new() -> Self {
        ProcessContext {
            branch_epoch_depth: 0,
            nodes: Arena::new(),
            sat_nodes: Arena::new(),
            edges: Arena::new(),
            distinct_edges: Arena::new(),
            disjoint_edges: Arena::new(),
            con_descs: Arena::new(),
            con_proc_descs: Arena::new(),
            clash_descs: Arena::new(),
            dep_nodes: Arena::new(),
            track_points: Arena::new(),
            dep_links: Arena::new(),
            branch_nodes: Arena::new(),
            branch_instrs: Arena::new(),
            label_sets: Arena::new(),
            core_con_descs: Arena::new(),
            role_succ_hashes: Arena::new(),
            restriction_specs: Arena::new(),
            branching_merging_candidate_linkers: Arena::new(),
            indi_sat_block_datas: Arena::new(),
            sat_exp_storing_datas: Arena::new(),
            extended_con_ref_linking_datas: Arena::new(),
            process_asserted_data_literal_linkers: Arena::new(),
            additional_role_assertion_linkers: Arena::new(),
            additional_data_assertion_linkers: Arena::new(),
            var_bindings: Arena::new(),
            var_binding_descs: Arena::new(),
            var_binding_paths: Arena::new(),
            var_binding_path_descs: Arena::new(),
            var_binding_path_sets: Arena::new(),
            var_binding_path_join_datas: Arena::new(),
            var_binding_path_join_hashes: Arena::new(),
            var_binding_path_merging_hashes: Arena::new(),
            var_binding_trigger_linkers: Arena::new(),
            var_binding_trigger_hashes: Arena::new(),
            concept_nominal_schema_grounding_datas: Arena::new(),
            concept_nominal_schema_grounding_hashes: Arena::new(),
            distinct_hashes: Arena::new(),
            conn_succ_sets: Arena::new(),
            conn_succ_corr_hashes: Arena::new(),
            disjoint_succ_role_hashes: Arena::new(),
            nominal_conn_sets: Arena::new(),
            blocking_follow_sets: Arena::new(),
            analized_con_exp_datas: Arena::new(),
            analized_con_exp_linkers: Arena::new(),
            sat_nominal_handling_datas: Arena::new(),
            nominal_caching_loss_reactivation_datas: Arena::new(),
            nominal_caching_loss_reactivation_hashes: Arena::new(),
            sat_succ_ext_ind_node_proc_queues: Arena::new(),
            sat_critical_ind_node_proc_queues: Arena::new(),
            sat_critical_ind_node_con_test_sets: Arena::new(),
            critical_sat_concept_queues: Arena::new(),
            critical_sat_concept_type_queues: Arena::new(),
            sat_influenced_nominal_sets: Arena::new(),
            sat_nominal_dependent_node_hashes: Arena::new(),
            sat_nominal_dependent_node_datas: Arena::new(),
            successor_individual_atmost_reactivation_datas: Arena::new(),
            datatypes_value_space_datas: Arena::new(),
            sig_block_cand_hashes: Arena::new(),
            blocking_test_datas: Arena::new(),
            blocking_alt_datas: Arena::new(),
            inc_exp_datas: Arena::new(),
            cond_reapply_con_descs: Arena::new(),
            reapply_con_descs: Arena::new(),
            con_var_bind_path_set_hashes: Arena::new(),
            con_prop_binding_set_hashes: Arena::new(),
            prop_bindings: Arena::new(),
            prop_binding_descs: Arena::new(),
            prop_binding_reapply_con_descs: Arena::new(),
            prop_binding_reapply_con_hashes: Arena::new(),
            prop_binding_sets: Arena::new(),
            prop_var_bind_trans_exts: Arena::new(),
            prop_rep_trans_exts: Arena::new(),
            rep_var_bind_path_set_datas: Arena::new(),
            rep_var_bind_path_set_migrate_datas: Arena::new(),
            rep_var_bind_path_joining_key_datas: Arena::new(),
            rep_var_bind_path_joining_key_hashes: Arena::new(),
            rep_var_bind_path_set_hashes: Arena::new(),
            rep_var_bind_path_hashes: Arena::new(),
            rep_var_bind_path_set_joining_datas: Arena::new(),
            rep_var_bind_path_set_joining_hashes: Arena::new(),
            rep_joining_datas: Arena::new(),
            rep_joining_hashes: Arena::new(),
            rep_prop_descs: Arena::new(),
            rep_prop_sets: Arena::new(),
            con_rep_prop_set_hashes: Arena::new(),
            backend_neighbour_expansion_controlling_datas: Arena::new(),
            backend_sync_datas: Arena::new(),
            blocking_indi_node_cand_hashes: Arena::new(),
            blocking_indi_node_cand_datas: Arena::new(),
            blocking_indi_node_linked_cand_hashes: Arena::new(),
            blocking_indi_node_linked_cand_datas: Arena::new(),
            blocking_indi_node_linkers: Arena::new(),
            sig_block_con_exp_datas: Arena::new(),
            reusing_con_exp_datas: Arena::new(),
            signature_blocking_review_sets: Arena::new(),
            reusing_review_datas: Arena::new(),
            node_switch_histories: Arena::new(),
            branching_trees: Arena::new(),
            marker_indi_node_hashes: Arena::new(),
            marker_indi_node_datas: Arena::new(),
            unsat_cache_ret_datas: Arena::new(),
            referred_individual_tracking_vectors: Arena::new(),
            concept_process_linkers: Arena::new(),
            individual_process_node_linkers: Arena::new(),
            backward_prop_links: Arena::new(),
            backward_prop_reapply_descs: Arena::new(),
            role_backward_prop_hashes: Arena::new(),
            con_sat_descs: Arena::new(),
            con_sat_proc_linkers: Arena::new(),
            role_sat_proc_linkers: Arena::new(),
            backward_sat_prop_links: Arena::new(),
            backward_sat_prop_reapply_descs: Arena::new(),
            role_backward_sat_prop_hashes: Arena::new(),
            sat_succ_datas: Arena::new(),
            sat_succ_ext_datas: Arena::new(),
            indi_sat_succ_link_data_linkers: Arena::new(),
            linked_role_sat_succ_datas: Arena::new(),
            linked_role_sat_succ_hashes: Arena::new(),
            indi_sat_node_ext_datas: Arena::new(),
            sat_indi_node_succ_ext_datas: Arena::new(),
            sat_indi_node_all_concept_ext_datas: Arena::new(),
            sat_linked_succ_indi_all_concept_ext_datas: Arena::new(),
            sat_successor_all_concept_ext_datas: Arena::new(),
            sat_indi_node_ext_resolve_datas: Arena::new(),
            sat_indi_node_ext_resolve_hashes: Arena::new(),
            sat_concept_extension_maps: Arena::new(),
            sat_successor_concept_extension_maps: Arena::new(),
            sat_indi_node_functional_concept_ext_datas: Arena::new(),
            sat_successor_functional_concept_ext_datas: Arena::new(),
            sat_disjunct_common_concept_extraction_datas: Arena::new(),
            sat_disjunct_extraction_linkers: Arena::new(),
            sat_atmost_successor_merging_datas: Arena::new(),
            sat_atmost_successor_merging_hashes: Arena::new(),
            linked_data_value_assertion_datas: Arena::new(),
            data_value_role_assertion_linkers: Arena::new(),
            sat_indi_node_datatype_datas: Arena::new(),
            sat_succ_role_assertion_linkers: Arena::new(),
            critical_pred_role_card_datas: Arena::new(),
            critical_pred_role_card_hashes: Arena::new(),
            reapply_con_sat_label_sets: Arena::new(),
            imp_reapply_con_sat_descs: Arena::new(),
            sat_modified_process_update_linkers: Arena::new(),
            indi_sat_process_node_linkers: Arena::new(),
            individual_merging_hashes: Arena::new(),
            succ_role_hashes: Arena::new(),
            indi_unsorted_proc_queues: Arena::new(),
            indi_rotation_proc_queues: Arena::new(),
            indi_depth_proc_queues: Arena::new(),
            indi_proc_node_descs: Arena::new(),
            indi_proc_queues: Arena::new(),
            indi_custom_priority_proc_queues: Arena::new(),
            indi_concept_batch_proc_queues: Arena::new(),
            indi_reactivation_proc_queues: Arena::new(),
            concept_proc_queues: Arena::new(),
            used_mem_man: INVALID,
            used_process_tagger: ProcessTagger::new(),
            used_process_stat_gath: INVALID,
        }
    }

    /// Port of `CProcessContext::getUsedProcessTagger` — the owned per-test tagger.
    pub fn used_process_tagger(&self) -> &ProcessTagger {
        &self.used_process_tagger
    }
    /// Mutable access to the owned tagger (the tag-increment path).
    pub fn used_process_tagger_mut(&mut self) -> &mut ProcessTagger {
        &mut self.used_process_tagger
    }

    // --- processing-queue accessor trios ---
    arena_accessors!(
        indi_unsorted_proc_queues,
        IndividualUnsortedProcessingQueue,
        IndividualUnsortedProcessingQueueId,
        indi_unsorted_proc_queue,
        indi_unsorted_proc_queue_mut,
        alloc_indi_unsorted_proc_queue
    );
    arena_accessors!(
        indi_rotation_proc_queues,
        IndividualLinkerRotationProcessingQueue,
        IndividualLinkerRotationProcessingQueueId,
        indi_rotation_proc_queue,
        indi_rotation_proc_queue_mut,
        alloc_indi_rotation_proc_queue
    );
    arena_accessors!(
        indi_depth_proc_queues,
        IndividualDepthProcessingQueue,
        IndividualDepthProcessingQueueId,
        indi_depth_proc_queue,
        indi_depth_proc_queue_mut,
        alloc_indi_depth_proc_queue
    );
    arena_accessors!(
        indi_proc_node_descs,
        IndividualProcessNodeDescriptor,
        IndividualProcessNodeDescriptorId,
        indi_proc_node_desc,
        indi_proc_node_desc_mut,
        alloc_indi_proc_node_desc
    );
    arena_accessors!(
        indi_proc_queues,
        IndividualProcessingQueue,
        IndividualProcessingQueueId,
        indi_proc_queue,
        indi_proc_queue_mut,
        alloc_indi_proc_queue
    );
    arena_accessors!(
        indi_custom_priority_proc_queues,
        IndividualCustomPriorityProcessingQueue,
        IndividualCustomPriorityProcessingQueueId,
        indi_custom_priority_proc_queue,
        indi_custom_priority_proc_queue_mut,
        alloc_indi_custom_priority_proc_queue
    );
    arena_accessors!(
        indi_concept_batch_proc_queues,
        IndividualConceptBatchProcessingQueue,
        IndividualConceptBatchProcessingQueueId,
        indi_concept_batch_proc_queue,
        indi_concept_batch_proc_queue_mut,
        alloc_indi_concept_batch_proc_queue
    );
    arena_accessors!(
        indi_reactivation_proc_queues,
        IndividualReactivationProcessingQueue,
        IndividualReactivationProcessingQueueId,
        indi_reactivation_proc_queue,
        indi_reactivation_proc_queue_mut,
        alloc_indi_reactivation_proc_queue
    );
    // Hand-written Arc-COW accessors — see `label_set*` / the
    // KONCLUDE-PORT-NOTE[cow] on the `label_sets` field.
    /// Resolve an id to a shared borrow (the `obj->` read path). Raw-index
    /// rebuild: the id stays phantom-typed by the inner type (see `label_set`).
    #[inline]
    pub fn concept_proc_queue(&self, id: ConceptProcessingQueueId) -> &ConceptProcessingQueue {
        self.concept_proc_queues.get(Id::new(id.raw)).as_ref()
    }
    /// Resolve an id to a mutable borrow — copy-on-write when shared.
    #[inline]
    pub fn concept_proc_queue_mut(
        &mut self,
        id: ConceptProcessingQueueId,
    ) -> &mut ConceptProcessingQueue {
        std::sync::Arc::make_mut(self.concept_proc_queues.get_mut_journaled(Id::new(id.raw)))
    }
    /// Pool-allocate a new concept processing queue, returning its stable id.
    #[inline]
    pub fn alloc_concept_proc_queue(
        &mut self,
        v: ConceptProcessingQueue,
    ) -> ConceptProcessingQueueId {
        Id::new(self.concept_proc_queues.push(std::sync::Arc::new(v)).raw)
    }
    arena_accessors!(
        branching_merging_candidate_linkers,
        BranchingMergingIndividualNodeCandidateLinker,
        CandidateLinkerId,
        branching_merging_candidate_linker,
        branching_merging_candidate_linker_mut,
        alloc_branching_merging_candidate_linker
    );
    arena_accessors!(
        process_asserted_data_literal_linkers,
        ProcessAssertedDataLiteralLinker,
        ProcessAssertedDataLiteralLinkerId,
        process_asserted_data_literal_linker,
        process_asserted_data_literal_linker_mut,
        alloc_process_asserted_data_literal_linker
    );
    arena_accessors!(
        additional_role_assertion_linkers,
        AdditionalProcessRoleAssertionsLinker,
        AdditionalRoleAssertionsLinkerId,
        additional_role_assertion_linker,
        additional_role_assertion_linker_mut,
        alloc_additional_role_assertion_linker
    );
    arena_accessors!(
        additional_data_assertion_linkers,
        AdditionalProcessDataAssertionsLinker,
        AdditionalDataAssertionsLinkerId,
        additional_data_assertion_linker,
        additional_data_assertion_linker_mut,
        alloc_additional_data_assertion_linker
    );

    /// `CIndividualDepthProcessingQueue::takeNextProcessIndividual` — disjoint
    /// borrow of the depth-queue arena (mut) + the node arena (read).
    pub fn indi_depth_queue_take_next(&mut self, qid: IndividualDepthProcessingQueueId) -> NodeId {
        let ProcessContext {
            ref mut indi_depth_proc_queues,
            ref nodes,
            ..
        } = *self;
        indi_depth_proc_queues
            .get_mut_journaled(qid)
            .take_next_process_individual(nodes)
    }

    /// `CIndividualDepthProcessingQueue::insertProcessIndiviudal` — disjoint borrow.
    pub fn indi_depth_queue_insert(
        &mut self,
        qid: IndividualDepthProcessingQueueId,
        individual: NodeId,
    ) {
        let ProcessContext {
            ref mut indi_depth_proc_queues,
            ref nodes,
            ..
        } = *self;
        indi_depth_proc_queues
            .get_mut_journaled(qid)
            .insert_process_indiviudal(nodes, individual);
    }

    /// `CIndividualProcessingQueue::insertIndiviudalProcessDescriptor` — disjoint borrow.
    pub fn indi_processing_queue_insert_descriptor(
        &mut self,
        qid: IndividualProcessingQueueId,
        desc: IndividualProcessNodeDescriptorId,
    ) {
        let ProcessContext {
            ref mut indi_proc_queues,
            ref indi_proc_node_descs,
            ref nodes,
            ..
        } = *self;
        indi_proc_queues
            .get_mut_journaled(qid)
            .insert_indiviudal_process_descriptor(indi_proc_node_descs, nodes, desc);
    }

    /// `CIndividualProcessingQueue::takeNextProcessIndividualDescriptor`.
    pub fn indi_processing_queue_take_next_descriptor(
        &mut self,
        qid: IndividualProcessingQueueId,
    ) -> IndividualProcessNodeDescriptorId {
        let ProcessContext {
            ref mut indi_proc_queues,
            ref indi_proc_node_descs,
            ref nodes,
            ..
        } = *self;
        indi_proc_queues
            .get_mut_journaled(qid)
            .take_next_process_individual_descriptor(indi_proc_node_descs, nodes)
    }

    /// `CIndividualProcessingQueue::isIndividualQueued` — disjoint borrow.
    pub fn indi_processing_queue_is_individual_queued(
        &mut self,
        qid: IndividualProcessingQueueId,
        individual: NodeId,
    ) -> bool {
        let ProcessContext {
            ref mut indi_proc_queues,
            ref nodes,
            ..
        } = *self;
        indi_proc_queues
            .get_mut_journaled(qid)
            .is_individual_queued(nodes, individual)
    }

    /// `CIndividualCustomPriorityProcessingQueue::takeNextProcessIndividual`.
    pub fn indi_custom_priority_queue_take_next(
        &mut self,
        qid: IndividualCustomPriorityProcessingQueueId,
    ) -> NodeId {
        self.indi_custom_priority_proc_queue_mut(qid)
            .take_next_process_individual()
    }

    /// `CIndividualCustomPriorityProcessingQueue::insertIndiviudal`.
    pub fn indi_custom_priority_queue_insert(
        &mut self,
        qid: IndividualCustomPriorityProcessingQueueId,
        priority: f64,
        individual: NodeId,
    ) {
        self.indi_custom_priority_proc_queue_mut(qid)
            .insert_indiviudal(priority, individual);
    }

    /// `CIndividualReactivationProcessingQueue::insertReactivationIndiviudal` — disjoint borrow.
    pub fn indi_reactivation_queue_insert(
        &mut self,
        qid: IndividualReactivationProcessingQueueId,
        individual: NodeId,
        force_reactivation: bool,
    ) -> bool {
        let ProcessContext {
            ref mut indi_reactivation_proc_queues,
            ref nodes,
            ..
        } = *self;
        indi_reactivation_proc_queues
            .get_mut_journaled(qid)
            .insert_reactivation_indiviudal(nodes, individual, force_reactivation)
    }

    /// `CIndividualReactivationProcessingQueue::hasQueuedIndividual` — disjoint borrow.
    pub fn indi_reactivation_queue_has_queued_individual(
        &self,
        qid: IndividualReactivationProcessingQueueId,
        individual: NodeId,
    ) -> bool {
        let ProcessContext {
            ref indi_reactivation_proc_queues,
            ref nodes,
            ..
        } = *self;
        indi_reactivation_proc_queues
            .get(qid)
            .has_queued_individual(nodes, individual)
    }

    /// `CIndividualConceptBatchProcessingQueue::takeNextConceptProcessIndividual`.
    pub fn indi_concept_batch_queue_take_next(
        &mut self,
        qid: IndividualConceptBatchProcessingQueueId,
        onto: &super::super::model::ontology::OntologyArenas,
    ) -> Option<(super::super::model::ConceptId, NodeId, ConProcDescId)> {
        let ProcessContext {
            ref mut indi_concept_batch_proc_queues,
            ref nodes,
            ref con_proc_descs,
            ref con_descs,
            ..
        } = *self;
        indi_concept_batch_proc_queues
            .get_mut_journaled(qid)
            .take_next_concept_process_individual(nodes, con_proc_descs, con_descs, onto)
    }

    /// `CIndividualConceptBatchProcessingQueue::insertIndiviudalForConcept`.
    pub fn indi_concept_batch_queue_insert_indiviudal_for_concept(
        &mut self,
        qid: IndividualConceptBatchProcessingQueueId,
        onto: &super::super::model::ontology::OntologyArenas,
        concept: super::super::model::ConceptId,
        individual: NodeId,
        con_pro_des: ConProcDescId,
    ) {
        let ProcessContext {
            ref mut indi_concept_batch_proc_queues,
            ref nodes,
            ref con_proc_descs,
            ..
        } = *self;
        indi_concept_batch_proc_queues
            .get_mut_journaled(qid)
            .insert_indiviudal_for_concept(
                nodes,
                con_proc_descs,
                onto,
                concept,
                individual,
                con_pro_des,
            );
    }

    /// `CIndividualConceptBatchProcessingQueue::insertIndiviudalForBindingCount`.
    pub fn indi_concept_batch_queue_insert_indiviudal_for_binding_count(
        &mut self,
        qid: IndividualConceptBatchProcessingQueueId,
        onto: &super::super::model::ontology::OntologyArenas,
        concept: super::super::model::ConceptId,
        bind_count: Cint64,
        individual: NodeId,
        con_pro_des: ConProcDescId,
    ) {
        let ProcessContext {
            ref mut indi_concept_batch_proc_queues,
            ref nodes,
            ref con_proc_descs,
            ref con_descs,
            ..
        } = *self;
        indi_concept_batch_proc_queues
            .get_mut_journaled(qid)
            .insert_indiviudal_for_binding_count(
                nodes,
                con_proc_descs,
                con_descs,
                onto,
                concept,
                bind_count,
                individual,
                con_pro_des,
            );
    }

    /// Allocate a fresh `CIndividualUnsortedProcessingQueue` and run
    /// `initProcessingQueue(prev)` (the db3 `getXxx(create)` allocation site).
    pub fn alloc_unsorted_proc_queue_from_prev(
        &mut self,
        prev: IndividualUnsortedProcessingQueueId,
    ) -> IndividualUnsortedProcessingQueueId {
        let mut q = IndividualUnsortedProcessingQueue::new();
        if prev.is_some() {
            let prev_val = self.indi_unsorted_proc_queue(prev).clone();
            q.init_processing_queue(Some(&prev_val));
        } else {
            q.init_processing_queue(None);
        }
        self.alloc_indi_unsorted_proc_queue(q)
    }

    /// Allocate a fresh `CIndividualLinkerRotationProcessingQueue` + init from prev.
    pub fn alloc_rotation_proc_queue_from_prev(
        &mut self,
        prev: IndividualLinkerRotationProcessingQueueId,
    ) -> IndividualLinkerRotationProcessingQueueId {
        let mut q = IndividualLinkerRotationProcessingQueue::new();
        if prev.is_some() {
            let prev_val = self.indi_rotation_proc_queue(prev).clone();
            q.init_processing_queue(Some(&prev_val));
        } else {
            q.init_processing_queue(None);
        }
        self.alloc_indi_rotation_proc_queue(q)
    }

    /// Allocate a fresh `CIndividualDepthProcessingQueue` + init from prev.
    pub fn alloc_depth_proc_queue_from_prev(
        &mut self,
        prev: IndividualDepthProcessingQueueId,
    ) -> IndividualDepthProcessingQueueId {
        let mut q = IndividualDepthProcessingQueue::new();
        if prev.is_some() {
            let prev_val = self.indi_depth_proc_queue(prev).clone();
            q.init_processing_queue(Some(&prev_val));
        } else {
            q.init_processing_queue(None);
        }
        self.alloc_indi_depth_proc_queue(q)
    }

    /// Allocate a fresh `CIndividualProcessingQueue` + init from prev.
    pub fn alloc_individual_processing_queue_from_prev(
        &mut self,
        prev: IndividualProcessingQueueId,
    ) -> IndividualProcessingQueueId {
        let mut q = IndividualProcessingQueue::new();
        if prev.is_some() {
            let prev_val = self.indi_proc_queue(prev).clone();
            q.init_processing_queue(Some(&prev_val));
        } else {
            q.init_processing_queue(None);
        }
        self.alloc_indi_proc_queue(q)
    }

    /// Allocate a fresh `CIndividualCustomPriorityProcessingQueue` + init from prev.
    pub fn alloc_custom_priority_proc_queue_from_prev(
        &mut self,
        prev: IndividualCustomPriorityProcessingQueueId,
    ) -> IndividualCustomPriorityProcessingQueueId {
        let mut q = IndividualCustomPriorityProcessingQueue::new();
        if prev.is_some() {
            let prev_val = self.indi_custom_priority_proc_queue(prev).clone();
            q.init_processing_queue(Some(&prev_val));
        } else {
            q.init_processing_queue(None);
        }
        self.alloc_indi_custom_priority_proc_queue(q)
    }

    /// Allocate a fresh `CIndividualConceptBatchProcessingQueue` + init from prev.
    pub fn alloc_concept_batch_proc_queue_from_prev(
        &mut self,
        prev: IndividualConceptBatchProcessingQueueId,
    ) -> IndividualConceptBatchProcessingQueueId {
        let mut q = IndividualConceptBatchProcessingQueue::new();
        if prev.is_some() {
            let prev_val = self.indi_concept_batch_proc_queue(prev).clone();
            q.init_processing_queue(Some(&prev_val));
        } else {
            q.init_processing_queue(None);
        }
        self.alloc_indi_concept_batch_proc_queue(q)
    }

    /// Allocate a fresh `CIndividualReactivationProcessingQueue` + init from prev.
    pub fn alloc_reactivation_proc_queue_from_prev(
        &mut self,
        prev: IndividualReactivationProcessingQueueId,
    ) -> IndividualReactivationProcessingQueueId {
        let mut q = IndividualReactivationProcessingQueue::new();
        if prev.is_some() {
            let prev_val = self.indi_reactivation_proc_queue(prev).clone();
            q.init_processing_queue(Some(&prev_val));
        } else {
            q.init_processing_queue(None);
        }
        self.alloc_indi_reactivation_proc_queue(q)
    }

    /// Allocate a fresh `CSignatureBlockingReviewSet` + init from prev.
    pub fn alloc_signature_blocking_review_set_from_prev(
        &mut self,
        prev: SignatureBlockingReviewSetId,
    ) -> SignatureBlockingReviewSetId {
        let mut set = SignatureBlockingReviewSet::new();
        if prev.is_some() {
            let prev_val = self.signature_blocking_review_set(prev).clone();
            set.init_signature_blocking_review_set(Some(&prev_val));
        } else {
            set.init_signature_blocking_review_set(None);
        }
        self.alloc_signature_blocking_review_set(set)
    }

    /// Allocate a fresh `CReusingReviewData` + init from prev.
    pub fn alloc_reusing_review_data_from_prev(
        &mut self,
        prev: ReusingReviewDataId,
    ) -> ReusingReviewDataId {
        let mut data = ReusingReviewData::new();
        if prev.is_some() {
            let prev_val = self.reusing_review_data(prev).clone();
            data.init_review_data(Some(&prev_val));
        } else {
            data.init_review_data(None);
        }
        self.alloc_reusing_review_data(data)
    }

    /// Allocate a fresh `CNodeSwitchHistory` + init from prev.
    pub fn alloc_node_switch_history_from_prev(
        &mut self,
        prev: NodeSwitchHistoryId,
    ) -> NodeSwitchHistoryId {
        let mut history = NodeSwitchHistory::new(INVALID);
        if prev.is_some() {
            let prev_val = self.node_switch_history(prev).clone();
            history.init_switch_history(Some(&prev_val));
        } else {
            history.init_switch_history(None);
        }
        self.alloc_node_switch_history(history)
    }

    /// Allocate a fresh `CBranchingTree` + init from prev.
    pub fn alloc_branching_tree_from_prev(&mut self, prev: BranchingTreeId) -> BranchingTreeId {
        let mut tree = BranchingTree::new(INVALID);
        if prev.is_some() {
            let prev_val = self.branching_tree(prev).clone();
            tree.init_branching_tree(Some(&prev_val));
        } else {
            tree.init_branching_tree(None);
        }
        self.alloc_branching_tree(tree)
    }

    /// Allocate a fresh `CReusingIndividualNodeConceptExpansionData` + init from prev.
    pub fn alloc_reusing_con_exp_data_from_prev(
        &mut self,
        prev: ReusingIndividualNodeConceptExpansionDataId,
    ) -> ReusingIndividualNodeConceptExpansionDataId {
        let mut data = ReusingIndividualNodeConceptExpansionData::new();
        if prev.is_some() {
            let prev_val = self.reusing_con_exp_data(prev).clone();
            data.init_reusing_expansion_data(Some(&prev_val));
        } else {
            data.init_reusing_expansion_data(None);
        }
        self.alloc_reusing_con_exp_data(data)
    }

    /// Allocate a fresh `CBackendNeighbourExpansionControllingData` + init from prev.
    pub fn alloc_backend_neighbour_expansion_controlling_data_from_prev(
        &mut self,
        prev: BackendNeighbourExpansionControllingDataId,
    ) -> BackendNeighbourExpansionControllingDataId {
        let mut data = BackendNeighbourExpansionControllingData::new();
        if prev.is_some() {
            let prev_val = self
                .backend_neighbour_expansion_controlling_data(prev)
                .clone();
            data.init_expansion_controlling_data(Some(&prev_val));
        } else {
            data.init_expansion_controlling_data(None);
        }
        self.alloc_backend_neighbour_expansion_controlling_data(data)
    }

    /// Allocate a fresh `CIndividualNodeRepresentativeMemoryBackendCacheSynchronisationData`
    /// and initialize it from the previous snapshot.
    pub fn alloc_backend_sync_data_from_prev(
        &mut self,
        prev: BackendSyncDataId,
    ) -> BackendSyncDataId {
        let mut data = IndividualNodeBackendCacheSynchronisationData::new();
        if prev.is_some() {
            let prev_val = self.backend_sync_data(prev).clone();
            data.init_synchronisation_data(Some(&prev_val));
        } else {
            data.init_synchronisation_data(None);
        }
        self.alloc_backend_sync_data(data)
    }

    /// Port of `CIndividualProcessNode::getConceptProcessingQueue` (the lazy-alloc
    /// create path), lifted to the context because the allocation needs the
    /// `concept_proc_queues` arena that lives here (the W3b node-lazy-getter
    /// convention). Returns `mUseConceptProcessingQueue` (`Id::NONE` when absent and
    /// `create` is false).
    pub fn node_concept_processing_queue(
        &mut self,
        node: NodeId,
        create: bool,
    ) -> ConceptProcessingQueueId {
        if create && self.node(node).concept_processing_queue.is_none() {
            let prev = self.node(node).prev_concept_processing_queue;
            // initProcessingQueue(prev): deep-copy the parent's contents.
            let init_val = if prev.is_some() {
                let mut q = ConceptProcessingQueue::new();
                let prev_val = self.concept_proc_queue(prev).clone();
                q.init_processing_queue(Some(&prev_val));
                q
            } else {
                let mut q = ConceptProcessingQueue::new();
                q.init_processing_queue(None);
                q
            };
            let qid = self.alloc_concept_proc_queue(init_val);
            let n = self.node_mut(node);
            n.concept_processing_queue = qid;
            n.use_concept_processing_queue = qid;
        }
        self.node(node).use_concept_processing_queue
    }

    // --- the accessor trios (the C++ `obj->method()` deref replacement) ---
    arena_accessors!(
        nodes,
        IndividualProcessNode,
        NodeId,
        node,
        node_mut,
        alloc_node
    );
    /// Port-facing individual process-node arena size.
    #[inline]
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }
    arena_accessors!(
        sat_nodes,
        IndividualSaturationProcessNode,
        SatNodeId,
        sat_node,
        sat_node_mut,
        alloc_sat_node
    );
    /// Port-facing `CIndividualSaturationProcessNodeVector::getItemCount`.
    #[inline]
    pub fn sat_node_count(&self) -> usize {
        self.sat_nodes.len()
    }
    arena_accessors!(
        edges,
        IndividualLinkEdge,
        EdgeId,
        edge,
        edge_mut,
        alloc_edge
    );
    /// Whole-arena borrow of the individual-link edge pool for role-successor
    /// iterator snapshots.
    #[inline]
    pub fn edges(&self) -> &Arena<IndividualLinkEdge> {
        &self.edges
    }
    arena_accessors!(
        distinct_edges,
        DistinctEdge,
        DistinctEdgeId,
        distinct_edge,
        distinct_edge_mut,
        alloc_distinct_edge
    );
    /// Whole-arena borrow of the distinct-edge pool (the `CDistinctIterator`
    /// deref path threads `&Arena<DistinctEdge>`, mirroring rs1).
    #[inline]
    pub fn distinct_edges(&self) -> &Arena<DistinctEdge> {
        &self.distinct_edges
    }
    arena_accessors!(
        disjoint_edges,
        DisjointEdge,
        DisjointEdgeId,
        disjoint_edge,
        disjoint_edge_mut,
        alloc_disjoint_edge
    );
    arena_accessors!(
        con_descs,
        ConceptDescriptor,
        ConDescId,
        con_desc,
        con_desc_mut,
        alloc_con_desc
    );
    /// Port-facing concept descriptor arena size.
    #[inline]
    pub fn con_desc_count(&self) -> usize {
        self.con_descs.len()
    }
    arena_accessors!(
        con_proc_descs,
        ConceptProcessDescriptor,
        ConProcDescId,
        con_proc_desc,
        con_proc_desc_mut,
        alloc_con_proc_desc
    );
    arena_accessors!(
        concept_process_linkers,
        ConceptProcessLinker,
        ConceptProcessLinkerId,
        concept_process_linker,
        concept_process_linker_mut,
        alloc_concept_process_linker
    );
    arena_accessors!(
        individual_process_node_linkers,
        IndividualProcessNodeLinker,
        IndividualProcessNodeLinkerId,
        individual_process_node_linker,
        individual_process_node_linker_mut,
        alloc_individual_process_node_linker
    );

    /// Port of `CIndividualProcessNodeLinker::append(oldHead)` for arena ids.
    pub fn append_individual_process_node_linker_chain(
        &mut self,
        linker: IndividualProcessNodeLinkerId,
        appending_list: IndividualProcessNodeLinkerId,
    ) -> IndividualProcessNodeLinkerId {
        if linker.is_none() {
            return appending_list;
        }
        let mut last = linker;
        loop {
            let next = self.individual_process_node_linker(last).get_next();
            if next.is_none() {
                break;
            }
            last = next;
        }
        self.individual_process_node_linker_mut(last)
            .set_next(appending_list);
        linker
    }
    arena_accessors!(
        backward_prop_links,
        BackwardPropagationLink,
        BackwardPropagationLinkId,
        backward_prop_link,
        backward_prop_link_mut,
        alloc_backward_prop_link
    );
    arena_accessors!(
        backward_prop_reapply_descs,
        BackwardPropagationReapplyDescriptor,
        BackwardPropagationReapplyDescriptorId,
        backward_prop_reapply_desc,
        backward_prop_reapply_desc_mut,
        alloc_backward_prop_reapply_desc
    );
    arena_accessors!(
        role_backward_prop_hashes,
        RoleBackwardPropagationHash,
        RoleBackwardPropagationHashId,
        role_backward_prop_hash,
        role_backward_prop_hash_mut,
        alloc_role_backward_prop_hash
    );

    /// Port of `CBackwardPropagationLink::append(oldHead)` for arena ids.
    pub fn append_backward_propagation_link_chain(
        &mut self,
        head: BackwardPropagationLinkId,
        old_head: BackwardPropagationLinkId,
    ) -> BackwardPropagationLinkId {
        if head.is_none() {
            return old_head;
        }
        let mut tail = head;
        while self.backward_prop_link(tail).next.is_some() {
            tail = self.backward_prop_link(tail).next;
        }
        self.backward_prop_link_mut(tail).next = old_head;
        head
    }

    /// Port of `CBackwardPropagationReapplyDescriptor::append(oldHead)` for arena ids.
    pub fn append_backward_propagation_reapply_descriptor_chain(
        &mut self,
        head: BackwardPropagationReapplyDescriptorId,
        old_head: BackwardPropagationReapplyDescriptorId,
    ) -> BackwardPropagationReapplyDescriptorId {
        if head.is_none() {
            return old_head;
        }
        let mut tail = head;
        while self.backward_prop_reapply_desc(tail).next.is_some() {
            tail = self.backward_prop_reapply_desc(tail).next;
        }
        self.backward_prop_reapply_desc_mut(tail).next = old_head;
        head
    }

    /// Context-threaded port of `CIndividualProcessNode::getRoleBackwardPropagationHash`.
    pub fn node_role_backward_propagation_hash(
        &mut self,
        node: NodeId,
        create: bool,
    ) -> RoleBackwardPropagationHashId {
        if node.is_none() {
            return RoleBackwardPropagationHashId::NONE;
        }
        if self.node(node).role_back_prop_hash.is_none() && create {
            let hash =
                self.alloc_role_backward_prop_hash(RoleBackwardPropagationHash::new(INVALID));
            self.node_mut(node).role_back_prop_hash = hash;
        }
        self.node(node).role_back_prop_hash
    }

    /// Context-threaded port of `CRoleBackwardPropagationHash::addBackwardPropagationLink`.
    pub fn role_backward_prop_hash_add_backward_propagation_link(
        &mut self,
        hash: RoleBackwardPropagationHashId,
        role: RoleId,
        link: BackwardPropagationLinkId,
    ) -> BackwardPropagationReapplyDescriptorId {
        if hash.is_none() || link.is_none() {
            return BackwardPropagationReapplyDescriptorId::NONE;
        }
        let (old_head, reapply_linker) = {
            let data = self
                .role_backward_prop_hash(hash)
                .role_back_prop_data_hash
                .get(&role);
            let old_head = data
                .map(|data| data.link_linker)
                .unwrap_or(BackwardPropagationLinkId::NONE);
            let reapply_linker = data
                .map(|data| data.reapply_linker)
                .unwrap_or(BackwardPropagationReapplyDescriptorId::NONE);
            (old_head, reapply_linker)
        };

        if old_head.is_some()
            && self.backward_prop_link(old_head).get_source_individual()
                == self.backward_prop_link(link).get_source_individual()
        {
            return BackwardPropagationReapplyDescriptorId::NONE;
        }

        let new_head = self.append_backward_propagation_link_chain(link, old_head);
        self.role_backward_prop_hash_mut(hash)
            .role_back_prop_data_hash
            .entry(role)
            .or_insert_with(RoleBackwardPropagationHashData::new)
            .link_linker = new_head;
        reapply_linker
    }

    /// Context-threaded port of
    /// `CRoleBackwardPropagationHash::addBackwardPropagationConceptDescriptor`.
    pub fn role_backward_prop_hash_add_backward_propagation_concept_descriptor(
        &mut self,
        hash: RoleBackwardPropagationHashId,
        role: RoleId,
        reapply_con_des: BackwardPropagationReapplyDescriptorId,
    ) -> BackwardPropagationLinkId {
        if hash.is_none() || reapply_con_des.is_none() {
            return BackwardPropagationLinkId::NONE;
        }
        let (old_head, link_linker) = {
            let data = self
                .role_backward_prop_hash(hash)
                .role_back_prop_data_hash
                .get(&role);
            let old_head = data
                .map(|data| data.reapply_linker)
                .unwrap_or(BackwardPropagationReapplyDescriptorId::NONE);
            let link_linker = data
                .map(|data| data.link_linker)
                .unwrap_or(BackwardPropagationLinkId::NONE);
            (old_head, link_linker)
        };
        let new_head =
            self.append_backward_propagation_reapply_descriptor_chain(reapply_con_des, old_head);
        self.role_backward_prop_hash_mut(hash)
            .role_back_prop_data_hash
            .entry(role)
            .or_insert_with(RoleBackwardPropagationHashData::new)
            .reapply_linker = new_head;
        link_linker
    }
    arena_accessors!(
        clash_descs,
        ClashDescriptor,
        ClashDescId,
        clash_desc,
        clash_desc_mut,
        alloc_clash_desc
    );

    /// Port of `CClashedDependencyDescriptor::append(oldHead)` for arena ids.
    pub fn append_clash_descriptor_chain(
        &mut self,
        head: ClashDescId,
        old_head: ClashDescId,
    ) -> ClashDescId {
        if head.is_none() {
            return old_head;
        }
        let mut tail = head;
        while self.clash_desc(tail).next.is_some() {
            tail = self.clash_desc(tail).next;
        }
        self.clash_desc_mut(tail).next = old_head;
        head
    }
    arena_accessors!(
        dep_nodes,
        DependencyNode,
        DependencyId,
        dep_node,
        dep_node_mut,
        alloc_dep_node
    );
    arena_accessors!(
        track_points,
        DependencyTrackPoint,
        TrackPointId,
        track_point,
        track_point_mut,
        alloc_track_point
    );
    arena_accessors!(
        dep_links,
        DependencyLink,
        DepLinkId,
        dep_link,
        dep_link_mut,
        alloc_dep_link
    );
    arena_accessors!(
        branch_nodes,
        BranchTreeNode,
        BranchNodeId,
        branch_node,
        branch_node_mut,
        alloc_branch_node
    );
    /// Port-owned helper for `CBranchingTree::getBranchTreeNode` child creation.
    pub fn alloc_branch_child_node(
        &mut self,
        parent_branch_tree_node: BranchNodeId,
        sat_calc_task: Cint64,
    ) -> BranchNodeId {
        let branch_node = self.alloc_branch_node(BranchTreeNode::new());
        if parent_branch_tree_node.is_some() {
            BranchTreeNode::init_branching_child_node(
                &mut self.branch_nodes,
                branch_node,
                parent_branch_tree_node,
                sat_calc_task,
            );
        } else {
            self.branch_node_mut(branch_node)
                .init_branching_root_node(branch_node, sat_calc_task);
        }
        branch_node
    }
    /// Port-owned helper for
    /// `CNonDeterministicDependencyNode::getDependencyTrackPointBranch`.
    pub fn dependency_track_point_branch(&mut self, dependency_node: DependencyId) -> TrackPointId {
        self.dep_nodes
            .get_mut_journaled(dependency_node)
            .get_dependency_track_point_branch(dependency_node, &mut self.track_points)
    }

    /// Port-owned helper for `CDeterministicDependencyNode::updateBranchingTag`.
    pub fn update_dependency_branching_tag(&mut self, dependency_node: DependencyId) -> bool {
        self.dep_nodes
            .get_mut_journaled(dependency_node)
            .update_branching_tag(&self.track_points, &self.dep_links)
    }

    /// Port-owned helper for `CNonDeterministicDependencyNode::updateBranchingTags`.
    pub fn update_dependency_branching_tags(&mut self, dependency_node: DependencyId) -> bool {
        self.dep_nodes
            .get_mut_journaled(dependency_node)
            .update_branching_tags(&mut self.track_points, &self.dep_links)
    }
    arena_accessors!(
        branch_instrs,
        BranchingInstruction,
        BranchInstrId,
        branch_instr,
        branch_instr_mut,
        alloc_branch_instr
    );
    // Hand-written Arc-COW accessors (see the KONCLUDE-PORT-NOTE[cow] on the
    // field): same signatures the macro would generate, so no call-site
    // changes — the read path derefs the Arc, the mutate path journals the
    // O(1) Arc clone and deep-copies only when the slot is shared.
    /// Resolve an id to a shared borrow (the `obj->` read path).
    /// (`LabelSetId` stays phantom-typed by the INNER type; the Arc wrapper is
    /// an arena-internal representation detail, hence the raw-index rebuild.)
    #[inline]
    pub fn label_set(&self, id: LabelSetId) -> &ReapplyConceptLabelSet {
        self.label_sets.get(Id::new(id.raw)).as_ref()
    }
    /// Resolve an id to a mutable borrow — copy-on-write when shared.
    #[inline]
    pub fn label_set_mut(&mut self, id: LabelSetId) -> &mut ReapplyConceptLabelSet {
        std::sync::Arc::make_mut(self.label_sets.get_mut_journaled(Id::new(id.raw)))
    }
    /// Pool-allocate a new label set, returning its stable id.
    #[inline]
    pub fn alloc_label_set(&mut self, v: ReapplyConceptLabelSet) -> LabelSetId {
        Id::new(self.label_sets.push(std::sync::Arc::new(v)).raw)
    }
    arena_accessors!(
        core_con_descs,
        CoreConceptDescriptor,
        CoreConceptDescriptorId,
        core_con_desc,
        core_con_desc_mut,
        alloc_core_con_desc
    );
    /// Port-facing concept label-set arena size.
    #[inline]
    pub fn label_set_count(&self) -> usize {
        self.label_sets.len()
    }

    /// Context-threaded port of
    /// `CCoreConceptDescriptor::initCoreConceptDescriptor` +
    /// `CReapplyConceptLabelSet::addCoreConceptDescriptor`.
    pub fn label_set_add_core_concept_descriptor(
        &mut self,
        label_set: LabelSetId,
        concept_descriptor: ConDescId,
    ) -> CoreConceptDescriptorId {
        let mut core_con_des = CoreConceptDescriptor::new();
        core_con_des.init_core_concept_descriptor(concept_descriptor);
        let core_con_des = self.alloc_core_con_desc(core_con_des);
        let old_head = self
            .label_set(label_set)
            .get_core_concept_descriptor_linker();
        self.core_con_desc_mut(core_con_des).append(old_head);
        self.label_set_mut(label_set)
            .add_core_concept_descriptor(core_con_des);
        core_con_des
    }
    // Hand-written Arc-COW accessors (see the KONCLUDE-PORT-NOTE[cow] on the
    // `label_sets` field): same signatures the macro generated, raw-index id
    // rebuild at the Arc boundary.
    /// Resolve an id to a shared borrow (the `obj->` read path).
    #[inline]
    pub fn role_succ_hash(&self, id: RoleSuccHashId) -> &ReapplyRoleSuccessorHash {
        self.role_succ_hashes.get(Id::new(id.raw)).as_ref()
    }
    /// Resolve an id to a mutable borrow — copy-on-write when shared.
    #[inline]
    pub fn role_succ_hash_mut(&mut self, id: RoleSuccHashId) -> &mut ReapplyRoleSuccessorHash {
        std::sync::Arc::make_mut(self.role_succ_hashes.get_mut_journaled(Id::new(id.raw)))
    }
    /// Pool-allocate a new role-successor hash, returning its stable id.
    #[inline]
    pub fn alloc_role_succ_hash(&mut self, v: ReapplyRoleSuccessorHash) -> RoleSuccHashId {
        Id::new(self.role_succ_hashes.push(std::sync::Arc::new(v)).raw)
    }
    arena_accessors!(
        restriction_specs,
        BranchingMergingProcessingRestrictionSpecification,
        RestrictionSpecId,
        restriction_spec,
        restriction_spec_mut,
        alloc_restriction_spec
    );
    arena_accessors!(
        indi_sat_block_datas,
        IndividualNodeSaturationBlockingData,
        IndiSatBlockDataId,
        indi_sat_block_data,
        indi_sat_block_data_mut,
        alloc_indi_sat_block_data
    );
    arena_accessors!(
        sat_exp_storing_datas,
        IndividualNodeSatisfiableExpandingCacheStoringData,
        IndividualNodeSatisfiableExpandingCacheStoringDataId,
        sat_exp_storing_data,
        sat_exp_storing_data_mut,
        alloc_sat_exp_storing_data
    );
    arena_accessors!(
        extended_con_ref_linking_datas,
        ExtendedConceptReferenceLinkingData,
        super::stubs::ExtendedConceptReferenceLinkingDataId,
        extended_con_ref_linking_data,
        extended_con_ref_linking_data_mut,
        alloc_extended_con_ref_linking_data
    );
    /// Port-facing saturation concept-reference arena size.
    #[inline]
    pub fn extended_con_ref_linking_data_count(&self) -> usize {
        self.extended_con_ref_linking_datas.len()
    }

    // --- W2.7 variable-binding-path satellite trios ---
    arena_accessors!(
        var_bindings,
        VariableBinding,
        VarBindingId,
        var_binding,
        var_binding_mut,
        alloc_var_binding
    );
    arena_accessors!(
        var_binding_descs,
        VariableBindingDescriptor,
        VarBindingDescriptorId,
        var_binding_des,
        var_binding_des_mut,
        alloc_var_binding_des
    );
    arena_accessors!(
        var_binding_paths,
        VariableBindingPath,
        VarBindingPathId,
        vbpath,
        vbpath_mut,
        alloc_vbpath
    );
    arena_accessors!(
        var_binding_path_descs,
        VariableBindingPathDescriptor,
        VarBindingPathDescriptorId,
        vbpath_des,
        vbpath_des_mut,
        alloc_vbpath_des
    );
    arena_accessors!(
        var_binding_path_sets,
        VariableBindingPathSet,
        VarBindingPathSetId,
        vbpath_set,
        vbpath_set_mut,
        alloc_vbpath_set
    );
    arena_accessors!(
        var_binding_path_join_datas,
        VariableBindingPathJoiningData,
        VarBindingPathJoiningDataId,
        vbpath_join_data,
        vbpath_join_data_mut,
        alloc_vbpath_join_data
    );
    arena_accessors!(
        var_binding_path_join_hashes,
        VariableBindingPathJoiningHash,
        VariableBindingPathJoiningHashId,
        vbpath_join_hash,
        vbpath_join_hash_mut,
        alloc_vbpath_join_hash
    );
    arena_accessors!(
        var_binding_path_merging_hashes,
        VariableBindingPathMergingHash,
        VariableBindingPathMergingHashId,
        vbpath_merging_hash,
        vbpath_merging_hash_mut,
        alloc_vbpath_merging_hash
    );
    arena_accessors!(
        var_binding_trigger_linkers,
        VariableBindingTriggerLinker,
        VarBindingTriggerLinkerId,
        vbtrigger_linker,
        vbtrigger_linker_mut,
        alloc_vbtrigger_linker
    );
    arena_accessors!(
        var_binding_trigger_hashes,
        VariableBindingTriggerHash,
        VariableBindingTriggerHashId,
        vbtrigger_hash,
        vbtrigger_hash_mut,
        alloc_vbtrigger_hash
    );
    arena_accessors!(
        concept_nominal_schema_grounding_datas,
        ConceptNominalSchemaGroundingData,
        ConceptNominalSchemaGroundingDataId,
        grounding_data,
        grounding_data_mut,
        alloc_grounding_data
    );
    arena_accessors!(
        concept_nominal_schema_grounding_hashes,
        ConceptNominalSchemaGroundingHash,
        ConceptNominalSchemaGroundingHashId,
        grounding_hash,
        grounding_hash_mut,
        alloc_grounding_hash
    );

    // --- W2.7 distinct / connection-successor / disjoint-role satellite trios ---
    // Hand-written Arc-COW accessors (see the KONCLUDE-PORT-NOTE[cow] on the
    // `label_sets` field).
    /// Resolve an id to a shared borrow (the `obj->` read path).
    #[inline]
    pub fn distinct_hash(&self, id: DistinctHashId) -> &DistinctHash {
        self.distinct_hashes.get(Id::new(id.raw)).as_ref()
    }
    /// Resolve an id to a mutable borrow — copy-on-write when shared.
    #[inline]
    pub fn distinct_hash_mut(&mut self, id: DistinctHashId) -> &mut DistinctHash {
        std::sync::Arc::make_mut(self.distinct_hashes.get_mut_journaled(Id::new(id.raw)))
    }
    /// Pool-allocate a new distinct hash, returning its stable id.
    #[inline]
    pub fn alloc_distinct_hash(&mut self, v: DistinctHash) -> DistinctHashId {
        Id::new(self.distinct_hashes.push(std::sync::Arc::new(v)).raw)
    }
    arena_accessors!(
        conn_succ_sets,
        ConnectionSuccessorSet,
        ConnectionSuccessorSetId,
        conn_succ_set,
        conn_succ_set_mut,
        alloc_conn_succ_set
    );
    arena_accessors!(
        conn_succ_corr_hashes,
        ConnectionSuccessorCorrectionHash,
        ConnectionSuccessorCorrectionHashId,
        conn_succ_corr_hash,
        conn_succ_corr_hash_mut,
        alloc_conn_succ_corr_hash
    );
    arena_accessors!(
        disjoint_succ_role_hashes,
        DisjointSuccessorRoleHash,
        DisjointSuccessorRoleHashId,
        disjoint_succ_role_hash,
        disjoint_succ_role_hash_mut,
        alloc_disjoint_succ_role_hash
    );
    arena_accessors!(
        nominal_conn_sets,
        SuccessorConnectedNominalSet,
        SuccessorConnectedNominalSetId,
        nominal_conn_set,
        nominal_conn_set_mut,
        alloc_nominal_conn_set
    );
    arena_accessors!(
        blocking_follow_sets,
        BlockingFollowSet,
        BlockingFollowSetId,
        blocking_follow_set,
        blocking_follow_set_mut,
        alloc_blocking_follow_set
    );
    arena_accessors!(
        analized_con_exp_datas,
        IndividualNodeAnalizedConceptExpansionData,
        IndividualNodeAnalizedConceptExpansionDataId,
        analized_con_exp_data,
        analized_con_exp_data_mut,
        alloc_analized_con_exp_data
    );
    arena_accessors!(
        analized_con_exp_linkers,
        AnalizedConceptExpansionLinker,
        AnalizedConceptExpansionLinkerId,
        analized_con_exp_linker,
        analized_con_exp_linker_mut,
        alloc_analized_con_exp_linker
    );

    /// Port-facing helper for `CLinkerBase::getCount` on a
    /// `CAnalizedConceptExpansionLinker` chain.
    pub fn analized_con_exp_linker_count(
        &self,
        mut linker: AnalizedConceptExpansionLinkerId,
    ) -> Cint64 {
        let mut count = 0;
        while linker.is_some() {
            count += 1;
            linker = self.analized_con_exp_linker(linker).get_next();
        }
        count
    }

    /// Port-facing helper for `CLinkerBase::append` on
    /// `CAnalizedConceptExpansionLinker`.
    pub fn analized_con_exp_linker_append(
        &mut self,
        linker: AnalizedConceptExpansionLinkerId,
        appending_list: AnalizedConceptExpansionLinkerId,
    ) -> AnalizedConceptExpansionLinkerId {
        if linker.is_none() {
            return appending_list;
        }
        let mut last = linker;
        loop {
            let next = self.analized_con_exp_linker(last).get_next();
            if next.is_none() {
                self.analized_con_exp_linker_mut(last)
                    .set_next(appending_list);
                return linker;
            }
            last = next;
        }
    }
    arena_accessors!(
        sat_nominal_handling_datas,
        SaturationIndividualNodeNominalHandlingData,
        SaturationIndividualNodeNominalHandlingDataId,
        sat_nominal_handling_data,
        sat_nominal_handling_data_mut,
        alloc_sat_nominal_handling_data
    );
    arena_accessors!(
        nominal_caching_loss_reactivation_datas,
        NominalCachingLossReactivationData,
        NominalCachingLossReactivationDataId,
        nominal_caching_loss_reactivation_data,
        nominal_caching_loss_reactivation_data_mut,
        alloc_nominal_caching_loss_reactivation_data
    );
    arena_accessors!(
        nominal_caching_loss_reactivation_hashes,
        NominalCachingLossReactivationHash,
        NominalCachingLossReactivationHashId,
        nominal_caching_loss_reactivation_hash,
        nominal_caching_loss_reactivation_hash_mut,
        alloc_nominal_caching_loss_reactivation_hash
    );
    arena_accessors!(
        sat_succ_ext_ind_node_proc_queues,
        SaturationSuccessorExtensionIndividualNodeProcessingQueue,
        SaturationSuccessorExtensionIndividualNodeProcessingQueueId,
        sat_succ_ext_ind_node_proc_queue,
        sat_succ_ext_ind_node_proc_queue_mut,
        alloc_sat_succ_ext_ind_node_proc_queue
    );
    arena_accessors!(
        sat_critical_ind_node_proc_queues,
        CriticalIndividualNodeProcessingQueue,
        CriticalIndividualNodeProcessingQueueId,
        sat_critical_ind_node_proc_queue,
        sat_critical_ind_node_proc_queue_mut,
        alloc_sat_critical_ind_node_proc_queue
    );
    arena_accessors!(
        sat_critical_ind_node_con_test_sets,
        CriticalIndividualNodeConceptTestSet,
        CriticalIndividualNodeConceptTestSetId,
        sat_critical_ind_node_con_test_set,
        sat_critical_ind_node_con_test_set_mut,
        alloc_sat_critical_ind_node_con_test_set
    );
    arena_accessors!(
        critical_sat_concept_queues,
        CriticalSaturationConceptQueue,
        CriticalSaturationConceptQueueId,
        critical_sat_concept_queue,
        critical_sat_concept_queue_mut,
        alloc_critical_sat_concept_queue
    );
    arena_accessors!(
        critical_sat_concept_type_queues,
        CriticalSaturationConceptTypeQueues,
        CriticalSaturationConceptTypeQueuesId,
        critical_sat_concept_type_queues,
        critical_sat_concept_type_queues_mut,
        alloc_critical_sat_concept_type_queues
    );
    arena_accessors!(
        sat_influenced_nominal_sets,
        SaturationInfluencedNominalSet,
        SaturationInfluencedNominalSetId,
        sat_influenced_nominal_set,
        sat_influenced_nominal_set_mut,
        alloc_sat_influenced_nominal_set
    );
    arena_accessors!(
        sat_nominal_dependent_node_hashes,
        SaturationNominalDependentNodeHash,
        SaturationNominalDependentNodeHashId,
        sat_nominal_dependent_node_hash,
        sat_nominal_dependent_node_hash_mut,
        alloc_sat_nominal_dependent_node_hash
    );
    arena_accessors!(
        sat_nominal_dependent_node_datas,
        SaturationNominalDependentNodeData,
        SaturationNominalDependentNodeDataId,
        sat_nominal_dependent_node_data,
        sat_nominal_dependent_node_data_mut,
        alloc_sat_nominal_dependent_node_data
    );
    arena_accessors!(
        successor_individual_atmost_reactivation_datas,
        SuccessorIndividualATMOSTReactivationData,
        ATMOSTReactivationDataId,
        successor_individual_atmost_reactivation_data,
        successor_individual_atmost_reactivation_data_mut,
        alloc_successor_individual_atmost_reactivation_data
    );
    arena_accessors!(
        datatypes_value_space_datas,
        DatatypesValueSpaceData,
        DatatypesValueSpaceDataId,
        datatypes_value_space_data,
        datatypes_value_space_data_mut,
        alloc_datatypes_value_space_data
    );

    // --- W2.7 reapply / signature-blocking / incremental-expansion satellite trios ---
    arena_accessors!(
        sig_block_cand_hashes,
        SignatureBlockingCandidateHash,
        SigBlockCandHashId,
        sig_block_cand_hash,
        sig_block_cand_hash_mut,
        alloc_sig_block_cand_hash
    );
    arena_accessors!(
        blocking_test_datas,
        IndividualNodeBlockingTestData,
        BlockingTestDataId,
        blocking_test_data,
        blocking_test_data_mut,
        alloc_blocking_test_data
    );
    arena_accessors!(
        blocking_alt_datas,
        BlockingAlternativeSignatureBlockingCandidateData,
        BlockingAltDataId,
        blocking_alt_data,
        blocking_alt_data_mut,
        alloc_blocking_alt_data
    );
    arena_accessors!(
        inc_exp_datas,
        IndividualNodeIncrementalExpansionData,
        IncrementalExpansionDataId,
        inc_exp_data,
        inc_exp_data_mut,
        alloc_inc_exp_data
    );
    arena_accessors!(
        cond_reapply_con_descs,
        CondensedReapplyConceptDescriptor,
        CondensedReapplyConceptDescriptorId,
        cond_reapply_con_desc,
        cond_reapply_con_desc_mut,
        alloc_cond_reapply_con_desc
    );
    arena_accessors!(
        reapply_con_descs,
        ReapplyConceptDescriptor,
        ReapplyConceptDescriptorId,
        reapply_con_desc,
        reapply_con_desc_mut,
        alloc_reapply_con_desc
    );

    // --- W3b node-owned binding-set container hash trios ---
    arena_accessors!(
        con_var_bind_path_set_hashes,
        ConceptVariableBindingPathSetHash,
        ConceptVariableBindingPathSetHashId,
        con_var_bind_path_set_hash,
        con_var_bind_path_set_hash_mut,
        alloc_con_var_bind_path_set_hash
    );
    arena_accessors!(
        con_prop_binding_set_hashes,
        ConceptPropagationBindingSetHash,
        ConceptPropagationBindingSetHashId,
        con_prop_binding_set_hash,
        con_prop_binding_set_hash_mut,
        alloc_con_prop_binding_set_hash
    );

    // --- W3c propagation-binding subsystem trios ---
    arena_accessors!(
        prop_bindings,
        PropagationBinding,
        PropagationBindingId,
        prop_binding,
        prop_binding_mut,
        alloc_prop_binding
    );
    arena_accessors!(
        prop_binding_descs,
        PropagationBindingDescriptor,
        PropagationBindingDescriptorId,
        prop_binding_des,
        prop_binding_des_mut,
        alloc_prop_binding_des
    );
    arena_accessors!(
        prop_binding_reapply_con_descs,
        PropagationBindingReapplyConceptDescriptor,
        PropagationBindingReapplyConceptDescriptorId,
        prop_binding_reapply_con_des,
        prop_binding_reapply_con_des_mut,
        alloc_prop_binding_reapply_con_des
    );
    arena_accessors!(
        prop_binding_reapply_con_hashes,
        PropagationBindingReapplyConceptHash,
        PropagationBindingReapplyConceptHashId,
        prop_binding_reapply_con_hash,
        prop_binding_reapply_con_hash_mut,
        alloc_prop_binding_reapply_con_hash
    );
    arena_accessors!(
        prop_binding_sets,
        PropagationBindingSet,
        PropagationBindingSetId,
        prop_binding_set,
        prop_binding_set_mut,
        alloc_prop_binding_set
    );
    arena_accessors!(
        prop_var_bind_trans_exts,
        PropagationVariableBindingTransitionExtension,
        PropagationVariableBindingTransitionExtensionId,
        prop_var_bind_trans_ext,
        prop_var_bind_trans_ext_mut,
        alloc_prop_var_bind_trans_ext
    );
    arena_accessors!(
        prop_rep_trans_exts,
        PropagationRepresentativeTransitionExtension,
        PropagationRepresentativeTransitionExtensionId,
        prop_rep_trans_ext,
        prop_rep_trans_ext_mut,
        alloc_prop_rep_trans_ext
    );

    // --- W3.5r representative variable-binding-path-set subsystem trios ---
    arena_accessors!(
        rep_var_bind_path_set_datas,
        RepresentativeVariableBindingPathSetData,
        RepresentativeVariableBindingPathSetDataId,
        rep_var_bind_path_set_data,
        rep_var_bind_path_set_data_mut,
        alloc_rep_var_bind_path_set_data
    );
    arena_accessors!(
        rep_var_bind_path_set_migrate_datas,
        RepresentativeVariableBindingPathSetMigrateData,
        RepresentativeVariableBindingPathSetMigrateDataId,
        rep_var_bind_path_set_migrate_data,
        rep_var_bind_path_set_migrate_data_mut,
        alloc_rep_var_bind_path_set_migrate_data
    );
    arena_accessors!(
        rep_var_bind_path_joining_key_datas,
        RepresentativeVariableBindingPathJoiningKeyData,
        RepresentativeVariableBindingPathJoiningKeyDataId,
        rep_var_bind_path_joining_key_data,
        rep_var_bind_path_joining_key_data_mut,
        alloc_rep_var_bind_path_joining_key_data
    );
    arena_accessors!(
        rep_var_bind_path_joining_key_hashes,
        RepresentativeVariableBindingPathJoiningKeyHash,
        RepresentativeVariableBindingPathJoiningKeyHashId,
        rep_var_bind_path_joining_key_hash,
        rep_var_bind_path_joining_key_hash_mut,
        alloc_rep_var_bind_path_joining_key_hash
    );
    arena_accessors!(
        rep_var_bind_path_set_hashes,
        RepresentativeVariableBindingPathSetHash,
        RepresentativeVariableBindingPathSetHashId,
        rep_var_bind_path_set_hash,
        rep_var_bind_path_set_hash_mut,
        alloc_rep_var_bind_path_set_hash
    );
    arena_accessors!(
        rep_var_bind_path_hashes,
        RepresentativeVariableBindingPathHash,
        RepresentativeVariableBindingPathHashId,
        rep_var_bind_path_hash,
        rep_var_bind_path_hash_mut,
        alloc_rep_var_bind_path_hash
    );
    arena_accessors!(
        rep_var_bind_path_set_joining_datas,
        RepresentativeVariableBindingPathSetJoiningData,
        RepresentativeVariableBindingPathSetJoiningDataId,
        rep_var_bind_path_set_joining_data,
        rep_var_bind_path_set_joining_data_mut,
        alloc_rep_var_bind_path_set_joining_data
    );
    arena_accessors!(
        rep_var_bind_path_set_joining_hashes,
        RepresentativeVariableBindingPathSetJoiningHash,
        RepresentativeVariableBindingPathSetJoiningHashId,
        rep_var_bind_path_set_joining_hash,
        rep_var_bind_path_set_joining_hash_mut,
        alloc_rep_var_bind_path_set_joining_hash
    );
    arena_accessors!(
        rep_joining_datas,
        RepresentativeJoiningData,
        RepresentativeJoiningDataId,
        rep_joining_data,
        rep_joining_data_mut,
        alloc_rep_joining_data
    );
    arena_accessors!(
        rep_joining_hashes,
        RepresentativeJoiningHash,
        RepresentativeJoiningHashId,
        rep_joining_hash,
        rep_joining_hash_mut,
        alloc_rep_joining_hash
    );
    arena_accessors!(
        rep_prop_descs,
        RepresentativePropagationDescriptor,
        RepresentativePropagationDescriptorId,
        rep_prop_des,
        rep_prop_des_mut,
        alloc_rep_prop_des
    );
    arena_accessors!(
        rep_prop_sets,
        RepresentativePropagationSet,
        RepresentativePropagationSetId,
        rep_prop_set,
        rep_prop_set_mut,
        alloc_rep_prop_set
    );
    arena_accessors!(
        con_rep_prop_set_hashes,
        ConceptRepresentativePropagationSetHash,
        ConceptRepresentativePropagationSetHashId,
        con_rep_prop_set_hash,
        con_rep_prop_set_hash_mut,
        alloc_con_rep_prop_set_hash
    );

    // --- backend-neighbour expansion controlling data trios ---
    arena_accessors!(
        backend_neighbour_expansion_controlling_datas,
        BackendNeighbourExpansionControllingData,
        BackendNeighbourExpansionControllingDataId,
        backend_neighbour_expansion_controlling_data,
        backend_neighbour_expansion_controlling_data_mut,
        alloc_backend_neighbour_expansion_controlling_data
    );
    arena_accessors!(
        backend_sync_datas,
        IndividualNodeBackendCacheSynchronisationData,
        BackendSyncDataId,
        backend_sync_data,
        backend_sync_data_mut,
        alloc_backend_sync_data
    );

    // --- W3.5b blocking-individual-node candidate + signature-blocking concept-expansion trios ---
    arena_accessors!(
        blocking_indi_node_cand_hashes,
        BlockingIndividualNodeCandidateHash,
        BlockingIndividualNodeCandidateHashId,
        blocking_indi_node_cand_hash,
        blocking_indi_node_cand_hash_mut,
        alloc_blocking_indi_node_cand_hash
    );
    arena_accessors!(
        blocking_indi_node_cand_datas,
        BlockingIndividualNodeCandidateData,
        BlockingIndividualNodeCandidateDataId,
        blocking_indi_node_cand_data,
        blocking_indi_node_cand_data_mut,
        alloc_blocking_indi_node_cand_data
    );
    arena_accessors!(
        blocking_indi_node_linked_cand_hashes,
        BlockingIndividualNodeLinkedCandidateHash,
        BlockingIndividualNodeLinkedCandidateHashId,
        blocking_indi_node_linked_cand_hash,
        blocking_indi_node_linked_cand_hash_mut,
        alloc_blocking_indi_node_linked_cand_hash
    );
    arena_accessors!(
        blocking_indi_node_linked_cand_datas,
        BlockingIndividualNodeLinkedCandidateData,
        BlockingIndividualNodeLinkedCandidateDataId,
        blocking_indi_node_linked_cand_data,
        blocking_indi_node_linked_cand_data_mut,
        alloc_blocking_indi_node_linked_cand_data
    );
    arena_accessors!(
        blocking_indi_node_linkers,
        BlockingIndividualNodeLinker,
        BlockingIndividualNodeLinkerId,
        blocking_indi_node_linker,
        blocking_indi_node_linker_mut,
        alloc_blocking_indi_node_linker
    );

    /// Context-threaded port helper for
    /// `CBlockingIndividualNodeCandidateData::insertBlockingCandidateIndividualNode`.
    pub fn blocking_indi_node_cand_data_insert_blocking_candidate_individual_node(
        &mut self,
        data: BlockingIndividualNodeCandidateDataId,
        candidate_indi: NodeId,
    ) {
        let candidate_individual_id = self.node(candidate_indi).individual_node_id();
        self.blocking_indi_node_cand_data_mut(data)
            .candidate_indi_map
            .insert(-candidate_individual_id, candidate_indi);
    }

    /// Context-threaded port helper for
    /// `CBlockingIndividualNodeLinkedCandidateData::addBlockingCandidateIndividualNode`.
    pub fn blocking_indi_node_linked_cand_data_add_blocking_candidate_individual_node(
        &mut self,
        data: BlockingIndividualNodeLinkedCandidateDataId,
        candidate_indi: NodeId,
    ) {
        let mut linker = BlockingIndividualNodeLinker::new();
        linker.init_blocking_individual_node_linker(candidate_indi);
        let linker = self.alloc_blocking_indi_node_linker(linker);
        let old_head = self
            .blocking_indi_node_linked_cand_data(data)
            .get_blocking_candidates_individual_node_linker();
        self.blocking_indi_node_linker_mut(linker).append(old_head);
        let data_ref = self.blocking_indi_node_linked_cand_data_mut(data);
        data_ref.cand_linker = linker;
        data_ref.candidate_count += 1;
    }
    arena_accessors!(
        sig_block_con_exp_datas,
        SignatureBlockingIndividualNodeConceptExpansionData,
        SignatureBlockingIndividualNodeConceptExpansionDataId,
        sig_block_con_exp_data,
        sig_block_con_exp_data_mut,
        alloc_sig_block_con_exp_data
    );
    arena_accessors!(
        reusing_con_exp_datas,
        ReusingIndividualNodeConceptExpansionData,
        ReusingIndividualNodeConceptExpansionDataId,
        reusing_con_exp_data,
        reusing_con_exp_data_mut,
        alloc_reusing_con_exp_data
    );
    arena_accessors!(
        signature_blocking_review_sets,
        SignatureBlockingReviewSet,
        SignatureBlockingReviewSetId,
        signature_blocking_review_set,
        signature_blocking_review_set_mut,
        alloc_signature_blocking_review_set
    );
    arena_accessors!(
        reusing_review_datas,
        ReusingReviewData,
        ReusingReviewDataId,
        reusing_review_data,
        reusing_review_data_mut,
        alloc_reusing_review_data
    );
    arena_accessors!(
        node_switch_histories,
        NodeSwitchHistory,
        NodeSwitchHistoryId,
        node_switch_history,
        node_switch_history_mut,
        alloc_node_switch_history
    );
    arena_accessors!(
        branching_trees,
        BranchingTree,
        BranchingTreeId,
        branching_tree,
        branching_tree_mut,
        alloc_branching_tree
    );

    /// Context-threaded port of
    /// `CBranchingTree::getBranchTreeNode(CSatisfiableCalculationTask*, bool)`.
    pub fn branching_tree_branch_tree_node(
        &mut self,
        tree_id: BranchingTreeId,
        sat_calc_task: Cint64,
        force_branch_creation: bool,
    ) -> BranchNodeId {
        let mut curr_node = self.branching_tree(tree_id).curr_node;
        if curr_node.is_some() {
            if self
                .branch_node(curr_node)
                .get_satisfiable_calculation_task()
                != sat_calc_task
            {
                let branch_node = self.alloc_branch_node(BranchTreeNode::new());
                BranchTreeNode::init_branching_copy_node(
                    &mut self.branch_nodes,
                    branch_node,
                    curr_node,
                    sat_calc_task,
                );
                curr_node = branch_node;
                let branch_node_is_root = self.branch_node(branch_node).is_root_node();
                let tree = self.branching_tree_mut(tree_id);
                tree.curr_node = branch_node;
                tree.prev_curr_node = branch_node;
                if branch_node_is_root {
                    tree.root_node = branch_node;
                }
            }
            if force_branch_creation {
                let branch_node = self.alloc_branch_node(BranchTreeNode::new());
                BranchTreeNode::init_branching_child_node(
                    &mut self.branch_nodes,
                    branch_node,
                    curr_node,
                    sat_calc_task,
                );
                let tree = self.branching_tree_mut(tree_id);
                tree.curr_node = branch_node;
                tree.prev_curr_node = branch_node;
                curr_node = branch_node;
            }
        } else {
            let prev_curr_node = self.branching_tree(tree_id).prev_curr_node;
            let branch_node = if prev_curr_node.is_some() {
                let branch_node = self.alloc_branch_node(BranchTreeNode::new());
                BranchTreeNode::init_branching_child_node(
                    &mut self.branch_nodes,
                    branch_node,
                    prev_curr_node,
                    sat_calc_task,
                );
                branch_node
            } else {
                let branch_node = self.alloc_branch_node(BranchTreeNode::new());
                self.branch_node_mut(branch_node)
                    .init_branching_root_node(branch_node, sat_calc_task);
                self.branching_tree_mut(tree_id).root_node = branch_node;
                branch_node
            };
            let tree = self.branching_tree_mut(tree_id);
            tree.curr_node = branch_node;
            tree.prev_curr_node = branch_node;
            curr_node = branch_node;
        }
        curr_node
    }

    /// Context-threaded port of `CBranchingTree::getBaseDependencyNode`.

    // =======================================================================
    // Branch-epoch COW (in-process stand-in for Konclude's per-task memory
    // pools + copy-on-write databox referencing). One epoch per ACTIVE OR
    // alternative: `pop_branch_epoch` rolls back every allocation AND every
    // in-place mutation made under the alternative — the complete-graph
    // restore the single-node label snapshot could not provide. The
    // dependency track-point and branch-node arenas are WATERMARK-ONLY: their
    // in-place mutations (clash markings, branching tags) are branch-SHARED
    // state in Konclude and must survive the alternative's death (the DDB
    // learning / all-siblings-clashed propagation).
    // =======================================================================

    /// Open a branch epoch across every arena.
    pub fn push_branch_epoch(&mut self) {
        self.additional_data_assertion_linkers.push_epoch();
        self.additional_role_assertion_linkers.push_epoch();
        self.analized_con_exp_datas.push_epoch();
        self.analized_con_exp_linkers.push_epoch();
        self.backend_neighbour_expansion_controlling_datas
            .push_epoch();
        self.backend_sync_datas.push_epoch();
        self.backward_prop_links.push_epoch();
        self.backward_prop_reapply_descs.push_epoch();
        self.backward_sat_prop_links.push_epoch();
        self.backward_sat_prop_reapply_descs.push_epoch();
        self.blocking_alt_datas.push_epoch();
        self.blocking_follow_sets.push_epoch();
        self.blocking_indi_node_cand_datas.push_epoch();
        self.blocking_indi_node_cand_hashes.push_epoch();
        self.blocking_indi_node_linked_cand_datas.push_epoch();
        self.blocking_indi_node_linked_cand_hashes.push_epoch();
        self.blocking_indi_node_linkers.push_epoch();
        self.blocking_test_datas.push_epoch();
        self.branching_merging_candidate_linkers.push_epoch();
        self.branching_trees.push_epoch();
        self.branch_instrs.push_epoch();
        // clash_descs is epoch-EXEMPT: the DDB marks (`set_clashes`) store
        // ClashDescId lists on track points that SURVIVE alternative pops
        // (watermark-only arenas) — truncating the descriptors would leave
        // dangling ids in surviving branch memory (Konclude allocates these
        // from the branch-shared pool for exactly this reason). Append-only;
        // persists until the probe environment is dropped.
        self.concept_nominal_schema_grounding_datas.push_epoch();
        self.concept_nominal_schema_grounding_hashes.push_epoch();
        self.concept_process_linkers.push_epoch();
        self.concept_proc_queues.push_epoch();
        // con_descs: epoch-exempt — persisted DDB marks reference concept
        // descriptors transitively (tracked-copy hasher/tag reads); label
        // CONTENT is governed by the journaled label-set map, and ported
        // label descriptors do not chain `.next`, so persistence cannot leak
        // popped concepts back into a restored label.
        self.cond_reapply_con_descs.push_epoch();
        self.conn_succ_corr_hashes.push_epoch();
        self.conn_succ_sets.push_epoch();
        self.con_proc_descs.push_epoch();
        self.con_prop_binding_set_hashes.push_epoch();
        self.con_rep_prop_set_hashes.push_epoch();
        self.con_sat_descs.push_epoch();
        self.con_sat_proc_linkers.push_epoch();
        self.con_var_bind_path_set_hashes.push_epoch();
        self.core_con_descs.push_epoch();
        self.critical_pred_role_card_datas.push_epoch();
        self.critical_pred_role_card_hashes.push_epoch();
        self.critical_sat_concept_queues.push_epoch();
        self.critical_sat_concept_type_queues.push_epoch();
        self.datatypes_value_space_datas.push_epoch();
        self.data_value_role_assertion_linkers.push_epoch();
        // dep_links: epoch-exempt — dependency spine is branch-SHARED memory
        // dep_nodes: epoch-exempt — dependency spine is branch-SHARED memory
        self.disjoint_edges.push_epoch();
        self.disjoint_succ_role_hashes.push_epoch();
        self.distinct_edges.push_epoch();
        self.distinct_hashes.push_epoch();
        self.edges.push_epoch();
        self.extended_con_ref_linking_datas.push_epoch();
        self.imp_reapply_con_sat_descs.push_epoch();
        self.inc_exp_datas.push_epoch();
        self.indi_concept_batch_proc_queues.push_epoch();
        self.indi_custom_priority_proc_queues.push_epoch();
        self.indi_depth_proc_queues.push_epoch();
        self.indi_proc_node_descs.push_epoch();
        self.indi_proc_queues.push_epoch();
        self.indi_reactivation_proc_queues.push_epoch();
        self.indi_rotation_proc_queues.push_epoch();
        self.indi_sat_block_datas.push_epoch();
        self.indi_sat_node_ext_datas.push_epoch();
        self.indi_sat_process_node_linkers.push_epoch();
        self.indi_sat_succ_link_data_linkers.push_epoch();
        self.indi_unsorted_proc_queues.push_epoch();
        self.individual_merging_hashes.push_epoch();
        self.individual_process_node_linkers.push_epoch();
        self.label_sets.push_epoch();
        self.linked_data_value_assertion_datas.push_epoch();
        self.linked_role_sat_succ_datas.push_epoch();
        self.linked_role_sat_succ_hashes.push_epoch();
        self.marker_indi_node_datas.push_epoch();
        self.marker_indi_node_hashes.push_epoch();
        self.nodes.push_epoch();
        self.node_switch_histories.push_epoch();
        self.nominal_caching_loss_reactivation_datas.push_epoch();
        self.nominal_caching_loss_reactivation_hashes.push_epoch();
        self.nominal_conn_sets.push_epoch();
        self.process_asserted_data_literal_linkers.push_epoch();
        self.prop_binding_descs.push_epoch();
        self.prop_binding_reapply_con_descs.push_epoch();
        self.prop_binding_reapply_con_hashes.push_epoch();
        self.prop_bindings.push_epoch();
        self.prop_binding_sets.push_epoch();
        self.prop_rep_trans_exts.push_epoch();
        self.prop_var_bind_trans_exts.push_epoch();
        self.reapply_con_descs.push_epoch();
        self.reapply_con_sat_label_sets.push_epoch();
        self.referred_individual_tracking_vectors.push_epoch();
        self.rep_joining_datas.push_epoch();
        self.rep_joining_hashes.push_epoch();
        self.rep_prop_descs.push_epoch();
        self.rep_prop_sets.push_epoch();
        self.rep_var_bind_path_hashes.push_epoch();
        self.rep_var_bind_path_joining_key_datas.push_epoch();
        self.rep_var_bind_path_joining_key_hashes.push_epoch();
        self.rep_var_bind_path_set_datas.push_epoch();
        self.rep_var_bind_path_set_hashes.push_epoch();
        self.rep_var_bind_path_set_joining_datas.push_epoch();
        self.rep_var_bind_path_set_joining_hashes.push_epoch();
        self.rep_var_bind_path_set_migrate_datas.push_epoch();
        self.restriction_specs.push_epoch();
        self.reusing_con_exp_datas.push_epoch();
        self.reusing_review_datas.push_epoch();
        self.role_backward_prop_hashes.push_epoch();
        self.role_backward_sat_prop_hashes.push_epoch();
        self.role_sat_proc_linkers.push_epoch();
        self.role_succ_hashes.push_epoch();
        self.sat_atmost_successor_merging_datas.push_epoch();
        self.sat_atmost_successor_merging_hashes.push_epoch();
        self.sat_concept_extension_maps.push_epoch();
        self.sat_critical_ind_node_con_test_sets.push_epoch();
        self.sat_critical_ind_node_proc_queues.push_epoch();
        self.sat_disjunct_common_concept_extraction_datas
            .push_epoch();
        self.sat_disjunct_extraction_linkers.push_epoch();
        self.sat_indi_node_all_concept_ext_datas.push_epoch();
        self.sat_indi_node_datatype_datas.push_epoch();
        self.sat_indi_node_ext_resolve_datas.push_epoch();
        self.sat_indi_node_ext_resolve_hashes.push_epoch();
        self.sat_indi_node_functional_concept_ext_datas.push_epoch();
        self.sat_indi_node_succ_ext_datas.push_epoch();
        self.sat_influenced_nominal_sets.push_epoch();
        self.sat_linked_succ_indi_all_concept_ext_datas.push_epoch();
        self.sat_modified_process_update_linkers.push_epoch();
        self.sat_nodes.push_epoch();
        self.sat_nominal_dependent_node_datas.push_epoch();
        self.sat_nominal_dependent_node_hashes.push_epoch();
        self.sat_nominal_handling_datas.push_epoch();
        self.sat_succ_datas.push_epoch();
        self.sat_successor_all_concept_ext_datas.push_epoch();
        self.sat_successor_concept_extension_maps.push_epoch();
        self.sat_successor_functional_concept_ext_datas.push_epoch();
        self.sat_succ_ext_datas.push_epoch();
        self.sat_succ_ext_ind_node_proc_queues.push_epoch();
        self.sat_succ_role_assertion_linkers.push_epoch();
        self.sig_block_cand_hashes.push_epoch();
        self.sig_block_con_exp_datas.push_epoch();
        self.signature_blocking_review_sets.push_epoch();
        self.successor_individual_atmost_reactivation_datas
            .push_epoch();
        self.succ_role_hashes.push_epoch();
        self.unsat_cache_ret_datas.push_epoch();
        self.var_binding_descs.push_epoch();
        self.var_binding_path_descs.push_epoch();
        self.var_binding_path_join_datas.push_epoch();
        self.var_binding_path_join_hashes.push_epoch();
        self.var_binding_path_merging_hashes.push_epoch();
        self.var_binding_paths.push_epoch();
        self.var_binding_path_sets.push_epoch();
        self.var_bindings.push_epoch();
        self.var_binding_trigger_hashes.push_epoch();
        self.var_binding_trigger_linkers.push_epoch();
        // track_points / branch_nodes: epoch-exempt — in Konclude the whole
        // dependency spine (nodes, links, track points, branch tree) lives in
        // branch-SHARED memory that outlives every alternative of the task
        // subtree: the DDB marks stored on surviving track points reference
        // dependency chains transitively, so truncating ANY spine arena per
        // alternative leaves dangling ids in persisted clash sets (measured:
        // ore_ont_541 Plan⊑Particular probe panicked reading a truncated
        // continue track point). Append-only per probe environment.
        self.branch_epoch_depth += 1;
    }

    /// KM_BRIDGE_SEARCH_LOG diagnostics: verify node→satellite id coherence —
    /// a node surviving a pop must not point at a TRUNCATED satellite slot
    /// (the dangling-id corruption fingerprint: empty/aliased labels →
    /// duplicate ∃-successors → phantom at-most violations).
    pub fn ht_check_dangling_satellites(&self, wher: &str) {
        if std::env::var_os("KM_BRIDGE_SEARCH_LOG").is_none() {
            return;
        }
        let n_ls = self.label_sets.len();
        let n_q = self.concept_proc_queues.len();
        let n_srh = self.succ_role_hashes.len();
        for ix in 0..self.nodes.len() {
            let n = self.nodes.get(super::NodeId::new(ix as Cint64));
            let ls = n.use_reapply_con_label_set;
            if ls.is_some() && ls.index() >= n_ls {
                eprintln!(
                    "SL DANGLING at {wher} node={ix} label_set={} >= len {n_ls}",
                    ls.index()
                );
            }
            let q = n.use_concept_processing_queue;
            if q.is_some() && q.index() >= n_q {
                eprintln!(
                    "SL DANGLING at {wher} node={ix} proc_queue={} >= len {n_q}",
                    q.index()
                );
            }
            let h = n.use_succ_role_hash;
            if h.is_some() && h.index() >= n_srh {
                eprintln!(
                    "SL DANGLING at {wher} node={ix} succ_hash={} >= len {n_srh}",
                    h.index()
                );
            }
        }
    }

    /// Close the innermost branch epoch: journal-rollback + truncate.
    pub fn pop_branch_epoch(&mut self) {
        self.additional_data_assertion_linkers.pop_epoch();
        self.additional_role_assertion_linkers.pop_epoch();
        self.analized_con_exp_datas.pop_epoch();
        self.analized_con_exp_linkers.pop_epoch();
        self.backend_neighbour_expansion_controlling_datas
            .pop_epoch();
        self.backend_sync_datas.pop_epoch();
        self.backward_prop_links.pop_epoch();
        self.backward_prop_reapply_descs.pop_epoch();
        self.backward_sat_prop_links.pop_epoch();
        self.backward_sat_prop_reapply_descs.pop_epoch();
        self.blocking_alt_datas.pop_epoch();
        self.blocking_follow_sets.pop_epoch();
        self.blocking_indi_node_cand_datas.pop_epoch();
        self.blocking_indi_node_cand_hashes.pop_epoch();
        self.blocking_indi_node_linked_cand_datas.pop_epoch();
        self.blocking_indi_node_linked_cand_hashes.pop_epoch();
        self.blocking_indi_node_linkers.pop_epoch();
        self.blocking_test_datas.pop_epoch();
        self.branching_merging_candidate_linkers.pop_epoch();
        self.branching_trees.pop_epoch();
        self.branch_instrs.pop_epoch();
        // clash_descs: epoch-exempt (see push_branch_epoch).
        self.concept_nominal_schema_grounding_datas.pop_epoch();
        self.concept_nominal_schema_grounding_hashes.pop_epoch();
        self.concept_process_linkers.pop_epoch();
        self.concept_proc_queues.pop_epoch();
        // con_descs: epoch-exempt (see push_branch_epoch).
        self.cond_reapply_con_descs.pop_epoch();
        self.conn_succ_corr_hashes.pop_epoch();
        self.conn_succ_sets.pop_epoch();
        self.con_proc_descs.pop_epoch();
        self.con_prop_binding_set_hashes.pop_epoch();
        self.con_rep_prop_set_hashes.pop_epoch();
        self.con_sat_descs.pop_epoch();
        self.con_sat_proc_linkers.pop_epoch();
        self.con_var_bind_path_set_hashes.pop_epoch();
        self.core_con_descs.pop_epoch();
        self.critical_pred_role_card_datas.pop_epoch();
        self.critical_pred_role_card_hashes.pop_epoch();
        self.critical_sat_concept_queues.pop_epoch();
        self.critical_sat_concept_type_queues.pop_epoch();
        self.datatypes_value_space_datas.pop_epoch();
        self.data_value_role_assertion_linkers.pop_epoch();
        // dep_links: epoch-exempt (see push)
        // dep_nodes: epoch-exempt (see push)
        self.disjoint_edges.pop_epoch();
        self.disjoint_succ_role_hashes.pop_epoch();
        self.distinct_edges.pop_epoch();
        self.distinct_hashes.pop_epoch();
        self.edges.pop_epoch();
        self.extended_con_ref_linking_datas.pop_epoch();
        self.imp_reapply_con_sat_descs.pop_epoch();
        self.inc_exp_datas.pop_epoch();
        self.indi_concept_batch_proc_queues.pop_epoch();
        self.indi_custom_priority_proc_queues.pop_epoch();
        self.indi_depth_proc_queues.pop_epoch();
        self.indi_proc_node_descs.pop_epoch();
        self.indi_proc_queues.pop_epoch();
        self.indi_reactivation_proc_queues.pop_epoch();
        self.indi_rotation_proc_queues.pop_epoch();
        self.indi_sat_block_datas.pop_epoch();
        self.indi_sat_node_ext_datas.pop_epoch();
        self.indi_sat_process_node_linkers.pop_epoch();
        self.indi_sat_succ_link_data_linkers.pop_epoch();
        self.indi_unsorted_proc_queues.pop_epoch();
        self.individual_merging_hashes.pop_epoch();
        self.individual_process_node_linkers.pop_epoch();
        self.label_sets.pop_epoch();
        self.linked_data_value_assertion_datas.pop_epoch();
        self.linked_role_sat_succ_datas.pop_epoch();
        self.linked_role_sat_succ_hashes.pop_epoch();
        self.marker_indi_node_datas.pop_epoch();
        self.marker_indi_node_hashes.pop_epoch();
        self.nodes.pop_epoch();
        self.node_switch_histories.pop_epoch();
        self.nominal_caching_loss_reactivation_datas.pop_epoch();
        self.nominal_caching_loss_reactivation_hashes.pop_epoch();
        self.nominal_conn_sets.pop_epoch();
        self.process_asserted_data_literal_linkers.pop_epoch();
        self.prop_binding_descs.pop_epoch();
        self.prop_binding_reapply_con_descs.pop_epoch();
        self.prop_binding_reapply_con_hashes.pop_epoch();
        self.prop_bindings.pop_epoch();
        self.prop_binding_sets.pop_epoch();
        self.prop_rep_trans_exts.pop_epoch();
        self.prop_var_bind_trans_exts.pop_epoch();
        self.reapply_con_descs.pop_epoch();
        self.reapply_con_sat_label_sets.pop_epoch();
        self.referred_individual_tracking_vectors.pop_epoch();
        self.rep_joining_datas.pop_epoch();
        self.rep_joining_hashes.pop_epoch();
        self.rep_prop_descs.pop_epoch();
        self.rep_prop_sets.pop_epoch();
        self.rep_var_bind_path_hashes.pop_epoch();
        self.rep_var_bind_path_joining_key_datas.pop_epoch();
        self.rep_var_bind_path_joining_key_hashes.pop_epoch();
        self.rep_var_bind_path_set_datas.pop_epoch();
        self.rep_var_bind_path_set_hashes.pop_epoch();
        self.rep_var_bind_path_set_joining_datas.pop_epoch();
        self.rep_var_bind_path_set_joining_hashes.pop_epoch();
        self.rep_var_bind_path_set_migrate_datas.pop_epoch();
        self.restriction_specs.pop_epoch();
        self.reusing_con_exp_datas.pop_epoch();
        self.reusing_review_datas.pop_epoch();
        self.role_backward_prop_hashes.pop_epoch();
        self.role_backward_sat_prop_hashes.pop_epoch();
        self.role_sat_proc_linkers.pop_epoch();
        self.role_succ_hashes.pop_epoch();
        self.sat_atmost_successor_merging_datas.pop_epoch();
        self.sat_atmost_successor_merging_hashes.pop_epoch();
        self.sat_concept_extension_maps.pop_epoch();
        self.sat_critical_ind_node_con_test_sets.pop_epoch();
        self.sat_critical_ind_node_proc_queues.pop_epoch();
        self.sat_disjunct_common_concept_extraction_datas
            .pop_epoch();
        self.sat_disjunct_extraction_linkers.pop_epoch();
        self.sat_indi_node_all_concept_ext_datas.pop_epoch();
        self.sat_indi_node_datatype_datas.pop_epoch();
        self.sat_indi_node_ext_resolve_datas.pop_epoch();
        self.sat_indi_node_ext_resolve_hashes.pop_epoch();
        self.sat_indi_node_functional_concept_ext_datas.pop_epoch();
        self.sat_indi_node_succ_ext_datas.pop_epoch();
        self.sat_influenced_nominal_sets.pop_epoch();
        self.sat_linked_succ_indi_all_concept_ext_datas.pop_epoch();
        self.sat_modified_process_update_linkers.pop_epoch();
        self.sat_nodes.pop_epoch();
        self.sat_nominal_dependent_node_datas.pop_epoch();
        self.sat_nominal_dependent_node_hashes.pop_epoch();
        self.sat_nominal_handling_datas.pop_epoch();
        self.sat_succ_datas.pop_epoch();
        self.sat_successor_all_concept_ext_datas.pop_epoch();
        self.sat_successor_concept_extension_maps.pop_epoch();
        self.sat_successor_functional_concept_ext_datas.pop_epoch();
        self.sat_succ_ext_datas.pop_epoch();
        self.sat_succ_ext_ind_node_proc_queues.pop_epoch();
        self.sat_succ_role_assertion_linkers.pop_epoch();
        self.sig_block_cand_hashes.pop_epoch();
        self.sig_block_con_exp_datas.pop_epoch();
        self.signature_blocking_review_sets.pop_epoch();
        self.successor_individual_atmost_reactivation_datas
            .pop_epoch();
        self.succ_role_hashes.pop_epoch();
        self.unsat_cache_ret_datas.pop_epoch();
        self.var_binding_descs.pop_epoch();
        self.var_binding_path_descs.pop_epoch();
        self.var_binding_path_join_datas.pop_epoch();
        self.var_binding_path_join_hashes.pop_epoch();
        self.var_binding_path_merging_hashes.pop_epoch();
        self.var_binding_paths.pop_epoch();
        self.var_binding_path_sets.pop_epoch();
        self.var_bindings.pop_epoch();
        self.var_binding_trigger_hashes.pop_epoch();
        self.var_binding_trigger_linkers.pop_epoch();
        // dependency spine arenas: epoch-exempt (see push_branch_epoch).
        self.branch_epoch_depth -= 1;
    }

    /// Open branch epochs (0 = none).
    #[inline]
    pub fn branch_epoch_depth(&self) -> usize {
        self.branch_epoch_depth
    }

    pub fn branching_tree_base_dependency_node(
        &mut self,
        tree_id: BranchingTreeId,
        create: bool,
    ) -> DependencyId {
        let base_dep_node = self.branching_tree(tree_id).base_dep_node;
        if base_dep_node.is_none() && create {
            let dep_node = self.alloc_independent_base_dependency_node();
            self.dep_node_mut(dep_node)
                .init_independent_base_dependency_node();
            self.branching_tree_mut(tree_id).base_dep_node = dep_node;
            dep_node
        } else {
            base_dep_node
        }
    }
    arena_accessors!(
        marker_indi_node_hashes,
        MarkerIndividualNodeHash,
        MarkerIndividualNodeHashId,
        marker_indi_node_hash,
        marker_indi_node_hash_mut,
        alloc_marker_indi_node_hash
    );
    arena_accessors!(
        marker_indi_node_datas,
        MarkerIndividualNodeData,
        MarkerIndividualNodeDataId,
        marker_indi_node_data,
        marker_indi_node_data_mut,
        alloc_marker_indi_node_data
    );
    arena_accessors!(
        unsat_cache_ret_datas,
        IndividualNodeUnsatisfiableOccurenceCacheRetrievalData,
        IndividualNodeUnsatisfiableOccurenceCacheRetrievalDataId,
        unsat_cache_ret_data,
        unsat_cache_ret_data_mut,
        alloc_unsat_cache_ret_data
    );
    arena_accessors!(
        referred_individual_tracking_vectors,
        ReferredIndividualTrackingVector,
        ReferredIndividualTrackingVectorId,
        referred_individual_tracking_vector,
        referred_individual_tracking_vector_mut,
        alloc_referred_individual_tracking_vector
    );

    /// Context-threaded port helper for
    /// `CProcessingDataBox::getMarkerIndividualNodeHash(true)`.
    pub fn processing_data_box_marker_individual_node_hash(
        &mut self,
        data_box: &mut super::databox::ProcessingDataBox,
        create_or_force_localisation: bool,
    ) -> MarkerIndividualNodeHashId {
        if create_or_force_localisation && data_box.loc_marker_indi_node_hash.is_none() {
            let prev = data_box.use_marker_indi_node_hash;
            let new_hash = self.alloc_marker_indi_node_hash(MarkerIndividualNodeHash::new(INVALID));
            if prev.is_some() {
                let taken = std::mem::replace(
                    self.marker_indi_node_hash_mut(prev),
                    MarkerIndividualNodeHash::new(INVALID),
                );
                self.marker_indi_node_hash_mut(new_hash)
                    .init_marker_individual_node_hash(Some(&taken));
                *self.marker_indi_node_hash_mut(prev) = taken;
            } else {
                self.marker_indi_node_hash_mut(new_hash)
                    .init_marker_individual_node_hash(None);
            }
            data_box.loc_marker_indi_node_hash = new_hash;
            data_box.use_marker_indi_node_hash = new_hash;
        }
        data_box.use_marker_indi_node_hash
    }

    /// Context-threaded port helper for
    /// `CProcessingDataBox::getSaturationSucessorExtensionIndividualNodeProcessingQueue(true)`.
    pub fn processing_data_box_saturation_successor_extension_individual_node_processing_queue(
        &mut self,
        data_box: &mut super::databox::ProcessingDataBox,
        create: bool,
    ) -> SaturationSuccessorExtensionIndividualNodeProcessingQueueId {
        if data_box.sat_succ_ext_ind_node_proc_queue.is_none() && create {
            let queue = self.alloc_sat_succ_ext_ind_node_proc_queue(
                SaturationSuccessorExtensionIndividualNodeProcessingQueue::new(INVALID),
            );
            self.sat_succ_ext_ind_node_proc_queue_mut(queue)
                .init_processing_queue(None);
            data_box.sat_succ_ext_ind_node_proc_queue = queue;
        }
        data_box.sat_succ_ext_ind_node_proc_queue
    }

    /// Context-threaded port helper for
    /// `CProcessingDataBox::getSaturationCriticalIndividualNodeProcessingQueue(true)`.
    pub fn processing_data_box_saturation_critical_individual_node_processing_queue(
        &mut self,
        data_box: &mut super::databox::ProcessingDataBox,
        create: bool,
    ) -> CriticalIndividualNodeProcessingQueueId {
        if data_box.sat_critical_indi_node_proc_queue.is_none() && create {
            let queue = self.alloc_sat_critical_ind_node_proc_queue(
                CriticalIndividualNodeProcessingQueue::new(INVALID),
            );
            self.sat_critical_ind_node_proc_queue_mut(queue)
                .init_processing_queue(None);
            data_box.sat_critical_indi_node_proc_queue = queue;
        }
        data_box.sat_critical_indi_node_proc_queue
    }

    /// Context-threaded port helper for
    /// `CProcessingDataBox::getSaturationCriticalIndividualNodeConceptTestSet(true)`.
    pub fn processing_data_box_saturation_critical_individual_node_concept_test_set(
        &mut self,
        data_box: &mut super::databox::ProcessingDataBox,
        create: bool,
    ) -> CriticalIndividualNodeConceptTestSetId {
        if data_box.sat_critical_indi_node_con_test_set.is_none() && create {
            let set = self.alloc_sat_critical_ind_node_con_test_set(
                CriticalIndividualNodeConceptTestSet::new(INVALID),
            );
            self.sat_critical_ind_node_con_test_set_mut(set)
                .init_individual_node_concept_test_set(None);
            data_box.sat_critical_indi_node_con_test_set = set;
        }
        data_box.sat_critical_indi_node_con_test_set
    }

    /// Context-threaded port helper for
    /// `CProcessingDataBox::getNominalCachingLossReactivationHash(true)`.
    pub fn processing_data_box_nominal_caching_loss_reactivation_hash(
        &mut self,
        data_box: &mut super::databox::ProcessingDataBox,
        create_or_force_localisation: bool,
    ) -> NominalCachingLossReactivationHashId {
        if data_box.loc_nom_caching_loss_react_hash.is_none() && create_or_force_localisation {
            let prev = data_box.use_nom_caching_loss_react_hash;
            let hash = self.alloc_nominal_caching_loss_reactivation_hash(
                NominalCachingLossReactivationHash::new(INVALID),
            );
            if prev.is_some() {
                let prev_hash = self.nominal_caching_loss_reactivation_hash(prev).clone();
                self.nominal_caching_loss_reactivation_hash_mut(hash)
                    .init_nominal_dependent_node_hash(Some(&prev_hash));
            } else {
                self.nominal_caching_loss_reactivation_hash_mut(hash)
                    .init_nominal_dependent_node_hash(None);
            }
            data_box.loc_nom_caching_loss_react_hash = hash;
            data_box.use_nom_caching_loss_react_hash = hash;
        }
        data_box.use_nom_caching_loss_react_hash
    }

    /// Context-threaded port of
    /// `CNominalCachingLossReactivationHash::getNominalCachingLossReactivationData(cint64, bool)`.
    pub fn nominal_caching_loss_reactivation_hash_get_data(
        &mut self,
        hash: NominalCachingLossReactivationHashId,
        nominal_id: Cint64,
        create: bool,
    ) -> NominalCachingLossReactivationDataId {
        if hash.is_none() {
            return NominalCachingLossReactivationDataId::NONE;
        }
        if !create {
            return self
                .nominal_caching_loss_reactivation_hash(hash)
                .get_nominal_caching_loss_reactivation_data(nominal_id);
        }

        let (current, prev) = {
            let data = self
                .nominal_caching_loss_reactivation_hash_mut(hash)
                .nominal_reactivation_data_hash
                .entry(nominal_id)
                .or_default();
            (data.reactivation_data, data.prev_reactivation_data)
        };
        if current.is_some() {
            return current;
        }

        let prev_data = if prev.is_some() {
            Some(self.nominal_caching_loss_reactivation_data(prev).clone())
        } else {
            None
        };
        let new_data = self.alloc_nominal_caching_loss_reactivation_data(
            NominalCachingLossReactivationData::new(INVALID),
        );
        self.nominal_caching_loss_reactivation_data_mut(new_data)
            .init_nominal_caching_loss_reactivation_data(nominal_id, prev_data.as_ref());
        let data = self
            .nominal_caching_loss_reactivation_hash_mut(hash)
            .nominal_reactivation_data_hash
            .entry(nominal_id)
            .or_default();
        data.reactivation_data = new_data;
        data.prev_reactivation_data = new_data;
        new_data
    }

    /// Context-threaded port helper for
    /// `CProcessingDataBox::getSaturationInfluencedNominalSet(true)`.
    pub fn processing_data_box_saturation_influenced_nominal_set(
        &mut self,
        data_box: &mut super::databox::ProcessingDataBox,
        create: bool,
    ) -> SaturationInfluencedNominalSetId {
        if data_box.sat_influenced_nominal_set.is_none() && create {
            let set =
                self.alloc_sat_influenced_nominal_set(SaturationInfluencedNominalSet::new(INVALID));
            self.sat_influenced_nominal_set_mut(set)
                .init_influenced_nominal_set(None);
            data_box.sat_influenced_nominal_set = set;
        }
        data_box.sat_influenced_nominal_set
    }

    /// Context-threaded port helper for
    /// `CProcessingDataBox::getSaturationNominalDependentNodeHash(true)`.
    pub fn processing_data_box_saturation_nominal_dependent_node_hash(
        &mut self,
        data_box: &mut super::databox::ProcessingDataBox,
        create: bool,
    ) -> SaturationNominalDependentNodeHashId {
        if data_box.sat_nominal_dependent_node_hash.is_none() && create {
            let hash = self.alloc_sat_nominal_dependent_node_hash(
                SaturationNominalDependentNodeHash::new(INVALID),
            );
            self.sat_nominal_dependent_node_hash_mut(hash)
                .init_nominal_dependent_node_hash(None);
            data_box.sat_nominal_dependent_node_hash = hash;
        }
        data_box.sat_nominal_dependent_node_hash
    }

    /// Context-threaded port of
    /// `CSaturationNominalDependentNodeHash::addNominalDependentNode`.
    pub fn sat_nominal_dependent_node_hash_add_nominal_dependent_node(
        &mut self,
        hash: SaturationNominalDependentNodeHashId,
        nominal_id: Cint64,
        dependent_node: SatNodeId,
        connection_type: SaturationNominalConnectionType,
    ) -> SaturationNominalDependentNodeDataId {
        let data = self.alloc_sat_nominal_dependent_node_data(
            SaturationNominalDependentNodeData::new(INVALID),
        );
        self.sat_nominal_dependent_node_data_mut(data)
            .init_nominal_dependent_node_data(dependent_node, connection_type);
        let old_head = self
            .sat_nominal_dependent_node_hash_mut(hash)
            .add_nominal_dependent_node_data(nominal_id, data);
        self.sat_nominal_dependent_node_data_mut(data)
            .append(old_head);
        data
    }

    /// Context-threaded port helper for
    /// `CProcessingDataBox::getConceptNominalSchemaGroundingHash(true)`.
    pub fn processing_data_box_concept_nominal_schema_grounding_hash(
        &mut self,
        data_box: &mut super::databox::ProcessingDataBox,
        force_localisation: bool,
    ) -> ConceptNominalSchemaGroundingHashId {
        if force_localisation && data_box.loc_grounding_hash.is_none() {
            let prev = data_box.use_grounding_hash;
            let new_hash =
                self.alloc_grounding_hash(ConceptNominalSchemaGroundingHash::new(INVALID));
            if prev.is_some() {
                let taken = std::mem::replace(
                    self.grounding_hash_mut(prev),
                    ConceptNominalSchemaGroundingHash::new(INVALID),
                );
                self.grounding_hash_mut(new_hash)
                    .init_concept_nominal_schema_grounding_hash(Some(&taken));
                *self.grounding_hash_mut(prev) = taken;
            } else {
                self.grounding_hash_mut(new_hash)
                    .init_concept_nominal_schema_grounding_hash(None);
            }
            data_box.loc_grounding_hash = new_hash;
            data_box.use_grounding_hash = new_hash;
        }
        data_box.use_grounding_hash
    }

    /// Context-threaded port helper for
    /// `CProcessingDataBox::getVariableBindingPathMergingHash(true)`.
    pub fn processing_data_box_variable_binding_path_merging_hash(
        &mut self,
        data_box: &mut super::databox::ProcessingDataBox,
        force_localisation: bool,
    ) -> VariableBindingPathMergingHashId {
        if force_localisation && data_box.loc_var_binding_path_merging_hash.is_none() {
            let prev = data_box.use_var_binding_path_merging_hash;
            let new_hash =
                self.alloc_vbpath_merging_hash(VariableBindingPathMergingHash::new(INVALID));
            if prev.is_some() {
                let taken = std::mem::replace(
                    self.vbpath_merging_hash_mut(prev),
                    VariableBindingPathMergingHash::new(INVALID),
                );
                self.vbpath_merging_hash_mut(new_hash)
                    .init_variable_binding_path_merging_hash(Some(&taken));
                *self.vbpath_merging_hash_mut(prev) = taken;
            } else {
                self.vbpath_merging_hash_mut(new_hash)
                    .init_variable_binding_path_merging_hash(None);
            }
            data_box.loc_var_binding_path_merging_hash = new_hash;
            data_box.use_var_binding_path_merging_hash = new_hash;
        }
        data_box.use_var_binding_path_merging_hash
    }

    /// Context-threaded port helper for
    /// `CProcessingDataBox::getRepresentativeVariableBindingPathSetHash(true)`.
    pub fn processing_data_box_representative_variable_binding_path_set_hash(
        &mut self,
        data_box: &mut super::databox::ProcessingDataBox,
        force_localisation: bool,
    ) -> RepresentativeVariableBindingPathSetHashId {
        if force_localisation && data_box.loc_rep_var_bind_path_set_hash.is_none() {
            let prev = data_box.use_rep_var_bind_path_set_hash;
            let new_hash = self.alloc_rep_var_bind_path_set_hash(
                RepresentativeVariableBindingPathSetHash::new(INVALID),
            );
            if prev.is_some() {
                let taken = std::mem::replace(
                    self.rep_var_bind_path_set_hash_mut(prev),
                    RepresentativeVariableBindingPathSetHash::new(INVALID),
                );
                self.rep_var_bind_path_set_hash_mut(new_hash)
                    .init_representative_variable_binding_path_set_hash(Some(&taken));
                *self.rep_var_bind_path_set_hash_mut(prev) = taken;
            } else {
                self.rep_var_bind_path_set_hash_mut(new_hash)
                    .init_representative_variable_binding_path_set_hash(None);
            }
            data_box.loc_rep_var_bind_path_set_hash = new_hash;
            data_box.use_rep_var_bind_path_set_hash = new_hash;
        }
        data_box.use_rep_var_bind_path_set_hash
    }

    /// Context-threaded port helper for
    /// `CProcessingDataBox::getRepresentativeVariableBindingPathHash(true)`.
    pub fn processing_data_box_representative_variable_binding_path_hash(
        &mut self,
        data_box: &mut super::databox::ProcessingDataBox,
        force_localisation: bool,
    ) -> RepresentativeVariableBindingPathHashId {
        if force_localisation && data_box.loc_rep_var_bind_path_hash.is_none() {
            let prev = data_box.use_rep_var_bind_path_hash;
            let new_hash = self
                .alloc_rep_var_bind_path_hash(RepresentativeVariableBindingPathHash::new(INVALID));
            if prev.is_some() {
                let taken = std::mem::replace(
                    self.rep_var_bind_path_hash_mut(prev),
                    RepresentativeVariableBindingPathHash::new(INVALID),
                );
                self.rep_var_bind_path_hash_mut(new_hash)
                    .init_representative_variable_binding_path_hash(Some(&taken));
                *self.rep_var_bind_path_hash_mut(prev) = taken;
            } else {
                self.rep_var_bind_path_hash_mut(new_hash)
                    .init_representative_variable_binding_path_hash(None);
            }
            data_box.loc_rep_var_bind_path_hash = new_hash;
            data_box.use_rep_var_bind_path_hash = new_hash;
        }
        data_box.use_rep_var_bind_path_hash
    }

    /// Context-threaded port helper for
    /// `CProcessingDataBox::getRepresentativeVariableBindingPathJoiningKeyHash(true)`.
    pub fn processing_data_box_representative_variable_binding_path_joining_key_hash(
        &mut self,
        data_box: &mut super::databox::ProcessingDataBox,
        force_localisation: bool,
    ) -> RepresentativeVariableBindingPathJoiningKeyHashId {
        if force_localisation && data_box.loc_rep_var_bind_path_joining_key_hash.is_none() {
            let prev = data_box.use_rep_var_bind_path_joining_key_hash;
            let new_hash = self.alloc_rep_var_bind_path_joining_key_hash(
                RepresentativeVariableBindingPathJoiningKeyHash::new(INVALID),
            );
            if prev.is_some() {
                let taken = std::mem::replace(
                    self.rep_var_bind_path_joining_key_hash_mut(prev),
                    RepresentativeVariableBindingPathJoiningKeyHash::new(INVALID),
                );
                self.rep_var_bind_path_joining_key_hash_mut(new_hash)
                    .init_representative_variable_binding_path_joining_key_hash(Some(&taken));
                *self.rep_var_bind_path_joining_key_hash_mut(prev) = taken;
            } else {
                self.rep_var_bind_path_joining_key_hash_mut(new_hash)
                    .init_representative_variable_binding_path_joining_key_hash(None);
            }
            data_box.loc_rep_var_bind_path_joining_key_hash = new_hash;
            data_box.use_rep_var_bind_path_joining_key_hash = new_hash;
        }
        data_box.use_rep_var_bind_path_joining_key_hash
    }

    /// Context-threaded port helper for
    /// `CProcessingDataBox::getRepresentativeJoiningHash(true)`.
    pub fn processing_data_box_representative_joining_hash(
        &mut self,
        data_box: &mut super::databox::ProcessingDataBox,
        force_localisation: bool,
    ) -> RepresentativeJoiningHashId {
        if force_localisation && data_box.loc_rep_joining_hash.is_none() {
            let prev = data_box.use_rep_joining_hash;
            let new_hash = self.alloc_rep_joining_hash(RepresentativeJoiningHash::new(INVALID));
            if prev.is_some() {
                let taken = std::mem::replace(
                    self.rep_joining_hash_mut(prev),
                    RepresentativeJoiningHash::new(INVALID),
                );
                self.rep_joining_hash_mut(new_hash)
                    .init_representative_joining_hash(Some(&taken));
                *self.rep_joining_hash_mut(prev) = taken;
            } else {
                self.rep_joining_hash_mut(new_hash)
                    .init_representative_joining_hash(None);
            }
            data_box.loc_rep_joining_hash = new_hash;
            data_box.use_rep_joining_hash = new_hash;
        }
        data_box.use_rep_joining_hash
    }

    /// Context-threaded port helper for
    /// `CProcessingDataBox::getSignatureBlockingCandidateHash(true)`.
    pub fn processing_data_box_signature_blocking_candidate_hash(
        &mut self,
        data_box: &mut super::databox::ProcessingDataBox,
        create: bool,
    ) -> SigBlockCandHashId {
        if data_box.signature_blocking_candidate_hash.is_none() && create {
            let prev = data_box.prev_signature_blocking_candidate_hash;
            let new_hash =
                self.alloc_sig_block_cand_hash(SignatureBlockingCandidateHash::new(INVALID));
            if prev.is_some() {
                let taken = std::mem::replace(
                    self.sig_block_cand_hash_mut(prev),
                    SignatureBlockingCandidateHash::new(INVALID),
                );
                self.sig_block_cand_hash_mut(new_hash)
                    .init_signature_blocking_candidate_hash(Some(&taken));
                *self.sig_block_cand_hash_mut(prev) = taken;
            } else {
                self.sig_block_cand_hash_mut(new_hash)
                    .init_signature_blocking_candidate_hash(None);
            }
            data_box.signature_blocking_candidate_hash = new_hash;
            data_box.use_signature_blocking_candidate_hash = new_hash;
        }
        data_box.use_signature_blocking_candidate_hash
    }

    /// Context-threaded port helper for
    /// `CProcessingDataBox::getSignatureNominalDelayingCandidateHash(true)`.
    pub fn processing_data_box_signature_nominal_delaying_candidate_hash(
        &mut self,
        data_box: &mut super::databox::ProcessingDataBox,
        create: bool,
    ) -> SigBlockCandHashId {
        if data_box.signature_nominal_delaying_candidate_hash.is_none() && create {
            let prev = data_box.prev_signature_nominal_delaying_candidate_hash;
            let new_hash =
                self.alloc_sig_block_cand_hash(SignatureBlockingCandidateHash::new(INVALID));
            if prev.is_some() {
                let taken = std::mem::replace(
                    self.sig_block_cand_hash_mut(prev),
                    SignatureBlockingCandidateHash::new(INVALID),
                );
                self.sig_block_cand_hash_mut(new_hash)
                    .init_signature_blocking_candidate_hash(Some(&taken));
                *self.sig_block_cand_hash_mut(prev) = taken;
            } else {
                self.sig_block_cand_hash_mut(new_hash)
                    .init_signature_blocking_candidate_hash(None);
            }
            data_box.signature_nominal_delaying_candidate_hash = new_hash;
            data_box.use_signature_nominal_delaying_candidate_hash = new_hash;
        }
        data_box.use_signature_nominal_delaying_candidate_hash
    }

    /// Context-threaded port helper for
    /// `CProcessingDataBox::getBlockingIndividualNodeCandidateHash(true)`.
    pub fn processing_data_box_blocking_individual_node_candidate_hash(
        &mut self,
        data_box: &mut super::databox::ProcessingDataBox,
        create: bool,
    ) -> BlockingIndividualNodeCandidateHashId {
        if data_box.blocking_indi_node_candidate_hash.is_none() && create {
            let prev = data_box.prev_blocking_indi_node_candidate_hash;
            let new_hash = self.alloc_blocking_indi_node_cand_hash(
                BlockingIndividualNodeCandidateHash::new(INVALID),
            );
            if prev.is_some() {
                let taken = std::mem::replace(
                    self.blocking_indi_node_cand_hash_mut(prev),
                    BlockingIndividualNodeCandidateHash::new(INVALID),
                );
                self.blocking_indi_node_cand_hash_mut(new_hash)
                    .init_blocking_individual_node_candidate_hash(Some(&taken));
                *self.blocking_indi_node_cand_hash_mut(prev) = taken;
            } else {
                self.blocking_indi_node_cand_hash_mut(new_hash)
                    .init_blocking_individual_node_candidate_hash(None);
            }
            data_box.blocking_indi_node_candidate_hash = new_hash;
            data_box.use_blocking_indi_node_candidate_hash = new_hash;
        }
        data_box.use_blocking_indi_node_candidate_hash
    }

    /// Context-threaded port helper for
    /// `CProcessingDataBox::getBlockingIndividualNodeLinkedCandidateHash(true)`.
    pub fn processing_data_box_blocking_individual_node_linked_candidate_hash(
        &mut self,
        data_box: &mut super::databox::ProcessingDataBox,
        create: bool,
    ) -> BlockingIndividualNodeLinkedCandidateHashId {
        if data_box.blocking_indi_node_linked_candidate_hash.is_none() && create {
            let prev = data_box.prev_blocking_indi_node_linked_candidate_hash;
            let new_hash = self.alloc_blocking_indi_node_linked_cand_hash(
                BlockingIndividualNodeLinkedCandidateHash::new(INVALID),
            );
            if prev.is_some() {
                let taken = std::mem::replace(
                    self.blocking_indi_node_linked_cand_hash_mut(prev),
                    BlockingIndividualNodeLinkedCandidateHash::new(INVALID),
                );
                self.blocking_indi_node_linked_cand_hash_mut(new_hash)
                    .init_blocking_individual_node_candidate_hash(Some(&taken));
                *self.blocking_indi_node_linked_cand_hash_mut(prev) = taken;
            } else {
                self.blocking_indi_node_linked_cand_hash_mut(new_hash)
                    .init_blocking_individual_node_candidate_hash(None);
            }
            data_box.blocking_indi_node_linked_candidate_hash = new_hash;
            data_box.use_blocking_indi_node_linked_candidate_hash = new_hash;
        }
        data_box.use_blocking_indi_node_linked_candidate_hash
    }

    /// Context-threaded port helper for
    /// `CProcessingDataBox::getNodeSwitchHistory(true)`.
    pub fn processing_data_box_node_switch_history(
        &mut self,
        data_box: &mut super::databox::ProcessingDataBox,
        create: bool,
    ) -> NodeSwitchHistoryId {
        if data_box.node_switch_history.is_none() && create {
            let history =
                self.alloc_node_switch_history_from_prev(data_box.prev_node_switch_history);
            data_box.node_switch_history = history;
            data_box.use_node_switch_history = history;
        }
        data_box.use_node_switch_history
    }

    /// Context-threaded port helper for
    /// `CProcessingDataBox::getBranchingTree(true)`.
    pub fn processing_data_box_branching_tree(
        &mut self,
        data_box: &mut super::databox::ProcessingDataBox,
        create: bool,
    ) -> BranchingTreeId {
        if data_box.branching_tree.is_none() && create {
            let tree = self.alloc_branching_tree_from_prev(data_box.prev_branching_tree);
            data_box.branching_tree = tree;
            data_box.use_branching_tree = tree;
        }
        data_box.use_branching_tree
    }

    // --- W4.5 saturation-layer per-test satellite trios ---
    arena_accessors!(
        con_sat_descs,
        ConceptSaturationDescriptor,
        ConceptSaturationDescriptorId,
        con_sat_desc,
        con_sat_desc_mut,
        alloc_con_sat_desc
    );
    /// Port-facing saturation concept descriptor arena size.
    #[inline]
    pub fn con_sat_desc_count(&self) -> usize {
        self.con_sat_descs.len()
    }

    /// Diagnostic arena sizes for exact KM/Konclude saturation comparisons.
    #[inline]
    pub fn con_sat_proc_linker_count(&self) -> usize {
        self.con_sat_proc_linkers.len()
    }

    #[inline]
    pub fn backward_sat_prop_link_count(&self) -> usize {
        self.backward_sat_prop_links.len()
    }

    #[inline]
    pub fn backward_sat_prop_reapply_desc_count(&self) -> usize {
        self.backward_sat_prop_reapply_descs.len()
    }

    #[inline]
    pub fn role_backward_sat_prop_hash_count(&self) -> usize {
        self.role_backward_sat_prop_hashes.len()
    }

    #[inline]
    pub fn imp_reapply_con_sat_desc_count(&self) -> usize {
        self.imp_reapply_con_sat_descs.len()
    }

    /// Logical main/additional label entries.  Additional hashes can be shared,
    /// so the second value is intentionally a logical count rather than a byte
    /// estimate; it exposes copy-shape divergence without walking heap internals.
    pub fn reapply_con_sat_label_entry_counts(&self) -> (usize, usize) {
        self.reapply_con_sat_label_sets
            .iter()
            .fold((0, 0), |(main, additional), label| {
                (
                    main + label.concept_des_dep_hash.len(),
                    additional
                        + if label.has_additional_concept_des_dep_hash {
                            label.additional_concept_des_dep_hash.len()
                        } else {
                            0
                        },
                )
            })
    }

    /// Move the SATURATION-side arena state out of `other` into `self` (swap).
    ///
    /// KONCLUDE-PORT-NOTE[api]: in Konclude the approximation-saturation task
    /// stays alive for the whole (pre)computation and the completion tasks
    /// dereference raw pointers into its memory (via the concept↔saturation
    /// reference linkings). The port keeps saturation nodes in the SAME
    /// `ProcessContext` id space as the completion probes, so a probe-env
    /// reset (`bridge::reset_probe_env`) must carry the saturation arenas
    /// over — this method is that carry. The completion probes only READ
    /// these arenas (the saturation drive is the sole writer), so moving
    /// them across resets reproduces Konclude's stable-pointer semantics.
    ///
    /// `indi_sat_block_datas` (the COMPLETION node's saturation-blocking
    /// satellite) is deliberately NOT moved: it is per-probe search state.
    pub fn adopt_saturation_state_from(&mut self, other: &mut ProcessContext) {
        use std::mem::swap;
        swap(&mut self.sat_nodes, &mut other.sat_nodes);
        swap(
            &mut self.sat_nominal_handling_datas,
            &mut other.sat_nominal_handling_datas,
        );
        swap(
            &mut self.sat_succ_ext_ind_node_proc_queues,
            &mut other.sat_succ_ext_ind_node_proc_queues,
        );
        swap(
            &mut self.sat_critical_ind_node_proc_queues,
            &mut other.sat_critical_ind_node_proc_queues,
        );
        swap(
            &mut self.sat_critical_ind_node_con_test_sets,
            &mut other.sat_critical_ind_node_con_test_sets,
        );
        swap(
            &mut self.critical_sat_concept_queues,
            &mut other.critical_sat_concept_queues,
        );
        swap(
            &mut self.critical_sat_concept_type_queues,
            &mut other.critical_sat_concept_type_queues,
        );
        swap(
            &mut self.sat_influenced_nominal_sets,
            &mut other.sat_influenced_nominal_sets,
        );
        swap(
            &mut self.sat_nominal_dependent_node_hashes,
            &mut other.sat_nominal_dependent_node_hashes,
        );
        swap(
            &mut self.sat_nominal_dependent_node_datas,
            &mut other.sat_nominal_dependent_node_datas,
        );
        swap(&mut self.con_sat_descs, &mut other.con_sat_descs);
        swap(
            &mut self.con_sat_proc_linkers,
            &mut other.con_sat_proc_linkers,
        );
        swap(
            &mut self.role_sat_proc_linkers,
            &mut other.role_sat_proc_linkers,
        );
        swap(
            &mut self.backward_sat_prop_links,
            &mut other.backward_sat_prop_links,
        );
        swap(
            &mut self.backward_sat_prop_reapply_descs,
            &mut other.backward_sat_prop_reapply_descs,
        );
        swap(
            &mut self.role_backward_sat_prop_hashes,
            &mut other.role_backward_sat_prop_hashes,
        );
        swap(&mut self.sat_succ_datas, &mut other.sat_succ_datas);
        swap(&mut self.sat_succ_ext_datas, &mut other.sat_succ_ext_datas);
        swap(
            &mut self.indi_sat_succ_link_data_linkers,
            &mut other.indi_sat_succ_link_data_linkers,
        );
        swap(
            &mut self.linked_role_sat_succ_datas,
            &mut other.linked_role_sat_succ_datas,
        );
        swap(
            &mut self.linked_role_sat_succ_hashes,
            &mut other.linked_role_sat_succ_hashes,
        );
        swap(
            &mut self.indi_sat_node_ext_datas,
            &mut other.indi_sat_node_ext_datas,
        );
        swap(
            &mut self.sat_indi_node_succ_ext_datas,
            &mut other.sat_indi_node_succ_ext_datas,
        );
        swap(
            &mut self.sat_indi_node_all_concept_ext_datas,
            &mut other.sat_indi_node_all_concept_ext_datas,
        );
        swap(
            &mut self.sat_linked_succ_indi_all_concept_ext_datas,
            &mut other.sat_linked_succ_indi_all_concept_ext_datas,
        );
        swap(
            &mut self.sat_successor_all_concept_ext_datas,
            &mut other.sat_successor_all_concept_ext_datas,
        );
        swap(
            &mut self.sat_indi_node_ext_resolve_datas,
            &mut other.sat_indi_node_ext_resolve_datas,
        );
        swap(
            &mut self.sat_indi_node_ext_resolve_hashes,
            &mut other.sat_indi_node_ext_resolve_hashes,
        );
        swap(
            &mut self.sat_concept_extension_maps,
            &mut other.sat_concept_extension_maps,
        );
        swap(
            &mut self.sat_successor_concept_extension_maps,
            &mut other.sat_successor_concept_extension_maps,
        );
        swap(
            &mut self.sat_indi_node_functional_concept_ext_datas,
            &mut other.sat_indi_node_functional_concept_ext_datas,
        );
        swap(
            &mut self.sat_successor_functional_concept_ext_datas,
            &mut other.sat_successor_functional_concept_ext_datas,
        );
        swap(
            &mut self.sat_disjunct_common_concept_extraction_datas,
            &mut other.sat_disjunct_common_concept_extraction_datas,
        );
        swap(
            &mut self.sat_disjunct_extraction_linkers,
            &mut other.sat_disjunct_extraction_linkers,
        );
        swap(
            &mut self.sat_atmost_successor_merging_datas,
            &mut other.sat_atmost_successor_merging_datas,
        );
        swap(
            &mut self.sat_atmost_successor_merging_hashes,
            &mut other.sat_atmost_successor_merging_hashes,
        );
        swap(
            &mut self.sat_indi_node_datatype_datas,
            &mut other.sat_indi_node_datatype_datas,
        );
        swap(
            &mut self.sat_succ_role_assertion_linkers,
            &mut other.sat_succ_role_assertion_linkers,
        );
        swap(
            &mut self.reapply_con_sat_label_sets,
            &mut other.reapply_con_sat_label_sets,
        );
        swap(
            &mut self.imp_reapply_con_sat_descs,
            &mut other.imp_reapply_con_sat_descs,
        );
        swap(
            &mut self.sat_modified_process_update_linkers,
            &mut other.sat_modified_process_update_linkers,
        );
        swap(
            &mut self.indi_sat_process_node_linkers,
            &mut other.indi_sat_process_node_linkers,
        );
        swap(
            &mut self.extended_con_ref_linking_datas,
            &mut other.extended_con_ref_linking_datas,
        );
    }

    arena_accessors!(
        con_sat_proc_linkers,
        ConceptSaturationProcessLinker,
        ConceptSaturationProcessLinkerId,
        con_sat_proc_linker,
        con_sat_proc_linker_mut,
        alloc_con_sat_proc_linker
    );
    arena_accessors!(
        imp_reapply_con_sat_descs,
        ImplicationReapplyConceptSaturationDescriptor,
        ImplicationReapplyConceptSaturationDescriptorId,
        imp_reapply_con_sat_desc,
        imp_reapply_con_sat_desc_mut,
        alloc_imp_reapply_con_sat_desc
    );
    arena_accessors!(
        sat_modified_process_update_linkers,
        SaturationModifiedProcessUpdateLinker,
        SaturationModifiedProcessUpdateLinkerId,
        sat_modified_process_update_linker,
        sat_modified_process_update_linker_mut,
        alloc_sat_modified_process_update_linker
    );

    /// Port of `CConceptSaturationProcessLinker::append(oldHead)` for arena ids.
    pub fn append_concept_saturation_process_linker_chain(
        &mut self,
        head: ConceptSaturationProcessLinkerId,
        old_head: ConceptSaturationProcessLinkerId,
    ) -> ConceptSaturationProcessLinkerId {
        if head.is_none() {
            return old_head;
        }
        let mut tail = head;
        while self.con_sat_proc_linker(tail).next.is_some() {
            tail = self.con_sat_proc_linker(tail).next;
        }
        self.con_sat_proc_linker_mut(tail).next = old_head;
        head
    }

    /// Port of `CConceptSaturationDescriptor::append(oldHead)` for arena ids.
    pub fn append_concept_saturation_descriptor_chain(
        &mut self,
        head: ConceptSaturationDescriptorId,
        old_head: ConceptSaturationDescriptorId,
    ) -> ConceptSaturationDescriptorId {
        if head.is_none() {
            return old_head;
        }
        let mut tail = head;
        while self.con_sat_desc(tail).next.is_some() {
            tail = self.con_sat_desc(tail).next;
        }
        self.con_sat_desc_mut(tail).next = old_head;
        head
    }

    /// Port of `CImplicationReapplyConceptSaturationDescriptor::append(oldHead)`.
    pub fn append_implication_reapply_concept_saturation_descriptor_chain(
        &mut self,
        head: ImplicationReapplyConceptSaturationDescriptorId,
        old_head: ImplicationReapplyConceptSaturationDescriptorId,
    ) -> ImplicationReapplyConceptSaturationDescriptorId {
        if head.is_none() {
            return old_head;
        }
        let mut tail = head;
        while self.imp_reapply_con_sat_desc(tail).next.is_some() {
            tail = self.imp_reapply_con_sat_desc(tail).next;
        }
        self.imp_reapply_con_sat_desc_mut(tail).next = old_head;
        head
    }

    /// Port of `CSaturationModifiedProcessUpdateLinker::append(oldHead)`.
    pub fn append_saturation_modified_process_update_linker_chain(
        &mut self,
        head: SaturationModifiedProcessUpdateLinkerId,
        old_head: SaturationModifiedProcessUpdateLinkerId,
    ) -> SaturationModifiedProcessUpdateLinkerId {
        if head.is_none() {
            return old_head;
        }
        let mut tail = head;
        while self.sat_modified_process_update_linker(tail).next.is_some() {
            tail = self.sat_modified_process_update_linker(tail).next;
        }
        self.sat_modified_process_update_linker_mut(tail).next = old_head;
        head
    }

    /// Context-threaded port of
    /// `CReapplyConceptSaturationLabelSet::addModifiedUpdateLinker`.
    pub fn reapply_con_sat_label_set_add_modified_update_linker(
        &mut self,
        label_set: ReapplyConceptSaturationLabelSetId,
        mod_update_linker: SaturationModifiedProcessUpdateLinkerId,
    ) -> ReapplyConceptSaturationLabelSetId {
        if label_set.is_none() || mod_update_linker.is_none() {
            return label_set;
        }
        let old_head = self
            .reapply_con_sat_label_set(label_set)
            .get_modified_update_linker();
        let new_head = self
            .append_saturation_modified_process_update_linker_chain(mod_update_linker, old_head);
        self.reapply_con_sat_label_set_mut(label_set)
            .set_modified_update_linker(new_head);
        label_set
    }

    /// Context-threaded port of
    /// `CReapplyConceptSaturationLabelSet::insertConceptReapplicationReturnTriggered`.
    /// KONCLUDE-PORT-NOTE[api-extension]: C++ hardcodes the triggered check to
    /// `mConSatDes && !mConSatDes->isNegated()` (positive presence) because
    /// Konclude's absorption only ever builds implication triggers that wait
    /// for POSITIVE concepts (the trigger linkers store the inverted `¬sub`
    /// polarity). The bridge's clause encoding (`implication()` in bridge.rs)
    /// also emits negative-presence triggers (non-negated linkers), for which
    /// the insert-side reapply match (`linker.negated != con_neg`) is already
    /// polarity-aware — so the wanted presence polarity is threaded through
    /// here as `wanted_negation`. For Konclude-shaped triggers callers pass
    /// `false` and the behaviour is identical to the C++.
    pub fn reapply_con_sat_label_set_insert_concept_reapplication_return_triggered(
        &mut self,
        label_set: ReapplyConceptSaturationLabelSetId,
        con_tag: Cint64,
        wanted_negation: bool,
        reapply_imp_reapply_con_sat_des: ImplicationReapplyConceptSaturationDescriptorId,
        con_sat_des: Option<&mut ConceptSaturationDescriptorId>,
    ) -> bool {
        let copy_from_additional = {
            let label_set_ref = self.reapply_con_sat_label_set(label_set);
            let main_missing = label_set_ref
                .concept_des_dep_hash
                .get(&con_tag)
                .map(|data| data.con_sat_des.is_none() && data.imp_reapply_con_sat_des.is_none())
                .unwrap_or(true);
            if main_missing && label_set_ref.has_additional_concept_des_dep_hash {
                label_set_ref
                    .additional_concept_des_dep_hash
                    .get(&con_tag)
                    .copied()
            } else {
                None
            }
        };

        let (old_head, direct_con_sat_des, had_reapply) = {
            let label_set_ref = self.reapply_con_sat_label_set_mut(label_set);
            let data = label_set_ref
                .concept_des_dep_hash
                .entry(con_tag)
                .or_insert_with(ConceptSaturationDescriptorReapplyData::new);
            if data.con_sat_des.is_none() && data.imp_reapply_con_sat_des.is_none() {
                if let Some(prev_data) = copy_from_additional {
                    if prev_data.con_sat_des.is_some() {
                        data.con_sat_des = prev_data.con_sat_des;
                    }
                    if prev_data.imp_reapply_con_sat_des.is_some() {
                        data.imp_reapply_con_sat_des = prev_data.imp_reapply_con_sat_des;
                    }
                }
            }
            let old_head = data.imp_reapply_con_sat_des;
            let direct_con_sat_des = data.con_sat_des;
            let had_reapply = old_head.is_some();
            (old_head, direct_con_sat_des, had_reapply)
        };
        let triggered = direct_con_sat_des.is_some()
            && self.con_sat_desc(direct_con_sat_des).get_negation() == wanted_negation;

        if !had_reapply {
            self.reapply_con_sat_label_set_mut(label_set).totel_count += 1;
        }
        if triggered {
            if let Some(con_sat_des) = con_sat_des {
                *con_sat_des = direct_con_sat_des;
            }
        }

        let new_head = self.append_implication_reapply_concept_saturation_descriptor_chain(
            reapply_imp_reapply_con_sat_des,
            old_head,
        );
        self.reapply_con_sat_label_set_mut(label_set)
            .concept_des_dep_hash
            .entry(con_tag)
            .or_insert_with(ConceptSaturationDescriptorReapplyData::new)
            .imp_reapply_con_sat_des = new_head;

        triggered
    }

    /// Context-threaded port of
    /// `CReapplyConceptSaturationLabelSet::insertConceptReturnClashed`.
    pub fn reapply_con_sat_label_set_insert_concept_return_clashed(
        &mut self,
        label_set: ReapplyConceptSaturationLabelSetId,
        con_sat_des: ConceptSaturationDescriptorId,
        con_tag: Cint64,
        new_insertion: Option<&mut bool>,
        imp_reapply_con_sat_des: Option<&mut ImplicationReapplyConceptSaturationDescriptorId>,
    ) -> bool {
        let copy_from_additional = {
            let label_set_ref = self.reapply_con_sat_label_set(label_set);
            let main_missing = label_set_ref
                .concept_des_dep_hash
                .get(&con_tag)
                .map(|data| data.con_sat_des.is_none() && data.imp_reapply_con_sat_des.is_none())
                .unwrap_or(true);
            if main_missing && label_set_ref.has_additional_concept_des_dep_hash {
                label_set_ref
                    .additional_concept_des_dep_hash
                    .get(&con_tag)
                    .copied()
            } else {
                None
            }
        };

        let new_negation = self.con_sat_desc(con_sat_des).get_negation();
        let (inserted, existing_con_sat_des, old_head, imp_head) = {
            let label_set_ref = self.reapply_con_sat_label_set_mut(label_set);
            let data = label_set_ref
                .concept_des_dep_hash
                .entry(con_tag)
                .or_insert_with(ConceptSaturationDescriptorReapplyData::new);
            if data.con_sat_des.is_none() && data.imp_reapply_con_sat_des.is_none() {
                if let Some(prev_data) = copy_from_additional {
                    if prev_data.con_sat_des.is_some() {
                        data.con_sat_des = prev_data.con_sat_des;
                    }
                    if prev_data.imp_reapply_con_sat_des.is_some() {
                        data.imp_reapply_con_sat_des = prev_data.imp_reapply_con_sat_des;
                    }
                }
            }
            if data.con_sat_des.is_none() {
                let old_head = label_set_ref.concept_sat_des_linker;
                data.con_sat_des = con_sat_des;
                let imp_head = data.imp_reapply_con_sat_des;
                (
                    true,
                    ConceptSaturationDescriptorId::NONE,
                    old_head,
                    imp_head,
                )
            } else {
                (
                    false,
                    data.con_sat_des,
                    ConceptSaturationDescriptorId::NONE,
                    data.imp_reapply_con_sat_des,
                )
            }
        };
        let clashed = existing_con_sat_des.is_some()
            && self.con_sat_desc(existing_con_sat_des).get_negation() != new_negation;

        if inserted {
            if let Some(new_insertion) = new_insertion {
                *new_insertion = true;
            }
            let new_head = self.append_concept_saturation_descriptor_chain(con_sat_des, old_head);
            let label_set_ref = self.reapply_con_sat_label_set_mut(label_set);
            label_set_ref.concept_sat_des_linker = new_head;
            label_set_ref.concept_count += 1;
            label_set_ref.totel_count += 1;
        }
        if let Some(imp_reapply_con_sat_des) = imp_reapply_con_sat_des {
            *imp_reapply_con_sat_des = imp_head;
        }
        clashed
    }

    /// Context-threaded port of
    /// `CIndividualSaturationProcessNode::addClashedConceptSaturationDescriptorLinker`.
    pub fn sat_node_add_clashed_concept_saturation_descriptor_linker(
        &mut self,
        node: SatNodeId,
        clash_con_sat_des: ConceptSaturationDescriptorId,
    ) {
        let old_head = self.sat_node(node).clashed_con_sat_des_linker;
        let new_head = self.append_concept_saturation_descriptor_chain(clash_con_sat_des, old_head);
        self.sat_node_mut(node).clashed_con_sat_des_linker = new_head;
    }

    /// Context-threaded port of `CIndividualSaturationProcessNode::takeConceptSaturationProcessLinker`.
    pub fn sat_node_take_concept_saturation_process_linker(
        &mut self,
        node: SatNodeId,
    ) -> ConceptSaturationProcessLinkerId {
        let con_proc_linker = self.sat_node(node).get_concept_saturation_process_linker();
        if con_proc_linker.is_some() {
            let next = self.con_sat_proc_linker(con_proc_linker).get_next();
            self.sat_node_mut(node)
                .set_concept_saturation_process_linker(next);
        }
        con_proc_linker
    }

    /// Context-threaded port of `CIndividualSaturationProcessNode::addConceptSaturationProcessLinker`.
    pub fn sat_node_add_concept_saturation_process_linker(
        &mut self,
        node: SatNodeId,
        con_process_linker: ConceptSaturationProcessLinkerId,
    ) {
        let old_head = self.sat_node(node).get_concept_saturation_process_linker();
        let new_head =
            self.append_concept_saturation_process_linker_chain(con_process_linker, old_head);
        self.sat_node_mut(node)
            .set_concept_saturation_process_linker(new_head);
    }

    /// Context-threaded port of
    /// `CCriticalSaturationConceptQueue::takeNextCriticalConceptDescriptor`.
    pub fn critical_sat_concept_queue_take_next_critical_concept_descriptor(
        &mut self,
        queue: CriticalSaturationConceptQueueId,
    ) -> ConceptSaturationProcessLinkerId {
        let con_des_linker = self
            .critical_sat_concept_queue(queue)
            .get_critical_concept_descriptor_linker();
        if con_des_linker.is_some() {
            let next = self.con_sat_proc_linker(con_des_linker).get_next();
            self.critical_sat_concept_queue_mut(queue)
                .critical_con_des_linker = next;
            self.con_sat_proc_linker_mut(con_des_linker)
                .set_next(ConceptSaturationProcessLinkerId::NONE);
        }
        con_des_linker
    }

    /// Context-threaded port of
    /// `CCriticalSaturationConceptQueue::addCriticalConceptDescriptorLinker`.
    pub fn critical_sat_concept_queue_add_critical_concept_descriptor_linker(
        &mut self,
        queue: CriticalSaturationConceptQueueId,
        con_des_proc_linker: ConceptSaturationProcessLinkerId,
    ) -> CriticalSaturationConceptQueueId {
        let old_head = self
            .critical_sat_concept_queue(queue)
            .get_critical_concept_descriptor_linker();
        let new_head =
            self.append_concept_saturation_process_linker_chain(con_des_proc_linker, old_head);
        self.critical_sat_concept_queue_mut(queue)
            .critical_con_des_linker = new_head;
        queue
    }

    /// Context-threaded port of
    /// `CCriticalSaturationConceptTypeQueues::hasCriticalSaturationConceptsQueued`.
    pub fn critical_sat_concept_type_queues_has_critical_saturation_concepts_queued(
        &self,
        queues: CriticalSaturationConceptTypeQueuesId,
    ) -> bool {
        self.critical_sat_concept_type_queues(queues)
            .has_critical_saturation_concepts_queued(|queue| {
                self.critical_sat_concept_queue(queue)
                    .has_critical_concept_descriptor_linker()
            })
    }

    /// Context-threaded port of
    /// `CCriticalSaturationConceptTypeQueues::getCriticalSaturationConceptQueue`.
    pub fn critical_sat_concept_type_queues_get_critical_saturation_concept_queue(
        &mut self,
        queues: CriticalSaturationConceptTypeQueuesId,
        queue_type: CriticalSaturationConceptQueueType,
        create: bool,
    ) -> CriticalSaturationConceptQueueId {
        let index = queue_type.as_index();
        let queue = self.critical_sat_concept_type_queues(queues).queue_vec[index];
        if queue.is_none() && create {
            let indi_node = self.critical_sat_concept_type_queues(queues).indi_node;
            let queue =
                self.alloc_critical_sat_concept_queue(CriticalSaturationConceptQueue::new(INVALID));
            self.critical_sat_concept_queue_mut(queue)
                .init_critical_saturation_concept_queue(indi_node);
            self.critical_sat_concept_type_queues_mut(queues).queue_vec[index] = queue;
            return queue;
        }
        queue
    }

    arena_accessors!(
        role_sat_proc_linkers,
        RoleSaturationProcessLinker,
        RoleSaturationProcessLinkerId,
        role_sat_proc_linker,
        role_sat_proc_linker_mut,
        alloc_role_sat_proc_linker
    );
    arena_accessors!(
        backward_sat_prop_links,
        BackwardSaturationPropagationLink,
        BackwardSaturationPropagationLinkId,
        backward_sat_prop_link,
        backward_sat_prop_link_mut,
        alloc_backward_sat_prop_link
    );

    /// Port of `CBackwardSaturationPropagationLink::append(oldHead)` for arena ids.
    pub fn append_backward_saturation_propagation_link_chain(
        &mut self,
        head: BackwardSaturationPropagationLinkId,
        old_head: BackwardSaturationPropagationLinkId,
    ) -> BackwardSaturationPropagationLinkId {
        if head.is_none() {
            return old_head;
        }
        let mut tail = head;
        while self.backward_sat_prop_link(tail).next.is_some() {
            tail = self.backward_sat_prop_link(tail).next;
        }
        self.backward_sat_prop_link_mut(tail).next = old_head;
        head
    }

    arena_accessors!(
        backward_sat_prop_reapply_descs,
        BackwardSaturationPropagationReapplyDescriptor,
        BackwardSaturationPropagationReapplyDescriptorId,
        backward_sat_prop_reapply_desc,
        backward_sat_prop_reapply_desc_mut,
        alloc_backward_sat_prop_reapply_desc
    );
    arena_accessors!(
        role_backward_sat_prop_hashes,
        RoleBackwardSaturationPropagationHash,
        RoleBackwardSaturationPropagationHashId,
        role_backward_sat_prop_hash,
        role_backward_sat_prop_hash_mut,
        alloc_role_backward_sat_prop_hash
    );

    /// Context-threaded port of
    /// `CIndividualSaturationProcessNode::getRoleBackwardPropagationHash`.
    pub fn sat_node_role_backward_propagation_hash(
        &mut self,
        node: SatNodeId,
        create: bool,
    ) -> RoleBackwardSaturationPropagationHashId {
        if node.is_none() {
            return RoleBackwardSaturationPropagationHashId::NONE;
        }
        if self.sat_node(node).role_back_prop_hash.is_none() && create {
            let hash = self.alloc_role_backward_sat_prop_hash(
                RoleBackwardSaturationPropagationHash::new(INVALID),
            );
            self.role_backward_sat_prop_hash_mut(hash)
                .init_role_backward_saturation_propagation_hash();
            self.sat_node_mut(node).role_back_prop_hash = hash;
        }
        self.sat_node(node).role_back_prop_hash
    }

    /// The mutation core of Konclude's
    /// `CRoleBackwardSaturationPropagationHash::addBackwardPropagationLink`.
    ///
    /// Konclude obtains one mutable `mRoleBackPropDataHash[role]` bucket, tests
    /// the current head, prepends the link, and reads the reapply linker from
    /// that same bucket. Keeping this operation on `ProcessContext` lets Rust
    /// borrow the link and hash arenas as disjoint fields and perform the same
    /// update with one role-map lookup.
    pub fn role_backward_saturation_propagation_hash_install_link(
        &mut self,
        hash: RoleBackwardSaturationPropagationHashId,
        role: RoleId,
        link: BackwardSaturationPropagationLinkId,
    ) -> (bool, BackwardSaturationPropagationReapplyDescriptorId) {
        let link_source = self
            .backward_sat_prop_links
            .get(link)
            .get_source_individual();
        let (backward_links, role_hashes) = (
            &mut self.backward_sat_prop_links,
            &mut self.role_backward_sat_prop_hashes,
        );
        let data = role_hashes
            .get_mut_journaled(hash)
            .role_back_prop_data_hash
            .entry(role)
            .or_insert_with(RoleBackwardSaturationPropagationHashData::new);
        let old_head = data.link_linker;
        let install_link = old_head.is_none()
            || backward_links.get(old_head).get_source_individual() != link_source;
        if install_link {
            backward_links.get_mut_journaled(link).set_next(old_head);
            data.link_linker = link;
        }
        (install_link, data.reapply_linker)
    }

    /// Port of the predecessor-merging flag tail of
    /// `installBackwardPropagationLink`. This deliberately runs after pending
    /// backward concepts have been reapplied, matching the C++ operation order.
    pub fn role_backward_saturation_propagation_hash_queue_predecessor_merging(
        &mut self,
        hash: RoleBackwardSaturationPropagationHashId,
        role: RoleId,
        queue_functional_processing: bool,
    ) -> bool {
        let data = self
            .role_backward_sat_prop_hashes
            .get_mut_journaled(hash)
            .role_back_prop_data_hash
            .entry(role)
            .or_insert_with(RoleBackwardSaturationPropagationHashData::new);
        if data.role_predecessor_merging_queuing_required
            && queue_functional_processing
            && !data.role_predecessor_merging_processing_queued
        {
            data.role_predecessor_merging_processing_queued = true;
            true
        } else {
            false
        }
    }

    /// Port helper for `CRoleBackwardSaturationPropagationHash::addBackwardPropagationLink`.
    pub fn sat_node_add_backward_propagation_link(
        &mut self,
        node: SatNodeId,
        role: RoleId,
        source_individual: SatNodeId,
    ) -> BackwardSaturationPropagationReapplyDescriptorId {
        let hash = self.sat_node_role_backward_propagation_hash(node, true);
        if hash.is_none() {
            return BackwardSaturationPropagationReapplyDescriptorId::NONE;
        }

        let (old_head, reapply_linker) = {
            let data = self
                .role_backward_sat_prop_hash(hash)
                .role_back_prop_data_hash
                .get(&role);
            let old_head = data
                .map(|data| data.link_linker)
                .unwrap_or(BackwardSaturationPropagationLinkId::NONE);
            let reapply_linker = data
                .map(|data| data.reapply_linker)
                .unwrap_or(BackwardSaturationPropagationReapplyDescriptorId::NONE);
            (old_head, reapply_linker)
        };

        if old_head.is_some()
            && self
                .backward_sat_prop_link(old_head)
                .get_source_individual()
                == source_individual
        {
            return BackwardSaturationPropagationReapplyDescriptorId::NONE;
        }

        let mut link = BackwardSaturationPropagationLink::new();
        link.init_backward_propagation_link(source_individual, role)
            .set_next(old_head);
        let link = self.alloc_backward_sat_prop_link(link);
        self.role_backward_sat_prop_hash_mut(hash)
            .role_back_prop_data_hash
            .entry(role)
            .or_insert_with(RoleBackwardSaturationPropagationHashData::new)
            .link_linker = link;
        reapply_linker
    }

    /// Port helper for `CRoleBackwardSaturationPropagationHash::addSelfConnectedBackwardPropagationLink`.
    pub fn sat_node_add_self_connected_backward_propagation_link(
        &mut self,
        node: SatNodeId,
        role: RoleId,
        source_individual: SatNodeId,
    ) -> BackwardSaturationPropagationReapplyDescriptorId {
        let hash = self.sat_node_role_backward_propagation_hash(node, true);
        if hash.is_none() {
            return BackwardSaturationPropagationReapplyDescriptorId::NONE;
        }
        self.role_backward_sat_prop_hash_mut(hash).self_connected = true;
        let reapply = self.sat_node_add_backward_propagation_link(node, role, source_individual);
        self.role_backward_sat_prop_hash_mut(hash)
            .role_back_prop_data_hash
            .entry(role)
            .or_insert_with(RoleBackwardSaturationPropagationHashData::new)
            .self_connected = true;
        reapply
    }

    /// Port of `CRoleBackwardSaturationPropagationHash::copyRoleBackwardSaturationPropagationHash`.
    pub fn copy_role_backward_saturation_propagation_hash(
        &mut self,
        target_hash: RoleBackwardSaturationPropagationHashId,
        source_hash: RoleBackwardSaturationPropagationHashId,
        new_indi_node: SatNodeId,
    ) -> RoleBackwardSaturationPropagationHashId {
        if target_hash.is_none() || source_hash.is_none() {
            return target_hash;
        }

        let (self_connected, copied_data): (
            bool,
            Vec<(RoleId, RoleBackwardSaturationPropagationHashData)>,
        ) = {
            let source = self.role_backward_sat_prop_hash(source_hash);
            (
                source.self_connected,
                source
                    .role_back_prop_data_hash
                    .iter()
                    .map(|(role, data)| {
                        (
                            *role,
                            RoleBackwardSaturationPropagationHashData::copy_without_links(data),
                        )
                    })
                    .collect(),
            )
        };

        {
            let target = self.role_backward_sat_prop_hash_mut(target_hash);
            target.role_back_prop_data_hash = copied_data.into_iter().collect();
            target.self_connected = self_connected;
        }

        if self_connected {
            let self_connected_roles: Vec<RoleId> = self
                .role_backward_sat_prop_hash(target_hash)
                .role_back_prop_data_hash
                .iter()
                .filter_map(|(role, data)| data.self_connected.then_some(*role))
                .collect();

            for role in self_connected_roles {
                let old_head = self
                    .role_backward_sat_prop_hash(target_hash)
                    .role_back_prop_data_hash
                    .get(&role)
                    .map(|data| data.link_linker)
                    .unwrap_or(BackwardSaturationPropagationLinkId::NONE);
                let mut self_back_link = BackwardSaturationPropagationLink::new();
                self_back_link
                    .init_backward_propagation_link(new_indi_node, role)
                    .set_next(old_head);
                let self_back_link = self.alloc_backward_sat_prop_link(self_back_link);
                self.role_backward_sat_prop_hash_mut(target_hash)
                    .role_back_prop_data_hash
                    .entry(role)
                    .or_insert_with(RoleBackwardSaturationPropagationHashData::new)
                    .link_linker = self_back_link;
            }
        }

        target_hash
    }

    /// Arena-threaded port of
    /// `CIndividualSaturationProcessNode::initCopingIndividualSaturationProcessNode`.
    pub fn sat_node_init_coping_individual_saturation_process_node(
        &mut self,
        target_node: SatNodeId,
        source_node: SatNodeId,
        try_flat_label_copy: bool,
    ) {
        if target_node.is_none() || source_node.is_none() {
            return;
        }

        let source_role_back_prop_hash = self.sat_node(source_node).role_back_prop_hash;
        if source_role_back_prop_hash.is_some() {
            let target_role_back_prop_hash =
                self.sat_node_role_backward_propagation_hash(target_node, true);
            self.copy_role_backward_saturation_propagation_hash(
                target_role_back_prop_hash,
                source_role_back_prop_hash,
                target_node,
            );
        }

        if self
            .sat_node(source_node)
            .reapply_con_sat_label_set
            .is_some()
        {
            let target_label_set =
                self.sat_node_reapply_concept_saturation_label_set(target_node, true);
            let source_label_set = self.sat_node(source_node).reapply_con_sat_label_set;
            self.copy_reapply_concept_saturation_label_set(
                target_label_set,
                source_label_set,
                try_flat_label_copy,
            );
        }

        let source_successor_connected_nominal_set =
            self.sat_node_successor_connected_nominal_set_existing(source_node);
        if source_successor_connected_nominal_set.is_some() {
            let copied_set = self
                .nominal_conn_set(source_successor_connected_nominal_set)
                .clone();
            let target_successor_connected_nominal_set =
                self.sat_node_successor_connected_nominal_set(target_node, true);
            if target_successor_connected_nominal_set.is_some() {
                self.nominal_conn_set_mut(target_successor_connected_nominal_set)
                    .copy_successor_connected_nominal_set(Some(&copied_set));
            }
        }

        let (source_integrated_nominal_indi, source_nominal_indi, source_data_value_applied) = {
            let source = self.sat_node(source_node);
            (
                source.integrated_nominal_indi,
                source.nominal_indi,
                source.data_value_applied,
            )
        };
        let target_nominal_indi = self.sat_node(target_node).nominal_indi;
        let target = self.sat_node_mut(target_node);
        target.integrated_nominal_indi = source_integrated_nominal_indi;
        if source_nominal_indi.is_some() {
            target.integrated_nominal_indi = source_nominal_indi;
        }
        if target_nominal_indi.is_some() {
            target.integrated_nominal_indi = target_nominal_indi;
        }
        target.data_value_applied = source_data_value_applied;

        let source_applied_datatype_data =
            self.sat_node_ext_applied_datatype_data(source_node, false);
        if source_applied_datatype_data.is_some() {
            let applied_data_literal = self
                .sat_indi_node_datatype_data(source_applied_datatype_data)
                .get_applied_data_literal();
            let applied_datatype = self
                .sat_indi_node_datatype_data(source_applied_datatype_data)
                .get_applied_datatype();
            let target_applied_datatype_data =
                self.sat_node_ext_applied_datatype_data(target_node, true);
            if target_applied_datatype_data.is_some() {
                self.sat_indi_node_datatype_data_mut(target_applied_datatype_data)
                    .set_applied_data_literal(applied_data_literal)
                    .set_applied_datatype(applied_datatype);
            }
        }

        self.sat_node_mut(source_node)
            .add_copy_depending_individual_node_linker(NegLink {
                target: target_node,
                negated: true,
            });
    }

    /// Arena-threaded port of
    /// `CReapplyConceptSaturationLabelSet::copyReapplyConceptSaturationLabelSet`.
    pub fn copy_reapply_concept_saturation_label_set(
        &mut self,
        target_label_set: ReapplyConceptSaturationLabelSetId,
        source_label_set: ReapplyConceptSaturationLabelSetId,
        try_flat_label_copy: bool,
    ) -> ReapplyConceptSaturationLabelSetId {
        if target_label_set.is_none() || source_label_set.is_none() {
            return target_label_set;
        }

        let (
            source_concept_count,
            source_total_count,
            source_concept_flags,
            source_main_len,
            source_has_additional,
            source_additional_len,
        ) = {
            let source = self.reapply_con_sat_label_set(source_label_set);
            (
                source.concept_count,
                source.totel_count,
                source.concept_flags,
                source.concept_des_dep_hash.len(),
                source.has_additional_concept_des_dep_hash,
                source.additional_concept_des_dep_hash.len(),
            )
        };

        if source_main_len >= ReapplyConceptSaturationLabelSet::ADDITIONALCOPYSIZE as usize
            || (try_flat_label_copy && source_main_len > 0)
        {
            let (new_additional, new_main) = {
                let source = self.reapply_con_sat_label_set(source_label_set);
                if source_has_additional {
                    let mut tmp = if source_additional_len > source_main_len {
                        source.additional_concept_des_dep_hash.as_ref().clone()
                    } else {
                        source.concept_des_dep_hash.clone()
                    };
                    let merge_from = if source_additional_len > source_main_len {
                        &source.concept_des_dep_hash
                    } else {
                        &source.additional_concept_des_dep_hash
                    };
                    for (con_tag, data) in merge_from {
                        let entry = tmp.entry(*con_tag).or_default();
                        if data.con_sat_des.is_some() {
                            entry.con_sat_des = data.con_sat_des;
                        }
                        if data.imp_reapply_con_sat_des.is_some() {
                            entry.imp_reapply_con_sat_des = data.imp_reapply_con_sat_des;
                        }
                    }
                    (std::sync::Arc::new(tmp), Default::default())
                } else {
                    (
                        std::sync::Arc::new(source.concept_des_dep_hash.clone()),
                        Default::default(),
                    )
                }
            };
            let source = self.reapply_con_sat_label_set_mut(source_label_set);
            source.additional_concept_des_dep_hash = new_additional;
            source.has_additional_concept_des_dep_hash = true;
            source.concept_des_dep_hash = new_main;
        }

        let (
            source_main,
            source_additional,
            source_has_additional,
            source_concept_sat_des_linker,
            source_last_nominal_indep_con_sat_des,
        ) = {
            let source = self.reapply_con_sat_label_set(source_label_set);
            (
                source.concept_des_dep_hash.clone(),
                source.additional_concept_des_dep_hash.clone(),
                source.has_additional_concept_des_dep_hash,
                source.concept_sat_des_linker,
                source.last_nominal_indep_con_sat_des,
            )
        };

        let target = self.reapply_con_sat_label_set_mut(target_label_set);
        target.concept_count = source_concept_count;
        target.totel_count = source_total_count;
        target.concept_flags = source_concept_flags;
        target.concept_des_dep_hash = source_main;
        target.additional_concept_des_dep_hash = source_additional;
        target.has_additional_concept_des_dep_hash = source_has_additional;
        target.concept_sat_des_linker = source_concept_sat_des_linker;
        target.last_nominal_indep_con_sat_des = source_last_nominal_indep_con_sat_des;
        target_label_set
    }

    /// Collects all `CBackwardSaturationPropagationLink::getSourceIndividual`
    /// targets for the node's role-backward propagation hash.
    pub fn sat_node_role_backward_source_individuals(&self, node: SatNodeId) -> Vec<SatNodeId> {
        if node.is_none() {
            return Vec::new();
        }
        let hash = self.sat_node(node).role_back_prop_hash;
        if hash.is_none() {
            return Vec::new();
        }

        let mut out = Vec::new();
        for data in self
            .role_backward_sat_prop_hash(hash)
            .role_back_prop_data_hash
            .values()
        {
            let mut link = data.link_linker;
            while link.is_some() {
                let link_ref = self.backward_sat_prop_link(link);
                let source = link_ref.get_source_individual();
                if source.is_some() {
                    out.push(source);
                }
                link = link_ref.get_next();
            }
        }
        out
    }
    arena_accessors!(
        sat_succ_datas,
        SaturationSuccessorData,
        SaturationSuccessorDataId,
        sat_succ_data,
        sat_succ_data_mut,
        alloc_sat_succ_data
    );
    /// Port-facing saturation successor-data arena size.
    #[inline]
    pub fn sat_succ_data_count(&self) -> usize {
        self.sat_succ_datas.len()
    }
    arena_accessors!(
        sat_succ_ext_datas,
        SaturationSuccessorExtensionData,
        SaturationSuccessorExtensionDataId,
        sat_succ_ext_data,
        sat_succ_ext_data_mut,
        alloc_sat_succ_ext_data
    );
    /// Port-facing saturation successor-extension-data arena size.
    #[inline]
    pub fn sat_succ_ext_data_count(&self) -> usize {
        self.sat_succ_ext_datas.len()
    }
    arena_accessors!(
        indi_sat_succ_link_data_linkers,
        IndividualSaturationSuccessorLinkDataLinker,
        IndividualSaturationSuccessorLinkDataLinkerId,
        indi_sat_succ_link_data_linker,
        indi_sat_succ_link_data_linker_mut,
        alloc_indi_sat_succ_link_data_linker
    );
    /// Port-facing individual saturation successor-link-data linker arena size.
    #[inline]
    pub fn indi_sat_succ_link_data_linker_count(&self) -> usize {
        self.indi_sat_succ_link_data_linkers.len()
    }
    arena_accessors!(
        linked_role_sat_succ_datas,
        LinkedRoleSaturationSuccessorData,
        LinkedRoleSaturationSuccessorDataId,
        linked_role_sat_succ_data,
        linked_role_sat_succ_data_mut,
        alloc_linked_role_sat_succ_data
    );
    /// Port-facing linked-role saturation successor-data arena size.
    #[inline]
    pub fn linked_role_sat_succ_data_count(&self) -> usize {
        self.linked_role_sat_succ_datas.len()
    }
    arena_accessors!(
        linked_role_sat_succ_hashes,
        LinkedRoleSaturationSuccessorHash,
        LinkedRoleSaturationSuccessorHashId,
        linked_role_sat_succ_hash,
        linked_role_sat_succ_hash_mut,
        alloc_linked_role_sat_succ_hash
    );
    /// Port-facing linked-role saturation successor-hash arena size.
    #[inline]
    pub fn linked_role_sat_succ_hash_count(&self) -> usize {
        self.linked_role_sat_succ_hashes.len()
    }
    arena_accessors!(
        indi_sat_node_ext_datas,
        IndividualSaturationProcessNodeExtensionData,
        IndividualSaturationProcessNodeExtensionDataId,
        indi_sat_node_ext_data,
        indi_sat_node_ext_data_mut,
        alloc_indi_sat_node_ext_data
    );
    /// Port-facing saturation node extension-data arena size.
    #[inline]
    pub fn indi_sat_node_ext_data_count(&self) -> usize {
        self.indi_sat_node_ext_datas.len()
    }
    arena_accessors!(
        sat_indi_node_succ_ext_datas,
        SaturationIndividualNodeSuccessorExtensionData,
        SaturationIndividualNodeSuccessorExtensionDataId,
        sat_indi_node_succ_ext_data,
        sat_indi_node_succ_ext_data_mut,
        alloc_sat_indi_node_succ_ext_data
    );
    /// Port-facing saturation individual-node successor-extension-data arena size.
    #[inline]
    pub fn sat_indi_node_succ_ext_data_count(&self) -> usize {
        self.sat_indi_node_succ_ext_datas.len()
    }
    arena_accessors!(
        sat_indi_node_all_concept_ext_datas,
        SaturationIndividualNodeAllConceptsExtensionData,
        SaturationIndividualNodeAllConceptsExtensionDataId,
        sat_indi_node_all_concept_ext_data,
        sat_indi_node_all_concept_ext_data_mut,
        alloc_sat_indi_node_all_concept_ext_data
    );
    /// Port-facing saturation ALL concepts extension-data arena size.
    #[inline]
    pub fn sat_indi_node_all_concept_ext_data_count(&self) -> usize {
        self.sat_indi_node_all_concept_ext_datas.len()
    }
    arena_accessors!(
        sat_linked_succ_indi_all_concept_ext_datas,
        SaturationLinkedSuccessorIndividualAllConceptsExtensionData,
        SaturationLinkedSuccessorIndividualAllConceptsExtensionDataId,
        sat_linked_succ_indi_all_concept_ext_data,
        sat_linked_succ_indi_all_concept_ext_data_mut,
        alloc_sat_linked_succ_indi_all_concept_ext_data
    );
    #[inline]
    pub fn sat_linked_succ_indi_all_concept_ext_data_count(&self) -> usize {
        self.sat_linked_succ_indi_all_concept_ext_datas.len()
    }
    arena_accessors!(
        sat_successor_all_concept_ext_datas,
        SaturationSuccessorAllConceptExtensionData,
        SaturationSuccessorAllConceptExtensionDataId,
        sat_successor_all_concept_ext_data,
        sat_successor_all_concept_ext_data_mut,
        alloc_sat_successor_all_concept_ext_data
    );
    #[inline]
    pub fn sat_successor_all_concept_ext_data_count(&self) -> usize {
        self.sat_successor_all_concept_ext_datas.len()
    }
    arena_accessors!(
        sat_indi_node_ext_resolve_datas,
        SaturationIndividualNodeExtensionResolveData,
        SaturationIndividualNodeExtensionResolveDataId,
        sat_indi_node_ext_resolve_data,
        sat_indi_node_ext_resolve_data_mut,
        alloc_sat_indi_node_ext_resolve_data
    );
    #[inline]
    pub fn sat_indi_node_ext_resolve_data_count(&self) -> usize {
        self.sat_indi_node_ext_resolve_datas.len()
    }
    arena_accessors!(
        sat_indi_node_ext_resolve_hashes,
        SaturationIndividualNodeExtensionResolveHash,
        SaturationIndividualNodeExtensionResolveHashId,
        sat_indi_node_ext_resolve_hash,
        sat_indi_node_ext_resolve_hash_mut,
        alloc_sat_indi_node_ext_resolve_hash
    );
    #[inline]
    pub fn sat_indi_node_ext_resolve_hash_count(&self) -> usize {
        self.sat_indi_node_ext_resolve_hashes.len()
    }
    arena_accessors!(
        sat_concept_extension_maps,
        SaturationConceptExtensionMap,
        SaturationConceptExtensionMapId,
        sat_concept_extension_map,
        sat_concept_extension_map_mut,
        alloc_sat_concept_extension_map
    );
    #[inline]
    pub fn sat_concept_extension_map_count(&self) -> usize {
        self.sat_concept_extension_maps.len()
    }
    arena_accessors!(
        sat_successor_concept_extension_maps,
        SaturationSuccessorConceptExtensionMap,
        SaturationSuccessorConceptExtensionMapId,
        sat_successor_concept_extension_map,
        sat_successor_concept_extension_map_mut,
        alloc_sat_successor_concept_extension_map
    );
    #[inline]
    pub fn sat_successor_concept_extension_map_count(&self) -> usize {
        self.sat_successor_concept_extension_maps.len()
    }
    arena_accessors!(
        sat_indi_node_functional_concept_ext_datas,
        SaturationIndividualNodeFunctionalConceptsExtensionData,
        SaturationIndividualNodeFunctionalConceptsExtensionDataId,
        sat_indi_node_functional_concept_ext_data,
        sat_indi_node_functional_concept_ext_data_mut,
        alloc_sat_indi_node_functional_concept_ext_data
    );
    /// Port-facing saturation FUNCTIONAL concepts extension-data arena size.
    #[inline]
    pub fn sat_indi_node_functional_concept_ext_data_count(&self) -> usize {
        self.sat_indi_node_functional_concept_ext_datas.len()
    }
    arena_accessors!(
        sat_successor_functional_concept_ext_datas,
        SaturationSuccessorFunctionalConceptExtensionData,
        SaturationSuccessorFunctionalConceptExtensionDataId,
        sat_successor_functional_concept_ext_data,
        sat_successor_functional_concept_ext_data_mut,
        alloc_sat_successor_functional_concept_ext_data
    );
    /// Port-facing saturation successor FUNCTIONAL concept-extension data arena size.
    #[inline]
    pub fn sat_successor_functional_concept_ext_data_count(&self) -> usize {
        self.sat_successor_functional_concept_ext_datas.len()
    }
    arena_accessors!(
        sat_disjunct_common_concept_extraction_datas,
        SaturationDisjunctCommonConceptExtractionData,
        SaturationDisjunctCommonConceptExtractionDataId,
        sat_disjunct_common_concept_extraction_data,
        sat_disjunct_common_concept_extraction_data_mut,
        alloc_sat_disjunct_common_concept_extraction_data
    );
    /// Port-facing disjunct common-concept extraction-data arena size.
    #[inline]
    pub fn sat_disjunct_common_concept_extraction_data_count(&self) -> usize {
        self.sat_disjunct_common_concept_extraction_datas.len()
    }
    arena_accessors!(
        sat_disjunct_extraction_linkers,
        SaturationDisjunctExtractionLinker,
        SaturationDisjunctExtractionLinkerId,
        sat_disjunct_extraction_linker,
        sat_disjunct_extraction_linker_mut,
        alloc_sat_disjunct_extraction_linker
    );
    /// Port-facing disjunct extraction-linker arena size.
    #[inline]
    pub fn sat_disjunct_extraction_linker_count(&self) -> usize {
        self.sat_disjunct_extraction_linkers.len()
    }
    arena_accessors!(
        sat_atmost_successor_merging_datas,
        SaturationAtmostSuccessorMergingData,
        SaturationAtmostSuccessorMergingDataId,
        sat_atmost_successor_merging_data,
        sat_atmost_successor_merging_data_mut,
        alloc_sat_atmost_successor_merging_data
    );
    /// Port-facing ATMOST successor-merging-data arena size.
    #[inline]
    pub fn sat_atmost_successor_merging_data_count(&self) -> usize {
        self.sat_atmost_successor_merging_datas.len()
    }
    arena_accessors!(
        sat_atmost_successor_merging_hashes,
        SaturationAtmostSuccessorMergingHash,
        SaturationAtmostSuccessorMergingHashId,
        sat_atmost_successor_merging_hash,
        sat_atmost_successor_merging_hash_mut,
        alloc_sat_atmost_successor_merging_hash
    );
    /// Port-facing ATMOST successor-merging-hash arena size.
    #[inline]
    pub fn sat_atmost_successor_merging_hash_count(&self) -> usize {
        self.sat_atmost_successor_merging_hashes.len()
    }
    arena_accessors!(
        linked_data_value_assertion_datas,
        LinkedDataValueAssertionSaturationData,
        LinkedDataValueAssertionSaturationDataId,
        linked_data_value_assertion_data,
        linked_data_value_assertion_data_mut,
        alloc_linked_data_value_assertion_data
    );
    /// Port-facing linked data-value assertion-data arena size.
    #[inline]
    pub fn linked_data_value_assertion_data_count(&self) -> usize {
        self.linked_data_value_assertion_datas.len()
    }
    arena_accessors!(
        data_value_role_assertion_linkers,
        DataValueRoleAssertionLinker,
        DataValueRoleAssertionLinkerId,
        data_value_role_assertion_linker,
        data_value_role_assertion_linker_mut,
        alloc_data_value_role_assertion_linker
    );
    /// Port-facing data-value role-assertion linker arena size.
    #[inline]
    pub fn data_value_role_assertion_linker_count(&self) -> usize {
        self.data_value_role_assertion_linkers.len()
    }
    arena_accessors!(
        sat_indi_node_datatype_datas,
        SaturationIndividualNodeDatatypeData,
        SaturationIndividualNodeDatatypeDataId,
        sat_indi_node_datatype_data,
        sat_indi_node_datatype_data_mut,
        alloc_sat_indi_node_datatype_data
    );
    /// Port-facing saturation individual-node datatype-data arena size.
    #[inline]
    pub fn sat_indi_node_datatype_data_count(&self) -> usize {
        self.sat_indi_node_datatype_datas.len()
    }
    arena_accessors!(
        sat_succ_role_assertion_linkers,
        SaturationSuccessorRoleAssertionLinker,
        SaturationSuccessorRoleAssertionLinkerId,
        sat_succ_role_assertion_linker,
        sat_succ_role_assertion_linker_mut,
        alloc_sat_succ_role_assertion_linker
    );
    /// Port-facing saturation successor role-assertion linker arena size.
    #[inline]
    pub fn sat_succ_role_assertion_linker_count(&self) -> usize {
        self.sat_succ_role_assertion_linkers.len()
    }
    arena_accessors!(
        critical_pred_role_card_datas,
        CriticalPredecessorRoleCardinalityData,
        CriticalPredecessorRoleCardinalityDataId,
        critical_pred_role_card_data,
        critical_pred_role_card_data_mut,
        alloc_critical_pred_role_card_data
    );
    /// Port-facing critical predecessor role-cardinality data arena size.
    #[inline]
    pub fn critical_pred_role_card_data_count(&self) -> usize {
        self.critical_pred_role_card_datas.len()
    }
    arena_accessors!(
        critical_pred_role_card_hashes,
        CriticalPredecessorRoleCardinalityHash,
        CriticalPredecessorRoleCardinalityHashId,
        critical_pred_role_card_hash,
        critical_pred_role_card_hash_mut,
        alloc_critical_pred_role_card_hash
    );
    /// Port-facing critical predecessor role-cardinality hash arena size.
    #[inline]
    pub fn critical_pred_role_card_hash_count(&self) -> usize {
        self.critical_pred_role_card_hashes.len()
    }
    arena_accessors!(
        reapply_con_sat_label_sets,
        ReapplyConceptSaturationLabelSet,
        ReapplyConceptSaturationLabelSetId,
        reapply_con_sat_label_set,
        reapply_con_sat_label_set_mut,
        alloc_reapply_con_sat_label_set
    );
    /// Port-facing saturation concept label-set arena size.
    #[inline]
    pub fn reapply_con_sat_label_set_count(&self) -> usize {
        self.reapply_con_sat_label_sets.len()
    }
    arena_accessors!(
        indi_sat_process_node_linkers,
        IndividualSaturationProcessNodeLinker,
        IndividualSaturationProcessNodeLinkerId,
        indi_sat_process_node_linker,
        indi_sat_process_node_linker_mut,
        alloc_indi_sat_process_node_linker
    );
    /// Port-facing saturation process-node linker arena size.
    #[inline]
    pub fn indi_sat_process_node_linker_count(&self) -> usize {
        self.indi_sat_process_node_linkers.len()
    }

    /// Context-threaded port of `CIndividualSaturationProcessNode::getIndividualExtensionData`.
    pub fn sat_node_individual_extension_data(
        &mut self,
        node: SatNodeId,
        create: bool,
    ) -> IndividualSaturationProcessNodeExtensionDataId {
        if node.is_none() {
            return IndividualSaturationProcessNodeExtensionDataId::NONE;
        }
        if self.sat_node(node).indi_extension_data.is_none() && create {
            let mut ext = IndividualSaturationProcessNodeExtensionData::new(INVALID);
            ext.init_individual_extension_data(node);
            let ext = self.alloc_indi_sat_node_ext_data(ext);
            self.sat_node_mut(node).indi_extension_data = ext;
        }
        self.sat_node(node).indi_extension_data
    }

    /// Context-threaded port of
    /// `CIndividualSaturationProcessNode::getLinkedRoleSuccessorHash`.
    pub fn sat_node_ext_linked_role_successor_hash(
        &mut self,
        node: SatNodeId,
        create: bool,
    ) -> LinkedRoleSaturationSuccessorHashId {
        let ext = self.sat_node_individual_extension_data(node, create);
        if ext.is_none() {
            return LinkedRoleSaturationSuccessorHashId::NONE;
        }
        if self
            .indi_sat_node_ext_data(ext)
            .linked_role_succ_hash
            .is_none()
            && create
        {
            let mut hash = LinkedRoleSaturationSuccessorHash::new();
            hash.init_role_successor_hash();
            let hash = self.alloc_linked_role_sat_succ_hash(hash);
            self.indi_sat_node_ext_data_mut(ext).linked_role_succ_hash = hash;
        }
        self.indi_sat_node_ext_data(ext).linked_role_succ_hash
    }

    /// Context-threaded port of
    /// `CIndividualSaturationProcessNode::getLinkedDataValueAssertionData`.
    pub fn sat_node_ext_linked_data_value_assertion_data(
        &mut self,
        node: SatNodeId,
        create: bool,
    ) -> LinkedDataValueAssertionSaturationDataId {
        let ext = self.sat_node_individual_extension_data(node, create);
        if ext.is_none() {
            return LinkedDataValueAssertionSaturationDataId::NONE;
        }
        if self
            .indi_sat_node_ext_data(ext)
            .linked_data_value_assertion_data
            .is_none()
            && create
        {
            let mut data = LinkedDataValueAssertionSaturationData::new(INVALID);
            data.init_data_value_assertion_data();
            let data = self.alloc_linked_data_value_assertion_data(data);
            self.indi_sat_node_ext_data_mut(ext)
                .linked_data_value_assertion_data = data;
        }
        self.indi_sat_node_ext_data(ext)
            .linked_data_value_assertion_data
    }

    /// Context-threaded port of
    /// `CLinkedDataValueAssertionSaturationData::addDataValueAssertion`.
    ///
    /// The Konclude implementation accepts `CDataLiteral* dataLiteral` but does
    /// not read it; `_data_literal` is retained only for signature fidelity.
    pub fn linked_data_value_assertion_data_add_data_value_assertion(
        &mut self,
        data: LinkedDataValueAssertionSaturationDataId,
        data_role: RoleId,
        _data_literal: Cint64,
    ) -> LinkedDataValueAssertionSaturationDataId {
        if data.is_none() {
            return data;
        }
        let mut linker = DataValueRoleAssertionLinker::new();
        linker.init_linker(data_role);
        let linker = self.alloc_data_value_role_assertion_linker(linker);
        let old_head = self.linked_data_value_assertion_data(data).data_role_linker;
        self.data_value_role_assertion_linker_mut(linker)
            .set_next(old_head);
        self.linked_data_value_assertion_data_mut(data)
            .data_role_linker = linker;
        data
    }

    /// Context-threaded port of
    /// `CIndividualSaturationProcessNode::getSuccessorExtensionData`.
    pub fn sat_node_ext_successor_extension_data(
        &mut self,
        node: SatNodeId,
        create: bool,
    ) -> SaturationIndividualNodeSuccessorExtensionDataId {
        let ext = self.sat_node_individual_extension_data(node, create);
        if ext.is_none() {
            return SaturationIndividualNodeSuccessorExtensionDataId::NONE;
        }
        if self
            .indi_sat_node_ext_data(ext)
            .successor_extension_data
            .is_none()
            && create
        {
            let mut data = SaturationIndividualNodeSuccessorExtensionData::new(INVALID);
            data.init_extension_data(node);
            let data = self.alloc_sat_indi_node_succ_ext_data(data);
            self.indi_sat_node_ext_data_mut(ext)
                .successor_extension_data = data;
        }
        self.indi_sat_node_ext_data(ext).successor_extension_data
    }

    /// Context-threaded port of
    /// `CSaturationIndividualNodeSuccessorExtensionData::getBaseExtensionResolveData`.
    pub fn sat_successor_extension_base_extension_resolve_data(
        &mut self,
        succ_ext: SaturationIndividualNodeSuccessorExtensionDataId,
        create: bool,
    ) -> SaturationIndividualNodeExtensionResolveDataId {
        if succ_ext.is_none() {
            return SaturationIndividualNodeExtensionResolveDataId::NONE;
        }
        if self
            .sat_indi_node_succ_ext_data(succ_ext)
            .get_base_extension_resolve_data()
            .is_none()
            && create
        {
            let indi_node = self.sat_indi_node_succ_ext_data(succ_ext).indi_process_node;
            let indi_id = if indi_node.is_some() {
                self.sat_node(indi_node).get_individual_id()
            } else {
                0
            };
            let mut data = SaturationIndividualNodeExtensionResolveData::new();
            data.init_extension_resolve_data_for_node(indi_node, indi_id);
            let data = self.alloc_sat_indi_node_ext_resolve_data(data);
            self.sat_indi_node_succ_ext_data_mut(succ_ext)
                .set_extension_resolve_data(data);
        }
        self.sat_indi_node_succ_ext_data(succ_ext)
            .get_base_extension_resolve_data()
    }

    /// Context-threaded port of
    /// `CSaturationIndividualNodeExtensionResolveData::getIndividualNodeExtensionResolveHash`.
    pub fn sat_extension_resolve_hash(
        &mut self,
        resolve_data: SaturationIndividualNodeExtensionResolveDataId,
        create: bool,
    ) -> SaturationIndividualNodeExtensionResolveHashId {
        if resolve_data.is_none() {
            return SaturationIndividualNodeExtensionResolveHashId::NONE;
        }
        if self
            .sat_indi_node_ext_resolve_data(resolve_data)
            .extension_resolve_hash
            .is_none()
            && create
        {
            let mut hash = SaturationIndividualNodeExtensionResolveHash::new();
            hash.init_individual_node_extension_resolve_hash();
            let hash = self.alloc_sat_indi_node_ext_resolve_hash(hash);
            self.sat_indi_node_ext_resolve_data_mut(resolve_data)
                .extension_resolve_hash = hash;
        }
        self.sat_indi_node_ext_resolve_data(resolve_data)
            .extension_resolve_hash
    }

    /// Context-threaded port of
    /// `CSaturationIndividualNodeSuccessorExtensionData::getALLConceptsExtensionData`.
    pub fn sat_successor_extension_all_concepts_extension_data(
        &mut self,
        succ_ext: SaturationIndividualNodeSuccessorExtensionDataId,
        create: bool,
    ) -> SaturationIndividualNodeAllConceptsExtensionDataId {
        if succ_ext.is_none() {
            return SaturationIndividualNodeAllConceptsExtensionDataId::NONE;
        }
        if self
            .sat_indi_node_succ_ext_data(succ_ext)
            .get_all_concepts_extension_data()
            .is_none()
            && create
        {
            let indi_process_node = self.sat_indi_node_succ_ext_data(succ_ext).indi_process_node;
            let mut data = SaturationIndividualNodeAllConceptsExtensionData::new();
            data.init_all_concepts_extension_data(indi_process_node);
            let data = self.alloc_sat_indi_node_all_concept_ext_data(data);
            self.sat_indi_node_succ_ext_data_mut(succ_ext)
                .set_all_concepts_extension_data(data);
        }
        self.sat_indi_node_succ_ext_data(succ_ext)
            .get_all_concepts_extension_data()
    }

    /// Context-threaded port of
    /// `CIndividualSaturationProcessNode::getSuccessorExtensionData(...)->getALLConceptsExtensionData`.
    pub fn sat_node_all_concepts_extension_data(
        &mut self,
        node: SatNodeId,
        create: bool,
    ) -> SaturationIndividualNodeAllConceptsExtensionDataId {
        let succ_ext = self.sat_node_ext_successor_extension_data(node, create);
        self.sat_successor_extension_all_concepts_extension_data(succ_ext, create)
    }

    /// Context-threaded port of
    /// `CSaturationIndividualNodeALLConceptsExtensionData::getALLConceptsExtensionData`.
    pub fn sat_all_linked_successor_individual_concepts_extension_data(
        &mut self,
        all_ext: SaturationIndividualNodeAllConceptsExtensionDataId,
        indi_node: SatNodeId,
        create: bool,
    ) -> SaturationLinkedSuccessorIndividualAllConceptsExtensionDataId {
        if all_ext.is_none() {
            return SaturationLinkedSuccessorIndividualAllConceptsExtensionDataId::NONE;
        }
        if let Some(data) = self
            .sat_indi_node_all_concept_ext_data(all_ext)
            .linked_successor_individual_all_concepts_extension_hash
            .linked_successor_individual_all_concepts_extension_hash
            .get(&indi_node)
            .copied()
        {
            return data;
        }
        if !create {
            return SaturationLinkedSuccessorIndividualAllConceptsExtensionDataId::NONE;
        }
        let mut data = SaturationLinkedSuccessorIndividualAllConceptsExtensionData::new();
        data.init_linked_successor_individual_all_concepts_extension_data(indi_node);
        let data = self.alloc_sat_linked_succ_indi_all_concept_ext_data(data);
        self.sat_indi_node_all_concept_ext_data_mut(all_ext)
            .linked_successor_individual_all_concepts_extension_hash
            .linked_successor_individual_all_concepts_extension_hash
            .insert(indi_node, data);
        data
    }

    /// Context-threaded port of
    /// `CSaturationLinkedSuccessorIndividualALLConceptsExtensionData::getRoleSuccessorALLConceptExtensionData`.
    pub fn sat_role_successor_all_concept_extension_data(
        &mut self,
        linked_succ_indi_all_ext: SaturationLinkedSuccessorIndividualAllConceptsExtensionDataId,
        role: RoleId,
        create: bool,
    ) -> SaturationSuccessorAllConceptExtensionDataId {
        if linked_succ_indi_all_ext.is_none() {
            return SaturationSuccessorAllConceptExtensionDataId::NONE;
        }

        if create {
            let only_role = self
                .sat_linked_succ_indi_all_concept_ext_data(linked_succ_indi_all_ext)
                .only_role;
            if only_role.is_some() && only_role != role {
                let only_data = self
                    .sat_linked_succ_indi_all_concept_ext_data(linked_succ_indi_all_ext)
                    .only_all_concept_ext_data;
                if only_data.is_some() {
                    self.sat_linked_succ_indi_all_concept_ext_data_mut(linked_succ_indi_all_ext)
                        .role_concept_extension_hash
                        .insert(only_role, only_data);
                }
                let data =
                    self.sat_linked_succ_indi_all_concept_ext_data_mut(linked_succ_indi_all_ext);
                data.only_role = RoleId::NONE;
                data.only_all_concept_ext_data = SaturationSuccessorAllConceptExtensionDataId::NONE;
            }

            if !self
                .sat_linked_succ_indi_all_concept_ext_data(linked_succ_indi_all_ext)
                .role_concept_extension_hash
                .is_empty()
            {
                if let Some(data) = self
                    .sat_linked_succ_indi_all_concept_ext_data(linked_succ_indi_all_ext)
                    .role_concept_extension_hash
                    .get(&role)
                    .copied()
                {
                    return data;
                }
                let indi_node = self
                    .sat_linked_succ_indi_all_concept_ext_data(linked_succ_indi_all_ext)
                    .indi_proc_sat_node;
                let map = self.alloc_sat_successor_concept_extension_map(
                    SaturationSuccessorConceptExtensionMap::new(),
                );
                let mut data = SaturationSuccessorAllConceptExtensionData::new();
                data.init_successor_concept_extension_data(role, indi_node, map);
                let data = self.alloc_sat_successor_all_concept_ext_data(data);
                self.sat_linked_succ_indi_all_concept_ext_data_mut(linked_succ_indi_all_ext)
                    .role_concept_extension_hash
                    .insert(role, data);
                return data;
            }

            let only_role = self
                .sat_linked_succ_indi_all_concept_ext_data(linked_succ_indi_all_ext)
                .only_role;
            if only_role.is_none() {
                let indi_node = self
                    .sat_linked_succ_indi_all_concept_ext_data(linked_succ_indi_all_ext)
                    .indi_proc_sat_node;
                let map = self.alloc_sat_successor_concept_extension_map(
                    SaturationSuccessorConceptExtensionMap::new(),
                );
                let mut data = SaturationSuccessorAllConceptExtensionData::new();
                data.init_successor_concept_extension_data(role, indi_node, map);
                let data = self.alloc_sat_successor_all_concept_ext_data(data);
                let linked_data =
                    self.sat_linked_succ_indi_all_concept_ext_data_mut(linked_succ_indi_all_ext);
                linked_data.only_role = role;
                linked_data.only_all_concept_ext_data = data;
                return data;
            }
            return self
                .sat_linked_succ_indi_all_concept_ext_data(linked_succ_indi_all_ext)
                .only_all_concept_ext_data;
        }

        let linked_data = self.sat_linked_succ_indi_all_concept_ext_data(linked_succ_indi_all_ext);
        if !linked_data.role_concept_extension_hash.is_empty() {
            linked_data
                .role_concept_extension_hash
                .get(&role)
                .copied()
                .unwrap_or(SaturationSuccessorAllConceptExtensionDataId::NONE)
        } else if linked_data.only_role == role {
            linked_data.only_all_concept_ext_data
        } else {
            SaturationSuccessorAllConceptExtensionDataId::NONE
        }
    }

    /// Context-threaded port of
    /// `CSaturationIndividualNodeSuccessorExtensionData::getFUNCTIONALConceptsExtensionData`.
    pub fn sat_successor_extension_functional_concepts_extension_data(
        &mut self,
        succ_ext: SaturationIndividualNodeSuccessorExtensionDataId,
        create: bool,
    ) -> SaturationIndividualNodeFunctionalConceptsExtensionDataId {
        if succ_ext.is_none() {
            return SaturationIndividualNodeFunctionalConceptsExtensionDataId::NONE;
        }
        if self
            .sat_indi_node_succ_ext_data(succ_ext)
            .get_functional_concepts_extension_data()
            .is_none()
            && create
        {
            let indi_process_node = self.sat_indi_node_succ_ext_data(succ_ext).indi_process_node;
            let mut data = SaturationIndividualNodeFunctionalConceptsExtensionData::new();
            data.init_functional_concepts_extension_data(indi_process_node);
            let data = self.alloc_sat_indi_node_functional_concept_ext_data(data);
            self.sat_indi_node_succ_ext_data_mut(succ_ext)
                .set_functional_concepts_extension_data(data);
        }
        self.sat_indi_node_succ_ext_data(succ_ext)
            .get_functional_concepts_extension_data()
    }

    /// Context-threaded port of
    /// `CIndividualSaturationProcessNode::getSuccessorExtensionData(...)->getFUNCTIONALConceptsExtensionData`.
    pub fn sat_node_functional_concepts_extension_data(
        &mut self,
        node: SatNodeId,
        create: bool,
    ) -> SaturationIndividualNodeFunctionalConceptsExtensionDataId {
        let succ_ext = self.sat_node_ext_successor_extension_data(node, create);
        self.sat_successor_extension_functional_concepts_extension_data(succ_ext, create)
    }

    /// Context-threaded port of
    /// `CSaturationIndividualNodeFUNCTIONALConceptsExtensionData::getSuccessorFUNCTIONALConceptsExtensionData`.
    pub fn sat_functional_successor_concepts_extension_data(
        &mut self,
        functional_ext: SaturationIndividualNodeFunctionalConceptsExtensionDataId,
        role: RoleId,
        create: bool,
    ) -> SaturationSuccessorFunctionalConceptExtensionDataId {
        if functional_ext.is_none() {
            return SaturationSuccessorFunctionalConceptExtensionDataId::NONE;
        }
        if let Some(data) = self
            .sat_indi_node_functional_concept_ext_data(functional_ext)
            .linked_succ_role_functional_concept_ext_hash
            .linked_succ_role_functional_concept_ext_hash
            .get(&role)
            .copied()
        {
            return data;
        }
        if !create {
            return SaturationSuccessorFunctionalConceptExtensionDataId::NONE;
        }
        let mut data = SaturationSuccessorFunctionalConceptExtensionData::new();
        data.init_successor_concept_extension_data(role);
        let data = self.alloc_sat_successor_functional_concept_ext_data(data);
        self.sat_indi_node_functional_concept_ext_data_mut(functional_ext)
            .linked_succ_role_functional_concept_ext_hash
            .linked_succ_role_functional_concept_ext_hash
            .insert(role, data);
        data
    }

    /// Context-threaded port of
    /// `CIndividualSaturationProcessNode::getDisjunctCommonConceptExtractionData`.
    pub fn sat_node_ext_disjunct_common_concept_extraction_data(
        &mut self,
        node: SatNodeId,
        create: bool,
    ) -> SaturationDisjunctCommonConceptExtractionDataId {
        let ext = self.sat_node_individual_extension_data(node, create);
        if ext.is_none() {
            return SaturationDisjunctCommonConceptExtractionDataId::NONE;
        }
        if self
            .indi_sat_node_ext_data(ext)
            .dis_com_con_ext_data
            .is_none()
            && create
        {
            let mut data = SaturationDisjunctCommonConceptExtractionData::new(INVALID);
            data.init_extraction_data(node);
            let mut linker = IndividualSaturationProcessNodeLinker::new();
            linker.init_process_node_linker(node, false);
            let linker = self.alloc_indi_sat_process_node_linker(linker);
            data.set_extraction_continue_process_linker(linker);
            let data = self.alloc_sat_disjunct_common_concept_extraction_data(data);
            self.indi_sat_node_ext_data_mut(ext).dis_com_con_ext_data = data;
        }
        self.indi_sat_node_ext_data(ext).dis_com_con_ext_data
    }

    /// Context-threaded port of
    /// `CSaturationDisjunctCommonConceptExtractionData::addDisjunctIndividualNodeExtractionLinker`.
    pub fn sat_disjunct_common_concept_extraction_data_add_linker(
        &mut self,
        data: SaturationDisjunctCommonConceptExtractionDataId,
        linker: SaturationDisjunctExtractionLinkerId,
    ) -> SaturationDisjunctCommonConceptExtractionDataId {
        if data.is_none() {
            return data;
        }
        if linker.is_some() {
            let old_head = self
                .sat_disjunct_common_concept_extraction_data(data)
                .disjunct_extraction_linker;
            self.sat_disjunct_extraction_linker_mut(linker)
                .set_next(old_head);
            self.sat_disjunct_common_concept_extraction_data_mut(data)
                .set_disjunct_individual_node_extraction_linker(linker);
        }
        data
    }

    /// Context-threaded port of
    /// `CIndividualSaturationProcessNode::getATMOSTSuccessorMergingData`.
    pub fn sat_node_ext_atmost_successor_merging_data(
        &mut self,
        node: SatNodeId,
        create: bool,
    ) -> SaturationAtmostSuccessorMergingDataId {
        let ext = self.sat_node_individual_extension_data(node, create);
        if ext.is_none() {
            return SaturationAtmostSuccessorMergingDataId::NONE;
        }
        if self
            .indi_sat_node_ext_data(ext)
            .atmost_successor_merging_data
            .is_none()
            && create
        {
            let mut data = SaturationAtmostSuccessorMergingData::new(INVALID);
            data.init_successor_merging_data(node);
            let data = self.alloc_sat_atmost_successor_merging_data(data);
            self.indi_sat_node_ext_data_mut(ext)
                .atmost_successor_merging_data = data;
        }
        self.indi_sat_node_ext_data(ext)
            .atmost_successor_merging_data
    }

    /// Context-threaded port of
    /// `CSaturationATMOSTSuccessorMergingData::getATMOSTConceptMergingDataHash`.
    pub fn sat_atmost_successor_merging_data_concept_merging_hash(
        &mut self,
        data: SaturationAtmostSuccessorMergingDataId,
        create: bool,
    ) -> SaturationAtmostSuccessorMergingHashId {
        if data.is_none() {
            return SaturationAtmostSuccessorMergingHashId::NONE;
        }
        if self
            .sat_atmost_successor_merging_data(data)
            .concept_merging_data_hash
            .is_none()
            && create
        {
            let mut hash = SaturationAtmostSuccessorMergingHash::new(INVALID);
            hash.init_atmost_concept_descriptor_merging_hash(None);
            let hash = self.alloc_sat_atmost_successor_merging_hash(hash);
            self.sat_atmost_successor_merging_data_mut(data)
                .concept_merging_data_hash = hash;
        }
        self.sat_atmost_successor_merging_data(data)
            .concept_merging_data_hash
    }

    /// Context-threaded port of
    /// `CSaturationATMOSTSuccessorMergingData::getATMOSTConceptMergingData`.
    pub fn sat_atmost_successor_merging_data_atmost_concept_merging_data(
        &mut self,
        data: SaturationAtmostSuccessorMergingDataId,
        con_sat_des: ConceptSaturationDescriptorId,
    ) -> Option<&mut super::super::saturation::satellites::SaturationAtmostSuccessorMergingHashData>
    {
        let hash = self.sat_atmost_successor_merging_data_concept_merging_hash(data, true);
        if hash.is_none() {
            return None;
        }
        Some(
            self.sat_atmost_successor_merging_hash_mut(hash)
                .get_atmost_concept_merging_data(con_sat_des),
        )
    }

    /// Context-threaded port of
    /// `CSaturationATMOSTSuccessorMergingData::addMergingProcessingConcept`.
    pub fn sat_atmost_successor_merging_data_add_merging_processing_concept(
        &mut self,
        data: SaturationAtmostSuccessorMergingDataId,
        con_sat_des: ConceptSaturationDescriptorId,
    ) -> SaturationAtmostSuccessorMergingDataId {
        if data.is_none() {
            return data;
        }
        let mut linker = ConceptSaturationProcessLinker::new();
        linker.init_concept_saturation_process_linker(con_sat_des);
        let linker = self.alloc_con_sat_proc_linker(linker);
        let old_head = self
            .sat_atmost_successor_merging_data(data)
            .merging_concept_linker;
        self.con_sat_proc_linker_mut(linker).set_next(old_head);
        self.sat_atmost_successor_merging_data_mut(data)
            .merging_concept_linker = linker;
        data
    }

    /// Context-threaded port of
    /// `CSaturationATMOSTSuccessorMergingData::takeNextMergingConceptLinker`.
    pub fn sat_atmost_successor_merging_data_take_next_merging_concept_linker(
        &mut self,
        data: SaturationAtmostSuccessorMergingDataId,
    ) -> ConceptSaturationProcessLinkerId {
        if data.is_none() {
            return ConceptSaturationProcessLinkerId::NONE;
        }
        let current = self
            .sat_atmost_successor_merging_data(data)
            .merging_concept_linker;
        if current.is_some() {
            let next = self.con_sat_proc_linker(current).get_next();
            self.sat_atmost_successor_merging_data_mut(data)
                .merging_concept_linker = next;
        }
        self.sat_atmost_successor_merging_data(data)
            .merging_concept_linker
    }

    /// Context-threaded port of
    /// `CSaturationATMOSTSuccessorMergingData::getMergedLinkedRoleSaturationSuccessorHash`.
    pub fn sat_atmost_successor_merging_data_merged_linked_role_successor_hash(
        &mut self,
        data: SaturationAtmostSuccessorMergingDataId,
        create: bool,
    ) -> LinkedRoleSaturationSuccessorHashId {
        if data.is_none() {
            return LinkedRoleSaturationSuccessorHashId::NONE;
        }
        if self
            .sat_atmost_successor_merging_data(data)
            .new_successor_hash
            .is_none()
            && create
        {
            let mut hash = LinkedRoleSaturationSuccessorHash::new();
            hash.init_role_successor_hash();
            let hash = self.alloc_linked_role_sat_succ_hash(hash);
            self.sat_atmost_successor_merging_data_mut(data)
                .new_successor_hash = hash;
        }
        self.sat_atmost_successor_merging_data(data)
            .new_successor_hash
    }

    /// Context-threaded port of
    /// `CSaturationATMOSTSuccessorMergingData::getRemainingMergeableCardinalityHash`.
    pub fn sat_atmost_successor_merging_data_remaining_mergeable_cardinality_hash(
        &mut self,
        data: SaturationAtmostSuccessorMergingDataId,
        create: bool,
    ) -> Option<&mut std::collections::HashMap<SaturationSuccessorDataId, Cint64>> {
        if data.is_none() {
            return None;
        }
        if create {
            self.sat_atmost_successor_merging_data_mut(data)
                .has_remain_mergeable_card_hash = true;
        }
        self.sat_atmost_successor_merging_data_mut(data)
            .get_remaining_mergeable_cardinality_hash_mut()
    }

    /// Context-threaded port of
    /// `CSaturationATMOSTSuccessorMergingData::getMergingDistintHash`.
    pub fn sat_atmost_successor_merging_data_merging_distinct_hash(
        &mut self,
        data: SaturationAtmostSuccessorMergingDataId,
        create: bool,
    ) -> Option<&mut std::collections::HashMap<SaturationSuccessorDataId, SaturationSuccessorDataId>>
    {
        if data.is_none() {
            return None;
        }
        if create {
            self.sat_atmost_successor_merging_data_mut(data)
                .has_merge_distinct_hash = true;
        }
        self.sat_atmost_successor_merging_data_mut(data)
            .get_merging_distinct_hash_mut()
    }

    /// Context-threaded port of
    /// `CSaturationATMOSTSuccessorMergingData::getMergingDistintSet`.
    pub fn sat_atmost_successor_merging_data_merging_distinct_set(
        &mut self,
        data: SaturationAtmostSuccessorMergingDataId,
        create: bool,
    ) -> Option<
        &mut std::collections::HashSet<(SaturationSuccessorDataId, SaturationSuccessorDataId)>,
    > {
        if data.is_none() {
            return None;
        }
        if create {
            self.sat_atmost_successor_merging_data_mut(data)
                .has_merge_distinct_set = true;
        }
        self.sat_atmost_successor_merging_data_mut(data)
            .get_merging_distinct_set_mut()
    }

    /// Context-threaded port of
    /// `CIndividualSaturationProcessNodeExtensionData::addRoleAssertionLinker`.
    pub fn sat_node_ext_add_role_assertion_linker(
        &mut self,
        node: SatNodeId,
        role_assertion_linker: SaturationSuccessorRoleAssertionLinkerId,
    ) -> IndividualSaturationProcessNodeExtensionDataId {
        let ext = self.sat_node_individual_extension_data(node, true);
        if ext.is_none() {
            return ext;
        }
        if role_assertion_linker.is_some() {
            let old_head = self.indi_sat_node_ext_data(ext).role_assertion_linker;
            self.sat_succ_role_assertion_linker_mut(role_assertion_linker)
                .set_next(old_head);
            self.indi_sat_node_ext_data_mut(ext).role_assertion_linker = role_assertion_linker;
        }
        ext
    }

    /// Context-threaded port of
    /// `CIndividualSaturationProcessNodeExtensionData::addRoleAssertion`.
    pub fn sat_node_ext_add_role_assertion(
        &mut self,
        node: SatNodeId,
        destination_node: SatNodeId,
        role: RoleId,
        role_negation: bool,
    ) -> IndividualSaturationProcessNodeExtensionDataId {
        if node.is_none() {
            return IndividualSaturationProcessNodeExtensionDataId::NONE;
        }
        let mut linker = SaturationSuccessorRoleAssertionLinker::new();
        linker.init_saturation_successor_role_assertion_linker(
            destination_node,
            role,
            role_negation,
        );
        let linker = self.alloc_sat_succ_role_assertion_linker(linker);
        self.sat_node_ext_add_role_assertion_linker(node, linker)
    }

    /// Context-threaded port of
    /// `CIndividualSaturationProcessNode::getRoleAssertionLinker`.
    pub fn sat_node_ext_role_assertion_linker(
        &self,
        node: SatNodeId,
    ) -> SaturationSuccessorRoleAssertionLinkerId {
        if node.is_none() {
            return SaturationSuccessorRoleAssertionLinkerId::NONE;
        }
        let ext = self.sat_node(node).indi_extension_data;
        if ext.is_none() {
            return SaturationSuccessorRoleAssertionLinkerId::NONE;
        }
        self.indi_sat_node_ext_data(ext).role_assertion_linker
    }

    /// Context-threaded port of
    /// `CIndividualSaturationProcessNode::getCriticalConceptTypeQueues`.
    pub fn sat_node_ext_critical_concept_type_queues(
        &mut self,
        node: SatNodeId,
        create: bool,
    ) -> CriticalSaturationConceptTypeQueuesId {
        let ext = self.sat_node_individual_extension_data(node, create);
        if ext.is_none() {
            return CriticalSaturationConceptTypeQueuesId::NONE;
        }
        if self
            .indi_sat_node_ext_data(ext)
            .critical_concept_type_queues
            .is_none()
            && create
        {
            let mut queues = CriticalSaturationConceptTypeQueues::new(INVALID);
            queues.init_critical_saturation_concept_queues(node);
            let queues = self.alloc_critical_sat_concept_type_queues(queues);
            self.indi_sat_node_ext_data_mut(ext)
                .critical_concept_type_queues = queues;
        }
        self.indi_sat_node_ext_data(ext)
            .critical_concept_type_queues
    }

    /// Context-threaded port of
    /// `CIndividualSaturationProcessNode::getCriticalPredecessorRoleCardinalityHash`.
    pub fn sat_node_ext_critical_predecessor_role_cardinality_hash(
        &mut self,
        node: SatNodeId,
        create: bool,
    ) -> CriticalPredecessorRoleCardinalityHashId {
        let ext = self.sat_node_individual_extension_data(node, create);
        if ext.is_none() {
            return CriticalPredecessorRoleCardinalityHashId::NONE;
        }
        if self
            .indi_sat_node_ext_data(ext)
            .critical_pred_role_card_hash
            .is_none()
            && create
        {
            let mut hash = CriticalPredecessorRoleCardinalityHash::new(INVALID);
            hash.init_critical_predecessor_role_cardinality_hash();
            let hash = self.alloc_critical_pred_role_card_hash(hash);
            self.indi_sat_node_ext_data_mut(ext)
                .critical_pred_role_card_hash = hash;
        }
        self.indi_sat_node_ext_data(ext)
            .critical_pred_role_card_hash
    }

    /// Context-threaded port of
    /// `CCriticalPredecessorRoleCardinalityHash::getCriticalPredecessorRoleCardinalityData`.
    pub fn critical_predecessor_role_cardinality_hash_data(
        &mut self,
        hash: CriticalPredecessorRoleCardinalityHashId,
        role: RoleId,
        force_creation: bool,
    ) -> CriticalPredecessorRoleCardinalityDataId {
        if hash.is_none() {
            return CriticalPredecessorRoleCardinalityDataId::NONE;
        }
        let data = self
            .critical_pred_role_card_hash(hash)
            .get_critical_predecessor_role_cardinality_data(role);
        if data.is_none() && force_creation {
            let data = self
                .alloc_critical_pred_role_card_data(CriticalPredecessorRoleCardinalityData::new());
            self.critical_pred_role_card_hash_mut(hash)
                .critical_predecessor_role_data_hash
                .insert(role, data);
            data
        } else {
            data
        }
    }

    /// Context-threaded port of
    /// `CCriticalPredecessorRoleCardinalityHash::addCriticalPredecessorRoleCardinality`.
    pub fn critical_predecessor_role_cardinality_hash_add_cardinality(
        &mut self,
        hash: CriticalPredecessorRoleCardinalityHashId,
        role: RoleId,
        unproblematic_concept: ConceptId,
        unproblematic_negation: bool,
    ) -> CriticalPredecessorRoleCardinalityHashId {
        let data = self.critical_predecessor_role_cardinality_hash_data(hash, role, true);
        if data.is_some() {
            self.critical_pred_role_card_data_mut(data)
                .unproblematic_concept_linker
                .insert(
                    0,
                    NegLink {
                        target: unproblematic_concept,
                        negated: unproblematic_negation,
                    },
                );
        }
        hash
    }

    /// Context-threaded port of
    /// `CIndividualSaturationProcessNode::getAppliedDatatypeData`.
    pub fn sat_node_ext_applied_datatype_data(
        &mut self,
        node: SatNodeId,
        create: bool,
    ) -> SaturationIndividualNodeDatatypeDataId {
        let ext = self.sat_node_individual_extension_data(node, create);
        if ext.is_none() {
            return SaturationIndividualNodeDatatypeDataId::NONE;
        }
        if self
            .indi_sat_node_ext_data(ext)
            .applied_datatype_data
            .is_none()
            && create
        {
            let mut data = SaturationIndividualNodeDatatypeData::new(INVALID);
            data.init_extension_data(node);
            let data = self.alloc_sat_indi_node_datatype_data(data);
            self.indi_sat_node_ext_data_mut(ext).applied_datatype_data = data;
        }
        self.indi_sat_node_ext_data(ext).applied_datatype_data
    }

    /// Context-threaded port of
    /// `CLinkedRoleSaturationSuccessorHash::getLinkedRoleSuccessorData`.
    pub fn linked_role_successor_data(
        &mut self,
        hash: LinkedRoleSaturationSuccessorHashId,
        role: RoleId,
        create: bool,
    ) -> LinkedRoleSaturationSuccessorDataId {
        if hash.is_none() {
            return LinkedRoleSaturationSuccessorDataId::NONE;
        }
        if let Some(data) = self
            .linked_role_sat_succ_hash(hash)
            .role_succ_data_hash
            .get(&role)
            .copied()
        {
            return data;
        }
        if !create {
            return LinkedRoleSaturationSuccessorDataId::NONE;
        }
        let data = self.alloc_linked_role_sat_succ_data(LinkedRoleSaturationSuccessorData::new());
        self.linked_role_sat_succ_hash_mut(hash)
            .role_succ_data_hash
            .insert(role, data);
        data
    }

    /// Context-threaded port of
    /// `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::getSucessorExtensionData`.
    pub fn linked_role_successor_extension_data(
        &mut self,
        succ_data: LinkedRoleSaturationSuccessorDataId,
        create: bool,
    ) -> SaturationSuccessorExtensionDataId {
        if succ_data.is_none() {
            return SaturationSuccessorExtensionDataId::NONE;
        }
        let ext_data = self.linked_role_sat_succ_data(succ_data).extension_data;
        if ext_data.is_some() || !create {
            return ext_data;
        }
        let mut data = SaturationSuccessorExtensionData::new(INVALID);
        data.init_successor_extension_data();
        let data = self.alloc_sat_succ_ext_data(data);
        self.linked_role_sat_succ_data_mut(succ_data).extension_data = data;
        data
    }

    /// Read a role bucket's successor data for the given saturation successor
    /// node id.
    pub fn linked_role_successor_node_data(
        &self,
        data: LinkedRoleSaturationSuccessorDataId,
        succ_node: SatNodeId,
    ) -> SaturationSuccessorDataId {
        if data.is_none() || succ_node.is_none() || succ_node.index() >= self.sat_node_count() {
            return SaturationSuccessorDataId::NONE;
        }
        let succ_key = self.sat_successor_key_for_node(succ_node);
        self.linked_role_sat_succ_data(data)
            .succ_node_data_map
            .get(&succ_key)
            .copied()
            .unwrap_or(SaturationSuccessorDataId::NONE)
    }

    /// Minimal live surface for Konclude's active linked-successor checks.
    pub fn linked_role_successor_has_active_successor(
        &self,
        data: LinkedRoleSaturationSuccessorDataId,
        succ_node: SatNodeId,
    ) -> bool {
        let succ_data = self.linked_role_successor_node_data(data, succ_node);
        succ_data.is_some() && self.sat_succ_data(succ_data).is_active()
    }

    fn sat_successor_key_for_node(&self, linked_indi: SatNodeId) -> Cint64 {
        self.sat_node(linked_indi).get_individual_id()
    }

    /// Context-threaded port of
    /// `CLinkedRoleSaturationSuccessorHash::getLinkedRoleSuccessorData(roleSuccData, linkedIndiID, forceNewCreation)`.
    pub fn linked_role_successor_data_for_individual_id(
        &mut self,
        role_succ_data: LinkedRoleSaturationSuccessorDataId,
        linked_indi_id: Cint64,
        force_new_creation: bool,
    ) -> SaturationSuccessorDataId {
        if role_succ_data.is_none() {
            return SaturationSuccessorDataId::NONE;
        }
        let prev_succ_data = self
            .linked_role_sat_succ_data(role_succ_data)
            .succ_node_data_map
            .get(&linked_indi_id)
            .copied()
            .unwrap_or(SaturationSuccessorDataId::NONE);
        if prev_succ_data.is_some() && !force_new_creation {
            return prev_succ_data;
        }

        let mut succ_data = SaturationSuccessorData::new();
        if prev_succ_data.is_some() {
            let prev = self.sat_succ_data(prev_succ_data);
            succ_data.succ_count = prev.succ_count;
            succ_data.active_count = prev.active_count;
            succ_data.extension = prev.extension;
            succ_data.value_nominal_connection = prev.value_nominal_connection;
            succ_data.value_nominal_id = prev.value_nominal_id;
            succ_data.succ_indi_node = prev.succ_indi_node;
            succ_data.creation_role_linker = prev.creation_role_linker.clone();
            self.sat_succ_data_mut(prev_succ_data).active_count = 0;
        }
        succ_data.next_link = self
            .linked_role_sat_succ_data(role_succ_data)
            .get_last_successor_link_data();
        let succ_data = self.alloc_sat_succ_data(succ_data);
        self.linked_role_sat_succ_data_mut(role_succ_data)
            .succ_node_data_map
            .insert(linked_indi_id, succ_data);
        self.linked_role_sat_succ_data_mut(role_succ_data)
            .set_last_successor_link_data(succ_data);
        succ_data
    }

    /// Port of `CLinkedRoleSaturationSuccessorHash::hasActiveCreationRole`.
    pub fn saturation_successor_data_has_active_creation_role(
        &self,
        succ_data: SaturationSuccessorDataId,
        creation_role: RoleId,
    ) -> bool {
        succ_data.is_some()
            && self
                .sat_succ_data(succ_data)
                .creation_role_linker
                .iter()
                .any(|link| !link.negated && link.target == creation_role)
    }

    /// Context-threaded port of
    /// `CLinkedRoleSaturationSuccessorHash::hasActiveLinkedSuccessor`.
    pub fn linked_role_successor_hash_has_active_linked_successor(
        &self,
        hash: LinkedRoleSaturationSuccessorHashId,
        role: RoleId,
        succ_node: SatNodeId,
        creation_role: Option<RoleId>,
        link_count: Cint64,
    ) -> bool {
        if hash.is_none() || succ_node.is_none() {
            return false;
        }
        let data = self
            .linked_role_sat_succ_hash(hash)
            .get_linked_role_successor_data(role);
        if data.is_none() {
            return false;
        }
        let succ_key = self.sat_successor_key_for_node(succ_node);
        let succ_data = self
            .linked_role_sat_succ_data(data)
            .succ_node_data_map
            .get(&succ_key)
            .copied()
            .unwrap_or(SaturationSuccessorDataId::NONE);
        if succ_data.is_none() {
            return false;
        }
        let succ = self.sat_succ_data(succ_data);
        if succ.active_count < 1 || succ.succ_count < link_count {
            return false;
        }
        match creation_role {
            None => true,
            Some(creation_role) => succ
                .creation_role_linker
                .iter()
                .any(|link| !link.negated && link.target == creation_role),
        }
    }

    /// Context-threaded port of
    /// `CLinkedRoleSaturationSuccessorHash::addExtensionSuccessor`.
    pub fn linked_role_successor_hash_add_extension_successor(
        &mut self,
        hash: LinkedRoleSaturationSuccessorHashId,
        role: RoleId,
        succ_node: SatNodeId,
        creation_role: RoleId,
        link_count: Cint64,
    ) -> SaturationSuccessorDataId {
        if hash.is_none() || role.is_none() || succ_node.is_none() {
            return SaturationSuccessorDataId::NONE;
        }
        let role_succ_data = self.linked_role_successor_data(hash, role, true);
        let succ_key = self.sat_successor_key_for_node(succ_node);
        let succ_data =
            self.linked_role_successor_data_for_individual_id(role_succ_data, succ_key, true);
        let creation_role_already_exists =
            self.saturation_successor_data_has_active_creation_role(succ_data, creation_role);
        if !creation_role_already_exists {
            self.sat_succ_data_mut(succ_data).active_count += 1;
        }
        {
            let succ_ref = self.sat_succ_data_mut(succ_data);
            succ_ref.extension = true;
            succ_ref.succ_indi_node = succ_node;
            if !creation_role_already_exists {
                succ_ref.creation_role_linker.insert(
                    0,
                    NegLink {
                        target: creation_role,
                        negated: false,
                    },
                );
            }
        }
        let old_count = self.sat_succ_data(succ_data).succ_count;
        let link_count_diff = if old_count < link_count {
            link_count - old_count
        } else {
            0
        };
        self.sat_succ_data_mut(succ_data).succ_count += link_count_diff;
        self.linked_role_sat_succ_data_mut(role_succ_data)
            .succ_count += link_count_diff;
        succ_data
    }

    /// Context-threaded port of
    /// `CLinkedRoleSaturationSuccessorHash::addLinkedSuccessor`.
    pub fn linked_role_successor_hash_add_linked_successor(
        &mut self,
        hash: LinkedRoleSaturationSuccessorHashId,
        role: RoleId,
        succ_node: SatNodeId,
        creation_role: RoleId,
        link_count: Cint64,
    ) -> SaturationSuccessorDataId {
        if hash.is_none() || role.is_none() || succ_node.is_none() {
            return SaturationSuccessorDataId::NONE;
        }
        let role_succ_data = self.linked_role_successor_data(hash, role, true);
        let succ_key = self.sat_successor_key_for_node(succ_node);
        let succ_data =
            self.linked_role_successor_data_for_individual_id(role_succ_data, succ_key, true);
        let creation_role_already_exists =
            self.saturation_successor_data_has_active_creation_role(succ_data, creation_role);
        if !creation_role_already_exists {
            self.sat_succ_data_mut(succ_data).active_count += 1;
        }
        {
            let succ_ref = self.sat_succ_data_mut(succ_data);
            succ_ref.extension = false;
            succ_ref.value_nominal_connection = false;
            succ_ref.succ_indi_node = succ_node;
            if !creation_role_already_exists {
                succ_ref.creation_role_linker.insert(
                    0,
                    NegLink {
                        target: creation_role,
                        negated: false,
                    },
                );
            }
        }
        let old_count = self.sat_succ_data(succ_data).succ_count;
        let link_count_diff = if old_count < link_count {
            link_count - old_count
        } else {
            0
        };
        self.sat_succ_data_mut(succ_data).succ_count += link_count_diff;
        self.linked_role_sat_succ_data_mut(role_succ_data)
            .succ_count += link_count_diff;
        succ_data
    }

    /// Context-threaded port of
    /// `CLinkedRoleSaturationSuccessorHash::addLinkedVALUESuccessor`.
    pub fn linked_role_successor_hash_add_linked_value_successor(
        &mut self,
        hash: LinkedRoleSaturationSuccessorHashId,
        role: RoleId,
        nominal_id: Cint64,
        creation_role: RoleId,
    ) -> SaturationSuccessorDataId {
        if hash.is_none() || role.is_none() {
            return SaturationSuccessorDataId::NONE;
        }
        let role_succ_data = self.linked_role_successor_data(hash, role, true);
        let succ_data =
            self.linked_role_successor_data_for_individual_id(role_succ_data, nominal_id, true);
        let creation_role_already_exists =
            self.saturation_successor_data_has_active_creation_role(succ_data, creation_role);
        if !creation_role_already_exists {
            self.sat_succ_data_mut(succ_data).active_count += 1;
        }
        {
            let succ_ref = self.sat_succ_data_mut(succ_data);
            succ_ref.extension = false;
            succ_ref.value_nominal_connection = true;
            succ_ref.value_nominal_id = nominal_id;
            succ_ref.succ_indi_node = SatNodeId::NONE;
            if !creation_role_already_exists {
                succ_ref.creation_role_linker.insert(
                    0,
                    NegLink {
                        target: creation_role,
                        negated: false,
                    },
                );
            }
        }
        let old_count = self.sat_succ_data(succ_data).succ_count;
        let link_count_diff = if old_count < 1 { 1 - old_count } else { 0 };
        self.sat_succ_data_mut(succ_data).succ_count += link_count_diff;
        self.linked_role_sat_succ_data_mut(role_succ_data)
            .succ_count += link_count_diff;
        succ_data
    }

    /// Context-threaded port of
    /// `CLinkedRoleSaturationSuccessorHash::deactivateLinkedSuccessor`.
    pub fn linked_role_successor_hash_deactivate_linked_successor(
        &mut self,
        hash: LinkedRoleSaturationSuccessorHashId,
        role: RoleId,
        succ_node: SatNodeId,
        creation_role: RoleId,
    ) -> bool {
        if hash.is_none() || role.is_none() || succ_node.is_none() {
            return false;
        }
        let role_succ_data = self.linked_role_successor_data(hash, role, true);
        let succ_key = self.sat_successor_key_for_node(succ_node);
        let succ_data =
            self.linked_role_successor_data_for_individual_id(role_succ_data, succ_key, false);
        if succ_data.is_none() || self.sat_succ_data(succ_data).active_count <= 0 {
            return false;
        }
        self.sat_succ_data_mut(succ_data).active_count -= 1;
        if let Some(link) = self
            .sat_succ_data_mut(succ_data)
            .creation_role_linker
            .iter_mut()
            .find(|link| link.target == creation_role && !link.negated)
        {
            link.negated = true;
        }
        if self.sat_succ_data(succ_data).active_count <= 0 {
            let old_count = self.sat_succ_data(succ_data).succ_count;
            self.linked_role_sat_succ_data_mut(role_succ_data)
                .succ_count -= old_count;
            self.sat_succ_data_mut(succ_data).succ_count = 0;
        }
        true
    }

    /// Context-threaded port of `CIndividualSaturationProcessNode::getNominalHandlingData`.
    pub fn sat_node_nominal_handling_data(
        &mut self,
        node: SatNodeId,
        create: bool,
    ) -> SaturationIndividualNodeNominalHandlingDataId {
        let ext = self.sat_node_individual_extension_data(node, create);
        if ext.is_none() {
            return SaturationIndividualNodeNominalHandlingDataId::NONE;
        }
        if self
            .indi_sat_node_ext_data(ext)
            .nominal_handling_data
            .is_none()
            && create
        {
            let mut data = SaturationIndividualNodeNominalHandlingData::new(INVALID);
            data.init_nominal_handling_data(node);
            let data = self.alloc_sat_nominal_handling_data(data);
            self.indi_sat_node_ext_data_mut(ext).nominal_handling_data = data;
        }
        self.indi_sat_node_ext_data(ext).nominal_handling_data
    }

    /// Context-threaded port of `CIndividualSaturationProcessNode::getSuccessorConnectedNominalSet(true)`.
    pub fn sat_node_successor_connected_nominal_set(
        &mut self,
        node: SatNodeId,
        create: bool,
    ) -> SuccessorConnectedNominalSetId {
        let nominal_handling = self.sat_node_nominal_handling_data(node, create);
        if nominal_handling.is_none() {
            return SuccessorConnectedNominalSetId::NONE;
        }
        if self
            .sat_nominal_handling_data(nominal_handling)
            .succ_connected_nominal_set
            .is_none()
            && create
        {
            let mut set = SuccessorConnectedNominalSet::new();
            set.init_successor_connected_nominal_set(None);
            let set = self.alloc_nominal_conn_set(set);
            self.sat_nominal_handling_data_mut(nominal_handling)
                .succ_connected_nominal_set = set;
        }
        self.sat_nominal_handling_data(nominal_handling)
            .succ_connected_nominal_set
    }

    /// Context-threaded port of `CIndividualSaturationProcessNode::getSuccessorConnectedNominalSet(false)`.
    pub fn sat_node_successor_connected_nominal_set_existing(
        &mut self,
        node: SatNodeId,
    ) -> SuccessorConnectedNominalSetId {
        self.sat_node_successor_connected_nominal_set(node, false)
    }

    /// Snapshot of `getSuccessorConnectedNominalSet(false)->constBegin/constEnd`.
    pub fn sat_node_successor_connected_nominals(&mut self, node: SatNodeId) -> Vec<Cint64> {
        let set = self.sat_node_successor_connected_nominal_set_existing(node);
        if set.is_some() {
            self.nominal_conn_set(set).iter_snapshot()
        } else {
            Vec::new()
        }
    }

    /// Context-threaded port of `CSuccessorConnectedNominalSet::hasSuccessorConnectedNominal`
    /// for saturation nodes.
    pub fn sat_node_has_successor_connected_nominal(
        &mut self,
        node: SatNodeId,
        nominal_id: Cint64,
    ) -> bool {
        let set = self.sat_node_successor_connected_nominal_set_existing(node);
        set.is_some()
            && self
                .nominal_conn_set(set)
                .has_successor_connected_nominal(nominal_id)
    }

    /// Context-threaded port of
    /// `CIndividualSaturationProcessNode::getSuccessorConnectedNominalSet(true)->addSuccessorConnectedNominal`.
    pub fn sat_node_add_successor_connected_nominal(
        &mut self,
        node: SatNodeId,
        nominal_id: Cint64,
    ) -> bool {
        let set = self.sat_node_successor_connected_nominal_set(node, true);
        set.is_some()
            && self
                .nominal_conn_set_mut(set)
                .add_successor_connected_nominal(nominal_id)
    }

    // --- u15 merge / nominal-expansion satellite trios ---
    arena_accessors!(
        individual_merging_hashes,
        IndividualMergingHash,
        IndividualMergingHashId,
        individual_merging_hash,
        individual_merging_hash_mut,
        alloc_individual_merging_hash
    );
    // Hand-written Arc-COW accessors (see the KONCLUDE-PORT-NOTE[cow] on the
    // `label_sets` field).
    /// Resolve an id to a shared borrow (the `obj->` read path).
    #[inline]
    pub fn succ_role_hash(&self, id: SuccessorRoleHashId) -> &SuccessorRoleHash {
        self.succ_role_hashes.get(Id::new(id.raw)).as_ref()
    }
    /// Resolve an id to a mutable borrow — copy-on-write when shared.
    #[inline]
    pub fn succ_role_hash_mut(&mut self, id: SuccessorRoleHashId) -> &mut SuccessorRoleHash {
        std::sync::Arc::make_mut(self.succ_role_hashes.get_mut_journaled(Id::new(id.raw)))
    }
    /// Pool-allocate a new successor-role hash, returning its stable id.
    #[inline]
    pub fn alloc_succ_role_hash(&mut self, v: SuccessorRoleHash) -> SuccessorRoleHashId {
        Id::new(self.succ_role_hashes.push(std::sync::Arc::new(v)).raw)
    }

    // =======================================================================
    // u15 CONTEXT-THREADED node successor-role / disjoint-role wiring.
    //
    // The PN-3 getters (`get_successor_role_iterator`, `get_successor_iterator`,
    // `has_successor_individual_node_id`, `get_disjoint_successor_role_iterator_id`)
    // are `&self` methods on `IndividualProcessNode`; they cannot resolve the
    // node's `use_succ_role_hash` / `use_disjoint_succ_role_hash` id against the
    // arena, so they return the empty placeholder iterator. These context-threaded
    // siblings DO resolve the id and seed the REAL iterator from the backing hash —
    // the un-defer wave routes the relocation loops through these (the same
    // `ctx.node_*` supersedes-`&mut self`-stub pattern as the W3b lazy-getters).
    // =======================================================================

    /// Context-threaded port of `CIndividualProcessNode::getSuccessorRoleHash(true)`
    /// (lazy-allocate the node's successor-role hash from the pool).
    pub fn node_successor_role_hash(&mut self, node: NodeId) -> SuccessorRoleHashId {
        if self.node(node).succ_role_hash.is_none() {
            let prev = self.node(node).prev_succ_role_hash;
            let new_id = self.alloc_succ_role_hash(SuccessorRoleHash::new());
            if prev.is_some() {
                let taken =
                    std::mem::replace(self.succ_role_hash_mut(prev), SuccessorRoleHash::new());
                self.succ_role_hash_mut(new_id)
                    .init_successor_role_hash(Some(&taken));
                *self.succ_role_hash_mut(prev) = taken;
            } else {
                self.succ_role_hash_mut(new_id)
                    .init_successor_role_hash(None);
            }
            let n = self.node_mut(node);
            n.succ_role_hash = new_id;
            n.use_succ_role_hash = new_id;
        }
        self.node(node).use_succ_role_hash
    }

    /// Context-threaded port of `CIndividualProcessNode::getSuccessorRoleIterator(indiID)`
    /// — seeds the real `SuccessorRoleIterator` from the node's successor-role hash.
    pub fn node_successor_role_iterator(
        &self,
        node: NodeId,
        indi_id: Cint64,
    ) -> SuccessorRoleIterator {
        let hash = self.node(node).use_succ_role_hash;
        if hash.is_none() {
            SuccessorRoleIterator::empty()
        } else {
            self.succ_role_hash(hash)
                .get_successor_role_iterator(indi_id)
        }
    }

    /// Context-threaded port of `CIndividualProcessNode::getSuccessorIterator()`.
    pub fn node_successor_iterator(&self, node: NodeId) -> SuccessorIterator {
        let hash = self.node(node).use_succ_role_hash;
        if hash.is_none() {
            SuccessorIterator::empty()
        } else {
            self.succ_role_hash(hash).get_successor_iterator()
        }
    }

    /// Context-threaded port of `CIndividualProcessNode::getConnectionSuccessorIterator`.
    pub fn node_connection_successor_iterator(
        &self,
        node: NodeId,
    ) -> ConnectionSuccessorSetIterator {
        let set = self.node(node).use_conn_succ_set;
        if set.is_none() {
            ConnectionSuccessorSetIterator::from_single(Cint64::MIN)
        } else {
            self.conn_succ_set(set).get_connection_successor_iterator()
        }
    }

    /// Context-threaded port of `CIndividualProcessNode::getReapplyRoleSuccessorHash(true)`.
    pub fn node_reapply_role_successor_hash(&mut self, node: NodeId) -> RoleSuccHashId {
        if self.node(node).reapply_role_succ_hash.is_none() {
            let prev = self.node(node).prev_reapply_role_succ_hash;
            let new_id = self.alloc_role_succ_hash(ReapplyRoleSuccessorHash::new(INVALID));
            if prev.is_some() {
                let taken = std::mem::replace(
                    self.role_succ_hash_mut(prev),
                    ReapplyRoleSuccessorHash::new(INVALID),
                );
                self.role_succ_hash_mut(new_id)
                    .init_role_successor_hash(Some(&taken));
                *self.role_succ_hash_mut(prev) = taken;
            } else {
                self.role_succ_hash_mut(new_id)
                    .init_role_successor_hash(None);
            }
            let n = self.node_mut(node);
            n.reapply_role_succ_hash = new_id;
            n.use_reapply_role_succ_hash = new_id;
        }
        self.node(node).use_reapply_role_succ_hash
    }

    /// Context-threaded port of `CIndividualProcessNode::getReapplyRoleSuccessorHash(false)`.
    pub fn node_reapply_role_successor_hash_existing(&self, node: NodeId) -> RoleSuccHashId {
        self.node(node).use_reapply_role_succ_hash
    }

    /// Context-threaded port of
    /// `CReapplyRoleSuccessorHash::getRoleSuccessorLinkIterator(CRole*, cint64*)`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: the hash iterator needs the context-owned
    /// edge arena to snapshot the intrusive `CIndividualLinkEdge` chain.
    pub fn role_succ_hash_role_successor_link_iterator_count(
        &self,
        hash: RoleSuccHashId,
        role: RoleId,
        link_count: Option<&mut Cint64>,
    ) -> RoleSuccessorLinkIterator {
        self.role_succ_hash(hash)
            .get_role_successor_link_iterator_count(&self.edges, role, link_count)
    }

    /// Context-threaded port of `CIndividualProcessNode::getRoleSuccessorLinkIterator`.
    pub fn node_role_successor_link_iterator(
        &self,
        node: NodeId,
        role: RoleId,
    ) -> RoleSuccessorLinkIterator {
        let hash = self.node(node).use_reapply_role_succ_hash;
        if hash.is_none() {
            return RoleSuccessorLinkIterator::empty();
        }
        self.role_succ_hash(hash)
            .get_role_successor_link_iterator(&self.edges, role)
    }

    /// Context-threaded port of `CIndividualProcessNode::getRoleSuccessorCount`.
    pub fn node_role_successor_count(&self, node: NodeId, role: RoleId) -> Cint64 {
        let hash = self.node(node).use_reapply_role_succ_hash;
        if hash.is_none() {
            return 0;
        }
        self.role_succ_hash(hash).get_role_successor_count(role)
    }

    /// Context-threaded port of `CIndividualProcessNode::getRoleSuccessorHistoryLinkIterator`.
    pub fn node_role_successor_history_link_iterator(
        &self,
        node: NodeId,
        role: RoleId,
        last_link: EdgeId,
    ) -> RoleSuccessorLinkIterator {
        let hash = self.node(node).use_reapply_role_succ_hash;
        if hash.is_none() {
            return RoleSuccessorLinkIterator::empty();
        }
        self.role_succ_hash(hash)
            .get_role_successor_history_link_iterator(&self.edges, role, last_link)
    }

    /// Context-threaded port of
    /// `CIndividualProcessNode::hasRoleSuccessorToIndividual(CRole*, cint64, bool)`.
    pub fn node_has_role_successor_to_individual_id(
        &mut self,
        source: NodeId,
        role: RoleId,
        destination_indi_id: Cint64,
        locateable: bool,
    ) -> bool {
        let hash = self.node(source).use_reapply_role_succ_hash;
        if hash.is_none() {
            return false;
        }
        let source_indi_id = self.node(source).individual_node_id();
        let locateable = locateable && self.node(source).reapply_role_succ_hash.is_some();
        let ProcessContext {
            ref nodes,
            ref edges,
            ref mut role_succ_hashes,
            ..
        } = *self;
        // Arc-COW split-borrow: `make_mut` deep-copies only when shared.
        std::sync::Arc::make_mut(role_succ_hashes.get_mut_journaled(Id::new(hash.raw)))
            .has_role_successor_to_individual(
                nodes,
                edges,
                role,
                source_indi_id,
                destination_indi_id,
                locateable,
            )
    }

    /// Context-threaded port of
    /// `CIndividualProcessNode::getRoleSuccessorToIndividualLink(CRole*, cint64, bool)`.
    pub fn node_get_role_successor_to_individual_link_id(
        &mut self,
        source: NodeId,
        role: RoleId,
        destination_indi_id: Cint64,
        locateable: bool,
    ) -> EdgeId {
        let hash = self.node(source).use_reapply_role_succ_hash;
        if hash.is_none() {
            return EdgeId::NONE;
        }
        let source_indi_id = self.node(source).individual_node_id();
        let locateable = locateable && self.node(source).reapply_role_succ_hash.is_some();
        let ProcessContext {
            ref nodes,
            ref edges,
            ref mut role_succ_hashes,
            ..
        } = *self;
        // Arc-COW split-borrow: `make_mut` deep-copies only when shared.
        std::sync::Arc::make_mut(role_succ_hashes.get_mut_journaled(Id::new(hash.raw)))
            .get_role_successor_to_individual_link(
                nodes,
                edges,
                role,
                source_indi_id,
                destination_indi_id,
                locateable,
            )
    }

    /// Context-threaded port of `CIndividualProcessNode::getRoleIterator`.
    pub fn node_role_iterator(&self, node: NodeId) -> RoleSuccessorIterator {
        let hash = self.node(node).use_reapply_role_succ_hash;
        if hash.is_none() {
            return RoleSuccessorIterator::empty();
        }
        self.role_succ_hash(hash).get_role_iterator()
    }

    /// Context-threaded port of `CIndividualProcessNode::getRoleReapplyIterator`.
    pub fn node_role_reapply_iterator(
        &mut self,
        node: NodeId,
        role: RoleId,
        clear_dynamic_reapply_queue: bool,
    ) -> ReapplyQueueIterator {
        let hash = self.node(node).use_reapply_role_succ_hash;
        if hash.is_none() {
            ReapplyQueueIterator::empty()
        } else {
            self.role_succ_hash_mut(hash)
                .get_role_reapply_iterator(role, clear_dynamic_reapply_queue)
        }
    }

    /// Context-threaded port of `CIndividualProcessNode::installIndividualLink`.
    ///
    /// Installs `link` into both the node's reapply role-successor hash and the
    /// topology successor-role hash, returning the per-role link count and filling
    /// `reapply_queue_it` with the role queue entries that must be re-fired for the
    /// newly created edge.
    pub fn node_install_individual_link(
        &mut self,
        source: NodeId,
        link: EdgeId,
        reapply_queue_it: &mut ReapplyQueueIterator,
    ) -> Cint64 {
        let role = self.edge(link).get_link_role();
        let destination = self.edge(link).get_destination_individual();
        let dest_id = self.node(destination).individual_node_id();

        let reapply_hash = self.node_reapply_role_successor_hash(source);
        let ProcessContext {
            ref nodes,
            ref mut role_succ_hashes,
            ref mut edges,
            ..
        } = *self;
        // Arc-COW split-borrow: `make_mut` deep-copies only when shared.
        let link_count =
            std::sync::Arc::make_mut(role_succ_hashes.get_mut_journaled(Id::new(reapply_hash.raw)))
                .insert_role_successor_link(nodes, edges, role, link, Some(reapply_queue_it));

        let succ_hash = self.node_successor_role_hash(source);
        self.succ_role_hash_mut(succ_hash)
            .insert_successor_role_link(dest_id, link);
        self.node_mut(source).last_added_link = link;
        link_count
    }

    /// Context-threaded port of `CIndividualProcessNode::installDisjointLink`.
    ///
    /// Installs the negation-disjoint edge into the source node's
    /// `CDisjointSuccessorRoleHash`, keyed by the opposite/destination individual
    /// id and the edge role.
    pub fn node_install_disjoint_link(&mut self, source: NodeId, link: DisjointEdgeId) {
        let destination = self.disjoint_edge(link).get_destination_individual();
        let dest_id = self.node(destination).individual_node_id();
        let disjoint_hash = self.node_disjoint_successor_role_hash(source);
        let ProcessContext {
            ref mut disjoint_succ_role_hashes,
            ref disjoint_edges,
            ..
        } = *self;
        disjoint_succ_role_hashes
            .get_mut_journaled(disjoint_hash)
            .insert_disjoint_successor_role_link(disjoint_edges, dest_id, link);
    }

    /// Context-threaded port of
    /// `CIndividualProcessNode::hasNegationDisjointToIndividual(CRole*, cint64)`.
    pub fn node_has_negation_disjoint_to_individual_id(
        &self,
        source: NodeId,
        role: RoleId,
        destination_indi_id: Cint64,
    ) -> bool {
        let hash = self.node(source).use_disjoint_succ_role_hash;
        hash.is_some()
            && self
                .disjoint_succ_role_hash(hash)
                .has_disjoint_successor_role_link(destination_indi_id, role)
    }

    /// Context-threaded port of
    /// `CDisjointSuccessorRoleHash::getDisjointSuccessorRoleLink` for a node.
    pub fn node_disjoint_successor_role_link(
        &self,
        source: NodeId,
        role: RoleId,
        destination_indi_id: Cint64,
    ) -> DisjointEdgeId {
        let hash = self.node(source).use_disjoint_succ_role_hash;
        if hash.is_none() {
            DisjointEdgeId::NONE
        } else {
            self.disjoint_succ_role_hash(hash)
                .get_disjoint_successor_role_link(destination_indi_id, role)
        }
    }

    /// Context-threaded port of `CIndividualProcessNode::removeDisjointLinks`.
    pub fn node_remove_disjoint_links(&mut self, source: NodeId, succ_indi_id: Cint64) {
        if self.node(source).use_disjoint_succ_role_hash.is_some() {
            let hash = self.node_disjoint_successor_role_hash(source);
            self.disjoint_succ_role_hash_mut(hash)
                .remove_disjoint_successor_role_links(succ_indi_id);
        }
    }

    /// Context-threaded port of `CIndividualProcessNode::getRoleReapplyQueue(role,true)`
    /// followed by `CReapplyQueue::addReapplyConceptDescriptor`.
    pub fn node_add_role_reapply_concept_descriptor(
        &mut self,
        node: NodeId,
        role: RoleId,
        reapply_con_desc: ReapplyConceptDescriptorId,
    ) {
        if reapply_con_desc.is_none() {
            return;
        }
        let hash = self.node_reapply_role_successor_hash(node);
        let static_descriptor = self
            .reapply_con_desc(reapply_con_desc)
            .is_static_descriptor();
        let previous_head = {
            let queue = self
                .role_succ_hash_mut(hash)
                .get_role_reapply_queue(role, true)
                .expect("create=true must return a role reapply queue");
            if static_descriptor {
                queue.static_reapply_des_linker
            } else {
                queue.dynamic_reapply_des_linker
            }
        };
        self.reapply_con_desc_mut(reapply_con_desc).next = previous_head;
        let queue = self
            .role_succ_hash_mut(hash)
            .get_role_reapply_queue(role, true)
            .expect("create=true must return a role reapply queue");
        if static_descriptor {
            queue.static_reapply_des_linker = reapply_con_desc;
        } else {
            queue.dynamic_reapply_des_linker = reapply_con_desc;
        }
    }

    /// Context-threaded port of `CReapplyQueue::hasConceptDescriptor` for a node's
    /// role-keyed queue.
    pub fn node_role_reapply_queue_has_concept_descriptor(
        &self,
        node: NodeId,
        role: RoleId,
        concept_descriptor: ConDescId,
    ) -> bool {
        let hash = self.node(node).use_reapply_role_succ_hash;
        if hash.is_none() {
            return false;
        }
        if let Some(data) = self
            .role_succ_hash(hash)
            .role_successor_data_hash
            .get(&role)
        {
            data.reapply_queue
                .has_concept_descriptor(self, concept_descriptor)
        } else {
            false
        }
    }

    /// Context-threaded port of `CIndividualProcessNode::hasSuccessorIndividualNode(indiID)`.
    pub fn node_has_successor_individual_node(&self, node: NodeId, indi_id: Cint64) -> bool {
        let hash = self.node(node).use_succ_role_hash;
        if hash.is_none() {
            false
        } else {
            self.succ_role_hash(hash)
                .has_successor_individual_node(indi_id)
        }
    }

    /// Context-threaded port of `CIndividualProcessNode::getDisjointSuccessorRoleIterator(succIndiId)`
    /// — seeds the real `distinct::DisjointSuccessorRoleIterator` from the node's
    /// disjoint-successor-role hash (already a real port in `process::distinct`).
    pub fn node_disjoint_successor_role_iterator(
        &self,
        node: NodeId,
        succ_indi_id: Cint64,
    ) -> DisjointSuccessorRoleIterator {
        let hash = self.node(node).use_disjoint_succ_role_hash;
        if hash.is_none() {
            DisjointSuccessorRoleIterator::new()
        } else {
            self.disjoint_succ_role_hash(hash)
                .get_disjoint_role_iterator(succ_indi_id)
        }
    }

    // =======================================================================
    // W3b CONTEXT-THREADED node lazy-getters (the `&mut self` C++
    // `getX()`-allocates-a-satellite keystone).
    //
    // In Konclude these are `CIndividualProcessNode::getX(bool create)` methods
    // that, on first access, bump-allocate a node-owned satellite from the task
    // pool (`if (!mX) { mX = new CX(mProcessContext); mX->initX(mPrevX); mUseX = mX; }`)
    // and return `mUseX`. In the arena port the allocation needs the
    // `ProcessContext` arena, which the `&mut self` node method cannot reach, so
    // the create path is lifted here as a context method threaded by `NodeId`.
    // These always allocate-if-absent (the C++ `create == true` path); the
    // `create == false` read is just `ctx.node(id).use_X`. The old `&mut self`
    // stub getters in `pn3`/`pn6` are superseded by these (see their `//
    // superseded by ctx.node_*` markers) — the un-defer wave calls these.
    //
    // KONCLUDE-PORT-NOTE[ownership]: the satellite and its `mPrev…` parent live in
    // the SAME arena, so `init…(prev)` cannot borrow both at once; the parent is
    // lifted out with `mem::replace` (a default placeholder), the new satellite is
    // initialised against it, then the parent is restored. Observable content is
    // identical; only the transient placeholder differs (single-threaded test).
    // =======================================================================

    /// Context-threaded port of `CIndividualProcessNode::getConnectionSuccessorSet(true)`.
    pub fn node_connection_successor_set(&mut self, node: NodeId) -> ConnectionSuccessorSetId {
        if self.node(node).conn_succ_set.is_none() {
            let prev = self.node(node).prev_conn_succ_set;
            let new_id = self.alloc_conn_succ_set(ConnectionSuccessorSet::new());
            if prev.is_some() {
                let taken =
                    std::mem::replace(self.conn_succ_set_mut(prev), ConnectionSuccessorSet::new());
                self.conn_succ_set_mut(new_id)
                    .init_connection_successor_set(Some(&taken));
                *self.conn_succ_set_mut(prev) = taken;
            } else {
                self.conn_succ_set_mut(new_id)
                    .init_connection_successor_set(None);
            }
            let n = self.node_mut(node);
            n.conn_succ_set = new_id;
            n.use_conn_succ_set = new_id;
        }
        self.node(node).use_conn_succ_set
    }

    /// Context-threaded port of `CIndividualProcessNode::getConnectionSuccessorSet(false)`.
    pub fn node_connection_successor_set_existing(&self, node: NodeId) -> ConnectionSuccessorSetId {
        self.node(node).use_conn_succ_set
    }

    /// Context-threaded port of `CIndividualProcessNode::getSuccessorNominalConnectionSet(true)`.
    pub fn node_successor_nominal_connection_set(
        &mut self,
        node: NodeId,
    ) -> SuccessorConnectedNominalSetId {
        if self.node(node).loc_nominal_connection_set.is_none() {
            let prev = self.node(node).use_nominal_connection_set;
            let new_id = self.alloc_nominal_conn_set(SuccessorConnectedNominalSet::new());
            if prev.is_some() {
                let taken = std::mem::replace(
                    self.nominal_conn_set_mut(prev),
                    SuccessorConnectedNominalSet::new(),
                );
                self.nominal_conn_set_mut(new_id)
                    .init_successor_connected_nominal_set(Some(&taken));
                *self.nominal_conn_set_mut(prev) = taken;
            } else {
                self.nominal_conn_set_mut(new_id)
                    .init_successor_connected_nominal_set(None);
            }
            let n = self.node_mut(node);
            n.loc_nominal_connection_set = new_id;
            n.use_nominal_connection_set = new_id;
        }
        self.node(node).use_nominal_connection_set
    }

    /// Context-threaded port of `CIndividualProcessNode::getSuccessorNominalConnectionSet(false)`.
    pub fn node_successor_nominal_connection_set_existing(
        &self,
        node: NodeId,
    ) -> SuccessorConnectedNominalSetId {
        self.node(node).use_nominal_connection_set
    }

    /// Context-threaded port of `CIndividualProcessNode::hasSuccessorConnectionToNominal`.
    pub fn node_has_successor_connection_to_nominal(
        &self,
        node: NodeId,
        nominal_id: Cint64,
    ) -> bool {
        let nom_conn_set = self.node_successor_nominal_connection_set_existing(node);
        nom_conn_set.is_some()
            && self
                .nominal_conn_set(nom_conn_set)
                .has_successor_connected_nominal(nominal_id)
    }

    /// Context-threaded port of `CIndividualProcessNode::addSuccessorConnectionToNominal`.
    pub fn node_add_successor_connection_to_nominal(
        &mut self,
        node: NodeId,
        nominal_id: Cint64,
    ) -> bool {
        let nom_conn_set = self.node_successor_nominal_connection_set(node);
        self.nominal_conn_set_mut(nom_conn_set)
            .add_successor_connected_nominal(nominal_id)
    }

    /// Snapshot of `getSuccessorNominalConnectionSet(false)->constBegin/constEnd`.
    pub fn node_successor_connected_nominals(&self, node: NodeId) -> Vec<Cint64> {
        let nom_conn_set = self.node_successor_nominal_connection_set_existing(node);
        if nom_conn_set.is_some() {
            self.nominal_conn_set(nom_conn_set).iter_snapshot()
        } else {
            Vec::new()
        }
    }

    /// Context-threaded port of
    /// `CIndividualProcessNode::getSuccessorIndividualATMOSTReactivationData(true)`.
    pub fn node_successor_individual_atmost_reactivation_data(
        &mut self,
        node: NodeId,
        create: bool,
    ) -> ATMOSTReactivationDataId {
        if self
            .node(node)
            .loc_succ_indi_atmost_reactivation_data
            .is_none()
            && create
        {
            let prev = self.node(node).use_succ_indi_atmost_reactivation_data;
            let new_id = self.alloc_successor_individual_atmost_reactivation_data(
                SuccessorIndividualATMOSTReactivationData::default(),
            );
            if prev.is_some() {
                let taken =
                    std::mem::take(self.successor_individual_atmost_reactivation_data_mut(prev));
                self.successor_individual_atmost_reactivation_data_mut(new_id)
                    .init_successor_individual_atmost_reactivation_data(Some(&taken));
                *self.successor_individual_atmost_reactivation_data_mut(prev) = taken;
            } else {
                self.successor_individual_atmost_reactivation_data_mut(new_id)
                    .init_successor_individual_atmost_reactivation_data(None);
            }
            let n = self.node_mut(node);
            n.loc_succ_indi_atmost_reactivation_data = new_id;
            n.use_succ_indi_atmost_reactivation_data = new_id;
        }
        self.node(node).use_succ_indi_atmost_reactivation_data
    }

    /// Context-threaded port of
    /// `CIndividualProcessNode::getSuccessorIndividualATMOSTReactivationData(false)`.
    pub fn node_successor_individual_atmost_reactivation_data_existing(
        &self,
        node: NodeId,
    ) -> ATMOSTReactivationDataId {
        self.node(node).use_succ_indi_atmost_reactivation_data
    }

    /// Context-threaded port of `CIndividualProcessNode::getDatatypesValueSpaceData(true)`.
    pub fn node_datatypes_value_space_data(
        &mut self,
        node: NodeId,
        create: bool,
    ) -> DatatypesValueSpaceDataId {
        if self.node(node).loc_datatypes_value_space_data.is_none() && create {
            let prev = self.node(node).use_datatypes_value_space_data;
            let new_id = self.alloc_datatypes_value_space_data(DatatypesValueSpaceData::default());
            if prev.is_some() {
                let taken = std::mem::take(self.datatypes_value_space_data_mut(prev));
                self.datatypes_value_space_data_mut(new_id)
                    .init_datatypes_value_space_data(Some(&taken));
                *self.datatypes_value_space_data_mut(prev) = taken;
            } else {
                self.datatypes_value_space_data_mut(new_id)
                    .init_datatypes_value_space_data(None);
            }
            let n = self.node_mut(node);
            n.loc_datatypes_value_space_data = new_id;
            n.use_datatypes_value_space_data = new_id;
        }
        self.node(node).use_datatypes_value_space_data
    }

    /// Context-threaded port of `CIndividualProcessNode::getDatatypesValueSpaceData(false)`.
    pub fn node_datatypes_value_space_data_existing(
        &self,
        node: NodeId,
    ) -> DatatypesValueSpaceDataId {
        self.node(node).use_datatypes_value_space_data
    }

    /// Context-threaded port of `CIndividualProcessNode::getBlockingFollowSet`.
    pub fn node_blocking_follow_set(
        &mut self,
        node: NodeId,
        create_or_localize: bool,
    ) -> BlockingFollowSetId {
        let needs_alloc = self.node(node).sig_block_follow_set.is_none() && create_or_localize;
        if needs_alloc {
            let prev_set_id = self.node(node).prev_sig_block_follow_set;
            let current_tag = self.used_process_tagger().get_current_blocking_follow_tag();
            let mut new_set = BlockingFollowSet::new();
            if prev_set_id.is_some() {
                let prev_set = self.blocking_follow_set(prev_set_id).clone();
                new_set.init_blocking_follow_set(Some(&prev_set), current_tag);
            } else {
                new_set.init_blocking_follow_set(None, current_tag);
            }
            let new_set_id = self.alloc_blocking_follow_set(new_set);
            let n = self.node_mut(node);
            n.sig_block_follow_set = new_set_id;
            n.use_sig_block_follow_set = new_set_id;
        }
        self.node(node).use_sig_block_follow_set
    }

    /// Context-threaded port of `CIndividualProcessNode::getBlockingFollowSet(false)`.
    pub fn node_blocking_follow_set_existing(&self, node: NodeId) -> BlockingFollowSetId {
        self.node(node).use_sig_block_follow_set
    }

    /// Context-threaded port of `CIndividualProcessNode::hasBlockingFollower`.
    pub fn node_has_blocking_follower(&self, node: NodeId) -> bool {
        let follow_set = self.node_blocking_follow_set_existing(node);
        follow_set.is_some() && !self.blocking_follow_set(follow_set).is_empty()
    }

    /// Port of `getBlockingFollowSet(true)->insert(individualNodeID)`.
    pub fn node_add_blocking_follower(&mut self, node: NodeId, individual_node_id: Cint64) -> bool {
        let follow_set = self.node_blocking_follow_set(node, true);
        self.blocking_follow_set_mut(follow_set)
            .insert(individual_node_id)
    }

    /// Port of `getBlockingFollowSet(true)->remove(individualNodeID)`.
    pub fn node_remove_blocking_follower(
        &mut self,
        node: NodeId,
        individual_node_id: Cint64,
    ) -> bool {
        let follow_set = self.node_blocking_follow_set(node, true);
        self.blocking_follow_set_mut(follow_set)
            .remove(individual_node_id)
    }

    /// Snapshot of `getBlockingFollowSet(false)->constBegin/constEnd`.
    pub fn node_blocking_followers(&self, node: NodeId) -> Vec<Cint64> {
        let follow_set = self.node_blocking_follow_set_existing(node);
        if follow_set.is_some() {
            self.blocking_follow_set(follow_set).iter_snapshot()
        } else {
            Vec::new()
        }
    }

    /// Context-threaded port of `CIndividualProcessNode::getIncrementalExpansionData`.
    pub fn node_incremental_expansion_data(
        &mut self,
        node: NodeId,
        create: bool,
    ) -> IncrementalExpansionDataId {
        let needs_alloc = self.node(node).loc_inc_exp_data.is_none() && create;
        if needs_alloc {
            let prev_data_id = self.node(node).use_inc_exp_data;
            let mut new_data = IndividualNodeIncrementalExpansionData::new(INVALID);
            if prev_data_id.is_some() {
                let prev_data = self.inc_exp_data(prev_data_id).clone();
                new_data.init_incremental_expansion_data(Some(&prev_data));
            } else {
                new_data.init_incremental_expansion_data(None);
            }
            let new_data_id = self.alloc_inc_exp_data(new_data);
            let n = self.node_mut(node);
            n.loc_inc_exp_data = new_data_id;
            n.use_inc_exp_data = new_data_id;
        }
        self.node(node).use_inc_exp_data
    }

    /// Context-threaded port of `CIndividualProcessNode::getIncrementalExpansionData(false)`.
    pub fn node_incremental_expansion_data_existing(
        &self,
        node: NodeId,
    ) -> IncrementalExpansionDataId {
        self.node(node).use_inc_exp_data
    }

    /// Context-threaded port of
    /// `CIndividualProcessNode::getNominalCachingLossReactivationData`.
    pub fn node_nominal_caching_loss_reactivation_data(
        &mut self,
        node: NodeId,
        create: bool,
    ) -> NominalCachingLossReactivationDataId {
        if node.is_none() {
            return NominalCachingLossReactivationDataId::NONE;
        }
        if self.node(node).loc_reactivation_data.is_none() && create {
            let prev = self.node(node).use_reactivation_data;
            let nominal_id = self.node(node).individual_node_id();
            let new_id = self.alloc_nominal_caching_loss_reactivation_data(
                NominalCachingLossReactivationData::new(INVALID),
            );
            if prev.is_some() {
                let taken = std::mem::replace(
                    self.nominal_caching_loss_reactivation_data_mut(prev),
                    NominalCachingLossReactivationData::new(INVALID),
                );
                self.nominal_caching_loss_reactivation_data_mut(new_id)
                    .init_nominal_caching_loss_reactivation_data(nominal_id, Some(&taken));
                *self.nominal_caching_loss_reactivation_data_mut(prev) = taken;
            } else {
                self.nominal_caching_loss_reactivation_data_mut(new_id)
                    .init_nominal_caching_loss_reactivation_data(nominal_id, None);
            }
            let n = self.node_mut(node);
            n.loc_reactivation_data = new_id;
            n.use_reactivation_data = new_id;
        }
        self.node(node).use_reactivation_data
    }

    /// Context-threaded port of `CIndividualProcessNode::removeIndividualLink`.
    pub fn node_remove_individual_link(&mut self, node: NodeId, link: EdgeId) {
        let role = self.edge(link).get_link_role();
        let reapply_hash = self.node_reapply_role_successor_hash(node);
        let ProcessContext {
            ref nodes,
            ref mut role_succ_hashes,
            ref mut edges,
            ..
        } = *self;
        // Arc-COW split-borrow: `make_mut` deep-copies only when shared.
        std::sync::Arc::make_mut(role_succ_hashes.get_mut_journaled(Id::new(reapply_hash.raw)))
            .remove_role_successor_link_by_link(nodes, edges, role, link);
    }

    /// Context-threaded port of `CIndividualProcessNode::removeIndividualConnection`.
    pub fn node_remove_individual_connection(&mut self, node: NodeId, indi: NodeId) {
        let indi_id = self.node(indi).individual_node_id();
        if self.node(node).use_succ_role_hash.is_some() {
            let succ_hash = self.node_successor_role_hash(node);
            self.succ_role_hash_mut(succ_hash).remove_successor(indi_id);
        }
        if self.node(node).use_conn_succ_set.is_some() {
            let conn_set = self.node_connection_successor_set(node);
            self.conn_succ_set_mut(conn_set).remove_connection(indi_id);
        }
    }

    /// Context-threaded port of `CIndividualProcessNode::getReapplyConceptLabelSet(true)`.
    pub fn node_reapply_concept_label_set(&mut self, node: NodeId) -> LabelSetId {
        if self.node(node).reapply_con_label_set.is_none() {
            let prev = self.node(node).prev_reapply_con_label_set;
            let new_id = self.alloc_label_set(ReapplyConceptLabelSet::new(INVALID));
            if prev.is_some() {
                let taken = std::mem::replace(
                    self.label_set_mut(prev),
                    ReapplyConceptLabelSet::new(INVALID),
                );
                self.label_set_mut(new_id)
                    .init_concept_label_set(Some((prev, &taken)));
                *self.label_set_mut(prev) = taken;
            } else {
                self.label_set_mut(new_id).init_concept_label_set(None);
            }
            let n = self.node_mut(node);
            n.reapply_con_label_set = new_id;
            n.use_reapply_con_label_set = new_id;
        }
        self.node(node).use_reapply_con_label_set
    }

    fn label_set_additional_alias_map(
        &self,
        alias: LabelSetMapAlias,
    ) -> Option<&HashMap<Cint64, ConceptDescriptorDependencyReapplyData>> {
        let label_set = self.label_set(alias.label_set);
        match alias.which {
            AdditionalMapSlot::Main => Some(&label_set.concept_des_dep_map),
            AdditionalMapSlot::Additional => match &label_set.additional_concept_des_dep_map {
                AdditionalDesDepMapRef::Null => None,
                AdditionalDesDepMapRef::Owned(m) => Some(m),
                AdditionalDesDepMapRef::Shared(next_alias) => {
                    self.label_set_additional_alias_map(*next_alias)
                }
            },
        }
    }

    /// Context-threaded read of `mAdditionalConceptDesDepMap->size()`, following
    /// shared aliases exactly like the C++ raw map pointer.
    pub fn label_set_additional_size(&self, label_set: LabelSetId) -> usize {
        match &self.label_set(label_set).additional_concept_des_dep_map {
            AdditionalDesDepMapRef::Null => 0,
            AdditionalDesDepMapRef::Owned(m) => m.len(),
            AdditionalDesDepMapRef::Shared(alias) => self
                .label_set_additional_alias_map(*alias)
                .map_or(0, |m| m.len()),
        }
    }

    /// Context-threaded read of `mAdditionalConceptDesDepMap->value(conTag)`.
    pub fn label_set_additional_get_cloned(
        &self,
        label_set: LabelSetId,
        con_tag: Cint64,
    ) -> Option<ConceptDescriptorDependencyReapplyData> {
        let clone_data =
            |d: &ConceptDescriptorDependencyReapplyData| ConceptDescriptorDependencyReapplyData {
                concept_descriptor: d.concept_descriptor,
                pos_neg_reapply_queue: d.pos_neg_reapply_queue,
            };
        match &self.label_set(label_set).additional_concept_des_dep_map {
            AdditionalDesDepMapRef::Null => None,
            AdditionalDesDepMapRef::Owned(m) => m.get(&con_tag).map(clone_data),
            AdditionalDesDepMapRef::Shared(alias) => self
                .label_set_additional_alias_map(*alias)
                .and_then(|m| m.get(&con_tag).map(clone_data)),
        }
    }

    fn label_set_snapshot_sorted_entries(
        m: &HashMap<Cint64, ConceptDescriptorDependencyReapplyData>,
    ) -> Vec<LabelSetMapEntry> {
        let mut entries: Vec<LabelSetMapEntry> = m
            .iter()
            .map(|(k, v)| LabelSetMapEntry {
                key: *k,
                concept_descriptor: v.concept_descriptor,
                pos_neg_reapply_queue: v.pos_neg_reapply_queue,
            })
            .collect();
        entries.sort_by_key(|e| e.key);
        entries
    }

    /// Context-threaded port of `CReapplyConceptLabelSet::getConceptLabelSetIterator`
    /// that can follow shared additional-map aliases through the label-set arena.
    pub fn label_set_concept_label_set_iterator(
        &self,
        label_set: LabelSetId,
        get_sorted: bool,
        get_dependencies: bool,
        get_all_structure: bool,
    ) -> super::reapply_sat::ReapplyConceptLabelSetIterator {
        let label_set_ref = self.label_set(label_set);
        if get_sorted || get_dependencies || get_all_structure {
            let main = Self::label_set_snapshot_sorted_entries(&label_set_ref.concept_des_dep_map);
            let additional = match &label_set_ref.additional_concept_des_dep_map {
                AdditionalDesDepMapRef::Null => Vec::new(),
                AdditionalDesDepMapRef::Owned(m) => Self::label_set_snapshot_sorted_entries(m),
                AdditionalDesDepMapRef::Shared(alias) => self
                    .label_set_additional_alias_map(*alias)
                    .map_or_else(Vec::new, Self::label_set_snapshot_sorted_entries),
            };
            super::reapply_sat::ReapplyConceptLabelSetIterator::new(
                label_set_ref.concept_count,
                ConDescId::NONE,
                main,
                additional,
                !get_all_structure,
            )
        } else {
            super::reapply_sat::ReapplyConceptLabelSetIterator::new(
                label_set_ref.concept_count,
                label_set_ref.concept_des_linker,
                Vec::new(),
                Vec::new(),
                true,
            )
        }
    }

    /// Context-threaded port of `CIndividualProcessNode::getConceptReapplyIterator`.
    pub fn node_concept_reapply_iterator(
        &mut self,
        node: NodeId,
        concept: ConceptId,
        concept_negation: bool,
        clear_dynamic_reapply_queue: bool,
    ) -> CondensedReapplyQueueIterator {
        self.node_concept_reapply_iterator_by_tag(
            node,
            concept.raw,
            concept_negation,
            clear_dynamic_reapply_queue,
        )
    }

    /// Context-threaded by-tag port of `CIndividualProcessNode::getConceptReapplyIterator`.
    pub fn node_concept_reapply_iterator_by_tag(
        &mut self,
        node: NodeId,
        con_tag: Cint64,
        concept_negation: bool,
        clear_dynamic_reapply_queue: bool,
    ) -> CondensedReapplyQueueIterator {
        let label_set = self.node(node).use_reapply_con_label_set;
        if label_set.is_none() {
            return CondensedReapplyQueueIterator::new();
        }
        let head = {
            let queue_opt = self
                .label_set_mut(label_set)
                .get_concept_reapply_queue_by_tag(con_tag, false);
            let _ = concept_negation;
            if let Some(queue) = queue_opt {
                let head = queue.dynamic_pos_neg_reapply_des_linker();
                if clear_dynamic_reapply_queue {
                    queue.set_dynamic_pos_neg_reapply_des_linker(
                        CondensedReapplyConceptDescriptorId::NONE,
                    );
                }
                head
            } else {
                CondensedReapplyConceptDescriptorId::NONE
            }
        };
        CondensedReapplyQueueIterator::new_only_positive(self, head, !concept_negation)
    }

    /// Context-threaded port helper for the
    /// `getConceptDescriptorAndReapplyQueue(..., reapplyQueue)` +
    /// `getConceptReapplyIterator(bindingConDes)` sequence when the caller has a
    /// real concept tag. The lookup and queue-head extraction use the same label
    /// set entry; the iterator is built after the label-set borrow is released.
    pub fn node_concept_descriptor_and_reapply_iterator_by_tag(
        &mut self,
        node: NodeId,
        con_tag: Cint64,
        concept_negation: bool,
        clear_dynamic_reapply_queue: bool,
        con_des: &mut ConDescId,
        dep_track_point: &mut TrackPointId,
    ) -> (bool, CondensedReapplyQueueIterator) {
        let label_set = self.node(node).use_reapply_con_label_set;
        if label_set.is_none() {
            *con_des = ConDescId::NONE;
            *dep_track_point = TrackPointId::NONE;
            return (false, CondensedReapplyQueueIterator::new());
        }
        let (contained, head) = {
            let label_set_ref = self.label_set_mut(label_set);
            let mut queue_empty = true;
            let contained = label_set_ref.get_concept_descriptor_and_reapply_queue_state_by_tag(
                con_tag,
                con_des,
                dep_track_point,
                &mut queue_empty,
            );
            let head = if contained && !queue_empty {
                label_set_ref
                    .take_concept_reapply_queue_head_by_tag(con_tag, clear_dynamic_reapply_queue)
            } else {
                CondensedReapplyConceptDescriptorId::NONE
            };
            (contained, head)
        };
        (
            contained,
            CondensedReapplyQueueIterator::new_only_positive(self, head, !concept_negation),
        )
    }

    /// Context-threaded port of `getConceptReapplyQueue(..., true)->addReapplyConceptDescriptor`.
    pub fn node_add_concept_reapply_concept_descriptor(
        &mut self,
        node: NodeId,
        concept: ConceptId,
        concept_negation: bool,
        reapply_con_desc: CondensedReapplyConceptDescriptorId,
    ) {
        self.node_add_concept_reapply_concept_descriptor_by_tag(
            node,
            concept.raw,
            concept_negation,
            reapply_con_desc,
        );
    }

    /// Context-threaded by-tag port of
    /// `getConceptReapplyQueue(..., true)->addReapplyConceptDescriptor`.
    pub fn node_add_concept_reapply_concept_descriptor_by_tag(
        &mut self,
        node: NodeId,
        con_tag: Cint64,
        concept_negation: bool,
        reapply_con_desc: CondensedReapplyConceptDescriptorId,
    ) {
        if reapply_con_desc.is_none() {
            return;
        }
        let label_set = self.node_reapply_concept_label_set(node);
        let previous_head = {
            let queue = self
                .label_set_mut(label_set)
                .get_concept_reapply_queue_by_tag(con_tag, true)
                .expect("create=true must return a concept reapply queue");
            let _ = concept_negation;
            queue.dynamic_pos_neg_reapply_des_linker()
        };
        self.cond_reapply_con_desc_mut(reapply_con_desc).next = previous_head;
        let queue = self
            .label_set_mut(label_set)
            .get_concept_reapply_queue_by_tag(con_tag, true)
            .expect("create=true must return a concept reapply queue");
        queue.set_dynamic_pos_neg_reapply_des_linker(reapply_con_desc);
    }

    /// Context-threaded port of `CCondensedReapplyQueue::hasConceptDescriptor`.
    pub fn node_concept_reapply_queue_has_concept_descriptor(
        &self,
        node: NodeId,
        concept: ConceptId,
        concept_negation: bool,
        concept_descriptor: ConDescId,
    ) -> bool {
        self.node_concept_reapply_queue_has_concept_descriptor_by_tag(
            node,
            concept.raw,
            concept_negation,
            concept_descriptor,
        )
    }

    /// Context-threaded by-tag port of `CCondensedReapplyQueue::hasConceptDescriptor`.
    pub fn node_concept_reapply_queue_has_concept_descriptor_by_tag(
        &self,
        node: NodeId,
        con_tag: Cint64,
        concept_negation: bool,
        concept_descriptor: ConDescId,
    ) -> bool {
        let label_set = self.node(node).use_reapply_con_label_set;
        if label_set.is_none() {
            return false;
        }
        if let Some(data) = self.label_set(label_set).concept_des_dep_map.get(&con_tag) {
            data.pos_neg_reapply_queue
                .has_concept_descriptor(self, concept_descriptor)
        } else {
            let _ = concept_negation;
            false
        }
    }

    /// Context-threaded port of `CIndividualProcessNode::getDistinctHash(true)`.
    pub fn node_distinct_hash(&mut self, node: NodeId) -> DistinctHashId {
        if self.node(node).distinct_hash.is_none() {
            let prev = self.node(node).prev_distinct_hash;
            let new_id = self.alloc_distinct_hash(DistinctHash::new());
            if prev.is_some() {
                let taken = std::mem::replace(self.distinct_hash_mut(prev), DistinctHash::new());
                self.distinct_hash_mut(new_id)
                    .init_distinct_hash(Some(&taken));
                *self.distinct_hash_mut(prev) = taken;
            } else {
                self.distinct_hash_mut(new_id).init_distinct_hash(None);
            }
            let n = self.node_mut(node);
            n.distinct_hash = new_id;
            n.use_distinct_hash = new_id;
        }
        self.node(node).use_distinct_hash
    }

    /// Context-threaded port of `CIndividualProcessNode::getDistinctHash(false)`.
    pub fn node_distinct_hash_existing(&self, node: NodeId) -> DistinctHashId {
        self.node(node).use_distinct_hash
    }

    /// Context-threaded port of `CIndividualProcessNode::getDisjointSuccessorRoleHash(true)`.
    pub fn node_disjoint_successor_role_hash(
        &mut self,
        node: NodeId,
    ) -> DisjointSuccessorRoleHashId {
        if self.node(node).disjoint_succ_role_hash.is_none() {
            let prev = self.node(node).prev_disjoint_succ_role_hash;
            let new_id = self.alloc_disjoint_succ_role_hash(DisjointSuccessorRoleHash::new());
            if prev.is_some() {
                let taken = std::mem::replace(
                    self.disjoint_succ_role_hash_mut(prev),
                    DisjointSuccessorRoleHash::new(),
                );
                self.disjoint_succ_role_hash_mut(new_id)
                    .init_disjoint_successor_role_hash(Some(&taken));
                *self.disjoint_succ_role_hash_mut(prev) = taken;
            } else {
                self.disjoint_succ_role_hash_mut(new_id)
                    .init_disjoint_successor_role_hash(None);
            }
            let n = self.node_mut(node);
            n.disjoint_succ_role_hash = new_id;
            n.use_disjoint_succ_role_hash = new_id;
        }
        self.node(node).use_disjoint_succ_role_hash
    }

    /// Context-threaded port of `CIndividualProcessNode::getConceptVariableBindingPathSetHash(true)`.
    pub fn node_concept_variable_binding_path_set_hash(
        &mut self,
        node: NodeId,
    ) -> ConceptVariableBindingPathSetHashId {
        if self.node(node).concept_var_bind_path_set_hash.is_none() {
            let prev = self.node(node).prev_concept_var_bind_path_set_hash;
            let new_id = self
                .alloc_con_var_bind_path_set_hash(ConceptVariableBindingPathSetHash::new(INVALID));
            if prev.is_some() {
                let taken = std::mem::replace(
                    self.con_var_bind_path_set_hash_mut(prev),
                    ConceptVariableBindingPathSetHash::new(INVALID),
                );
                self.con_var_bind_path_set_hash_mut(new_id)
                    .init_concept_variable_binding_path_set_hash(Some(&taken));
                *self.con_var_bind_path_set_hash_mut(prev) = taken;
            } else {
                self.con_var_bind_path_set_hash_mut(new_id)
                    .init_concept_variable_binding_path_set_hash(None);
            }
            let n = self.node_mut(node);
            n.concept_var_bind_path_set_hash = new_id;
            n.use_concept_var_bind_path_set_hash = new_id;
        }
        self.node(node).use_concept_var_bind_path_set_hash
    }

    /// Context-threaded port of `CIndividualProcessNode::getConceptPropagationBindingSetHash(true)`.
    pub fn node_concept_propagation_binding_set_hash(
        &mut self,
        node: NodeId,
    ) -> ConceptPropagationBindingSetHashId {
        if self.node(node).concept_prop_binding_set_hash.is_none() {
            let prev = self.node(node).prev_concept_prop_binding_set_hash;
            let new_id = self
                .alloc_con_prop_binding_set_hash(ConceptPropagationBindingSetHash::new(INVALID));
            if prev.is_some() {
                let taken = std::mem::replace(
                    self.con_prop_binding_set_hash_mut(prev),
                    ConceptPropagationBindingSetHash::new(INVALID),
                );
                self.con_prop_binding_set_hash_mut(new_id)
                    .init_concept_propagation_binding_set_hash(Some(&taken));
                *self.con_prop_binding_set_hash_mut(prev) = taken;
            } else {
                self.con_prop_binding_set_hash_mut(new_id)
                    .init_concept_propagation_binding_set_hash(None);
            }
            let n = self.node_mut(node);
            n.concept_prop_binding_set_hash = new_id;
            n.use_concept_prop_binding_set_hash = new_id;
        }
        self.node(node).use_concept_prop_binding_set_hash
    }

    /// Context-threaded port of `CIndividualProcessNode::getConceptRepresentativePropagationSetHash(true)`.
    pub fn node_concept_representative_propagation_set_hash(
        &mut self,
        node: NodeId,
    ) -> ConceptRepresentativePropagationSetHashId {
        if self.node(node).concept_rep_prop_set_hash.is_none() {
            let prev = self.node(node).prev_concept_rep_prop_set_hash;
            let new_id = self
                .alloc_con_rep_prop_set_hash(ConceptRepresentativePropagationSetHash::new(INVALID));
            if prev.is_some() {
                let taken = std::mem::replace(
                    self.con_rep_prop_set_hash_mut(prev),
                    ConceptRepresentativePropagationSetHash::new(INVALID),
                );
                self.con_rep_prop_set_hash_mut(new_id)
                    .init_concept_representative_propagation_set_hash(Some(&taken));
                *self.con_rep_prop_set_hash_mut(prev) = taken;
            } else {
                self.con_rep_prop_set_hash_mut(new_id)
                    .init_concept_representative_propagation_set_hash(None);
            }
            let n = self.node_mut(node);
            n.concept_rep_prop_set_hash = new_id;
            n.use_concept_rep_prop_set_hash = new_id;
        }
        self.node(node).use_concept_rep_prop_set_hash
    }
}

impl Default for ProcessContext {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::super::databox::ProcessingDataBox;
    use super::super::grounding_hash::{
        ConceptNominalSchemaGroundingData, ConceptNominalSchemaGroundingHash,
    };
    use super::super::individual_process_linker::IndividualProcessNodeLinker;
    use super::super::representative::{
        RepresentativeVariableBindingPathHash, RepresentativeVariableBindingPathSetData,
        RepresentativeVariableBindingPathSetHash,
    };
    use super::super::varbind::{
        VariableBindingPath, VariableBindingPathMergingHash, VariableBindingPathMergingHashData,
    };
    use super::*;

    #[test]
    fn processing_data_box_grounding_hash_localizes_and_copies_previous_entries() {
        let mut ctx = ProcessContext::new();
        let mut data_box = ProcessingDataBox::new();
        let mut data = ConceptNominalSchemaGroundingData::new();
        data.set_grounding_concept(ConceptId::new(13))
            .set_grounded_concept(ConceptId::new(17))
            .add_binded_nominal_schema_concept(ConceptId::new(19));

        let mut prev_hash = ConceptNominalSchemaGroundingHash::new(INVALID);
        prev_hash.insert(data.clone());
        let prev_hash_id = ctx.alloc_grounding_hash(prev_hash);
        data_box.use_grounding_hash = prev_hash_id;

        let localized_hash_id =
            ctx.processing_data_box_concept_nominal_schema_grounding_hash(&mut data_box, true);

        assert!(localized_hash_id.is_some());
        assert_ne!(localized_hash_id, prev_hash_id);
        assert_eq!(data_box.loc_grounding_hash, localized_hash_id);
        assert_eq!(data_box.use_grounding_hash, localized_hash_id);
        assert_eq!(
            ctx.grounding_hash(localized_hash_id)
                .value(&data)
                .expect("copied grounding entry")
                .get_grounded_concept(),
            ConceptId::new(17)
        );
        assert_eq!(
            ctx.grounding_hash(prev_hash_id)
                .value(&data)
                .expect("previous grounding entry restored")
                .get_grounded_concept(),
            ConceptId::new(17)
        );
        assert_eq!(
            ctx.processing_data_box_concept_nominal_schema_grounding_hash(&mut data_box, false),
            localized_hash_id
        );
    }

    #[test]
    fn processing_data_box_marker_individual_node_hash_localizes_and_copies_previous_entries() {
        let mut ctx = ProcessContext::new();
        let mut data_box = ProcessingDataBox::new();
        let marker_concept = ConceptId::new(23);
        let prev_data = ctx.alloc_marker_indi_node_data(MarkerIndividualNodeData::new(INVALID));
        let mut prev_hash = MarkerIndividualNodeHash::new(INVALID);
        prev_hash.marker_individual_node_hash.insert(
            marker_concept,
            MarkerIndividualNodeHashData {
                marker_indi_node_data: prev_data,
                prev_marker_indi_node_data: prev_data,
            },
        );
        let prev_hash_id = ctx.alloc_marker_indi_node_hash(prev_hash);
        data_box.use_marker_indi_node_hash = prev_hash_id;

        let localized_hash_id =
            ctx.processing_data_box_marker_individual_node_hash(&mut data_box, true);

        assert!(localized_hash_id.is_some());
        assert_ne!(localized_hash_id, prev_hash_id);
        assert_eq!(data_box.loc_marker_indi_node_hash, localized_hash_id);
        assert_eq!(data_box.use_marker_indi_node_hash, localized_hash_id);

        let copied_data = ctx
            .marker_indi_node_hash(localized_hash_id)
            .marker_individual_node_hash
            .get(&marker_concept)
            .copied()
            .expect("copied marker individual node bucket");
        assert!(copied_data.marker_indi_node_data.is_none());
        assert_eq!(copied_data.prev_marker_indi_node_data, prev_data);

        let prev_bucket = ctx
            .marker_indi_node_hash(prev_hash_id)
            .marker_individual_node_hash
            .get(&marker_concept)
            .copied()
            .expect("previous marker individual node bucket restored");
        assert_eq!(prev_bucket.marker_indi_node_data, prev_data);
        assert_eq!(prev_bucket.prev_marker_indi_node_data, prev_data);
        assert_eq!(
            ctx.processing_data_box_marker_individual_node_hash(&mut data_box, false),
            localized_hash_id
        );
    }

    #[test]
    fn processing_data_box_representative_variable_binding_path_set_hash_localizes_and_copies_previous_entries(
    ) {
        let mut ctx = ProcessContext::new();
        let mut data_box = ProcessingDataBox::new();
        let tag = ctx.used_process_tagger().get_current_localization_tag();
        let rep_set_data = ctx.alloc_rep_var_bind_path_set_data(
            RepresentativeVariableBindingPathSetData::new(INVALID, tag),
        );
        ctx.rep_var_bind_path_set_data_mut(rep_set_data)
            .set_representative_id(23)
            .add_key_signature_value(29);
        let key = ctx
            .rep_var_bind_path_set_data(rep_set_data)
            .get_representative_key();
        let prev_hash_id = ctx.alloc_rep_var_bind_path_set_hash(
            RepresentativeVariableBindingPathSetHash::new(INVALID),
        );
        RepresentativeVariableBindingPathSetHash::insert_representative_variable_binding_path_set_data(
            &mut ctx,
            prev_hash_id,
            rep_set_data,
        );
        data_box.use_rep_var_bind_path_set_hash = prev_hash_id;

        let localized_hash_id = ctx
            .processing_data_box_representative_variable_binding_path_set_hash(&mut data_box, true);

        assert!(localized_hash_id.is_some());
        assert_ne!(localized_hash_id, prev_hash_id);
        assert_eq!(data_box.loc_rep_var_bind_path_set_hash, localized_hash_id);
        assert_eq!(data_box.use_rep_var_bind_path_set_hash, localized_hash_id);

        let localized_bucket = ctx
            .rep_var_bind_path_set_hash(localized_hash_id)
            .map
            .get(&key)
            .copied()
            .expect("copied representative path-set bucket");
        assert_eq!(localized_bucket.use_data_linker, rep_set_data);
        assert!(localized_bucket.loc_data_linker.is_none());

        let prev_bucket = ctx
            .rep_var_bind_path_set_hash(prev_hash_id)
            .map
            .get(&key)
            .copied()
            .expect("previous representative path-set bucket restored");
        assert_eq!(prev_bucket.use_data_linker, rep_set_data);
        assert_eq!(prev_bucket.loc_data_linker, rep_set_data);
        assert_eq!(
            ctx.processing_data_box_representative_variable_binding_path_set_hash(
                &mut data_box,
                false,
            ),
            localized_hash_id
        );
    }

    #[test]
    fn processing_data_box_representative_variable_binding_path_hash_localizes_and_copies_previous_entries(
    ) {
        let mut ctx = ProcessContext::new();
        let mut data_box = ProcessingDataBox::new();
        let path = ctx.alloc_vbpath(VariableBindingPath::new());
        ctx.vbpath_mut(path).set_propagation_id(31);
        let prev_hash_id =
            ctx.alloc_rep_var_bind_path_hash(RepresentativeVariableBindingPathHash::new(INVALID));
        let rep_data =
            RepresentativeVariableBindingPathHash::get_representative_variable_binding_path_set_data(
                &mut ctx,
                prev_hash_id,
                path,
                true,
            );
        data_box.use_rep_var_bind_path_hash = prev_hash_id;

        let localized_hash_id =
            ctx.processing_data_box_representative_variable_binding_path_hash(&mut data_box, true);

        assert!(localized_hash_id.is_some());
        assert_ne!(localized_hash_id, prev_hash_id);
        assert_eq!(data_box.loc_rep_var_bind_path_hash, localized_hash_id);
        assert_eq!(data_box.use_rep_var_bind_path_hash, localized_hash_id);

        let localized_bucket = ctx
            .rep_var_bind_path_hash(localized_hash_id)
            .map
            .get(&31)
            .copied()
            .expect("copied representative path bucket");
        assert_eq!(localized_bucket.use_data_linker, rep_data);
        assert!(localized_bucket.loc_data_linker.is_none());

        let prev_bucket = ctx
            .rep_var_bind_path_hash(prev_hash_id)
            .map
            .get(&31)
            .copied()
            .expect("previous representative path bucket restored");
        assert_eq!(prev_bucket.use_data_linker, rep_data);
        assert_eq!(prev_bucket.loc_data_linker, rep_data);
        assert_eq!(
            ctx.processing_data_box_representative_variable_binding_path_hash(
                &mut data_box,
                false,
            ),
            localized_hash_id
        );
    }

    #[test]
    fn pn3_context_role_successor_wrappers_read_installed_links() {
        let mut ctx = ProcessContext::new();
        let role = RoleId::new(17);
        let source = ctx.alloc_node(IndividualProcessNode::default());
        let first_dest = ctx.alloc_node(IndividualProcessNode::default());
        let second_dest = ctx.alloc_node(IndividualProcessNode::default());
        ctx.node_mut(source).set_individual_node_id(10);
        ctx.node_mut(first_dest).set_individual_node_id(20);
        ctx.node_mut(second_dest).set_individual_node_id(30);

        let mut first_edge = IndividualLinkEdge::new();
        first_edge.init_individual_link_edge(source, source, first_dest, role, TrackPointId::NONE);
        let first_edge = ctx.alloc_edge(first_edge);
        let mut reapply_it = ReapplyQueueIterator::default();
        assert_eq!(
            ctx.node_install_individual_link(source, first_edge, &mut reapply_it),
            1
        );

        let mut second_edge = IndividualLinkEdge::new();
        second_edge.init_individual_link_edge(
            source,
            source,
            second_dest,
            role,
            TrackPointId::NONE,
        );
        let second_edge = ctx.alloc_edge(second_edge);
        assert_eq!(
            ctx.node_install_individual_link(source, second_edge, &mut reapply_it),
            2
        );

        assert_eq!(ctx.node_role_successor_count(source, role), 2);
        assert_eq!(
            ctx.node_get_role_successor_to_individual_link_id(source, role, 20, true),
            first_edge
        );
        assert_eq!(
            ctx.node_get_role_successor_to_individual_link_id(source, role, 30, true),
            second_edge
        );
        assert!(ctx.node_has_role_successor_to_individual_id(source, role, 20, true));
        assert!(!ctx.node_has_role_successor_to_individual_id(source, role, 40, true));

        let mut it = ctx.node_role_successor_link_iterator(source, role);
        assert_eq!(it.next(true), second_edge);
        assert_eq!(it.next(true), first_edge);
        assert_eq!(it.next(true), EdgeId::NONE);

        let mut history_it =
            ctx.node_role_successor_history_link_iterator(source, role, first_edge);
        assert_eq!(history_it.next(true), second_edge);
        assert_eq!(history_it.next(true), EdgeId::NONE);

        let mut role_it = ctx.node_role_iterator(source);
        assert_eq!(role_it.next(true), role);
        assert_eq!(role_it.next(true), RoleId::NONE);

        let mut successor_ids = Vec::new();
        let mut succ_it = ctx.node_successor_iterator(source);
        while succ_it.has_next() {
            successor_ids.push(succ_it.next_individual_id(true));
        }
        successor_ids.sort();
        assert_eq!(successor_ids, vec![20, 30]);
        assert!(ctx.node_has_successor_individual_node(source, 20));

        let conn_set = ctx.node_connection_successor_set(source);
        ctx.conn_succ_set_mut(conn_set)
            .insert_connection_successor(20)
            .insert_connection_successor(30);
        let mut connection_ids = Vec::new();
        let mut conn_it = ctx.node_connection_successor_iterator(source);
        while conn_it.has_next() {
            connection_ids.push(conn_it.next_successor_connection_id(true));
        }
        connection_ids.sort();
        assert_eq!(connection_ids, vec![20, 30]);

        ctx.node_remove_individual_link(source, first_edge);
        assert_eq!(ctx.node_role_successor_count(source, role), 1);
        assert_eq!(
            ctx.node_get_role_successor_to_individual_link_id(source, role, 20, true),
            EdgeId::NONE
        );
        assert!(
            ctx.node_has_successor_individual_node(source, 20),
            "Konclude removeIndividualLink only updates the reapply-role hash"
        );

        ctx.node_remove_individual_connection(source, first_dest);
        assert!(!ctx.node_has_successor_individual_node(source, 20));
        let mut connection_ids_after = Vec::new();
        let mut conn_it = ctx.node_connection_successor_iterator(source);
        while conn_it.has_next() {
            connection_ids_after.push(conn_it.next_successor_connection_id(true));
        }
        assert_eq!(connection_ids_after, vec![30]);
    }

    #[test]
    fn pn3_context_disjoint_successor_wrappers_install_read_iterate_and_remove() {
        let mut ctx = ProcessContext::new();
        let role = RoleId::new(23);
        let source = ctx.alloc_node(IndividualProcessNode::default());
        let dest = ctx.alloc_node(IndividualProcessNode::default());
        ctx.node_mut(source).set_individual_node_id(100);
        ctx.node_mut(dest).set_individual_node_id(200);

        assert!(!ctx.node_has_negation_disjoint_to_individual_id(source, role, 200));
        assert_eq!(
            ctx.node_disjoint_successor_role_link(source, role, 200),
            DisjointEdgeId::NONE
        );

        let mut disjoint_edge = DisjointEdge::new();
        disjoint_edge.init_negation_disjoint_edge(source, dest, role, TrackPointId::NONE);
        let disjoint_edge = ctx.alloc_disjoint_edge(disjoint_edge);
        ctx.node_install_disjoint_link(source, disjoint_edge);

        assert!(ctx.node_has_negation_disjoint_to_individual_id(source, role, 200));
        assert_eq!(
            ctx.node_disjoint_successor_role_link(source, role, 200),
            disjoint_edge
        );

        let mut it = ctx.node_disjoint_successor_role_iterator(source, 200);
        assert_eq!(it.get_successor_individual_id(), 200);
        assert_eq!(it.next(true), disjoint_edge);
        assert_eq!(it.next(true), DisjointEdgeId::NONE);

        ctx.node_remove_disjoint_links(source, 200);
        assert!(!ctx.node_has_negation_disjoint_to_individual_id(source, role, 200));
        assert_eq!(
            ctx.node_disjoint_successor_role_link(source, role, 200),
            DisjointEdgeId::NONE
        );
        assert!(!ctx
            .node_disjoint_successor_role_iterator(source, 200)
            .has_next());
    }

    #[test]
    fn processing_data_box_representative_variable_binding_path_joining_key_hash_localizes_and_copies_previous_entries(
    ) {
        let mut ctx = ProcessContext::new();
        let mut data_box = ProcessingDataBox::new();
        let bucket_key = 19;
        let joining_key_data = RepresentativeVariableBindingPathJoiningKeyDataId::new(23);
        let mut prev_hash = RepresentativeVariableBindingPathJoiningKeyHash::new(INVALID);
        prev_hash.next_rep_var_bind_path_joining_key_tag = 31;
        prev_hash.map.insert(
            bucket_key,
            vec![RepresentativeVariableBindingPathJoiningKeyHashData {
                var_bind_path_joining_data: joining_key_data,
            }],
        );
        let prev_hash_id = ctx.alloc_rep_var_bind_path_joining_key_hash(prev_hash);
        data_box.use_rep_var_bind_path_joining_key_hash = prev_hash_id;

        let localized_hash_id = ctx
            .processing_data_box_representative_variable_binding_path_joining_key_hash(
                &mut data_box,
                true,
            );

        assert!(localized_hash_id.is_some());
        assert_ne!(localized_hash_id, prev_hash_id);
        assert_eq!(
            data_box.loc_rep_var_bind_path_joining_key_hash,
            localized_hash_id
        );
        assert_eq!(
            data_box.use_rep_var_bind_path_joining_key_hash,
            localized_hash_id
        );
        assert_eq!(
            ctx.rep_var_bind_path_joining_key_hash(localized_hash_id)
                .next_rep_var_bind_path_joining_key_tag,
            31
        );
        assert_eq!(
            ctx.rep_var_bind_path_joining_key_hash(localized_hash_id)
                .map[&bucket_key][0]
                .var_bind_path_joining_data,
            joining_key_data
        );
        assert_eq!(
            ctx.rep_var_bind_path_joining_key_hash(prev_hash_id)
                .next_rep_var_bind_path_joining_key_tag,
            31
        );
        assert_eq!(
            ctx.processing_data_box_representative_variable_binding_path_joining_key_hash(
                &mut data_box,
                false,
            ),
            localized_hash_id
        );
    }

    #[test]
    fn processing_data_box_representative_joining_hash_localizes_and_copies_previous_entries() {
        let mut ctx = ProcessContext::new();
        let mut data_box = ProcessingDataBox::new();
        let key = (3, 5);
        let joining_data = RepresentativeJoiningDataId::new(29);
        let mut prev_hash = RepresentativeJoiningHash::new(INVALID);
        prev_hash.map.insert(
            key,
            RepresentativeJoiningHashData {
                var_bind_path_joining_data: joining_data,
            },
        );
        let prev_hash_id = ctx.alloc_rep_joining_hash(prev_hash);
        data_box.use_rep_joining_hash = prev_hash_id;

        let localized_hash_id =
            ctx.processing_data_box_representative_joining_hash(&mut data_box, true);

        assert!(localized_hash_id.is_some());
        assert_ne!(localized_hash_id, prev_hash_id);
        assert_eq!(data_box.loc_rep_joining_hash, localized_hash_id);
        assert_eq!(data_box.use_rep_joining_hash, localized_hash_id);
        assert_eq!(
            ctx.rep_joining_hash(localized_hash_id).map[&key].var_bind_path_joining_data,
            joining_data
        );
        assert_eq!(
            ctx.rep_joining_hash(prev_hash_id).map[&key].var_bind_path_joining_data,
            joining_data
        );
        assert_eq!(
            ctx.processing_data_box_representative_joining_hash(&mut data_box, false),
            localized_hash_id
        );
    }

    #[test]
    fn processing_data_box_variable_binding_path_merging_hash_localizes_and_copies_previous_entries(
    ) {
        let mut ctx = ProcessContext::new();
        let mut data_box = ProcessingDataBox::new();
        let key = (7, 11);
        let merged_path = VarBindingPathId::new(31);
        let mut prev_hash = VariableBindingPathMergingHash::new(INVALID);
        prev_hash.map.insert(key, {
            let mut data = VariableBindingPathMergingHashData::new();
            data.set_variable_binding_path(merged_path);
            data
        });
        let prev_hash_id = ctx.alloc_vbpath_merging_hash(prev_hash);
        data_box.use_var_binding_path_merging_hash = prev_hash_id;

        let localized_hash_id =
            ctx.processing_data_box_variable_binding_path_merging_hash(&mut data_box, true);

        assert!(localized_hash_id.is_some());
        assert_ne!(localized_hash_id, prev_hash_id);
        assert_eq!(
            data_box.loc_var_binding_path_merging_hash,
            localized_hash_id
        );
        assert_eq!(
            data_box.use_var_binding_path_merging_hash,
            localized_hash_id
        );
        assert_eq!(
            ctx.vbpath_merging_hash(localized_hash_id)
                .map
                .get(&key)
                .expect("copied variable-binding path merging entry")
                .get_variable_binding_path(),
            merged_path
        );
        assert_eq!(
            ctx.vbpath_merging_hash(prev_hash_id)
                .map
                .get(&key)
                .expect("previous variable-binding path merging entry restored")
                .get_variable_binding_path(),
            merged_path
        );
        assert_eq!(
            ctx.processing_data_box_variable_binding_path_merging_hash(&mut data_box, false),
            localized_hash_id
        );
    }

    #[test]
    fn processing_data_box_signature_blocking_candidate_hash_creates_from_previous_hash() {
        let mut ctx = ProcessContext::new();
        let mut data_box = ProcessingDataBox::new();
        let mut prev_hash = SignatureBlockingCandidateHash::new(INVALID);
        prev_hash.insert_signature_blocking_candidates(41, vec![3, 5]);
        let prev_hash_id = ctx.alloc_sig_block_cand_hash(prev_hash);
        data_box.prev_signature_blocking_candidate_hash = prev_hash_id;

        let created_hash_id =
            ctx.processing_data_box_signature_blocking_candidate_hash(&mut data_box, true);

        assert!(created_hash_id.is_some());
        assert_ne!(created_hash_id, prev_hash_id);
        assert_eq!(data_box.signature_blocking_candidate_hash, created_hash_id);
        assert_eq!(
            data_box.use_signature_blocking_candidate_hash,
            created_hash_id
        );
        assert_eq!(
            ctx.sig_block_cand_hash(created_hash_id)
                .get_blocking_candidates_count(41),
            2
        );
        assert_eq!(
            ctx.sig_block_cand_hash(prev_hash_id)
                .get_blocking_candidates_count(41),
            2
        );
        assert_eq!(
            ctx.processing_data_box_signature_blocking_candidate_hash(&mut data_box, false),
            created_hash_id
        );
    }

    #[test]
    fn processing_data_box_signature_nominal_delaying_candidate_hash_creates_from_previous_hash() {
        let mut ctx = ProcessContext::new();
        let mut data_box = ProcessingDataBox::new();
        let mut prev_hash = SignatureBlockingCandidateHash::new(INVALID);
        prev_hash.insert_signature_blocking_candidates(43, vec![7, 11, 13]);
        let prev_hash_id = ctx.alloc_sig_block_cand_hash(prev_hash);
        data_box.prev_signature_nominal_delaying_candidate_hash = prev_hash_id;

        let created_hash_id =
            ctx.processing_data_box_signature_nominal_delaying_candidate_hash(&mut data_box, true);

        assert!(created_hash_id.is_some());
        assert_ne!(created_hash_id, prev_hash_id);
        assert_eq!(
            data_box.signature_nominal_delaying_candidate_hash,
            created_hash_id
        );
        assert_eq!(
            data_box.use_signature_nominal_delaying_candidate_hash,
            created_hash_id
        );
        assert_eq!(
            ctx.sig_block_cand_hash(created_hash_id)
                .get_blocking_candidates_count(43),
            3
        );
        assert_eq!(
            ctx.sig_block_cand_hash(prev_hash_id)
                .get_blocking_candidates_count(43),
            3
        );
        assert_eq!(
            ctx.processing_data_box_signature_nominal_delaying_candidate_hash(
                &mut data_box,
                false,
            ),
            created_hash_id
        );
    }

    #[test]
    fn processing_data_box_signature_blocking_review_set_creates_from_previous_and_clears() {
        let mut ctx = ProcessContext::new();
        let mut data_box = ProcessingDataBox::new();
        assert!(data_box
            .signature_blocking_review_set(&mut ctx, false)
            .is_none());

        let prev_set = ctx.alloc_signature_blocking_review_set(SignatureBlockingReviewSet::new());
        ctx.signature_blocking_review_set_mut(prev_set)
            .get_review_data(false)
            .insert(1, 11);
        ctx.signature_blocking_review_set_mut(prev_set)
            .get_review_data(true)
            .insert(2, 22);
        data_box.prev_signature_blocking_review_set = prev_set;

        let created_set = data_box.signature_blocking_review_set(&mut ctx, true);

        assert!(created_set.is_some());
        assert_ne!(created_set, prev_set);
        assert_eq!(data_box.signature_blocking_review_set, created_set);
        assert_eq!(data_box.use_signature_blocking_review_set, created_set);
        assert!(ctx
            .signature_blocking_review_set(created_set)
            .non_subset_reviews
            .contains(11));
        assert!(ctx
            .signature_blocking_review_set(created_set)
            .subset_reviews
            .contains(22));
        assert!(ctx
            .signature_blocking_review_set(prev_set)
            .non_subset_reviews
            .contains(11));
        assert_eq!(
            data_box.signature_blocking_review_set(&mut ctx, false),
            created_set
        );

        data_box.clear_signature_blocking_review_set();
        assert!(data_box.signature_blocking_review_set.is_none());
        assert!(data_box.use_signature_blocking_review_set.is_none());
        assert!(data_box.prev_signature_blocking_review_set.is_none());
    }

    #[test]
    fn processing_data_box_reactivation_queues_create_from_previous_and_clear() {
        let mut ctx = ProcessContext::new();
        let mut data_box = ProcessingDataBox::new();
        let early_node = ctx.alloc_node(IndividualProcessNode::new(
            super::super::stubs::ProcessContextId::NONE,
        ));
        ctx.node_mut(early_node)
            .set_individual_node_id(31)
            .set_individual_ancestor_depth(2);
        let late_node = ctx.alloc_node(IndividualProcessNode::new(
            super::super::stubs::ProcessContextId::NONE,
        ));
        ctx.node_mut(late_node)
            .set_individual_node_id(37)
            .set_individual_ancestor_depth(3);
        assert!(data_box
            .early_individual_reactivation_processing_queue(&mut ctx, false)
            .is_none());
        assert!(data_box
            .late_individual_reactivation_processing_queue(&mut ctx, false)
            .is_none());

        let prev_early =
            ctx.alloc_indi_reactivation_proc_queue(IndividualReactivationProcessingQueue::new());
        assert!(ctx.indi_reactivation_queue_insert(prev_early, early_node, true));
        data_box.prev_early_indi_react_pro_queue = prev_early;
        let prev_late =
            ctx.alloc_indi_reactivation_proc_queue(IndividualReactivationProcessingQueue::new());
        assert!(ctx.indi_reactivation_queue_insert(prev_late, late_node, false));
        data_box.prev_late_indi_react_pro_queue = prev_late;

        let early_queue = data_box.early_individual_reactivation_processing_queue(&mut ctx, true);
        let late_queue = data_box.late_individual_reactivation_processing_queue(&mut ctx, true);

        assert!(early_queue.is_some());
        assert!(late_queue.is_some());
        assert_ne!(early_queue, prev_early);
        assert_ne!(late_queue, prev_late);
        assert_eq!(data_box.early_indi_react_pro_queue, early_queue);
        assert_eq!(data_box.use_early_indi_react_pro_queue, early_queue);
        assert_eq!(data_box.late_indi_react_pro_queue, late_queue);
        assert_eq!(data_box.use_late_indi_react_pro_queue, late_queue);
        assert!(ctx.indi_reactivation_queue_has_queued_individual(early_queue, early_node));
        assert!(ctx.indi_reactivation_queue_has_queued_individual(prev_early, early_node));
        assert!(ctx.indi_reactivation_queue_has_queued_individual(late_queue, late_node));
        assert!(ctx.indi_reactivation_queue_has_queued_individual(prev_late, late_node));
        assert_eq!(
            data_box.early_individual_reactivation_processing_queue(&mut ctx, false),
            early_queue
        );
        assert_eq!(
            data_box.late_individual_reactivation_processing_queue(&mut ctx, false),
            late_queue
        );

        data_box.clear_early_individual_reactivation_processing_queue();
        assert!(data_box.early_indi_react_pro_queue.is_none());
        assert!(data_box.use_early_indi_react_pro_queue.is_none());
        assert!(data_box.prev_early_indi_react_pro_queue.is_none());
        data_box.clear_late_individual_reactivation_processing_queue();
        assert!(data_box.late_indi_react_pro_queue.is_none());
        assert!(data_box.use_late_indi_react_pro_queue.is_none());
        assert!(data_box.prev_late_indi_react_pro_queue.is_none());
    }

    #[test]
    fn processing_data_box_db4_linkers_preserve_konclude_head_order_and_counts() {
        let mut ctx = ProcessContext::new();
        let mut data_box = ProcessingDataBox::new();
        let n1 = NodeId::new(1);
        let n2 = NodeId::new(2);
        let n3 = NodeId::new(3);
        let n4 = NodeId::new(4);

        assert!(!data_box.has_cache_testing_individual_nodes());
        data_box.add_individual_node_cache_testing_linker(vec![n2, n3]);
        data_box.add_individual_node_cache_testing_linker(vec![n1]);
        assert!(data_box.has_cache_testing_individual_nodes());
        assert_eq!(data_box.take_next_cache_testing_individual_node(), n1);
        assert_eq!(
            data_box.take_individual_node_cache_testing_linker(),
            vec![n2, n3]
        );
        assert!(!data_box.has_cache_testing_individual_nodes());

        data_box.set_sorted_nominal_non_deterministic_processing_node_linker(vec![n2, n3]);
        assert_eq!(data_box.nominal_non_det_processing_count, 2);
        data_box.add_sorted_nominal_non_deterministic_processing_node_linker(vec![n1]);
        assert_eq!(data_box.nominal_non_det_processing_count, 3);
        assert_eq!(
            data_box.sorted_nominal_non_deterministic_processing_node_linker(),
            &[n1, n2, n3]
        );
        assert_eq!(
            data_box.take_sorted_nominal_non_deterministic_processing_node(),
            n1
        );
        assert_eq!(data_box.nominal_non_det_processing_count, 2);
        assert_eq!(
            data_box.take_sorted_nominal_non_deterministic_processing_node_linker(),
            vec![n2, n3]
        );
        assert_eq!(
            data_box.nominal_non_det_processing_count, 2,
            "Konclude take-linker clears the head without changing the count"
        );
        data_box.clear_sorted_nominal_non_deterministic_processing_node_linker();
        assert_eq!(data_box.nominal_non_det_processing_count, 0);
        assert!(!data_box.has_sorted_nominal_non_deterministic_processing_nodes());

        data_box.add_individual_node_blocked_resolve_linker(vec![n3]);
        data_box.add_individual_node_blocked_resolve_linker(vec![n1, n2]);
        assert!(data_box.has_blocked_resolve_individual_nodes());
        assert_eq!(
            data_box.take_next_individual_node_blocked_resolve_linker(),
            n1
        );
        assert_eq!(
            data_box.take_next_individual_node_blocked_resolve_linker(),
            n2
        );
        data_box.clear_blocked_resolve_individual_nodes();
        assert!(!data_box.has_blocked_resolve_individual_nodes());

        data_box.add_blockable_individual_node_updated_linker(vec![n3]);
        data_box.add_blockable_individual_node_updated_linker(vec![n1, n2]);
        assert!(data_box.has_blockable_individual_node_updated_linker());
        assert_eq!(data_box.blockable_individual_node_updated_linker(), n1);
        assert_eq!(data_box.blockable_individual_node_updated_linker(), n2);
        data_box.clear_blockable_individual_node_updated_linker();
        assert!(!data_box.has_blockable_individual_node_updated_linker());

        let mut link2 = IndividualProcessNodeLinker::new();
        link2.init_process_node_linker(n2, true);
        let link2 = ctx.alloc_individual_process_node_linker(link2);
        let mut link3 = IndividualProcessNodeLinker::new();
        link3.init_process_node_linker(n3, false);
        let link3 = ctx.alloc_individual_process_node_linker(link3);
        ctx.individual_process_node_linker_mut(link2)
            .set_next(link3);
        let mut link1 = IndividualProcessNodeLinker::new();
        link1.init_process_node_linker(n1, false);
        let link1 = ctx.alloc_individual_process_node_linker(link1);

        data_box.set_individual_process_node_linker(link2);
        data_box.add_individual_process_node_linker(&mut ctx, link1);
        assert_eq!(data_box.individual_process_node_linker(), link1);
        assert_eq!(
            ctx.individual_process_node_linker(link1)
                .get_processing_individual(),
            n1
        );
        assert_eq!(ctx.individual_process_node_linker(link1).get_next(), link2);
        assert!(ctx
            .individual_process_node_linker(link2)
            .is_processing_queued());
        assert!(!ctx
            .individual_process_node_linker(link3)
            .is_processing_queued());
        assert_eq!(
            data_box.take_individual_process_node_linker(&mut ctx),
            link1
        );
        assert!(ctx
            .individual_process_node_linker(link1)
            .get_next()
            .is_none());
        assert_eq!(
            data_box.take_individual_process_node_linker(&mut ctx),
            link2
        );
        assert_eq!(
            data_box.take_individual_process_node_linker(&mut ctx),
            link3
        );
        assert!(data_box
            .take_individual_process_node_linker(&mut ctx)
            .is_none());
        data_box.add_individual_node_cache_testing_linker(vec![n4]);
        assert_eq!(data_box.take_next_cache_testing_individual_node(), n4);
    }

    #[test]
    fn processing_data_box_blocking_individual_node_candidate_hash_creates_from_previous_hash() {
        let mut ctx = ProcessContext::new();
        let mut data_box = ProcessingDataBox::new();
        let key = (ConceptId::new(17), true);
        let prev_data = ctx
            .alloc_blocking_indi_node_cand_data(BlockingIndividualNodeCandidateData::new(INVALID));
        let mut prev_hash = BlockingIndividualNodeCandidateHash::new(INVALID);
        prev_hash.block_candidate_hash.insert(
            key,
            BlockingCandidateHashData {
                candidate_indi_data: prev_data,
                prev_candidate_indi_data: prev_data,
            },
        );
        let prev_hash_id = ctx.alloc_blocking_indi_node_cand_hash(prev_hash);
        data_box.prev_blocking_indi_node_candidate_hash = prev_hash_id;

        let created_hash_id =
            ctx.processing_data_box_blocking_individual_node_candidate_hash(&mut data_box, true);

        assert!(created_hash_id.is_some());
        assert_ne!(created_hash_id, prev_hash_id);
        assert_eq!(data_box.blocking_indi_node_candidate_hash, created_hash_id);
        assert_eq!(
            data_box.use_blocking_indi_node_candidate_hash,
            created_hash_id
        );

        let copied_data = ctx
            .blocking_indi_node_cand_hash(created_hash_id)
            .block_candidate_hash
            .get(&key)
            .copied()
            .expect("copied blocking candidate bucket");
        assert!(copied_data.candidate_indi_data.is_none());
        assert_eq!(copied_data.prev_candidate_indi_data, prev_data);

        let prev_bucket = ctx
            .blocking_indi_node_cand_hash(prev_hash_id)
            .block_candidate_hash
            .get(&key)
            .copied()
            .expect("previous blocking candidate bucket restored");
        assert_eq!(prev_bucket.candidate_indi_data, prev_data);
        assert_eq!(prev_bucket.prev_candidate_indi_data, prev_data);
        assert_eq!(
            ctx.processing_data_box_blocking_individual_node_candidate_hash(&mut data_box, false),
            created_hash_id
        );
    }

    #[test]
    fn blocking_candidate_data_materializes_tags_and_candidate_iterator() {
        let mut ctx = ProcessContext::new();
        let mut data_box = ProcessingDataBox::new();
        let hash_id =
            ctx.processing_data_box_blocking_individual_node_candidate_hash(&mut data_box, true);

        let concept = ConceptId::new(23);
        let mut descriptor = ConceptDescriptor::new();
        descriptor.concept = concept;
        descriptor.negated = true;
        let descriptor_id = ctx.alloc_con_desc(descriptor);

        let data_id = BlockingIndividualNodeCandidateHash::get_blocking_individual_candidate_data_for_concept_descriptor(
            &mut ctx,
            hash_id,
            descriptor_id,
            true,
        );
        assert!(data_id.is_some());

        let n1 = ctx.alloc_node(IndividualProcessNode::default());
        ctx.node_mut(n1).set_individual_node_id(3);
        let n2 = ctx.alloc_node(IndividualProcessNode::default());
        ctx.node_mut(n2).set_individual_node_id(7);
        ctx.blocking_indi_node_cand_data_insert_blocking_candidate_individual_node(data_id, n1);
        ctx.blocking_indi_node_cand_data_insert_blocking_candidate_individual_node(data_id, n2);

        {
            let data = ctx.blocking_indi_node_cand_data_mut(data_id);
            assert!(data.update_concept_label_set_modification_tag(11));
            assert!(data.update_node_switch_tag(13));
            data.set_max_valid_individual_id(7);
        }
        assert_eq!(
            ctx.blocking_indi_node_cand_data(data_id)
                .get_concept_label_set_modification_tag(),
            11
        );
        assert_eq!(
            ctx.blocking_indi_node_cand_data(data_id)
                .get_node_switch_tag(),
            13
        );
        assert_eq!(
            ctx.blocking_indi_node_cand_data(data_id)
                .get_max_valid_individual_id(),
            7
        );

        let mut iterator = ctx
            .blocking_indi_node_cand_data(data_id)
            .get_blocking_candidates_individual_node_iterator(8);
        assert_eq!(iterator.next_individual_candidate(true), Some(n2));
        assert_eq!(iterator.next_individual_candidate(true), Some(n1));
        assert!(!iterator.has_next());
    }

    #[test]
    fn linked_blocking_candidate_hash_copies_and_prepends_candidate_linkers() {
        let mut ctx = ProcessContext::new();
        let mut data_box = ProcessingDataBox::new();
        let hash_id = ctx.processing_data_box_blocking_individual_node_linked_candidate_hash(
            &mut data_box,
            true,
        );

        let concept = ConceptId::new(31);
        let mut descriptor = ConceptDescriptor::new();
        descriptor.concept = concept;
        descriptor.negated = false;
        let descriptor_id = ctx.alloc_con_desc(descriptor);

        let data_id = BlockingIndividualNodeLinkedCandidateHash::get_blocking_individual_candidate_data_for_concept_descriptor(
            &mut ctx,
            hash_id,
            descriptor_id,
            true,
        );
        let n1 = ctx.alloc_node(IndividualProcessNode::default());
        let n2 = ctx.alloc_node(IndividualProcessNode::default());
        ctx.blocking_indi_node_linked_cand_data_add_blocking_candidate_individual_node(data_id, n1);
        ctx.blocking_indi_node_linked_cand_data_add_blocking_candidate_individual_node(data_id, n2);

        assert_eq!(
            ctx.blocking_indi_node_linked_cand_data(data_id)
                .get_candidate_count(),
            2
        );
        let head = ctx
            .blocking_indi_node_linked_cand_data(data_id)
            .get_blocking_candidates_individual_node_linker();
        assert_eq!(
            ctx.blocking_indi_node_linker(head)
                .get_candidate_individual_node(),
            n2
        );
        let next = ctx.blocking_indi_node_linker(head).get_next();
        assert_eq!(
            ctx.blocking_indi_node_linker(next)
                .get_candidate_individual_node(),
            n1
        );

        let mut copied_box = ProcessingDataBox::new();
        copied_box.prev_blocking_indi_node_linked_candidate_hash = hash_id;
        let copied_hash = ctx.processing_data_box_blocking_individual_node_linked_candidate_hash(
            &mut copied_box,
            true,
        );
        assert_ne!(copied_hash, hash_id);
        let copied_data =
            BlockingIndividualNodeLinkedCandidateHash::get_blocking_individual_candidate_data_for_concept_descriptor(
                &mut ctx,
                copied_hash,
                descriptor_id,
                true,
            );
        assert_ne!(copied_data, data_id);
        assert_eq!(
            ctx.blocking_indi_node_linked_cand_data(copied_data)
                .get_candidate_count(),
            2
        );
        assert_eq!(
            ctx.blocking_indi_node_linked_cand_data(copied_data)
                .get_blocking_candidates_individual_node_linker(),
            head
        );

        let n3 = ctx.alloc_node(IndividualProcessNode::default());
        ctx.blocking_indi_node_linked_cand_data_add_blocking_candidate_individual_node(
            copied_data,
            n3,
        );
        assert_eq!(
            ctx.blocking_indi_node_linked_cand_data(copied_data)
                .get_candidate_count(),
            3
        );
        assert_eq!(
            ctx.blocking_indi_node_linked_cand_data(data_id)
                .get_candidate_count(),
            2
        );
        let copied_head = ctx
            .blocking_indi_node_linked_cand_data(copied_data)
            .get_blocking_candidates_individual_node_linker();
        assert_eq!(
            ctx.blocking_indi_node_linker(copied_head)
                .get_candidate_individual_node(),
            n3
        );
    }

    #[test]
    fn blocking_data_tag_protocol_updates_node_switch_and_label_modification_tags() {
        let mut block_data = IndividualNodeBlockingTestData::new();
        assert_eq!(block_data.get_node_switch_tag(), 0);
        assert!(block_data.update_node_switch_tag(5));
        assert_eq!(block_data.get_node_switch_tag(), 5);
        assert!(!block_data.update_node_switch_tag(5));
        assert!(block_data.is_node_switch_tag_up_to_date(4));
        assert!(block_data.is_node_switch_tag_up_to_date(5));
        assert!(!block_data.is_node_switch_tag_updated(5));
        assert!(block_data.is_node_switch_tag_updated(6));
        assert!(block_data.update_concept_label_set_modification_tag(7));
        assert_eq!(block_data.get_concept_label_set_modification_tag(), 7);
        assert!(!block_data.update_concept_label_set_modification_tag(7));

        let mut candidate_data = BlockingIndividualNodeCandidateData::new(INVALID);
        candidate_data.set_node_switch_tag(11);
        assert_eq!(candidate_data.get_node_switch_tag(), 11);
        candidate_data.init_node_switch_tag(13);
        assert_eq!(candidate_data.get_node_switch_tag(), 13);
        assert!(candidate_data.is_node_switch_tag_up_to_date(12));
        assert!(!candidate_data.is_node_switch_tag_up_to_date(14));
        assert!(candidate_data.update_concept_label_set_modification_tag(17));
        assert_eq!(candidate_data.get_concept_label_set_modification_tag(), 17);
        assert!(!candidate_data.update_concept_label_set_modification_tag(17));
    }

    #[test]
    fn blocking_test_data_copies_blocking_fields_but_keeps_fresh_tags() {
        let mut ctx = ProcessContext::new();
        let blocker = ctx.alloc_node(IndividualProcessNode::default());
        ctx.node_mut(blocker).set_individual_node_id(19);

        let mut previous = IndividualNodeBlockingTestData::new();
        previous
            .set_blocking_individual_node(blocker)
            .set_last_added_core_concept_descriptor(CoreConceptDescriptorId::NONE)
            .set_last_core_blocking_candidate_concept_descriptor(ConDescId::NONE)
            .set_last_core_blocking_candidate_concept_node_difference(3);
        previous.update_node_switch_tag(11);
        previous.update_concept_label_set_modification_tag(13);

        let mut localized = IndividualNodeBlockingTestData::new();
        localized.init_block_data(Some(&previous));

        assert_eq!(localized.get_blocking_individual_node(), blocker);
        assert_eq!(
            localized.get_last_core_blocking_candidate_concept_node_difference(),
            3
        );
        assert_eq!(
            localized.get_node_switch_tag(),
            0,
            "Konclude initBlockData does not copy inherited CNodeSwitchTag state"
        );
        assert_eq!(
            localized.get_concept_label_set_modification_tag(),
            0,
            "Konclude initBlockData does not copy inherited label-modification tag state"
        );

        localized.set_blocking_individual_node(NodeId::NONE);
        assert!(localized.get_blocking_individual_node().is_none());
    }

    #[test]
    fn linked_candidate_blocking_bookkeeping_uses_core_linker_and_block_data_cursors() {
        let mut ctx = ProcessContext::new();
        let con_desc = ConDescId::new(31);
        let label_set = ctx.alloc_label_set(ReapplyConceptLabelSet::new(INVALID));
        let core_desc = ctx.label_set_add_core_concept_descriptor(label_set, con_desc);
        assert_eq!(
            ctx.label_set(label_set)
                .get_core_concept_descriptor_linker(),
            core_desc
        );
        assert_eq!(
            ctx.core_con_desc(core_desc).get_concept_desciptor(),
            con_desc
        );

        let mut block_data = IndividualNodeBlockingTestData::new();
        block_data
            .set_blocking_individual_node(NodeId::new(7))
            .clear_blocking_individual_node()
            .set_last_added_core_concept_descriptor(core_desc)
            .set_last_core_blocking_candidate_concept_descriptor(ConDescId::NONE)
            .set_last_core_blocking_candidate_concept_node_difference(0);

        assert!(block_data.get_blocking_individual_node().is_none());
        assert_eq!(
            block_data.get_last_added_core_concept_descriptor(),
            core_desc
        );
        assert_eq!(
            block_data.get_last_core_blocking_candidate_concept_descriptor(),
            ConDescId::NONE
        );
        assert_eq!(
            block_data.get_last_core_blocking_candidate_concept_node_difference(),
            0
        );
    }

    #[test]
    fn node_switch_history_tracks_newer_min_bounds_and_updates_latest_switch() {
        let mut history = NodeSwitchHistory::new(INVALID);
        history
            .add_individual_process_node_switch(5, 50, 1)
            .add_individual_process_node_switch(3, 70, 2)
            .add_individual_process_node_switch(4, 20, 4);

        assert_eq!(
            history.get_min_individual_ancestor_depth_and_node_id(1),
            (true, 3, 20)
        );
        assert_eq!(
            history.get_min_individual_ancestor_depth_and_node_id(2),
            (true, 4, 20)
        );
        assert_eq!(
            history.get_min_individual_ancestor_depth_and_node_id(4),
            (true, Cint64::MAX, Cint64::MAX)
        );
        assert_eq!(history.get_min_individual_ancestor_depth(0), 3);
        assert_eq!(history.get_min_individual_node_id(0), 20);

        history.update_last_individual_process_node_switch(2, 10);
        assert_eq!(
            history.get_min_individual_ancestor_depth_and_node_id(2),
            (true, 2, 10)
        );
    }

    #[test]
    fn processing_data_box_node_switch_history_creates_from_previous_history() {
        let mut ctx = ProcessContext::new();
        let mut data_box = ProcessingDataBox::new();
        let mut prev_history = NodeSwitchHistory::new(INVALID);
        prev_history
            .add_individual_process_node_switch(9, 90, 1)
            .add_individual_process_node_switch(4, 40, 3);
        let prev_history_id = ctx.alloc_node_switch_history(prev_history);
        data_box.prev_node_switch_history = prev_history_id;

        let created_history_id = data_box.node_switch_history_with_context(&mut ctx, true);

        assert!(created_history_id.is_some());
        assert_ne!(created_history_id, prev_history_id);
        assert_eq!(data_box.node_switch_history, created_history_id);
        assert_eq!(data_box.use_node_switch_history, created_history_id);
        assert_eq!(
            ctx.node_switch_history(created_history_id)
                .get_min_individual_ancestor_depth_and_node_id(1),
            (true, 4, 40)
        );

        ctx.node_switch_history_mut(created_history_id)
            .add_individual_process_node_switch(2, 20, 5);
        assert_eq!(
            ctx.node_switch_history(prev_history_id)
                .get_min_individual_ancestor_depth_and_node_id(1),
            (true, 4, 40),
            "Rust clone preserves previous history while the new arena object mutates independently"
        );
        assert_eq!(
            data_box.node_switch_history_with_context(&mut ctx, false),
            created_history_id
        );
    }

    #[test]
    fn branching_tree_lifecycle_matches_konclude_task_copy_and_force_child() {
        let mut ctx = ProcessContext::new();
        let tree_id = ctx.alloc_branching_tree(BranchingTree::new(INVALID));

        let root = ctx.branching_tree_branch_tree_node(tree_id, 11, false);
        assert!(root.is_some());
        assert_eq!(ctx.branching_tree(tree_id).root_node, root);
        assert_eq!(ctx.branching_tree(tree_id).curr_node, root);
        assert_eq!(ctx.branch_node(root).parent_node(), BranchNodeId::NONE);
        assert_eq!(ctx.branch_node(root).get_root_node(), root);
        assert_eq!(ctx.branch_node(root).get_branching_level(), 0);
        assert_eq!(ctx.branch_node(root).get_satisfiable_calculation_task(), 11);

        assert_eq!(
            ctx.branching_tree_branch_tree_node(tree_id, 11, false),
            root
        );

        let copied_root = ctx.branching_tree_branch_tree_node(tree_id, 17, false);
        assert_ne!(copied_root, root);
        assert_eq!(
            ctx.branch_node(copied_root).parent_node(),
            BranchNodeId::NONE
        );
        assert_eq!(ctx.branch_node(copied_root).get_root_node(), copied_root);
        assert_eq!(
            ctx.branch_node(copied_root)
                .get_satisfiable_calculation_task(),
            17
        );
        assert_eq!(ctx.branching_tree(tree_id).root_node, copied_root);

        let forced_child = ctx.branching_tree_branch_tree_node(tree_id, 17, true);
        assert_ne!(forced_child, copied_root);
        assert_eq!(ctx.branch_node(forced_child).parent_node(), copied_root);
        assert_eq!(ctx.branch_node(forced_child).get_root_node(), copied_root);
        assert_eq!(
            ctx.branch_node(forced_child)
                .get_satisfiable_calculation_task(),
            17
        );
        assert_eq!(ctx.branching_tree(tree_id).curr_node, forced_child);
        assert_eq!(ctx.branching_tree(tree_id).prev_curr_node, forced_child);
    }

    #[test]
    fn processing_data_box_branching_tree_creates_from_previous_tree() {
        let mut ctx = ProcessContext::new();
        let mut parent_box = ProcessingDataBox::new();
        let parent_tree = parent_box.branching_tree_with_context(&mut ctx, true);
        let parent_root = ctx.branching_tree_branch_tree_node(parent_tree, 23, false);
        let base_dep = ctx.branching_tree_base_dependency_node(parent_tree, true);
        assert!(ctx.dep_node(base_dep).is_independent_base_dependency_type());

        let mut child_box = ProcessingDataBox::new();
        child_box.prev_branching_tree = parent_tree;
        let child_tree = child_box.branching_tree_with_context(&mut ctx, true);

        assert!(child_tree.is_some());
        assert_ne!(child_tree, parent_tree);
        assert_eq!(child_box.branching_tree, child_tree);
        assert_eq!(child_box.use_branching_tree, child_tree);
        assert_eq!(ctx.branching_tree(child_tree).curr_node, BranchNodeId::NONE);
        assert_eq!(ctx.branching_tree(child_tree).prev_curr_node, parent_root);
        assert_eq!(ctx.branching_tree(child_tree).root_node, parent_root);
        assert_eq!(
            ctx.branching_tree_base_dependency_node(child_tree, false),
            base_dep
        );
        assert_eq!(
            ctx.branching_tree_base_dependency_node(child_tree, true),
            base_dep
        );

        let child_branch = ctx.branching_tree_branch_tree_node(child_tree, 29, false);
        assert_ne!(child_branch, parent_root);
        assert_eq!(ctx.branch_node(child_branch).parent_node(), parent_root);
        assert_eq!(ctx.branch_node(child_branch).get_root_node(), parent_root);
        assert_eq!(
            ctx.branch_node(child_branch)
                .get_satisfiable_calculation_task(),
            29
        );
        assert_eq!(
            child_box.branching_tree_with_context(&mut ctx, false),
            child_tree
        );
    }
}
