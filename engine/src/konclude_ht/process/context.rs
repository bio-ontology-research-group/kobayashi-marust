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

use super::super::model::substrate::{Arena, Cint64, INVALID};

use super::descriptor::{ClashDescriptor, ConceptDescriptor, ConceptProcessDescriptor};
use super::dependency::{
    BranchTreeNode, BranchingInstruction, DependencyLink, DependencyNode, DependencyTrackPoint,
};
use super::edge::{DisjointEdge, DistinctEdge, IndividualLinkEdge};
use super::node::IndividualProcessNode;
use super::node_resolution::ProcessTagger;
use super::sat_node::IndividualSaturationProcessNode;
use super::satellites::{
    BranchingMergingProcessingRestrictionSpecification, ReapplyConceptLabelSet,
    ReapplyRoleSuccessorHash,
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
    VariableBindingPathJoiningData, VariableBindingPathSet, VariableBindingTriggerLinker,
};
// --- W2.7 satellite arenas: distinct / connection-successor / disjoint-role ---
use super::distinct::{
    ConnectionSuccessorCorrectionHash, ConnectionSuccessorCorrectionHashId, ConnectionSuccessorSet,
    ConnectionSuccessorSetId, DisjointSuccessorRoleHash, DisjointSuccessorRoleHashId, DistinctHash,
    DistinctHashId,
};
// --- W2.7 satellite arenas: reapply / signature-blocking / incremental-expansion ---
use super::reapply_sat::{
    BlockingAltDataId, BlockingAlternativeSignatureBlockingCandidateData, BlockingTestDataId,
    CondensedReapplyConceptDescriptor, CondensedReapplyConceptDescriptorId,
    IncrementalExpansionDataId, IndividualNodeBlockingTestData,
    IndividualNodeIncrementalExpansionData, SigBlockCandHashId, SignatureBlockingCandidateHash,
};
// --- W3b node-owned binding-set container hashes ---
use super::binding_hash::{
    ConceptPropagationBindingSetHash, ConceptPropagationBindingSetHashId,
    ConceptVariableBindingPathSetHash, ConceptVariableBindingPathSetHashId,
};
// --- W3c propagation-binding subsystem arenas (propagation_binding.rs) ---
use super::propagation_binding::{
    PropagationBinding, PropagationBindingDescriptor, PropagationBindingDescriptorId,
    PropagationBindingId, PropagationBindingReapplyConceptDescriptor,
    PropagationBindingReapplyConceptDescriptorId, PropagationBindingSet, PropagationBindingSetId,
};
// --- W3.5r representative variable-binding-path-set subsystem arenas (representative.rs) ---
use super::representative::{
    RepresentativePropagationDescriptor, RepresentativePropagationDescriptorId,
    RepresentativePropagationSet, RepresentativePropagationSetId,
    RepresentativeVariableBindingPathSetData, RepresentativeVariableBindingPathSetDataId,
    RepresentativeVariableBindingPathSetMigrateData,
    RepresentativeVariableBindingPathSetMigrateDataId,
};
// --- W3.5b blocking-individual-node candidate + signature-blocking concept-expansion (blocking_hash.rs) ---
use super::blocking_hash::{
    BlockingIndividualNodeCandidateData, BlockingIndividualNodeCandidateDataId,
    BlockingIndividualNodeCandidateHash, BlockingIndividualNodeCandidateHashId,
    SignatureBlockingIndividualNodeConceptExpansionData,
    SignatureBlockingIndividualNodeConceptExpansionDataId,
};
// --- W4.5 saturation-layer per-test satellites (saturation::satellites) ---
use super::super::saturation::satellites::{
    BackwardSaturationPropagationLink, BackwardSaturationPropagationLinkId,
    ConceptSaturationDescriptor, ConceptSaturationDescriptorId, ConceptSaturationProcessLinker,
    ConceptSaturationProcessLinkerId, IndividualSaturationProcessNodeExtensionData,
    IndividualSaturationProcessNodeExtensionDataId, LinkedRoleSaturationSuccessorData,
    LinkedRoleSaturationSuccessorDataId, LinkedRoleSaturationSuccessorHash,
    LinkedRoleSaturationSuccessorHashId, ReapplyConceptSaturationLabelSet,
    ReapplyConceptSaturationLabelSetId, RoleSaturationProcessLinker, RoleSaturationProcessLinkerId,
    SaturationSuccessorData, SaturationSuccessorDataId,
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
        #[inline]
        pub fn $get_mut(&mut self, id: $id) -> &mut $ty {
            self.$field.get_mut(id)
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
    label_sets: Arena<ReapplyConceptLabelSet>,
    /// `CReapplyRoleSuccessorHash` pool.
    role_succ_hashes: Arena<ReapplyRoleSuccessorHash>,
    /// `CBranchingMergingProcessingRestrictionSpecification` pool.
    restriction_specs: Arena<BranchingMergingProcessingRestrictionSpecification>,

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
    /// `CVariableBindingTriggerLinker` pool.
    var_binding_trigger_linkers: Arena<VariableBindingTriggerLinker>,

    // --- W2.7 distinct / connection-successor / disjoint-role satellites (distinct.rs) ---
    /// `CDistinctHash` pool.
    distinct_hashes: Arena<DistinctHash>,
    /// `CConnectionSuccessorSet` pool.
    conn_succ_sets: Arena<ConnectionSuccessorSet>,
    /// `CConnectionSuccessorCorrectionHash` pool.
    conn_succ_corr_hashes: Arena<ConnectionSuccessorCorrectionHash>,
    /// `CDisjointSuccessorRoleHash` pool.
    disjoint_succ_role_hashes: Arena<DisjointSuccessorRoleHash>,

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
    /// `CPropagationBindingSet` pool.
    prop_binding_sets: Arena<PropagationBindingSet>,

    // --- W3.5r representative variable-binding-path-set subsystem pools (representative.rs) ---
    /// `CRepresentativeVariableBindingPathSetData` pool.
    rep_var_bind_path_set_datas: Arena<RepresentativeVariableBindingPathSetData>,
    /// `CRepresentativeVariableBindingPathSetMigrateData` pool.
    rep_var_bind_path_set_migrate_datas: Arena<RepresentativeVariableBindingPathSetMigrateData>,
    /// `CRepresentativePropagationDescriptor` pool.
    rep_prop_descs: Arena<RepresentativePropagationDescriptor>,
    /// `CRepresentativePropagationSet` pool.
    rep_prop_sets: Arena<RepresentativePropagationSet>,

    // --- W3.5b blocking-individual-node candidate + signature-blocking concept-expansion pools (blocking_hash.rs) ---
    /// `CBlockingIndividualNodeCandidateHash` pool.
    blocking_indi_node_cand_hashes: Arena<BlockingIndividualNodeCandidateHash>,
    /// `CBlockingIndividualNodeCandidateData` pool.
    blocking_indi_node_cand_datas: Arena<BlockingIndividualNodeCandidateData>,
    /// `CSignatureBlockingIndividualNodeConceptExpansionData` pool.
    sig_block_con_exp_datas: Arena<SignatureBlockingIndividualNodeConceptExpansionData>,

    // --- W4.5 saturation-layer per-test satellite pools (saturation::satellites.rs) ---
    /// `CConceptSaturationDescriptor` pool.
    con_sat_descs: Arena<ConceptSaturationDescriptor>,
    /// `CConceptSaturationProcessLinker` pool.
    con_sat_proc_linkers: Arena<ConceptSaturationProcessLinker>,
    /// `CRoleSaturationProcessLinker` pool.
    role_sat_proc_linkers: Arena<RoleSaturationProcessLinker>,
    /// `CBackwardSaturationPropagationLink` pool.
    backward_sat_prop_links: Arena<BackwardSaturationPropagationLink>,
    /// `CSaturationSuccessorData` pool.
    sat_succ_datas: Arena<SaturationSuccessorData>,
    /// `CLinkedRoleSaturationSuccessorData` pool.
    linked_role_sat_succ_datas: Arena<LinkedRoleSaturationSuccessorData>,
    /// `CLinkedRoleSaturationSuccessorHash` pool.
    linked_role_sat_succ_hashes: Arena<LinkedRoleSaturationSuccessorHash>,
    /// `CIndividualSaturationProcessNodeExtensionData` pool.
    indi_sat_node_ext_datas: Arena<IndividualSaturationProcessNodeExtensionData>,
    /// `CReapplyConceptSaturationLabelSet` pool.
    reapply_con_sat_label_sets: Arena<ReapplyConceptSaturationLabelSet>,

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
            role_succ_hashes: Arena::new(),
            restriction_specs: Arena::new(),
            var_bindings: Arena::new(),
            var_binding_descs: Arena::new(),
            var_binding_paths: Arena::new(),
            var_binding_path_descs: Arena::new(),
            var_binding_path_sets: Arena::new(),
            var_binding_path_join_datas: Arena::new(),
            var_binding_trigger_linkers: Arena::new(),
            distinct_hashes: Arena::new(),
            conn_succ_sets: Arena::new(),
            conn_succ_corr_hashes: Arena::new(),
            disjoint_succ_role_hashes: Arena::new(),
            sig_block_cand_hashes: Arena::new(),
            blocking_test_datas: Arena::new(),
            blocking_alt_datas: Arena::new(),
            inc_exp_datas: Arena::new(),
            cond_reapply_con_descs: Arena::new(),
            con_var_bind_path_set_hashes: Arena::new(),
            con_prop_binding_set_hashes: Arena::new(),
            prop_bindings: Arena::new(),
            prop_binding_descs: Arena::new(),
            prop_binding_reapply_con_descs: Arena::new(),
            prop_binding_sets: Arena::new(),
            rep_var_bind_path_set_datas: Arena::new(),
            rep_var_bind_path_set_migrate_datas: Arena::new(),
            rep_prop_descs: Arena::new(),
            rep_prop_sets: Arena::new(),
            blocking_indi_node_cand_hashes: Arena::new(),
            blocking_indi_node_cand_datas: Arena::new(),
            sig_block_con_exp_datas: Arena::new(),
            con_sat_descs: Arena::new(),
            con_sat_proc_linkers: Arena::new(),
            role_sat_proc_linkers: Arena::new(),
            backward_sat_prop_links: Arena::new(),
            sat_succ_datas: Arena::new(),
            linked_role_sat_succ_datas: Arena::new(),
            linked_role_sat_succ_hashes: Arena::new(),
            indi_sat_node_ext_datas: Arena::new(),
            reapply_con_sat_label_sets: Arena::new(),
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

    // --- the accessor trios (the C++ `obj->method()` deref replacement) ---
    arena_accessors!(nodes, IndividualProcessNode, NodeId, node, node_mut, alloc_node);
    arena_accessors!(
        sat_nodes,
        IndividualSaturationProcessNode,
        SatNodeId,
        sat_node,
        sat_node_mut,
        alloc_sat_node
    );
    arena_accessors!(edges, IndividualLinkEdge, EdgeId, edge, edge_mut, alloc_edge);
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
    arena_accessors!(
        con_proc_descs,
        ConceptProcessDescriptor,
        ConProcDescId,
        con_proc_desc,
        con_proc_desc_mut,
        alloc_con_proc_desc
    );
    arena_accessors!(
        clash_descs,
        ClashDescriptor,
        ClashDescId,
        clash_desc,
        clash_desc_mut,
        alloc_clash_desc
    );
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
    arena_accessors!(
        branch_instrs,
        BranchingInstruction,
        BranchInstrId,
        branch_instr,
        branch_instr_mut,
        alloc_branch_instr
    );
    arena_accessors!(
        label_sets,
        ReapplyConceptLabelSet,
        LabelSetId,
        label_set,
        label_set_mut,
        alloc_label_set
    );
    arena_accessors!(
        role_succ_hashes,
        ReapplyRoleSuccessorHash,
        RoleSuccHashId,
        role_succ_hash,
        role_succ_hash_mut,
        alloc_role_succ_hash
    );
    arena_accessors!(
        restriction_specs,
        BranchingMergingProcessingRestrictionSpecification,
        RestrictionSpecId,
        restriction_spec,
        restriction_spec_mut,
        alloc_restriction_spec
    );

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
        var_binding_trigger_linkers,
        VariableBindingTriggerLinker,
        VarBindingTriggerLinkerId,
        vbtrigger_linker,
        vbtrigger_linker_mut,
        alloc_vbtrigger_linker
    );

    // --- W2.7 distinct / connection-successor / disjoint-role satellite trios ---
    arena_accessors!(
        distinct_hashes,
        DistinctHash,
        DistinctHashId,
        distinct_hash,
        distinct_hash_mut,
        alloc_distinct_hash
    );
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
        prop_binding_sets,
        PropagationBindingSet,
        PropagationBindingSetId,
        prop_binding_set,
        prop_binding_set_mut,
        alloc_prop_binding_set
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
        sig_block_con_exp_datas,
        SignatureBlockingIndividualNodeConceptExpansionData,
        SignatureBlockingIndividualNodeConceptExpansionDataId,
        sig_block_con_exp_data,
        sig_block_con_exp_data_mut,
        alloc_sig_block_con_exp_data
    );

    // --- W4.5 saturation-layer per-test satellite trios ---
    arena_accessors!(
        con_sat_descs,
        ConceptSaturationDescriptor,
        ConceptSaturationDescriptorId,
        con_sat_desc,
        con_sat_desc_mut,
        alloc_con_sat_desc
    );
    arena_accessors!(
        con_sat_proc_linkers,
        ConceptSaturationProcessLinker,
        ConceptSaturationProcessLinkerId,
        con_sat_proc_linker,
        con_sat_proc_linker_mut,
        alloc_con_sat_proc_linker
    );
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
    arena_accessors!(
        sat_succ_datas,
        SaturationSuccessorData,
        SaturationSuccessorDataId,
        sat_succ_data,
        sat_succ_data_mut,
        alloc_sat_succ_data
    );
    arena_accessors!(
        linked_role_sat_succ_datas,
        LinkedRoleSaturationSuccessorData,
        LinkedRoleSaturationSuccessorDataId,
        linked_role_sat_succ_data,
        linked_role_sat_succ_data_mut,
        alloc_linked_role_sat_succ_data
    );
    arena_accessors!(
        linked_role_sat_succ_hashes,
        LinkedRoleSaturationSuccessorHash,
        LinkedRoleSaturationSuccessorHashId,
        linked_role_sat_succ_hash,
        linked_role_sat_succ_hash_mut,
        alloc_linked_role_sat_succ_hash
    );
    arena_accessors!(
        indi_sat_node_ext_datas,
        IndividualSaturationProcessNodeExtensionData,
        IndividualSaturationProcessNodeExtensionDataId,
        indi_sat_node_ext_data,
        indi_sat_node_ext_data_mut,
        alloc_indi_sat_node_ext_data
    );
    arena_accessors!(
        reapply_con_sat_label_sets,
        ReapplyConceptSaturationLabelSet,
        ReapplyConceptSaturationLabelSetId,
        reapply_con_sat_label_set,
        reapply_con_sat_label_set_mut,
        alloc_reapply_con_sat_label_set
    );

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

    /// Context-threaded port of `CIndividualProcessNode::getReapplyConceptLabelSet(true)`.
    pub fn node_reapply_concept_label_set(&mut self, node: NodeId) -> LabelSetId {
        if self.node(node).reapply_con_label_set.is_none() {
            let prev = self.node(node).prev_reapply_con_label_set;
            let new_id = self.alloc_label_set(ReapplyConceptLabelSet::new(INVALID));
            if prev.is_some() {
                let taken =
                    std::mem::replace(self.label_set_mut(prev), ReapplyConceptLabelSet::new(INVALID));
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

    /// Context-threaded port of `CIndividualProcessNode::getDistinctHash(true)`.
    pub fn node_distinct_hash(&mut self, node: NodeId) -> DistinctHashId {
        if self.node(node).distinct_hash.is_none() {
            let prev = self.node(node).prev_distinct_hash;
            let new_id = self.alloc_distinct_hash(DistinctHash::new());
            if prev.is_some() {
                let taken = std::mem::replace(self.distinct_hash_mut(prev), DistinctHash::new());
                self.distinct_hash_mut(new_id).init_distinct_hash(Some(&taken));
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

    /// Context-threaded port of `CIndividualProcessNode::getDisjointSuccessorRoleHash(true)`.
    pub fn node_disjoint_successor_role_hash(&mut self, node: NodeId) -> DisjointSuccessorRoleHashId {
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
            let new_id =
                self.alloc_con_var_bind_path_set_hash(ConceptVariableBindingPathSetHash::new(INVALID));
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
            let new_id =
                self.alloc_con_prop_binding_set_hash(ConceptPropagationBindingSetHash::new(INVALID));
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
}

impl Default for ProcessContext {
    fn default() -> Self {
        Self::new()
    }
}
