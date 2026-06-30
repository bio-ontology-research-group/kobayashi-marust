//! `process` — the runtime completion-graph data model (Konclude
//! `Source/Reasoner/Kernel/Process/`): the per-satisfiability-test state the
//! completion engine mutates. Built on the `model` foundation + `substrate`.
//!
//! Canonical process-layer id aliases live here (the W2 coherence anchor, the
//! analogue of `model/mod.rs`). Each `Id<T>` points at the real ported struct,
//! so an `Arena<T>` is indexed by its `Id<T>`. See `manifest/05-process-units.md`
//! for the field-level decomposition and the struct→file mapping.

use super::model::substrate::Id;

pub mod stubs;       // W2: shared not-yet-ported `Process/` placeholder markers + ids
pub mod edge;        // SD-1: CIndividualLinkEdge + distinct/disjoint edges
pub mod descriptor;  // SD-1: CConceptDescriptor / CConceptProcessDescriptor / clash
pub mod node;        // SD-3: CIndividualProcessNode (the completion-graph node)
pub mod pn1;         // PN-1: CIndividualProcessNode init/ctor/buffer-handoff method bodies
pub mod sat_node;    // SD-4: CIndividualSaturationProcessNode
pub mod sat1;        // SAT-1: CIndividualSaturationProcessNode method bodies
pub mod satellites;  // SD-4: reapply label set, role-succ hash, branching-merging spec
pub mod rs1;         // RS-1: CReapplyRoleSuccessorHash method bodies (over `satellites`)
pub mod ls1;         // LS-1: CReapplyConceptLabelSet method bodies (over `satellites`)
pub mod bm1;         // BM-1: CBranchingMergingProcessingRestrictionSpecification method bodies (over `satellites`)
pub mod databox;     // SD-2: CProcessingDataBox (ambient per-test state; not an Id)
pub mod db1;         // DB-1: CProcessingDataBox lifecycle / save-restore methods
pub mod db2;         // DB-2: CProcessingDataBox method bodies (Wave-B)
pub mod db3;         // DB-3: CProcessingDataBox method bodies (Wave-B)
pub mod db4;         // DB-4: CProcessingDataBox method bodies (Wave-B)
pub mod db5;         // DB-5: CProcessingDataBox method bodies (Wave-B)
pub mod db6;         // DB-6: CProcessingDataBox method bodies (Wave-B)
pub mod pn2;         // PN-2: CIndividualProcessNode method bodies (Wave-B)
pub mod pn3;         // PN-3: CIndividualProcessNode method bodies (Wave-B)
pub mod pn4;         // PN-4: CIndividualProcessNode method bodies (Wave-B)
pub mod pn5;         // PN-5: CIndividualProcessNode method bodies (Wave-B)
pub mod pn6;         // PN-6: CIndividualProcessNode method bodies (Wave-B)
pub mod dependency;  // SD-5: the DependencyNode tagged enum + track points / branch tree
pub mod dep1;        // DEP-1: CDependencyNode ctors/accessors + DependencyLink chain ops + track-point accessors
pub mod dep2;        // DEP-2: track-point / branch-tree-node / branching-instruction / dependency-link methods
pub mod context;     // W3.5: CProcessContext — the per-test arena-owning container (the id-resolution root)
pub mod varbind;     // W2.7: variable-binding-path satellite subsystem (7 arenas)
pub mod binding_hash; // W3b: node-owned concept→binding-set container hashes (varbind-path + propagation)
pub mod propagation_binding; // W3c: propagation-binding subsystem (set/map/descriptor/binding; 4 arenas)
pub mod distinct;    // W2.7: distinct / connection-successor / disjoint-role satellites (4 arenas)
pub mod reapply_sat; // W2.7: reapply label-set iterator / signature blocking-candidate / incremental-expansion (4 arenas)
pub mod node_resolution; // node-resolution keystone: CProcessTagger + CIndividualProcessNodeVector + getUpToDate/Localized/Successor/Ancestor resolvers (ctx-level)
pub mod blocking_hash; // W3.5b: blocking-individual-node candidate hash/data/iterator + signature-blocking concept-expansion data (3 arenas)
pub mod representative; // W3.5r: representative variable-binding-path-set subsystem (set-data/migrate-data/propagation-set/descriptor; 4 arenas)
pub mod condensed_reapply; // u15: CCondensedReapplyQueue (dynamic reapply-queue head + descriptor linker, feeds the reapply_sat iterator)
pub mod merging_hash; // u15/nominal: CIndividualMergingHash + CIndividualMergingHashData (per-node merge hash; 1 arena)
pub mod succ_role_hash; // u15: CSuccessorRoleHash backend + CSuccessorRoleIterator / CSuccessorIterator (so pn3 relocation iterators iterate; 1 arena)

// --- the 16 process-layer ids (manifest/05) ---
/// `CIndividualProcessNode*`           → `NodeId`.
pub type NodeId = Id<node::IndividualProcessNode>;
/// `CIndividualSaturationProcessNode*` → `SatNodeId`.
pub type SatNodeId = Id<sat_node::IndividualSaturationProcessNode>;
/// `CIndividualLinkEdge*`              → `EdgeId`.
pub type EdgeId = Id<edge::IndividualLinkEdge>;
/// `CDistinctRoleAssertionLinkEdge*`-ish → `DistinctEdgeId`.
pub type DistinctEdgeId = Id<edge::DistinctEdge>;
/// disjoint-edge record                → `DisjointEdgeId`.
pub type DisjointEdgeId = Id<edge::DisjointEdge>;
/// `CConceptDescriptor*`               → `ConDescId`.
pub type ConDescId = Id<descriptor::ConceptDescriptor>;
/// `CConceptProcessDescriptor*`        → `ConProcDescId`.
pub type ConProcDescId = Id<descriptor::ConceptProcessDescriptor>;
/// clash descriptor                    → `ClashDescId`.
pub type ClashDescId = Id<descriptor::ClashDescriptor>;
/// `CReapplyConceptLabelSet*`          → `LabelSetId`.
pub type LabelSetId = Id<satellites::ReapplyConceptLabelSet>;
/// `CReapplyRoleSuccessorHash*`        → `RoleSuccHashId`.
pub type RoleSuccHashId = Id<satellites::ReapplyRoleSuccessorHash>;
/// `CBranchingMergingProcessingRestrictionSpecification*` → `RestrictionSpecId`.
pub type RestrictionSpecId = Id<satellites::BranchingMergingProcessingRestrictionSpecification>;
/// `CDependencyNode*` (the tagged enum)→ `DependencyId`.
pub type DependencyId = Id<dependency::DependencyNode>;
/// `CDependencyTrackPoint*`            → `TrackPointId`.
pub type TrackPointId = Id<dependency::DependencyTrackPoint>;
/// dependency link record              → `DepLinkId`.
pub type DepLinkId = Id<dependency::DependencyLink>;
/// `CBranchTreeNode*`                  → `BranchNodeId`.
pub type BranchNodeId = Id<dependency::BranchTreeNode>;
/// branching-instruction record        → `BranchInstrId`.
pub type BranchInstrId = Id<dependency::BranchingInstruction>;
