//! `process::dep2` — DEP-2 method bodies for the dependency / backjumping spine
//! (manifest/05-process-units.md §3, unit **DEP-2**): `CBranchingTree` /
//! `CBranchTreeNode` + the deterministic / non-deterministic / OR-disjunct
//! track-point logic, plus the `CDependency` link methods and the
//! `CBranchingInstruction` recorded branch decision.
//!
//! The struct definitions live in `process::dependency` (SD-5); this file adds
//! the ported method bodies as additional inherent `impl` blocks on those types.
//! Folded-class methods (the `CNonDeterministicDependencyTrackPoint` /
//! `CORDisjunctDependencyTrackPoint` accessors, and the `…AddIndividualConcepts`
//! branching-instruction subclass) become methods on the single folded
//! `DependencyTrackPoint` / `BranchingInstruction` structs respectively.
//!
//! KONCLUDE-PORT-NOTE[ownership]: Konclude's `init*` methods return `this` and
//! `mRootNode = this` self-references the live object. Here a node is addressed
//! by its `BranchNodeId` into the per-test `Arena<BranchTreeNode>`, so the few
//! methods that read a *sibling* node (parent/copy) while writing `this`, or that
//! self-reference `this`, take the arena + the node's own id rather than `&self`
//! (the `&mut self` borrow would alias the arena). Per-node-only methods keep the
//! plain `&self` / `&mut self` form. See `model/substrate.rs` for the single
//! global decision.

#![allow(dead_code)]

use super::super::model::{Arena, Cint64, ConceptId, NegLink};
use super::context::ProcessContext;
use super::dependency::{
    BranchTreeNode, BranchingInstruction, BranchingInstructionType, DependencyLink,
    DependencyTrackPoint,
};
use super::{BranchNodeId, ClashDescId, DepLinkId, DependencyId, NodeId, TrackPointId};

// ===========================================================================
// CDependencyTrackPoint (+ folded CNonDeterministicDependencyTrackPoint
//                          + folded CORDisjunctDependencyTrackPoint)
// ===========================================================================
impl DependencyTrackPoint {
    /// Port of `CDependencyTrackPoint::CDependencyTrackPoint(CDependencyNode*)`
    /// folded with the `CNonDeterministicDependencyTrackPoint` and
    /// `CORDisjunctDependencyTrackPoint` constructors (each only nulls its own
    /// extension members, so one fully-defaulted record covers all three).
    pub fn new(dep_node: DependencyId) -> Self {
        DependencyTrackPoint {
            // CBranchingTag(0) base.
            process_tag: 0,
            dep_node,
            relevant_flag: false,
            // CNonDeterministicDependencyTrackPoint extension.
            clashes: ClashDescId::NONE,
            branch_node: BranchNodeId::NONE,
            clashed_irrelevant: false,
            involved_indi_ids: Vec::new(),
            next: TrackPointId::NONE,
            // CORDisjunctDependencyTrackPoint extension.
            disjunct_concept_linker: Vec::new(),
            disjunct_branch_stats: super::super::model::INVALID,
        }
    }

    // KM-COHERENCE[dedup]: processing_tag / is_pointing_to_deterministic_dependency_node
    // / is_pointing_to_independent_dependency_node are the "plain CDependencyTrackPoint
    // accessors" owned by DEP-1 (dep1.rs); removed here to avoid duplicate definitions.

    /// Port of `CBranchingTag::addMaximumBranchingTagCandidate(cint64)`. The
    /// non-deterministic track point multiply-inherits `CBranchingTag`, so this
    /// raises the track point's own `mProcessTag`. Used by `init_branch`.
    pub fn add_maximum_branching_tag_candidate(&mut self, branching_tag: Cint64) -> bool {
        if branching_tag > self.process_tag || branching_tag < 0 {
            self.process_tag = branching_tag;
            return true;
        }
        false
    }

    /// Port of `CNonDeterministicDependencyTrackPoint::initBranch(CBranchTreeNode*)`.
    /// `mBranchNode = branchNode; addMaximumBranchingTagCandidate(mBranchNode->getBranchingLevel());`
    pub fn init_branch(&mut self, branch_node: BranchNodeId, branches: &Arena<BranchTreeNode>) {
        self.branch_node = branch_node;
        // C++ unconditionally derefs mBranchNode; the live call site always passes
        // a non-null branch node.
        let level = branches.get(branch_node).get_branching_level();
        self.add_maximum_branching_tag_candidate(level);
    }

    /// Port of `CNonDeterministicDependencyTrackPoint::getClashes()`.
    pub fn get_clashes(&self) -> ClashDescId {
        self.clashes
    }

    /// Port of `CBranchingTag::getBranchingTag()` (inherited base accessor).
    /// The track point multiply-inherits `CBranchingTag`; the tag is its own
    /// `mProcessTag`.
    pub fn get_branching_tag(&self) -> Cint64 {
        self.process_tag
    }

    /// Port of `CNonDeterministicDependencyTrackPoint::addClashes(CClashedDependencyDescriptor*, bool)`.
    /// `if (clashes) { mClashes = clashes->append(mClashes); mClashedIrelevant |= setClashed; }`
    pub fn add_clashes(
        &mut self,
        process_context: &mut ProcessContext,
        clashes: ClashDescId,
        set_clashed: bool,
    ) {
        if clashes.is_some() {
            self.clashes = process_context.append_clash_descriptor_chain(clashes, self.clashes);
            self.clashed_irrelevant |= set_clashed;
        }
    }

    /// Port of `CNonDeterministicDependencyTrackPoint::setClashes(CClashedDependencyDescriptor*, bool)`.
    pub fn set_clashes(&mut self, clashes: ClashDescId, set_clashed: bool) {
        self.clashes = clashes;
        self.clashed_irrelevant |= set_clashed;
    }

    /// Port of `CNonDeterministicDependencyTrackPoint::getBranchNode()`.
    pub fn get_branch_node(&self) -> BranchNodeId {
        self.branch_node
    }

    /// Port of `CNonDeterministicDependencyTrackPoint::isClashedOrIrelevantBranch()`.
    pub fn is_clashed_or_irelevant_branch(&self) -> bool {
        self.clashed_irrelevant
    }

    /// Port of `CNonDeterministicDependencyTrackPoint::setClashedOrIrelevantBranch(bool)`.
    pub fn set_clashed_or_irelevant_branch(&mut self, clashed_or_irelevant: bool) {
        self.clashed_irrelevant = clashed_or_irelevant;
    }

    /// Port of `CNonDeterministicDependencyTrackPoint::getInvolvedIndividualIdsLinker()`.
    /// KONCLUDE-PORT-NOTE[ownership]: the `CXLinker<cint64>*` chain is the
    /// `involved_indi_ids: Vec<Cint64>` field; returns it as a slice.
    pub fn get_involved_individual_ids_linker(&self) -> &[Cint64] {
        &self.involved_indi_ids
    }

    /// Port of `CNonDeterministicDependencyTrackPoint::setInvolvedIndividualIdsLinker(CXLinker<cint64>*)`.
    pub fn set_involved_individual_ids_linker(&mut self, linker: Vec<Cint64>) {
        self.involved_indi_ids = linker;
    }

    /// Port of `CORDisjunctDependencyTrackPoint::getDisjunctConceptLinker()`.
    pub fn get_disjunct_concept_linker(&self) -> &[NegLink<ConceptId>] {
        &self.disjunct_concept_linker
    }

    /// Port of `CORDisjunctDependencyTrackPoint::getDisjunctBranchingStatistics()`.
    /// KONCLUDE-PORT-NOTE[ownership]: `CDisjunctBranchingStatistics*` held as the
    /// opaque `disjunct_branch_stats: Cint64` until that side object is ported
    /// (`INVALID` when unset).
    pub fn get_disjunct_branching_statistics(&self) -> Cint64 {
        self.disjunct_branch_stats
    }

    /// Port of `CORDisjunctDependencyTrackPoint::setDisjunctConceptLinker(CSortedNegLinker<CConcept*>*)`.
    pub fn set_disjunct_concept_linker(&mut self, disjunct_con_linker: Vec<NegLink<ConceptId>>) {
        self.disjunct_concept_linker = disjunct_con_linker;
    }

    /// Port of `CORDisjunctDependencyTrackPoint::setDisjunctBranchingStatistics(CDisjunctBranchingStatistics*)`.
    pub fn set_disjunct_branching_statistics(&mut self, disjunct_branch_stats: Cint64) {
        self.disjunct_branch_stats = disjunct_branch_stats;
    }
}

// ===========================================================================
// CDependency  (Rust name DependencyLink)
// ===========================================================================
impl DependencyLink {
    /// Port of `CDependency::CDependency()`
    /// (`CLinkerBase(this,nullptr); mDepTrackPoint = nullptr;`).
    pub fn new() -> Self {
        DependencyLink {
            dep_track_point: TrackPointId::NONE,
            next: DepLinkId::NONE,
        }
    }

    // KM-COHERENCE[dedup]: init_dependency / previous_tracked_dependency /
    // add_additional_dependency are ported once in DEP-1 (dep1.rs), which owns the
    // DependencyLink chain ops. Removed here to avoid duplicate definitions; dep1's
    // init_dependency returns `&mut Self` (faithful to C++ `return this`).
}

impl Default for DependencyLink {
    fn default() -> Self {
        Self::new()
    }
}

// ===========================================================================
// CBranchTreeNode
// ===========================================================================
impl BranchTreeNode {
    /// Port of `CBranchTreeNode::CBranchTreeNode(CProcessContext*)`.
    /// KONCLUDE-PORT-NOTE[ownership]: `mProcessContext` is the ambient `&mut`
    /// context in the port, not a stored field; the ctor only nulls the carried
    /// members. `mParentNode`/`mRootNode` are left `NONE` (set by the `init*`
    /// methods, exactly as the C++ ctor leaves them uninitialised).
    pub fn new() -> Self {
        BranchTreeNode {
            process_tag: 0,
            parent_node: BranchNodeId::NONE,
            root_node: BranchNodeId::NONE,
            branched_dep_track_point: TrackPointId::NONE,
            sat_calc_task: super::super::model::INVALID,
        }
    }

    /// Port of `CBranchingTag::getBranchingLevel()` (== `getBranchingTag()` ==
    /// `CProcessTag::getProcessTag()` == `mProcessTag`).
    #[inline]
    pub fn get_branching_level(&self) -> Cint64 {
        self.process_tag
    }

    /// Port of `CBranchingTag::setBranchingTag(cint64)`.
    #[inline]
    pub fn set_branching_tag(&mut self, branching_tag: Cint64) {
        self.process_tag = branching_tag;
    }

    /// Port of `CBranchingTag::initBranchingTag(cint64)`.
    /// KONCLUDE-PORT-NOTE[ownership]: `CProcessTag::initProcessTag` reduces to a
    /// plain assignment under the `process_tag: Cint64` substrate model.
    #[inline]
    pub fn init_branching_tag(&mut self, branching_tag: Cint64) {
        self.process_tag = branching_tag;
    }

    /// Port of `CBranchingTag::incBranchingTag(cint64)` (`++mProcessTag;` — the
    /// `incCount` argument is ignored in the original, faithfully reproduced).
    #[inline]
    pub fn inc_branching_tag(&mut self, _inc_count: Cint64) {
        self.process_tag += 1;
    }

    /// Port of `CBranchTreeNode::initBranchingRootNode(CSatisfiableCalculationTask*)`.
    /// Takes the node's own id for the `mRootNode = this` self-reference.
    pub fn init_branching_root_node(&mut self, this: BranchNodeId, sat_calc_task: Cint64) {
        self.parent_node = BranchNodeId::NONE;
        self.root_node = this;
        self.init_branching_tag(0);
        self.sat_calc_task = sat_calc_task;
    }

    /// Port of `CBranchTreeNode::initBranchingChildNode(CBranchTreeNode*, CSatisfiableCalculationTask*)`.
    /// KONCLUDE-PORT-NOTE[ownership]: associated fn over the arena — reads the
    /// parent (`mRootNode`, `getBranchingLevel()`) before writing `this`.
    pub fn init_branching_child_node(
        branches: &mut Arena<BranchTreeNode>,
        this: BranchNodeId,
        parent_branch_tree_node: BranchNodeId,
        sat_calc_task: Cint64,
    ) {
        // Pre-read the parent (the C++ `parentBranchTreeNode->…` derefs).
        let (parent_root, parent_level) = if parent_branch_tree_node.is_some() {
            let parent = branches.get(parent_branch_tree_node);
            (parent.root_node, parent.get_branching_level())
        } else {
            (BranchNodeId::NONE, 0)
        };
        let node = branches.get_mut(this);
        node.sat_calc_task = sat_calc_task;
        node.branched_dep_track_point = TrackPointId::NONE;
        node.parent_node = parent_branch_tree_node;
        node.root_node = BranchNodeId::NONE;
        node.init_branching_tag(0);
        if parent_branch_tree_node.is_some() {
            node.root_node = parent_root;
            node.set_branching_tag(parent_level);
        }
    }

    /// Port of `CBranchTreeNode::initBranchingCopyNode(CBranchTreeNode*, CSatisfiableCalculationTask*)`.
    /// KONCLUDE-PORT-NOTE[ownership]: associated fn over the arena — reads the
    /// copy source before writing `this`. `copy->isRootNode()` is `mRootNode == copy`.
    pub fn init_branching_copy_node(
        branches: &mut Arena<BranchTreeNode>,
        this: BranchNodeId,
        copy_branch_tree_node: BranchNodeId,
        sat_calc_task: Cint64,
    ) {
        let (copy_dtp, copy_parent, copy_root, copy_level, copy_is_root) = {
            let copy = branches.get(copy_branch_tree_node);
            (
                copy.branched_dep_track_point,
                copy.parent_node,
                copy.root_node,
                copy.get_branching_level(),
                copy.root_node == copy_branch_tree_node,
            )
        };
        let node = branches.get_mut(this);
        node.sat_calc_task = sat_calc_task;
        node.branched_dep_track_point = copy_dtp;
        node.parent_node = copy_parent;
        node.root_node = copy_root;
        node.set_branching_tag(copy_level);
        if copy_is_root {
            node.root_node = this;
        }
    }

    /// Port of `CBranchTreeNode::getRootNode()`.
    #[inline]
    pub fn get_root_node(&self) -> BranchNodeId {
        self.root_node
    }

    /// Port of `CBranchTreeNode::branchingIncrement(CNonDeterministicDependencyTrackPoint*)`.
    /// `incBranchingTag(); mBranchedDepTrackPoint = depTrackPoint;`
    pub fn branching_increment(&mut self, dep_track_point: TrackPointId) {
        self.inc_branching_tag(1);
        self.branched_dep_track_point = dep_track_point;
    }

    /// Port of `CBranchTreeNode::getSatisfiableCalculationTask()`.
    /// KONCLUDE-PORT-NOTE[ownership]: opaque `Cint64` handle until the Task layer
    /// lands (see `BranchTreeNode::sat_calc_task`).
    #[inline]
    pub fn get_satisfiable_calculation_task(&self) -> Cint64 {
        self.sat_calc_task
    }
}

impl Default for BranchTreeNode {
    fn default() -> Self {
        Self::new()
    }
}

// ===========================================================================
// CBranchingInstruction (+ folded CBranchingInstructionAddIndividualConcepts)
// ===========================================================================
impl BranchingInstruction {
    /// Port of `CBranchingInstructionAddIndividualConcepts::CBranchingInstructionAddIndividualConcepts()`
    /// (the abstract `CBranchingInstruction()` base ctor is a no-op). Folds the
    /// single concrete subclass; `kind` fixes the only variant today.
    pub fn new() -> Self {
        BranchingInstruction {
            kind: BranchingInstructionType::AddIndividualConcepts,
            adding_individual_node: NodeId::NONE,
            adding_concept_linker: Vec::new(),
            adding_dep_track_point: TrackPointId::NONE,
        }
    }

    /// Port of `CBranchingInstructionAddIndividualConcepts::initAddIndividualConceptsBranchingInstruction(
    /// CIndividualProcessNode*, CSortedNegLinker<CConcept*>*, CDependencyTrackPoint*)`.
    pub fn init_add_individual_concepts_branching_instruction(
        &mut self,
        indi_node: NodeId,
        adding_concept_linker: Vec<NegLink<ConceptId>>,
        adding_dep_track_point: TrackPointId,
    ) {
        self.adding_individual_node = indi_node;
        self.adding_dep_track_point = adding_dep_track_point;
        self.adding_concept_linker = adding_concept_linker;
    }

    /// Port of `CBranchingInstructionAddIndividualConcepts::getAddingConceptLinker()`.
    pub fn get_adding_concept_linker(&self) -> &[NegLink<ConceptId>] {
        &self.adding_concept_linker
    }
}

impl Default for BranchingInstruction {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::super::descriptor::ClashDescriptor;
    use super::*;

    #[test]
    fn dep2_add_clashes_prepends_chain_and_preserves_old_head() {
        let mut ctx = ProcessContext::new();
        let old_head = ctx.alloc_clash_desc(ClashDescriptor::new());
        let new_head = ctx.alloc_clash_desc(ClashDescriptor::new());
        let new_tail = ctx.alloc_clash_desc(ClashDescriptor::new());
        ctx.clash_desc_mut(new_head).set_next(new_tail);

        let mut track_point = DependencyTrackPoint::new(DependencyId::NONE);
        track_point.set_clashes(old_head, false);
        track_point.add_clashes(&mut ctx, new_head, true);

        assert_eq!(track_point.get_clashes(), new_head);
        assert_eq!(ctx.clash_desc(new_head).get_next(), new_tail);
        assert_eq!(ctx.clash_desc(new_tail).get_next(), old_head);
        assert_eq!(ctx.clash_desc(old_head).get_next(), ClashDescId::NONE);
        assert!(track_point.is_clashed_or_irelevant_branch());
    }

    #[test]
    fn dep2_add_clashes_ignores_none_without_setting_flag() {
        let mut ctx = ProcessContext::new();
        let mut track_point = DependencyTrackPoint::new(DependencyId::NONE);

        track_point.add_clashes(&mut ctx, ClashDescId::NONE, true);

        assert_eq!(track_point.get_clashes(), ClashDescId::NONE);
        assert!(!track_point.is_clashed_or_irelevant_branch());
    }
}
