//! `process::dep1` — DEP-1 method bodies for the dependency-node spine
//! (Konclude `Source/Reasoner/Kernel/Process/Dependency/`).
//!
//! This is the **DEP-1** port unit (manifest/05-process-units.md §3): the
//! `CDependencyNode` ctors/accessors, the per-subclass `init…DependencyNode`
//! methods, `CDependency` (`DependencyLink`) chain ops, and the plain
//! `CDependencyTrackPoint` accessors. The struct definitions live in
//! `process/dependency.rs` (SD-5); this file only fills the methods, in `impl`
//! blocks added onto those types.
//!
//! ## Virtual dispatch → enum dispatch
//! Konclude's dependency-node hierarchy uses C++ virtual methods
//! (`isDeterministiDependencyNode`, `getContinueDependencyTrackPoint`,
//! `getDependencyTrackPointBranch`, `isRepresentative{Resolve,Select}…`). The
//! port collapsed the 63 concrete `C*DependencyNode` classes into the
//! `DependencyNode` enum's 7 structural variants carrying a 64-value `DepKind`
//! tag (see `dependency.rs`). Every virtual is reproduced as a `match` on either
//! the **variant** (when the override depends on the payload shape — e.g.
//! `getContinueDependencyTrackPoint` returns the clash track point only for the
//! non-deterministic family) or the **`DepKind` discriminant** (when the override
//! tracks the exact tag — e.g. `isRepresentativeResolveDependencyNode` is `true`
//! only for `ResolveRepresentative`). This keeps the dispatch behaviour
//! bit-identical to the C++ vtable while staying within one owned object.
//!
//! KONCLUDE-PORT-NOTE[ownership]: every `CXxx*` is a typed arena id; intrusive
//! `CLinkerBase` chains are walked through the relevant `Arena<…>` threaded in as
//! a parameter (the ambient `CProcessContext` is not an object here). `nullptr`
//! → `Id::NONE`. See `model/substrate.rs` for the single global decision.
//!
//! Branching-tag machinery (`CBranchingTag::addMaximumBranchingTagCandidate` /
//! `getBranchingTag`, `updateBranchingTag(s)`, `getDependedBranchingTag`) and the
//! allocating branch openers (`getDependencyTrackPointBranch`) belong to the
//! backjumping spine ported in **DEP-2**; calls into them are marked
//! `// W2-DEFER[api]` and stubbed here.

#![allow(dead_code)]

use super::super::model::substrate::{Arena, Cint64};
use super::dependency::{
    DepKind, DependencyLink, DependencyNode, DependencyTrackPoint, NonDetData,
};
use super::{BranchNodeId, ClashDescId, ConDescId, DependencyId, DepLinkId, NodeId, TrackPointId};

// ===========================================================================
// CDependencyNode — ctors / accessors  (CDependencyNode.cpp 232–422)
// ===========================================================================

impl DependencyNode {
    /// Port of `CDependencyNode::initDependencyNode(DEPENDENCNODEYTYPE, CConceptDescriptor*)`.
    pub fn init_dependency_node(
        &mut self,
        dep_type: DepKind,
        concept_descriptor: ConDescId,
    ) -> &mut Self {
        let base = self.base_mut();
        base.concept_descriptor = concept_descriptor;
        base.kind = dep_type;
        // mMarker = nullptr; (commented out in Konclude)
        base.individual_node = NodeId::NONE;
        self
    }

    /// Port of `CDependencyNode::initDependencyNode(DEPENDENCNODEYTYPE, CIndividualProcessNode*, CConceptDescriptor*)`.
    pub fn init_dependency_node_indi(
        &mut self,
        dep_type: DepKind,
        individual_node: NodeId,
        concept_descriptor: ConDescId,
    ) -> &mut Self {
        self.init_dependency_node(dep_type, concept_descriptor);
        self.base_mut().individual_node = individual_node;
        self
    }

    /// Port of `CDependencyNode::setConceptDescriptor`.
    pub fn set_concept_descriptor(&mut self, concept_descriptor: ConDescId) -> &mut Self {
        self.base_mut().concept_descriptor = concept_descriptor;
        self
    }

    /// Port of `CDependencyNode::getPreviousDependencyTrackPoint` (the node's
    /// `mDepTrackPoint`; distinct from `DependencyLink`'s same-named accessor).
    pub fn previous_dependency_track_point(&self) -> TrackPointId {
        self.base().dep_track_point
    }

    /// Port of `CDependencyNode::isNonDeterministiDependencyNode`
    /// (`return !isDeterministiDependencyNode()`).
    pub fn is_non_deterministic(&self) -> bool {
        !self.is_deterministic()
    }

    /// Port of `CDependencyNode::getAdditionalAfterDependencies`.
    pub fn additional_after_dependencies(&self) -> DepLinkId {
        self.base().additional_after
    }

    /// Port of `CDependencyNode::getAdditionalDependencyCount` — counts the
    /// after-dependency `CDependency` chain (`CLinkerBase::getCount`).
    pub fn additional_dependency_count(&self, dep_arena: &Arena<DependencyLink>) -> Cint64 {
        let mut dep_count: Cint64 = 0;
        let head = self.base().additional_after;
        if head.is_some() {
            dep_count += link_get_count(head, dep_arena);
        }
        dep_count
    }

    /// Port of `CDependencyNode::hasAdditionalDependencies`.
    pub fn has_additional_dependencies(&self) -> bool {
        self.base().additional_after.is_some()
    }

    /// Port of `CDependencyNode::hasAdditionalAfterDependencies`.
    pub fn has_additional_after_dependencies(&self) -> bool {
        self.base().additional_after.is_some()
    }

    /// Port of `CDependencyNode::hasDependencies`
    /// (`mAdditionalAfterDepLinker || mDepTrackPoint`).
    pub fn has_dependencies(&self) -> bool {
        self.base().additional_after.is_some() || self.base().dep_track_point.is_some()
    }

    /// Port of `CDependencyNode::getDependencyCount`.
    pub fn dependency_count(&self, dep_arena: &Arena<DependencyLink>) -> Cint64 {
        let mut dep_count: Cint64 = 0;
        if self.base().dep_track_point.is_some() {
            dep_count += 1;
        }
        dep_count += self.additional_dependency_count(dep_arena);
        dep_count
    }

    /// Port of `CDependencyNode::isDependencyType`.
    pub fn is_dependency_type(&self, dep_type: DepKind) -> bool {
        self.base().kind == dep_type
    }

    /// Port of `CDependencyNode::isIndependentBaseDependencyType`.
    pub fn is_independent_base_dependency_type(&self) -> bool {
        self.is_dependency_type(DepKind::IndependentBase)
    }

    /// Port of `CDependencyNode::isUndefinedDependencyType`.
    pub fn is_undefined_dependency_type(&self) -> bool {
        self.is_dependency_type(DepKind::Undefined)
    }

    /// Port of `CDependencyNode::hasAppropriateIndividualNode`.
    pub fn has_appropriate_individual_node(&self) -> bool {
        self.base().individual_node.is_some()
    }

    /// Port of `CDependencyNode::setAppropriateIndividualNode`.
    pub fn set_appropriate_individual_node(&mut self, indi_node: NodeId) -> &mut Self {
        self.base_mut().individual_node = indi_node;
        self
    }

    /// Port of `CDependencyNode::addAfterDependency`
    /// (`mAdditionalAfterDepLinker = linkDependency->append(mAdditionalAfterDepLinker)`).
    /// `append` splices the old chain onto the *tail* of `link` and makes `link`
    /// the new head — the prepend Konclude relies on.
    pub fn add_after_dependency(&mut self, link: DepLinkId, dep_arena: &mut Arena<DependencyLink>) -> &mut Self {
        let old_head = self.base().additional_after;
        let new_head = link_append(link, old_head, dep_arena);
        self.base_mut().additional_after = new_head;
        self
    }

    /// Port of `CDependencyNode::isRepresentativeResolveDependencyNode` (virtual).
    /// Base returns `false`; `CRepresentativeResolveDependencyNode` (the base of
    /// the `ResolveRepresentative` tag) overrides it to `true`.
    pub fn is_representative_resolve_dependency_node(&self) -> bool {
        // KONCLUDE-PORT-NOTE[overload]: the `true` override lives on the
        // intermediate base `CRepresentativeResolveDependencyNode`, whose only
        // concrete tag is `DNTRESOLVEREPRESENTATIVE`.
        matches!(self.base().kind, DepKind::ResolveRepresentative)
    }

    /// Port of `CDependencyNode::isRepresentativeSelectDependencyNode` (virtual).
    /// Base returns `false`; `CRepresentativeSelectDependencyNode` (base of the
    /// `RepresentativeBindVariable` / `RepresentativeGrounding` tags) → `true`.
    pub fn is_representative_select_dependency_node(&self) -> bool {
        matches!(
            self.base().kind,
            DepKind::RepresentativeBindVariable | DepKind::RepresentativeGrounding
        )
    }

    // -------------------------------------------------------------------
    // CDeterministicDependencyNode / CNonDeterministicDependencyNode virtuals
    // -------------------------------------------------------------------

    /// Port of the `getContinueDependencyTrackPoint()` virtual.
    /// `CDeterministicDependencyNode` returns `this` (the det node *is* its own
    /// track point); `CNonDeterministicDependencyNode` returns `&mClashTrackPoint`.
    pub fn continue_dependency_track_point(&self) -> TrackPointId {
        match self {
            DependencyNode::NonDeterministic { nd, .. }
            | DependencyNode::Or { nd, .. }
            | DependencyNode::ReuseBackendModes { nd, .. } => nd.clash_track_point,
            // Deterministic family: `return this;`. The det node is its own track
            // point, materialised lazily from the node in the unified TrackPointId
            // space. W2-DEFER[api]: lazy det-node→track-point materialisation lands
            // with the branch save/restore plumbing in DEP-2.
            _ => TrackPointId::NONE,
        }
    }
}

// ===========================================================================
// Per-subclass `init…DependencyNode` constructors.
//
// Konclude has one `initXxxDependencyNode` per concrete class; under the
// 7-variant collapse the *shape* of the init is fixed by the variant, so the
// generic deterministic / non-deterministic inits below cover every tag-only
// subclass (pass the subclass's `DepKind`). The named inits that follow show
// the payload-carrying shapes (1/2 back-edges, OR disjunct, reuse-backend).
// ===========================================================================

impl DependencyNode {
    /// Port of `CIndependentBaseDependencyNode::initIndependentBaseDependencyNode`
    /// (`initDependencyNode(DNTINDEPENDENTBASE, nullptr, nullptr)`).
    pub fn init_independent_base_dependency_node(&mut self) -> &mut Self {
        self.init_dependency_node_indi(DepKind::IndependentBase, NodeId::NONE, ConDescId::NONE);
        self
    }

    /// Port of `CDeterministicDependencyNode::initDeterministicDependencyNode(depType, conceptDescriptor)`.
    /// Covers every tag-only deterministic subclass (`AND`, `SOME`, `SELF`, … —
    /// they each just call `initDependencyNode(theirTag, …)`).
    pub fn init_deterministic_dependency_node(
        &mut self,
        dep_type: DepKind,
        concept_descriptor: ConDescId,
    ) -> &mut Self {
        self.init_dependency_node(dep_type, concept_descriptor);
        self
    }

    /// Port of `CDeterministicDependencyNode::initDeterministicDependencyNode(depType, individualNode, conceptDescriptor)`.
    pub fn init_deterministic_dependency_node_indi(
        &mut self,
        dep_type: DepKind,
        individual_node: NodeId,
        concept_descriptor: ConDescId,
    ) -> &mut Self {
        self.init_dependency_node_indi(dep_type, individual_node, concept_descriptor);
        self
    }

    /// Port of `CNonDeterministicDependencyNode::initNonDeterministicDependencyNode(depType, branchNode, conceptDescriptor)`.
    pub fn init_non_deterministic_dependency_node(
        &mut self,
        dep_type: DepKind,
        branch_node: BranchNodeId,
        concept_descriptor: ConDescId,
        tp_arena: &mut Arena<DependencyTrackPoint>,
    ) -> &mut Self {
        self.init_dependency_node(dep_type, concept_descriptor);
        self.setup_non_deterministic(branch_node, tp_arena);
        self
    }

    /// Port of `CNonDeterministicDependencyNode::initNonDeterministicDependencyNode(depType, branchNode, individualNode, conceptDescriptor)`.
    pub fn init_non_deterministic_dependency_node_indi(
        &mut self,
        dep_type: DepKind,
        branch_node: BranchNodeId,
        individual_node: NodeId,
        concept_descriptor: ConDescId,
        tp_arena: &mut Arena<DependencyTrackPoint>,
    ) -> &mut Self {
        self.init_dependency_node_indi(dep_type, individual_node, concept_descriptor);
        self.setup_non_deterministic(branch_node, tp_arena);
        self
    }

    /// The shared body of the two non-deterministic inits (the C++ overloads run
    /// the identical `mClashTrackPoint`/`mBranchTrackPoints`/… setup after the
    /// base `initDependencyNode`).
    fn setup_non_deterministic(
        &mut self,
        branch_node: BranchNodeId,
        tp_arena: &mut Arena<DependencyTrackPoint>,
    ) {
        match self {
            DependencyNode::NonDeterministic { nd, .. }
            | DependencyNode::Or { nd, .. }
            | DependencyNode::ReuseBackendModes { nd, .. } => {
                // mClashTrackPoint.setClashedOrIrelevantBranch(true);
                tp_arena.get_mut(nd.clash_track_point).clashed_irrelevant = true;
                // mBranchTrackPoints = &mClashTrackPoint;
                nd.branch_track_points = nd.clash_track_point;
                nd.dependency_clashes = ClashDescId::NONE;
                nd.branch_node = branch_node;
                nd.branch_tag = 0;
                nd.closed_track_point = TrackPointId::NONE;
                nd.closing_track_point = TrackPointId::NONE;
            }
            _ => unreachable!(
                "initNonDeterministicDependencyNode invoked on a deterministic variant"
            ),
        }
    }

    /// Port of `CALLDependencyNode::initALLDependencyNode` — a representative
    /// **DetLink** (one back-edge `mPrevLinkDep`) constructor. Every other
    /// 1-back-edge deterministic tag (`AUTOMATTRANSACTION`, `DATAASSERTION`,
    /// `MERGEDLINK`, `NEGVALUE`, `NOMINAL`, `VALUE`, `ROLEASSERTION`,
    /// `SAMEINDIVIDUALSMERGE`, the `…SUCCESSOR`/`REPRESENTATIVE{ALL,JOIN}`/… set)
    /// follows this exact shape with its own `DepKind`.
    pub fn init_all_dependency_node(
        &mut self,
        concept_descriptor: ConDescId,
        individual_node: NodeId,
        prev_concept_dep_track_point: TrackPointId,
        prev_link_dep_track_point: TrackPointId,
        dep_arena: &mut Arena<DependencyLink>,
    ) -> &mut Self {
        self.init_dependency_node_indi(DepKind::All, individual_node, concept_descriptor);
        self.base_mut().dep_track_point = prev_concept_dep_track_point;
        if let DependencyNode::DetLink { prev, .. } = self {
            // mPrevLinkDep.initDependency(prevLinkDependencyTrackPoint);
            dep_arena.get_mut(*prev).dep_track_point = prev_link_dep_track_point;
        }
        // W2-DEFER[api]: updateBranchingTag() — CBranchingTag machinery (DEP-2).
        self
    }

    /// Port of `CMERGEDCONCEPTDependencyNode::initMERGEDCONCEPTDependencyNode` —
    /// also **DetLink**, but note Konclude's argument wiring: the *merging-step*
    /// track point goes to `mPrevLinkDep`, the *concept* track point to
    /// `mDepTrackPoint`.
    pub fn init_merged_concept_dependency_node(
        &mut self,
        concept_descriptor: ConDescId,
        prev_merging_step_dep_track_point: TrackPointId,
        prev_concept_dep_track_point: TrackPointId,
        dep_arena: &mut Arena<DependencyLink>,
    ) -> &mut Self {
        self.init_dependency_node(DepKind::MergedConcept, concept_descriptor);
        self.base_mut().dep_track_point = prev_concept_dep_track_point;
        if let DependencyNode::DetLink { prev, .. } = self {
            dep_arena.get_mut(*prev).dep_track_point = prev_merging_step_dep_track_point;
        }
        // W2-DEFER[api]: updateBranchingTag() (DEP-2).
        self
    }

    /// Port of `CFUNCTIONALDependencyNode::initFUNCTIONALDependencyNode` — the
    /// only **DetLink2** (two back-edges `mPrevLink1Dep`, `mPrevLink2Dep`).
    pub fn init_functional_dependency_node(
        &mut self,
        concept_descriptor: ConDescId,
        individual_node: NodeId,
        prev_concept_dep_track_point: TrackPointId,
        prev_link1_dep_track_point: TrackPointId,
        prev_link2_dep_track_point: TrackPointId,
        dep_arena: &mut Arena<DependencyLink>,
    ) -> &mut Self {
        self.init_dependency_node_indi(DepKind::Functional, individual_node, concept_descriptor);
        self.base_mut().dep_track_point = prev_concept_dep_track_point;
        if let DependencyNode::DetLink2 { prev1, prev2, .. } = self {
            dep_arena.get_mut(*prev1).dep_track_point = prev_link1_dep_track_point;
            dep_arena.get_mut(*prev2).dep_track_point = prev_link2_dep_track_point;
        }
        // W2-DEFER[api]: updateBranchingTag() (DEP-2).
        self
    }

    /// Port of `CORDependencyNode::initORDependencyNode` — non-deterministic +
    /// the OR-disjunct track data variant.
    pub fn init_or_dependency_node(
        &mut self,
        branch_node: BranchNodeId,
        concept_descriptor: ConDescId,
        dep_track_point: TrackPointId,
        tp_arena: &mut Arena<DependencyTrackPoint>,
    ) -> &mut Self {
        self.init_non_deterministic_dependency_node(
            DepKind::Or,
            branch_node,
            concept_descriptor,
            tp_arena,
        );
        self.base_mut().dep_track_point = dep_track_point;
        // W2-DEFER[api]: updateBranchingTags() (DEP-2).
        self
    }

    /// Port of `CREUSEBACKENDEXPANSIONMODESDependencyNode::initREUSEBACKENDEXPANSIONMODESDependencyNode`
    /// — non-deterministic + the `CXLinker<cint64>` involved-id list outlier.
    pub fn init_reuse_backend_expansion_modes_dependency_node(
        &mut self,
        branch_node: BranchNodeId,
        dep_track_point: TrackPointId,
        tp_arena: &mut Arena<DependencyTrackPoint>,
    ) -> &mut Self {
        self.init_non_deterministic_dependency_node_indi(
            DepKind::ReuseBackendExpansionModes,
            branch_node,
            NodeId::NONE,
            ConDescId::NONE,
            tp_arena,
        );
        self.base_mut().dep_track_point = dep_track_point;
        // W2-DEFER[api]: updateBranchingTags() (DEP-2).
        if let DependencyNode::ReuseBackendModes { involved, .. } = self {
            // mInvolvedIndividualIdLinker = nullptr;
            involved.clear();
        }
        // W2-DEFER[api]: mFixedReuseDepTrackPoint / mPriorizedReuseDepTrackPoint /
        // mAffectedIndividualIdLinker (the QAtomicPointer side fields) — reachable
        // through `nd.branch_track_points` per the dependency.rs fold; their
        // [threading] init lands with the reuse-backend method unit.
        self
    }
}

// ===========================================================================
// CNonDeterministicDependencyNode — accessors  (CNonDeterministicDependencyNode.cpp)
// ===========================================================================

impl DependencyNode {
    /// Immutable `NonDetData` accessor (the non-deterministic subclass state).
    /// Panics on a deterministic variant, matching the fact that these methods
    /// only exist on `CNonDeterministicDependencyNode` in C++.
    fn non_det(&self) -> &NonDetData {
        match self {
            DependencyNode::NonDeterministic { nd, .. }
            | DependencyNode::Or { nd, .. }
            | DependencyNode::ReuseBackendModes { nd, .. } => nd,
            _ => unreachable!("non-deterministic accessor on a deterministic dependency node"),
        }
    }

    fn non_det_mut(&mut self) -> &mut NonDetData {
        match self {
            DependencyNode::NonDeterministic { nd, .. }
            | DependencyNode::Or { nd, .. }
            | DependencyNode::ReuseBackendModes { nd, .. } => nd,
            _ => unreachable!("non-deterministic accessor on a deterministic dependency node"),
        }
    }

    /// Port of `CNonDeterministicDependencyNode::getDependencyClashes`.
    pub fn dependency_clashes(&self) -> ClashDescId {
        self.non_det().dependency_clashes
    }

    /// Port of `CNonDeterministicDependencyNode::hasDependencyClashes`.
    pub fn has_dependency_clashes(&self) -> bool {
        self.non_det().dependency_clashes.is_some()
    }

    /// Port of `CNonDeterministicDependencyNode::setDependencyClash`.
    pub fn set_dependency_clash(&mut self, clash: ClashDescId) -> &mut Self {
        self.non_det_mut().dependency_clashes = clash;
        self
    }

    /// Port of `CNonDeterministicDependencyNode::getBranchTrackPoints`.
    pub fn branch_track_points(&self) -> TrackPointId {
        self.non_det().branch_track_points
    }

    /// Port of `CNonDeterministicDependencyNode::getClashTrackPoint`
    /// (`return &mClashTrackPoint;`).
    pub fn clash_track_point(&self) -> TrackPointId {
        self.non_det().clash_track_point
    }

    /// Port of `CNonDeterministicDependencyNode::getBranchNode`.
    pub fn branch_node(&self) -> BranchNodeId {
        self.non_det().branch_node
    }

    /// Port of `CNonDeterministicDependencyNode::getClosingDependencyTrackPoint`.
    pub fn closing_dependency_track_point(&self) -> TrackPointId {
        self.non_det().closing_track_point
    }

    /// Port of `CNonDeterministicDependencyNode::getClosedDependencyTrackPoint`.
    pub fn closed_dependency_track_point(&self) -> TrackPointId {
        self.non_det().closed_track_point
    }

    /// Port of `CNonDeterministicDependencyNode::setClosingDependencyTrackPoint`.
    pub fn set_closing_dependency_track_point(&mut self, dep_track_point: TrackPointId) -> &mut Self {
        self.non_det_mut().closing_track_point = dep_track_point;
        self
    }

    /// Port of `CNonDeterministicDependencyNode::setClosedDependencyTrackPoint`.
    pub fn set_closed_dependency_track_point(&mut self, dep_track_point: TrackPointId) -> &mut Self {
        self.non_det_mut().closed_track_point = dep_track_point;
        self
    }

    /// Port of `CNonDeterministicDependencyNode::hasClosingDependencyTrackPoint(depTrackPoint)`.
    pub fn has_closing_dependency_track_point_eq(&self, dep_track_point: TrackPointId) -> bool {
        self.non_det().closing_track_point == dep_track_point
    }

    /// Port of `CNonDeterministicDependencyNode::hasClosedDependencyTrackPoint(depTrackPoint)`.
    pub fn has_closed_dependency_track_point_eq(&self, dep_track_point: TrackPointId) -> bool {
        self.non_det().closed_track_point == dep_track_point
    }

    /// Port of `CNonDeterministicDependencyNode::hasClosingDependencyTrackPoint()`.
    pub fn has_closing_dependency_track_point(&self) -> bool {
        self.non_det().closing_track_point.is_some()
    }

    /// Port of `CNonDeterministicDependencyNode::hasClosedDependencyTrackPoint()`.
    pub fn has_closed_dependency_track_point(&self) -> bool {
        self.non_det().closed_track_point.is_some()
    }

    /// Port of `CNonDeterministicDependencyNode::getOpenedDependencyTrackingPointsCount`
    /// — walks the `mBranchTrackPoints` chain counting branches not flagged
    /// clashed-or-irrelevant.
    pub fn opened_dependency_tracking_points_count(
        &self,
        tp_arena: &Arena<DependencyTrackPoint>,
    ) -> Cint64 {
        let mut op_count: Cint64 = 0;
        let mut it = self.non_det().branch_track_points;
        while it.is_some() {
            let tp = tp_arena.get(it);
            if !tp.clashed_irrelevant {
                op_count += 1;
            }
            it = tp.next;
        }
        op_count
    }

    /// Port of `CNonDeterministicDependencyNode::hasMultipleOpenedDependencyTrackingPoints`.
    pub fn has_multiple_opened_dependency_tracking_points(
        &self,
        tp_arena: &Arena<DependencyTrackPoint>,
    ) -> bool {
        let mut op_count: Cint64 = 0;
        let mut it = self.non_det().branch_track_points;
        while it.is_some() {
            let tp = tp_arena.get(it);
            if !tp.clashed_irrelevant {
                op_count += 1;
                if op_count >= 2 {
                    return true;
                }
            }
            it = tp.next;
        }
        false
    }

    /// Port of `CNonDeterministicDependencyNode::hasOtherOpenedDependencyTrackingPoints`.
    pub fn has_other_opened_dependency_tracking_points(
        &self,
        dep_track_point: TrackPointId,
        tp_arena: &Arena<DependencyTrackPoint>,
    ) -> bool {
        let mut it = self.non_det().branch_track_points;
        while it.is_some() {
            let tp = tp_arena.get(it);
            if it != dep_track_point && !tp.clashed_irrelevant {
                return true;
            }
            it = tp.next;
        }
        false
    }

    // W2-DEFER[api]: getDependencyTrackPointBranch() (allocates a new
    // CNonDeterministicDependencyTrackPoint / CORDisjunctDependencyTrackPoint and
    // appends it to mBranchTrackPoints, then updates branching tags), addBranchClashes(),
    // updateBranchingTags(), and CDeterministicDependencyNode::updateBranchingTag() —
    // these open/relabel branch track points and drive the branching-tag spine,
    // ported in DEP-2.
}

// ===========================================================================
// CDependency  → DependencyLink  (CDependency.cpp 1107–1141)
// ===========================================================================

impl DependencyLink {
    /// Port of `CDependency::initDependency`.
    pub fn init_dependency(&mut self, prev_dependency_track_point: TrackPointId) -> &mut Self {
        self.dep_track_point = prev_dependency_track_point;
        self
    }

    /// Port of `CDependency::getPreviousTrackedDependency`
    /// (`mDepTrackPoint ? mDepTrackPoint->getDependencyNode() : nullptr`).
    pub fn previous_tracked_dependency(
        &self,
        tp_arena: &Arena<DependencyTrackPoint>,
    ) -> DependencyId {
        if self.dep_track_point.is_some() {
            tp_arena.get(self.dep_track_point).dep_node
        } else {
            DependencyId::NONE
        }
    }

    /// Port of `CDependency::addAdditionalDependency`
    /// (`insertNext(addDependency); return this;`). Associated fn because
    /// `insertNext` mutates both `this` and the inserted link's chain through the
    /// arena (no aliasing `&mut self` + `&mut other`).
    pub fn add_additional_dependency(
        this: DepLinkId,
        add_dependency: DepLinkId,
        dep_arena: &mut Arena<DependencyLink>,
    ) {
        link_insert_next(this, add_dependency, dep_arena);
    }
}

// ===========================================================================
// CDependencyTrackPoint — plain accessors  (CDependencyTrackPoint.cpp 1294–1318)
//
// (getDependencyNode / isDependencyRelevant / setDependencyRelevance already live
//  on the struct in dependency.rs.)
// ===========================================================================

impl DependencyTrackPoint {
    /// Port of `CDependencyTrackPoint::getProcessingTag`
    /// (`return mDepNode->getProcessingTag();`).
    pub fn processing_tag(&self, node_arena: &Arena<DependencyNode>) -> Cint64 {
        node_arena.get(self.dep_node).base().process_tag
    }

    /// Port of `CDependencyTrackPoint::isPointingToDeterministicDependencyNode`.
    pub fn is_pointing_to_deterministic_dependency_node(
        &self,
        node_arena: &Arena<DependencyNode>,
    ) -> bool {
        node_arena.get(self.dep_node).is_deterministic()
    }

    /// Port of `CDependencyTrackPoint::isPointingToIndependentDependencyNode`.
    pub fn is_pointing_to_independent_dependency_node(
        &self,
        node_arena: &Arena<DependencyNode>,
    ) -> bool {
        node_arena
            .get(self.dep_node)
            .is_independent_base_dependency_type()
    }
}

// ===========================================================================
// CLinkerBase<CDependency> chain primitives (Utilities/Container/CLinker.cpp),
// ported over the DependencyLink arena.
// ===========================================================================

/// Port of `CLinkerBase::getCount` — chain length from `head` to the end.
fn link_get_count(head: DepLinkId, dep_arena: &Arena<DependencyLink>) -> Cint64 {
    let mut linker_count: Cint64 = 0;
    let mut it = head;
    while it.is_some() {
        linker_count += 1;
        it = dep_arena.get(it).next;
    }
    linker_count
}

/// Port of `CLinkerBase::getLastListLink` — the tail link of `head`'s chain.
fn link_get_last(head: DepLinkId, dep_arena: &Arena<DependencyLink>) -> DepLinkId {
    let mut last = head;
    loop {
        let next = dep_arena.get(last).next;
        if next.is_none() {
            return last;
        }
        last = next;
    }
}

/// Port of `CLinkerBase::append(appendingList)` — splice `appending_list` onto the
/// tail of `this_link`'s chain and return `this_link` (the head). Konclude's
/// `link->append(old)` is the prepend-of-`old`-after-`link` it uses for
/// `addAfterDependency`.
fn link_append(
    this_link: DepLinkId,
    appending_list: DepLinkId,
    dep_arena: &mut Arena<DependencyLink>,
) -> DepLinkId {
    let last = link_get_last(this_link, dep_arena);
    dep_arena.get_mut(last).next = appending_list;
    this_link
}

/// Port of `CLinkerBase::insertNext(nextLink)`
/// (`tmpNext = next; next = nextLink; if (tmpNext) nextLink->append(tmpNext);`).
fn link_insert_next(this_link: DepLinkId, next_link: DepLinkId, dep_arena: &mut Arena<DependencyLink>) {
    if next_link.is_some() {
        let tmp_next = dep_arena.get(this_link).next;
        dep_arena.get_mut(this_link).next = next_link;
        if tmp_next.is_some() {
            link_append(next_link, tmp_next, dep_arena);
        }
    }
}
