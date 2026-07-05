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
//! Branching-tag propagation (`getDependedBranchingTag`,
//! `updateBranchingTag(s)`) is implemented here against the DEP-2 track-point
//! substrate. The allocating branch openers (`getDependencyTrackPointBranch`)
//! are also live over the folded non-deterministic track-point arena.

#![allow(dead_code)]

use super::super::model::substrate::{Arena, Cint64};
use super::dependency::{
    DepKind, DependencyLink, DependencyNode, DependencyTrackPoint, NonDetData,
};
use super::representative::RepresentativePropagationMap;
use super::varbind::RepresentativeVariableBindingPathMap;
use super::{BranchNodeId, ClashDescId, ConDescId, DepLinkId, DependencyId, NodeId, TrackPointId};

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
    pub fn add_after_dependency(
        &mut self,
        link: DepLinkId,
        dep_arena: &mut Arena<DependencyLink>,
    ) -> &mut Self {
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
    pub fn continue_dependency_track_point(
        &self,
        this: DependencyId,
        tp_arena: &mut Arena<DependencyTrackPoint>,
    ) -> TrackPointId {
        match self {
            DependencyNode::NonDeterministic { nd, .. }
            | DependencyNode::Or { nd, .. }
            | DependencyNode::ReuseBackendModes { nd, .. } => nd.clash_track_point,
            // CDeterministicDependencyNode multiply-inherits CDependencyTrackPoint,
            // so `this` is the continuation point. The split arenas materialise
            // that inherited track-point half as a record pointing back to `this`.
            _ => {
                let mut track_point = DependencyTrackPoint::new(this);
                track_point.process_tag = self.base().process_tag;
                tp_arena.push(track_point)
            }
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
        tp_arena: &Arena<DependencyTrackPoint>,
        dep_arena: &mut Arena<DependencyLink>,
    ) -> &mut Self {
        self.init_dependency_node_indi(DepKind::All, individual_node, concept_descriptor);
        self.base_mut().dep_track_point = prev_concept_dep_track_point;
        if let DependencyNode::DetLink { prev, .. } = self {
            // mPrevLinkDep.initDependency(prevLinkDependencyTrackPoint);
            dep_arena.get_mut(*prev).dep_track_point = prev_link_dep_track_point;
        }
        self.update_branching_tag(tp_arena, dep_arena);
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
        tp_arena: &Arena<DependencyTrackPoint>,
        dep_arena: &mut Arena<DependencyLink>,
    ) -> &mut Self {
        self.init_dependency_node(DepKind::MergedConcept, concept_descriptor);
        self.base_mut().dep_track_point = prev_concept_dep_track_point;
        if let DependencyNode::DetLink { prev, .. } = self {
            dep_arena.get_mut(*prev).dep_track_point = prev_merging_step_dep_track_point;
        }
        self.update_branching_tag(tp_arena, dep_arena);
        self
    }

    /// Port of `CMERGEDLINKDependencyNode::initMERGEDLINKDependencyNode`.
    pub fn init_merged_link_dependency_node(
        &mut self,
        prev_merging_step_dep_track_point: TrackPointId,
        prev_link_dep_track_point: TrackPointId,
        tp_arena: &Arena<DependencyTrackPoint>,
        dep_arena: &mut Arena<DependencyLink>,
    ) -> &mut Self {
        self.init_dependency_node(DepKind::MergedLink, ConDescId::NONE);
        self.base_mut().dep_track_point = prev_merging_step_dep_track_point;
        if let DependencyNode::DetLink { prev, .. } = self {
            dep_arena.get_mut(*prev).dep_track_point = prev_link_dep_track_point;
        }
        self.update_branching_tag(tp_arena, dep_arena);
        self
    }

    /// Port of `CMERGEDINDIVIDUALDependencyNode::initMERGEDINDIVIDUALDependencyNode`.
    pub fn init_merged_individual_dependency_node(
        &mut self,
        prev_merging_step_dep_track_point: TrackPointId,
        prev_individual_dep_track_point: TrackPointId,
        tp_arena: &Arena<DependencyTrackPoint>,
        dep_arena: &mut Arena<DependencyLink>,
    ) -> &mut Self {
        self.init_dependency_node(DepKind::MergedIndividual, ConDescId::NONE);
        self.base_mut().dep_track_point = prev_merging_step_dep_track_point;
        if let DependencyNode::DetLink { prev, .. } = self {
            dep_arena.get_mut(*prev).dep_track_point = prev_individual_dep_track_point;
        }
        self.update_branching_tag(tp_arena, dep_arena);
        self
    }

    /// Port of `CSAMEINDIVIDUALMERGEDependencyNode::initSAMEINDIVIDUALMERGEDependencyNode`.
    pub fn init_same_individual_merge_dependency_node(
        &mut self,
        prev_dep_track_point: TrackPointId,
        prev_other_dep_track_point: TrackPointId,
        tp_arena: &Arena<DependencyTrackPoint>,
        dep_arena: &mut Arena<DependencyLink>,
    ) -> &mut Self {
        self.init_dependency_node(DepKind::SameIndividualsMerge, ConDescId::NONE);
        self.base_mut().dep_track_point = prev_dep_track_point;
        if let DependencyNode::DetLink { prev, .. } = self {
            dep_arena.get_mut(*prev).dep_track_point = prev_other_dep_track_point;
        }
        self.update_branching_tag(tp_arena, dep_arena);
        self
    }

    /// Port of `CMERGEDependencyNode::initMERGEDependencyNode`.
    ///
    /// Returns the inline clash track point so a `ProcessContext` caller can mark
    /// it clashed/irrelevant without needing direct access to both arenas here.
    pub fn init_merge_dependency_node(
        &mut self,
        branch_node: BranchNodeId,
        concept_descriptor: ConDescId,
        prev_dep_track_point: TrackPointId,
    ) -> TrackPointId {
        self.init_dependency_node(DepKind::Merge, concept_descriptor);
        self.base_mut().dep_track_point = prev_dep_track_point;
        let nd = self.non_det_mut();
        let clash_track_point = nd.clash_track_point;
        nd.branch_track_points = clash_track_point;
        nd.dependency_clashes = ClashDescId::NONE;
        nd.branch_node = branch_node;
        nd.branch_tag = 0;
        nd.closed_track_point = TrackPointId::NONE;
        nd.closing_track_point = TrackPointId::NONE;
        clash_track_point
    }

    /// Port of `CRESOLVEREPRESENTATIVEDependencyNode::initRESOLVEREPRESENTATIVEDependencyNode`.
    ///
    /// This is the representative resolve **DetLink** shape: `mDepTrackPoint`
    /// stores the previous concept dependency, and the inline `CDependency
    /// mAdditionalDep` stores the additional dependency track point.
    pub fn init_resolve_representative_dependency_node(
        &mut self,
        concept_descriptor: ConDescId,
        resolve_var_bind_path_map: Option<&RepresentativeVariableBindingPathMap>,
        resolve_rep_prop_map: Option<&RepresentativePropagationMap>,
        prev_dependency_track_point: TrackPointId,
        additional_dependency_track_point: TrackPointId,
        tp_arena: &Arena<DependencyTrackPoint>,
        dep_arena: &mut Arena<DependencyLink>,
    ) -> &mut Self {
        self.init_dependency_node(DepKind::ResolveRepresentative, concept_descriptor);
        self.base_mut().resolve_var_bind_path_map = resolve_var_bind_path_map.cloned();
        self.base_mut().resolve_rep_prop_map = resolve_rep_prop_map.cloned();
        self.base_mut().dep_track_point = prev_dependency_track_point;
        let additional_dep = if let DependencyNode::DetLink { prev, .. } = self {
            *prev
        } else {
            DepLinkId::NONE
        };
        if additional_dependency_track_point.is_some() && additional_dep.is_some() {
            self.base_mut().additional_after = additional_dep;
            dep_arena
                .get_mut(additional_dep)
                .init_dependency(additional_dependency_track_point);
        }
        self.update_branching_tag(tp_arena, dep_arena);
        self
    }

    /// Port of `CRESOLVEREPRESENTATIVEDependencyNode::getAdditionalDependency`.
    pub fn resolve_representative_additional_dependency(&self) -> DepLinkId {
        if let DependencyNode::DetLink { prev, .. } = self {
            *prev
        } else {
            DepLinkId::NONE
        }
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
        tp_arena: &Arena<DependencyTrackPoint>,
        dep_arena: &mut Arena<DependencyLink>,
    ) -> &mut Self {
        self.init_dependency_node_indi(DepKind::Functional, individual_node, concept_descriptor);
        self.base_mut().dep_track_point = prev_concept_dep_track_point;
        if let DependencyNode::DetLink2 { prev1, prev2, .. } = self {
            dep_arena.get_mut(*prev1).dep_track_point = prev_link1_dep_track_point;
            dep_arena.get_mut(*prev2).dep_track_point = prev_link2_dep_track_point;
        }
        self.update_branching_tag(tp_arena, dep_arena);
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
        dep_arena: &Arena<DependencyLink>,
    ) -> &mut Self {
        self.init_non_deterministic_dependency_node(
            DepKind::Or,
            branch_node,
            concept_descriptor,
            tp_arena,
        );
        self.base_mut().dep_track_point = dep_track_point;
        self.update_branching_tags(tp_arena, dep_arena);
        self
    }

    /// Port of `CMERGEPOSSIBLEINSTANCEINDIVIDUALDependencyNode::initMERGEPOSSIBLEINSTANCEINDIVIDUALDependencyNode`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: Konclude's signature accepts
    /// `mergingIndividualNode`, but the C++ body does not store or read it; the
    /// wrapper keeps that parameter and discards it before calling this exact init.
    pub fn init_merge_possible_instance_individual_dependency_node(
        &mut self,
        branch_node: BranchNodeId,
        individual_node: NodeId,
        dep_track_point: TrackPointId,
        tp_arena: &mut Arena<DependencyTrackPoint>,
        dep_arena: &Arena<DependencyLink>,
    ) -> &mut Self {
        self.init_non_deterministic_dependency_node_indi(
            DepKind::MergePossibleInstanceIndividual,
            branch_node,
            individual_node,
            ConDescId::NONE,
            tp_arena,
        );
        self.base_mut().dep_track_point = dep_track_point;
        self.update_branching_tags(tp_arena, dep_arena);
        self
    }

    /// Port of `CREUSEBACKENDEXPANSIONMODESDependencyNode::initREUSEBACKENDEXPANSIONMODESDependencyNode`
    /// — non-deterministic + the `CXLinker<cint64>` involved-id list outlier.
    pub fn init_reuse_backend_expansion_modes_dependency_node(
        &mut self,
        branch_node: BranchNodeId,
        dep_track_point: TrackPointId,
        tp_arena: &mut Arena<DependencyTrackPoint>,
        dep_arena: &Arena<DependencyLink>,
    ) -> &mut Self {
        self.init_non_deterministic_dependency_node_indi(
            DepKind::ReuseBackendExpansionModes,
            branch_node,
            NodeId::NONE,
            ConDescId::NONE,
            tp_arena,
        );
        self.base_mut().dep_track_point = dep_track_point;
        self.update_branching_tags(tp_arena, dep_arena);
        if let DependencyNode::ReuseBackendModes {
            fixed_reuse_dep_track_point,
            priorized_reuse_dep_track_point,
            involved,
            affected,
            ..
        } = self
        {
            // mFixedReuseDepTrackPoint = nullptr;
            *fixed_reuse_dep_track_point = TrackPointId::NONE;
            // mPriorizedReuseDepTrackPoint = nullptr;
            *priorized_reuse_dep_track_point = TrackPointId::NONE;
            // mInvolvedIndividualIdLinker = nullptr;
            involved.clear();
            // mAffectedIndividualIdLinker = nullptr;
            affected.clear();
        }
        self
    }

    /// Port of `CREUSEBACKENDEXPANSIONMODESDependencyNode::getFixedReuseDependencyTrackPoint`.
    pub fn fixed_reuse_dependency_track_point(&self) -> TrackPointId {
        match self {
            DependencyNode::ReuseBackendModes {
                fixed_reuse_dep_track_point,
                ..
            } => *fixed_reuse_dep_track_point,
            _ => TrackPointId::NONE,
        }
    }

    /// Port of `CREUSEBACKENDEXPANSIONMODESDependencyNode::setFixedReuseDependencyTrackPoint`.
    pub fn set_fixed_reuse_dependency_track_point(
        &mut self,
        dep_track_point: TrackPointId,
    ) -> &mut Self {
        if let DependencyNode::ReuseBackendModes {
            fixed_reuse_dep_track_point,
            ..
        } = self
        {
            *fixed_reuse_dep_track_point = dep_track_point;
        }
        self
    }

    /// Port of `CREUSEBACKENDEXPANSIONMODESDependencyNode::getPriorizedReuseDependencyTrackPoint`.
    pub fn priorized_reuse_dependency_track_point(&self) -> TrackPointId {
        match self {
            DependencyNode::ReuseBackendModes {
                priorized_reuse_dep_track_point,
                ..
            } => *priorized_reuse_dep_track_point,
            _ => TrackPointId::NONE,
        }
    }

    /// Port of `CREUSEBACKENDEXPANSIONMODESDependencyNode::setPriorizedReuseDependencyTrackPoint`.
    pub fn set_priorized_reuse_dependency_track_point(
        &mut self,
        dep_track_point: TrackPointId,
    ) -> &mut Self {
        if let DependencyNode::ReuseBackendModes {
            priorized_reuse_dep_track_point,
            ..
        } = self
        {
            *priorized_reuse_dep_track_point = dep_track_point;
        }
        self
    }

    /// Port of `CREUSEBACKENDEXPANSIONMODESDependencyNode::getAffectedIndividualIdLinker`.
    pub fn affected_individual_id_linker(&self) -> &[Cint64] {
        match self {
            DependencyNode::ReuseBackendModes { affected, .. } => affected,
            _ => &[],
        }
    }

    /// Port of `CREUSEBACKENDEXPANSIONMODESDependencyNode::addAffectedIndividualIdLinker`.
    pub fn add_affected_individual_id_linker(
        &mut self,
        expected_linker: &[Cint64],
        new_linker: Vec<Cint64>,
    ) -> bool {
        match self {
            DependencyNode::ReuseBackendModes { affected, .. } => {
                if affected.as_slice() == expected_linker {
                    *affected = new_linker;
                    true
                } else {
                    false
                }
            }
            _ => false,
        }
    }

    /// Port of `CREUSEBACKENDEXPANSIONMODESDependencyNode::getInvolvedIndividualIdLinker`.
    pub fn involved_individual_id_linker(&self) -> &[Cint64] {
        match self {
            DependencyNode::ReuseBackendModes { involved, .. } => involved,
            _ => &[],
        }
    }

    /// Port of `CREUSEBACKENDEXPANSIONMODESDependencyNode::setInvolvedIndividualIdLinker`.
    pub fn set_involved_individual_id_linker(&mut self, new_linker: Vec<Cint64>) -> &mut Self {
        if let DependencyNode::ReuseBackendModes { involved, .. } = self {
            *involved = new_linker;
        }
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

    /// Port of `CNonDeterministicDependencyNode::getDependencyTrackPointBranch`
    /// and the `CORDependencyNode` override.
    ///
    /// Both variants allocate a fresh non-deterministic track point, prepend it
    /// to `mBranchTrackPoints`, and copy the dependency node's current branch
    /// tag into the new point. In the folded Rust representation the OR-specific
    /// `CORDisjunctDependencyTrackPoint` fields already live on every
    /// `DependencyTrackPoint`, so the override reduces to the same allocation.
    pub fn get_dependency_track_point_branch(
        &mut self,
        this: DependencyId,
        tp_arena: &mut Arena<DependencyTrackPoint>,
    ) -> TrackPointId {
        let (old_head, branch_tag) = {
            let nd = self.non_det();
            (nd.branch_track_points, nd.branch_tag)
        };
        let mut non_det_track_point = DependencyTrackPoint::new(this);
        non_det_track_point.next = old_head;
        non_det_track_point.add_maximum_branching_tag_candidate(branch_tag);
        let non_det_track_point = tp_arena.push(non_det_track_point);
        self.non_det_mut().branch_track_points = non_det_track_point;
        non_det_track_point
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
    pub fn set_closing_dependency_track_point(
        &mut self,
        dep_track_point: TrackPointId,
    ) -> &mut Self {
        self.non_det_mut().closing_track_point = dep_track_point;
        self
    }

    /// Port of `CNonDeterministicDependencyNode::setClosedDependencyTrackPoint`.
    pub fn set_closed_dependency_track_point(
        &mut self,
        dep_track_point: TrackPointId,
    ) -> &mut Self {
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

    /// Port of `CDependencyNode::getDependedBranchingTag`.
    pub fn depended_branching_tag(
        &self,
        tp_arena: &Arena<DependencyTrackPoint>,
        dep_arena: &Arena<DependencyLink>,
    ) -> Cint64 {
        let mut branch_level_tag: Cint64 = 0;
        let dep_track_point = self.base().dep_track_point;
        if dep_track_point.is_some() {
            branch_level_tag =
                branch_level_tag.max(tp_arena.get(dep_track_point).get_branching_tag());
        }
        let mut link_dep_linker_it = self.base().additional_after;
        while link_dep_linker_it.is_some() && branch_level_tag >= 0 {
            let track_point = dep_arena
                .get(link_dep_linker_it)
                .previous_dependency_track_point();
            if track_point.is_some() {
                branch_level_tag =
                    branch_level_tag.max(tp_arena.get(track_point).get_branching_tag());
            } else {
                branch_level_tag = -1;
            }
            link_dep_linker_it = dep_arena
                .get(link_dep_linker_it)
                .next_additional_dependency();
        }
        branch_level_tag
    }

    /// Port of `CDependencyNode::getDependedBranchingLevel`.
    pub fn depended_branching_level(
        &self,
        tp_arena: &Arena<DependencyTrackPoint>,
        dep_arena: &Arena<DependencyLink>,
    ) -> Cint64 {
        self.depended_branching_tag(tp_arena, dep_arena)
    }

    /// Port of `CDependencyNode::updateDependencyTrackPointBranchingTag`.
    pub fn update_dependency_track_point_branching_tag(
        dep_track_point: TrackPointId,
        branching_level_tag: Cint64,
        tp_arena: &mut Arena<DependencyTrackPoint>,
    ) -> bool {
        tp_arena
            .get_mut(dep_track_point)
            .add_maximum_branching_tag_candidate(branching_level_tag)
    }

    /// Port of `CDeterministicDependencyNode::updateBranchingTag`.
    pub fn update_branching_tag(
        &mut self,
        tp_arena: &Arena<DependencyTrackPoint>,
        dep_arena: &Arena<DependencyLink>,
    ) -> bool {
        let branch_tag = self.depended_branching_level(tp_arena, dep_arena);
        if branch_tag > self.base().process_tag || branch_tag < 0 {
            self.base_mut().process_tag = branch_tag;
            return true;
        }
        false
    }

    /// Port of `CNonDeterministicDependencyNode::updateBranchingTags`.
    pub fn update_branching_tags(
        &mut self,
        tp_arena: &mut Arena<DependencyTrackPoint>,
        dep_arena: &Arena<DependencyLink>,
    ) -> bool {
        let branch_tag = self.depended_branching_level(tp_arena, dep_arena);
        self.non_det_mut().branch_tag = branch_tag;
        let mut changed = false;
        let mut branch_track_points_it = self.non_det().branch_track_points;
        while branch_track_points_it.is_some() {
            changed |= Self::update_dependency_track_point_branching_tag(
                branch_track_points_it,
                branch_tag,
                tp_arena,
            );
            branch_track_points_it = tp_arena.get(branch_track_points_it).next;
        }
        changed
    }
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
fn link_insert_next(
    this_link: DepLinkId,
    next_link: DepLinkId,
    dep_arena: &mut Arena<DependencyLink>,
) {
    if next_link.is_some() {
        let tmp_next = dep_arena.get(this_link).next;
        dep_arena.get_mut(this_link).next = next_link;
        if tmp_next.is_some() {
            link_append(next_link, tmp_next, dep_arena);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::super::model::{IndividualId, RoleId, INVALID};
    use super::super::dependency::{DepNodeBase, OrDisjunctTrackData};
    use super::super::varbind::VarBindingPathId;
    use super::*;

    fn empty_base(kind: DepKind) -> DepNodeBase {
        DepNodeBase {
            process_tag: 0,
            concept_descriptor: ConDescId::NONE,
            individual_node: NodeId::NONE,
            kind,
            dep_track_point: TrackPointId::NONE,
            additional_after: DepLinkId::NONE,
            selected_var_bind_path: VarBindingPathId::NONE,
            resolve_var_bind_path_map: None,
            resolve_rep_prop_map: None,
            base_assertion_role: RoleId::NONE,
            base_assertion_individual: IndividualId::NONE,
        }
    }

    fn non_det_data(clash_track_point: TrackPointId) -> NonDetData {
        NonDetData {
            branch_track_points: TrackPointId::NONE,
            clash_track_point,
            dependency_clashes: ClashDescId::NONE,
            branch_node: BranchNodeId::NONE,
            branch_tag: 0,
            closing_track_point: TrackPointId::NONE,
            closed_track_point: TrackPointId::NONE,
        }
    }

    fn track_point_with_tag(
        tp_arena: &mut Arena<DependencyTrackPoint>,
        tag: Cint64,
    ) -> TrackPointId {
        let mut track_point = DependencyTrackPoint::new(DependencyId::NONE);
        track_point.add_maximum_branching_tag_candidate(tag);
        tp_arena.push(track_point)
    }

    fn det_link_node(prev: DepLinkId) -> DependencyNode {
        DependencyNode::DetLink {
            base: empty_base(DepKind::Undefined),
            prev,
        }
    }

    #[test]
    fn dep1_branch_continue_track_point_materializes_deterministic_node() {
        let mut tp_arena = Arena::new();
        let mut node = DependencyNode::Deterministic {
            base: empty_base(DepKind::And),
        };
        node.base_mut().process_tag = 11;

        let continue_tp =
            node.continue_dependency_track_point(DependencyId::new(23), &mut tp_arena);

        let track_point = tp_arena.get(continue_tp);
        assert_eq!(track_point.dependency_node(), DependencyId::new(23));
        assert_eq!(track_point.get_branching_tag(), 11);
    }

    #[test]
    fn dep1_branch_continue_track_point_returns_non_det_clash_track_point() {
        let mut tp_arena = Arena::new();
        let clash_tp = tp_arena.push(DependencyTrackPoint::new(DependencyId::NONE));
        let node = DependencyNode::NonDeterministic {
            base: empty_base(DepKind::Or),
            nd: non_det_data(clash_tp),
        };

        let continue_tp =
            node.continue_dependency_track_point(DependencyId::new(29), &mut tp_arena);

        assert_eq!(continue_tp, clash_tp);
        assert_eq!(
            tp_arena.get(continue_tp).dependency_node(),
            DependencyId::NONE
        );
        assert_eq!(tp_arena.len(), 1);
    }

    #[test]
    fn dep1_branch_all_init_uses_previous_concept_branching_tag() {
        let mut tp_arena = Arena::new();
        let concept_tp = track_point_with_tag(&mut tp_arena, 3);
        let link_tp = track_point_with_tag(&mut tp_arena, 7);
        let mut dep_arena = Arena::new();
        let prev = dep_arena.push(DependencyLink::new());
        let mut node = det_link_node(prev);

        node.init_all_dependency_node(
            ConDescId::NONE,
            NodeId::NONE,
            concept_tp,
            link_tp,
            &tp_arena,
            &mut dep_arena,
        );

        assert_eq!(node.base().process_tag, 3);
        assert_eq!(node.base().dep_track_point, concept_tp);
        assert_eq!(
            dep_arena.get(prev).previous_dependency_track_point(),
            link_tp
        );
    }

    #[test]
    fn dep1_branch_resolve_representative_counts_additional_dependency() {
        let mut tp_arena = Arena::new();
        let previous_tp = track_point_with_tag(&mut tp_arena, 2);
        let additional_tp = track_point_with_tag(&mut tp_arena, 9);
        let mut dep_arena = Arena::new();
        let prev = dep_arena.push(DependencyLink::new());
        let mut node = det_link_node(prev);

        node.init_resolve_representative_dependency_node(
            ConDescId::NONE,
            None,
            None,
            previous_tp,
            additional_tp,
            &tp_arena,
            &mut dep_arena,
        );

        assert_eq!(node.base().process_tag, 9);
        assert_eq!(node.additional_after_dependencies(), prev);
        assert_eq!(
            dep_arena.get(prev).previous_dependency_track_point(),
            additional_tp
        );
    }

    #[test]
    fn dep1_merge_det_link_inits_preserve_konclude_track_point_wiring() {
        let mut tp_arena = Arena::new();
        let merge_tp = track_point_with_tag(&mut tp_arena, 3);
        let other_tp = track_point_with_tag(&mut tp_arena, 7);
        let mut dep_arena = Arena::new();

        let merged_link_prev = dep_arena.push(DependencyLink::new());
        let mut merged_link = det_link_node(merged_link_prev);
        merged_link.init_merged_link_dependency_node(merge_tp, other_tp, &tp_arena, &mut dep_arena);
        assert_eq!(merged_link.kind(), DepKind::MergedLink);
        assert_eq!(merged_link.base().dep_track_point, merge_tp);
        assert_eq!(
            dep_arena
                .get(merged_link_prev)
                .previous_dependency_track_point(),
            other_tp
        );
        assert_eq!(merged_link.base().process_tag, 3);

        let merged_individual_prev = dep_arena.push(DependencyLink::new());
        let mut merged_individual = det_link_node(merged_individual_prev);
        merged_individual.init_merged_individual_dependency_node(
            merge_tp,
            other_tp,
            &tp_arena,
            &mut dep_arena,
        );
        assert_eq!(merged_individual.kind(), DepKind::MergedIndividual);
        assert_eq!(
            dep_arena
                .get(merged_individual_prev)
                .previous_dependency_track_point(),
            other_tp
        );

        let same_prev = dep_arena.push(DependencyLink::new());
        let mut same_merge = det_link_node(same_prev);
        same_merge.init_same_individual_merge_dependency_node(
            merge_tp,
            other_tp,
            &tp_arena,
            &mut dep_arena,
        );
        assert_eq!(same_merge.kind(), DepKind::SameIndividualsMerge);
        assert_eq!(same_merge.base().dep_track_point, merge_tp);
        assert_eq!(
            dep_arena.get(same_prev).previous_dependency_track_point(),
            other_tp
        );
    }

    #[test]
    fn dep1_branch_missing_additional_dependency_sets_negative_tag() {
        let tp_arena = Arena::new();
        let mut dep_arena = Arena::new();
        let missing_dep = dep_arena.push(DependencyLink::new());
        let mut node = DependencyNode::Deterministic {
            base: empty_base(DepKind::And),
        };
        node.add_after_dependency(missing_dep, &mut dep_arena);

        assert!(node.update_branching_tag(&tp_arena, &dep_arena));
        assert_eq!(node.base().process_tag, -1);
    }

    #[test]
    fn dep1_branch_or_init_updates_clash_and_opened_track_points() {
        let mut tp_arena = Arena::new();
        let main_tp = track_point_with_tag(&mut tp_arena, 4);
        let clash_tp = tp_arena.push(DependencyTrackPoint::new(DependencyId::NONE));
        let mut dep_arena = Arena::new();
        let mut node = DependencyNode::Or {
            base: empty_base(DepKind::Undefined),
            nd: non_det_data(clash_tp),
            disj: OrDisjunctTrackData::default(),
        };

        node.init_or_dependency_node(
            BranchNodeId::new(1),
            ConDescId::NONE,
            main_tp,
            &mut tp_arena,
            &dep_arena,
        );

        assert_eq!(node.non_det().branch_tag, 4);
        assert_eq!(tp_arena.get(clash_tp).get_branching_tag(), 4);
        assert_eq!(node.branch_track_points(), clash_tp);

        let opened_tp =
            node.get_dependency_track_point_branch(DependencyId::new(17), &mut tp_arena);
        assert_eq!(tp_arena.get(opened_tp).get_branching_tag(), 4);
        let high_tp = track_point_with_tag(&mut tp_arena, 8);
        node.base_mut().dep_track_point = high_tp;

        assert!(node.update_branching_tags(&mut tp_arena, &dep_arena));
        assert_eq!(node.non_det().branch_tag, 8);
        assert_eq!(tp_arena.get(opened_tp).get_branching_tag(), 8);
        assert_eq!(tp_arena.get(clash_tp).get_branching_tag(), 8);
    }

    #[test]
    fn dep1_branch_reuse_backend_init_updates_branch_tag() {
        let mut tp_arena = Arena::new();
        let main_tp = track_point_with_tag(&mut tp_arena, 6);
        let clash_tp = tp_arena.push(DependencyTrackPoint::new(DependencyId::NONE));
        let dep_arena = Arena::new();
        let mut node = DependencyNode::ReuseBackendModes {
            base: empty_base(DepKind::Undefined),
            nd: non_det_data(clash_tp),
            fixed_reuse_dep_track_point: TrackPointId::new(101),
            priorized_reuse_dep_track_point: TrackPointId::new(103),
            involved: vec![1, 2, 3],
            affected: vec![4, 5, 6],
        };

        node.init_reuse_backend_expansion_modes_dependency_node(
            BranchNodeId::new(2),
            main_tp,
            &mut tp_arena,
            &dep_arena,
        );

        assert_eq!(node.non_det().branch_tag, 6);
        assert_eq!(tp_arena.get(clash_tp).get_branching_tag(), 6);
        if let DependencyNode::ReuseBackendModes {
            fixed_reuse_dep_track_point,
            priorized_reuse_dep_track_point,
            involved,
            affected,
            ..
        } = node
        {
            assert_eq!(fixed_reuse_dep_track_point, TrackPointId::NONE);
            assert_eq!(priorized_reuse_dep_track_point, TrackPointId::NONE);
            assert!(involved.is_empty());
            assert!(affected.is_empty());
        } else {
            unreachable!("{}", INVALID);
        }
    }

    #[test]
    fn dep1_reuse_backend_side_field_accessors_follow_konclude() {
        let clash_tp = TrackPointId::new(11);
        let fixed_tp = TrackPointId::new(13);
        let priorized_tp = TrackPointId::new(17);
        let mut node = DependencyNode::ReuseBackendModes {
            base: empty_base(DepKind::ReuseBackendExpansionModes),
            nd: non_det_data(clash_tp),
            fixed_reuse_dep_track_point: TrackPointId::NONE,
            priorized_reuse_dep_track_point: TrackPointId::NONE,
            involved: Vec::new(),
            affected: Vec::new(),
        };

        assert_eq!(
            node.fixed_reuse_dependency_track_point(),
            TrackPointId::NONE
        );
        assert_eq!(
            node.priorized_reuse_dependency_track_point(),
            TrackPointId::NONE
        );
        node.set_fixed_reuse_dependency_track_point(fixed_tp)
            .set_priorized_reuse_dependency_track_point(priorized_tp)
            .set_involved_individual_id_linker(vec![3, 5]);
        assert_eq!(node.fixed_reuse_dependency_track_point(), fixed_tp);
        assert_eq!(node.priorized_reuse_dependency_track_point(), priorized_tp);
        assert_eq!(node.involved_individual_id_linker(), &[3, 5]);

        assert!(node.add_affected_individual_id_linker(&[], vec![7, 11]));
        assert_eq!(node.affected_individual_id_linker(), &[7, 11]);
        assert!(!node.add_affected_individual_id_linker(&[], vec![13]));
        assert_eq!(node.affected_individual_id_linker(), &[7, 11]);
        assert!(node.add_affected_individual_id_linker(&[7, 11], vec![13]));
        assert_eq!(node.affected_individual_id_linker(), &[13]);
    }
}
