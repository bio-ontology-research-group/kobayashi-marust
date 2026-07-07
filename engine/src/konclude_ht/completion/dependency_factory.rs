//! `completion::dependency_factory` — the real allocator behind the
//! `create*Dependency` wrappers (Konclude
//! `Source/Reasoner/Kernel/Algorithm/CDependencyFactory.{h,cpp}`).
//!
//! ## What this is
//! Every `CDependencyFactory::createXDependency(...)` method has the identical
//! body shape (`CDependencyFactory.cpp` 36–677):
//!
//! ```cpp
//! CXDependencyNode* depNode = nullptr;
//! if (mConfBuildDependencies) {
//!     depNode = CObjectParameterizingAllocator<CXDependencyNode, CProcessContext*>
//!         ::allocateAndConstructAndParameterize(
//!             calcAlgContext->getUsedProcessTaskMemoryAllocationManager(),
//!             calcAlgContext->getUsedProcessContext());
//!     depNode->initXDependencyNode(...);
//!     xContinueDepTrackPoint = depNode->getContinueDependencyTrackPoint();
//! }
//! return depNode;
//! ```
//!
//! i.e. **bump-allocate the `CXDependencyNode` from the per-test process pool**,
//! run its `initX…` constructor, and read back the continuation track point. The
//! `create*Dependency` wrappers in `u28`/`u29`/`u30` currently port the
//! `mConfBuildDependencies` guard + the `nullptr` (`Id::NONE`) return but defer the
//! allocation (`// W6-DEFER[api]: factory->createX…`). This module supplies the
//! deferred allocation — the un-defer wave switches each wrapper's `W6-DEFER` line
//! over to one of the `alloc_*_dependency_node` methods below + the matching
//! `init_*` (already ported in `process/dep1.rs`) + the continue-track-point
//! materialiser.
//!
//! ## Where the factory lives
//! KONCLUDE-PORT-NOTE[ownership]: in Konclude `CDependencyFactory` is a distinct
//! class (the algorithm's `mDependencyFactory`), but every method bump-allocates
//! from the `CProcessContext` pool (`getUsedProcessContext()`). The port realises
//! that single typeless pool as the typed `Arena<T>` fields ON `ProcessContext`
//! (`process/context.rs`), so the faithful home for the allocator is an
//! `impl ProcessContext`: `new CXDependencyNode(…)` ≡ `self.alloc_dep_node(
//! DependencyNode::Variant{…})`. The wrappers reach it through
//! `calc_alg_context.process_context_mut()`. The factory's `mConfBuildDependencies`
//! state is NOT duplicated here: the guard already lives on the wrapper
//! (`self.conf_build_dependencies`), exactly where Konclude's wrapper sits relative
//! to the factory call; these methods are the unconditional allocation that runs
//! once past that guard.
//!
//! ## The 7 structural variants
//! `process/dependency.rs` collapses Konclude's ~63 `C*DependencyNode` classes into
//! 7 structural `DependencyNode` enum variants carrying a 64-value `DepKind` tag.
//! The factory therefore needs **one allocator per variant shape** (not per
//! `create*` wrapper); the wrapper picks the variant its tag maps to and passes its
//! `DepKind`:
//!
//! | variant            | C++ shape                              | inline members co-allocated      |
//! |--------------------|----------------------------------------|----------------------------------|
//! | `IndependentBase`  | `CIndependentBaseDependencyNode`       | —                                |
//! | `Deterministic`    | tag-only `CDeterministicDependencyNode`| —                                |
//! | `DetLink`          | 1 `CDependency mPrevLinkDep`           | 1 `DependencyLink`               |
//! | `DetLink2`         | `CFUNCTIONALDependencyNode` (2 edges)  | 2 `DependencyLink`               |
//! | `NonDeterministic` | `CNonDeterministicDependencyNode` fam. | 1 clash `DependencyTrackPoint`   |
//! | `Or`               | `CORDependencyNode`                    | 1 clash `DependencyTrackPoint`   |
//! | `ReuseBackendModes`| `CREUSEBACKENDEXPANSIONMODES…`         | 1 clash `DependencyTrackPoint`   |
//!
//! KONCLUDE-PORT-NOTE[ownership]: the C++ `CDependency mPrevLinkDep` / `mPrevLink2Dep`
//! and `CNonDeterministicDependencyTrackPoint mClashTrackPoint` are INLINE (by-value)
//! members of the node object. In the arena split each is its own pooled record, so
//! the variant allocator co-allocates it and stores its `Id`. `setup_non_deterministic`
//! (`process/dep1.rs`) dereferences `nd.clash_track_point`, so the clash track point
//! MUST exist before the wrapper's `init_*` runs — hence it is allocated here, in the
//! constructor, and back-linked to the node (mirroring the inline-member identity).

#![allow(dead_code)]

use super::super::process::context::ProcessContext;
use super::super::process::dependency::{
    DepKind, DepNodeBase, DependencyLink, DependencyNode, DependencyTrackPoint, NonDetData,
    OrDisjunctTrackData,
};
use super::super::process::{
    BranchNodeId, ClashDescId, ConDescId, DepLinkId, DependencyId, NodeId, TrackPointId,
};

/// A freshly-constructed, all-default `DepNodeBase` for `kind` (the state every
/// `CDependencyNode` ctor leaves before its `initX…` runs: null descriptor / node,
/// no previous track point, no after-dependencies, zero process tag).
fn empty_base(kind: DepKind) -> DepNodeBase {
    DepNodeBase {
        process_tag: 0,
        concept_descriptor: ConDescId::NONE,
        individual_node: NodeId::NONE,
        kind,
        dep_track_point: TrackPointId::NONE,
        additional_after: DepLinkId::NONE,
        selected_var_bind_path: super::super::process::varbind::VarBindingPathId::NONE,
        resolve_var_bind_path_map: None,
        resolve_rep_prop_map: None,
        base_assertion_role: super::super::model::RoleId::NONE,
        base_assertion_individual: super::super::model::IndividualId::NONE,
    }
}

/// A freshly-constructed `NonDetData` whose inline clash track point is `clash_tp`.
/// (`setup_non_deterministic` later sets `clashed_irrelevant`, `branch_track_points`,
/// `branch_node`, … — this only nulls the rest and plants the pre-allocated clash
/// track point so that step can deref it.)
fn empty_non_det(clash_tp: TrackPointId) -> NonDetData {
    NonDetData {
        branch_track_points: TrackPointId::NONE,
        clash_track_point: clash_tp,
        dependency_clashes: ClashDescId::NONE,
        branch_node: BranchNodeId::NONE,
        branch_tag: 0,
        closing_track_point: TrackPointId::NONE,
        closed_track_point: TrackPointId::NONE,
    }
}

/// An empty `CDependency` (`DependencyLink`) record (the inline `mPrevLink*Dep`
/// member before `initDependency`). Both fields null.
fn empty_dep_link() -> DependencyLink {
    DependencyLink {
        dep_track_point: TrackPointId::NONE,
        next: DepLinkId::NONE,
    }
}

impl ProcessContext {
    // =======================================================================
    // The dependency-node allocators — the `CObjectParameterizingAllocator<
    // CXDependencyNode, CProcessContext*>::allocateAndConstructAndParameterize`
    // step of every `CDependencyFactory::createX…`. Each returns a freshly pooled,
    // base-zeroed node whose inline members (back-edges / clash track point) are
    // co-allocated and back-linked, ready for the wrapper's `init_*` call.
    // =======================================================================

    /// Allocate a `CIndependentBaseDependencyNode` (`DNTINDEPENDENTBASE`).
    /// Port of the allocation step shared by the search-root construction.
    pub fn alloc_independent_base_dependency_node(&mut self) -> DependencyId {
        self.alloc_dep_node(DependencyNode::IndependentBase {
            base: empty_base(DepKind::IndependentBase),
        })
    }

    /// Allocate a tag-only `CDeterministicDependencyNode` of tag `kind` (`AND`,
    /// `SOME`, `SELF`, `DISTINCT`, `ATLEAST`, `IMPLICATION`, `EXPANDED`,
    /// `CONNECTION`, the `…BINDING`/`…PROPAGATE…` det families, …). Covers every
    /// `create*Dependency` whose tag maps to the `Deterministic` variant.
    pub fn alloc_deterministic_dependency_node(&mut self, kind: DepKind) -> DependencyId {
        self.alloc_dep_node(DependencyNode::Deterministic {
            base: empty_base(kind),
        })
    }

    /// Allocate a one-back-edge `CDeterministicDependencyNode` of tag `kind` (the
    /// `CALLDependencyNode::mPrevLinkDep` shape: `ALL`, `VALUE`, `NEGVALUE`,
    /// `NOMINAL`, `MERGEDCONCEPT`, `MERGEDLINK`, `ROLEASSERTION`, `DATAASSERTION`,
    /// `SAMEINDIVIDUALSMERGE`, `AUTOMATTRANSACTION`, the `…SUCCESSOR` /
    /// `REPRESENTATIVE{ALL,JOIN}` set, …). Co-allocates the inline `CDependency`
    /// back-edge that `init_*` then `initDependency`-binds.
    pub fn alloc_det_link_dependency_node(&mut self, kind: DepKind) -> DependencyId {
        let prev = self.alloc_dep_link(empty_dep_link());
        self.alloc_dep_node(DependencyNode::DetLink {
            base: empty_base(kind),
            prev,
        })
    }

    /// Bind a DetLink node's inline back-edge AND chain it onto the node's
    /// additional-after list — Konclude's `addAfterDependency(&mPrevLinkDep);
    /// mPrevLinkDep.initDependency(tp)` pair (constructor-chained for
    /// ALL/MERGEDCONCEPT/MERGEDLINK/AUTOMATTRANSACTION/REPRESENTATIVE{ALL,JOIN},
    /// init-conditional for VALUE/NEGVALUE/NOMINAL/ROLEASSERTION/…). The chain
    /// membership is LOAD-BEARING: `getDependedBranchingLevel` and the u29
    /// tracked-clash additional-dependency traversal only walk
    /// `additional_after` — a detached back-edge hid e.g. a MERGEDCONCEPT's
    /// merge-decision taint, making merged-label clashes look deterministic
    /// (measured: ore_ont_12653 AlternativePath ⊑ PathOfLength2 wrong
    /// ROOT-CANCEL under DDB). No-op when `tp` is NONE (the conditional
    /// classes skip both calls then).
    pub fn bind_det_link_prev(&mut self, dep_node: DependencyId, tp: TrackPointId) {
        if dep_node.is_none() || tp.is_none() {
            return;
        }
        let prev = if let DependencyNode::DetLink { prev, .. } = self.dep_node(dep_node) {
            *prev
        } else {
            return;
        };
        if prev.is_none() {
            return;
        }
        self.dep_link_mut(prev).init_dependency(tp);
        self.dep_node_mut(dep_node).base_mut().additional_after = prev;
    }

    /// Port of `CDependencyFactory::createDATAASSERTIONDependency`.
    /// Upstream `CDependencyFactory.cpp` 380–388.
    ///
    /// The algorithm-layer wrapper owns the `mConfBuildDependencies` guard; this
    /// is the factory body shape after that guard: allocate the
    /// `CDATAASSERTIONDependencyNode`, run `initDATAASSERTIONDependencyNode`, and
    /// read back the continuation track point.
    pub fn create_dataassertion_dependency(
        &mut self,
        value_dep_track_point: &mut TrackPointId,
        process_indi: &mut NodeId,
        prev_dep_track_point: TrackPointId,
    ) -> DependencyId {
        let dep_node = self.alloc_det_link_dependency_node(DepKind::DataAssertion);
        {
            let dep = self.dep_node_mut(dep_node);
            dep.init_deterministic_dependency_node_indi(
                DepKind::DataAssertion,
                *process_indi,
                ConDescId::NONE,
            );
            dep.base_mut().dep_track_point = prev_dep_track_point;
        }
        self.update_dependency_branching_tag(dep_node);
        *value_dep_track_point = self.materialize_continue_dependency_track_point(dep_node);
        dep_node
    }

    /// Port of `CDependencyFactory::createMERGEDLINKDependency`.
    /// Upstream `CDependencyFactory.cpp` has the standard alloc/init/read-back body.
    pub fn create_merged_link_dependency_node(
        &mut self,
        merged_link_continue_dep_track_point: &mut TrackPointId,
        merge_prev_dep_track_point: TrackPointId,
        link_prev_dep_track_point: TrackPointId,
    ) -> DependencyId {
        let dep_node = self.alloc_det_link_dependency_node(DepKind::MergedLink);
        {
            let dep = self.dep_node_mut(dep_node);
            dep.init_dependency_node(DepKind::MergedLink, ConDescId::NONE);
            dep.base_mut().dep_track_point = merge_prev_dep_track_point;
        }
        self.bind_det_link_prev(dep_node, link_prev_dep_track_point);
        self.update_dependency_branching_tag(dep_node);
        *merged_link_continue_dep_track_point =
            self.materialize_continue_dependency_track_point(dep_node);
        dep_node
    }

    /// Port of `CDependencyFactory::createMERGEDINDIVIDUALDependency`.
    pub fn create_merged_individual_dependency_node(
        &mut self,
        merged_individual_continue_dep_track_point: &mut TrackPointId,
        merge_prev_dep_track_point: TrackPointId,
        individual_prev_dep_track_point: TrackPointId,
    ) -> DependencyId {
        let dep_node = self.alloc_det_link_dependency_node(DepKind::MergedIndividual);
        {
            let dep = self.dep_node_mut(dep_node);
            dep.init_dependency_node(DepKind::MergedIndividual, ConDescId::NONE);
            dep.base_mut().dep_track_point = merge_prev_dep_track_point;
        }
        self.bind_det_link_prev(dep_node, individual_prev_dep_track_point);
        self.update_dependency_branching_tag(dep_node);
        *merged_individual_continue_dep_track_point =
            self.materialize_continue_dependency_track_point(dep_node);
        dep_node
    }

    /// Port of `CDependencyFactory::createMERGEDependency`.
    pub fn create_merge_dependency_node(
        &mut self,
        branch_node: BranchNodeId,
        concept_descriptor: ConDescId,
        prev_dep_track_point: TrackPointId,
    ) -> DependencyId {
        let dep_node = self.alloc_non_deterministic_dependency_node(DepKind::Merge);
        let clash_track_point = self.dep_node_mut(dep_node).init_merge_dependency_node(
            branch_node,
            concept_descriptor,
            prev_dep_track_point,
        );
        if clash_track_point.is_some() {
            let tp = self.track_point_mut(clash_track_point);
            tp.clashed_irrelevant = true;
        }
        self.update_dependency_branching_tags(dep_node);
        dep_node
    }

    /// Port of `CDependencyFactory::createMERGEPOSSIBLEINSTANCEINDIVIDUALDependencyNode`.
    pub fn create_merge_possible_instance_individual_dependency_node(
        &mut self,
        branch_node: BranchNodeId,
        individual_node: NodeId,
        prev_dep_track_point: TrackPointId,
    ) -> DependencyId {
        let dep_node =
            self.alloc_non_deterministic_dependency_node(DepKind::MergePossibleInstanceIndividual);
        let clash_track_point = {
            let dep = self.dep_node_mut(dep_node);
            dep.init_dependency_node_indi(
                DepKind::MergePossibleInstanceIndividual,
                individual_node,
                ConDescId::NONE,
            );
            dep.base_mut().dep_track_point = prev_dep_track_point;
            if let DependencyNode::NonDeterministic { nd, .. } = dep {
                nd.branch_track_points = nd.clash_track_point;
                nd.dependency_clashes = ClashDescId::NONE;
                nd.branch_node = branch_node;
                nd.branch_tag = 0;
                nd.closed_track_point = TrackPointId::NONE;
                nd.closing_track_point = TrackPointId::NONE;
                nd.clash_track_point
            } else {
                TrackPointId::NONE
            }
        };
        if clash_track_point.is_some() {
            self.track_point_mut(clash_track_point).clashed_irrelevant = true;
        }
        self.update_dependency_branching_tags(dep_node);
        dep_node
    }

    /// Port of `CDependencyFactory::createSAMEINDIVIDUALMERGEDependency`.
    pub fn create_same_individual_merge_dependency_node(
        &mut self,
        exp_continue_dep_track_point: &mut TrackPointId,
        prev_dep_track_point: TrackPointId,
        prev_other_dep_track_point: TrackPointId,
    ) -> DependencyId {
        let dep_node = self.alloc_det_link_dependency_node(DepKind::SameIndividualsMerge);
        {
            let dep = self.dep_node_mut(dep_node);
            dep.init_dependency_node(DepKind::SameIndividualsMerge, ConDescId::NONE);
            dep.base_mut().dep_track_point = prev_dep_track_point;
        }
        self.bind_det_link_prev(dep_node, prev_other_dep_track_point);
        self.update_dependency_branching_tag(dep_node);
        *exp_continue_dep_track_point = self.materialize_continue_dependency_track_point(dep_node);
        dep_node
    }

    /// Allocate the two-back-edge `CFUNCTIONALDependencyNode` (`DNTFUNCTIONAL`),
    /// the only `DetLink2`. Co-allocates both inline `CDependency` back-edges
    /// (`mPrevLink1Dep`, `mPrevLink2Dep`).
    pub fn alloc_functional_dependency_node(&mut self) -> DependencyId {
        let prev1 = self.alloc_dep_link(empty_dep_link());
        let prev2 = self.alloc_dep_link(empty_dep_link());
        self.alloc_dep_node(DependencyNode::DetLink2 {
            base: empty_base(DepKind::Functional),
            prev1,
            prev2,
        })
    }

    /// Allocate a `CNonDeterministicDependencyNode` of tag `kind` (`MERGE`,
    /// `ATMOST`, `QUALIFY`, `MERGEPOSSIBLEINSTANCEINDIVIDUAL`, the `REUSE*` non-det
    /// family, …). Co-allocates the inline clash `CNonDeterministicDependencyTrackPoint`
    /// and back-links it to the node (the C++ inline-member identity), so the
    /// wrapper's `init_non_deterministic_dependency_node` can deref it.
    pub fn alloc_non_deterministic_dependency_node(&mut self, kind: DepKind) -> DependencyId {
        let clash_tp = self.alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
        let dep = self.alloc_dep_node(DependencyNode::NonDeterministic {
            base: empty_base(kind),
            nd: empty_non_det(clash_tp),
        });
        self.track_point_mut(clash_tp).dep_node = dep;
        dep
    }

    /// Allocate a `CORDependencyNode` (`DNTORDEPENDENCY`) — non-deterministic + the
    /// `⊔`-disjunct track data. Co-allocates the inline clash track point (as the
    /// non-det allocator) and an empty `OrDisjunctTrackData`.
    pub fn alloc_or_dependency_node(&mut self) -> DependencyId {
        let clash_tp = self.alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
        let dep = self.alloc_dep_node(DependencyNode::Or {
            base: empty_base(DepKind::Or),
            nd: empty_non_det(clash_tp),
            disj: OrDisjunctTrackData::default(),
        });
        self.track_point_mut(clash_tp).dep_node = dep;
        dep
    }

    /// Allocate a `CREUSEBACKENDEXPANSIONMODESDependencyNode`
    /// (`DNTREUSEBACKENDEXPANSIONMODESDEPENDENCY`) — non-deterministic + the
    /// `CXLinker<cint64>` involved-id list (empty at construction). Co-allocates the
    /// inline clash track point.
    pub fn alloc_reuse_backend_modes_dependency_node(&mut self) -> DependencyId {
        let clash_tp = self.alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
        let dep = self.alloc_dep_node(DependencyNode::ReuseBackendModes {
            base: empty_base(DepKind::ReuseBackendExpansionModes),
            nd: empty_non_det(clash_tp),
            fixed_reuse_dep_track_point: TrackPointId::NONE,
            priorized_reuse_dep_track_point: TrackPointId::NONE,
            involved: Vec::new(),
            affected: Vec::new(),
        });
        self.track_point_mut(clash_tp).dep_node = dep;
        dep
    }

    // =======================================================================
    // The continuation-track-point read-back — the
    // `xContinueDepTrackPoint = depNode->getContinueDependencyTrackPoint()` step.
    // =======================================================================

    /// Port of the factory's `depNode->getContinueDependencyTrackPoint()` read-back
    /// (`CDependencyNode.cpp`, `CDeterministicDependencyNode::getContinueDependencyTrackPoint`
    /// returns `this`; `CNonDeterministicDependencyNode` returns `&mClashTrackPoint`).
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: a `CDeterministicDependencyNode` multiply-inherits
    /// `CDependencyTrackPoint`, so the node IS its own continuation point and `this`
    /// is returned. The arena split keeps node and track point in separate pools, so
    /// the det case materialises a `DependencyTrackPoint` bound back to the node here
    /// because this factory has the `ProcessContext` needed to allocate it. The
    /// non-det case returns the pre-allocated `nd.clash_track_point` directly. The
    /// factory calls this once per `create*` (matching the single C++ read-back), so
    /// the det allocation is not duplicated.
    pub fn materialize_continue_dependency_track_point(
        &mut self,
        dep: DependencyId,
    ) -> TrackPointId {
        // Each `self.dep_node(dep)` is a fresh temporary borrow ending at the
        // statement, so the det branch's `&mut self` alloc does not alias it.
        if self.dep_node(dep).is_deterministic() {
            // CDeterministicDependencyNode::getContinueDependencyTrackPoint → `this`.
            let process_tag = self.dep_node(dep).base().process_tag;
            let mut track_point = DependencyTrackPoint::new(dep);
            track_point.process_tag = process_tag;
            self.alloc_track_point(track_point)
        } else {
            // CNonDeterministicDependencyNode::getContinueDependencyTrackPoint
            //   → &mClashTrackPoint.
            self.dep_node(dep).clash_track_point()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tagged_track_point(ctx: &mut ProcessContext, tag: i64) -> TrackPointId {
        let mut track_point = DependencyTrackPoint::new(DependencyId::NONE);
        track_point.add_maximum_branching_tag_candidate(tag);
        ctx.alloc_track_point(track_point)
    }

    fn det_link_previous(ctx: &ProcessContext, dep_node: DependencyId) -> DepLinkId {
        if let DependencyNode::DetLink { prev, .. } = ctx.dep_node(dep_node) {
            *prev
        } else {
            DepLinkId::NONE
        }
    }

    #[test]
    fn dependency_factory_creates_merged_link_and_same_individual_nodes() {
        let mut ctx = ProcessContext::new();
        let merge_tp = tagged_track_point(&mut ctx, 3);
        let other_tp = tagged_track_point(&mut ctx, 7);

        let mut merged_link_continue = TrackPointId::NONE;
        let merged_link =
            ctx.create_merged_link_dependency_node(&mut merged_link_continue, merge_tp, other_tp);
        assert_eq!(ctx.dep_node(merged_link).kind(), DepKind::MergedLink);
        assert_eq!(ctx.dep_node(merged_link).base().dep_track_point, merge_tp);
        assert_eq!(
            ctx.dep_link(det_link_previous(&ctx, merged_link))
                .previous_dependency_track_point(),
            other_tp
        );
        // max over BOTH back-edges: the bound merging-step dependency is
        // CHAINED onto additional-after (Konclude addAfterDependency), so its
        // tag (7) dominates the concept-prev tag (3).
        assert_eq!(ctx.dep_node(merged_link).base().process_tag, 7);
        assert_eq!(
            ctx.track_point(merged_link_continue).dependency_node(),
            merged_link
        );

        let mut same_continue = TrackPointId::NONE;
        let same = ctx.create_same_individual_merge_dependency_node(
            &mut same_continue,
            merge_tp,
            other_tp,
        );
        assert_eq!(ctx.dep_node(same).kind(), DepKind::SameIndividualsMerge);
        assert_eq!(
            ctx.dep_link(det_link_previous(&ctx, same))
                .previous_dependency_track_point(),
            other_tp
        );
        assert_eq!(ctx.track_point(same_continue).dependency_node(), same);
    }

    #[test]
    fn dependency_factory_creates_merged_individual_and_merge_nodes() {
        let mut ctx = ProcessContext::new();
        let merge_tp = tagged_track_point(&mut ctx, 5);
        let individual_tp = tagged_track_point(&mut ctx, 11);

        let mut merged_individual_continue = TrackPointId::NONE;
        let merged_individual = ctx.create_merged_individual_dependency_node(
            &mut merged_individual_continue,
            merge_tp,
            individual_tp,
        );
        assert_eq!(
            ctx.dep_node(merged_individual).kind(),
            DepKind::MergedIndividual
        );
        assert_eq!(
            ctx.dep_link(det_link_previous(&ctx, merged_individual))
                .previous_dependency_track_point(),
            individual_tp
        );
        assert_eq!(
            ctx.track_point(merged_individual_continue)
                .dependency_node(),
            merged_individual
        );

        let merge =
            ctx.create_merge_dependency_node(BranchNodeId::new(13), ConDescId::new(17), merge_tp);
        assert_eq!(ctx.dep_node(merge).kind(), DepKind::Merge);
        assert_eq!(ctx.dep_node(merge).concept_descriptor(), ConDescId::new(17));
        assert_eq!(ctx.dep_node(merge).base().dep_track_point, merge_tp);
        assert_eq!(ctx.dep_node(merge).branch_node(), BranchNodeId::new(13));
        let clash_tp = ctx.dep_node(merge).clash_track_point();
        assert_eq!(ctx.dep_node(merge).branch_track_points(), clash_tp);
        assert_eq!(ctx.track_point(clash_tp).dependency_node(), merge);
        assert!(ctx.track_point(clash_tp).clashed_irrelevant);
        assert_eq!(ctx.track_point(clash_tp).get_branching_tag(), 5);
    }
}
