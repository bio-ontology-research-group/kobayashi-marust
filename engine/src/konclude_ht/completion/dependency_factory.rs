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
            involved: Vec::new(),
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
    /// (the dep1.rs `continue_dependency_track_point` returned `Id::NONE` with a
    /// `W2-DEFER[api]` for exactly this lazy materialisation, which needs the
    /// `ProcessContext` to allocate). The non-det case returns the pre-allocated
    /// `nd.clash_track_point` directly. The factory calls this once per `create*`
    /// (matching the single C++ read-back), so the det allocation is not duplicated.
    pub fn materialize_continue_dependency_track_point(&mut self, dep: DependencyId) -> TrackPointId {
        // Each `self.dep_node(dep)` is a fresh temporary borrow ending at the
        // statement, so the det branch's `&mut self` alloc does not alias it.
        if self.dep_node(dep).is_deterministic() {
            // CDeterministicDependencyNode::getContinueDependencyTrackPoint → `this`.
            self.alloc_track_point(DependencyTrackPoint::new(dep))
        } else {
            // CNonDeterministicDependencyNode::getContinueDependencyTrackPoint
            //   → &mClashTrackPoint.
            self.dep_node(dep).clash_track_point()
        }
    }
}
