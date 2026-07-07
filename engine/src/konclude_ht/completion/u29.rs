//! `completion::u29` — Dependency tracking / backtracking family, batch
//! (port unit #29 of 36).
//!
//! Faithful port of the 27 methods the manifest (`01-completion-methods.md`,
//! "Unit 29") groups under dependency-node construction + clash backtracking of
//! Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`.
//! cpp source line ranges (1-based) are noted on each item.
//!
//! Methods (cpp order):
//!   * the 13 `create*Dependency` factory wrappers                 [10123–10265]
//!   * `clashedBacktracking`                                       [6774–6861]
//!   * `backtrackFromTrackingLine`                                 [6963–6974]
//!   * `backtrackFromTrackingLineStep`                             [6976–7073]
//!   * `backtrackNonDeterministicBranchingClashedDescriptorFromCurrentIndividualNodeLevel`  [7075–7077]
//!   * `backtrackNonDeterministicBranchingClashedDescriptorFromPreviousIndividualNodeLevel` [7080–7082]
//!   * `backtrackNonDeterministicBranchingClashedDescriptor`       [7085–7349]
//!   * `backtrackDeterministicBranchingClashedDescriptorFromCurrentIndividualNodeLevel`     [7655–7665]
//!   * `backtrackDeterministicClashedDescriptorFromPreviousIndividualNodeLevels`            [7669–7674]
//!   * `getBacktrackedDeterministicClashedDescriptorsBeforeProcessingTag`  [7677–7772]
//!   * `getBacktrackedDeterministicClashedDescriptors`            [7779–7863]
//!   * `tryGetInvalidSameIndividualNodeLevelBacktrackedDeterministicClashedDescriptors`     [7866–7896]
//!   * `createNonDeterministicDependencyTrackPointBranch`         [16669–16685]
//!   * `createDependendBranchingTaskList`                         [17182–17198]
//!   * `hasNondeterministicDependency`                            [23027–23033]
//!
//! KONCLUDE-PORT-NOTE[ownership]: each method is a member of
//! `CCalculationTableauCompletionTaskHandleAlgorithm`, so it becomes `&mut self`
//! plus the threaded per-thread context `calc_alg_context: &mut
//! CalculationAlgorithmContextBase`. C++ `CIndividualProcessNode*&` in/out
//! pointer-references become `&mut NodeId`; a plain value pointer becomes the
//! matching id; `CConceptDescriptor*` → `ConDescId`; `CDependencyTrackPoint*` →
//! `TrackPointId`; the returned `C*DependencyNode*` (all of the tagged
//! `DependencyNode` enum) → `DependencyId`. The per-test arenas are reached
//! through the context (`calc_alg_context.process_context()` / `_mut()`), the
//! databox as `calc_alg_context.processing_data_box{,_mut}()`.
//!
//! KONCLUDE-PORT-NOTE[api]: `CDependency*` (the additional-dependency back-edge
//! element carried as `prevOtherDependencies`) maps to `DepLinkId` (the ported
//! `DependencyLink` record — the additional-dependency link the dependency factory
//! threads onto the new node).
//!
//! Deferral landscape. Two subsystems gate most of this unit:
//!   * the `CDependencyFactory` (`self.dependency_factory` /
//!     `calc_alg_context...used_dep_factory`, a zero-size `Id` stub) — every
//!     `create*Dependency` wrapper bottoms out in one `factory->create*Dependency`
//!     call; the `mConfBuildDependencies` guard + null return are ported in full,
//!     the factory call is `W6-DEFER[api]`;
//!   * the clash-backtracking tracked records (`CTrackedClashedDescriptor`,
//!     `CTrackedClashedDescriptorHasher`, `CTrackedClashedDependencyLine`) now
//!     exist in Unit 30, and the tracking-line step dispatcher is live. The deeper
//!     non-deterministic branch task handling and deterministic descriptor
//!     re-derivation helpers remain `// PORT-PENDING` with faithful C++
//!     transcriptions. Logic is documented, never silently dropped.
//!
//! Fully ported here (substrate-resolvable): `createATMOSTDependency`,
//! `createREUSEINDIVIDUALDependency`, `createREUSECOMPLETIONGRAPHDependency`,
//! `createREUSECONCEPTSDependency`, `createQUALIFYDependency`,
//! `hasNondeterministicDependency` (the deterministic-branch-tag comparison),
//! `backtrackFromTrackingLine` and `backtrackFromTrackingLineStep` over the live
//! Unit 30 tracking-line buckets, the two non-deterministic backtrack forwarders,
//! deterministic current/previous wrapper call points, and the
//! `mConfBuildDependencies`/`mConfBuildAllBranchingNodes` decision structure of
//! the other `create*` wrappers + `createNonDeterministicDependencyTrackPointBranch`.

#![allow(dead_code)]
#![allow(unused_variables)]

use super::super::model::substrate::{Cint64, Id, INVALID};
use super::super::process::dependency::{DepKind, DependencyNode};
use super::super::process::varbind::VarBindingPathId;
use super::super::process::{
    ClashDescId, ConDescId, DepLinkId, DependencyId, NodeId, TrackPointId,
};
use super::context::CalculationAlgorithmContextBase;
use super::stubs::SatisfiableCalculationTask;
use super::u30::TrackedClashedDependencyLine;

/// `Id<SatisfiableCalculationTask>` — the Task-layer handle (W6 stub) the branch
/// task-list builder returns.
type SatCalcTaskId = Id<SatisfiableCalculationTask>;

impl super::algorithm::CompletionTaskHandleAlgorithm {
    // =======================================================================
    // Dependency-node factory wrappers (cpp 10123–10265).
    //
    // Each is the identical Konclude idiom:
    //   CXDependencyNode* depNode = nullptr;
    //   if (mConfBuildDependencies)
    //       depNode = calcAlgContext->getUsedDependencyFactory()->createXDependency(...);
    //   return depNode;
    // The `mConfBuildDependencies` guard + null (`Id::NONE`) return are ported in
    // full; wrappers listed as fully ported above use the existing typed arena
    // allocators directly, while the remaining factory dispatches stay W6-DEFER[api].
    // All return the tagged `DependencyId`.
    // =======================================================================

    /// Port of `createATMOSTDependency`. cpp 10123–10129.
    pub fn create_atmost_dependency(
        &mut self,
        process_indi: &mut NodeId,
        con_des: ConDescId,
        prev_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node = Id::NONE;
        if self.conf_build_dependencies {
            let branch_node = calc_alg_context.base.used_branch_tree_node();
            let pc = calc_alg_context.process_context_mut();
            dep_node = pc.alloc_non_deterministic_dependency_node(DepKind::AtMost);

            let clash_track_point = {
                let dep = pc.dep_node_mut(dep_node);
                dep.init_dependency_node_indi(DepKind::AtMost, *process_indi, con_des);
                dep.base_mut().dep_track_point = prev_dep_track_point;
                match dep {
                    DependencyNode::NonDeterministic { nd, .. } => {
                        nd.branch_track_points = nd.clash_track_point;
                        nd.dependency_clashes = Id::NONE;
                        nd.branch_node = branch_node;
                        nd.branch_tag = 0;
                        nd.closed_track_point = Id::NONE;
                        nd.closing_track_point = Id::NONE;
                        nd.clash_track_point
                    }
                    _ => unreachable!("AtMost dependency allocated with non-det shape"),
                }
            };
            pc.track_point_mut(clash_track_point).clashed_irrelevant = true;
            pc.update_dependency_branching_tags(dep_node);
        }
        dep_node
    }

    /// Port of `createREUSEINDIVIDUALDependency`. cpp 10139–10145.
    pub fn create_reuse_individual_dependency(
        &mut self,
        process_indi: NodeId,
        con_des: ConDescId,
        prev_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node = Id::NONE;
        if self.conf_build_dependencies {
            let branch_node = calc_alg_context.base.used_branch_tree_node();
            let pc = calc_alg_context.process_context_mut();
            dep_node = pc.alloc_non_deterministic_dependency_node(DepKind::ReuseIndividual);

            let clash_track_point = {
                let dep = pc.dep_node_mut(dep_node);
                dep.init_dependency_node_indi(DepKind::ReuseIndividual, process_indi, con_des);
                dep.base_mut().dep_track_point = prev_dep_track_point;
                match dep {
                    DependencyNode::NonDeterministic { nd, .. } => {
                        nd.branch_track_points = nd.clash_track_point;
                        nd.dependency_clashes = Id::NONE;
                        nd.branch_node = branch_node;
                        nd.branch_tag = 0;
                        nd.closed_track_point = Id::NONE;
                        nd.closing_track_point = Id::NONE;
                        nd.clash_track_point
                    }
                    _ => unreachable!("ReuseIndividual dependency allocated with non-det shape"),
                }
            };
            pc.track_point_mut(clash_track_point).clashed_irrelevant = true;
            pc.update_dependency_branching_tags(dep_node);
        }
        dep_node
    }

    /// Port of `createREUSECOMPLETIONGRAPHDependency`. cpp 10147–10153.
    pub fn create_reuse_completion_graph_dependency(
        &mut self,
        process_indi: &mut NodeId,
        con_des: ConDescId,
        prev_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node = Id::NONE;
        if self.conf_build_dependencies {
            let branch_node = calc_alg_context.base.used_branch_tree_node();
            let pc = calc_alg_context.process_context_mut();
            dep_node = pc.alloc_non_deterministic_dependency_node(DepKind::ReuseCompletionGraph);

            let clash_track_point = {
                let dep = pc.dep_node_mut(dep_node);
                dep.init_dependency_node_indi(
                    DepKind::ReuseCompletionGraph,
                    *process_indi,
                    con_des,
                );
                dep.base_mut().dep_track_point = prev_dep_track_point;
                match dep {
                    DependencyNode::NonDeterministic { nd, .. } => {
                        nd.branch_track_points = nd.clash_track_point;
                        nd.dependency_clashes = Id::NONE;
                        nd.branch_node = branch_node;
                        nd.branch_tag = 0;
                        nd.closed_track_point = Id::NONE;
                        nd.closing_track_point = Id::NONE;
                        nd.clash_track_point
                    }
                    _ => {
                        unreachable!("ReuseCompletionGraph dependency allocated with non-det shape")
                    }
                }
            };
            pc.track_point_mut(clash_track_point).clashed_irrelevant = true;
            pc.update_dependency_branching_tags(dep_node);
        }
        dep_node
    }

    /// Port of `createREUSECONCEPTSDependency`. cpp 10165–10171.
    pub fn create_reuse_concepts_dependency(
        &mut self,
        process_indi: NodeId,
        con_des: ConDescId,
        prev_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node = Id::NONE;
        if self.conf_build_dependencies {
            let branch_node = calc_alg_context.base.used_branch_tree_node();
            let pc = calc_alg_context.process_context_mut();
            dep_node = pc.alloc_non_deterministic_dependency_node(DepKind::ReuseConcepts);

            let clash_track_point = {
                let dep = pc.dep_node_mut(dep_node);
                dep.init_dependency_node_indi(DepKind::ReuseConcepts, process_indi, con_des);
                dep.base_mut().dep_track_point = prev_dep_track_point;
                match dep {
                    DependencyNode::NonDeterministic { nd, .. } => {
                        nd.branch_track_points = nd.clash_track_point;
                        nd.dependency_clashes = Id::NONE;
                        nd.branch_node = branch_node;
                        nd.branch_tag = 0;
                        nd.closed_track_point = Id::NONE;
                        nd.closing_track_point = Id::NONE;
                        nd.clash_track_point
                    }
                    _ => unreachable!("ReuseConcepts dependency allocated with non-det shape"),
                }
            };
            pc.track_point_mut(clash_track_point).clashed_irrelevant = true;
            pc.update_dependency_branching_tags(dep_node);
        }
        dep_node
    }

    /// Port of `createQUALIFYDependency`. cpp 10173–10179.
    pub fn create_qualify_dependency(
        &mut self,
        process_indi: &mut NodeId,
        con_des: ConDescId,
        prev_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node = Id::NONE;
        if self.conf_build_dependencies {
            let branch_node = calc_alg_context.base.used_branch_tree_node();
            let pc = calc_alg_context.process_context_mut();
            dep_node = pc.alloc_non_deterministic_dependency_node(DepKind::Qualify);

            let clash_track_point = {
                let dep = pc.dep_node_mut(dep_node);
                dep.init_dependency_node_indi(DepKind::Qualify, *process_indi, con_des);
                dep.base_mut().dep_track_point = prev_dep_track_point;
                match dep {
                    DependencyNode::NonDeterministic { nd, .. } => {
                        nd.branch_track_points = nd.clash_track_point;
                        nd.dependency_clashes = Id::NONE;
                        nd.branch_node = branch_node;
                        nd.branch_tag = 0;
                        nd.closed_track_point = Id::NONE;
                        nd.closing_track_point = Id::NONE;
                        nd.clash_track_point
                    }
                    _ => unreachable!("Qualify dependency allocated with non-det shape"),
                }
            };
            pc.track_point_mut(clash_track_point).clashed_irrelevant = true;
            pc.update_dependency_branching_tags(dep_node);
        }
        dep_node
    }

    /// Port of `createORONLYOPTIONDependency`. cpp 10183–10189.
    ///
    /// `or_continue_dep_track_point` is the C++ `CDependencyTrackPoint*&` out
    /// reference the factory fills with the continuation point; deferred with the
    /// factory call.
    pub fn create_oronly_option_dependency(
        &mut self,
        or_continue_dep_track_point: &mut TrackPointId,
        process_indi: &mut NodeId,
        con_des: ConDescId,
        prev_dep_track_point: TrackPointId,
        prev_other_dependencies: DepLinkId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node = Id::NONE;
        if self.conf_build_dependencies {
            dep_node = calc_alg_context
                .process_context_mut()
                .alloc_deterministic_dependency_node(DepKind::OrOnlyOption);
            {
                let proc_ctx = calc_alg_context.process_context_mut();
                let dep = proc_ctx.dep_node_mut(dep_node);
                dep.init_deterministic_dependency_node(DepKind::OrOnlyOption, con_des);
                dep.base_mut().dep_track_point = prev_dep_track_point;
                if prev_other_dependencies.is_some() {
                    dep.base_mut().additional_after = prev_other_dependencies;
                }
                proc_ctx.update_dependency_branching_tag(dep_node);
            }
            *or_continue_dep_track_point = calc_alg_context
                .process_context_mut()
                .materialize_continue_dependency_track_point(dep_node);
            let _ = process_indi;
        }
        dep_node
    }

    /// Port of `createIMPLICATIONDependency`. cpp 10192–10198.
    pub fn create_implication_dependency(
        &mut self,
        impl_continue_dep_track_point: &mut TrackPointId,
        process_indi: &mut NodeId,
        con_des: ConDescId,
        prev_dep_track_point: TrackPointId,
        prev_other_dependencies: DepLinkId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node = Id::NONE;
        if self.conf_build_dependencies {
            dep_node = calc_alg_context
                .process_context_mut()
                .alloc_deterministic_dependency_node(DepKind::Implication);
            {
                let proc_ctx = calc_alg_context.process_context_mut();
                let dep = proc_ctx.dep_node_mut(dep_node);
                dep.init_deterministic_dependency_node(DepKind::Implication, con_des);
                dep.base_mut().dep_track_point = prev_dep_track_point;
                if prev_other_dependencies.is_some() {
                    dep.base_mut().additional_after = prev_other_dependencies;
                }
                proc_ctx.update_dependency_branching_tag(dep_node);
            }
            *impl_continue_dep_track_point = calc_alg_context
                .process_context_mut()
                .materialize_continue_dependency_track_point(dep_node);
            let _ = process_indi;
        }
        dep_node
    }

    /// Port of `createEXPANDEDDependency`. cpp 10201–10207.
    pub fn create_expanded_dependency(
        &mut self,
        exp_continue_dep_track_point: &mut TrackPointId,
        process_indi: &mut NodeId,
        prev_dep_track_point: TrackPointId,
        prev_other_dependencies: DepLinkId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node = Id::NONE;
        if self.conf_build_dependencies {
            dep_node = calc_alg_context
                .process_context_mut()
                .alloc_deterministic_dependency_node(DepKind::Expanded);
            {
                let proc_ctx = calc_alg_context.process_context_mut();
                let dep = proc_ctx.dep_node_mut(dep_node);
                dep.init_deterministic_dependency_node(DepKind::Expanded, ConDescId::NONE);
                dep.base_mut().dep_track_point = prev_dep_track_point;
                if prev_other_dependencies.is_some() {
                    dep.base_mut().additional_after = prev_other_dependencies;
                }
                proc_ctx.update_dependency_branching_tag(dep_node);
            }
            *exp_continue_dep_track_point = calc_alg_context
                .process_context_mut()
                .materialize_continue_dependency_track_point(dep_node);
            let _ = process_indi;
        }
        dep_node
    }

    /// Port of `createCONNECTIONDependency`. cpp 10210–10216.
    pub fn create_connection_dependency(
        &mut self,
        process_indi: &mut NodeId,
        con_des: ConDescId,
        prev_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node = Id::NONE;
        if self.conf_build_dependencies {
            dep_node = calc_alg_context
                .process_context_mut()
                .alloc_deterministic_dependency_node(DepKind::Connection);
            {
                let proc_ctx = calc_alg_context.process_context_mut();
                let dep = proc_ctx.dep_node_mut(dep_node);
                dep.init_deterministic_dependency_node(DepKind::Connection, con_des);
                dep.base_mut().dep_track_point = prev_dep_track_point;
                proc_ctx.update_dependency_branching_tag(dep_node);
            }
            let _continue_track_point = calc_alg_context
                .process_context_mut()
                .materialize_continue_dependency_track_point(dep_node);
            let _ = process_indi;
        }
        dep_node
    }

    /// Port of `createREUSEBACKENDEXPANSIONMODESDependency`. cpp 10230–10236.
    pub fn create_reuse_backend_expansion_modes_dependency(
        &mut self,
        prev_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node = Id::NONE;
        if self.conf_build_dependencies {
            let branch_node = calc_alg_context.base.used_branch_tree_node();
            let pc = calc_alg_context.process_context_mut();
            dep_node = pc.alloc_reuse_backend_modes_dependency_node();

            let clash_track_point = {
                let dep = pc.dep_node_mut(dep_node);
                dep.init_dependency_node_indi(
                    DepKind::ReuseBackendExpansionModes,
                    NodeId::NONE,
                    ConDescId::NONE,
                );
                dep.base_mut().dep_track_point = prev_dep_track_point;
                match dep {
                    DependencyNode::ReuseBackendModes {
                        nd,
                        fixed_reuse_dep_track_point,
                        priorized_reuse_dep_track_point,
                        involved,
                        affected,
                        ..
                    } => {
                        nd.branch_track_points = nd.clash_track_point;
                        nd.dependency_clashes = Id::NONE;
                        nd.branch_node = branch_node;
                        nd.branch_tag = 0;
                        nd.closed_track_point = Id::NONE;
                        nd.closing_track_point = Id::NONE;
                        *fixed_reuse_dep_track_point = Id::NONE;
                        *priorized_reuse_dep_track_point = Id::NONE;
                        involved.clear();
                        affected.clear();
                        nd.clash_track_point
                    }
                    _ => unreachable!("ReuseBackendModes dependency allocated with wrong shape"),
                }
            };
            pc.track_point_mut(clash_track_point).clashed_irrelevant = true;
            pc.update_dependency_branching_tags(dep_node);
            // KONCLUDE-PORT-NOTE[ownership]: fixed/prioritized/affected side
            // fields are explicit Rust fields on `ReuseBackendModes`; the
            // affected atomic linker is modelled as compare-and-set on a Vec.
        }
        dep_node
    }

    /// Port of `createREUSEBACKENDFIXEDINDIVIDUALEXPANSIONDependency`. cpp 10239–10245.
    pub fn create_reuse_backend_fixed_individual_expansion_dependency(
        &mut self,
        process_indi: &mut NodeId,
        prev_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node = Id::NONE;
        if self.conf_build_dependencies {
            let branch_node = calc_alg_context.base.used_branch_tree_node();
            let pc = calc_alg_context.process_context_mut();
            dep_node = pc.alloc_non_deterministic_dependency_node(
                DepKind::ReuseBackendFixedIndividualExpansion,
            );

            let clash_track_point = {
                let dep = pc.dep_node_mut(dep_node);
                dep.init_dependency_node_indi(
                    DepKind::ReuseBackendFixedIndividualExpansion,
                    *process_indi,
                    ConDescId::NONE,
                );
                dep.base_mut().dep_track_point = prev_dep_track_point;
                match dep {
                    DependencyNode::NonDeterministic { nd, .. } => {
                        nd.branch_track_points = nd.clash_track_point;
                        nd.dependency_clashes = Id::NONE;
                        nd.branch_node = branch_node;
                        nd.branch_tag = 0;
                        nd.closed_track_point = Id::NONE;
                        nd.closing_track_point = Id::NONE;
                        nd.clash_track_point
                    }
                    _ => unreachable!(
                        "ReuseBackendFixedIndividualExpansion dependency allocated with non-det shape"
                    ),
                }
            };
            pc.track_point_mut(clash_track_point).clashed_irrelevant = true;
            pc.update_dependency_branching_tags(dep_node);
        }
        dep_node
    }

    /// Port of `createREUSEBACKENDPRIORITIZEDINDIVIDUALEXPANSIONDependency`. cpp 10248–10254.
    pub fn create_reuse_backend_prioritized_individual_expansion_dependency(
        &mut self,
        process_indi: &mut NodeId,
        prev_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node = Id::NONE;
        if self.conf_build_dependencies {
            let branch_node = calc_alg_context.base.used_branch_tree_node();
            let pc = calc_alg_context.process_context_mut();
            dep_node = pc.alloc_non_deterministic_dependency_node(
                DepKind::ReuseBackendPrioritizedIndividualExpansion,
            );

            let clash_track_point = {
                let dep = pc.dep_node_mut(dep_node);
                dep.init_dependency_node_indi(
                    DepKind::ReuseBackendPrioritizedIndividualExpansion,
                    *process_indi,
                    ConDescId::NONE,
                );
                dep.base_mut().dep_track_point = prev_dep_track_point;
                match dep {
                    DependencyNode::NonDeterministic { nd, .. } => {
                        nd.branch_track_points = nd.clash_track_point;
                        nd.dependency_clashes = Id::NONE;
                        nd.branch_node = branch_node;
                        nd.branch_tag = 0;
                        nd.closed_track_point = Id::NONE;
                        nd.closing_track_point = Id::NONE;
                        nd.clash_track_point
                    }
                    _ => unreachable!(
                        "ReuseBackendPrioritizedIndividualExpansion dependency allocated with non-det shape"
                    ),
                }
            };
            pc.track_point_mut(clash_track_point).clashed_irrelevant = true;
            pc.update_dependency_branching_tags(dep_node);
        }
        dep_node
    }

    /// Port of `createREUSEBACKENDVALUEDependency`. cpp 10259–10265.
    pub fn create_reuse_backend_value_dependency(
        &mut self,
        value_dep_track_point: &mut TrackPointId,
        process_indi: &mut NodeId,
        con_des: ConDescId,
        prev_dep_track_point: TrackPointId,
        nominal_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node = Id::NONE;
        if self.conf_build_dependencies {
            dep_node = calc_alg_context
                .process_context_mut()
                .alloc_det_link_dependency_node(DepKind::ReuseBackendValue);
            {
                let proc_ctx = calc_alg_context.process_context_mut();
                let prev = {
                    let dep = proc_ctx.dep_node_mut(dep_node);
                    dep.init_dependency_node_indi(
                        DepKind::ReuseBackendValue,
                        *process_indi,
                        con_des,
                    );
                    dep.base_mut().dep_track_point = prev_dep_track_point;
                    if let DependencyNode::DetLink { prev, .. } = dep {
                        *prev
                    } else {
                        unreachable!("REUSEBACKENDVALUE dependency allocated with DetLink shape")
                    }
                };
                if nominal_dep_track_point.is_some() {
                    proc_ctx.dep_link_mut(prev).dep_track_point = nominal_dep_track_point;
                }
                proc_ctx.update_dependency_branching_tag(dep_node);
            }
            *value_dep_track_point = calc_alg_context
                .process_context_mut()
                .materialize_continue_dependency_track_point(dep_node);
        }
        dep_node
    }

    // =======================================================================
    // Non-deterministic dependency track-point branch (cpp 16669–16685).
    // =======================================================================

    /// Port of `createNonDeterministicDependencyTrackPointBranch`. cpp 16669–16685.
    ///
    /// Allocates / fetches the branch tree node for a non-deterministic dependency
    /// node and increments its branching, then binds the node's branch track point
    /// to it. A fresh branch tree node is used for a single branch (or when all
    /// branching nodes are built); otherwise the context's current branch tree node
    /// is reused. Returns the bound non-deterministic track point.
    ///
    /// The `mConfBuildDependencies && dependencyNode` guard and the
    /// `singleBranch || mConfBuildAllBranchingNodes` split are ported in full.
    pub fn create_non_deterministic_dependency_track_point_branch(
        &mut self,
        dependency_node: DependencyId,
        single_branch: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> TrackPointId {
        let mut non_dep_track_point = Id::NONE;
        if self.conf_build_dependencies && dependency_node.is_some() {
            let branch_node = if single_branch || self.conf_build_all_branching_nodes {
                calc_alg_context.get_new_branch_tree_node()
            } else {
                calc_alg_context.base.used_branch_tree_node()
            };

            let pc = calc_alg_context.process_context_mut();
            non_dep_track_point = pc.dependency_track_point_branch(dependency_node);
            pc.branch_node_mut(branch_node)
                .branching_increment(non_dep_track_point);
            let branch_level = pc.branch_node(branch_node).get_branching_level();
            let track_point = pc.track_point_mut(non_dep_track_point);
            track_point.branch_node = branch_node;
            track_point.add_maximum_branching_tag_candidate(branch_level);
        }
        non_dep_track_point
    }

    // =======================================================================
    // Branch-dependent task list (cpp 17182–17198).
    // =======================================================================

    /// Port of `createDependendBranchingTaskList`. cpp 17182–17198.
    ///
    /// Allocates `new_task_count` fresh `CSatisfiableCalculationTask`s, each
    /// initialised as a branch-dependent child of the current task (with a debug
    /// task id when the parent depth < 90), front-spliced into a returned linked
    /// list.
    ///
    /// KONCLUDE-PORT-NOTE[memory-pool]: each task is bump-allocated from the
    /// temporary task-memory pool in C++; the port allocates it in the context's
    /// typed satisfiable-task arena.
    pub fn create_dependend_branching_task_list(
        &mut self,
        new_task_count: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> SatCalcTaskId {
        let mut task_list = Id::NONE;
        let used_sat_calc_task = calc_alg_context.base.used_sat_calc_task;
        for _ in 0..new_task_count {
            // W3-DEFER[macro]: STATINC(TASKCREATIONCOUNT, calcAlgContext).
            let sat_calc_task = calc_alg_context
                .base
                .alloc_branch_depended_satisfiable_calculation_task(used_sat_calc_task);
            let parent_depth = calc_alg_context
                .base
                .sat_calc_task(used_sat_calc_task)
                .base
                .get_task_depth();
            if parent_depth < 90 {
                let debug_slot = (parent_depth + 1) as usize;
                let task_id = self.debug_task_id_vector[debug_slot];
                self.debug_task_id_vector[debug_slot] += 1;
                calc_alg_context
                    .base
                    .sat_calc_task_mut(sat_calc_task)
                    .base
                    .set_task_id(task_id);
            }
            calc_alg_context
                .base
                .sat_calc_task_mut(sat_calc_task)
                .set_next(task_list);
            task_list = sat_calc_task;
        }
        task_list
    }

    // =======================================================================
    // Non-deterministic-dependency predicate (cpp 23027–23033). Fully ported.
    // =======================================================================

    /// Port of `hasNondeterministicDependency`. cpp 23027–23033.
    ///
    /// A dependency track point is non-deterministic unless its branching tag is at
    /// or below the databox's maximum deterministic branch tag.
    pub fn has_nondeterministic_dependency(
        &mut self,
        dependency_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut nondeterministically = true;
        if dependency_track_point.is_some()
            && calc_alg_context
                .process_context()
                .track_point(dependency_track_point)
                .get_branching_tag()
                <= calc_alg_context
                    .processing_data_box()
                    .maximum_deterministic_branch_tag()
        {
            nondeterministically = false;
        }
        nondeterministically
    }

    // =======================================================================
    // Clash backtracking (cpp 6774–7896).
    //
    // The driver + tracking-line stepping over the clash-dependency graph. The
    // record types `CTrackedClashedDescriptor`, `CTrackedClashedDescriptorHasher`,
    // and the stack-local `CTrackedClashedDependencyLine` now exist in Unit 30.
    // The remaining methods below still await the branch-filtered/backtracking
    // integration over those containers. `CClashedDependencyDescriptor*` IS
    // ported (`ClashDescId`). `cint64* minIndiLevel` → `Option<&mut Cint64>`.
    // =======================================================================

    /// Compact dependency-graph walk from a track point (tp → dep node →
    /// prev/additional), printing tag + kind per hop — the taint-lie hunter
    /// (see the SIBLING late-desc dump).
    fn ht_dump_dep_chain_of(
        &self,
        tp: TrackPointId,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) {
        let ctx = calc_alg_context.process_context();
        let mut stack: Vec<(TrackPointId, usize)> = vec![(tp, 2)];
        let mut seen: std::collections::HashSet<usize> = Default::default();
        let mut lines = 0;
        while let Some((t, d)) = stack.pop() {
            if t.is_none() || lines > 24 || d > 12 {
                continue;
            }
            if !seen.insert(t.index()) {
                continue;
            }
            lines += 1;
            let tpr = ctx.track_point(t);
            let dn = tpr.dependency_node();
            if dn.is_none() {
                eprintln!(
                    "{:indent$}tp#{} tag={} (BASE)",
                    "",
                    t.index(),
                    tpr.process_tag,
                    indent = d * 2
                );
                continue;
            }
            let node = ctx.dep_node(dn);
            let base = node.base();
            eprintln!(
                "{:indent$}tp#{} tag={} node={:?} nondet={}",
                "",
                t.index(),
                tpr.process_tag,
                node.kind(),
                node.kind().is_non_deterministic(),
                indent = d * 2
            );
            stack.push((base.dep_track_point, d + 1));
            let mut al = base.additional_after;
            while al.is_some() {
                stack.push((ctx.dep_link(al).dep_track_point, d + 1));
                al = ctx.dep_link(al).next;
            }
        }
    }

    /// Format a tracked-clash descriptor chain (concept tag/polarity, pointer
    /// class, branching-level tag, node level) — shared by the DDB-CLOSURE and
    /// the root-cancel dumps.
    fn ht_fmt_tracked_closure(
        &self,
        head: ClashDescId,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> String {
        let pc = calc_alg_context.process_context();
        let mut it = head;
        let mut parts: Vec<String> = Vec::new();
        while it.is_some() && parts.len() < 12 {
            let d = pc.clash_desc(it);
            let (ctag, cneg) =
                if let super::super::process::descriptor::ClashDescriptorKind::Tracked {
                    concept_descriptor,
                    ..
                } = &d.kind
                {
                    if concept_descriptor.is_some() {
                        let cd = pc.con_desc(*concept_descriptor);
                        let con = cd.get_concept();
                        (
                            if con.is_some() {
                                calc_alg_context
                                    .ontology_arenas()
                                    .concept(con)
                                    .get_concept_tag()
                            } else {
                                -1
                            },
                            cd.is_negated(),
                        )
                    } else {
                        (-1, false)
                    }
                } else {
                    (-1, false)
                };
            parts.push(format!(
                "[c={}{} ind={} det={} tag={} lvl={} tp={:?}]",
                if cneg { "¬" } else { "" },
                ctag,
                d.is_pointing_to_independent_dependency_node(),
                !d.is_pointing_to_non_deterministic_dependency_node(),
                d.get_branching_level_tag(),
                d.get_appropriated_individual_level(),
                d.get_dependency_track_point(),
            ));
            it = d.get_next_descriptor();
        }
        parts.join(" ")
    }

    /// Port of `clashedBacktracking`. cpp 6774–6861.
    ///
    /// Entry point: installs the clash descriptor linker, builds the tracked-clash
    /// descriptors, primes the tracking line (involved individuals, fixed-reuse
    /// involved-individual set), and — if the line initialises — backtracks it
    /// (cancelling the root task at branching level 0, caching current-level-only
    /// clashes) down to a fixpoint.
    pub fn clashed_backtracking(
        &mut self,
        clashes: ClashDescId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        calc_alg_context
            .processing_data_box_mut()
            .set_clashed_descriptor_linker(clashes);

        // W3-DEFER[instrumentation]: mTimerBacktracing + STATINC/STATINCM and
        // debug-string generation stay at the Konclude call points.
        let tracked_clash_descriptors =
            self.create_tracked_clashes_descriptors(clashes, calc_alg_context, INVALID, false);

        let mut tracked_clash_des_it = tracked_clash_descriptors;
        while tracked_clash_des_it.is_some() {
            let indi_id = calc_alg_context
                .process_context()
                .clash_desc(tracked_clash_des_it)
                .get_appropriated_individual_id();
            if indi_id
                <= calc_alg_context
                    .base
                    .max_completion_graph_cached_individual_node_id()
            {
                self.track_individual_extended_dependence(indi_id, calc_alg_context);
            }
            tracked_clash_des_it = calc_alg_context
                .process_context()
                .clash_desc(tracked_clash_des_it)
                .get_next_descriptor();
        }

        // DDB diagnostics (KM_BRIDGE_PROGRESS): dump the first few clash
        // closures — descriptor classes and tags decide the whole analysis.
        let dump_this_call =
            self.ddb_analysis_dumps < 8 && std::env::var_os("KM_BRIDGE_PROGRESS").is_some();
        // KM_BRIDGE_DUMP_CLASH additionally dumps the closure at the ROOT-CANCEL
        // moment (the verdict-deciding analysis), however late it happens.
        let dump_on_root_cancel = std::env::var_os("KM_BRIDGE_DUMP_CLASH").is_some();
        let mut closure_parts: Vec<String> = Vec::new();
        if dump_this_call || dump_on_root_cancel {
            closure_parts =
                vec![self.ht_fmt_tracked_closure(tracked_clash_descriptors, calc_alg_context)];
        }
        if dump_this_call {
            self.ddb_analysis_dumps += 1;
            eprintln!("DDB-CLOSURE {}", closure_parts.join(" "));
        }

        let mut tracking_line = TrackedClashedDependencyLine::new();
        // W6-DEFER[backend]: if fixed backend-reuse expansion mode is active,
        // Konclude allocates and installs an involved-individual tracking set here.
        let line_ok = self.initialize_tracking_line(
            &mut tracking_line,
            tracked_clash_descriptors,
            calc_alg_context,
        );
        if !line_ok {
            // diagnostics: how often the whole analysis aborts at line init
            // (tracking ERRORs in the closure) — the ddb_fallback precursor.
            self.ddb_line_init_fail_count += 1;
        }
        if line_ok {
            if dump_this_call {
                eprintln!(
                    "DDB-LINE branching_level={}",
                    tracking_line.get_branching_level(),
                );
            }
            if tracking_line.get_branching_level() == 0 {
                if dump_on_root_cancel && self.ddb_analysis_dumps < 16 {
                    self.ddb_analysis_dumps += 1;
                    eprintln!(
                        "DDB-ROOT-CANCEL closure: {}",
                        closure_parts.join(" ")
                    );
                }
                self.cancellation_root_task(calc_alg_context);
            }
            if tracking_line.has_only_current_individual_node_level_clashes_descriptors() {
                self.write_clash_descriptors_to_cache_from_line(
                    &mut tracking_line,
                    calc_alg_context,
                );
            }
            self.backtrack_from_tracking_line(&mut tracking_line, calc_alg_context);
        }
    }

    /// Port of `backtrackFromTrackingLine`. cpp 6963–6974.
    ///
    /// Repeatedly applies a backtracking step until it fails. The step loop is
    /// ported in full; the per-step debug tracking-line-string write is deferred.
    pub fn backtrack_from_tracking_line(
        &mut self,
        tracking_line: &mut TrackedClashedDependencyLine,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut _backtrack_step: Cint64 = 0;
        while self.backtrack_from_tracking_line_step(tracking_line, calc_alg_context) {
            // until backtracking failed
            // KONCLUDE-PORT-NOTE[api]: per-step `writeDebugTrackingLineStringToFile`
            // instrumentation (mBacktrackDebug) deferred.
            _backtrack_step += 1;
        }
        false
    }

    /// Port of `backtrackFromTrackingLineStep`. cpp 6976–7073.
    ///
    /// One backtracking step: (1) drains all deterministic previous-individual-node
    /// level clashes, (2) backtracks non-deterministic previous-level branching
    /// clashes, else (3) backtracks the next-individual-node level branching clash
    /// (non-deterministic or deterministic), else terminates (caching when only
    /// independent clashes remain). Returns whether tracking should continue.
    pub fn backtrack_from_tracking_line_step(
        &mut self,
        tracking_line: &mut TrackedClashedDependencyLine,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut tracking_success = true;
        let mut prev_level_backtracked = false;

        while tracking_line.has_pervious_level_tracked_clashed_descriptors() && tracking_success {
            let tracked_clashed_des =
                tracking_line.take_next_pervious_level_tracked_clashed_descriptor(calc_alg_context);
            tracking_success &= self
                .backtrack_deterministic_clashed_descriptor_from_previous_individual_node_levels(
                    tracked_clashed_des,
                    tracking_line,
                    calc_alg_context,
                );
            prev_level_backtracked = true;
        }
        if prev_level_backtracked
            && tracking_line.has_only_current_individual_node_level_clashes_descriptors()
        {
            self.write_clash_descriptors_to_cache_from_line(tracking_line, calc_alg_context);
        }

        if tracking_line
            .has_pervious_level_tracked_non_deterministic_branching_clashed_descriptors()
        {
            let tracked_clashed_des = tracking_line
                .take_next_pervious_level_tracked_non_deterministic_branching_clashed_descriptor(
                    calc_alg_context,
                );
            tracking_success &= self
                .backtrack_non_deterministic_branching_clashed_descriptor_from_previous_individual_node_level(
                    tracked_clashed_des,
                    tracking_line,
                    calc_alg_context,
                );
        } else if tracking_line.has_level_tracked_branching_clashed_descriptors() {
            let tracked_clashed_des = tracking_line
                .take_next_level_tracked_branching_clashed_descriptor(calc_alg_context);
            if calc_alg_context
                .process_context()
                .clash_desc(tracked_clashed_des)
                .is_pointing_to_non_deterministic_dependency_node()
            {
                tracking_success &= self
                    .backtrack_non_deterministic_branching_clashed_descriptor_from_current_individual_node_level(
                        tracked_clashed_des,
                        tracking_line,
                        calc_alg_context,
                    );
            } else {
                tracking_success &= self
                    .backtrack_deterministic_branching_clashed_descriptor_from_current_individual_node_level(
                        tracked_clashed_des,
                        tracking_line,
                        calc_alg_context,
                    );
            }
        } else {
            if tracking_line.has_only_independent_tracked_clashed_descriptors_remaining() {
                self.write_clash_descriptors_to_cache_from_line(tracking_line, calc_alg_context);
            }
            tracking_success = false;
        }
        tracking_success
    }

    /// Port of `backtrackNonDeterministicBranchingClashedDescriptorFromCurrentIndividualNodeLevel`.
    /// cpp 7075–7077. Pure delegation.
    pub fn backtrack_non_deterministic_branching_clashed_descriptor_from_current_individual_node_level(
        &mut self,
        tracked_clashed_des: ClashDescId,
        tracking_line: &mut TrackedClashedDependencyLine,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        self.backtrack_non_deterministic_branching_clashed_descriptor(
            tracked_clashed_des,
            tracking_line,
            calc_alg_context,
        )
    }

    /// Port of `backtrackNonDeterministicBranchingClashedDescriptorFromPreviousIndividualNodeLevel`.
    /// cpp 7080–7082. Pure delegation.
    pub fn backtrack_non_deterministic_branching_clashed_descriptor_from_previous_individual_node_level(
        &mut self,
        tracked_clashed_des: ClashDescId,
        tracking_line: &mut TrackedClashedDependencyLine,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        self.backtrack_non_deterministic_branching_clashed_descriptor(
            tracked_clashed_des,
            tracking_line,
            calc_alg_context,
        )
    }

    /// Port of `backtrackNonDeterministicBranchingClashedDescriptor`. cpp 7085–7349.
    ///
    /// The non-deterministic backjump: cancels the branch's accumulating task,
    /// collects all clashes processed before the non-deterministic dependency's
    /// processing tag (per individual-node level), installs branch clash
    /// descriptors (allocated from a sent-along memory pool, honouring the
    /// fixed-reuse expansion mode's involved-individual set), updates disjunct
    /// branching statistics, and — when no other branch track points remain open —
    /// collects the filtered clash descriptors of all branches and re-initialises
    /// the tracking line at the closed dependency node (cancelling the root task at
    /// level 0). Returns whether backtracking continues.
    pub fn backtrack_non_deterministic_branching_clashed_descriptor(
        &mut self,
        tracked_clashed_des: ClashDescId,
        tracking_line: &mut TrackedClashedDependencyLine,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let dep_track_point = calc_alg_context
            .process_context()
            .clash_desc(tracked_clashed_des)
            .get_dependency_track_point();
        let non_det_dependency_node = calc_alg_context
            .process_context()
            .track_point(dep_track_point)
            .dependency_node();

        // W6-DEFER[task]: Konclude cancels the branch accumulating task here via
        // `nonDetDepTrackPoint->getBranchNode()->getSatisfiableCalculationTask()`.
        if calc_alg_context
            .process_context()
            .track_point(dep_track_point)
            .is_clashed_or_irelevant_branch()
        {
            // diagnostics: the analysis reached a nondet tp that is ALREADY
            // marked — no new mark, likely followed by a fallback (the tp is
            // stale w.r.t. the current stack).
            self.ddb_already_marked_count += 1;
            if std::env::var_os("KM_BRIDGE_PROGRESS").is_some()
                && self.ddb_already_marked_count <= 4
            {
                let (in_stack, cur, rem) = {
                    let mut in_stack = false;
                    let mut cur = false;
                    let mut rem = false;
                    for bp in &self.or_branch_stack {
                        if bp.alt_track_points.iter().any(|&t| t == dep_track_point) {
                            in_stack = true;
                            cur = bp
                                .alt_track_points
                                .get(bp.next_alt.wrapping_sub(1))
                                .map(|&t| t == dep_track_point)
                                .unwrap_or(false);
                            rem = bp.next_alt < bp.alternatives_len();
                            break;
                        }
                    }
                    (in_stack, cur, rem)
                };
                eprintln!(
                    "DDB-ALREADY-MARKED tp={:?} in_stack={} current_alt={} remaining={}",
                    dep_track_point, in_stack, cur, rem
                );
            }
            return false;
        }

        let proc_tag = calc_alg_context
            .process_context()
            .dep_node(non_det_dependency_node)
            .base()
            .process_tag;
        let mut tracked_clashed_descriptor_before_proc_tag_list = ClashDescId::NONE;
        while tracking_line.has_more_tracked_clashed_list() {
            let tracked_clashed_des_list = tracking_line.take_next_tracked_clashed_list();
            let tracked_clashed_descriptors_before_proc_tag = self
                .get_backtracked_deterministic_clashed_descriptors_before_processing_tag(
                    tracked_clashed_des_list,
                    proc_tag,
                    tracking_line,
                    calc_alg_context,
                );
            tracked_clashed_descriptor_before_proc_tag_list = self.append_tracked_clash_chain(
                tracked_clashed_descriptors_before_proc_tag,
                tracked_clashed_descriptor_before_proc_tag_list,
                calc_alg_context,
            );
        }

        self.write_clash_descriptors_to_cache_with_additional(
            &mut tracked_clashed_descriptor_before_proc_tag_list,
            tracked_clashed_des,
            tracking_line,
            calc_alg_context,
        );

        // W6-DEFER[backend/task]: fixed-reuse expansion-mode involved-individual
        // reporting and memory-pool communication are task/backend-cache substrate.
        let new_involved_indi_linker: Vec<Cint64> = tracking_line
            .get_involved_individual_tracking_set()
            .map(|set| set.iter().copied().collect())
            .unwrap_or_default();

        let branch_mem_con_clashed_des_list = self.create_tracked_clashes_descriptors(
            tracked_clashed_descriptor_before_proc_tag_list,
            calc_alg_context,
            INVALID,
            true,
        );

        if calc_alg_context
            .process_context()
            .track_point(dep_track_point)
            .is_clashed_or_irelevant_branch()
        {
            return false;
        }
        self.ddb_mark_count += 1;
        calc_alg_context
            .process_context_mut()
            .track_point_mut(dep_track_point)
            .set_clashes(branch_mem_con_clashed_des_list, true);
        if !new_involved_indi_linker.is_empty() {
            calc_alg_context
                .process_context_mut()
                .track_point_mut(dep_track_point)
                .set_involved_individual_ids_linker(new_involved_indi_linker);
        }

        // W3/W6-DEFER[statistics/task]: disjunct/disjunction branching statistics
        // and task memory-pool communication stay at the Konclude call points.
        let other_opened_track_points = {
            let proc_ctx = calc_alg_context.process_context();
            let mut other_opened = false;
            let mut track_point_it = proc_ctx
                .dep_node(non_det_dependency_node)
                .branch_track_points();
            while track_point_it.is_some() && !other_opened {
                let track_point = proc_ctx.track_point(track_point_it);
                if track_point_it != dep_track_point
                    && !track_point.is_clashed_or_irelevant_branch()
                {
                    other_opened = true;
                }
                track_point_it = track_point.next;
            }
            other_opened
        };
        if !other_opened_track_points {
            self.relevant_non_deterministic_decision_count += 1;
            let collected_tracked_clashed_des = self
                .get_collected_filtered_clashed_descriptors_from_branch(
                    tracked_clashed_des,
                    non_det_dependency_node,
                    tracking_line,
                    calc_alg_context,
                    INVALID,
                );

            if self.initialize_tracking_line(
                tracking_line,
                collected_tracked_clashed_des,
                calc_alg_context,
            ) {
                if tracking_line.get_branching_level() == 0 {
                    if std::env::var_os("KM_BRIDGE_DUMP_CLASH").is_some()
                        && self.ddb_analysis_dumps < 16
                    {
                        self.ddb_analysis_dumps += 1;
                        let s = self
                            .ht_fmt_tracked_closure(collected_tracked_clashed_des, calc_alg_context);
                        eprintln!("DDB-ROOT-CANCEL[propagated] collected closure: {s}");
                        // per-sibling stored clash sets of the refuted decision
                        // — is the tag-0 degeneration a STORAGE bug (empty /
                        // thin sets) or a semantics bug upstream?
                        let mut tp_it = calc_alg_context
                            .process_context()
                            .dep_node(non_det_dependency_node)
                            .branch_track_points();
                        let mut k = 0;
                        while tp_it.is_some() && k < 8 {
                            let (clashes, marked, tag) = {
                                let t = calc_alg_context.process_context().track_point(tp_it);
                                (t.get_clashes(), t.is_clashed_or_irelevant_branch(), t.process_tag)
                            };
                            let cs = self.ht_fmt_tracked_closure(clashes, calc_alg_context);
                            eprintln!(
                                "  SIBLING[{k}] tp#{} tag={} marked={} stored: {}",
                                tp_it.index(),
                                tag,
                                marked,
                                if cs.is_empty() { "(EMPTY)".into() } else { cs }
                            );
                            // chain-walk the first LATE-tp stored descriptor —
                            // a late tag-0 continue point built from
                            // branch-dependent inputs is the taint lie.
                            let mut d_it = clashes;
                            while d_it.is_some() {
                                let dtp = calc_alg_context
                                    .process_context()
                                    .clash_desc(d_it)
                                    .get_dependency_track_point();
                                if dtp.is_some() && dtp.index() > 10_000 {
                                    eprintln!("  SIBLING[{k}] late-desc chain:");
                                    self.ht_dump_dep_chain_of(dtp, calc_alg_context);
                                    break;
                                }
                                d_it = calc_alg_context
                                    .process_context()
                                    .clash_desc(d_it)
                                    .get_next_descriptor();
                            }
                            tp_it = calc_alg_context.process_context().track_point(tp_it).next;
                            k += 1;
                        }
                    }
                    self.cancellation_root_task(calc_alg_context);
                }
                if tracking_line.has_only_current_individual_node_level_clashes_descriptors() {
                    self.write_clash_descriptors_to_cache_from_line(
                        tracking_line,
                        calc_alg_context,
                    );
                }
                return true;
            }
        } else {
            // C++ keeps this branch as a relevance-marking placeholder:
            // `trackedClashedDescriptorBeforeProcTagList;`
        }
        false
    }

    fn append_tracked_clash_chain(
        &mut self,
        chain: ClashDescId,
        head: ClashDescId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> ClashDescId {
        if chain.is_none() {
            return head;
        }
        let mut tail = chain;
        loop {
            let next = calc_alg_context
                .process_context()
                .clash_desc(tail)
                .get_next_descriptor();
            if next.is_none() {
                break;
            }
            tail = next;
        }
        calc_alg_context
            .process_context_mut()
            .clash_desc_mut(tail)
            .set_next(head);
        chain
    }

    /// Port of `backtrackDeterministicBranchingClashedDescriptorFromCurrentIndividualNodeLevel`.
    /// cpp 7655–7665.
    ///
    /// Backtracks a deterministic branching clash at the current individual-node
    /// level: re-derives the descriptors (tracking the minimum individual level),
    /// frees the consumed descriptor, advances to the next individual-node level
    /// when the minimum dropped below the current one, and sorts the new
    /// descriptors back into the line.
    pub fn backtrack_deterministic_branching_clashed_descriptor_from_current_individual_node_level(
        &mut self,
        tracked_clashed_des: ClashDescId,
        tracking_line: &mut TrackedClashedDependencyLine,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // PORT-PENDING: faithful transcription of cpp 7655–7665:
        //
        //   minIndiLevel = CINT64_MAX;
        //   newList = getBacktrackedDeterministicClashedDescriptors(trackedClashedDes, trackingLine, &minIndiLevel, ctx);  // this unit
        //   trackingLine.addFreeTrackedClashedDescriptor(trackedClashedDes);
        //   if minIndiLevel < trackingLine.getIndividualNodeLevel():
        //     trackingLine.moveToNextIndividualNodeLevel(minIndiLevel);
        //   trackingLine.sortInTrackedClashedDescriptors(newList);
        //   return true;
        //
        let mut min_indi_level = Cint64::MAX;
        let new_list = self.get_backtracked_deterministic_clashed_descriptors(
            tracked_clashed_des,
            tracking_line,
            Some(&mut min_indi_level),
            calc_alg_context,
        );
        tracking_line.add_free_tracked_clashed_descriptor(tracked_clashed_des, calc_alg_context);
        if min_indi_level < tracking_line.get_individual_node_level() {
            tracking_line.move_to_next_individual_node_level(min_indi_level, calc_alg_context);
        }
        tracking_line.sort_in_tracked_clashed_descriptors(new_list, false, calc_alg_context);
        true
    }

    /// Port of `backtrackDeterministicClashedDescriptorFromPreviousIndividualNodeLevels`.
    /// cpp 7669–7674.
    pub fn backtrack_deterministic_clashed_descriptor_from_previous_individual_node_levels(
        &mut self,
        tracked_clashed_des: ClashDescId,
        tracking_line: &mut TrackedClashedDependencyLine,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // PORT-PENDING: faithful transcription of cpp 7669–7674:
        //
        //   newList = getBacktrackedDeterministicClashedDescriptors(trackedClashedDes, trackingLine, nullptr, ctx);  // this unit
        //   trackingLine.addFreeTrackedClashedDescriptor(trackedClashedDes);
        //   trackingLine.sortInTrackedClashedDescriptors(newList);
        //   return true;
        //
        let new_list = self.get_backtracked_deterministic_clashed_descriptors(
            tracked_clashed_des,
            tracking_line,
            None,
            calc_alg_context,
        );
        tracking_line.add_free_tracked_clashed_descriptor(tracked_clashed_des, calc_alg_context);
        tracking_line.sort_in_tracked_clashed_descriptors(new_list, false, calc_alg_context);
        true
    }

    /// Port of `getBacktrackedDeterministicClashedDescriptorsBeforeProcessingTag`.
    /// cpp 7677–7772.
    ///
    /// Splits a tracked-clash list at `processing_tag`: descriptors pointing at a
    /// non-deterministic node or processed at/before the tag are carried forward
    /// directly; descriptors processed after the tag are recursively backtracked
    /// (deduplicated through the tracking line's tracked-clashed-descriptor set);
    /// the no-concept-descriptor non-independent case re-derives and, unless every
    /// derived descriptor stays on the same individual, carries the original
    /// forward. Returns the new before-tag descriptor list.
    pub fn get_backtracked_deterministic_clashed_descriptors_before_processing_tag(
        &mut self,
        mut tracked_clashed_descriptors: ClashDescId,
        processing_tag: Cint64,
        tracking_line: &mut TrackedClashedDependencyLine,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> ClashDescId {
        let mut new_tracked_clashed_descriptor_list = ClashDescId::NONE;

        while tracked_clashed_descriptors.is_some() {
            let tracked_clashed_descriptor = tracked_clashed_descriptors;
            tracked_clashed_descriptors = calc_alg_context
                .process_context()
                .clash_desc(tracked_clashed_descriptor)
                .get_next_descriptor();
            calc_alg_context
                .process_context_mut()
                .clash_desc_mut(tracked_clashed_descriptor)
                .set_next(ClashDescId::NONE);

            if calc_alg_context
                .process_context()
                .clash_desc(tracked_clashed_descriptor)
                .is_pointing_to_non_deterministic_dependency_node()
            {
                assert!(
                    calc_alg_context
                        .process_context()
                        .clash_desc(tracked_clashed_descriptor)
                        .get_processing_tag()
                        <= processing_tag,
                    "non-deterministic dependency is processed after max branching leveled dependency"
                );
                calc_alg_context
                    .process_context_mut()
                    .clash_desc_mut(tracked_clashed_descriptor)
                    .set_next(new_tracked_clashed_descriptor_list);
                new_tracked_clashed_descriptor_list = tracked_clashed_descriptor;
            } else if calc_alg_context
                .process_context()
                .clash_desc(tracked_clashed_descriptor)
                .get_processing_tag()
                > processing_tag
            {
                let mut new_tracked_clashed_descriptor_it = self
                    .get_backtracked_deterministic_clashed_descriptors(
                        tracked_clashed_descriptor,
                        tracking_line,
                        None,
                        calc_alg_context,
                    );
                while new_tracked_clashed_descriptor_it.is_some() {
                    let new_tracked_clashed_descriptor = new_tracked_clashed_descriptor_it;
                    new_tracked_clashed_descriptor_it = calc_alg_context
                        .process_context()
                        .clash_desc(new_tracked_clashed_descriptor)
                        .get_next_descriptor();
                    calc_alg_context
                        .process_context_mut()
                        .clash_desc_mut(new_tracked_clashed_descriptor)
                        .set_next(ClashDescId::NONE);

                    if tracking_line.insert_tracked_clashed_descriptor_hasher(
                        new_tracked_clashed_descriptor,
                        calc_alg_context,
                    ) {
                        calc_alg_context
                            .process_context_mut()
                            .clash_desc_mut(new_tracked_clashed_descriptor)
                            .set_next(tracked_clashed_descriptors);
                        tracked_clashed_descriptors = new_tracked_clashed_descriptor;
                    } else {
                        tracking_line.add_free_tracked_clashed_descriptor(
                            new_tracked_clashed_descriptor,
                            calc_alg_context,
                        );
                    }
                }
                tracking_line.add_free_tracked_clashed_descriptor(
                    tracked_clashed_descriptor,
                    calc_alg_context,
                );
            } else if calc_alg_context
                .process_context()
                .clash_desc(tracked_clashed_descriptor)
                .get_concept_descriptor()
                .is_none()
                && !calc_alg_context
                    .process_context()
                    .clash_desc(tracked_clashed_descriptor)
                    .is_pointing_to_independent_dependency_node()
            {
                let continued_indi_id = calc_alg_context
                    .process_context()
                    .clash_desc(tracked_clashed_descriptor)
                    .get_appropriated_individual_id();
                let new_tracked_clashed_descriptors = self
                    .get_backtracked_deterministic_clashed_descriptors(
                        tracked_clashed_descriptor,
                        tracking_line,
                        None,
                        calc_alg_context,
                    );

                let mut all_indi_id_continued = true;
                let mut new_tracked_clashed_descriptor_it = new_tracked_clashed_descriptors;
                while new_tracked_clashed_descriptor_it.is_some() && all_indi_id_continued {
                    if calc_alg_context
                        .process_context()
                        .clash_desc(new_tracked_clashed_descriptor_it)
                        .get_appropriated_individual_id()
                        != continued_indi_id
                    {
                        all_indi_id_continued = false;
                    }
                    new_tracked_clashed_descriptor_it = calc_alg_context
                        .process_context()
                        .clash_desc(new_tracked_clashed_descriptor_it)
                        .get_next_descriptor();
                }

                if !all_indi_id_continued {
                    calc_alg_context
                        .process_context_mut()
                        .clash_desc_mut(tracked_clashed_descriptor)
                        .set_next(new_tracked_clashed_descriptor_list);
                    new_tracked_clashed_descriptor_list = tracked_clashed_descriptor;

                    new_tracked_clashed_descriptor_it = new_tracked_clashed_descriptors;
                    while new_tracked_clashed_descriptor_it.is_some() {
                        let new_tracked_clashed_descriptor = new_tracked_clashed_descriptor_it;
                        new_tracked_clashed_descriptor_it = calc_alg_context
                            .process_context()
                            .clash_desc(new_tracked_clashed_descriptor)
                            .get_next_descriptor();
                        calc_alg_context
                            .process_context_mut()
                            .clash_desc_mut(new_tracked_clashed_descriptor)
                            .set_next(ClashDescId::NONE);
                        tracking_line.add_free_tracked_clashed_descriptor(
                            new_tracked_clashed_descriptor,
                            calc_alg_context,
                        );
                    }
                } else {
                    new_tracked_clashed_descriptor_it = new_tracked_clashed_descriptors;
                    while new_tracked_clashed_descriptor_it.is_some() {
                        let new_tracked_clashed_descriptor = new_tracked_clashed_descriptor_it;
                        new_tracked_clashed_descriptor_it = calc_alg_context
                            .process_context()
                            .clash_desc(new_tracked_clashed_descriptor)
                            .get_next_descriptor();
                        calc_alg_context
                            .process_context_mut()
                            .clash_desc_mut(new_tracked_clashed_descriptor)
                            .set_next(ClashDescId::NONE);

                        if tracking_line.insert_tracked_clashed_descriptor_hasher(
                            new_tracked_clashed_descriptor,
                            calc_alg_context,
                        ) {
                            calc_alg_context
                                .process_context_mut()
                                .clash_desc_mut(new_tracked_clashed_descriptor)
                                .set_next(tracked_clashed_descriptors);
                            tracked_clashed_descriptors = new_tracked_clashed_descriptor;
                        } else {
                            tracking_line.add_free_tracked_clashed_descriptor(
                                new_tracked_clashed_descriptor,
                                calc_alg_context,
                            );
                        }
                    }
                    tracking_line.add_free_tracked_clashed_descriptor(
                        tracked_clashed_descriptor,
                        calc_alg_context,
                    );
                }
            } else {
                calc_alg_context
                    .process_context_mut()
                    .clash_desc_mut(tracked_clashed_descriptor)
                    .set_next(new_tracked_clashed_descriptor_list);
                new_tracked_clashed_descriptor_list = tracked_clashed_descriptor;
            }
        }

        new_tracked_clashed_descriptor_list
    }

    /// Port of `getBacktrackedDeterministicClashedDescriptors`. cpp 7779–7863.
    ///
    /// Backtracks one deterministic tracked-clash descriptor across its dependency
    /// node's previous track point + every additional dependency: records the
    /// involved individuals, resolves the corresponding (possibly representative-
    /// resolved variable-binding) individual node, tracks the minimum individual
    /// level, and emits one new tracked-clash descriptor per previous track point
    /// (each filtered through `tryGetInvalidSameIndividualNodeLevel*`). Returns the
    /// new descriptor list.
    pub fn get_backtracked_deterministic_clashed_descriptors(
        &mut self,
        tracked_clashed_des: ClashDescId,
        tracking_line: &mut TrackedClashedDependencyLine,
        mut min_indi_level: Option<&mut Cint64>,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> ClashDescId {
        // PORT-PENDING: faithful transcription of cpp 7779–7863:
        //
        //   depNode = trackedClashedDes.getDependencyTrackPoint().getDependencyNode();
        //   conDes  = depNode.getConceptDescriptor();
        //   newList = nullptr;
        //   if minIndiLevel: *minIndiLevel = trackedClashedDes.getAppropriatedIndividualLevel();
        //   if depNode.hasAppropriateIndividualNode():
        //     trackingLine.addInvolvedIndividual(depNode.getAppropriateIndividualNode());
        //     newIndiNode = getCoresspondingIndividualNodeFromDependency(depNode, ctx);   // Unit 28
        //     trackingLine.addInvolvedIndividual(newIndiNode);
        //     if minIndiLevel: *minIndiLevel = min(*minIndiLevel, newIndiNode.getIndividualNominalLevelOrAncestorDepth());
        //   depTrackPoint = depNode.getPreviousDependencyTrackPoint();
        //   varBindPath = trackedClashedDes.getVariableBindingPath();
        //   if depNode.isRepresentativeSelectDependencyNode(): varBindPath = repSelDepNode.getSelectedVariableBindingPath();
        //   else if depNode.isRepresentativeResolveDependencyNode():
        //     resolve varBindPath + depTrackPoint via repVarBindPathMap / repPropMap;
        //   newTrackedClashedDes = getFreeTrackedClashedDescriptor(trackingLine, ctx);    // Unit 30
        //   if newIndiNode: newTrackedClashedDes.initTrackedClashedDescriptor(newIndiNode, conDes, varBindPath, depTrackPoint);
        //   else:           newTrackedClashedDes.initTrackedClashedDescriptor(trackedClashedDes, conDes, varBindPath, depTrackPoint);
        //   newTrackedClashedDes = tryGetInvalidSameIndividualNodeLevelBacktrackedDeterministicClashedDescriptors(newTrackedClashedDes, trackingLine, nullptr, ctx);  // this unit
        //   newList = newTrackedClashedDes.append(newList);
        //   for dependency in depNode.getAdditionalDependencyIterator():
        //     depTrackPoint = dependency.getPreviousDependencyTrackPoint();
        //     addDepNewIndiNode = getCoresspondingIndividualNodeFromDependency(depTrackPoint, ctx);  // Unit 28
        //     trackingLine.addInvolvedIndividual(addDepNewIndiNode);
        //     newTrackedClashedDes = getFreeTrackedClashedDescriptor(trackingLine, ctx);
        //     if !addDepNewIndiNode: newTrackedClashedDes.initTrackedClashedDescriptor(trackedClashedDes, nullptr, varBindPath, depTrackPoint);
        //     else: if minIndiLevel: *minIndiLevel = min(*minIndiLevel, addDepNewIndiNode.getIndividualNominalLevelOrAncestorDepth());
        //           newTrackedClashedDes.initTrackedClashedDescriptor(addDepNewIndiNode, nullptr, varBindPath, depTrackPoint);
        //     newTrackedClashedDes = tryGetInvalidSameIndividualNodeLevelBacktrackedDeterministicClashedDescriptors(newTrackedClashedDes, trackingLine, nullptr, ctx);
        //     newList = newTrackedClashedDes.append(newList);
        //   return newList;
        //
        // Held PORT-PENDING: only the uncommon representative-resolve remapping
        // branch is still gated if its stored maps are absent. The ordinary
        // deterministic previous-track-point and additional-dependency paths are
        // live below.
        let mut new_tracked_clashed_des_list = ClashDescId::NONE;
        if let Some(min_indi_level) = min_indi_level.as_deref_mut() {
            *min_indi_level = calc_alg_context
                .process_context()
                .clash_desc(tracked_clashed_des)
                .get_appropriated_individual_level();
        }

        let dep_track_point = calc_alg_context
            .process_context()
            .clash_desc(tracked_clashed_des)
            .get_dependency_track_point();
        if dep_track_point.is_none() {
            return ClashDescId::NONE;
        }
        let dep_node = calc_alg_context
            .process_context()
            .track_point(dep_track_point)
            .dependency_node();
        if dep_node.is_none() {
            return ClashDescId::NONE;
        }

        let (con_des, has_appropriate, mut var_bind_path, mut prev_dep_track_point) = {
            let dep = calc_alg_context.process_context().dep_node(dep_node);
            (
                dep.concept_descriptor(),
                dep.has_appropriate_individual_node(),
                calc_alg_context
                    .process_context()
                    .clash_desc(tracked_clashed_des)
                    .get_variable_binding_path(),
                dep.previous_dependency_track_point(),
            )
        };

        let mut new_indi_node = NodeId::NONE;
        if has_appropriate {
            let appropriate = calc_alg_context
                .process_context()
                .dep_node(dep_node)
                .individual_node();
            tracking_line.add_involved_individual_node(appropriate, calc_alg_context);
            new_indi_node = self
                .get_coressponding_individual_node_from_dependency_node(dep_node, calc_alg_context);
            tracking_line.add_involved_individual_node(new_indi_node, calc_alg_context);
            if let Some(min_indi_level) = min_indi_level.as_deref_mut() {
                if new_indi_node.is_some() {
                    let new_level = calc_alg_context
                        .process_context()
                        .node(new_indi_node)
                        .individual_nominal_level_or_ancestor_depth();
                    *min_indi_level = (*min_indi_level).min(new_level);
                }
            }
        }

        let (is_rep_select, is_rep_resolve) = {
            let dep = calc_alg_context.process_context().dep_node(dep_node);
            (
                dep.is_representative_select_dependency_node(),
                dep.is_representative_resolve_dependency_node(),
            )
        };
        if is_rep_select {
            var_bind_path = calc_alg_context
                .process_context()
                .dep_node(dep_node)
                .selected_variable_binding_path();
        } else if is_rep_resolve && var_bind_path.is_some() {
            let remap = {
                let proc_ctx = calc_alg_context.process_context();
                let dep = proc_ctx.dep_node(dep_node);
                let prop_id = proc_ctx.vbpath(var_bind_path).get_propagation_id();
                dep.resolve_representative_variable_binding_path_map()
                    .map(|rep_var_bind_path_map| rep_var_bind_path_map.value(prop_id))
                    .and_then(|rep_var_bind_path_map_data| {
                        dep.resolve_representative_propagation_map().map(|rep_prop_map| {
                            (
                                rep_var_bind_path_map_data.get_resolve_variable_binding_path(),
                                rep_prop_map
                                    .value(
                                        rep_var_bind_path_map_data
                                            .get_resolve_representative_variable_binding_path_set_data_id(),
                                    )
                                    .get_representative_propagation_descriptor(),
                            )
                        })
                    })
            };
            if let Some((resolved_var_bind_path, rep_prop_des)) = remap {
                var_bind_path = resolved_var_bind_path;
                if rep_prop_des.is_some() {
                    prev_dep_track_point = calc_alg_context
                        .process_context()
                        .rep_prop_des(rep_prop_des)
                        .get_dependency_track_point();
                }
            }
        }

        let mut new_tracked_clashed_des =
            self.get_free_tracked_clashed_descriptor(tracking_line, calc_alg_context);
        let init_indi = if new_indi_node.is_some() {
            new_indi_node
        } else {
            calc_alg_context
                .process_context()
                .clash_desc(tracked_clashed_des)
                .get_appropriated_individual()
        };
        self.init_backtracked_tracked_clashed_descriptor(
            new_tracked_clashed_des,
            init_indi,
            con_des,
            var_bind_path,
            prev_dep_track_point,
            calc_alg_context,
        );
        new_tracked_clashed_des = self
            .try_get_invalid_same_individual_node_level_backtracked_deterministic_clashed_descriptors(
                new_tracked_clashed_des,
                tracking_line,
                None,
                calc_alg_context,
            );
        new_tracked_clashed_des_list = self.append_tracked_clash_chain(
            new_tracked_clashed_des,
            new_tracked_clashed_des_list,
            calc_alg_context,
        );

        let mut dep_it = calc_alg_context
            .process_context()
            .dep_node(dep_node)
            .additional_after_dependencies();
        while dep_it.is_some() {
            let add_dep_track_point = calc_alg_context
                .process_context()
                .dep_link(dep_it)
                .previous_dependency_track_point();
            let add_dep_new_indi_node = if add_dep_track_point.is_some() {
                self.get_coressponding_individual_node_from_dependency(
                    add_dep_track_point,
                    calc_alg_context,
                )
            } else {
                NodeId::NONE
            };
            tracking_line.add_involved_individual_node(add_dep_new_indi_node, calc_alg_context);

            let mut new_tracked_clashed_des =
                self.get_free_tracked_clashed_descriptor(tracking_line, calc_alg_context);
            if add_dep_new_indi_node.is_some() {
                if let Some(min_indi_level) = min_indi_level.as_deref_mut() {
                    let new_level = calc_alg_context
                        .process_context()
                        .node(add_dep_new_indi_node)
                        .individual_nominal_level_or_ancestor_depth();
                    *min_indi_level = (*min_indi_level).min(new_level);
                }
                self.init_backtracked_tracked_clashed_descriptor(
                    new_tracked_clashed_des,
                    add_dep_new_indi_node,
                    ConDescId::NONE,
                    var_bind_path,
                    add_dep_track_point,
                    calc_alg_context,
                );
            } else {
                let init_indi = calc_alg_context
                    .process_context()
                    .clash_desc(tracked_clashed_des)
                    .get_appropriated_individual();
                self.init_backtracked_tracked_clashed_descriptor(
                    new_tracked_clashed_des,
                    init_indi,
                    ConDescId::NONE,
                    var_bind_path,
                    add_dep_track_point,
                    calc_alg_context,
                );
            }
            new_tracked_clashed_des = self
                .try_get_invalid_same_individual_node_level_backtracked_deterministic_clashed_descriptors(
                    new_tracked_clashed_des,
                    tracking_line,
                    None,
                    calc_alg_context,
                );
            new_tracked_clashed_des_list = self.append_tracked_clash_chain(
                new_tracked_clashed_des,
                new_tracked_clashed_des_list,
                calc_alg_context,
            );

            dep_it = calc_alg_context
                .process_context()
                .dep_link(dep_it)
                .next_additional_dependency();
        }

        new_tracked_clashed_des_list
    }

    /// Port of `tryGetInvalidSameIndividualNodeLevelBacktrackedDeterministicClashedDescriptors`.
    /// cpp 7866–7896.
    ///
    /// If a no-concept deterministic non-independent descriptor's dependency node
    /// (or any of its additional dependencies) resolves an individual on a
    /// different nominal/ancestor level than the descriptor's current level, the
    /// descriptor is returned unchanged; otherwise it is further backtracked. A
    /// descriptor that does not match the precondition is returned as-is.
    pub fn try_get_invalid_same_individual_node_level_backtracked_deterministic_clashed_descriptors(
        &mut self,
        tracked_clashed_des: ClashDescId,
        tracking_line: &mut TrackedClashedDependencyLine,
        mut min_indi_level: Option<&mut Cint64>,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> ClashDescId {
        // PORT-PENDING: faithful transcription of cpp 7866–7896:
        //
        //   if trackedClashedDes.getConceptDescriptor() == nullptr
        //      && trackedClashedDes.isPointingToDeterministicDependencyNode()
        //      && !trackedClashedDes.isPointingToIndependentDependencyNode():
        //     depNode = trackedClashedDes.getDependencyTrackPoint().getDependencyNode();
        //     currLevel = trackedClashedDes.getAppropriatedIndividualLevel();
        //     if minIndiLevel: *minIndiLevel = trackedClashedDes.getAppropriatedIndividualLevel();
        //     if depNode.hasAppropriateIndividualNode():
        //       indiNode = getCoresspondingIndividualNodeFromDependency(depNode, ctx);   // Unit 28
        //       if indiNode.getIndividualNominalLevelOrAncestorDepth() != currLevel: return trackedClashedDes;
        //     for dependency in depNode.getAdditionalDependencyIterator():
        //       addDepNewIndiNode = getCoresspondingIndividualNodeFromDependency(dependency.getPreviousDependencyTrackPoint(), ctx);
        //       trackingLine.addInvolvedIndividual(addDepNewIndiNode);
        //       if addDepNewIndiNode && addDepNewIndiNode.getIndividualNominalLevelOrAncestorDepth() != currLevel: return trackedClashedDes;
        //     return getBacktrackedDeterministicClashedDescriptors(trackedClashedDes, trackingLine, minIndiLevel, ctx);  // this unit
        //   return trackedClashedDes;
        //
        let should_backtrack = {
            let tracked = calc_alg_context
                .process_context()
                .clash_desc(tracked_clashed_des);
            tracked.get_concept_descriptor().is_none()
                && tracked.is_pointing_to_deterministic_dependency_node()
                && !tracked.is_pointing_to_independent_dependency_node()
        };
        if should_backtrack {
            let dep_track_point = calc_alg_context
                .process_context()
                .clash_desc(tracked_clashed_des)
                .get_dependency_track_point();
            if dep_track_point.is_none() {
                return tracked_clashed_des;
            }
            let dep_node = calc_alg_context
                .process_context()
                .track_point(dep_track_point)
                .dependency_node();
            if dep_node.is_none() {
                return tracked_clashed_des;
            }
            let curr_level = calc_alg_context
                .process_context()
                .clash_desc(tracked_clashed_des)
                .get_appropriated_individual_level();
            if let Some(min_indi_level) = min_indi_level.as_deref_mut() {
                *min_indi_level = curr_level;
            }
            if calc_alg_context
                .process_context()
                .dep_node(dep_node)
                .has_appropriate_individual_node()
            {
                let indi_node = self.get_coressponding_individual_node_from_dependency_node(
                    dep_node,
                    calc_alg_context,
                );
                if indi_node.is_some()
                    && calc_alg_context
                        .process_context()
                        .node(indi_node)
                        .individual_nominal_level_or_ancestor_depth()
                        != curr_level
                {
                    return tracked_clashed_des;
                }
            }

            let mut dep_it = calc_alg_context
                .process_context()
                .dep_node(dep_node)
                .additional_after_dependencies();
            while dep_it.is_some() {
                let add_dep_track_point = calc_alg_context
                    .process_context()
                    .dep_link(dep_it)
                    .previous_dependency_track_point();
                let add_dep_new_indi_node = if add_dep_track_point.is_some() {
                    self.get_coressponding_individual_node_from_dependency(
                        add_dep_track_point,
                        calc_alg_context,
                    )
                } else {
                    NodeId::NONE
                };
                tracking_line.add_involved_individual_node(add_dep_new_indi_node, calc_alg_context);
                if add_dep_new_indi_node.is_some()
                    && calc_alg_context
                        .process_context()
                        .node(add_dep_new_indi_node)
                        .individual_nominal_level_or_ancestor_depth()
                        != curr_level
                {
                    return tracked_clashed_des;
                }
                dep_it = calc_alg_context
                    .process_context()
                    .dep_link(dep_it)
                    .next_additional_dependency();
            }
            return self.get_backtracked_deterministic_clashed_descriptors(
                tracked_clashed_des,
                tracking_line,
                min_indi_level,
                calc_alg_context,
            );
        }
        tracked_clashed_des
    }

    fn init_backtracked_tracked_clashed_descriptor(
        &mut self,
        tracked_clashed_des: ClashDescId,
        individual_node: NodeId,
        concept_descriptor: ConDescId,
        var_bind_path: VarBindingPathId,
        dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let mut individual_node_id = INVALID;
        let mut individual_node_level = INVALID;
        let mut nominal_individual = false;
        let mut error = false;
        if individual_node.is_some() {
            let node = calc_alg_context.process_context().node(individual_node);
            individual_node_id = node.individual_node_id();
            individual_node_level = node.individual_nominal_level_or_ancestor_depth();
            nominal_individual = node.is_nominal_individual_node();
        } else {
            error = true;
        }

        let mut deterministic = false;
        let mut independent = false;
        let mut processing_tag = INVALID;
        let mut branching_level_tag = INVALID;
        if dep_track_point.is_some() {
            let track_point = calc_alg_context
                .process_context()
                .track_point(dep_track_point);
            branching_level_tag = track_point.get_branching_tag();
            let dep_node = track_point.dependency_node();
            if dep_node.is_some() {
                let dep_node = calc_alg_context.process_context().dep_node(dep_node);
                processing_tag = dep_node.base().process_tag;
                deterministic = dep_node.is_deterministic();
                independent = dep_node.is_independent_base_dependency_type();
            } else {
                error = true;
            }
            if branching_level_tag <= -1 {
                error = true;
            }
        } else {
            error = true;
        }

        calc_alg_context
            .process_context_mut()
            .clash_desc_mut(tracked_clashed_des)
            .init_tracked_clashed_descriptor(
                individual_node,
                individual_node_id,
                individual_node_level,
                nominal_individual,
                concept_descriptor,
                var_bind_path,
                dep_track_point,
                deterministic,
                independent,
                processing_tag,
                branching_level_tag,
                error,
            );
    }
}
