//! `completion::u28` — Dependency tracking family, batch (port unit #28 of 36).
//!
//! Faithful port of the 54 methods the manifest (`01-completion-methods.md`,
//! "Unit 28") groups under dependency tracking of Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`.
//! cpp source line ranges (1-based) are noted on each item.
//!
//! Methods (cpp order):
//!   * `areAllDependentFactsUnchanged`                              [2873–2932]
//!   * `trackIndividualReferredDependence`                         [3871–3873]
//!   * `trackIndividualExtendedDependence`                         [3876–3878]
//!   * `trackIndividualDependence`                                 [3880–3945]
//!   * `isConceptFromPredecessorDependent`                         [4032–4046]
//!   * `isConceptFromDirectOrPredecessorOrNondeterminismusDependent` [6112–6140]
//!   * `getConceptDependenciesToSameIndividualNode`                [6144–6247]
//!   * `writeDebugTrackingLineStringToFile`                        [6723–6739]
//!   * `generateDebugTrackingLineString`                           [6744–6770]
//!   * `markDependencyRelevance`                                   [7360–7388]
//!   * `initializeTrackingLine`                                    [7900–7917]
//!   * `getCoresspondingIndividualNodeFromDependency` (track point)[7975–7978]
//!   * `getCoresspondingIndividualNodeFromDependency` (dep node)   [7981–7995]
//!   * `generateDebugDependencyString`                            [8175–8298]
//!   * the 40 `create*Dependency` factory wrappers                 [9755–10121]
//!
//! KONCLUDE-PORT-NOTE[ownership]: each method is a member of
//! `CCalculationTableauCompletionTaskHandleAlgorithm`, so it becomes `&mut self`
//! plus the threaded per-thread context `calc_alg_context: &mut
//! CalculationAlgorithmContextBase`. C++ `CIndividualProcessNode*&` (in/out
//! pointer-reference) becomes `&mut NodeId`; a plain `CIndividualProcessNode*`
//! value parameter becomes `NodeId`; `CConceptDescriptor*` → `ConDescId`;
//! `CDependencyTrackPoint*` → `TrackPointId` (an out `CDependencyTrackPoint*&` →
//! `&mut TrackPointId`); `CDependency*` (additional-dependency back-edge) →
//! `DepLinkId`; the returned `C*DependencyNode*` (all of the tagged
//! `DependencyNode` enum) → `DependencyId`; `CRole*`/`CIndividual*` → `RoleId`/
//! `IndividualId`. The per-test arenas are reached through the context
//! (`calc_alg_context.process_context()` / `_mut()`), the databox as
//! `calc_alg_context.processing_data_box{,_mut}()`.
//!
//! KONCLUDE-PORT-NOTE[api]: the variable-binding-path types Konclude threads
//! through some representative-dependency factories (`CVariableBindingPath*`,
//! `CRepresentativeVariableBindingPathMap*`, `CRepresentativePropagationMap*`) are
//! the not-yet-ported representative/answering subsystem; they appear as opaque
//! `Cint64` handles. The Unit 30 tracked-clash descriptor and tracking-line
//! records now have concrete Rust substrate used by `initializeTrackingLine`.
//!
//! Deferral landscape. Three subsystems gate most of this unit:
//!   * the `CDependencyFactory` (`calc_alg_context...used_dep_factory`, a zero-size
//!     `Id` stub) — every `create*Dependency` wrapper bottoms out in one
//!     `factory->create*Dependency` call; the `mConfBuildDependencies` guard + null
//!     return are ported in full, the factory dispatch is `W6-DEFER[api]`;
//!   * the per-task individual-dependence tracking adapter/observer/marker +
//!     referred-individual tracking vector (Task layer, `W6-DEFER[api]`) that
//!     `trackIndividualDependence` installs;
//!   * the Qt debug-string helpers (`generateDebug*`,
//!     `writeDebugTrackingLineStringToFile`) — `W3-DEFER`.
//!
//! Fully ported (substrate-resolvable): the two `trackIndividual*Dependence`
//! forwarders, `isConceptFromPredecessorDependent`,
//! `isConceptFromDirectOrPredecessorOrNondeterminismusDependent`, the recursive
//! spine of `markDependencyRelevance`, both
//! `getCoresspondingIndividualNodeFromDependency` overloads, and the
//! `mConfBuildDependencies` decision structure of all 40 `create*` wrappers.

#![allow(dead_code)]
#![allow(unused_variables)]

use std::collections::{HashSet, VecDeque};

use super::super::model::substrate::{Cint64, Id};
use super::super::model::{IndividualId, RoleId};
use super::super::process::dependency::{DepKind, DependencyNode};
use super::super::process::referred_tracking::ReferredIndividualTrackingVector;
use super::super::process::representative::RepresentativePropagationMap;
use super::super::process::varbind::{RepresentativeVariableBindingPathMap, VarBindingPathId};
use super::super::process::{
    ClashDescId, ConDescId, DepLinkId, DependencyId, NodeId, TrackPointId,
};
use super::context::CalculationAlgorithmContextBase;
use super::u30::TrackedClashedDependencyLine;

/// KONCLUDE-PORT-NOTE[api]: `CIndividualProcessNodeVector*` is kept in the
/// signature for source alignment. Konclude carries it through recursive calls,
/// but this helper reads the current graph through
/// `ctx->getUsedProcessingDataBox()->getIndividualProcessNodeVector()`.
type IndiNodeVec = Cint64;
/// KONCLUDE-PORT-NOTE[api]: debug-only tracking-line helpers still carry opaque
/// handles until their string-building call sites use the Unit 30 stack record.
type TrackingLine = Cint64;

impl super::algorithm::CompletionTaskHandleAlgorithm {
    // =======================================================================
    // areAllDependentFactsUnchanged (cpp 2873–2932). PORT-PENDING.
    // =======================================================================

    /// Port of `areAllDependentFactsUnchanged`. cpp 2873–2932.
    ///
    /// Recursively walks a dependency track point's node + additional-dependency
    /// chain, bounded by `rem_backtrack_count`, to decide whether every fact the
    /// backtracked individual node depends on is unchanged in the current (locally
    /// re-derived) completion graph: it fails on any blockable associated node, any
    /// node now present in the live individual-node vector, more than one role-/
    /// some-existential additional dependency, and bottoms out `true` only at the
    /// independent base reached from the backtracked (non-self) individual node.
    pub fn are_all_dependent_facts_unchanged(
        &mut self,
        individual_node: NodeId,
        backtracked_individual_node: NodeId,
        prev_con_dep_track_point: TrackPointId,
        prev_indi_node_vec: IndiNodeVec,
        rem_backtrack_count: &mut Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        *rem_backtrack_count -= 1;
        if *rem_backtrack_count < 0 {
            return false;
        }
        if prev_con_dep_track_point.is_none() {
            return false;
        }

        let dep_node = calc_alg_context
            .process_context()
            .track_point(prev_con_dep_track_point)
            .dependency_node();
        if dep_node.is_none() {
            return false;
        }

        let assoc_indi_node = calc_alg_context
            .process_context()
            .dep_node(dep_node)
            .individual_node();
        if assoc_indi_node.is_some() {
            if calc_alg_context
                .process_context()
                .node(assoc_indi_node)
                .is_blockable_individual()
            {
                return false;
            }
            let assoc_indi_id = calc_alg_context
                .process_context()
                .node(assoc_indi_node)
                .individual_node_id();
            if calc_alg_context
                .processing_data_box()
                .individual_process_node_vector()
                .get_data(assoc_indi_id)
                .is_some()
            {
                return false;
            }
        }

        let mut add_role_exist_dep = false;
        let mut add_dep_it = calc_alg_context
            .process_context()
            .dep_node(dep_node)
            .additional_after_dependencies();
        while add_dep_it.is_some() {
            let prev_add_dep_track_point = calc_alg_context
                .process_context()
                .dep_link(add_dep_it)
                .previous_dependency_track_point();
            let prev_add_dep_node = if prev_add_dep_track_point.is_some() {
                calc_alg_context
                    .process_context()
                    .track_point(prev_add_dep_track_point)
                    .dependency_node()
            } else {
                Id::NONE
            };

            if prev_add_dep_node.is_some()
                && calc_alg_context
                    .process_context()
                    .dep_node(prev_add_dep_node)
                    .kind()
                    == DepKind::RoleAssertion
            {
                if add_role_exist_dep {
                    return false;
                }
                add_role_exist_dep = true;
            } else if prev_add_dep_node.is_some()
                && calc_alg_context
                    .process_context()
                    .dep_node(prev_add_dep_node)
                    .kind()
                    == DepKind::Some
            {
                if add_role_exist_dep {
                    return false;
                }
                let add_assoc_indi_node = calc_alg_context
                    .process_context()
                    .dep_node(prev_add_dep_node)
                    .individual_node();
                if add_assoc_indi_node.is_some()
                    && calc_alg_context
                        .process_context()
                        .node(add_assoc_indi_node)
                        .is_blockable_individual()
                {
                    return false;
                }
                let next_backtracked = if add_assoc_indi_node.is_some() {
                    add_assoc_indi_node
                } else {
                    backtracked_individual_node
                };
                if !self.are_all_dependent_facts_unchanged(
                    individual_node,
                    next_backtracked,
                    prev_add_dep_track_point,
                    prev_indi_node_vec,
                    rem_backtrack_count,
                    calc_alg_context,
                ) {
                    return false;
                }
                add_role_exist_dep = true;
            } else if prev_add_dep_track_point.is_some() {
                let next_backtracked = if assoc_indi_node.is_some() {
                    assoc_indi_node
                } else {
                    backtracked_individual_node
                };
                if !self.are_all_dependent_facts_unchanged(
                    individual_node,
                    next_backtracked,
                    prev_add_dep_track_point,
                    prev_indi_node_vec,
                    rem_backtrack_count,
                    calc_alg_context,
                ) {
                    return false;
                }
            }

            add_dep_it = calc_alg_context
                .process_context()
                .dep_link(add_dep_it)
                .next_additional_dependency();
        }

        if calc_alg_context.process_context().dep_node(dep_node).kind() != DepKind::IndependentBase
        {
            let prev_dep_track_point = calc_alg_context
                .process_context()
                .dep_node(dep_node)
                .previous_dependency_track_point();
            if prev_dep_track_point.is_some() {
                let next_backtracked = if assoc_indi_node.is_some() {
                    assoc_indi_node
                } else {
                    backtracked_individual_node
                };
                if !self.are_all_dependent_facts_unchanged(
                    individual_node,
                    next_backtracked,
                    prev_dep_track_point,
                    prev_indi_node_vec,
                    rem_backtrack_count,
                    calc_alg_context,
                ) {
                    return false;
                }
                return true;
            }
        } else if backtracked_individual_node.is_some()
            && backtracked_individual_node != individual_node
        {
            return true;
        }
        false
    }

    // =======================================================================
    // Individual-dependence tracking (cpp 3871–3945).
    // =======================================================================

    /// Port of `trackIndividualReferredDependence`. cpp 3871–3873. Pure delegation.
    pub fn track_individual_referred_dependence(
        &mut self,
        indi_id: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        self.track_individual_dependence(indi_id, true, false, calc_alg_context)
    }

    /// Port of `trackIndividualExtendedDependence`. cpp 3876–3878. Pure delegation.
    pub fn track_individual_extended_dependence(
        &mut self,
        indi_id: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        self.track_individual_dependence(indi_id, false, true, calc_alg_context)
    }

    /// Port of `trackIndividualDependence`. cpp 3880–3945. PORT-PENDING.
    ///
    /// When the databox requires individual-dependence tracking, lazily installs a
    /// `CReferredIndividualTrackingVector` (sized from the ABox individual count and
    /// the cached deterministic-task node-vector size) on the satisfiable task's
    /// dependence-tracking observer, then marks the given (negated-id) individual as
    /// referred or referred-and-extended.
    pub fn track_individual_dependence(
        &mut self,
        indi_id: Cint64,
        indi_referred: bool,
        indi_extended: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // Faithful transcription of cpp 3880–3945:
        //
        //   if ctx.getUsedProcessingDataBox().isIndividualDependenceTrackingRequired():
        //     indiTrackVec = ctx.getUsedProcessingDataBox().getReferredIndividualTrackingVector();
        //     if !indiTrackVec:
        //       satCalcTask = ctx.getSatisfiableCalculationTask();
        //       indiDepTrackAdapter = satCalcTask.getSatisfiableTaskIndividualDependenceTrackingAdapter();
        //       if indiDepTrackAdapter:
        //         marker = indiDepTrackAdapter.getIndividualDependenceTrackingMarker();
        //         if marker: marker.setIndividualDependenceTracked();
        //         observer = indiDepTrackAdapter.getIndividualDependenceTrackingObserver();
        //         if observer:
        //           extendingIndiDepTrack = observer.getExtendingIndividualDependenceTracking();
        //           extendingRefIndiTrackVec = dynamic_cast<CReferredIndividualTrackingVector*>(extendingIndiDepTrack);
        //           if !extendingRefIndiTrackVec:
        //             aboxIndiCount = ctx.getProcessingDataBox().getOntology().getABox().getIndividualCount();
        //             trackIndiCount = aboxIndiCount;
        //             consData = ...getConsistence().getConsistenceModelData();
        //             if consData (CConsistenceTaskData):
        //               cachedSatTask = consTaskData.getDeterministicSatisfiableTask();
        //               if cachedSatTask: trackIndiCount = max(trackIndiCount,
        //                   cachedSatTask.getProcessingDataBox().getIndividualProcessNodeVector().getItemCount());
        //             extendingRefIndiTrackVec = new CReferredIndividualTrackingVector();
        //             extendingRefIndiTrackVec.initReferredIndividualTrackingVector(trackIndiCount, aboxIndiCount);
        //             indiTrackVec = observer.installIndividualDependenceTracking(extendingRefIndiTrackVec);
        //           else: indiTrackVec = extendingRefIndiTrackVec;
        //           satCalcTask.getProcessingDataBox().setReferredIndividualTrackingVector(indiTrackVec);
        //     if indiTrackVec:
        //       if indiExtended: indiTrackVec.setIndividualReferredAndExtended(-indiID);
        //       elif indiReferred: indiTrackVec.setIndividualReferred(-indiID);
        //       return true;
        //   return false;
        //
        if !calc_alg_context
            .processing_data_box()
            .is_individual_dependence_tracking_required()
        {
            return false;
        }

        let indi_track_vec = calc_alg_context
            .processing_data_box()
            .referred_individual_tracking_vector();
        let mut indi_track_vec = indi_track_vec;
        if indi_track_vec.is_none() {
            let sat_calc_task = calc_alg_context.base.used_sat_calc_task;
            let indi_dep_track_adapter = calc_alg_context
                .base
                .satisfiable_task_individual_dependence_tracking_adapter(sat_calc_task);
            if indi_dep_track_adapter.is_some() {
                let marker = calc_alg_context
                    .base
                    .individual_dependence_tracking_adapter(indi_dep_track_adapter)
                    .get_individual_dependence_tracking_marker();
                if marker.is_some() {
                    calc_alg_context
                        .base
                        .individual_dependence_tracking_marker_mut(marker)
                        .set_individual_dependence_tracked();
                }
                let observer = calc_alg_context
                    .base
                    .individual_dependence_tracking_adapter(indi_dep_track_adapter)
                    .get_individual_dependence_tracking_observer();
                if observer.is_some() {
                    let extending_indi_dep_track = calc_alg_context
                        .base
                        .individual_dependence_tracking_collector(observer)
                        .get_extending_individual_dependence_tracking();
                    if extending_indi_dep_track.is_none() {
                        let abox_indi_count =
                            calc_alg_context.base.ontology_arenas().individual_count();
                        let mut track_indi_count = abox_indi_count;
                        let cons_data = calc_alg_context
                            .processing_data_box()
                            .consistence_model_data();
                        if cons_data.is_some() {
                            let cached_sat_task = calc_alg_context
                                .base
                                .task_data(cons_data)
                                .get_deterministic_satisfiable_task();
                            if cached_sat_task.is_some() {
                                if let Some(cached_task) =
                                    calc_alg_context.base.try_sat_calc_task(cached_sat_task)
                                {
                                    if let Some(cached_data_box) =
                                        cached_task.processing_data_box_state()
                                    {
                                        track_indi_count = track_indi_count.max(
                                            cached_data_box
                                                .individual_process_node_vector()
                                                .get_item_count(),
                                        );
                                    }
                                }
                            }
                        }

                        let extending_ref_indi_track_vec = calc_alg_context
                            .process_context_mut()
                            .alloc_referred_individual_tracking_vector({
                                let mut vec = ReferredIndividualTrackingVector::new();
                                vec.init_referred_individual_tracking_vector(
                                    track_indi_count,
                                    abox_indi_count,
                                );
                                vec
                            });
                        indi_track_vec = calc_alg_context
                            .base
                            .individual_dependence_tracking_collector_mut(observer)
                            .install_individual_dependence_tracking(extending_ref_indi_track_vec);
                    } else {
                        indi_track_vec = extending_indi_dep_track;
                    }
                    calc_alg_context
                        .processing_data_box_mut()
                        .set_referred_individual_tracking_vector(indi_track_vec);
                }
            }
        }

        if indi_track_vec.is_none() {
            return false;
        }

        if indi_extended {
            calc_alg_context
                .process_context_mut()
                .referred_individual_tracking_vector_mut(indi_track_vec)
                .set_individual_referred_and_extended(-indi_id);
        } else if indi_referred {
            calc_alg_context
                .process_context_mut()
                .referred_individual_tracking_vector_mut(indi_track_vec)
                .set_individual_referred(-indi_id);
        }
        true
    }

    // =======================================================================
    // Predecessor / direct-or-nondeterminism dependence predicates
    // (cpp 4032–4046, 6112–6140). Fully ported.
    // =======================================================================

    /// Port of `isConceptFromPredecessorDependent`. cpp 4032–4046.
    ///
    /// True if the concept's dependency points to the independent base or to an
    /// appropriate individual node strictly shallower (an ancestor) than
    /// `individual_node`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: `CDependencyTrackPoint::isPointingTo*` need a
    /// `&Arena<DependencyNode>` the `ProcessContext` does not expose as a whole; the
    /// equivalent dep-node deref (`is_independent_base_dependency_type`) is inlined
    /// through the context accessors — behaviour is identical.
    pub fn is_concept_from_predecessor_dependent(
        &mut self,
        individual_node: &mut NodeId,
        con_des: ConDescId,
        dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let anc_depth = calc_alg_context
            .process_context()
            .node(*individual_node)
            .individual_ancestor_depth();
        let mut dependency_to_ancestor = false;
        let dep_node = calc_alg_context
            .process_context()
            .track_point(dep_track_point)
            .dependency_node();
        if calc_alg_context
            .process_context()
            .dep_node(dep_node)
            .is_independent_base_dependency_type()
        {
            dependency_to_ancestor = true;
        } else if calc_alg_context
            .process_context()
            .dep_node(dep_node)
            .has_appropriate_individual_node()
        {
            let app_indi_node = calc_alg_context
                .process_context()
                .dep_node(dep_node)
                .individual_node();
            let app_indi_anc_depth = calc_alg_context
                .process_context()
                .node(app_indi_node)
                .individual_ancestor_depth();
            if app_indi_anc_depth < anc_depth {
                dependency_to_ancestor = true;
            }
        }
        dependency_to_ancestor
    }

    /// Port of `isConceptFromDirectOrPredecessorOrNondeterminismusDependent`.
    /// cpp 6112–6140.
    ///
    /// Like `isConceptFromPredecessorDependent` but additionally true for any
    /// non-deterministic dependency and for a merged-concept dependency, and — at
    /// equal ancestor depth — true exactly when the dependency has no additional
    /// dependencies (setting `*direct_dependent_flag` when it was already set).
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: `isPointingTo{Deterministic,Independent}` are
    /// inlined as dep-node derefs through the context (see
    /// `is_concept_from_predecessor_dependent`).
    pub fn is_concept_from_direct_or_predecessor_or_nondeterminismus_dependent(
        &mut self,
        individual_node: &mut NodeId,
        con_des: ConDescId,
        dep_track_point: TrackPointId,
        direct_dependent_flag: &mut bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let anc_depth = calc_alg_context
            .process_context()
            .node(*individual_node)
            .individual_ancestor_depth();
        let mut dependency_to_ancestor = false;
        let dep_node = calc_alg_context
            .process_context()
            .track_point(dep_track_point)
            .dependency_node();
        // !isPointingToDeterministicDependencyNode() == the dep node is non-deterministic.
        if !calc_alg_context
            .process_context()
            .dep_node(dep_node)
            .is_deterministic()
        {
            dependency_to_ancestor = true;
        } else if calc_alg_context
            .process_context()
            .dep_node(dep_node)
            .is_independent_base_dependency_type()
        {
            dependency_to_ancestor = true;
        } else if calc_alg_context
            .process_context()
            .dep_node(dep_node)
            .has_appropriate_individual_node()
        {
            let app_indi_node = calc_alg_context
                .process_context()
                .dep_node(dep_node)
                .individual_node();
            let app_indi_anc_depth = calc_alg_context
                .process_context()
                .node(app_indi_node)
                .individual_ancestor_depth();
            if app_indi_anc_depth < anc_depth {
                dependency_to_ancestor = true;
            } else if
            /* mConfDirectRulePreprocessing && */
            app_indi_anc_depth == anc_depth {
                dependency_to_ancestor = !calc_alg_context
                    .process_context()
                    .dep_node(dep_node)
                    .has_additional_dependencies();
                if *direct_dependent_flag {
                    *direct_dependent_flag = true;
                }
            }
        } else {
            let dep_type = calc_alg_context.process_context().dep_node(dep_node).kind();
            if dep_type == DepKind::MergedConcept {
                dependency_to_ancestor = true;
            }
        }
        dependency_to_ancestor
    }

    // =======================================================================
    // getConceptDependenciesToSameIndividualNode (cpp 6144–6247).
    // =======================================================================

    /// Port of `getConceptDependenciesToSameIndividualNode`. cpp 6144–6247.
    ///
    /// Collects the concept descriptors of every dependency staying on the same
    /// individual-node ancestor depth as `individual_node`. The simple case (the
    /// dependency's appropriate node is at the base depth, the track point is
    /// dependent and either has a concept descriptor or no additional dependencies)
    /// just prepends that one concept descriptor; otherwise a depth-bounded
    /// breadth-first walk over the previous + additional dependencies collects each
    /// same-depth concept descriptor, failing (returning `false`) on any
    /// non-deterministic, shallower, or independent dependency.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: the C++ out parameter
    /// `CXLinker<CConceptDescriptor*>*& depLinker` (a head-front prepend chain) maps
    /// to `&mut Vec<ConDescId>` with the head at the FRONT (the canonical linker
    /// convention, `PORT.md` W2 Wave-B).
    pub fn get_concept_dependencies_to_same_individual_node(
        &mut self,
        individual_node: &mut NodeId,
        con_des: ConDescId,
        dep_track_point: TrackPointId,
        dep_linker: &mut Vec<ConDescId>,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let _ = con_des;
        if dep_track_point.is_none() {
            return false;
        }

        let dep_node = calc_alg_context
            .process_context()
            .track_point(dep_track_point)
            .dependency_node();
        if dep_node.is_none() {
            return false;
        }

        let dependend_con_des = calc_alg_context
            .process_context()
            .dep_node(dep_node)
            .concept_descriptor();
        let base_depth = calc_alg_context
            .process_context()
            .node(*individual_node)
            .individual_ancestor_depth();

        let mut simple_same_node_deps = false;
        if calc_alg_context
            .process_context()
            .dep_node(dep_node)
            .has_appropriate_individual_node()
        {
            let app_indi_node = calc_alg_context
                .process_context()
                .dep_node(dep_node)
                .individual_node();
            let app_indi_depth = calc_alg_context
                .process_context()
                .node(app_indi_node)
                .individual_ancestor_depth();
            if app_indi_depth == base_depth {
                simple_same_node_deps = true;
            }
        } else {
            simple_same_node_deps = true;
        }

        if simple_same_node_deps
            && !calc_alg_context
                .process_context()
                .dep_node(dep_node)
                .is_independent_base_dependency_type()
            && (dependend_con_des.is_none()
                || calc_alg_context
                    .process_context()
                    .dep_node(dep_node)
                    .has_additional_dependencies())
        {
            simple_same_node_deps = false;
        }

        if simple_same_node_deps {
            dep_linker.insert(0, dependend_con_des);
            return true;
        }

        let mut dep_set: HashSet<(Cint64, TrackPointId)> = HashSet::new();
        let mut dep_list: VecDeque<(Cint64, TrackPointId)> = VecDeque::new();
        dep_set.insert((base_depth, dep_track_point));
        dep_list.push_back((base_depth, dep_track_point));

        while let Some((anc_depth, curr_dep_track_point)) = dep_list.pop_front() {
            if curr_dep_track_point.is_none() {
                return false;
            }
            let dep_node = calc_alg_context
                .process_context()
                .track_point(curr_dep_track_point)
                .dependency_node();
            if dep_node.is_none()
                || !calc_alg_context
                    .process_context()
                    .dep_node(dep_node)
                    .is_deterministic()
            {
                return false;
            }

            let app_indi_node = calc_alg_context
                .process_context()
                .dep_node(dep_node)
                .individual_node();
            let mut new_anc_depth = anc_depth;
            let mut continue_dep_loading = true;
            if app_indi_node.is_some() {
                new_anc_depth = calc_alg_context
                    .process_context()
                    .node(app_indi_node)
                    .individual_ancestor_depth();
            }
            if new_anc_depth == base_depth {
                let next_con_des = calc_alg_context
                    .process_context()
                    .dep_node(dep_node)
                    .concept_descriptor();
                if next_con_des.is_some() {
                    continue_dep_loading = false;
                    dep_linker.insert(0, next_con_des);
                }
            }
            if new_anc_depth < base_depth
                || calc_alg_context
                    .process_context()
                    .dep_node(dep_node)
                    .is_independent_base_dependency_type()
            {
                return false;
            }

            if continue_dep_loading {
                let prev_dep_track_point = calc_alg_context
                    .process_context()
                    .dep_node(dep_node)
                    .previous_dependency_track_point();
                if prev_dep_track_point.is_none() {
                    return false;
                }
                let mut next_anc_depth = new_anc_depth;
                let next_dep_node = calc_alg_context
                    .process_context()
                    .track_point(prev_dep_track_point)
                    .dependency_node();
                if next_dep_node.is_some()
                    && calc_alg_context
                        .process_context()
                        .dep_node(next_dep_node)
                        .has_appropriate_individual_node()
                {
                    let next_app_indi_node = calc_alg_context
                        .process_context()
                        .dep_node(next_dep_node)
                        .individual_node();
                    next_anc_depth = calc_alg_context
                        .process_context()
                        .node(next_app_indi_node)
                        .individual_ancestor_depth();
                }
                if dep_set.insert((next_anc_depth, prev_dep_track_point)) {
                    dep_list.push_back((next_anc_depth, prev_dep_track_point));
                }
            }

            let mut dep_it = calc_alg_context
                .process_context()
                .dep_node(dep_node)
                .additional_after_dependencies();
            while dep_it.is_some() {
                let prev_dep_track_point = calc_alg_context
                    .process_context()
                    .dep_link(dep_it)
                    .previous_dependency_track_point();
                if prev_dep_track_point.is_none() {
                    return false;
                }
                // C++ computes a `nextAncDepth` from this dependency, but keys and
                // enqueues additional dependencies with the current `ancDepth`.
                let next_dep_node = calc_alg_context
                    .process_context()
                    .track_point(prev_dep_track_point)
                    .dependency_node();
                if next_dep_node.is_some()
                    && calc_alg_context
                        .process_context()
                        .dep_node(next_dep_node)
                        .has_appropriate_individual_node()
                {
                    let next_app_indi_node = calc_alg_context
                        .process_context()
                        .dep_node(next_dep_node)
                        .individual_node();
                    let _next_anc_depth = calc_alg_context
                        .process_context()
                        .node(next_app_indi_node)
                        .individual_ancestor_depth();
                }
                if dep_set.insert((anc_depth, prev_dep_track_point)) {
                    dep_list.push_back((anc_depth, prev_dep_track_point));
                }

                dep_it = calc_alg_context
                    .process_context()
                    .dep_link(dep_it)
                    .next_additional_dependency();
            }
        }
        true
    }

    // =======================================================================
    // Debug tracking-line / dependency strings (cpp 6723–6770, 8175–8298).
    // W3-DEFER: Qt string formatting over unported tracking-line / formatter types.
    // =======================================================================

    /// Port of `writeDebugTrackingLineStringToFile`. cpp 6723–6739.
    ///
    /// KONCLUDE-PORT-NOTE[api]: writes the debug tracking-line string to two
    /// `./Debugging/CompletionTasks/…` files (Qt `QFile`); the file I/O is deferred.
    /// The C++ returns the (unmodified) input `debugDataString` — preserved.
    pub fn write_debug_tracking_line_string_to_file(
        &mut self,
        debug_data_string: &str,
        file_name_string: &str,
        tracking_line: TrackingLine,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> String {
        // W3-DEFER[api]: the two QFile writes (backtrack-task-<depth>-<id>-<name>.txt
        // + the appended "-continued.txt") over the Qt task depth/id; return input.
        let _ = (file_name_string, tracking_line);
        debug_data_string.to_string()
    }

    /// Port of `generateDebugTrackingLineString`. cpp 6744–6770. W3-DEFER.
    ///
    /// Assembles the six tracked-clash descriptor buckets of a tracking line into a
    /// human-readable string. Depends on the Unit 30 `CTrackedClashedDependencyLine`
    /// substrate + `generateDebugTrackedClashedDescriptorString` sibling.
    pub fn generate_debug_tracking_line_string(
        &mut self,
        tracking_line: TrackingLine,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> String {
        // W3-DEFER[api]: faithful structure (cpp 6744–6770):
        //   trackLineString = "branching level: %1, individual node level: %2\r\n";
        //   for bucket in [independent, level-branching, level, prev-level,
        //                  prev-level-nondet-branching, prev-level-nondet]:
        //     trackLineString += "$ tracked clashes, ... \r\n" +
        //         generateDebugTrackedClashedDescriptorString(bucket, ctx);   // Unit 30 sibling
        //   trackLineString.replace("\r\n","<br>");
        // Held PORT-PENDING: the tracking-line record bucket getters +
        // `generateDebugTrackedClashedDescriptorString`.
        let _ = tracking_line;
        String::new()
    }

    /// Port of `generateDebugDependencyString`. cpp 8175–8298. W3-DEFER.
    ///
    /// Formats one dependency track point: the dependency-node type name, its
    /// concept descriptor (`CConceptTextFormater`), the appropriate individual id,
    /// non-deterministic open/branch-track-point counts, the additional-dependency
    /// count, and the branching tag.
    pub fn generate_debug_dependency_string(
        &mut self,
        dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> String {
        // W3-DEFER[api]: faithful structure (cpp 8175–8298):
        //   if !depTrackPoint: return "null";
        //   depNode = depTrackPoint.getDependencyNode();
        //   depTypeString = switch(depNode.getDependencyType()) { INDEPENDENT/ALL/SOME/AND/
        //     OR/ATLEAST/AUTOMATCHOOSE/AUTOMATTRANSACTION/SELF/VALUE/NEGVALUE/DISTINCT/
        //     MERGEDCONCEPT/MERGEDLINK/MERGE/ATMOST/QUALIFY/FUNCTIONAL/NOMINAL/IMPLICATION/
        //     EXPANDED/DATATYPETRIGGER/ROLEASSERTION };
        //   conceptDepNodeString = depNode.getConceptDescriptor()
        //       ? CConceptTextFormater::getConceptString(conDes.getConcept(), conDes.isNegated()) : "null";
        //   depIndiNodeString = depNode.getAppropriateIndividualNode() ? "@<id> " : "";
        //   depInfoString = (nonDet ? " NonDetDep, <opened/branchTrackPoints>" : "")
        //       + " + ...(<additionalDependencyCount>)";
        //   dependencyString = "<type>-Dependency: {<concept>}<indi><info>";
        //   return " ^<branchingTag>  --->  <dependencyString>";
        // Held PORT-PENDING: `CConceptTextFormater`, the track point's
        // `getBranchingTag`, and the non-deterministic open/branch-track-point
        // counts (the dep-node type switch + concept descriptor are otherwise live).
        let _ = dep_track_point;
        String::from("null")
    }

    // =======================================================================
    // markDependencyRelevance (cpp 7360–7388). Recursive spine ported.
    // =======================================================================

    /// Port of `markDependencyRelevance`. cpp 7360–7388.
    ///
    /// Marks a dependency track point relevant and recurses to its previous track
    /// point (and, in the C++, every additional dependency), then — for a
    /// non-deterministic node — flags its branch's task relevant. The relevance flag
    /// set + previous-track-point recursion are ported; the additional-dependency
    /// iteration and the Task-relevant communication are deferred.
    pub fn mark_dependency_relevance(
        &mut self,
        dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // KONCLUDE-PORT-NOTE[ownership]: C++ derefs the raw track-point pointer; the
        // recursion bottoms out at the independent base (its previous track point is
        // null), so guard `is_some()` to terminate without a panic.
        if dep_track_point.is_none() {
            return;
        }
        if !calc_alg_context
            .process_context()
            .track_point(dep_track_point)
            .is_dependency_relevant()
        {
            calc_alg_context
                .process_context_mut()
                .track_point_mut(dep_track_point)
                .set_dependency_relevance(true);

            let dep_node = calc_alg_context
                .process_context()
                .track_point(dep_track_point)
                .dependency_node();
            if dep_node.is_some() {
                // W3-DEFER[unclear]: getAdditionalDependencyIterator(true,true) — the
                // additional-dependency iterator's two-bool selector is not yet
                // ported; faithful loop:
                //   for dep in depNode.getAdditionalDependencyIterator(true,true):
                //       markDependencyRelevance(dep.getPreviousDependencyTrackPoint(), ctx);
                let prev_dep_track_point = calc_alg_context
                    .process_context()
                    .dep_node(dep_node)
                    .previous_dependency_track_point();
                self.mark_dependency_relevance(prev_dep_track_point, calc_alg_context);

                // W6-DEFER[api]: non-deterministic node → mark its branch task relevant:
                //   if depNode.isNonDeterministiDependencyNode():
                //     branchTreeNode = ((CNonDeterministicDependencyNode*)depNode).getBranchNode();
                //     branchSatCalcTask = branchTreeNode.getSatisfiableCalculationTask();
                //     if !branchSatCalcTask.isTaskRelevant():
                //       ctx.getUsedTaskProcessorContext().getTaskProcessorCommunicator()
                //          .communicateTaskRelevant(branchSatCalcTask);     // Task layer (W6)
            }
        }
    }

    // =======================================================================
    // initializeTrackingLine (cpp 7900–7917).
    // =======================================================================

    /// Port of `initializeTrackingLine`. cpp 7900–7917.
    ///
    /// Candidate-scans the tracked clashes for a tracking error / nominal occurrence
    /// / branching+individual level bounds; on no error, initialises the tracking
    /// line at those bounds, analyses involved individuals, and sorts the clashes
    /// in. Returns whether the line initialised (no tracking error).
    pub fn initialize_tracking_line(
        &mut self,
        tracking_line: &mut TrackedClashedDependencyLine,
        tracking_clashes: ClashDescId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut tracking_error = false;
        let mut nominal_occured = false;
        let mut max_branching_level = Cint64::MIN;
        let mut min_individual_level = Cint64::MAX;

        let mut tracking_clash_it = tracking_clashes;
        while tracking_clash_it.is_some() && !tracking_error {
            let tracking_clash = calc_alg_context
                .process_context()
                .clash_desc(tracking_clash_it);
            tracking_error |= tracking_clash.is_tracking_error();
            nominal_occured |= tracking_clash.is_appropriated_individual_nominal();
            max_branching_level = max_branching_level.max(tracking_clash.get_branching_level_tag());
            min_individual_level =
                min_individual_level.min(tracking_clash.get_appropriated_individual_level());
            tracking_clash_it = tracking_clash.get_next_descriptor();
        }

        if tracking_error {
            return false;
        }

        tracking_line.init_tracked_clashed_dependency_line(
            nominal_occured,
            min_individual_level,
            max_branching_level,
        );
        tracking_line.analyse_involved_individuals(tracking_clashes, calc_alg_context);
        tracking_line.sort_in_tracked_clashed_descriptors(tracking_clashes, true, calc_alg_context);
        true
    }

    // =======================================================================
    // getCoresspondingIndividualNodeFromDependency (cpp 7975–7995). Fully ported.
    // =======================================================================

    /// Port of `getCoresspondingIndividualNodeFromDependency(CDependencyTrackPoint*)`.
    /// cpp 7975–7978. Pure delegation to the dep-node overload.
    pub fn get_coressponding_individual_node_from_dependency(
        &mut self,
        dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        let dep_node = calc_alg_context
            .process_context()
            .track_point(dep_track_point)
            .dependency_node();
        self.get_coressponding_individual_node_from_dependency_node(dep_node, calc_alg_context)
    }

    /// Port of `getCoresspondingIndividualNodeFromDependency(CDependencyNode*)`.
    /// cpp 7981–7995.
    ///
    /// Resolves the dependency node's appropriate individual node to its up-to-date,
    /// merge-corrected representative (following a merged-into nominal node).
    ///
    /// KONCLUDE-PORT-NOTE[overload]: the C++ name is shared with the track-point
    /// overload; the `_node` suffix disambiguates. `getUpToDateIndividual(NodeId)`
    /// is an as-yet-unported sibling (a helper-batch unit); the faithful call stands
    /// and resolves on its reconcile pass.
    pub fn get_coressponding_individual_node_from_dependency_node(
        &mut self,
        dep_node: DependencyId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        let mut indi = calc_alg_context
            .process_context()
            .dep_node(dep_node)
            .individual_node();
        if indi.is_some() {
            let upd_indi = self.get_up_to_date_individual(indi, calc_alg_context);
            if upd_indi.is_some() {
                let mut upd_indi = upd_indi;
                if calc_alg_context
                    .process_context()
                    .node(upd_indi)
                    .has_merged_into_individual_node_id()
                {
                    let merged_into = calc_alg_context
                        .process_context()
                        .node(upd_indi)
                        .merged_into_individual_node_id();
                    upd_indi =
                        self.get_corrected_nominal_individual_node(merged_into, calc_alg_context);
                }
                indi = upd_indi;
            }
        }
        indi
    }

    // =======================================================================
    // Dependency-node factory wrappers (cpp 9755–10121).
    //
    // Each is the identical Konclude idiom:
    //   CXDependencyNode* depNode = nullptr;
    //   if (mConfBuildDependencies)
    //       depNode = calcAlgContext->getUsedDependencyFactory()->createXDependency(...);
    //   return depNode;
    // The `mConfBuildDependencies` guard + null (`Id::NONE`) return are ported in
    // full; the factory dispatch is W6-DEFER[api] (the `CDependencyFactory` is a
    // zero-size stub with no methods yet). All return the tagged `DependencyId`.
    // The `CDependencyTrackPoint*&` out-references are kept as `&mut TrackPointId`
    // (the factory fills the continuation point) — inert until the factory lands.
    // =======================================================================

    /// Port of `createREPRESENTATIVEGROUNDINGDependency`. cpp 9755–9761.
    pub fn create_representative_grounding_dependency(
        &mut self,
        impl_continue_dep_track_point: &mut TrackPointId,
        process_indi: &mut NodeId,
        con_des: ConDescId,
        prev_dep_track_point: TrackPointId,
        select_var_bind_path: VarBindingPathId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node = Id::NONE;
        if self.conf_build_dependencies {
            dep_node = calc_alg_context
                .process_context_mut()
                .alloc_deterministic_dependency_node(DepKind::RepresentativeGrounding);
            {
                let proc_ctx = calc_alg_context.process_context_mut();
                let dep = proc_ctx.dep_node_mut(dep_node);
                dep.init_deterministic_dependency_node(DepKind::RepresentativeGrounding, con_des);
                dep.base_mut().selected_var_bind_path = select_var_bind_path;
                dep.base_mut().dep_track_point = prev_dep_track_point;
                proc_ctx.update_dependency_branching_tag(dep_node);
            }
            *impl_continue_dep_track_point = calc_alg_context
                .process_context_mut()
                .materialize_continue_dependency_track_point(dep_node);
            let _ = process_indi;
        }
        dep_node
    }

    /// Port of `createREPRESENTATIVEJOINDependency`. cpp 9763–9769.
    pub fn create_representative_join_dependency(
        &mut self,
        join_continue_dep_track_point: &mut TrackPointId,
        process_indi: &mut NodeId,
        con_des: ConDescId,
        prev_dep_track_point: TrackPointId,
        other_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node = Id::NONE;
        if self.conf_build_dependencies {
            dep_node = calc_alg_context
                .process_context_mut()
                .alloc_det_link_dependency_node(DepKind::RepresentativeJoin);
            let other_dep = {
                let proc_ctx = calc_alg_context.process_context_mut();
                let dep = proc_ctx.dep_node_mut(dep_node);
                dep.init_deterministic_dependency_node(DepKind::RepresentativeJoin, con_des);
                dep.base_mut().dep_track_point = prev_dep_track_point;
                if let DependencyNode::DetLink { prev, .. } = dep {
                    *prev
                } else {
                    DepLinkId::NONE
                }
            };
            if other_dep_track_point.is_some() && other_dep.is_some() {
                let proc_ctx = calc_alg_context.process_context_mut();
                proc_ctx
                    .dep_link_mut(other_dep)
                    .init_dependency(other_dep_track_point);
                proc_ctx.update_dependency_branching_tag(dep_node);
            } else {
                calc_alg_context
                    .process_context_mut()
                    .update_dependency_branching_tag(dep_node);
            }
            *join_continue_dep_track_point = calc_alg_context
                .process_context_mut()
                .materialize_continue_dependency_track_point(dep_node);
            let _ = process_indi;
        }
        dep_node
    }

    /// Port of `createREPRESENTATIVEBINDVARIABLEDependency`. cpp 9771–9777.
    pub fn create_representative_bind_variable_dependency(
        &mut self,
        and_dep_track_point: &mut TrackPointId,
        process_indi: &mut NodeId,
        con_des: ConDescId,
        prev_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node = Id::NONE;
        if self.conf_build_dependencies {
            dep_node = calc_alg_context
                .process_context_mut()
                .alloc_deterministic_dependency_node(DepKind::RepresentativeBindVariable);
            {
                let proc_ctx = calc_alg_context.process_context_mut();
                let dep = proc_ctx.dep_node_mut(dep_node);
                dep.init_deterministic_dependency_node(
                    DepKind::RepresentativeBindVariable,
                    con_des,
                );
                dep.base_mut().dep_track_point = prev_dep_track_point;
                // C++ initializes the CRepresentativeSelectDependencyNode base with
                // selectedVarBindPath = nullptr for this dependency kind.
                proc_ctx.update_dependency_branching_tag(dep_node);
            }
            *and_dep_track_point = calc_alg_context
                .process_context_mut()
                .materialize_continue_dependency_track_point(dep_node);
            let _ = process_indi;
        }
        dep_node
    }

    /// Port of `createREPRESENTATIVEIMPLICATIONDependency`. cpp 9779–9785.
    pub fn create_representative_implication_dependency(
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
                .alloc_deterministic_dependency_node(DepKind::RepresentativeImplication);
            {
                let proc_ctx = calc_alg_context.process_context_mut();
                let dep = proc_ctx.dep_node_mut(dep_node);
                dep.init_deterministic_dependency_node(DepKind::RepresentativeImplication, con_des);
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

    /// Port of `createREPRESENTATIVEALLDependency`. cpp 9787–9793.
    pub fn create_representative_all_dependency(
        &mut self,
        all_dep_track_point: &mut TrackPointId,
        process_indi: &mut NodeId,
        con_des: ConDescId,
        prev_dep_track_point: TrackPointId,
        link_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node = Id::NONE;
        if self.conf_build_dependencies {
            dep_node = calc_alg_context
                .process_context_mut()
                .alloc_det_link_dependency_node(DepKind::RepresentativeAll);
            let link_dep = {
                let proc_ctx = calc_alg_context.process_context_mut();
                let dep = proc_ctx.dep_node_mut(dep_node);
                dep.init_deterministic_dependency_node(DepKind::RepresentativeAll, con_des);
                dep.base_mut().dep_track_point = prev_dep_track_point;
                if let DependencyNode::DetLink { prev, .. } = dep {
                    *prev
                } else {
                    DepLinkId::NONE
                }
            };
            if link_dep_track_point.is_some() && link_dep.is_some() {
                let proc_ctx = calc_alg_context.process_context_mut();
                proc_ctx
                    .dep_link_mut(link_dep)
                    .init_dependency(link_dep_track_point);
                proc_ctx.update_dependency_branching_tag(dep_node);
            } else {
                calc_alg_context
                    .process_context_mut()
                    .update_dependency_branching_tag(dep_node);
            }
            *all_dep_track_point = calc_alg_context
                .process_context_mut()
                .materialize_continue_dependency_track_point(dep_node);
            let _ = process_indi;
        }
        dep_node
    }

    /// Port of `createREPRESENTATIVEANDDependency`. cpp 9795–9801.
    pub fn create_representative_and_dependency(
        &mut self,
        and_dep_track_point: &mut TrackPointId,
        process_indi: &mut NodeId,
        con_des: ConDescId,
        prev_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node = Id::NONE;
        if self.conf_build_dependencies {
            dep_node = calc_alg_context
                .process_context_mut()
                .alloc_deterministic_dependency_node(DepKind::RepresentativeAnd);
            {
                let proc_ctx = calc_alg_context.process_context_mut();
                let dep = proc_ctx.dep_node_mut(dep_node);
                dep.init_deterministic_dependency_node(DepKind::RepresentativeAnd, con_des);
                dep.base_mut().dep_track_point = prev_dep_track_point;
                proc_ctx.update_dependency_branching_tag(dep_node);
            }
            *and_dep_track_point = calc_alg_context
                .process_context_mut()
                .materialize_continue_dependency_track_point(dep_node);
            let _ = process_indi;
        }
        dep_node
    }

    /// Port of `createRESOLVEREPRESENTATIVEDependency`. cpp 9803–9809.
    pub fn create_resolve_representative_dependency(
        &mut self,
        and_dep_track_point: &mut TrackPointId,
        process_indi: &mut NodeId,
        con_des: ConDescId,
        resolve_var_bind_path_map: Option<&RepresentativeVariableBindingPathMap>,
        resolve_rep_prop_map: Option<&RepresentativePropagationMap>,
        prev_dep_track_point: TrackPointId,
        additional_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node = Id::NONE;
        if self.conf_build_dependencies {
            dep_node = calc_alg_context
                .process_context_mut()
                .alloc_det_link_dependency_node(DepKind::ResolveRepresentative);
            let additional_dep = {
                let proc_ctx = calc_alg_context.process_context_mut();
                let dep = proc_ctx.dep_node_mut(dep_node);
                dep.init_deterministic_dependency_node(DepKind::ResolveRepresentative, con_des);
                dep.base_mut().resolve_var_bind_path_map = resolve_var_bind_path_map.cloned();
                dep.base_mut().resolve_rep_prop_map = resolve_rep_prop_map.cloned();
                dep.base_mut().dep_track_point = prev_dep_track_point;
                if let DependencyNode::DetLink { prev, .. } = dep {
                    *prev
                } else {
                    DepLinkId::NONE
                }
            };
            if additional_dep_track_point.is_some() && additional_dep.is_some() {
                let proc_ctx = calc_alg_context.process_context_mut();
                proc_ctx
                    .dep_link_mut(additional_dep)
                    .init_dependency(additional_dep_track_point);
                proc_ctx.dep_node_mut(dep_node).base_mut().additional_after = additional_dep;
                proc_ctx.update_dependency_branching_tag(dep_node);
            } else {
                calc_alg_context
                    .process_context_mut()
                    .update_dependency_branching_tag(dep_node);
            }
            *and_dep_track_point = calc_alg_context
                .process_context_mut()
                .materialize_continue_dependency_track_point(dep_node);
            let _ = process_indi;
        }
        dep_node
    }

    /// Port of `createPROPAGATEVARIABLECONNECTIONDependency`. cpp 9820–9826.
    pub fn create_propagate_variable_connection_dependency(
        &mut self,
        process_indi: NodeId,
        con_des: ConDescId,
        prev_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node = Id::NONE;
        if self.conf_build_dependencies {
            dep_node = calc_alg_context
                .process_context_mut()
                .alloc_deterministic_dependency_node(DepKind::PropagateVariableConnection);
            {
                let proc_ctx = calc_alg_context.process_context_mut();
                let dep = proc_ctx.dep_node_mut(dep_node);
                dep.init_deterministic_dependency_node_indi(
                    DepKind::PropagateVariableConnection,
                    process_indi,
                    con_des,
                );
                dep.base_mut().dep_track_point = prev_dep_track_point;
                proc_ctx.update_dependency_branching_tag(dep_node);
            }
        }
        dep_node
    }

    /// Port of `createVARBINDPROPAGATEIMPLICATIONDependency`. cpp 9828–9834.
    pub fn create_varbind_propagate_implication_dependency(
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
                .alloc_deterministic_dependency_node(DepKind::VarBindPropagateImplication);
            {
                let proc_ctx = calc_alg_context.process_context_mut();
                let dep = proc_ctx.dep_node_mut(dep_node);
                dep.init_deterministic_dependency_node(
                    DepKind::VarBindPropagateImplication,
                    con_des,
                );
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

    /// Port of `createVARBINDPROPAGATEGROUNDINGDependency`. cpp 9836–9842.
    pub fn create_varbind_propagate_grounding_dependency(
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
            // CDependencyFactory::createVARBINDPROPAGATEGROUNDINGDependency allocates a
            // tag-only deterministic node, initializes its previous/additional
            // dependencies, then returns its continuation track point.
            dep_node = calc_alg_context
                .process_context_mut()
                .alloc_deterministic_dependency_node(DepKind::VarBindPropagateGrounding);
            {
                let proc_ctx = calc_alg_context.process_context_mut();
                let dep = proc_ctx.dep_node_mut(dep_node);
                dep.init_deterministic_dependency_node(DepKind::VarBindPropagateGrounding, con_des);
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

    /// Port of `createVARBINDPROPAGATEALLDependency`. cpp 9844–9850.
    pub fn create_varbind_propagate_all_dependency(
        &mut self,
        all_dep_track_point: &mut TrackPointId,
        process_indi: &mut NodeId,
        con_des: ConDescId,
        prev_dep_track_point: TrackPointId,
        link_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node = Id::NONE;
        if self.conf_build_dependencies {
            dep_node = calc_alg_context
                .process_context_mut()
                .alloc_det_link_dependency_node(DepKind::VarBindPropagateAll);
            {
                let proc_ctx = calc_alg_context.process_context_mut();
                let prev = {
                    let dep = proc_ctx.dep_node_mut(dep_node);
                    dep.init_dependency_node_indi(
                        DepKind::VarBindPropagateAll,
                        *process_indi,
                        con_des,
                    );
                    dep.base_mut().dep_track_point = prev_dep_track_point;
                    if let super::super::process::dependency::DependencyNode::DetLink {
                        prev, ..
                    } = dep
                    {
                        *prev
                    } else {
                        unreachable!("VARBINDPROPAGATEALL dependency allocated with DetLink shape")
                    }
                };
                proc_ctx.dep_link_mut(prev).dep_track_point = link_dep_track_point;
                proc_ctx.update_dependency_branching_tag(dep_node);
            }
            *all_dep_track_point = calc_alg_context
                .process_context_mut()
                .materialize_continue_dependency_track_point(dep_node);
        }
        dep_node
    }

    /// Port of `createVARBINDPROPAGATEANDDependency`. cpp 9852–9858.
    pub fn create_varbind_propagate_and_dependency(
        &mut self,
        and_dep_track_point: &mut TrackPointId,
        process_indi: &mut NodeId,
        con_des: ConDescId,
        prev_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node = Id::NONE;
        if self.conf_build_dependencies {
            dep_node = calc_alg_context
                .process_context_mut()
                .alloc_deterministic_dependency_node(DepKind::VarBindPropagateAnd);
            {
                let proc_ctx = calc_alg_context.process_context_mut();
                let dep = proc_ctx.dep_node_mut(dep_node);
                dep.init_deterministic_dependency_node(DepKind::VarBindPropagateAnd, con_des);
                dep.base_mut().dep_track_point = prev_dep_track_point;
                proc_ctx.update_dependency_branching_tag(dep_node);
            }
            *and_dep_track_point = calc_alg_context
                .process_context_mut()
                .materialize_continue_dependency_track_point(dep_node);
            let _ = process_indi;
        }
        dep_node
    }

    /// Port of `createPROPAGATEVARIABLEBINDINGDependency`. cpp 9860–9866.
    pub fn create_propagate_variable_binding_dependency(
        &mut self,
        and_dep_track_point: &mut TrackPointId,
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
                .alloc_deterministic_dependency_node(DepKind::PropagateVariableBinding);
            {
                let proc_ctx = calc_alg_context.process_context_mut();
                let dep = proc_ctx.dep_node_mut(dep_node);
                dep.init_deterministic_dependency_node(DepKind::PropagateVariableBinding, con_des);
                dep.base_mut().dep_track_point = prev_dep_track_point;
                if prev_other_dependencies.is_some() {
                    dep.base_mut().additional_after = prev_other_dependencies;
                }
                proc_ctx.update_dependency_branching_tag(dep_node);
            }
            *and_dep_track_point = calc_alg_context
                .process_context_mut()
                .materialize_continue_dependency_track_point(dep_node);
            let _ = process_indi;
        }
        dep_node
    }

    /// Port of `createPROPAGATEVARIABLEBINDINGSSUCCESSORDependency`. cpp 9868–9874.
    pub fn create_propagate_variable_bindings_successor_dependency(
        &mut self,
        all_dep_track_point: &mut TrackPointId,
        process_indi: &mut NodeId,
        con_des: ConDescId,
        prev_dep_track_point: TrackPointId,
        link_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node = Id::NONE;
        if self.conf_build_dependencies {
            dep_node = calc_alg_context
                .process_context_mut()
                .alloc_det_link_dependency_node(DepKind::PropagateVariableBindingSuccessor);
            {
                let proc_ctx = calc_alg_context.process_context_mut();
                let prev = {
                    let dep = proc_ctx.dep_node_mut(dep_node);
                    dep.init_dependency_node_indi(
                        DepKind::PropagateVariableBindingSuccessor,
                        *process_indi,
                        con_des,
                    );
                    dep.base_mut().dep_track_point = prev_dep_track_point;
                    if let super::super::process::dependency::DependencyNode::DetLink {
                        prev, ..
                    } = dep
                    {
                        *prev
                    } else {
                        unreachable!(
                            "PROPAGATEVARIABLEBINDINGSSUCCESSOR dependency allocated with DetLink shape"
                        )
                    }
                };
                proc_ctx.dep_link_mut(prev).dep_track_point = link_dep_track_point;
                proc_ctx.update_dependency_branching_tag(dep_node);
            }
            *all_dep_track_point = calc_alg_context
                .process_context_mut()
                .materialize_continue_dependency_track_point(dep_node);
        }
        dep_node
    }

    /// Port of `createVARBINDVARIABLEDependency`. cpp 9876–9882.
    pub fn create_varbind_variable_dependency(
        &mut self,
        and_dep_track_point: &mut TrackPointId,
        process_indi: &mut NodeId,
        con_des: ConDescId,
        prev_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node = Id::NONE;
        if self.conf_build_dependencies {
            dep_node = calc_alg_context
                .process_context_mut()
                .alloc_deterministic_dependency_node(DepKind::VarBindVariable);
            {
                let proc_ctx = calc_alg_context.process_context_mut();
                let dep = proc_ctx.dep_node_mut(dep_node);
                dep.init_deterministic_dependency_node(DepKind::VarBindVariable, con_des);
                dep.base_mut().dep_track_point = prev_dep_track_point;
                proc_ctx.update_dependency_branching_tag(dep_node);
            }
            *and_dep_track_point = calc_alg_context
                .process_context_mut()
                .materialize_continue_dependency_track_point(dep_node);
            let _ = process_indi;
        }
        dep_node
    }

    /// Port of `createVARBINDPROPAGATEJOINDependency`. cpp 9884–9890.
    pub fn create_varbind_propagate_join_dependency(
        &mut self,
        continue_dep_track_point: &mut TrackPointId,
        process_indi: &mut NodeId,
        con_des: ConDescId,
        prev_dep_track_point: TrackPointId,
        other_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node = Id::NONE;
        if self.conf_build_dependencies {
            dep_node = calc_alg_context
                .process_context_mut()
                .alloc_det_link_dependency_node(DepKind::VarBindPropagateJoin);
            {
                let proc_ctx = calc_alg_context.process_context_mut();
                let prev = {
                    let dep = proc_ctx.dep_node_mut(dep_node);
                    dep.init_deterministic_dependency_node(DepKind::VarBindPropagateJoin, con_des);
                    dep.base_mut().dep_track_point = prev_dep_track_point;
                    if let super::super::process::dependency::DependencyNode::DetLink {
                        prev, ..
                    } = dep
                    {
                        *prev
                    } else {
                        unreachable!("VARBINDPROPAGATEJOIN dependency allocated with DetLink shape")
                    }
                };
                proc_ctx.dep_link_mut(prev).dep_track_point = other_dep_track_point;
                proc_ctx.update_dependency_branching_tag(dep_node);
            }
            *continue_dep_track_point = calc_alg_context
                .process_context_mut()
                .materialize_continue_dependency_track_point(dep_node);
            let _ = process_indi;
        }
        dep_node
    }

    /// Port of `createBINDPROPAGATEGROUNDINGDependency`. cpp 9897–9903.
    pub fn create_bind_propagate_grounding_dependency(
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
                .alloc_deterministic_dependency_node(DepKind::BindPropagateGrounding);
            {
                let proc_ctx = calc_alg_context.process_context_mut();
                let dep = proc_ctx.dep_node_mut(dep_node);
                dep.init_deterministic_dependency_node(DepKind::BindPropagateGrounding, con_des);
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

    /// Port of `createPROPAGATECONNECTIONAWAYDependency`. cpp 9905–9911.
    pub fn create_propagate_connection_away_dependency(
        &mut self,
        process_indi: NodeId,
        con_des: ConDescId,
        prev_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node = Id::NONE;
        if self.conf_build_dependencies {
            dep_node = calc_alg_context
                .process_context_mut()
                .alloc_deterministic_dependency_node(DepKind::PropagateConnectionAway);
            {
                let proc_ctx = calc_alg_context.process_context_mut();
                let dep = proc_ctx.dep_node_mut(dep_node);
                dep.init_deterministic_dependency_node_indi(
                    DepKind::PropagateConnectionAway,
                    process_indi,
                    con_des,
                );
                dep.base_mut().dep_track_point = prev_dep_track_point;
                proc_ctx.update_dependency_branching_tag(dep_node);
            }
        }
        dep_node
    }

    /// Port of `createPROPAGATECONNECTIONDependency`. cpp 9913–9919.
    pub fn create_propagate_connection_dependency(
        &mut self,
        process_indi: NodeId,
        con_des: ConDescId,
        prev_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node = Id::NONE;
        if self.conf_build_dependencies {
            dep_node = calc_alg_context
                .process_context_mut()
                .alloc_deterministic_dependency_node(DepKind::PropagateConnection);
            {
                let proc_ctx = calc_alg_context.process_context_mut();
                let dep = proc_ctx.dep_node_mut(dep_node);
                dep.init_deterministic_dependency_node_indi(
                    DepKind::PropagateConnection,
                    process_indi,
                    con_des,
                );
                dep.base_mut().dep_track_point = prev_dep_track_point;
                proc_ctx.update_dependency_branching_tag(dep_node);
            }
        }
        dep_node
    }

    /// Port of `createBINDPROPAGATECYCLEDependency`. cpp 9921–9927.
    pub fn create_bind_propagate_cycle_dependency(
        &mut self,
        continue_dep_track_point: &mut TrackPointId,
        process_indi: &mut NodeId,
        con_des: ConDescId,
        prev_dep_track_point: TrackPointId,
        trigg_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node = Id::NONE;
        if self.conf_build_dependencies {
            dep_node = calc_alg_context
                .process_context_mut()
                .alloc_det_link_dependency_node(DepKind::BindPropagateCycle);
            {
                let proc_ctx = calc_alg_context.process_context_mut();
                let prev = {
                    let dep = proc_ctx.dep_node_mut(dep_node);
                    dep.init_deterministic_dependency_node(DepKind::BindPropagateCycle, con_des);
                    dep.base_mut().dep_track_point = prev_dep_track_point;
                    if let super::super::process::dependency::DependencyNode::DetLink {
                        prev, ..
                    } = dep
                    {
                        *prev
                    } else {
                        unreachable!("BINDPROPAGATECYCLE dependency allocated with DetLink shape")
                    }
                };
                proc_ctx.dep_link_mut(prev).dep_track_point = trigg_dep_track_point;
                proc_ctx.update_dependency_branching_tag(dep_node);
            }
            *continue_dep_track_point = calc_alg_context
                .process_context_mut()
                .materialize_continue_dependency_track_point(dep_node);
            let _ = process_indi;
        }
        dep_node
    }

    /// Port of `createBINDPROPAGATEALLDependency`. cpp 9929–9935.
    pub fn create_bind_propagate_all_dependency(
        &mut self,
        all_dep_track_point: &mut TrackPointId,
        process_indi: &mut NodeId,
        con_des: ConDescId,
        prev_dep_track_point: TrackPointId,
        link_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node = Id::NONE;
        if self.conf_build_dependencies {
            dep_node = calc_alg_context
                .process_context_mut()
                .alloc_det_link_dependency_node(DepKind::BindPropagateAll);
            {
                let proc_ctx = calc_alg_context.process_context_mut();
                let prev = {
                    let dep = proc_ctx.dep_node_mut(dep_node);
                    dep.init_dependency_node_indi(
                        DepKind::BindPropagateAll,
                        *process_indi,
                        con_des,
                    );
                    dep.base_mut().dep_track_point = prev_dep_track_point;
                    if let super::super::process::dependency::DependencyNode::DetLink {
                        prev, ..
                    } = dep
                    {
                        *prev
                    } else {
                        unreachable!("BINDPROPAGATEALL dependency allocated with DetLink shape")
                    }
                };
                proc_ctx.dep_link_mut(prev).dep_track_point = link_dep_track_point;
                proc_ctx.update_dependency_branching_tag(dep_node);
            }
            *all_dep_track_point = calc_alg_context
                .process_context_mut()
                .materialize_continue_dependency_track_point(dep_node);
        }
        dep_node
    }

    /// Port of `createPROPAGATEBINDINGSSUCCESSORDependency`. cpp 9937–9943.
    pub fn create_propagate_bindings_successor_dependency(
        &mut self,
        all_dep_track_point: &mut TrackPointId,
        process_indi: &mut NodeId,
        con_des: ConDescId,
        prev_dep_track_point: TrackPointId,
        link_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node = Id::NONE;
        if self.conf_build_dependencies {
            dep_node = calc_alg_context
                .process_context_mut()
                .alloc_det_link_dependency_node(DepKind::PropagateBindingSuccessor);
            {
                let proc_ctx = calc_alg_context.process_context_mut();
                let prev = {
                    let dep = proc_ctx.dep_node_mut(dep_node);
                    dep.init_dependency_node_indi(
                        DepKind::PropagateBindingSuccessor,
                        *process_indi,
                        con_des,
                    );
                    dep.base_mut().dep_track_point = prev_dep_track_point;
                    if let super::super::process::dependency::DependencyNode::DetLink {
                        prev, ..
                    } = dep
                    {
                        *prev
                    } else {
                        unreachable!(
                            "PROPAGATEBINDINGSSUCCESSOR dependency allocated with DetLink shape"
                        )
                    }
                };
                proc_ctx.dep_link_mut(prev).dep_track_point = link_dep_track_point;
                proc_ctx.update_dependency_branching_tag(dep_node);
            }
            *all_dep_track_point = calc_alg_context
                .process_context_mut()
                .materialize_continue_dependency_track_point(dep_node);
        }
        dep_node
    }

    /// Port of `createBINDPROPAGATEIMPLICATIONDependency`. cpp 9945–9951.
    pub fn create_bind_propagate_implication_dependency(
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
                .alloc_deterministic_dependency_node(DepKind::BindPropagateImplication);
            {
                let proc_ctx = calc_alg_context.process_context_mut();
                let dep = proc_ctx.dep_node_mut(dep_node);
                dep.init_deterministic_dependency_node(DepKind::BindPropagateImplication, con_des);
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

    /// Port of `createANDDependency`. cpp 9953–9959.
    pub fn create_and_dependency(
        &mut self,
        and_dep_track_point: &mut TrackPointId,
        process_indi: &mut NodeId,
        con_des: ConDescId,
        prev_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node = Id::NONE;
        if self.conf_build_dependencies {
            dep_node = calc_alg_context
                .process_context_mut()
                .alloc_deterministic_dependency_node(DepKind::And);
            {
                let proc_ctx = calc_alg_context.process_context_mut();
                let dep = proc_ctx.dep_node_mut(dep_node);
                dep.init_deterministic_dependency_node(DepKind::And, con_des);
                dep.base_mut().dep_track_point = prev_dep_track_point;
                proc_ctx.update_dependency_branching_tag(dep_node);
            }
            *and_dep_track_point = calc_alg_context
                .process_context_mut()
                .materialize_continue_dependency_track_point(dep_node);
            let _ = process_indi;
        }
        dep_node
    }

    /// Port of `createBINDPROPAGATEANDDependency`. cpp 9961–9967.
    pub fn create_bind_propagate_and_dependency(
        &mut self,
        and_dep_track_point: &mut TrackPointId,
        process_indi: &mut NodeId,
        con_des: ConDescId,
        prev_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node = Id::NONE;
        if self.conf_build_dependencies {
            dep_node = calc_alg_context
                .process_context_mut()
                .alloc_deterministic_dependency_node(DepKind::BindPropagateAnd);
            {
                let proc_ctx = calc_alg_context.process_context_mut();
                let dep = proc_ctx.dep_node_mut(dep_node);
                dep.init_deterministic_dependency_node(DepKind::BindPropagateAnd, con_des);
                dep.base_mut().dep_track_point = prev_dep_track_point;
                proc_ctx.update_dependency_branching_tag(dep_node);
            }
            *and_dep_track_point = calc_alg_context
                .process_context_mut()
                .materialize_continue_dependency_track_point(dep_node);
            let _ = process_indi;
        }
        dep_node
    }

    /// Port of `createPROPAGATEBINDINGDependency`. cpp 9969–9975.
    pub fn create_propagate_binding_dependency(
        &mut self,
        and_dep_track_point: &mut TrackPointId,
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
                .alloc_deterministic_dependency_node(DepKind::PropagateBinding);
            {
                let proc_ctx = calc_alg_context.process_context_mut();
                let dep = proc_ctx.dep_node_mut(dep_node);
                dep.init_deterministic_dependency_node(DepKind::PropagateBinding, con_des);
                dep.base_mut().dep_track_point = prev_dep_track_point;
                if prev_other_dependencies.is_some() {
                    dep.base_mut().additional_after = prev_other_dependencies;
                }
                proc_ctx.update_dependency_branching_tag(dep_node);
            }
            *and_dep_track_point = calc_alg_context
                .process_context_mut()
                .materialize_continue_dependency_track_point(dep_node);
            let _ = process_indi;
        }
        dep_node
    }

    /// Port of `createBINDVARIABLEDependency`. cpp 9977–9983.
    pub fn create_bind_variable_dependency(
        &mut self,
        and_dep_track_point: &mut TrackPointId,
        process_indi: &mut NodeId,
        con_des: ConDescId,
        prev_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node = Id::NONE;
        if self.conf_build_dependencies {
            dep_node = calc_alg_context
                .process_context_mut()
                .alloc_deterministic_dependency_node(DepKind::BindVariable);
            {
                let proc_ctx = calc_alg_context.process_context_mut();
                let dep = proc_ctx.dep_node_mut(dep_node);
                dep.init_deterministic_dependency_node(DepKind::BindVariable, con_des);
                dep.base_mut().dep_track_point = prev_dep_track_point;
                proc_ctx.update_dependency_branching_tag(dep_node);
            }
            *and_dep_track_point = calc_alg_context
                .process_context_mut()
                .materialize_continue_dependency_track_point(dep_node);
            let _ = process_indi;
        }
        dep_node
    }

    /// Port of `createNOMINALDependency`. cpp 9985–9991.
    pub fn create_nominal_dependency(
        &mut self,
        nominal_cont_dep_track_point: &mut TrackPointId,
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
                .alloc_det_link_dependency_node(DepKind::Nominal);
            {
                let proc_ctx = calc_alg_context.process_context_mut();
                let prev = {
                    let dep = proc_ctx.dep_node_mut(dep_node);
                    dep.init_dependency_node_indi(DepKind::Nominal, *process_indi, con_des);
                    dep.base_mut().dep_track_point = prev_dep_track_point;
                    if let super::super::process::dependency::DependencyNode::DetLink {
                        prev, ..
                    } = dep
                    {
                        *prev
                    } else {
                        unreachable!("NOMINAL dependency allocated with DetLink shape")
                    }
                };
                if nominal_dep_track_point.is_some() {
                    proc_ctx.dep_link_mut(prev).dep_track_point = nominal_dep_track_point;
                }
                proc_ctx.update_dependency_branching_tag(dep_node);
            }
            *nominal_cont_dep_track_point = calc_alg_context
                .process_context_mut()
                .materialize_continue_dependency_track_point(dep_node);
        }
        dep_node
    }

    /// Port of `createAUTOMATCHOOSEDependency`. cpp 9993–9999.
    pub fn create_automat_choose_dependency(
        &mut self,
        and_dep_track_point: &mut TrackPointId,
        process_indi: &mut NodeId,
        con_des: ConDescId,
        prev_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node = Id::NONE;
        if self.conf_build_dependencies {
            dep_node = calc_alg_context
                .process_context_mut()
                .alloc_deterministic_dependency_node(DepKind::AutomatChoose);
            {
                let proc_ctx = calc_alg_context.process_context_mut();
                let dep = proc_ctx.dep_node_mut(dep_node);
                dep.init_deterministic_dependency_node(DepKind::AutomatChoose, con_des);
                dep.base_mut().dep_track_point = prev_dep_track_point;
                proc_ctx.update_dependency_branching_tag(dep_node);
            }
            *and_dep_track_point = calc_alg_context
                .process_context_mut()
                .materialize_continue_dependency_track_point(dep_node);
            let _ = process_indi;
        }
        dep_node
    }

    /// Port of `createSOMEDependency`. cpp 10001–10007.
    pub fn create_some_dependency(
        &mut self,
        some_dep_track_point: &mut TrackPointId,
        process_indi: &mut NodeId,
        con_des: ConDescId,
        prev_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node = Id::NONE;
        if self.conf_build_dependencies {
            dep_node = calc_alg_context
                .process_context_mut()
                .alloc_deterministic_dependency_node(DepKind::Some);
            {
                let proc_ctx = calc_alg_context.process_context_mut();
                let dep = proc_ctx.dep_node_mut(dep_node);
                dep.init_deterministic_dependency_node_indi(DepKind::Some, *process_indi, con_des);
                dep.base_mut().dep_track_point = prev_dep_track_point;
                proc_ctx.update_dependency_branching_tag(dep_node);
            }
            *some_dep_track_point = calc_alg_context
                .process_context_mut()
                .materialize_continue_dependency_track_point(dep_node);
        }
        dep_node
    }

    /// Port of `createSELFDependency`. cpp 10009–10015.
    pub fn create_self_dependency(
        &mut self,
        some_dep_track_point: &mut TrackPointId,
        process_indi: &mut NodeId,
        con_des: ConDescId,
        prev_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node = Id::NONE;
        if self.conf_build_dependencies {
            dep_node = calc_alg_context
                .process_context_mut()
                .alloc_deterministic_dependency_node(DepKind::Self_);
            {
                let proc_ctx = calc_alg_context.process_context_mut();
                let dep = proc_ctx.dep_node_mut(dep_node);
                dep.init_deterministic_dependency_node_indi(DepKind::Self_, *process_indi, con_des);
                dep.base_mut().dep_track_point = prev_dep_track_point;
                proc_ctx.update_dependency_branching_tag(dep_node);
            }
            *some_dep_track_point = calc_alg_context
                .process_context_mut()
                .materialize_continue_dependency_track_point(dep_node);
        }
        dep_node
    }

    /// Port of `createVALUEDependency`. cpp 10017–10023.
    pub fn create_value_dependency(
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
                .alloc_det_link_dependency_node(DepKind::Value);
            {
                let proc_ctx = calc_alg_context.process_context_mut();
                let prev = {
                    let dep = proc_ctx.dep_node_mut(dep_node);
                    dep.init_dependency_node_indi(DepKind::Value, *process_indi, con_des);
                    dep.base_mut().dep_track_point = prev_dep_track_point;
                    if let super::super::process::dependency::DependencyNode::DetLink {
                        prev, ..
                    } = dep
                    {
                        *prev
                    } else {
                        unreachable!("VALUE dependency allocated with DetLink shape")
                    }
                };
                proc_ctx.dep_link_mut(prev).dep_track_point = nominal_dep_track_point;
                proc_ctx.update_dependency_branching_tag(dep_node);
            }
            *value_dep_track_point = calc_alg_context
                .process_context_mut()
                .materialize_continue_dependency_track_point(dep_node);
        }
        dep_node
    }

    /// Port of `createROLEASSERTIONDependency`. cpp 10025–10031.
    pub fn create_role_assertion_dependency(
        &mut self,
        value_dep_track_point: &mut TrackPointId,
        process_indi: NodeId,
        prev_dep_track_point: TrackPointId,
        nominal_dep_track_point: TrackPointId,
        base_assertion_role: RoleId,
        base_assertion_indi: IndividualId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node = Id::NONE;
        if self.conf_build_dependencies {
            dep_node = calc_alg_context
                .process_context_mut()
                .alloc_det_link_dependency_node(DepKind::RoleAssertion);
            {
                let proc_ctx = calc_alg_context.process_context_mut();
                let prev = {
                    let dep = proc_ctx.dep_node_mut(dep_node);
                    // CDependencyFactory::createROLEASSERTIONDependency mirrors the
                    // VALUE/NEGVALUE one-link factory shape, but has no concept
                    // descriptor argument.
                    dep.init_dependency_node_indi(
                        DepKind::RoleAssertion,
                        process_indi,
                        ConDescId::NONE,
                    );
                    dep.base_mut().dep_track_point = prev_dep_track_point;
                    dep.base_mut().base_assertion_role = base_assertion_role;
                    dep.base_mut().base_assertion_individual = base_assertion_indi;
                    if let super::super::process::dependency::DependencyNode::DetLink {
                        prev, ..
                    } = dep
                    {
                        *prev
                    } else {
                        unreachable!("ROLEASSERTION dependency allocated with DetLink shape")
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

    /// Port of `createNEGVALUEDependency`. cpp 10041–10047.
    pub fn create_neg_value_dependency(
        &mut self,
        neg_value_dep_track_point: &mut TrackPointId,
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
                .alloc_det_link_dependency_node(DepKind::NegValue);
            {
                let proc_ctx = calc_alg_context.process_context_mut();
                let prev = {
                    let dep = proc_ctx.dep_node_mut(dep_node);
                    dep.init_dependency_node_indi(DepKind::NegValue, *process_indi, con_des);
                    dep.base_mut().dep_track_point = prev_dep_track_point;
                    if let super::super::process::dependency::DependencyNode::DetLink {
                        prev, ..
                    } = dep
                    {
                        *prev
                    } else {
                        unreachable!("NEGVALUE dependency allocated with DetLink shape")
                    }
                };
                proc_ctx.dep_link_mut(prev).dep_track_point = nominal_dep_track_point;
                proc_ctx.update_dependency_branching_tag(dep_node);
            }
            *neg_value_dep_track_point = calc_alg_context
                .process_context_mut()
                .materialize_continue_dependency_track_point(dep_node);
        }
        dep_node
    }

    /// Port of `createALLDependency`. cpp 10049–10055.
    pub fn create_all_dependency(
        &mut self,
        all_dep_track_point: &mut TrackPointId,
        process_indi: &mut NodeId,
        con_des: ConDescId,
        prev_dep_track_point: TrackPointId,
        link_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node = Id::NONE;
        if self.conf_build_dependencies {
            dep_node = calc_alg_context
                .process_context_mut()
                .alloc_det_link_dependency_node(DepKind::All);
            {
                let proc_ctx = calc_alg_context.process_context_mut();
                let prev = {
                    let dep = proc_ctx.dep_node_mut(dep_node);
                    dep.init_dependency_node_indi(DepKind::All, *process_indi, con_des);
                    dep.base_mut().dep_track_point = prev_dep_track_point;
                    if let super::super::process::dependency::DependencyNode::DetLink {
                        prev, ..
                    } = dep
                    {
                        *prev
                    } else {
                        unreachable!("ALL dependency allocated with DetLink shape")
                    }
                };
                proc_ctx.dep_link_mut(prev).dep_track_point = link_dep_track_point;
                proc_ctx.update_dependency_branching_tag(dep_node);
            }
            *all_dep_track_point = calc_alg_context
                .process_context_mut()
                .materialize_continue_dependency_track_point(dep_node);
        }
        dep_node
    }

    /// Port of `createFUNCTIONALDependency`. cpp 10083–10089.
    pub fn create_functional_dependency(
        &mut self,
        functional_continue_dep_track_point: &mut TrackPointId,
        process_indi: &mut NodeId,
        con_des: ConDescId,
        prev_dep_track_point: TrackPointId,
        prev_link1_dependency_track_point: TrackPointId,
        prev_link2_dependency_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node = Id::NONE;
        if self.conf_build_dependencies {
            dep_node = calc_alg_context
                .process_context_mut()
                .alloc_functional_dependency_node();
            {
                let proc_ctx = calc_alg_context.process_context_mut();
                let (prev1, prev2) = {
                    let dep = proc_ctx.dep_node_mut(dep_node);
                    dep.init_dependency_node_indi(DepKind::Functional, *process_indi, con_des);
                    dep.base_mut().dep_track_point = prev_dep_track_point;
                    if let super::super::process::dependency::DependencyNode::DetLink2 {
                        prev1,
                        prev2,
                        ..
                    } = dep
                    {
                        (*prev1, *prev2)
                    } else {
                        unreachable!("FUNCTIONAL dependency allocated with DetLink2 shape")
                    }
                };
                proc_ctx.dep_link_mut(prev1).dep_track_point = prev_link1_dependency_track_point;
                proc_ctx.dep_link_mut(prev2).dep_track_point = prev_link2_dependency_track_point;
                proc_ctx.update_dependency_branching_tag(dep_node);
            }
            *functional_continue_dep_track_point = calc_alg_context
                .process_context_mut()
                .materialize_continue_dependency_track_point(dep_node);
        }
        dep_node
    }

    /// Port of `createDISTINCTDependency`. cpp 10091–10097.
    pub fn create_distinct_dependency(
        &mut self,
        distinct_dep_track_point: &mut TrackPointId,
        process_indi: &mut NodeId,
        con_des: ConDescId,
        prev_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node = Id::NONE;
        if self.conf_build_dependencies {
            dep_node = calc_alg_context
                .process_context_mut()
                .alloc_deterministic_dependency_node(DepKind::Distinct);
            {
                let proc_ctx = calc_alg_context.process_context_mut();
                let dep = proc_ctx.dep_node_mut(dep_node);
                dep.init_deterministic_dependency_node_indi(
                    DepKind::Distinct,
                    *process_indi,
                    con_des,
                );
                dep.base_mut().dep_track_point = prev_dep_track_point;
                proc_ctx.update_dependency_branching_tag(dep_node);
            }
            *distinct_dep_track_point = calc_alg_context
                .process_context_mut()
                .materialize_continue_dependency_track_point(dep_node);
        }
        dep_node
    }

    /// Port of `createAUTOMATTRANSACTIONDependency`. cpp 10099–10105.
    pub fn create_automat_transaction_dependency(
        &mut self,
        all_dep_track_point: &mut TrackPointId,
        process_indi: &mut NodeId,
        con_des: ConDescId,
        prev_dep_track_point: TrackPointId,
        link_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node = Id::NONE;
        if self.conf_build_dependencies {
            dep_node = calc_alg_context
                .process_context_mut()
                .alloc_det_link_dependency_node(DepKind::AutomatTransaction);
            {
                let proc_ctx = calc_alg_context.process_context_mut();
                let prev = {
                    let dep = proc_ctx.dep_node_mut(dep_node);
                    dep.init_dependency_node_indi(
                        DepKind::AutomatTransaction,
                        *process_indi,
                        con_des,
                    );
                    dep.base_mut().dep_track_point = prev_dep_track_point;
                    if let super::super::process::dependency::DependencyNode::DetLink {
                        prev, ..
                    } = dep
                    {
                        *prev
                    } else {
                        unreachable!("AUTOMATTRANSACTION dependency allocated with DetLink shape")
                    }
                };
                proc_ctx.dep_link_mut(prev).dep_track_point = link_dep_track_point;
                proc_ctx.update_dependency_branching_tag(dep_node);
            }
            *all_dep_track_point = calc_alg_context
                .process_context_mut()
                .materialize_continue_dependency_track_point(dep_node);
        }
        dep_node
    }

    /// Port of `createATLEASTDependency`. cpp 10107–10113.
    pub fn create_atleast_dependency(
        &mut self,
        atleast_dep_track_point: &mut TrackPointId,
        process_indi: &mut NodeId,
        con_des: ConDescId,
        prev_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node = Id::NONE;
        if self.conf_build_dependencies {
            dep_node = calc_alg_context
                .process_context_mut()
                .alloc_deterministic_dependency_node(DepKind::AtLeast);
            {
                let proc_ctx = calc_alg_context.process_context_mut();
                let dep = proc_ctx.dep_node_mut(dep_node);
                dep.init_deterministic_dependency_node_indi(
                    DepKind::AtLeast,
                    *process_indi,
                    con_des,
                );
                dep.base_mut().dep_track_point = prev_dep_track_point;
                proc_ctx.update_dependency_branching_tag(dep_node);
            }
            *atleast_dep_track_point = calc_alg_context
                .process_context_mut()
                .materialize_continue_dependency_track_point(dep_node);
        }
        dep_node
    }

    /// Port of `createORDependency`. cpp 10115–10121.
    pub fn create_or_dependency(
        &mut self,
        process_indi: &mut NodeId,
        con_des: ConDescId,
        prev_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node = Id::NONE;
        if self.conf_build_dependencies {
            let branch_node = calc_alg_context.base.used_branch_tree_node();
            dep_node = calc_alg_context
                .process_context_mut()
                .alloc_or_dependency_node();
            {
                let proc_ctx = calc_alg_context.process_context_mut();
                let clash_track_point = {
                    let dep = proc_ctx.dep_node_mut(dep_node);
                    dep.init_dependency_node(DepKind::Or, con_des);
                    dep.base_mut().dep_track_point = prev_dep_track_point;
                    match dep {
                        super::super::process::dependency::DependencyNode::Or { nd, .. } => {
                            nd.branch_track_points = nd.clash_track_point;
                            nd.dependency_clashes = Id::NONE;
                            nd.branch_node = branch_node;
                            nd.branch_tag = 0;
                            nd.closed_track_point = Id::NONE;
                            nd.closing_track_point = Id::NONE;
                            nd.clash_track_point
                        }
                        _ => unreachable!("OR dependency allocated with Or shape"),
                    }
                };
                proc_ctx
                    .track_point_mut(clash_track_point)
                    .clashed_irrelevant = true;
                proc_ctx.update_dependency_branching_tags(dep_node);
            }
            let _ = process_indi;
        }
        dep_node
    }
}
