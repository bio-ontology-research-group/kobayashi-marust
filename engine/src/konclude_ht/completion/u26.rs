//! `completion::u26` — Incremental-expansion / compatibility family
//! (port unit #26 of 36).
//!
//! Faithful port of the 20 methods that the manifest (`01-completion-methods.md`,
//! "Unit 26") groups under the incremental (re)classification subsystem of Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`.
//! cpp source line ranges (1-based) per method are noted on each item.
//!
//! Methods (cpp order):
//!   * `initializeIncrementalIndividualExpansion`              [2937–3052]
//!   * `getNextIncrementalExpansionIndividual`                 [3058–3071]
//!   * `incrementalNodeExpansion`                              [3075–3084]
//!   * `requiresIncrementalNodeExpansion`                      [3088–3094]
//!   * `pruneIncrementalRemovedSuccessors`                     [3384–3431]
//!   * `checkCompatibilityUpdateDirectlyChangedPropagation`   [3476–3493]
//!   * `linkCreationDirectlyChangedNeighbourConnectionUpdate`  [3497–3508]
//!   * `establishDirectlyChangedNeighbourConnection`          [3512–3529]
//!   * `propagateDirectlyChangedNeighbourNodeConnection`      [3534–3634]
//!   * `searchDirectlyChangedNeighbourNodeConnection`         [3639–3702]
//!   * `clearDirectlyChangedNeighbourConnection`              [3706–3718]
//!   * `clearPropagatedDirectlyChangedNeighbourConnection`    [3722–3761]
//!   * `hasCompatibleConceptSetReuse`                         [4955–4972]
//!   * `hasCompatibleConceptSetSignature`                     [5960–6004]
//!   * `generateDebugIncrementalExpansionString`              [8014–8036]
//!   * `areVariablePropagationBindingsCompatible`             [17990–18013]
//!   * `getConceptsForCompatibleVariablePropagationBindings`  [18017–18050]
//!   * `getBindingsCompatibleConceptSetsHashValue`            [18262–18277]
//!   * `addIndividualToIncrementalCompatibilityCheckingQueue`  [27554–27563]
//!   * `addIndividualToIncrementalExpansionQueue`             [27565–27584]
//!
//! KONCLUDE-PORT-NOTE[ownership]: each method is a member of
//! `CCalculationTableauCompletionTaskHandleAlgorithm`, so it becomes `&mut self`
//! plus the threaded per-thread context `calc_alg_context: &mut
//! CalculationAlgorithmContextBase` (the C++ `CCalculationAlgorithmContextBase*`).
//! `CIndividualProcessNode*` value params become arena `NodeId`s resolved against
//! the context-owned `ProcessContext`
//! (`calc_alg_context.process_context().node(id)` for reads,
//! `…process_context_mut().node_mut(id)` for mutation — the W3.5 convention);
//! `CIndividualProcessNode*&` out/in-out → `&mut NodeId`; `CIndividual*` →
//! `IndividualId`; `CConcept*` → `ConceptId` (resolved against
//! `calc_alg_context.ontology_arenas()`); `CReapplyConceptLabelSet*` → `LabelSetId`.
//!
//! Deferral landscape. This unit is dominated by the per-node
//! `CIndividualNodeIncrementalExpansionData` satellite (the
//! `getIncrementalExpansionData(bool)` lazy getter and its
//! `isPreviousCompletionGraphCompatible` / `isDirectlyChanged` /
//! `hasDirectlyChangedNeighbourConnection` / `setDirectlyChangedNeighbourConnectionNode`
//! / `addNeighbourPropagatedDirectlyChanged` / incremental-expansion-list state) and
//! by `mIncExpHandler`
//! (`CIncrementalCompletionGraphCompatibleExpansionHandler`, an Algorithm-layer
//! stub). The satellite is `process::stubs::IncExpDataId`, a zero-size marker with no
//! method bodies and no node accessor yet (W2-DEFER[api]). Sixteen of the twenty
//! methods bottom out start-to-finish in that satellite (and in the
//! variable-binding-path subsystem `CVariableBindingPath` / `CVariableBinding`,
//! likewise unported), so they are kept PORT-PENDING with the faithful signature and
//! a structural transcription of the C++; logic is documented, never silently
//! dropped.
//!
//! Four methods port in full / as faithful control flow against the available
//! substrate:
//!   * `getBindingsCompatibleConceptSetsHashValue` (pure order-independent hash over
//!     concept tags) — FULLY PORTED;
//!   * `addIndividualToIncrementalCompatibilityCheckingQueue` (node queue-flag guard
//!     + databox queue getter) — FULLY PORTED bar the deferred `insertProcessIndiviudal`
//!     queue-method body + `STATINC` counter (the same W3-DEFER[api] shape as u04);
//!   * `linkCreationDirectlyChangedNeighbourConnectionUpdate` (pure sibling-call
//!     control flow over `establish*` / `propagate*`) — FULLY PORTED;
//!   * `incrementalNodeExpansion` (outer driver structure; the inner expand block is
//!     the deferred `getUpToDateIndividual` + queue re-add).

#![allow(dead_code)]
#![allow(unused_variables)]

use std::collections::{HashSet, VecDeque};

use super::super::model::substrate::{Cint64, Id, INVALID};
use super::super::model::{ConceptId, IndividualId};
use super::super::process::node::IndividualProcessNode;
use super::super::process::varbind::{VarBindingPathId, VariableBindingPath};
use super::super::process::{EdgeId, LabelSetId, NodeId};
use super::context::CalculationAlgorithmContextBase;

impl super::algorithm::CompletionTaskHandleAlgorithm {
    fn incremental_data_is_directly_changed_or_connected(
        calc_alg_context: &CalculationAlgorithmContextBase,
        inc_exp_data: super::super::process::stubs::IncExpDataId,
    ) -> bool {
        inc_exp_data.is_some()
            && (calc_alg_context
                .process_context()
                .inc_exp_data(inc_exp_data)
                .has_directly_changed_neighbour_connection()
                || calc_alg_context
                    .process_context()
                    .inc_exp_data(inc_exp_data)
                    .is_directly_changed())
    }

    fn individual_has_directly_changed_or_connected_incremental_data(
        calc_alg_context: &CalculationAlgorithmContextBase,
        individual_node: NodeId,
    ) -> bool {
        let inc_exp_data = calc_alg_context
            .process_context()
            .node_incremental_expansion_data_existing(individual_node);
        Self::incremental_data_is_directly_changed_or_connected(calc_alg_context, inc_exp_data)
    }

    fn individual_can_receive_directly_changed_connection(
        calc_alg_context: &CalculationAlgorithmContextBase,
        individual_node: NodeId,
    ) -> bool {
        let inc_exp_data = calc_alg_context
            .process_context()
            .node_incremental_expansion_data_existing(individual_node);
        inc_exp_data.is_none()
            || (!calc_alg_context
                .process_context()
                .inc_exp_data(inc_exp_data)
                .has_directly_changed_neighbour_connection()
                && !calc_alg_context
                    .process_context()
                    .inc_exp_data(inc_exp_data)
                    .is_directly_changed()
                && !calc_alg_context
                    .process_context()
                    .inc_exp_data(inc_exp_data)
                    .is_previous_completion_graph_compatible())
    }

    fn is_individual_node_previous_completion_graph_compatible_from_loaded_correspondence(
        individual_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let inc_exp_data = calc_alg_context
            .process_context()
            .node_incremental_expansion_data_existing(individual_node);
        let con_set = calc_alg_context
            .process_context()
            .node(individual_node)
            .use_reapply_con_label_set;
        let last_con_des = if con_set.is_some() {
            calc_alg_context
                .process_context()
                .label_set(con_set)
                .get_adding_sorted_concept_description_linker()
        } else {
            Id::NONE
        };
        let last_checked_con_des = calc_alg_context
            .process_context()
            .inc_exp_data(inc_exp_data)
            .get_last_compatible_checked_concept_descriptor();
        let mut compatible = calc_alg_context
            .process_context()
            .inc_exp_data(inc_exp_data)
            .is_previous_completion_graph_compatible();
        if !calc_alg_context
            .process_context()
            .node(individual_node)
            .has_partial_processing_restriction_flags(IndividualProcessNode::PRF_PURGEDBLOCKED)
            && last_checked_con_des != last_con_des
        {
            let prev_indi_node =
                Self::get_previous_deterministic_completion_graph_corresponding_individual_node(
                    individual_node,
                    calc_alg_context,
                );
            if prev_indi_node.is_some()
                && !calc_alg_context
                    .process_context()
                    .node(prev_indi_node)
                    .has_partial_processing_restriction_flags(
                        IndividualProcessNode::PRF_PURGEDBLOCKED,
                    )
            {
                let prev_con_set = calc_alg_context
                    .process_context()
                    .node(prev_indi_node)
                    .use_reapply_con_label_set;
                let mut incompatible_concepts = true;
                if con_set.is_some()
                    && prev_con_set.is_some()
                    && calc_alg_context
                        .process_context()
                        .label_set(con_set)
                        .get_concept_signature_value()
                        == calc_alg_context
                            .process_context()
                            .label_set(prev_con_set)
                            .get_concept_signature_value()
                    && calc_alg_context
                        .process_context()
                        .label_set(prev_con_set)
                        .get_concept_count()
                        == calc_alg_context
                            .process_context()
                            .label_set(con_set)
                            .get_concept_count()
                {
                    incompatible_concepts = false;
                    let mut con_set_it = calc_alg_context
                        .process_context()
                        .label_set_concept_label_set_iterator(con_set, true, false, false);
                    let mut prev_con_set_it = calc_alg_context
                        .process_context()
                        .label_set_concept_label_set_iterator(prev_con_set, true, false, false);
                    while con_set_it.has_next() && prev_con_set_it.has_next() {
                        let con_des = con_set_it.get_concept_descriptor();
                        let prev_con_des = prev_con_set_it.get_concept_descriptor();
                        if calc_alg_context
                            .process_context()
                            .con_desc(con_des)
                            .get_concept()
                            != calc_alg_context
                                .process_context()
                                .con_desc(prev_con_des)
                                .get_concept()
                            || calc_alg_context
                                .process_context()
                                .con_desc(con_des)
                                .is_negated()
                                != calc_alg_context
                                    .process_context()
                                    .con_desc(prev_con_des)
                                    .is_negated()
                        {
                            incompatible_concepts = true;
                        }
                        con_set_it.move_next(calc_alg_context.process_context());
                        prev_con_set_it.move_next(calc_alg_context.process_context());
                    }
                }
                if !incompatible_concepts {
                    compatible = true;
                }
            }
            let loc_inc_exp_data = calc_alg_context
                .process_context_mut()
                .node_incremental_expansion_data(individual_node, true);
            calc_alg_context
                .process_context_mut()
                .inc_exp_data_mut(loc_inc_exp_data)
                .set_previous_completion_graph_compatible(compatible)
                .set_last_compatible_checked_concept_descriptor(last_con_des);
        }
        compatible
    }

    fn get_previous_deterministic_completion_graph_task(
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> super::super::task::satisfiable_task::SatTaskId {
        let sat_calc_task = calc_alg_context.base.used_sat_calc_task;
        if sat_calc_task.is_none() {
            return Id::NONE;
        }
        let inc_adapter = calc_alg_context
            .satisfiable_task_incremental_consistency_testing_adapter(sat_calc_task);
        if inc_adapter.is_none() {
            return Id::NONE;
        }
        let prev_cons_data = calc_alg_context
            .inc_cons_testing_adapter(inc_adapter)
            .get_previous_consistence_data();
        if prev_cons_data.is_none() {
            return Id::NONE;
        }
        calc_alg_context
            .base
            .task_data(prev_cons_data)
            .get_deterministic_satisfiable_task()
    }

    fn get_previous_deterministic_completion_graph_corresponding_individual_node(
        individual_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        let inc_exp_data = calc_alg_context
            .process_context()
            .node_incremental_expansion_data_existing(individual_node);
        if inc_exp_data.is_none()
            || !calc_alg_context
                .process_context()
                .inc_exp_data(inc_exp_data)
                .is_previous_completion_graph_correspondence_individual_node_loaded()
        {
            let loc_inc_exp_data = calc_alg_context
                .process_context_mut()
                .node_incremental_expansion_data(individual_node, true);
            let prev_comp_graph_calc_task =
                Self::get_previous_deterministic_completion_graph_task(calc_alg_context);
            let prev_indi_node = if prev_comp_graph_calc_task.is_some() {
                let individual_node_id = calc_alg_context
                    .process_context()
                    .node(individual_node)
                    .individual_node_id();
                calc_alg_context
                    .base
                    .try_sat_calc_task(prev_comp_graph_calc_task)
                    .and_then(|task| task.processing_data_box_state())
                    .map(|data_box| {
                        data_box
                            .individual_process_node_vector()
                            .get_data(individual_node_id)
                    })
                    .unwrap_or(Id::NONE)
            } else {
                Id::NONE
            };
            calc_alg_context
                .process_context_mut()
                .inc_exp_data_mut(loc_inc_exp_data)
                .set_previous_completion_graph_correspondence_individual_node(prev_indi_node)
                .set_previous_completion_graph_correspondence_individual_node_loaded(true);
        }
        let inc_exp_data = calc_alg_context
            .process_context()
            .node_incremental_expansion_data_existing(individual_node);
        calc_alg_context
            .process_context()
            .inc_exp_data(inc_exp_data)
            .get_previous_completion_graph_correspondence_individual_node()
    }

    fn try_propagate_directly_changed_to_candidate(
        &mut self,
        candidate_node: NodeId,
        prop_indi_node: NodeId,
        queue_incremental_expansion: bool,
        prop_node_list: &mut VecDeque<NodeId>,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        if Self::individual_can_receive_directly_changed_connection(
            calc_alg_context,
            candidate_node,
        ) {
            let loc_candidate =
                self.get_localized_individual(candidate_node, false, calc_alg_context);
            if self.establish_directly_changed_neighbour_connection(
                loc_candidate,
                prop_indi_node,
                queue_incremental_expansion,
                calc_alg_context,
            ) {
                prop_node_list.push_back(loc_candidate);
                return true;
            }
        }
        false
    }

    // =======================================================================
    // Incremental individual-expansion initialization (cpp 2937–3052).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::initializeIncrementalIndividualExpansion`.
    /// cpp 2937–3052.
    ///
    /// One-time build of the node's incremental-expansion work list against the
    /// previous deterministic completion graph: (a) for the previous-graph
    /// correspondence node, replays every previous concept whose dependencies are all
    /// unchanged (`areAllDependentFactsUnchanged` → `addConceptToIndividual`); then
    /// (b) breadth-first walks the previous graph from this node over successors /
    /// connection-successors / merged individuals, collecting the not-yet-present
    /// nominal individuals into the expansion list; finally marks the list
    /// initialized and enqueues the node for incremental expansion.
    pub fn initialize_incremental_individual_expansion(
        &mut self,
        individual_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let inc_exp_data = calc_alg_context
            .process_context()
            .node_incremental_expansion_data_existing(individual_node);
        if inc_exp_data.is_some()
            && calc_alg_context
                .process_context()
                .inc_exp_data(inc_exp_data)
                .is_incremetnal_expansion_list_initialized()
        {
            return false;
        }

        let inc_exp_data = calc_alg_context
            .process_context_mut()
            .node_incremental_expansion_data(individual_node, true);

        let prev_indi_node =
            Self::get_previous_deterministic_completion_graph_corresponding_individual_node(
                individual_node,
                calc_alg_context,
            );

        let mut expansion_individuals = Vec::new();
        let mut replay_concepts = Vec::new();
        let current_individual_node_id = calc_alg_context
            .process_context()
            .node(individual_node)
            .individual_node_id();
        let prev_calc_task =
            Self::get_previous_deterministic_completion_graph_task(calc_alg_context);
        if prev_calc_task.is_some() {
            if let Some(prev_data_box) = calc_alg_context
                .base
                .try_sat_calc_task(prev_calc_task)
                .and_then(|task| task.processing_data_box_state())
            {
                if prev_indi_node.is_some() {
                    let con_set = calc_alg_context
                        .process_context()
                        .node(individual_node)
                        .use_reapply_con_label_set;
                    let prev_con_set = calc_alg_context
                        .process_context()
                        .node(prev_indi_node)
                        .use_reapply_con_label_set;
                    if con_set.is_some() && prev_con_set.is_some() {
                        let mut con_set_it = calc_alg_context
                            .process_context()
                            .label_set_concept_label_set_iterator(con_set, true, false, false);
                        let mut prev_con_set_it = calc_alg_context
                            .process_context()
                            .label_set_concept_label_set_iterator(prev_con_set, true, false, false);
                        while con_set_it.has_next() && prev_con_set_it.has_next() {
                            let con_tag = con_set_it.get_data_tag(
                                calc_alg_context.process_context(),
                                calc_alg_context.ontology_arenas(),
                            );
                            let prev_con_tag = prev_con_set_it.get_data_tag(
                                calc_alg_context.process_context(),
                                calc_alg_context.ontology_arenas(),
                            );
                            if con_tag == prev_con_tag {
                                con_set_it.move_next(calc_alg_context.process_context());
                                prev_con_set_it.move_next(calc_alg_context.process_context());
                            } else if prev_con_tag < con_tag {
                                let prev_con_des = prev_con_set_it.get_concept_descriptor();
                                let prev_con_dep_track_point = prev_con_set_it
                                    .get_dependency_track_point(calc_alg_context.process_context());
                                replay_concepts.push((
                                    calc_alg_context
                                        .process_context()
                                        .con_desc(prev_con_des)
                                        .get_concept(),
                                    calc_alg_context
                                        .process_context()
                                        .con_desc(prev_con_des)
                                        .is_negated(),
                                    prev_con_dep_track_point,
                                ));
                                prev_con_set_it.move_next(calc_alg_context.process_context());
                            } else {
                                con_set_it.move_next(calc_alg_context.process_context());
                            }
                        }

                        while prev_con_set_it.has_next() {
                            let prev_con_des = prev_con_set_it.get_concept_descriptor();
                            let prev_con_dep_track_point = prev_con_set_it
                                .get_dependency_track_point(calc_alg_context.process_context());
                            replay_concepts.push((
                                calc_alg_context
                                    .process_context()
                                    .con_desc(prev_con_des)
                                    .get_concept(),
                                calc_alg_context
                                    .process_context()
                                    .con_desc(prev_con_des)
                                    .is_negated(),
                                prev_con_dep_track_point,
                            ));
                            prev_con_set_it.move_next(calc_alg_context.process_context());
                        }
                    }
                }

                let mut searching_node_set: HashSet<Cint64> = HashSet::new();
                let mut searching_node_list: VecDeque<Cint64> = VecDeque::new();
                searching_node_set.insert(current_individual_node_id);
                searching_node_list.push_back(current_individual_node_id);

                while let Some(search_indi_node_id) = searching_node_list.pop_front() {
                    let search_indi_node = prev_data_box
                        .individual_process_node_vector()
                        .get_data(search_indi_node_id);
                    if search_indi_node.is_none() {
                        continue;
                    }

                    let search_node_ref = calc_alg_context.process_context().node(search_indi_node);
                    let nominal_indi = search_node_ref.nominal_individual();
                    if search_node_ref.individual_node_id() != current_individual_node_id
                        && nominal_indi.is_some()
                    {
                        let nominal_indi_id = calc_alg_context
                            .ontology_arenas()
                            .individual(nominal_indi)
                            .get_individual_id();
                        if calc_alg_context
                            .processing_data_box()
                            .individual_process_node_vector()
                            .get_data(-nominal_indi_id)
                            .is_none()
                        {
                            expansion_individuals.push(nominal_indi);
                        }
                    }

                    if (nominal_indi.is_none()
                        && search_node_ref.has_partial_processing_restriction_flags(
                            IndividualProcessNode::PRF_SUCCESSORNOMINALCONNECTION,
                        ))
                        || search_indi_node_id == current_individual_node_id
                    {
                        let mut succ_it = calc_alg_context
                            .process_context()
                            .node_successor_iterator(search_indi_node);
                        while succ_it.has_next() {
                            let succ_indi_id = succ_it.next_individual_id(true);
                            if searching_node_set.insert(succ_indi_id) {
                                searching_node_list.push_back(succ_indi_id);
                            }
                        }

                        let conn_set = calc_alg_context
                            .process_context()
                            .node_connection_successor_set_existing(search_indi_node);
                        if conn_set.is_some() {
                            let mut conn_it = calc_alg_context
                                .process_context()
                                .conn_succ_set(conn_set)
                                .get_connection_successor_iterator();
                            while conn_it.has_next() {
                                let conn_indi_id = conn_it.next(true);
                                if searching_node_set.insert(conn_indi_id) {
                                    searching_node_list.push_back(conn_indi_id);
                                }
                            }
                        }

                        let merge_hash = calc_alg_context
                            .process_context()
                            .node(search_indi_node)
                            .use_individual_merging_hash;
                        if merge_hash.is_some() {
                            let merged_ids: Vec<Cint64> = calc_alg_context
                                .process_context()
                                .individual_merging_hash(merge_hash)
                                .iter()
                                .filter_map(|(merged_indi_id, data)| {
                                    if data.is_merged_with_individual() {
                                        Some(*merged_indi_id)
                                    } else {
                                        None
                                    }
                                })
                                .collect();
                            for merged_indi_id in merged_ids {
                                if searching_node_set.insert(merged_indi_id) {
                                    searching_node_list.push_back(merged_indi_id);
                                }
                            }
                        }
                    }
                }
            }
        }

        for (concept, negated, dep_track_point) in replay_concepts {
            let mut rem_max_backtracking_count = 15;
            if self.are_all_dependent_facts_unchanged(
                individual_node,
                Id::NONE,
                dep_track_point,
                INVALID,
                &mut rem_max_backtracking_count,
                calc_alg_context,
            ) {
                let mut replay_node = individual_node;
                self.add_concept_to_individual(
                    concept,
                    negated,
                    &mut replay_node,
                    dep_track_point,
                    false,
                    false,
                    calc_alg_context,
                );
            }
        }

        {
            let data = calc_alg_context
                .process_context_mut()
                .inc_exp_data_mut(inc_exp_data);
            if !expansion_individuals.is_empty() {
                let exp_list = data.get_incremental_expansion_list(true).unwrap();
                exp_list.extend(expansion_individuals);
            }
            data.set_incremetnal_expansion_list_initialized(true);
        }
        self.add_individual_to_incremental_expansion_queue(individual_node, calc_alg_context);
        true
    }

    // =======================================================================
    // Incremental expansion individual cursor + node expansion
    // (cpp 3058–3094).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getNextIncrementalExpansionIndividual`.
    /// cpp 3058–3071.
    ///
    /// Returns the next previous-graph nominal individual queued for incremental
    /// expansion that does not yet have a node in the current graph (`Id::NONE` when
    /// none remain).
    pub fn get_next_incremental_expansion_individual(
        &mut self,
        individual_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> IndividualId {
        let inc_exp_data = calc_alg_context
            .process_context()
            .node_incremental_expansion_data_existing(individual_node);
        if inc_exp_data.is_none()
            || !calc_alg_context
                .process_context()
                .inc_exp_data(inc_exp_data)
                .requires_further_incremental_expansion()
        {
            return Id::NONE;
        }

        let inc_exp_data = calc_alg_context
            .process_context_mut()
            .node_incremental_expansion_data(individual_node, true);
        while calc_alg_context
            .process_context()
            .inc_exp_data(inc_exp_data)
            .requires_further_incremental_expansion()
        {
            let next_indi = calc_alg_context
                .process_context_mut()
                .inc_exp_data_mut(inc_exp_data)
                .take_next_incremental_expansion_individual();
            let next_indi_id = calc_alg_context
                .ontology_arenas()
                .individual(next_indi)
                .get_individual_id();
            if calc_alg_context
                .processing_data_box()
                .individual_process_node_vector()
                .get_data(-next_indi_id)
                .is_none()
            {
                return next_indi;
            }
        }
        Id::NONE
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::incrementalNodeExpansion`.
    /// cpp 3075–3084.
    ///
    /// Expands one queued incremental-expansion individual for `expandNode`: takes the
    /// next individual, loads/creates its up-to-date node, re-enqueues `expandNode`
    /// for any remaining work, and returns the freshly expanded node (`Id::NONE` when
    /// nothing remains to expand).
    pub fn incremental_node_expansion(
        &mut self,
        expand_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        // expIndi = getNextIncrementalExpansionIndividual(expandNode,ctx);
        // if expIndi:
        //   expandedIndiNode = getUpToDateIndividual(-expIndi->getIndividualID(),ctx);
        //   addIndividualToIncrementalExpansionQueue(expandNode,ctx);
        //   return expandedIndiNode;
        // return nullptr;
        let exp_indi =
            self.get_next_incremental_expansion_individual(expand_node, calc_alg_context);
        if exp_indi.is_some() {
            let exp_indi_id = calc_alg_context
                .ontology_arenas()
                .individual(exp_indi)
                .get_individual_id();
            let expanded_indi_node =
                self.get_up_to_date_individual_by_id(-exp_indi_id, calc_alg_context);
            self.add_individual_to_incremental_expansion_queue(expand_node, calc_alg_context);
            return expanded_indi_node;
        }
        Id::NONE
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::requiresIncrementalNodeExpansion`.
    /// cpp 3088–3094.
    ///
    /// True iff the node's previous-graph correspondence is incompatible AND it is
    /// flagged directly-changed-neighbour-connection or directly-changed.
    pub fn requires_incremental_node_expansion(
        &mut self,
        individual_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // incExpData = individualNode->getIncrementalExpansionData(false);
        let inc_exp_data = calc_alg_context
            .process_context()
            .node_incremental_expansion_data_existing(individual_node);
        // if !incExpData->isPreviousCompletionGraphCompatible()
        //    && (incExpData->hasDirectlyChangedNeighbourConnection() || incExpData->isDirectlyChanged()):
        //   return true;
        // return false;
        //
        // W2.7 reconcile: the `CIndividualNodeIncrementalExpansionData` satellite is now
        // arena-backed (`process::reapply_sat`); the change predicate goes live via the
        // process-context accessor. C++ derefs `incExpData` unconditionally here (the
        // node always carries the data when this is reached) — mirrored, no guard.
        let pc = calc_alg_context.process_context();
        if !pc
            .inc_exp_data(inc_exp_data)
            .is_previous_completion_graph_compatible()
            && (pc
                .inc_exp_data(inc_exp_data)
                .has_directly_changed_neighbour_connection()
                || pc.inc_exp_data(inc_exp_data).is_directly_changed())
        {
            return true;
        }
        false
    }

    // =======================================================================
    // Pruning of incrementally removed successors (cpp 3384–3431).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::pruneIncrementalRemovedSuccessors`.
    /// cpp 3384–3431.
    ///
    /// Breadth-first prunes (marks `PRFPURGEDBLOCKED` + eliminates blocked
    /// individuals) the blockable subtree reachable from `indi` over connection-
    /// successors and ordinary successors, skipping nominals and any node already in
    /// `pruningNodeSet` / `compatibleNominalNodeSet`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: the two caller-owned
    /// `CPROCESSINGSET<cint64>*` arguments become caller-owned `HashSet<Cint64>`
    /// values. The local `CPROCESSINGLIST<CIndividualProcessNode*>` worklist becomes
    /// `VecDeque<NodeId>`.
    pub fn prune_incremental_removed_successors(
        &mut self,
        indi: &mut NodeId,
        compatible_nominal_node_set: &HashSet<Cint64>,
        pruning_node_set: &mut HashSet<Cint64>,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let mut pruning_node_list = VecDeque::new();
        pruning_node_list.push_back(*indi);

        while let Some(pruning_node) = pruning_node_list.pop_front() {
            if pruning_node != *indi
                && !calc_alg_context
                    .process_context()
                    .node(pruning_node)
                    .has_partial_processing_restriction_flags(
                        IndividualProcessNode::PRF_PURGEDBLOCKED,
                    )
            {
                calc_alg_context
                    .process_context_mut()
                    .node_mut(pruning_node)
                    .add_processing_restriction_flags(IndividualProcessNode::PRF_PURGEDBLOCKED);
                self.eliminiate_blocked_individuals(pruning_node, calc_alg_context);
            }

            let conn_ids = {
                let conn_succ_set = calc_alg_context
                    .process_context()
                    .node_connection_successor_set_existing(pruning_node);
                if conn_succ_set.is_some()
                    && calc_alg_context
                        .process_context()
                        .conn_succ_set(conn_succ_set)
                        .get_connection_successor_count()
                        > 0
                {
                    let mut iterator = calc_alg_context
                        .process_context()
                        .conn_succ_set(conn_succ_set)
                        .get_connection_successor_iterator();
                    let mut ids = Vec::new();
                    while iterator.has_next() {
                        ids.push(iterator.next(true));
                    }
                    ids
                } else {
                    Vec::new()
                }
            };

            for conn_id in conn_ids {
                if !pruning_node_set.contains(&conn_id)
                    && !compatible_nominal_node_set.contains(&conn_id)
                {
                    let nom_indi = self.get_up_to_date_individual_by_id(conn_id, calc_alg_context);
                    if nom_indi.is_some()
                        && !calc_alg_context
                            .process_context()
                            .node(nom_indi)
                            .is_nominal_individual_node()
                        && !calc_alg_context
                            .process_context()
                            .node(nom_indi)
                            .has_partial_processing_restriction_flags(
                                IndividualProcessNode::PRF_PURGEDBLOCKED,
                            )
                    {
                        pruning_node_set.insert(conn_id);
                        let loc_nom_indi =
                            self.get_localized_individual(nom_indi, false, calc_alg_context);
                        pruning_node_list.push_back(loc_nom_indi);
                    }
                }
            }

            let _anc_depth = calc_alg_context
                .process_context()
                .node(pruning_node)
                .individual_ancestor_depth();
            let succ_links = {
                let mut iterator = calc_alg_context
                    .process_context()
                    .node_successor_iterator(pruning_node);
                let mut links = Vec::new();
                while iterator.has_next() {
                    links.push(iterator.next_link(true));
                }
                links
            };

            for succ_link in succ_links {
                let mut pruning_source = pruning_node;
                let succ_indi =
                    self.get_successor_individual(&mut pruning_source, succ_link, calc_alg_context);
                if succ_indi.is_some()
                    && !calc_alg_context
                        .process_context()
                        .node(succ_indi)
                        .is_nominal_individual_node()
                    && !calc_alg_context
                        .process_context()
                        .node(succ_indi)
                        .has_partial_processing_restriction_flags(
                            IndividualProcessNode::PRF_PURGEDBLOCKED,
                        )
                {
                    let succ_indi_id = calc_alg_context
                        .process_context()
                        .node(succ_indi)
                        .individual_node_id();
                    if !pruning_node_set.contains(&succ_indi_id)
                        && !compatible_nominal_node_set.contains(&succ_indi_id)
                    {
                        pruning_node_set.insert(succ_indi_id);
                        let loc_succ_indi =
                            self.get_localized_individual(succ_indi, false, calc_alg_context);
                        pruning_node_list.push_back(loc_succ_indi);
                    }
                }
            }
        }
    }

    // =======================================================================
    // Directly-changed neighbour-connection propagation (cpp 3476–3761).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::checkCompatibilityUpdateDirectlyChangedPropagation`.
    /// cpp 3476–3493.
    ///
    /// Asks `mIncExpHandler` whether the node is previous-graph compatible: if so,
    /// clears the propagated directly-changed-neighbour connection; otherwise (re)queues
    /// incremental expansion for a directly-changed node and, when neither directly-
    /// changed nor changed-connection yet, searches for a directly-changed neighbour and
    /// establishes + propagates the connection.
    pub fn check_compatibility_update_directly_changed_propagation(
        &mut self,
        individual_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let compatible =
            Self::is_individual_node_previous_completion_graph_compatible_from_loaded_correspondence(
                individual_node,
                calc_alg_context,
            );
        let inc_exp_data = calc_alg_context
            .process_context()
            .node_incremental_expansion_data_existing(individual_node);
        if compatible {
            self.clear_propagated_directly_changed_neighbour_connection(
                individual_node,
                true,
                calc_alg_context,
            );
        } else {
            if calc_alg_context
                .process_context()
                .inc_exp_data(inc_exp_data)
                .is_directly_changed()
            {
                self.add_individual_to_incremental_expansion_queue(
                    individual_node,
                    calc_alg_context,
                );
            }
            if !calc_alg_context
                .process_context()
                .inc_exp_data(inc_exp_data)
                .is_directly_changed()
                && !calc_alg_context
                    .process_context()
                    .inc_exp_data(inc_exp_data)
                    .has_directly_changed_neighbour_connection()
            {
                let directly_changed_conn_node = self
                    .search_directly_changed_neighbour_node_connection(
                        individual_node,
                        calc_alg_context,
                    );
                if directly_changed_conn_node.is_some()
                    && self.establish_directly_changed_neighbour_connection(
                        individual_node,
                        directly_changed_conn_node,
                        true,
                        calc_alg_context,
                    )
                {
                    self.propagate_directly_changed_neighbour_node_connection(
                        individual_node,
                        true,
                        calc_alg_context,
                    );
                }
            }
        }
        compatible
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::linkCreationDirectlyChangedNeighbourConnectionUpdate`.
    /// cpp 3497–3508. FULLY PORTED (pure sibling-call control flow).
    ///
    /// On a new link between `sourceIndi` and `destIndi`, establishes + propagates the
    /// directly-changed-neighbour connection in both directions; returns whether either
    /// direction updated.
    ///
    /// KONCLUDE-PORT-NOTE: the C++ ignores its `queueIncrementalExpansion` parameter,
    /// hard-coding `true` in both `establishDirectlyChangedNeighbourConnection` calls —
    /// transcribed verbatim (the param is intentionally unused).
    pub fn link_creation_directly_changed_neighbour_connection_update(
        &mut self,
        source_indi: NodeId,
        dest_indi: NodeId,
        queue_incremental_expansion: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut updated_neighbour_connection = false;
        if self.establish_directly_changed_neighbour_connection(
            source_indi,
            dest_indi,
            true,
            calc_alg_context,
        ) {
            self.propagate_directly_changed_neighbour_node_connection(
                source_indi,
                true,
                calc_alg_context,
            );
            updated_neighbour_connection = true;
        }
        if self.establish_directly_changed_neighbour_connection(
            dest_indi,
            source_indi,
            true,
            calc_alg_context,
        ) {
            self.propagate_directly_changed_neighbour_node_connection(
                dest_indi,
                true,
                calc_alg_context,
            );
            updated_neighbour_connection = true;
        }
        updated_neighbour_connection
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::establishDirectlyChangedNeighbourConnection`.
    /// cpp 3512–3529.
    ///
    /// If `individualNode` is not itself changed/changed-connection but
    /// `neighbourNodeCandidate` is, records the candidate as this node's directly-
    /// changed-connection node and back-registers this node on the candidate; queues
    /// incremental expansion when this node is a nominal. Returns whether the
    /// connection was established.
    pub fn establish_directly_changed_neighbour_connection(
        &mut self,
        individual_node: NodeId,
        neighbour_node_candidate: NodeId,
        queue_incremental_expansion: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // incExpData = individualNode->getIncrementalExpansionData(false);
        // if !incExpData || (!incExpData->hasDirectlyChangedNeighbourConnection() && !incExpData->isDirectlyChanged()):
        //   candIncExpData = neighbourNodeCandidate->getIncrementalExpansionData(false);
        //   if candIncExpData && (candIncExpData->hasDirectlyChangedNeighbourConnection() || candIncExpData->isDirectlyChanged()):
        //     locIncExpData = individualNode->getIncrementalExpansionData(true);
        //     locNeighbourNodeCandidate = getLocalizedIndividual(neighbourNodeCandidate,false,ctx);
        //     locIncExpData->setDirectlyChangedNeighbourConnectionNode(locNeighbourNodeCandidate);
        //     locCandIncExpData = locNeighbourNodeCandidate->getIncrementalExpansionData(true);
        //     locCandIncExpData->addNeighbourPropagatedDirectlyChanged(individualNode);
        //     if queueIncrementalExpansion && individualNode->getNominalIndividual():
        //       addIndividualToIncrementalExpansionQueue(individualNode,ctx);
        //     return true;
        // return false;
        //
        let inc_exp_data = calc_alg_context
            .process_context()
            .node_incremental_expansion_data_existing(individual_node);
        if inc_exp_data.is_none()
            || (!calc_alg_context
                .process_context()
                .inc_exp_data(inc_exp_data)
                .has_directly_changed_neighbour_connection()
                && !calc_alg_context
                    .process_context()
                    .inc_exp_data(inc_exp_data)
                    .is_directly_changed())
        {
            let cand_inc_exp_data = calc_alg_context
                .process_context()
                .node_incremental_expansion_data_existing(neighbour_node_candidate);
            if Self::incremental_data_is_directly_changed_or_connected(
                calc_alg_context,
                cand_inc_exp_data,
            ) {
                let loc_inc_exp_data = calc_alg_context
                    .process_context_mut()
                    .node_incremental_expansion_data(individual_node, true);
                let loc_neighbour_node_candidate = self.get_localized_individual(
                    neighbour_node_candidate,
                    false,
                    calc_alg_context,
                );
                calc_alg_context
                    .process_context_mut()
                    .inc_exp_data_mut(loc_inc_exp_data)
                    .set_directly_changed_neighbour_connection_node(loc_neighbour_node_candidate);

                let loc_cand_inc_exp_data = calc_alg_context
                    .process_context_mut()
                    .node_incremental_expansion_data(loc_neighbour_node_candidate, true);
                calc_alg_context
                    .process_context_mut()
                    .inc_exp_data_mut(loc_cand_inc_exp_data)
                    .add_neighbour_propagated_directly_changed(individual_node);

                if queue_incremental_expansion
                    && calc_alg_context
                        .process_context()
                        .node(individual_node)
                        .is_nominal_individual_node()
                {
                    self.add_individual_to_incremental_expansion_queue(
                        individual_node,
                        calc_alg_context,
                    );
                }
                return true;
            }
        }
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::propagateDirectlyChangedNeighbourNodeConnection`.
    /// cpp 3534–3634.
    ///
    /// Breadth-first propagates the directly-changed-neighbour connection outward from
    /// `individualNode` over successors, connection-successors and — for nodes carrying
    /// `PRFSUCCESSORNOMINALCONNECTION` — blocked / processing-blocked / follow-set /
    /// blocker / following individuals, establishing the connection on each newly
    /// reached node.
    pub fn propagate_directly_changed_neighbour_node_connection(
        &mut self,
        individual_node: NodeId,
        queue_incremental_expansion: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut prop_node_list = VecDeque::new();
        prop_node_list.push_back(individual_node);
        let mut propagated_directly_changed = false;

        while let Some(prop_indi_node) = prop_node_list.pop_front() {
            let mut succ_it = calc_alg_context
                .process_context()
                .node_successor_iterator(prop_indi_node);
            while succ_it.has_next() {
                let succ_link = succ_it.next_link(true);
                let mut prop_source = prop_indi_node;
                let succ_indi =
                    self.get_successor_individual(&mut prop_source, succ_link, calc_alg_context);
                if self.try_propagate_directly_changed_to_candidate(
                    succ_indi,
                    prop_indi_node,
                    queue_incremental_expansion,
                    &mut prop_node_list,
                    calc_alg_context,
                ) {
                    propagated_directly_changed = true;
                }
            }

            let conn_set = calc_alg_context
                .process_context()
                .node_connection_successor_set_existing(prop_indi_node);
            if conn_set.is_some() {
                let mut conn_it = calc_alg_context
                    .process_context()
                    .conn_succ_set(conn_set)
                    .get_connection_successor_iterator();
                while conn_it.has_next() {
                    let conn_id = conn_it.next(true);
                    let conn_indi_node =
                        self.get_up_to_date_individual_by_id(conn_id, calc_alg_context);
                    if self.try_propagate_directly_changed_to_candidate(
                        conn_indi_node,
                        prop_indi_node,
                        queue_incremental_expansion,
                        &mut prop_node_list,
                        calc_alg_context,
                    ) {
                        propagated_directly_changed = true;
                    }
                }
            }

            if calc_alg_context
                .process_context()
                .node(prop_indi_node)
                .has_partial_processing_restriction_flags(
                super::super::process::node::IndividualProcessNode::PRF_SUCCESSORNOMINALCONNECTION,
            ) {
                let blocked_nodes: Vec<NodeId> = calc_alg_context
                    .process_context()
                    .node(prop_indi_node)
                    .get_blocked_individuals_linker()
                    .to_vec();
                for blocked_indi_node in blocked_nodes {
                    let blocked_indi_node =
                        self.get_up_to_date_individual(blocked_indi_node, calc_alg_context);
                    if self.try_propagate_directly_changed_to_candidate(
                        blocked_indi_node,
                        prop_indi_node,
                        queue_incremental_expansion,
                        &mut prop_node_list,
                        calc_alg_context,
                    ) {
                        propagated_directly_changed = true;
                    }
                }

                let processing_blocked_nodes: Vec<NodeId> = calc_alg_context
                    .process_context()
                    .node(prop_indi_node)
                    .get_processing_blocked_individuals_linker()
                    .to_vec();
                for blocked_indi_node in processing_blocked_nodes {
                    let blocked_indi_node =
                        self.get_up_to_date_individual(blocked_indi_node, calc_alg_context);
                    if self.try_propagate_directly_changed_to_candidate(
                        blocked_indi_node,
                        prop_indi_node,
                        queue_incremental_expansion,
                        &mut prop_node_list,
                        calc_alg_context,
                    ) {
                        propagated_directly_changed = true;
                    }
                }

                let follow_set = calc_alg_context
                    .process_context()
                    .node_blocking_followers(prop_indi_node);
                for blocked_indi_node_id in follow_set {
                    let blocked_indi_node = self
                        .get_up_to_date_individual_by_id(blocked_indi_node_id, calc_alg_context);
                    if self.try_propagate_directly_changed_to_candidate(
                        blocked_indi_node,
                        prop_indi_node,
                        queue_incremental_expansion,
                        &mut prop_node_list,
                        calc_alg_context,
                    ) {
                        propagated_directly_changed = true;
                    }
                }

                let blocker_indi_node = calc_alg_context
                    .process_context()
                    .node(prop_indi_node)
                    .blocker_individual_node();
                if blocker_indi_node.is_some() {
                    let blocker_indi_node =
                        self.get_up_to_date_individual(blocker_indi_node, calc_alg_context);
                    if self.try_propagate_directly_changed_to_candidate(
                        blocker_indi_node,
                        prop_indi_node,
                        queue_incremental_expansion,
                        &mut prop_node_list,
                        calc_alg_context,
                    ) {
                        propagated_directly_changed = true;
                    }
                }

                let following_indi_node = calc_alg_context
                    .process_context()
                    .node(prop_indi_node)
                    .following_individual_node();
                if following_indi_node.is_some() {
                    let following_indi_node =
                        self.get_up_to_date_individual(following_indi_node, calc_alg_context);
                    if self.try_propagate_directly_changed_to_candidate(
                        following_indi_node,
                        prop_indi_node,
                        queue_incremental_expansion,
                        &mut prop_node_list,
                        calc_alg_context,
                    ) {
                        propagated_directly_changed = true;
                    }
                }
            }
        }
        propagated_directly_changed
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::searchDirectlyChangedNeighbourNodeConnection`.
    /// cpp 3639–3702.
    ///
    /// Scans the node's successors, connection-successors and (for
    /// `PRFSUCCESSORNOMINALCONNECTION` nodes) blocked / follow-set / blocker /
    /// following individuals for the first one already flagged directly-changed or
    /// changed-connection, returning it (`Id::NONE` when none).
    pub fn search_directly_changed_neighbour_node_connection(
        &mut self,
        individual_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        let mut succ_it = calc_alg_context
            .process_context()
            .node_successor_iterator(individual_node);
        while succ_it.has_next() {
            let succ_link = succ_it.next_link(true);
            let mut source = individual_node;
            let succ_indi = self.get_successor_individual(&mut source, succ_link, calc_alg_context);
            if Self::individual_has_directly_changed_or_connected_incremental_data(
                calc_alg_context,
                succ_indi,
            ) {
                return succ_indi;
            }
        }

        let conn_set = calc_alg_context
            .process_context()
            .node_connection_successor_set_existing(individual_node);
        if conn_set.is_some() {
            let mut conn_it = calc_alg_context
                .process_context()
                .conn_succ_set(conn_set)
                .get_connection_successor_iterator();
            while conn_it.has_next() {
                let conn_id = conn_it.next(true);
                let conn_indi_node =
                    self.get_up_to_date_individual_by_id(conn_id, calc_alg_context);
                if Self::individual_has_directly_changed_or_connected_incremental_data(
                    calc_alg_context,
                    conn_indi_node,
                ) {
                    return conn_indi_node;
                }
            }
        }

        if calc_alg_context
            .process_context()
            .node(individual_node)
            .has_partial_processing_restriction_flags(
                super::super::process::node::IndividualProcessNode::PRF_SUCCESSORNOMINALCONNECTION,
            )
        {
            let blocked_nodes: Vec<NodeId> = calc_alg_context
                .process_context()
                .node(individual_node)
                .get_blocked_individuals_linker()
                .to_vec();
            for blocked_indi_node in blocked_nodes {
                let blocked_indi_node =
                    self.get_up_to_date_individual(blocked_indi_node, calc_alg_context);
                if Self::individual_has_directly_changed_or_connected_incremental_data(
                    calc_alg_context,
                    blocked_indi_node,
                ) {
                    return blocked_indi_node;
                }
            }

            let processing_blocked_nodes: Vec<NodeId> = calc_alg_context
                .process_context()
                .node(individual_node)
                .get_processing_blocked_individuals_linker()
                .to_vec();
            for blocked_indi_node in processing_blocked_nodes {
                let blocked_indi_node =
                    self.get_up_to_date_individual(blocked_indi_node, calc_alg_context);
                if Self::individual_has_directly_changed_or_connected_incremental_data(
                    calc_alg_context,
                    blocked_indi_node,
                ) {
                    return blocked_indi_node;
                }
            }

            let follow_set = calc_alg_context
                .process_context()
                .node_blocking_followers(individual_node);
            for blocked_indi_node_id in follow_set {
                let blocked_indi_node =
                    self.get_up_to_date_individual_by_id(blocked_indi_node_id, calc_alg_context);
                if Self::individual_has_directly_changed_or_connected_incremental_data(
                    calc_alg_context,
                    blocked_indi_node,
                ) {
                    return blocked_indi_node;
                }
            }

            let blocker_indi_node = calc_alg_context
                .process_context()
                .node(individual_node)
                .blocker_individual_node();
            if blocker_indi_node.is_some() {
                let blocker_indi_node =
                    self.get_up_to_date_individual(blocker_indi_node, calc_alg_context);
                if Self::individual_has_directly_changed_or_connected_incremental_data(
                    calc_alg_context,
                    blocker_indi_node,
                ) {
                    return blocker_indi_node;
                }
            }

            let following_indi_node = calc_alg_context
                .process_context()
                .node(individual_node)
                .following_individual_node();
            if following_indi_node.is_some() {
                let following_indi_node =
                    self.get_up_to_date_individual(following_indi_node, calc_alg_context);
                if Self::individual_has_directly_changed_or_connected_incremental_data(
                    calc_alg_context,
                    following_indi_node,
                ) {
                    return following_indi_node;
                }
            }
        }
        Id::NONE
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::clearDirectlyChangedNeighbourConnection`.
    /// cpp 3706–3718.
    ///
    /// Clears this node's directly-changed-neighbour-connection node (queueing a
    /// nominal compatibility recheck) and then clears the propagated connection;
    /// returns whether anything was cleared.
    pub fn clear_directly_changed_neighbour_connection(
        &mut self,
        individual_node: NodeId,
        queue_compatibility_checks: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let inc_exp_data = calc_alg_context
            .process_context()
            .node_incremental_expansion_data_existing(individual_node);
        if inc_exp_data.is_some()
            && calc_alg_context
                .process_context()
                .inc_exp_data(inc_exp_data)
                .has_directly_changed_neighbour_connection()
        {
            let loc_inc_exp_data = calc_alg_context
                .process_context_mut()
                .node_incremental_expansion_data(individual_node, true);
            calc_alg_context
                .process_context_mut()
                .inc_exp_data_mut(loc_inc_exp_data)
                .set_directly_changed_neighbour_connection_node(Id::NONE);
            if queue_compatibility_checks
                && calc_alg_context
                    .process_context()
                    .node(individual_node)
                    .is_nominal_individual_node()
            {
                self.add_individual_to_incremental_compatibility_checking_queue(
                    individual_node,
                    calc_alg_context,
                );
            }
            self.clear_propagated_directly_changed_neighbour_connection(
                individual_node,
                true,
                calc_alg_context,
            );
            return true;
        }
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::clearPropagatedDirectlyChangedNeighbourConnection`.
    /// cpp 3722–3761.
    ///
    /// Breadth-first clears the directly-changed-neighbour connection on every node
    /// that propagated it from `individualNode` (matching the connection back-pointer),
    /// re-queueing nominal compatibility checks as it goes; the C++ returns `false`
    /// unconditionally (the local `propCleared` is computed but not returned).
    pub fn clear_propagated_directly_changed_neighbour_connection(
        &mut self,
        individual_node: NodeId,
        queue_compatibility_checks: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut _prop_cleared = false;
        let inc_exp_data = calc_alg_context
            .process_context()
            .node_incremental_expansion_data_existing(individual_node);
        if inc_exp_data.is_some()
            && calc_alg_context
                .process_context()
                .inc_exp_data(inc_exp_data)
                .has_neighbour_propagated_directly_changed()
        {
            let mut clear_prop_node_list = VecDeque::new();
            clear_prop_node_list.push_back(individual_node);

            while let Some(clear_prop_indi_node) = clear_prop_node_list.pop_front() {
                let clear_inc_exp_data = calc_alg_context
                    .process_context()
                    .node_incremental_expansion_data_existing(clear_prop_indi_node);
                if clear_inc_exp_data.is_none() {
                    continue;
                }
                let prop_indi_node_list = calc_alg_context
                    .process_context()
                    .inc_exp_data(clear_inc_exp_data)
                    .neighbour_propagated_directly_changed_snapshot();
                if !prop_indi_node_list.is_empty() {
                    let clear_inc_exp_data = calc_alg_context
                        .process_context_mut()
                        .node_incremental_expansion_data(clear_prop_indi_node, true);

                    for prop_node in prop_indi_node_list {
                        let prop_node = self.get_up_to_date_individual(prop_node, calc_alg_context);
                        let prop_inc_exp_data = calc_alg_context
                            .process_context()
                            .node_incremental_expansion_data_existing(prop_node);
                        if prop_inc_exp_data.is_some()
                            && calc_alg_context
                                .process_context()
                                .inc_exp_data(prop_inc_exp_data)
                                .has_directly_changed_neighbour_connection()
                        {
                            let conn_node = calc_alg_context
                                .process_context()
                                .inc_exp_data(prop_inc_exp_data)
                                .get_directly_changed_neighbour_connection_node();
                            let conn_node_id = calc_alg_context
                                .process_context()
                                .node(conn_node)
                                .individual_node_id();
                            let clear_prop_node_id = calc_alg_context
                                .process_context()
                                .node(clear_prop_indi_node)
                                .individual_node_id();
                            if conn_node_id == clear_prop_node_id {
                                _prop_cleared = true;
                                let prop_node = self.get_localized_individual(
                                    prop_node,
                                    false,
                                    calc_alg_context,
                                );
                                let prop_inc_exp_data = calc_alg_context
                                    .process_context_mut()
                                    .node_incremental_expansion_data(prop_node, true);
                                let has_neighbour_propagated = calc_alg_context
                                    .process_context()
                                    .inc_exp_data(prop_inc_exp_data)
                                    .has_neighbour_propagated_directly_changed();
                                calc_alg_context
                                    .process_context_mut()
                                    .inc_exp_data_mut(prop_inc_exp_data)
                                    .set_directly_changed_neighbour_connection_node(Id::NONE);
                                if has_neighbour_propagated {
                                    clear_prop_node_list.push_back(prop_node);
                                }
                                if queue_compatibility_checks
                                    && calc_alg_context
                                        .process_context()
                                        .node(individual_node)
                                        .is_nominal_individual_node()
                                {
                                    self.add_individual_to_incremental_compatibility_checking_queue(
                                        individual_node,
                                        calc_alg_context,
                                    );
                                }
                            }
                        }
                    }
                    calc_alg_context
                        .process_context_mut()
                        .inc_exp_data_mut(clear_inc_exp_data)
                        .clear_neighbour_propagated_directly_changed_list();
                }
            }
        }
        false
    }

    // =======================================================================
    // Compatible concept-set reuse / signature checks (cpp 4955–6004).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::hasCompatibleConceptSetReuse`.
    /// cpp 4955–4972.
    ///
    /// True iff `subConceptSet` is a label-subset of `reuseNodeCand`'s concept set and
    /// none of the super-set's concepts are signature-blocking-critical for the reuse
    /// candidate (marking the candidate's signature blocking invalid otherwise).
    pub fn has_compatible_concept_set_reuse(
        &mut self,
        indi_node: NodeId,
        sub_concept_set: LabelSetId,
        reuse_node_cand: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let super_concept_set = calc_alg_context
            .process_context()
            .node(reuse_node_cand)
            .use_reapply_con_label_set;
        let is_subset = self.is_label_concept_sub_set(
            sub_concept_set,
            super_concept_set,
            None,
            None,
            calc_alg_context,
        );
        if !is_subset {
            return false;
        }

        let mut super_con_set_it = calc_alg_context
            .process_context()
            .label_set_concept_label_set_iterator(super_concept_set, false, false, false);
        while super_con_set_it.has_next() {
            let con_des = super_con_set_it.next(true, calc_alg_context.process_context());
            let dep_track_point = calc_alg_context
                .process_context()
                .con_desc(con_des)
                .get_dependency_track_point();
            if self.is_concept_signature_blocking_critical(
                con_des,
                dep_track_point,
                calc_alg_context,
            ) {
                calc_alg_context
                    .process_context_mut()
                    .node_mut(indi_node)
                    .set_invalid_signature_blocking(true);
                return false;
            }
        }
        true
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::hasCompatibleConceptSetSignature`.
    /// cpp 5960–6004.
    ///
    /// Checks whether `conSet` is an order-/content-compatible suffix of
    /// `compatibleTestNode`'s concept set (aligning the sorted adding-linkers by the
    /// size difference), bailing to `false` on any signature-blocking-critical concept
    /// (which also marks `blockingNode`'s signature blocking invalid) or a missing
    /// concept once ordering compatibility is lost.
    pub fn has_compatible_concept_set_signature(
        &mut self,
        blocking_node: &mut NodeId,
        con_set: LabelSetId,
        compatible_test_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let comp_test_con_set = calc_alg_context
            .process_context()
            .node(compatible_test_node)
            .use_reapply_con_label_set;
        let con_count = calc_alg_context
            .process_context()
            .label_set(con_set)
            .get_concept_count();
        let comp_test_con_count = if comp_test_con_set.is_some() {
            calc_alg_context
                .process_context()
                .label_set(comp_test_con_set)
                .get_concept_count()
        } else {
            0
        };
        if con_count <= 0 || comp_test_con_count < con_count {
            return false;
        }

        let mut diff_count = comp_test_con_count - con_count;
        let mut comp_test_con_des_it = calc_alg_context
            .process_context()
            .label_set(comp_test_con_set)
            .get_adding_sorted_concept_description_linker();
        let mut con_des_it = calc_alg_context
            .process_context()
            .label_set(con_set)
            .get_adding_sorted_concept_description_linker();
        while diff_count > 0 {
            comp_test_con_des_it = calc_alg_context
                .process_context()
                .con_desc(comp_test_con_des_it)
                .get_next_concept_descriptor();
            diff_count -= 1;
        }

        let mut ordering_compatible = true;
        while ordering_compatible && con_des_it.is_some() {
            let concept = calc_alg_context
                .process_context()
                .con_desc(con_des_it)
                .get_concept();
            let con_neg = calc_alg_context
                .process_context()
                .con_desc(con_des_it)
                .is_negated();
            if comp_test_con_des_it.is_some()
                && calc_alg_context
                    .process_context()
                    .con_desc(comp_test_con_des_it)
                    .get_concept()
                    == concept
                && calc_alg_context
                    .process_context()
                    .con_desc(comp_test_con_des_it)
                    .is_negated()
                    == con_neg
            {
                let dep_track_point = calc_alg_context
                    .process_context()
                    .con_desc(con_des_it)
                    .get_dependency_track_point();
                if self.is_concept_signature_blocking_critical(
                    con_des_it,
                    dep_track_point,
                    calc_alg_context,
                ) {
                    calc_alg_context
                        .process_context_mut()
                        .node_mut(*blocking_node)
                        .set_invalid_signature_blocking(true);
                    return false;
                }
                con_des_it = calc_alg_context
                    .process_context()
                    .con_desc(con_des_it)
                    .get_next_concept_descriptor();
                comp_test_con_des_it = calc_alg_context
                    .process_context()
                    .con_desc(comp_test_con_des_it)
                    .get_next_concept_descriptor();
            } else {
                ordering_compatible = false;
            }
        }

        if !ordering_compatible {
            while con_des_it.is_some() {
                let concept = calc_alg_context
                    .process_context()
                    .con_desc(con_des_it)
                    .get_concept();
                let con_neg = calc_alg_context
                    .process_context()
                    .con_desc(con_des_it)
                    .is_negated();
                let dep_track_point = calc_alg_context
                    .process_context()
                    .con_desc(con_des_it)
                    .get_dependency_track_point();
                if self.is_concept_signature_blocking_critical(
                    con_des_it,
                    dep_track_point,
                    calc_alg_context,
                ) {
                    calc_alg_context
                        .process_context_mut()
                        .node_mut(*blocking_node)
                        .set_invalid_signature_blocking(true);
                    return false;
                }
                if !self.label_set_contains_concept_resolved(
                    con_set,
                    concept,
                    con_neg,
                    calc_alg_context,
                ) {
                    return false;
                }
                con_des_it = calc_alg_context
                    .process_context()
                    .con_desc(con_des_it)
                    .get_next_concept_descriptor();
            }
        }
        true
    }

    // =======================================================================
    // Debug rendering (cpp 8014–8036).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::generateDebugIncrementalExpansionString`.
    /// cpp 8014–8036.
    ///
    /// Renders the node's incremental-expansion status (compatible / directly-changed-
    /// connection / directly-changed-node), the changed-connection neighbour id, and
    /// the expansion priority into a debug string.
    pub fn generate_debug_incremental_expansion_string(
        &mut self,
        indi: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> String {
        let inc_exp_data = calc_alg_context
            .process_context()
            .node_incremental_expansion_data_existing(indi);
        if inc_exp_data.is_none() {
            return String::new();
        }

        let inc = calc_alg_context
            .process_context()
            .inc_exp_data(inc_exp_data);
        let mut status_strings = Vec::new();
        if inc.is_previous_completion_graph_compatible() {
            status_strings.push("compatible");
        }
        if inc.has_directly_changed_neighbour_connection() {
            status_strings.push("directly-changed-connection");
        }
        if inc.is_directly_changed() {
            status_strings.push("directly-changed-node");
        }

        let dir_changed_neigh_conn_node = inc.get_directly_changed_neighbour_connection_node();
        let dir_changed_neigh_conn_node_id = if dir_changed_neigh_conn_node.is_some() {
            calc_alg_context
                .process_context()
                .node(dir_changed_neigh_conn_node)
                .individual_node_id()
                .to_string()
        } else {
            "-".to_string()
        };

        format!(
            "Incremental-Expansion-Status: {}\r\n Directly-Changed-Connection-Neighbour: {}\r\n Expansion-Priority: {}",
            status_strings.join(", "),
            dir_changed_neigh_conn_node_id,
            inc.get_expansion_priority()
        )
    }

    // =======================================================================
    // Variable-propagation-binding compatibility (cpp 17990–18050).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::areVariablePropagationBindingsCompatible`.
    /// cpp 17990–18013.
    ///
    /// Two variable-binding paths are compatible iff they share a propagation id, or no
    /// variable bound in the smaller path is bound to a different individual in the
    /// larger path.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: `CVariableBindingPath*` → `VarBindingPathId`; the
    /// `CVariableBinding` / `CVariableBindingDescriptor` chain it walks is now the
    /// arena-backed variable-binding-path subsystem (`process::varbind`), reached
    /// through `calc_alg_context.process_context()`.
    pub fn are_variable_propagation_bindings_compatible(
        &mut self,
        var_bind_path1: VarBindingPathId,
        var_bind_path2: VarBindingPathId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let pc = calc_alg_context.process_context();
        // if varBindPath1->getPropagationID() == varBindPath2->getPropagationID(): return true;
        if pc.vbpath(var_bind_path1).get_propagation_id()
            == pc.vbpath(var_bind_path2).get_propagation_id()
        {
            return true;
        }
        // pick lessVarBindPath / moreVarBindPath by getVariableBindingCount();
        let count1 = VariableBindingPath::get_variable_binding_count(pc, var_bind_path1);
        let count2 = VariableBindingPath::get_variable_binding_count(pc, var_bind_path2);
        let (less_var_bind_path, more_var_bind_path) = if count1 <= count2 {
            (var_bind_path1, var_bind_path2)
        } else {
            (var_bind_path2, var_bind_path1)
        };
        // for lessVarBindDes in lessVarBindPath->getVariableBindingDescriptorLinker():
        //   variable  = lessVarBindDes->getVariableBinding()->getBindedVariable();
        //   boundIndi = lessVarBindDes->getVariableBinding()->getBindedIndividual();
        //   for moreVarBindDes in moreVarBindPath->getVariableBindingDescriptorLinker():
        //     if moreBinding->getBindedVariable() == variable
        //        && moreBinding->getBindedIndividual()->getIndividualNodeID() != boundIndi->getIndividualNodeID(): return false;
        let mut less_var_bind_des = pc
            .vbpath(less_var_bind_path)
            .get_variable_binding_descriptor_linker();
        while less_var_bind_des.is_some() {
            let less_binding = pc.var_binding_des(less_var_bind_des).get_variable_binding();
            let variable = pc.var_binding(less_binding).get_binded_variable();
            let bound_indi = pc.var_binding(less_binding).get_binded_individual();
            let bound_indi_node_id = pc.node(bound_indi).individual_node_id();
            let mut more_var_bind_des = pc
                .vbpath(more_var_bind_path)
                .get_variable_binding_descriptor_linker();
            while more_var_bind_des.is_some() {
                let more_binding = pc.var_binding_des(more_var_bind_des).get_variable_binding();
                if pc.var_binding(more_binding).get_binded_variable() == variable {
                    let more_bound_indi = pc.var_binding(more_binding).get_binded_individual();
                    if pc.node(more_bound_indi).individual_node_id() != bound_indi_node_id {
                        return false;
                    }
                }
                more_var_bind_des = pc.var_binding_des(more_var_bind_des).get_next();
            }
            less_var_bind_des = pc.var_binding_des(less_var_bind_des).get_next();
        }
        true
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getConceptsForCompatibleVariablePropagationBindings`.
    /// cpp 18017–18050.
    ///
    /// Collects the trigger concepts of every concept-variable-binding-path-set on
    /// `individualNode` whose binding path is compatible (per
    /// `areVariablePropagationBindingsCompatible`) with `varBindPath`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: returns the C++ `QSet<CConcept*>` as a
    /// de-duplicated `Vec<ConceptId>`; iteration order is irrelevant to the callers,
    /// which treat it as a set.
    pub fn get_concepts_for_compatible_variable_propagation_bindings(
        &mut self,
        individual_node: &mut NodeId,
        var_bind_path: VarBindingPathId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> Vec<ConceptId> {
        let candidates: Vec<(ConceptId, Vec<VarBindingPathId>)> = {
            let pc = calc_alg_context.process_context();
            let con_var_bind_set_hash =
                pc.node(*individual_node).use_concept_var_bind_path_set_hash;
            if con_var_bind_set_hash.is_none() {
                return Vec::new();
            }

            let mut candidates = Vec::new();
            for hash_data in pc
                .con_var_bind_path_set_hash(con_var_bind_set_hash)
                .map
                .values()
            {
                let var_bind_set = hash_data.use_variable_binding_path_set;
                if var_bind_set.is_none() {
                    continue;
                }
                let con_des = pc.vbpath_set(var_bind_set).get_concept_descriptor();
                if con_des.is_none() {
                    continue;
                }

                let concept = pc.con_desc(con_des).get_concept();
                let paths = pc
                    .vbpath_set(var_bind_set)
                    .get_variable_binding_path_map()
                    .map
                    .values()
                    .filter_map(|map_data| {
                        let var_bind_des = map_data.get_variable_binding_path_descriptor();
                        if var_bind_des.is_some() {
                            let path = pc.vbpath_des(var_bind_des).get_variable_binding_path();
                            if path.is_some() {
                                return Some(path);
                            }
                        }
                        None
                    })
                    .collect::<Vec<_>>();
                candidates.push((concept, paths));
            }
            candidates
        };

        let mut concept_set = Vec::new();
        for (concept, paths) in candidates {
            let mut concepts_var_binds_compatible = false;
            for con_var_bind_path in paths {
                if self.are_variable_propagation_bindings_compatible(
                    var_bind_path,
                    con_var_bind_path,
                    calc_alg_context,
                ) {
                    concepts_var_binds_compatible = true;
                    break;
                }
            }
            if concepts_var_binds_compatible && !concept_set.contains(&concept) {
                concept_set.push(concept);
            }
        }
        concept_set
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getBindingsCompatibleConceptSetsHashValue`.
    /// cpp 18262–18277. FULLY PORTED.
    ///
    /// Order-independent hash of a set of concept sets: `|sets| + Σ_set (|set| +
    /// Σ_concept tag) * |set|`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: the C++ `const QSet<QSet<CConcept*>>&` becomes
    /// `&[Vec<ConceptId>]`; the inner/outer iteration order is irrelevant (the
    /// accumulation is commutative), so the hash matches the C++ regardless of
    /// container ordering.
    pub fn get_bindings_compatible_concept_sets_hash_value(
        &mut self,
        associated_concept_sets: &[Vec<ConceptId>],
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> Cint64 {
        let mut hash_value: Cint64 = associated_concept_sets.len() as Cint64;
        for con_set in associated_concept_sets {
            let mut con_set_hash_value: Cint64 = con_set.len() as Cint64;
            for &concept in con_set {
                con_set_hash_value += calc_alg_context
                    .ontology_arenas()
                    .concept(concept)
                    .get_concept_tag();
            }
            hash_value += con_set_hash_value * con_set.len() as Cint64;
        }
        hash_value
    }

    // =======================================================================
    // Incremental processing-queue insertion (cpp 27554–27584).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addIndividualToIncrementalCompatibilityCheckingQueue`.
    /// cpp 27554–27563.
    ///
    /// Enqueues an un-queued nominal node onto the incremental-compatibility-checking
    /// queue; returns whether it was enqueued.
    pub fn add_individual_to_incremental_compatibility_checking_queue(
        &mut self,
        individual: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let is_queued = calc_alg_context
            .process_context()
            .node(individual)
            .is_incremental_compatibility_checking_queued();
        let is_nominal = calc_alg_context
            .process_context()
            .node(individual)
            .is_nominal_individual_node();
        if !is_queued && is_nominal {
            calc_alg_context
                .process_context_mut()
                .node_mut(individual)
                .set_incremental_compatibility_checking_queued(true);
            let inc_comp_checking_queue =
                calc_alg_context.get_incremental_compatibility_checking_queue(true);
            calc_alg_context
                .process_context_mut()
                .indi_depth_queue_insert(inc_comp_checking_queue, individual);
            // W3-DEFER[api]: STATINC(INDINODESADDEDPROCESSINGQUEUECOUNT,calcAlgContext);
            return true;
        }
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addIndividualToIncrementalExpansionQueue`.
    /// cpp 27565–27584.
    ///
    /// Enqueues an un-queued node onto the incremental-expansion-list-initializing
    /// queue (when its expansion list is not yet initialized) or, once initialized and
    /// further expansion is required, onto the priority incremental-expansion queue at
    /// the node's next expansion priority; returns whether it was enqueued.
    pub fn add_individual_to_incremental_expansion_queue(
        &mut self,
        individual: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W2.7/W158/W159 reconcile: the `CIndividualNodeIncrementalExpansionData`
        // satellite (`process::reapply_sat`) and both target queues are now
        // arena-backed, so the branch selection and insertions are live. `STATINC`
        // remains the only deferred leaf here.
        //
        // if !individual->isIncrementalExpansionQueued():
        if !calc_alg_context
            .process_context()
            .node(individual)
            .is_incremental_expansion_queued()
        {
            // incExpData = individual->getIncrementalExpansionData(false);
            let inc_exp_data = calc_alg_context
                .process_context()
                .node_incremental_expansion_data_existing(individual);
            // if !incExpData || !incExpData->isIncremetnalExpansionListInitialized():
            let list_initialized = inc_exp_data.is_some()
                && calc_alg_context
                    .process_context()
                    .inc_exp_data(inc_exp_data)
                    .is_incremetnal_expansion_list_initialized();
            if !list_initialized {
                // individual->setIncrementalExpansionQueued(true);
                calc_alg_context
                    .process_context_mut()
                    .node_mut(individual)
                    .set_incremental_expansion_queued(true);
                // incExpInitQueue = ctx->getProcessingDataBox()->getIncrementalExpansionInitializingProcessingQueue(true);
                let inc_exp_init_queue =
                    calc_alg_context.get_incremental_expansion_initializing_processing_queue(true);
                calc_alg_context
                    .process_context_mut()
                    .indi_depth_queue_insert(inc_exp_init_queue, individual);
                // W3-DEFER[macro]: STATINC(INDINODESADDEDPROCESSINGQUEUECOUNT, ctx);
                return true;
            } else if calc_alg_context
                .process_context()
                .inc_exp_data(inc_exp_data)
                .requires_further_incremental_expansion()
            {
                // individual->setIncrementalExpansionQueued(true);
                calc_alg_context
                    .process_context_mut()
                    .node_mut(individual)
                    .set_incremental_expansion_queued(true);
                // nextExpPriority = incExpData->getNextIncrementalExpansionPriority();
                let next_exp_priority = calc_alg_context
                    .process_context()
                    .inc_exp_data(inc_exp_data)
                    .get_next_incremental_expansion_priority();
                // incExpQueue = ctx->getProcessingDataBox()->getIncrementalExpansionProcessingQueue(true);
                let inc_exp_queue =
                    calc_alg_context.get_incremental_expansion_processing_queue(true);
                calc_alg_context
                    .process_context_mut()
                    .indi_custom_priority_queue_insert(
                        inc_exp_queue,
                        next_exp_priority,
                        individual,
                    );
                // W3-DEFER[macro]: STATINC(INDINODESADDEDPROCESSINGQUEUECOUNT, ctx);
                return true;
            }
        }
        false
    }
}
