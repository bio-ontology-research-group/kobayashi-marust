//! `completion::u19` — port unit #19 of the completion task-handle algorithm
//! (family: Blocking (pairwise / label-optimized / dynamic); 13 methods,
//! cpp ranges 17698–19322).
//!
//! Source (READ-ONLY): Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`.
//! Ported methods (in cpp order):
//!   - `hasOptimizedBlockingB2AutomateTransitionOperands`           [17698]
//!   - `isLabelConceptOptimizedBlocking`                            [18488]
//!   - `isLabelConceptSubSetBlocking`                               [18882]
//!   - `isLabelConceptEqualBlocking`                                [18896]
//!   - `isLabelConceptEqualPairwiseBlocking`                        [18904]
//!   - `isIndividualNodeBlocking`                                   [18927]
//!   - `detectIndividualNodeBlockedStatus`                          [18991]
//!   - `getBlockingIndividualNode`                                  [19121]
//!   - `continueIndividualNodeBlock`                                [19139]
//!   - `signatureCachedIndividualNodeBlock`                         [19172]
//!   - `clearBlockingCache`                                         [19193]
//!   - `getAncestorBlockingIndividualNode`                          [19199]
//!   - `getAnywhereBlockingIndividualNode`                          [19251]
//!
//! KONCLUDE-PORT-NOTE[ownership]: pointers become arena ids
//! (`CIndividualProcessNode*` → `NodeId`, `CConceptDescriptor*` → `ConDescId`,
//! `CConcept*` → `ConceptId`, `CRole*` → `RoleId`, `CReapplyConceptLabelSet*` →
//! `LabelSetId`, `CIndividualLinkEdge*` → `EdgeId`,
//! `CIndividualNodeBlockingTestData*` → `IndiBlockDataId`); the `calcAlgContext`
//! pointer becomes a threaded `&mut CalculationAlgorithmContextBase`. Per the W3.5
//! accessor convention a C++ `indi->getX()` resolves to
//! `calc_alg_context.process_context().node(id).get_x()` (read) /
//! `…process_context_mut().node_mut(id).set_x(v)` (mutate); the static
//! `concept->...` resolves through `calc_alg_context.ontology_arenas().concept(id)`;
//! a `CReapplyConceptLabelSet*` resolves through
//! `calc_alg_context.process_context().label_set(id)`; the databox is reached via
//! `calc_alg_context.processing_data_box_mut()`.
//!
//! KONCLUDE-PORT-NOTE[api]: the dynamic-blocking driver hangs off three SATELLITE
//! kinds that are still `process::stubs` markers with no methods —
//! `CIndividualNodeBlockingTestData` (`IndiBlockDataId`),
//! `CSignatureBlockingIndividualNodeConceptExpansionData` (`SigBlockConExpDataId`)
//! and `CBlockingAlternativeData`. Every `blockData->...` /
//! `sigBlockExpData->...` / `blockAltData->...` deref, the `CNodeSwitchHistory`
//! min-tag lookup, and the `CSuccessorRoleIterator` / `CReapplyQueueIterator` /
//! `CRoleSuccessorLinkIterator` / `CReapplyConceptLabelSetIterator` traversals
//! (whose iterator types are W2-DEFER stubs without `hasNext`/`next`) are marked
//! `// W6-DEFER[api]` with a control-flow-preserving placeholder. The branch/loop
//! structure, the node flag ops, the concept-operator dispatch, the label-set
//! count/contains tests, the databox getters and the `self.x(...)` sibling calls
//! are reproduced verbatim. No logic is dropped — only the unported satellite /
//! stub-iterator dereferences are stubbed.
//!
//! PORT-PENDING: the cross-unit Generic-helper siblings are not yet ported
//! (`is_label_concept_sub_set`, `is_label_concept_equal_set`,
//! `is_pairwise_label_concept_equal_set`, `contains_individual_node_concepts`,
//! `has_individuals_link`, `is_individual_node_concept_label_set_modified`) along
//! with the ancestor/successor/up-to-date/localize accessors
//! (`get_ancestor_individual`, `get_successor_individual`,
//! `get_up_to_date_individual{,_by_id}`, `get_localized_individual{,_by_id}`), the
//! saturation/nominal siblings (`detect_individual_node_saturation_cached`,
//! `propagate_individual_node_nominal_connection_status_to_ancestors`), the
//! propagation-binding blocking siblings
//! (`is_nominal_variable_propagation_binding_sub_set`,
//! `is_anonymous_variable_propagation_binding_analogous_path`), the unit-20
//! anywhere/hash search + successor-restriction siblings
//! (`get_anywhere_blocking_individual_node{,_linked_canidate_hashed,_canidate_hashed}`,
//! `propagate_indirect_successor_blocking`, `reactivate_indirect_blocked_successors`,
//! `add_individual_to_blocking_update_review_processing_queue`), and the unit-18
//! `establish_individual_node_signature_blocking`. They are invoked as `self.x(...)`
//! per the port convention with the faithful C++ argument list; the exact ported
//! signatures reconcile when those units land.

#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_mut)]

use super::super::model::op::{
    CCALL, CCAQSOME, CCATLEAST, CCATMOST, CCFS_ALL_AQALL_TYPE, CCFS_AQALL_TYPE, CCFS_AQAND_TYPE,
    CCSOME,
};
use super::super::model::substrate::{Cint64, Id, INVALID};
use super::super::model::{ConceptId, RoleId};
use super::super::process::node::IndividualProcessNode;
use super::super::process::reapply_sat::{
    BlockingAltDataId, BlockingAlternativeSignatureBlockingCandidateData,
    IndividualNodeBlockingTestData,
};
use super::super::process::stubs::IndiBlockDataId;
use super::super::process::{ConDescId, LabelSetId, NodeId, TrackPointId};

use super::context::CalculationAlgorithmContextBase;

/// The C++ `CBlockingAlternativeData**` out-parameter; the only concrete
/// subclass currently ported is `CBlockingAlternativeSignatureBlockingCandidateData`.
type BlockingAlternativeDataHandle = BlockingAltDataId;

impl super::algorithm::CompletionTaskHandleAlgorithm {
    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::hasOptimizedBlockingB2AutomateTransitionOperands`.
    ///
    /// Fully ported: the operand recursion / role match dispatch over `CConcept`
    /// and the `vConSet->containsConcept` test all resolve against the ported
    /// terminology + label-set arenas.
    pub fn has_optimized_blocking_b2_automate_transition_operands(
        &mut self,
        concept: ConceptId,
        role: RoleId,
        v_con_set: LabelSetId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W6-DEFER[api]: STATINC(OPTIMIZEDBLOCKINGB2AUTOMATETRANSACTIONTESTCOUNT,calcAlgContext);
        // cint64 opCode = concept->getOperatorCode();  (computed, unused in C++)
        let _op_code = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operator_code();
        let con_operator = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_concept_operator();
        if con_operator.has_partial_operator_code_flag(CCFS_AQAND_TYPE) {
            // recursive
            let op_list = calc_alg_context
                .ontology_arenas()
                .concept(concept)
                .get_operand_list()
                .to_vec();
            for op_link in op_list {
                let op_concept = op_link.target;
                if !self.has_optimized_blocking_b2_automate_transition_operands(
                    op_concept,
                    role,
                    v_con_set,
                    calc_alg_context,
                ) {
                    return false;
                }
            }
        } else if con_operator.has_partial_operator_code_flag(CCFS_AQALL_TYPE) {
            let con_role = calc_alg_context
                .ontology_arenas()
                .concept(concept)
                .get_role();
            if con_role == role {
                let op_list = calc_alg_context
                    .ontology_arenas()
                    .concept(concept)
                    .get_operand_list()
                    .to_vec();
                for op_link in op_list {
                    let op_concept = op_link.target;
                    if !self.label_set_contains_concept_resolved(
                        v_con_set,
                        op_concept,
                        false,
                        calc_alg_context,
                    ) {
                        return false;
                    }
                }
            }
        }
        true
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::isLabelConceptOptimizedBlocking`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: the B2 test now uses the live
    /// `CSuccessorRoleHash` iterator for the ancestor-role traversal and the live
    /// per-role `CReapplyQueueIterator` from the blocker's reapply hash. The B3/B5
    /// blocker-successor cardinality walks use the live `CRoleSuccessorLinkIterator`.
    /// B4a's successor-count subloop remains deferred. The B6 and B4
    /// `CReapplyConceptLabelSetIterator` walks are live through LS-1 / W2.7 and are
    /// reproduced against the ported label/concept arenas; B4a's successor-count
    /// subloop remains deferred with the role-successor-link iterator.
    pub fn is_label_concept_optimized_blocking(
        &mut self,
        test_indi: NodeId,
        blocking_indi: NodeId,
        block_data: IndiBlockDataId,
        test_continue_blocking: bool,
        block_alt_data: &mut BlockingAlternativeDataHandle,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W6-DEFER[api]: STATINC(OPTIMIZEDBLOCKINGTESTCOUNT,calcAlgContext);
        let mut w_node = test_indi;
        let w_pred_node = blocking_indi;

        let w_sub_con_set = calc_alg_context
            .process_context_mut()
            .node_mut(w_node)
            .get_reapply_concept_label_set(false);
        let w_pred_super_con_set = calc_alg_context
            .process_context_mut()
            .node_mut(w_pred_node)
            .get_reapply_concept_label_set(false);
        let mut first_not_entailed_con_des: ConDescId = Id::NONE;
        // B1 test
        let mut equal_set = false;
        let sub_set = self.is_label_concept_sub_set(
            w_sub_con_set,
            w_pred_super_con_set,
            Some(&mut first_not_entailed_con_des),
            Some(&mut equal_set),
            calc_alg_context,
        );
        if !sub_set {
            return false;
        }

        let mut v_node = self.get_ancestor_individual(&mut w_node, calc_alg_context);
        let v_con_set = calc_alg_context
            .process_context_mut()
            .node_mut(v_node)
            .get_reapply_concept_label_set(false);
        // B2 test

        let anc_role_hash = calc_alg_context
            .process_context()
            .node(w_node)
            .use_succ_role_hash;
        if anc_role_hash.is_none() {
            // no inverse roles
            return true;
        }
        // assume blocking is possible
        let mut blocked = true;

        let mut violating_b2_restrictions: Cint64 = 0;
        let mut violating_non_det_b2_restrictions: Cint64 = 0;

        let v_node_individual_id = calc_alg_context
            .process_context()
            .node(v_node)
            .individual_node_id();
        let mut anc_role_it1 = calc_alg_context
            .process_context()
            .node_successor_role_iterator(w_node, v_node_individual_id);
        while anc_role_it1.has_next() && blocked {
            let link = anc_role_it1.next(true);
            if link.is_none() {
                continue;
            }
            // from w to v is a edge labeled with r, w is an inv(r)-successor of v
            let role = calc_alg_context
                .process_context()
                .edge(link)
                .get_link_role();
            // B2, (ALL r. C) in w'
            let mut reapply_qu_it = calc_alg_context
                .process_context_mut()
                .node_role_reapply_iterator(w_pred_node, role, false);
            while reapply_qu_it.has_next() && blocked {
                let reapply_con_des = reapply_qu_it.next(calc_alg_context.process_context(), true);
                if reapply_con_des.is_none() {
                    continue;
                }
                let con_des = calc_alg_context
                    .process_context()
                    .reapply_con_desc(reapply_con_des)
                    .get_concept_descriptor();
                let concept = calc_alg_context
                    .process_context()
                    .con_desc(con_des)
                    .get_concept();
                let con_neg = calc_alg_context
                    .process_context()
                    .con_desc(con_des)
                    .is_negated();
                let con_op_code = calc_alg_context
                    .ontology_arenas()
                    .concept(concept)
                    .get_operator_code();
                let con_operator = calc_alg_context
                    .ontology_arenas()
                    .concept(concept)
                    .get_concept_operator();
                if (!con_neg && con_operator.has_partial_operator_code_flag(CCFS_ALL_AQALL_TYPE))
                    || (con_neg && con_op_code == CCSOME)
                {
                    let op_linker = calc_alg_context
                        .ontology_arenas()
                        .concept(concept)
                        .get_operand_list()
                        .to_vec();
                    for op_link in op_linker {
                        if !blocked {
                            break;
                        }
                        let op_concept = op_link.target;
                        let op_con_neg = op_link.negated ^ con_neg;
                        if !self.label_set_contains_concept_resolved(
                            v_con_set,
                            op_concept,
                            op_con_neg,
                            calc_alg_context,
                        ) {
                            blocked = false;
                            let dep_track_point = calc_alg_context
                                .process_context()
                                .con_desc(con_des)
                                .get_dependency_track_point();
                            let non_det_dependency = dep_track_point.is_some()
                                && calc_alg_context
                                    .process_context()
                                    .track_point(dep_track_point)
                                    .get_branching_tag()
                                    > 0;
                            violating_b2_restrictions += 1;
                            if non_det_dependency {
                                violating_non_det_b2_restrictions += 1;
                            }
                        }
                    }
                } else if !con_neg
                    && con_operator.has_partial_operator_code_flag(CCFS_AQAND_TYPE)
                    && !self.has_optimized_blocking_b2_automate_transition_operands(
                        concept,
                        role,
                        v_con_set,
                        calc_alg_context,
                    )
                {
                    blocked = false;
                    let dep_track_point = calc_alg_context
                        .process_context()
                        .con_desc(con_des)
                        .get_dependency_track_point();
                    let non_det_dependency = dep_track_point.is_some()
                        && calc_alg_context
                            .process_context()
                            .track_point(dep_track_point)
                            .get_branching_tag()
                            > 0;
                    violating_b2_restrictions += 1;
                    if non_det_dependency {
                        violating_non_det_b2_restrictions += 1;
                    }
                }
            }
        }

        let w_pred_succ_hash = calc_alg_context
            .process_context()
            .node(w_pred_node)
            .use_reapply_role_succ_hash;
        if blocked {
            // test c-blocked and a-blocked specific parts (B3, B5)
            let mut c_blocked = true;
            let _a_blocked = true;
            let mut anc_role_it2 = calc_alg_context
                .process_context()
                .node_successor_role_iterator(w_node, v_node_individual_id);
            while anc_role_it2.has_next() && blocked {
                let link = anc_role_it2.next(true);
                if link.is_none() {
                    continue;
                }
                let role = calc_alg_context
                    .process_context()
                    .edge(link)
                    .get_link_role();
                let mut reapply_qu_it = calc_alg_context
                    .process_context_mut()
                    .node_role_reapply_iterator(w_pred_node, role, false);
                while reapply_qu_it.has_next() && blocked {
                    let reapply_con_des =
                        reapply_qu_it.next(calc_alg_context.process_context(), true);
                    if reapply_con_des.is_none() {
                        continue;
                    }
                    let con_des = calc_alg_context
                        .process_context()
                        .reapply_con_desc(reapply_con_des)
                        .get_concept_descriptor();
                    let concept = calc_alg_context
                        .process_context()
                        .con_desc(con_des)
                        .get_concept();
                    let con_neg = calc_alg_context
                        .process_context()
                        .con_desc(con_des)
                        .is_negated();
                    let con_op_code = calc_alg_context
                        .ontology_arenas()
                        .concept(concept)
                        .get_operator_code();

                    let mut check_blocker_role_cardinality = false;
                    let mut blocker_min_succ_cardinality: Cint64 = 0;
                    let op_linker = calc_alg_context
                        .ontology_arenas()
                        .concept(concept)
                        .get_operand_list()
                        .to_vec();

                    if (!con_neg && con_op_code == CCATMOST)
                        || (con_neg && con_op_code == CCATLEAST)
                    {
                        let mut cardinality = calc_alg_context
                            .ontology_arenas()
                            .concept(concept)
                            .get_parameter();
                        if con_neg {
                            cardinality -= 1;
                        }

                        if op_linker.is_empty() {
                            c_blocked = false;
                            if !check_blocker_role_cardinality {
                                check_blocker_role_cardinality = true;
                                blocker_min_succ_cardinality = cardinality;
                            }
                        }
                        for op_link in &op_linker {
                            let op_concept = op_link.target;
                            let op_con_neg = op_link.negated;
                            let mut contains_neg = false;
                            if !self.label_set_contains_concept_get_negated_resolved(
                                v_con_set,
                                op_concept,
                                Some(&mut contains_neg),
                                calc_alg_context,
                            ) {
                                c_blocked = false;
                                if !check_blocker_role_cardinality {
                                    check_blocker_role_cardinality = true;
                                    blocker_min_succ_cardinality = cardinality;
                                }
                            } else if contains_neg == op_con_neg {
                                c_blocked = false;
                                if !check_blocker_role_cardinality {
                                    check_blocker_role_cardinality = true;
                                    blocker_min_succ_cardinality = cardinality;
                                }
                            }
                        }
                    }

                    if check_blocker_role_cardinality {
                        let mut min_role_cardinality: Cint64 = 0;
                        if w_pred_succ_hash.is_some() {
                            let mut succ_it = {
                                let pc = calc_alg_context.process_context();
                                pc.role_succ_hash(w_pred_succ_hash)
                                    .get_role_successor_link_iterator(pc.edges(), role)
                            };
                            while succ_it.has_next() && blocked {
                                let succ_link = succ_it.next(true);
                                if succ_link.is_none() {
                                    continue;
                                }
                                let mut pred_node = w_pred_node;
                                let mut succ_indi_node = self.get_successor_individual(
                                    &mut pred_node,
                                    succ_link,
                                    calc_alg_context,
                                );
                                let succ_qualifies = {
                                    let pc = calc_alg_context.process_context();
                                    let succ_node = pc.node(succ_indi_node);
                                    succ_node.is_nominal_individual_node()
                                        || succ_node.nominal_individual().is_some()
                                        || succ_node.individual_ancestor_depth()
                                            > pc.node(w_pred_node).individual_ancestor_depth()
                                };
                                if succ_qualifies {
                                    if op_linker.is_empty()
                                        || self.contains_individual_node_concepts(
                                            &mut succ_indi_node,
                                            &op_linker,
                                            calc_alg_context,
                                        )
                                    {
                                        min_role_cardinality += 1;
                                        if min_role_cardinality >= blocker_min_succ_cardinality {
                                            blocked = false;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }

            if c_blocked {
                // test whether B6 holds
                let mut v_con_set_it = calc_alg_context
                    .process_context()
                    .label_set(v_con_set)
                    .get_concept_label_set_iterator(false, false, false);
                while c_blocked && v_con_set_it.has_next() {
                    let con_des = v_con_set_it.next(true, calc_alg_context.process_context());
                    if con_des.is_none() {
                        continue;
                    }
                    let concept = calc_alg_context
                        .process_context()
                        .con_desc(con_des)
                        .get_concept();
                    let con_neg = calc_alg_context
                        .process_context()
                        .con_desc(con_des)
                        .is_negated();
                    let con_op_code = calc_alg_context
                        .ontology_arenas()
                        .concept(concept)
                        .get_operator_code();
                    if (!con_neg && con_op_code == CCATLEAST)
                        || (con_neg && con_op_code == CCATMOST)
                    {
                        let cardinality = calc_alg_context
                            .ontology_arenas()
                            .concept(concept)
                            .get_parameter()
                            + if con_neg { 1 } else { 0 };
                        if cardinality > 1 {
                            let role = calc_alg_context
                                .ontology_arenas()
                                .concept(concept)
                                .get_role();
                            if self.has_individuals_link(
                                &mut v_node,
                                &mut w_node,
                                role,
                                false,
                                calc_alg_context,
                            ) {
                                let op_linker = calc_alg_context
                                    .ontology_arenas()
                                    .concept(concept)
                                    .get_operand_list()
                                    .to_vec();
                                if !op_linker.is_empty() {
                                    if !self.contains_individual_node_concepts_label_negated(
                                        w_sub_con_set,
                                        &op_linker,
                                        !con_neg,
                                        calc_alg_context,
                                    ) {
                                        c_blocked = false;
                                    }
                                } else {
                                    c_blocked = false;
                                }
                            }
                        }
                    }
                }
                if c_blocked {
                    return true;
                }
            }
        }

        if blocked {
            // test whether B4 holds
            let mut blocker_con_lab_set_it = calc_alg_context
                .process_context()
                .label_set(w_pred_super_con_set)
                .get_concept_label_set_iterator(false, false, false);
            while blocker_con_lab_set_it.has_next() && blocked {
                let con_des = blocker_con_lab_set_it.next(true, calc_alg_context.process_context());
                if con_des.is_none() {
                    continue;
                }
                let concept = calc_alg_context
                    .process_context()
                    .con_desc(con_des)
                    .get_concept();
                let con_neg = calc_alg_context
                    .process_context()
                    .con_desc(con_des)
                    .is_negated();
                let con_op_code = calc_alg_context
                    .ontology_arenas()
                    .concept(concept)
                    .get_operator_code();
                let role = calc_alg_context
                    .ontology_arenas()
                    .concept(concept)
                    .get_role();
                let mut cardinality = calc_alg_context
                    .ontology_arenas()
                    .concept(concept)
                    .get_parameter();
                let op_linker = calc_alg_context
                    .ontology_arenas()
                    .concept(concept)
                    .get_operand_list()
                    .to_vec();
                let mut needs_restriction_test = false;
                let mut negate_ops = false;
                if (!con_neg && con_op_code == CCATLEAST) || (con_neg && con_op_code == CCATMOST) {
                    if con_neg {
                        cardinality += 1;
                    }
                    needs_restriction_test = true;
                } else if (!con_neg && (con_op_code == CCSOME || con_op_code == CCAQSOME))
                    || (con_neg && con_op_code == CCALL)
                {
                    cardinality = 1;
                    needs_restriction_test = true;
                    negate_ops = con_neg;
                }

                if needs_restriction_test {
                    // B4b
                    let mut restriction_holds = false;
                    if self.has_individuals_link(
                        &mut w_node,
                        &mut v_node,
                        role,
                        false,
                        calc_alg_context,
                    ) && self.contains_individual_node_concepts_label_negated(
                        v_con_set,
                        &op_linker,
                        negate_ops,
                        calc_alg_context,
                    ) {
                        restriction_holds = true;
                    }
                    if !restriction_holds {
                        // B4a
                        // w' needs m role-successors.
                        let mut min_role_cardinality: Cint64 = 0;
                        if w_pred_succ_hash.is_some() {
                            let mut succ_it = {
                                let pc = calc_alg_context.process_context();
                                pc.role_succ_hash(w_pred_succ_hash)
                                    .get_role_successor_link_iterator(pc.edges(), role)
                            };
                            while succ_it.has_next() {
                                let succ_link = succ_it.next(true);
                                if succ_link.is_none() {
                                    continue;
                                }
                                let mut pred_node = w_pred_node;
                                let mut succ_indi = self.get_successor_individual(
                                    &mut pred_node,
                                    succ_link,
                                    calc_alg_context,
                                );
                                let succ_qualifies = {
                                    let pc = calc_alg_context.process_context();
                                    let succ_node = pc.node(succ_indi);
                                    succ_node.is_nominal_individual_node()
                                        || succ_node.nominal_individual().is_some()
                                        || succ_node.individual_ancestor_depth()
                                            > pc.node(w_pred_node).individual_ancestor_depth()
                                };
                                if succ_qualifies
                                    && (op_linker.is_empty()
                                        || self.contains_individual_node_concepts_negated(
                                            &mut succ_indi,
                                            &op_linker,
                                            negate_ops,
                                            calc_alg_context,
                                        ))
                                {
                                    min_role_cardinality += 1;
                                }
                            }
                        }
                        if min_role_cardinality < cardinality {
                            blocked = false;
                        }
                    }
                }
            }
        }

        if !blocked
            && self.conf_signature_mirroring_blocking
            && self.opt_signature_mirroring_blocking_in_blocking
        {
            let w_pred_super_count = calc_alg_context
                .process_context()
                .label_set(w_pred_super_con_set)
                .get_concept_count();
            let w_sub_count = calc_alg_context
                .process_context()
                .label_set(w_sub_con_set)
                .get_concept_count();
            let diff_concept_count = w_pred_super_count - w_sub_count;

            let new_score = violating_non_det_b2_restrictions as f64 * 1.2
                + violating_b2_restrictions as f64
                + diff_concept_count as f64 * 0.1;
            if block_alt_data.is_none() {
                let mut sig_block_cand_data =
                    BlockingAlternativeSignatureBlockingCandidateData::new();
                sig_block_cand_data.init_signature_blocking_candidate_data(
                    w_pred_node,
                    violating_b2_restrictions,
                    violating_non_det_b2_restrictions,
                    diff_concept_count,
                );
                *block_alt_data = calc_alg_context
                    .process_context_mut()
                    .alloc_blocking_alt_data(sig_block_cand_data);
            } else {
                let old_score = {
                    let sig_block_cand_data = calc_alg_context
                        .process_context()
                        .blocking_alt_data(*block_alt_data);
                    sig_block_cand_data.get_violated_non_deterministic_restriction_count() as f64
                        * 1.2
                        + sig_block_cand_data.get_violated_restriction_count() as f64
                        + sig_block_cand_data.get_concept_difference_count() as f64 * 0.1
                };
                if new_score > old_score {
                    calc_alg_context
                        .process_context_mut()
                        .blocking_alt_data_mut(*block_alt_data)
                        .init_signature_blocking_candidate_data(
                            w_pred_node,
                            violating_b2_restrictions,
                            violating_non_det_b2_restrictions,
                            diff_concept_count,
                        );
                }
            }
        }

        blocked
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::isLabelConceptSubSetBlocking`.
    pub fn is_label_concept_sub_set_blocking(
        &mut self,
        test_indi: NodeId,
        blocking_indi: NodeId,
        block_data: IndiBlockDataId,
        test_continue_blocking: bool,
        block_alt_data: &mut BlockingAlternativeDataHandle,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W6-DEFER[api]: STATINC(SUBSETBLOCKINGTESTCOUNT,calcAlgContext);
        if test_continue_blocking {
            // is still sub set when added something to blocker individual node
            return true;
        }
        let sub_con_set = calc_alg_context
            .process_context_mut()
            .node_mut(test_indi)
            .get_reapply_concept_label_set(false);
        let super_con_set = calc_alg_context
            .process_context_mut()
            .node_mut(blocking_indi)
            .get_reapply_concept_label_set(false);
        let mut first_not_entailed_con_des: ConDescId = Id::NONE;
        let sub_set = self.is_label_concept_sub_set(
            sub_con_set,
            super_con_set,
            Some(&mut first_not_entailed_con_des),
            None,
            calc_alg_context,
        );
        sub_set
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::isLabelConceptEqualBlocking`.
    pub fn is_label_concept_equal_blocking(
        &mut self,
        test_indi: NodeId,
        blocking_indi: NodeId,
        block_data: IndiBlockDataId,
        test_continue_blocking: bool,
        block_alt_data: &mut BlockingAlternativeDataHandle,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W6-DEFER[api]: STATINC(EQUALSETBLOCKINGTESTCOUNT,calcAlgContext);
        let con_set1 = calc_alg_context
            .process_context_mut()
            .node_mut(test_indi)
            .get_reapply_concept_label_set(false);
        let con_set2 = calc_alg_context
            .process_context_mut()
            .node_mut(blocking_indi)
            .get_reapply_concept_label_set(false);
        self.is_label_concept_equal_set(con_set1, con_set2, calc_alg_context)
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::isLabelConceptEqualPairwiseBlocking`.
    pub fn is_label_concept_equal_pairwise_blocking(
        &mut self,
        mut test_indi: NodeId,
        mut blocking_indi: NodeId,
        block_data: IndiBlockDataId,
        test_continue_blocking: bool,
        block_alt_data: &mut BlockingAlternativeDataHandle,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W6-DEFER[api]: STATINC(PAIRWISEEQUALSETBLOCKINGTESTCOUNT,calcAlgContext);
        let anc_test_indi = self.get_ancestor_individual(&mut test_indi, calc_alg_context);
        if anc_test_indi.is_none() {
            return false;
        }
        let anc_blocking_indi = self.get_ancestor_individual(&mut blocking_indi, calc_alg_context);
        if anc_blocking_indi.is_none() {
            return false;
        }
        let test_indi_anc_link = calc_alg_context
            .process_context()
            .node(test_indi)
            .get_ancestor_link();
        // KONCLUDE-PORT-NOTE[unclear]: the C++ reads `testIndi->getAncestorLink()` for BOTH
        // links (an apparent upstream copy/paste — `blockingIndiAncLink` is taken from
        // `testIndi`, not `blockingIndi`); reproduced verbatim for faithfulness.
        let blocking_indi_anc_link = calc_alg_context
            .process_context()
            .node(test_indi)
            .get_ancestor_link();
        if calc_alg_context
            .process_context()
            .edge(test_indi_anc_link)
            .get_link_role()
            != calc_alg_context
                .process_context()
                .edge(blocking_indi_anc_link)
                .get_link_role()
        {
            return false;
        }
        let con_set1 = calc_alg_context
            .process_context_mut()
            .node_mut(test_indi)
            .get_reapply_concept_label_set(false);
        let con_set1_pair = calc_alg_context
            .process_context_mut()
            .node_mut(blocking_indi)
            .get_reapply_concept_label_set(false);
        let con_set2 = calc_alg_context
            .process_context_mut()
            .node_mut(anc_test_indi)
            .get_reapply_concept_label_set(false);
        let con_set2_pair = calc_alg_context
            .process_context_mut()
            .node_mut(anc_blocking_indi)
            .get_reapply_concept_label_set(false);
        self.is_pairwise_label_concept_equal_set(
            con_set1,
            con_set1_pair,
            con_set2,
            con_set2_pair,
            calc_alg_context,
        )
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::isIndividualNodeBlocking`.
    pub fn is_individual_node_blocking(
        &mut self,
        mut test_indi: NodeId,
        mut blocking_indi: NodeId,
        block_data: IndiBlockDataId,
        test_continue_blocking: bool,
        block_alt_data: &mut BlockingAlternativeDataHandle,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W6-DEFER[api]: STATINC(INDINODEBLOCKINGTESTCOUNT,calcAlgContext);
        // TODO (Konclude): check config, first test concept set sizes

        let test_con_set = calc_alg_context
            .process_context_mut()
            .node_mut(test_indi)
            .get_reapply_concept_label_set(false);
        let blocking_con_set = calc_alg_context
            .process_context_mut()
            .node_mut(blocking_indi)
            .get_reapply_concept_label_set(false);
        let test_con_set_count = calc_alg_context
            .process_context()
            .label_set(test_con_set)
            .get_concept_count();
        let blocking_con_set_count = calc_alg_context
            .process_context()
            .label_set(blocking_con_set)
            .get_concept_count();
        if test_con_set_count > blocking_con_set_count {
            return false;
        }

        if !test_continue_blocking {
            let init_con_des = calc_alg_context
                .process_context()
                .node(test_indi)
                .individual_initialization_concept();
            if !init_con_des.is_none() {
                let blocking_label_set = calc_alg_context
                    .process_context_mut()
                    .node_mut(blocking_indi)
                    .get_reapply_concept_label_set(false);
                let init_concept = calc_alg_context
                    .process_context()
                    .con_desc(init_con_des)
                    .get_concept();
                let init_negated = calc_alg_context
                    .process_context()
                    .con_desc(init_con_des)
                    .is_negated();
                let init_tag = calc_alg_context
                    .ontology_arenas()
                    .concept(init_concept)
                    .get_concept_tag();
                let mut blocking_init_con_des: ConDescId = Id::NONE;
                let mut blocking_init_dep: TrackPointId = Id::NONE;
                let blocking_contains_init = calc_alg_context
                    .process_context()
                    .label_set(blocking_label_set)
                    .get_concept_descriptor_by_tag(
                        init_tag,
                        &mut blocking_init_con_des,
                        &mut blocking_init_dep,
                    )
                    && calc_alg_context
                        .process_context()
                        .con_desc(blocking_init_con_des)
                        .is_negated()
                        == init_negated;
                if !blocking_contains_init {
                    return false;
                }
            }
        }

        let mut test_processing_blocking = false;
        if self.opt_det_exp_preporcessing {
            test_processing_blocking = true;
        }

        let mut blocking_concepts = false;

        if test_processing_blocking || self.conf_sub_set_blocking {
            if self.is_label_concept_sub_set_blocking(
                test_indi,
                blocking_indi,
                block_data,
                test_continue_blocking,
                block_alt_data,
                calc_alg_context,
            ) {
                blocking_concepts = true;
            }
        } else if self.conf_optimized_sub_set_blocking {
            if self.is_label_concept_optimized_blocking(
                test_indi,
                blocking_indi,
                block_data,
                test_continue_blocking,
                block_alt_data,
                calc_alg_context,
            ) {
                blocking_concepts = true;
            }
        } else if self.conf_equal_set_blocking {
            if self.is_label_concept_equal_blocking(
                test_indi,
                blocking_indi,
                block_data,
                test_continue_blocking,
                block_alt_data,
                calc_alg_context,
            ) {
                blocking_concepts = true;
            }
        } else if self.conf_pairwise_equal_set_blocking {
            if self.is_label_concept_equal_pairwise_blocking(
                test_indi,
                blocking_indi,
                block_data,
                test_continue_blocking,
                block_alt_data,
                calc_alg_context,
            ) {
                blocking_concepts = true;
            }
        }

        let mut blocking_prop_bindings = false;
        if blocking_concepts {
            if self.opt_analogous_propagation_path_blocking {
                blocking_prop_bindings = self
                    .is_anonymous_variable_propagation_binding_analogous_path(
                        &mut test_indi,
                        &mut blocking_indi,
                        block_data,
                        test_continue_blocking,
                        INVALID,
                        calc_alg_context,
                    );
            } else {
                let mut propagation_block_alt_data = INVALID;
                blocking_prop_bindings = self.is_nominal_variable_propagation_binding_sub_set(
                    test_indi,
                    blocking_indi,
                    block_data,
                    test_continue_blocking,
                    &mut propagation_block_alt_data,
                    calc_alg_context,
                );
            }
        }

        blocking_concepts && blocking_prop_bindings
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::detectIndividualNodeBlockedStatus`.
    pub fn detect_individual_node_blocked_status(
        &mut self,
        test_indi: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W6-DEFER[api]: STATINC(DETECTINDINODEBLOCKINGSTATUSCOUNT,calcAlgContext);
        let mut previous_processing_blocked = false;
        let previous_blocked = calc_alg_context
            .process_context()
            .node(test_indi)
            .has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_DIRECTBLOCKED
                    | IndividualProcessNode::PRF_INDIRECTBLOCKED
                    | IndividualProcessNode::PRF_PROCESSINGBLOCKED,
            );
        if !self.opt_det_exp_preporcessing
            && calc_alg_context
                .process_context()
                .node(test_indi)
                .has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_PROCESSINGBLOCKED,
                )
        {
            calc_alg_context
                .process_context_mut()
                .node_mut(test_indi)
                .clear_processing_restriction_flags(IndividualProcessNode::PRF_PROCESSINGBLOCKED);
            previous_processing_blocked = true;
        } else if self.opt_det_exp_preporcessing
            && calc_alg_context
                .process_context()
                .node(test_indi)
                .has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_PROCESSINGBLOCKED,
                )
        {
            return true;
        } else {
            if !calc_alg_context
                .process_context()
                .node(test_indi)
                .has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_BLOCKINGRETESTDUEANCESTORMODIFIED
                        | IndividualProcessNode::PRF_BLOCKINGRETESTDUEDIRECTMODIFIED
                        | IndividualProcessNode::PRF_BLOCKINGRETESTDUEBLOCKERMODIFIED
                        | IndividualProcessNode::PRF_BLOCKINGRETESTDUEINDIRECTBLOCKERLOSS,
                )
            {
                return previous_blocked;
            }
        }

        let previous_indirect_blocked = calc_alg_context
            .process_context()
            .node(test_indi)
            .has_partial_processing_restriction_flags(IndividualProcessNode::PRF_INDIRECTBLOCKED);
        if previous_indirect_blocked {
            if !calc_alg_context
                .process_context()
                .node(test_indi)
                .has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_BLOCKINGRETESTDUEINDIRECTBLOCKERLOSS,
                )
            {
                calc_alg_context
                    .process_context_mut()
                    .node_mut(test_indi)
                    .clear_processing_restriction_flags(
                        IndividualProcessNode::PRF_BLOCKINGRETESTDUEANCESTORMODIFIED
                            | IndividualProcessNode::PRF_BLOCKINGRETESTDUEDIRECTMODIFIED
                            | IndividualProcessNode::PRF_BLOCKINGRETESTDUEBLOCKERMODIFIED,
                    );
                return true;
            }
        }

        let _previous_direct_blocked = calc_alg_context
            .process_context()
            .node(test_indi)
            .has_partial_processing_restriction_flags(IndividualProcessNode::PRF_DIRECTBLOCKED);

        let mut anc_test_indi = test_indi;
        let mut blocking_indi: NodeId = Id::NONE;

        let mut block_alt_data: BlockingAlternativeDataHandle = Id::NONE;

        let mut blocked = false;

        let mut blocking_testing = true;
        if !previous_blocked
            && !self.comp_graph_cache_handler.is_none()
            && self.conf_ignore_blocking_completion_graph_cached_non_blocking_nodes
        {
            // W6-DEFER[api]: if mCompGraphCacheHandler->isIndividualNodeCompletionGraphConsistencePresentNonBlocked(testIndi,...): blockingTesting=false;
            let cached_non_blocked = false;
            if cached_non_blocked {
                blocking_testing = false;
            }
        }

        // test each modified ancestor
        while blocking_testing
            && !blocked
            && !anc_test_indi.is_none()
            && calc_alg_context
                .process_context()
                .node(anc_test_indi)
                .is_blockable_individual()
            && !calc_alg_context
                .process_context()
                .node(anc_test_indi)
                .has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_CONCRETEDATAINDINODE,
                )
            && calc_alg_context
                .process_context()
                .node(anc_test_indi)
                .has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_BLOCKINGRETESTDUEANCESTORMODIFIED
                        | IndividualProcessNode::PRF_BLOCKINGRETESTDUEDIRECTMODIFIED
                        | IndividualProcessNode::PRF_BLOCKINGRETESTDUEBLOCKERMODIFIED
                        | IndividualProcessNode::PRF_BLOCKINGRETESTDUEINDIRECTBLOCKERLOSS,
                )
            && !calc_alg_context
                .process_context()
                .node(anc_test_indi)
                .has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_INVALIDBLOCKINGORCACHING,
                )
        {
            // W6-DEFER[api]: STATINC(DETECTANCINDINODEBLOCKINGSTATUSCOUNT,calcAlgContext);
            let mut loc_anc_test_indi =
                self.get_localized_individual(anc_test_indi, false, calc_alg_context);

            // search blocker node
            block_alt_data = Id::NONE;
            blocking_indi = Id::NONE;

            if self.conf_saturation_caching_testing_during_blocking_tests {
                self.detect_individual_node_saturation_cached(loc_anc_test_indi, calc_alg_context);
            }

            let mut skip_blocker_search = false;
            if calc_alg_context
                .process_context()
                .node(loc_anc_test_indi)
                .has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_SATURATIONBLOCKINGCACHED,
                )
                && calc_alg_context
                    .process_context()
                    .node(loc_anc_test_indi)
                    .has_partial_processing_restriction_flags(
                        IndividualProcessNode::PRF_SATURATIONSUCCESSORCREATIONBLOCKINGCACHED,
                    )
            {
                skip_blocker_search = true;
            }

            if !skip_blocker_search {
                blocking_indi = self.get_blocking_individual_node(
                    loc_anc_test_indi,
                    &mut block_alt_data,
                    calc_alg_context,
                );
            }

            calc_alg_context
                .process_context_mut()
                .node_mut(loc_anc_test_indi)
                .clear_processing_restriction_flags(
                    IndividualProcessNode::PRF_BLOCKINGRETESTDUEANCESTORMODIFIED
                        | IndividualProcessNode::PRF_BLOCKINGRETESTDUEDIRECTMODIFIED
                        | IndividualProcessNode::PRF_BLOCKINGRETESTDUEBLOCKERMODIFIED
                        | IndividualProcessNode::PRF_BLOCKINGRETESTDUEINDIRECTBLOCKERLOSS
                        | IndividualProcessNode::PRF_DIRECTBLOCKED
                        | IndividualProcessNode::PRF_INDIRECTBLOCKED
                        | IndividualProcessNode::PRF_PROCESSINGBLOCKED,
                );

            if blocking_indi.is_none() {
                // W6-DEFER[api]: STATINC(FAILEDBLOCKINGSTATUSDETECTIONCOUNT,calcAlgContext);
                if block_alt_data.is_some() {
                    blocked = self.test_alternative_blocked(
                        loc_anc_test_indi,
                        block_alt_data,
                        calc_alg_context,
                    );
                }
                if !blocked {
                    calc_alg_context
                        .process_context_mut()
                        .node_mut(loc_anc_test_indi)
                        .set_blocker_individual_node(Id::NONE);
                    anc_test_indi =
                        self.get_ancestor_individual(&mut loc_anc_test_indi, calc_alg_context);

                    if !previous_blocked
                        && !self.comp_graph_cache_handler.is_none()
                        && self.conf_ignore_blocking_completion_graph_cached_non_blocking_nodes
                    {
                        // W6-DEFER[api]: if mCompGraphCacheHandler->isIndividualNodeCompletionGraphConsistencePresentNonBlocked(locAncTestIndi,...): blockingTesting=false;
                        let cached_non_blocked = false;
                        if cached_non_blocked {
                            blocking_testing = false;
                        }
                    }
                }
            } else {
                // W6-DEFER[api]: STATINC(SUCCESSBLOCKINGSTATUSDETECTIONCOUNT,calcAlgContext);

                if calc_alg_context
                    .process_context()
                    .node(blocking_indi)
                    .has_partial_processing_restriction_flags(
                        IndividualProcessNode::PRF_SUCCESSORNOMINALCONNECTION,
                    )
                {
                    self.propagate_individual_node_nominal_connection_status_to_ancestors(
                        loc_anc_test_indi,
                        blocking_indi,
                        calc_alg_context,
                    );
                }

                let mut test_processing_blocking = false;
                if self.opt_det_exp_preporcessing {
                    test_processing_blocking = true;
                }

                calc_alg_context
                    .process_context_mut()
                    .node_mut(loc_anc_test_indi)
                    .set_blocker_individual_node(blocking_indi);
                // locAncTestIndi->mDebugBlockerLastConceptDes = blockingIndi->getReapplyConceptLabelSet(false)->getAddingSortedConceptDescriptionLinker();
                let blocker_label_set = calc_alg_context
                    .process_context_mut()
                    .node_mut(blocking_indi)
                    .get_reapply_concept_label_set(false);
                let adding_sorted = calc_alg_context
                    .process_context()
                    .label_set(blocker_label_set)
                    .get_adding_sorted_concept_description_linker();
                calc_alg_context
                    .process_context_mut()
                    .node_mut(loc_anc_test_indi)
                    .debug_blocker_last_concept_des = adding_sorted;

                if !test_processing_blocking {
                    let loc_blocking_node =
                        self.get_localized_individual(blocking_indi, false, calc_alg_context);
                    // CXLinker<CIndividualProcessNode*> blockedIndiNodeLinker initLinker(locAncTestIndi);
                    // locBlockingNode->addBlockedIndividualsLinker(blockedIndiNodeLinker);
                    calc_alg_context
                        .process_context_mut()
                        .node_mut(loc_blocking_node)
                        .add_blocked_individuals_linker(vec![loc_anc_test_indi]);
                    calc_alg_context
                        .process_context_mut()
                        .node_mut(loc_anc_test_indi)
                        .add_processing_restriction_flags(IndividualProcessNode::PRF_DIRECTBLOCKED);
                } else {
                    calc_alg_context
                        .process_context_mut()
                        .node_mut(loc_anc_test_indi)
                        .add_processing_restriction_flags(
                            IndividualProcessNode::PRF_PROCESSINGBLOCKED,
                        );
                    self.add_individual_to_blocking_update_review_processing_queue(
                        blocking_indi,
                        calc_alg_context,
                    );
                }
                self.propagate_indirect_successor_blocking(loc_anc_test_indi, calc_alg_context);
                blocked = true;
            }
        }

        if blocking_indi.is_none() && previous_blocked {
            self.reactivate_indirect_blocked_successors(test_indi, false, calc_alg_context);
        }
        let _ = previous_processing_blocked;
        blocked
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getBlockingIndividualNode`.
    pub fn get_blocking_individual_node(
        &mut self,
        blocking_test_indi: NodeId,
        block_alt_data: &mut BlockingAlternativeDataHandle,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        let mut blocking_indi: NodeId = Id::NONE;
        if blocking_indi.is_none() && self.conf_anywhere_blocking_linked_candidate_hash_search {
            blocking_indi = self.get_anywhere_blocking_individual_node_linked_canidate_hashed(
                blocking_test_indi,
                *block_alt_data,
                calc_alg_context,
            );
        }
        if blocking_indi.is_none() && self.conf_anywhere_blocking_candidate_hash_search {
            blocking_indi = self.get_anywhere_blocking_individual_node_canidate_hashed(
                blocking_test_indi,
                *block_alt_data,
                calc_alg_context,
            );
        }
        if blocking_indi.is_none() && self.conf_anywhere_blocking_search {
            blocking_indi = self.get_anywhere_blocking_individual_node(
                blocking_test_indi,
                block_alt_data,
                calc_alg_context,
            );
        }
        if blocking_indi.is_none() && self.conf_ancestor_blocking_search {
            blocking_indi = self.get_ancestor_blocking_individual_node(
                blocking_test_indi,
                block_alt_data,
                calc_alg_context,
            );
        }
        blocking_indi
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::continueIndividualNodeBlock`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: the C++ `CIndividualProcessNode*& blockerIndiNode`
    /// out-reference becomes a `&mut NodeId` out-parameter.
    pub fn continue_individual_node_block(
        &mut self,
        indi: NodeId,
        block_data: IndiBlockDataId,
        blocker_indi_node: &mut NodeId,
        block_alt_data: &mut BlockingAlternativeDataHandle,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut blocking_indi_node: NodeId = Id::NONE;
        if !block_data.is_none() {
            // blockingIndiNode = blockData->getBlockingIndividualNode();
            blocking_indi_node = calc_alg_context
                .process_context()
                .blocking_test_data(block_data)
                .get_blocking_individual_node();
            if !blocking_indi_node.is_none() {
                // W6-DEFER[api]: STATINC(CONTINUEBLOCKINGTESTCOUNT,calcAlgContext);
                blocking_indi_node =
                    self.get_up_to_date_individual(blocking_indi_node, calc_alg_context);
                if calc_alg_context
                    .process_context()
                    .node(blocking_indi_node)
                    .is_blockable_individual()
                    && self.is_individual_node_valid_blocker(blocking_indi_node, calc_alg_context)
                {
                    if self.is_individual_node_blocking(
                        indi,
                        blocking_indi_node,
                        block_data,
                        true,
                        block_alt_data,
                        calc_alg_context,
                    ) {
                        *blocker_indi_node = blocking_indi_node;
                        return true;
                    }
                } else if calc_alg_context
                    .process_context()
                    .node(blocking_indi_node)
                    .has_partial_processing_restriction_flags(
                        IndividualProcessNode::PRF_DIRECTBLOCKED,
                    )
                {
                    let candidate_block_data = calc_alg_context
                        .process_context()
                        .node(blocking_indi_node)
                        .individual_block_data(false);
                    if !candidate_block_data.is_none() {
                        // candidateBlockingIndiNode = candidateBlockData->getBlockingIndividualNode();
                        let candidate_blocking_indi_node: NodeId = calc_alg_context
                            .process_context()
                            .blocking_test_data(candidate_block_data)
                            .get_blocking_individual_node();
                        if !candidate_blocking_indi_node.is_none()
                            && calc_alg_context
                                .process_context()
                                .node(candidate_blocking_indi_node)
                                .is_blockable_individual()
                            && self.is_individual_node_valid_blocker(
                                candidate_blocking_indi_node,
                                calc_alg_context,
                            )
                        {
                            if self.is_individual_node_blocking(
                                indi,
                                candidate_blocking_indi_node,
                                block_data,
                                true,
                                block_alt_data,
                                calc_alg_context,
                            ) {
                                *blocker_indi_node = candidate_blocking_indi_node;
                                // blockData->setBlockingIndividualNode(candidateBlockingIndiNode);
                                calc_alg_context
                                    .process_context_mut()
                                    .blocking_test_data_mut(block_data)
                                    .set_blocking_individual_node(candidate_blocking_indi_node);
                                return true;
                            }
                        }
                    }
                }
            }
        }
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::signatureCachedIndividualNodeBlock`.
    pub fn signature_cached_individual_node_block(
        &mut self,
        indi: NodeId,
        block_data: IndiBlockDataId,
        blocker_indi_node: &mut NodeId,
        block_alt_data: &mut BlockingAlternativeDataHandle,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        if calc_alg_context
            .process_context()
            .node(indi)
            .has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_SIGNATUREBLOCKINGCACHED,
            )
        {
            let sig_block_exp_data = calc_alg_context
                .process_context()
                .node(indi)
                .signature_blocking_individual_node_concept_expansion_data(false);
            if !sig_block_exp_data.is_none() {
                // blockingIndiNode = sigBlockExpData->getBlockerIndividualNode();
                let mut blocking_indi_node: NodeId = calc_alg_context
                    .process_context()
                    .sig_block_con_exp_data(sig_block_exp_data)
                    .get_blocker_individual_node();
                if !blocking_indi_node.is_none() {
                    blocking_indi_node =
                        self.get_up_to_date_individual(blocking_indi_node, calc_alg_context);
                    if calc_alg_context
                        .process_context()
                        .node(blocking_indi_node)
                        .is_blockable_individual()
                        && self
                            .is_individual_node_valid_blocker(blocking_indi_node, calc_alg_context)
                    {
                        if self.is_individual_node_blocking(
                            indi,
                            blocking_indi_node,
                            block_data,
                            false,
                            block_alt_data,
                            calc_alg_context,
                        ) {
                            *blocker_indi_node = blocking_indi_node;
                            return true;
                        }
                    }
                }
            }
        }
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::clearBlockingCache`.
    pub fn clear_blocking_cache(
        &mut self,
        _calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        self.cached_indi_associated_concept_set_hash.clear();
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getAncestorBlockingIndividualNode`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: the `CIndividualNodeBlockingTestData` block-data
    /// allocation/init, its node-switch / concept-label-set-modification tags and
    /// the `CNodeSwitchHistory` min-tag lookup are stubs; deferred to their neutral
    /// values (tags `0`, min bounds `0`) so the ancestor-chain blocker search runs
    /// over the full chain. The sibling-driven search loop is reproduced verbatim.
    pub fn get_ancestor_blocking_individual_node(
        &mut self,
        mut blocking_test_indi: NodeId,
        block_alt_data: &mut BlockingAlternativeDataHandle,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        self.clear_blocking_cache(calc_alg_context);
        // W6-DEFER[memory-pool]: taskMemMan = calcAlgContext->getUsedProcessTaskMemoryAllocationManager();
        let mut blocker_node: NodeId = Id::NONE;
        let node_switch_history = calc_alg_context
            .processing_data_box_mut()
            .node_switch_history(false);
        let block_data = calc_alg_context
            .process_context()
            .node(blocking_test_indi)
            .individual_block_data(false);
        let mut loc_block_data = calc_alg_context
            .process_context()
            .node(blocking_test_indi)
            .individual_block_data(true);
        if loc_block_data.is_none() {
            // locBlockData = CObjectAllocator<CIndividualNodeBlockingTestData>::allocateAndConstruct(taskMemMan);
            // locBlockData->initBlockData(blockData); blockingTestIndi->setIndividualBlockData(locBlockData);
            let pc = calc_alg_context.process_context_mut();
            let new_block_data = pc.alloc_blocking_test_data(IndividualNodeBlockingTestData::new());
            if !block_data.is_none() {
                let taken = std::mem::replace(
                    pc.blocking_test_data_mut(block_data),
                    IndividualNodeBlockingTestData::new(),
                );
                pc.blocking_test_data_mut(new_block_data)
                    .init_block_data(Some(&taken));
                *pc.blocking_test_data_mut(block_data) = taken;
            } else {
                pc.blocking_test_data_mut(new_block_data)
                    .init_block_data(None);
            }
            pc.node_mut(blocking_test_indi)
                .set_individual_block_data(new_block_data);
            loc_block_data = new_block_data;
        }
        let prev_node_switch_tag = calc_alg_context
            .process_context()
            .blocking_test_data(loc_block_data)
            .get_node_switch_tag();
        let prev_node_concept_label_mod_tag = calc_alg_context
            .process_context()
            .blocking_test_data(loc_block_data)
            .get_concept_label_set_modification_tag();
        let mut min_test_indi_node_id: Cint64 = 0;
        let mut min_test_anc_indi_depth: Cint64 = 0;
        let (current_node_switch_tag, current_label_mod_tag) = {
            let tagger = calc_alg_context.process_context().used_process_tagger();
            (
                tagger.get_current_node_switch_tag(),
                tagger.get_current_concept_label_set_modification_tag(),
            )
        };
        {
            let loc_block_data_ref = calc_alg_context
                .process_context_mut()
                .blocking_test_data_mut(loc_block_data);
            loc_block_data_ref.update_node_switch_tag(current_node_switch_tag);
            loc_block_data_ref.update_concept_label_set_modification_tag(current_label_mod_tag);
        }

        let mut continue_blocking_indi_node: NodeId = Id::NONE;
        if self.continue_individual_node_block(
            blocking_test_indi,
            loc_block_data,
            &mut continue_blocking_indi_node,
            block_alt_data,
            calc_alg_context,
        ) {
            blocker_node = continue_blocking_indi_node;
        } else {
            // locBlockData->clearBlockingIndividualNode();
            calc_alg_context
                .process_context_mut()
                .blocking_test_data_mut(loc_block_data)
                .clear_blocking_individual_node();
            if self.signature_cached_individual_node_block(
                blocking_test_indi,
                loc_block_data,
                &mut continue_blocking_indi_node,
                block_alt_data,
                calc_alg_context,
            ) {
                blocker_node = continue_blocking_indi_node;
            } else {
                if node_switch_history.is_some()
                    && loc_block_data.is_some()
                    && prev_node_switch_tag > 0
                {
                    (min_test_indi_node_id, min_test_anc_indi_depth) = calc_alg_context
                        .node_switch_history_min_bounds(
                            node_switch_history,
                            prev_node_switch_tag,
                            0,
                            0,
                        );
                }
                let mut anc_indi_node =
                    self.get_ancestor_individual(&mut blocking_test_indi, calc_alg_context);
                while blocker_node.is_none()
                    && !anc_indi_node.is_none()
                    && self.is_individual_node_valid_blocker(anc_indi_node, calc_alg_context)
                    && calc_alg_context
                        .process_context()
                        .node(anc_indi_node)
                        .individual_ancestor_depth()
                        >= min_test_anc_indi_depth
                {
                    if continue_blocking_indi_node != anc_indi_node {
                        // W6-DEFER[api]: STATINC(ANCESTORBLOCKINGSEARCHINDINODECOUNT,calcAlgContext);
                        if self.is_individual_node_concept_label_set_modified(
                            &mut anc_indi_node,
                            prev_node_concept_label_mod_tag,
                            calc_alg_context,
                        ) && self.is_individual_node_blocking(
                            blocking_test_indi,
                            anc_indi_node,
                            loc_block_data,
                            false,
                            block_alt_data,
                            calc_alg_context,
                        ) {
                            blocker_node = anc_indi_node;
                        }
                    }
                    if blocker_node.is_none() {
                        anc_indi_node =
                            self.get_ancestor_individual(&mut anc_indi_node, calc_alg_context);
                    }
                }
            }
        }
        // locBlockData->setBlockingIndividualNode(blockerNode);
        calc_alg_context
            .process_context_mut()
            .blocking_test_data_mut(loc_block_data)
            .set_blocking_individual_node(blocker_node);
        let _ = min_test_indi_node_id;
        blocker_node
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getAnywhereBlockingIndividualNode`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: as `getAncestorBlockingIndividualNode`, the
    /// block-data + node-switch-history satellites are stubs and deferred to their
    /// neutral values; the descending-id anywhere blocker search (with the
    /// descendant-exclusion ancestor walk) is reproduced over the ported node arena.
    pub fn get_anywhere_blocking_individual_node(
        &mut self,
        blocking_test_indi: NodeId,
        block_alt_data: &mut BlockingAlternativeDataHandle,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        self.clear_blocking_cache(calc_alg_context);
        // W6-DEFER[memory-pool]: taskMemMan = calcAlgContext->getUsedProcessTaskMemoryAllocationManager();
        let mut blocker_node: NodeId = Id::NONE;
        let node_switch_history = calc_alg_context
            .processing_data_box_mut()
            .node_switch_history(false);
        let block_data = calc_alg_context
            .process_context()
            .node(blocking_test_indi)
            .individual_block_data(false);
        let mut loc_block_data = calc_alg_context
            .process_context()
            .node(blocking_test_indi)
            .individual_block_data(true);
        if loc_block_data.is_none() {
            // locBlockData = CObjectAllocator<CIndividualNodeBlockingTestData>::allocateAndConstruct(taskMemMan);
            // locBlockData->initBlockData(blockData); blockingTestIndi->setIndividualBlockData(locBlockData);
            let pc = calc_alg_context.process_context_mut();
            let new_block_data = pc.alloc_blocking_test_data(IndividualNodeBlockingTestData::new());
            if !block_data.is_none() {
                let taken = std::mem::replace(
                    pc.blocking_test_data_mut(block_data),
                    IndividualNodeBlockingTestData::new(),
                );
                pc.blocking_test_data_mut(new_block_data)
                    .init_block_data(Some(&taken));
                *pc.blocking_test_data_mut(block_data) = taken;
            } else {
                pc.blocking_test_data_mut(new_block_data)
                    .init_block_data(None);
            }
            pc.node_mut(blocking_test_indi)
                .set_individual_block_data(new_block_data);
            loc_block_data = new_block_data;
        }
        let prev_node_switch_tag = calc_alg_context
            .process_context()
            .blocking_test_data(loc_block_data)
            .get_node_switch_tag();
        let prev_node_concept_label_mod_tag = calc_alg_context
            .process_context()
            .blocking_test_data(loc_block_data)
            .get_concept_label_set_modification_tag();
        let mut min_test_indi_node_id: Cint64 = 0;
        let mut min_test_anc_indi_depth: Cint64 = 0;
        let (current_node_switch_tag, current_label_mod_tag) = {
            let tagger = calc_alg_context.process_context().used_process_tagger();
            (
                tagger.get_current_node_switch_tag(),
                tagger.get_current_concept_label_set_modification_tag(),
            )
        };
        {
            let loc_block_data_ref = calc_alg_context
                .process_context_mut()
                .blocking_test_data_mut(loc_block_data);
            loc_block_data_ref.update_node_switch_tag(current_node_switch_tag);
            loc_block_data_ref.update_concept_label_set_modification_tag(current_label_mod_tag);
        }

        let mut continue_blocking_indi_node: NodeId = Id::NONE;
        if self.continue_individual_node_block(
            blocking_test_indi,
            loc_block_data,
            &mut continue_blocking_indi_node,
            block_alt_data,
            calc_alg_context,
        ) {
            blocker_node = continue_blocking_indi_node;
        } else {
            // W6-DEFER[api]: locBlockData->clearBlockingIndividualNode();
            if self.signature_cached_individual_node_block(
                blocking_test_indi,
                loc_block_data,
                &mut continue_blocking_indi_node,
                block_alt_data,
                calc_alg_context,
            ) {
                blocker_node = continue_blocking_indi_node;
            } else {
                // W6-DEFER[api]: lastContinueTestedBlockingIndiNodeID = locBlockData->getBlockingIndividualNode()
                //   ? ...->getIndividualNodeID() : -1;
                let last_continue_tested_blocking_indi_node_id: Cint64 = -1;
                if node_switch_history.is_some()
                    && loc_block_data.is_some()
                    && prev_node_switch_tag > 0
                {
                    (min_test_indi_node_id, min_test_anc_indi_depth) = calc_alg_context
                        .node_switch_history_min_bounds(
                            node_switch_history,
                            prev_node_switch_tag,
                            0,
                            0,
                        );
                }
                let mut prev_indi_id = calc_alg_context
                    .process_context()
                    .node(blocking_test_indi)
                    .individual_node_id()
                    - 1;
                while blocker_node.is_none()
                    && prev_indi_id > 0
                    && prev_indi_id >= min_test_indi_node_id
                {
                    if prev_indi_id != last_continue_tested_blocking_indi_node_id {
                        let mut prev_indi_node =
                            self.get_up_to_date_individual_by_id(prev_indi_id, calc_alg_context);
                        if !prev_indi_node.is_none()
                            && self
                                .is_individual_node_valid_blocker(prev_indi_node, calc_alg_context)
                            && self.is_individual_node_concept_label_set_modified(
                                &mut prev_indi_node,
                                prev_node_concept_label_mod_tag,
                                calc_alg_context,
                            )
                        {
                            let mut invalid_descendant = false;
                            if calc_alg_context
                                .process_context()
                                .node(prev_indi_node)
                                .individual_ancestor_depth()
                                >= calc_alg_context
                                    .process_context()
                                    .node(blocking_test_indi)
                                    .individual_ancestor_depth()
                            {
                                // make sure the candidate is not a descendant
                                let mut anc_prev_indi_node = prev_indi_node;
                                while !anc_prev_indi_node.is_none()
                                    && calc_alg_context
                                        .process_context()
                                        .node(anc_prev_indi_node)
                                        .individual_ancestor_depth()
                                        >= calc_alg_context
                                            .process_context()
                                            .node(blocking_test_indi)
                                            .individual_ancestor_depth()
                                    && !invalid_descendant
                                {
                                    if calc_alg_context
                                        .process_context()
                                        .node(anc_prev_indi_node)
                                        .individual_node_id()
                                        == calc_alg_context
                                            .process_context()
                                            .node(blocking_test_indi)
                                            .individual_node_id()
                                    {
                                        invalid_descendant = true;
                                    }
                                    anc_prev_indi_node = self.get_ancestor_individual(
                                        &mut anc_prev_indi_node,
                                        calc_alg_context,
                                    );
                                }
                            }

                            if !invalid_descendant {
                                // W6-DEFER[api]: STATINC(ANYWHEREBLOCKINGSEARCHINDINODECOUNT,calcAlgContext);
                                if self.is_individual_node_blocking(
                                    blocking_test_indi,
                                    prev_indi_node,
                                    loc_block_data,
                                    false,
                                    block_alt_data,
                                    calc_alg_context,
                                ) {
                                    blocker_node = prev_indi_node;
                                }
                            }
                        }
                    }
                    prev_indi_id -= 1;
                }
            }
        }
        // W6-DEFER[api]: locBlockData->setBlockingIndividualNode(blockerNode);
        let _ = loc_block_data;
        blocker_node
    }
}
