//! `completion::u09` — W3 method-batch unit #9 (Expansion rules family).
//!
//! Ports 6 methods of Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`
//! (the `∀` / `⊔` / implication / nominal-implication / self expansion rules and
//! the OR-branching executor), per `manifest/01-completion-methods.md` Unit 9:
//!   - `applyALLRule`               [16299-16393]
//!   - `executeORBranching`         [16741-17010]
//!   - `applyORRule`                [17022-17052]
//!   - `applyIMPLICATIONRule`       [17056-17122]
//!   - `applyNOMINALIMPLICATIONRule`[17130-17177]
//!   - `applySELFRule`              [17243-17283]
//!
//! KONCLUDE-PORT-NOTE[ownership]: the C++ signatures take
//! `CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes,
//! bool negate, CCalculationAlgorithmContextBase* calcAlgContext`. Ported as
//! `process_indi: &mut NodeId, con_pro_des: &mut ConProcDescId, negate: bool,
//! calc_alg_context: &mut CalculationAlgorithmContextBase` (pointer-to-pointer →
//! `&mut Id`; the context pointer → `&mut` of the per-thread context). All other
//! arena pointers become typed ids / opaque `Cint64`.
//!
//! W3.5 ARENA RECONCILE (this unit): the descriptor → concept → role READ heads
//! that open every method now resolve LIVE against the per-test arena container
//! (`calc_alg_context.process_context().con_proc_desc(id).get_concept_descriptor()`,
//! `…con_desc(id).get_concept()`, `…ontology_arenas().concept(id).get_role()`, the
//! operand list / count, `is_concept_reapplied`, the node's nominal-individual and
//! dependency-track-point), since those accessors ARE ported (`process/descriptor.rs`,
//! `process/node.rs`, `model/concept.rs`, `model/role.rs`, `model/individual.rs`).
//! The algorithm's OWN state — the `mAppliedALLRuleCount` / `mAppliedORRuleCount`
//! counters and the `mConf*` branching flags — is mutated/read live on `self`.
//!
//! KONCLUDE-PORT-NOTE[api]: everything past those heads stays deferred for the
//! SAME structural reason u01–u06 documented — the satellite subsystem
//! (`getReapplyConceptLabelSet` / `getReapplyRoleSuccessorHash` /
//! `getIndividualMergingHash` and the `CReapplyConceptLabelSet::hasConcept` /
//! `getConceptDescriptor` reads), the `CIndividualLinkEdge` accessors, the
//! `create*Dependency` / `getSuccessorIndividual` / `getLocalizedIndividual` /
//! `addConceptToIndividual(s)` / `addIndividualToProcessingQueue` /
//! `addConceptToReapplyQueue` / `isConceptInReapplyQueue` /
//! `getLinkProcessingRestriction` / `getIndividualNodeLink` /
//! `createNewIndividualsLinksReapplyed` / `createClashed*Descriptor` sibling
//! algorithm methods (other units), and the not-yet-ported
//! `CTriggeredImplicationProcessingRestrictionSpecification` /
//! `CBranchingORProcessingRestrictionSpecification` / `CDisjunctBranchingStatistics`
//! / `CIndividualMergingHash` classes are NONE of them callable here yet. Each such
//! dereference / call is reproduced as a `// W3-DEFER[api]:` (or `[exceptions]` /
//! `[macro]`) line plus the minimal value (`Id::NONE` / `INVALID` / `false` / `0` /
//! empty), preserving the EXACT branch + loop structure and order of operations.
//! Logic is documented, never dropped.
//!
//! KONCLUDE-PORT-NOTE[exceptions]: the C++ `throw CCalculationClashProcessingException`
//! / `throw CCalculationStopProcessingException` unwind out of the rule; the port
//! marks the throw site `// W3-DEFER[exceptions]` and `return`s (control leaves the
//! method, as the throw does). The real unwinding-result plumbing lands with the
//! clash/backtracking units.
//!
//! KONCLUDE-PORT-NOTE[api]: `executeORBranching`'s multi-disjunct branch
//! (cpp 16904–17000) spins up dependent `CSatisfiableCalculationTask`s via the
//! Task / ProcessTagger / TaskPriorityStrategy / UnsatisfiableCacheRetrievalStrategy
//! subsystems and `createCalculationAlgorithmContext`; per the deferral policy
//! (unported Cache/Task/analyser/Strategy) that sub-block keeps its faithful
//! operand-collection control flow with `// W6-DEFER[api]` stubs for the
//! task/context/strategy allocations. Not `todo!`: the structure is portable.

#![allow(
    unused_variables,
    unused_mut,
    unused_assignments,
    dead_code,
    clippy::collapsible_if,
    clippy::collapsible_else_if
)]

use super::super::model::substrate::{Cint64, Id, NegLink, INVALID};
use super::super::model::{ConceptId, IndividualId, RoleId};
use super::super::process::node::IndividualProcessNode;
use super::super::process::{
    ClashDescId, ConDescId, ConProcDescId, DepLinkId, EdgeId, LabelSetId, NodeId,
    RestrictionSpecId, TrackPointId,
};
use super::context::CalculationAlgorithmContextBase;

impl super::algorithm::CompletionTaskHandleAlgorithm {
    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyALLRule`.
    pub fn apply_all_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[macro]: STATINC(ALLRULEAPPLICATIONCOUNT, calc_alg_context)

        // --- arena-resolved read heads (cpp 16301–16305) ---
        let con_des: ConDescId = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .get_concept_descriptor();
        let concept: ConceptId = calc_alg_context
            .process_context()
            .con_desc(con_des)
            .get_concept();
        let role: RoleId = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_role();
        let dep_track_point: TrackPointId = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .get_dependency_track_point();
        let concept_op_linker: Vec<NegLink<ConceptId>> = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operand_list()
            .to_vec();

        // restLink = getLinkProcessingRestriction(conProDes) — the EDGE-TRIGGERED ∀
        // (cpp 16306–16345). The link-install reapply consumption queues an armed
        // ∀-descriptor RESTRICTED to the fresh link; propagating over just that link
        // is what lets a restriction reach a successor acquired LATE (e.g. a link
        // relocated onto this node by a ≤n merge). `get_successor_individual`
        // resolves the OPPOSITE endpoint relative to `process_indi`, so the same
        // branch serves both the forward case (armed on the source) and the
        // inverse-super case (armed on the destination, target = the source).
        let rest_link = self.get_link_processing_restriction(*con_pro_des, calc_alg_context);
        if rest_link != Id::NONE {
            self.applied_all_rule_count += 1;
            // W3-DEFER[api]: isRestrictedTopObjectPropertyPropagation — false here.
            let succ_indi = {
                let mut pi = *process_indi;
                self.get_successor_individual(&mut pi, rest_link, calc_alg_context)
            };
            if succ_indi.is_some() {
                let link_dep_track_point = calc_alg_context
                    .process_context()
                    .edge(rest_link)
                    .get_dependency_track_point();
                let mut next_dep_track_point = TrackPointId::NONE;
                let mut all_dep_node_created = false;
                let mut loc_succ_indi =
                    self.get_localized_individual(succ_indi, false, calc_alg_context);
                for con_op_linker_it in concept_op_linker.iter() {
                    let op_concept: ConceptId = con_op_linker_it.target;
                    let op_con_neg: bool = con_op_linker_it.negated ^ negate;
                    let ls: LabelSetId = calc_alg_context
                        .process_context()
                        .node(loc_succ_indi)
                        .use_reapply_con_label_set;
                    let has_concept = ls != Id::NONE
                        && self.label_set_contains_concept_resolved(
                            ls,
                            op_concept,
                            op_con_neg,
                            calc_alg_context,
                        );
                    if !has_concept {
                        if !all_dep_node_created {
                            all_dep_node_created = true;
                            self.create_all_dependency(
                                &mut next_dep_track_point,
                                process_indi,
                                con_des,
                                dep_track_point,
                                link_dep_track_point,
                                calc_alg_context,
                            );
                        }
                        self.add_concept_to_individual(
                            op_concept,
                            op_con_neg,
                            &mut loc_succ_indi,
                            next_dep_track_point,
                            true,
                            true,
                            calc_alg_context,
                        );
                        if calc_alg_context.has_pending_signal() {
                            return;
                        }
                    }
                }
                // W15-rbox inline transitivity (see the general branch): the ∀
                // itself re-propagates over the restricted link too.
                if calc_alg_context
                    .ontology_arenas()
                    .role(role)
                    .is_transitive()
                {
                    let ls: LabelSetId = calc_alg_context
                        .process_context()
                        .node(loc_succ_indi)
                        .use_reapply_con_label_set;
                    let has_all_self = ls != Id::NONE
                        && self.label_set_contains_concept_resolved(
                            ls,
                            concept,
                            negate,
                            calc_alg_context,
                        );
                    if !has_all_self {
                        if !all_dep_node_created {
                            all_dep_node_created = true;
                            self.create_all_dependency(
                                &mut next_dep_track_point,
                                process_indi,
                                con_des,
                                dep_track_point,
                                link_dep_track_point,
                                calc_alg_context,
                            );
                        }
                        self.add_concept_to_individual(
                            concept,
                            negate,
                            &mut loc_succ_indi,
                            next_dep_track_point,
                            true,
                            true,
                            calc_alg_context,
                        );
                        if calc_alg_context.has_pending_signal() {
                            return;
                        }
                    }
                }
                self.add_individual_to_processing_queue(loc_succ_indi, calc_alg_context);
            }
            return;
        }

        // General ∀: re-propagate the universal restriction to every existing
        // role-successor (cpp 16348–16392). The direct node-level
        // role-successor iterators are bypassed here; the context-threaded
        // `ht_role_successor_links` (u08) resolves the successor-role hash for real.
        //
        // W15-rbox: targets and their physical links are RBox-resolved by
        // `ht_all_rule_target_links` (u10):
        //  - role HIERARCHY (`R ⊑ S`): an R-successor is also an S-successor, so a
        //    `∀S.C` reaches it (Konclude registers an edge per indirect super-role on
        //    install; the port resolves super-roles on lookup);
        //  - INVERSE roles (`∀R⁻.C`): the predecessor reached via the node's ancestor
        //    link (an R-edge `pred --R--> node` makes `pred` an R⁻-successor of `node`).
        // TRANSITIVE roles (`Trans(S)`): in addition to the operands `C`, the `∀S.C`
        // concept ITSELF is propagated to every S-successor so it re-fires at the next
        // hop (the SHIQ transitivity ∀-rule). KONCLUDE-PORT-NOTE[api]: Konclude encodes
        // this in the normaliser (the `∀` operand list of a transitive role carries a
        // re-propagating `∀` concept) rather than inline in `applyALLRule`; the port
        // applies it inline here per the W15 task directive, behaviour-equivalent.
        self.applied_all_rule_count += 1;
        let is_transitive: bool = calc_alg_context
            .ontology_arenas()
            .role(role)
            .is_transitive();
        let role_targets = self.ht_all_rule_target_links(*process_indi, role, calc_alg_context);
        for (link, succ_indi) in role_targets {
            // W3-DEFER[api]: isRestrictedTopObjectPropertyPropagation — treated as false
            // (no restricted top-object-property propagation in this fragment).
            let link_dep_track_point = calc_alg_context
                .process_context()
                .edge(link)
                .get_dependency_track_point();
            let mut next_dep_track_point = TrackPointId::NONE;
            let mut all_dep_node_created = false;
            let mut loc_succ_indi: NodeId =
                self.get_localized_individual(succ_indi, false, calc_alg_context);
            for con_op_linker_it in concept_op_linker.iter() {
                let op_concept: ConceptId = con_op_linker_it.target;
                let op_con_neg: bool = con_op_linker_it.negated ^ negate;
                // conLabelSet->hasConcept(opConcept, opConNeg) — skip if already present.
                // Tag-RESOLVED (ls1::has_concept is a W2-DEFER stub: raw-index key +
                // always-false negation; a raw/tag collision would SKIP a required add).
                let ls: LabelSetId = calc_alg_context
                    .process_context()
                    .node(loc_succ_indi)
                    .use_reapply_con_label_set;
                let has_concept = ls != Id::NONE
                    && self.label_set_contains_concept_resolved(
                        ls,
                        op_concept,
                        op_con_neg,
                        calc_alg_context,
                    );
                if !has_concept {
                    // Konclude cpp 16423–16425: one CALLDependencyNode per traversed
                    // link, shared by every missing operand on that successor.  Its
                    // two parents are the ∀ descriptor and the physical role edge.
                    if !all_dep_node_created {
                        all_dep_node_created = true;
                        self.create_all_dependency(
                            &mut next_dep_track_point,
                            process_indi,
                            con_des,
                            dep_track_point,
                            link_dep_track_point,
                            calc_alg_context,
                        );
                    }
                    self.add_concept_to_individual(
                        op_concept,
                        op_con_neg,
                        &mut loc_succ_indi,
                        next_dep_track_point,
                        true,
                        true,
                        calc_alg_context,
                    );
                    if calc_alg_context.has_pending_signal() {
                        return;
                    }
                }
            }
            // W15-rbox transitivity: re-propagate `∀role.C` itself to the successor.
            if is_transitive {
                // tag-RESOLVED contains (see the operand guard above).
                let ls: LabelSetId = calc_alg_context
                    .process_context()
                    .node(loc_succ_indi)
                    .use_reapply_con_label_set;
                let has_all_self = ls != Id::NONE
                    && self.label_set_contains_concept_resolved(
                        ls,
                        concept,
                        negate,
                        calc_alg_context,
                    );
                if !has_all_self {
                    if !all_dep_node_created {
                        all_dep_node_created = true;
                        self.create_all_dependency(
                            &mut next_dep_track_point,
                            process_indi,
                            con_des,
                            dep_track_point,
                            link_dep_track_point,
                            calc_alg_context,
                        );
                    }
                    self.add_concept_to_individual(
                        concept,
                        negate,
                        &mut loc_succ_indi,
                        next_dep_track_point,
                        true,
                        true,
                        calc_alg_context,
                    );
                    if calc_alg_context.has_pending_signal() {
                        return;
                    }
                }
            }
            self.add_individual_to_processing_queue(loc_succ_indi, calc_alg_context);
        }

        let is_concept_reapplied: bool = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .is_concept_reapplied();
        if !is_concept_reapplied {
            // addConceptToReapplyQueue(conDes, role, processIndi, true, depTrackPoint, ...) [u10, role overload]
            self.add_concept_to_reapply_queue_role(
                con_des,
                role,
                *process_indi,
                true,
                dep_track_point,
                calc_alg_context,
            );
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::executeORBranching`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: `plannedBranchingProcessRestriction`'s type
    /// (`CBranchingORProcessingRestrictionSpecification*`) is not ported yet → opaque
    /// `Cint64` (`INVALID` == `nullptr`); all of its `getContainedOperand` /
    /// `getFirst…` / `getSecond…` / `getClashedConceptDescriptors` reads, the
    /// `CSortedNegLinker<CConcept*>` chain traversals they return, and the
    /// `CDisjunctBranchingStatistics` chains are deferred. The faithful list-driven
    /// control flow (operand contains-check, the `notPosAndNegContainedOperandCount`
    /// 0/1/>1 dispatch, semantic branching) is preserved.
    pub fn execute_or_branching(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        planned_branching_process_restriction: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        self.applied_or_rule_count += 1;
        // W3-DEFER[macro]: STATINC(OREXECUTIONCOUNT, calc_alg_context)

        // Live Rust representation of Konclude's planned restriction.  Keep
        // the transcription below as a source map, but all production calls
        // now enter with this typed payload and return from this block.
        if planned_branching_process_restriction != INVALID {
            let rest_id = RestrictionSpecId::new(planned_branching_process_restriction);
            let (already_contained, planned_operands, mut clash_con_des_linker) = {
                let rest = calc_alg_context.process_context().restriction_spec(rest_id);
                (
                    rest.or_contained_operand.is_some(),
                    rest.or_operands.clone(),
                    rest.or_clashed_concept_descriptors,
                )
            };
            if already_contained {
                return;
            }

            let label_set = calc_alg_context
                .process_context()
                .node(*process_indi)
                .use_reapply_con_label_set;
            let mut remaining: Vec<super::super::model::substrate::NegLink<ConceptId>> = Vec::new();
            for operand in planned_operands {
                let effective_negation = operand.negated ^ negate;
                let mut checking_concept = operand.target;
                let mut checking_negation = effective_negation;
                let mut contained_negation = false;
                let mut contains = label_set.is_some()
                    && self.label_set_contains_concept_get_negated_resolved(
                        label_set,
                        checking_concept,
                        Some(&mut contained_negation),
                        calc_alg_context,
                    );
                if !contains
                    && self.get_additional_disjunct_checking_concept(
                        operand.target,
                        effective_negation,
                        Some(&mut checking_concept),
                        Some(&mut checking_negation),
                        calc_alg_context,
                    )
                {
                    contains = label_set.is_some()
                        && self.label_set_contains_concept_get_negated_resolved(
                            label_set,
                            checking_concept,
                            Some(&mut contained_negation),
                            calc_alg_context,
                        );
                }
                if contains {
                    if contained_negation == checking_negation {
                        return;
                    }

                    // Konclude extends `clashConDesLinker` with the exact
                    // opposite-polarity descriptor that ruled this operand
                    // out.  Its dependency is load-bearing: the subsequent
                    // ORONLYOPTION node must depend on every eliminated
                    // choice, including a branch-local one.
                    let tag = calc_alg_context
                        .ontology_arenas()
                        .concept(checking_concept)
                        .get_concept_tag();
                    let mut contained_con_des = ConDescId::NONE;
                    let mut contained_con_dep_track_point = TrackPointId::NONE;
                    let contained_with_dependency = {
                        let process_context = calc_alg_context.process_context();
                        process_context
                            .label_set(label_set)
                            .get_concept_descriptor_by_tag_in_context(
                                process_context,
                                tag,
                                &mut contained_con_des,
                                &mut contained_con_dep_track_point,
                            )
                    };
                    if contained_with_dependency && contained_con_des.is_some() {
                        clash_con_des_linker = self.create_clashed_concept_descriptor(
                            clash_con_des_linker,
                            process_indi,
                            contained_con_des,
                            contained_con_dep_track_point,
                            calc_alg_context,
                        );
                    }
                    continue;
                }
                if self.has_saturated_clashed_flag_for_concept(
                    checking_concept,
                    checking_negation,
                    calc_alg_context,
                ) {
                    continue;
                }

                if let Some(previous) = remaining
                    .iter()
                    .find(|previous| previous.target == operand.target)
                {
                    if previous.negated == operand.negated {
                        continue;
                    }
                    // A v not-A makes the remaining disjunction tautological.
                    return;
                }
                remaining.push(operand);
            }

            let (con_des, dep_track_point) = {
                let cpd = calc_alg_context
                    .process_context()
                    .con_proc_desc(*con_pro_des);
                (
                    cpd.get_concept_descriptor(),
                    cpd.get_dependency_track_point(),
                )
            };
            match remaining.len() {
                0 => {
                    if std::env::var_os("KM_HT_OR_TRACE").is_some() {
                        eprintln!("OR-EXEC clash survivors=0");
                    }
                    let clash = self.create_clashed_concept_descriptor(
                        clash_con_des_linker,
                        process_indi,
                        con_des,
                        dep_track_point,
                        calc_alg_context,
                    );
                    calc_alg_context.raise_clash(clash);
                }
                1 => {
                    let only = remaining[0];
                    if std::env::var_os("KM_HT_OR_TRACE").is_some() {
                        eprintln!(
                            "OR-EXEC single tag={} negated={}",
                            calc_alg_context
                                .ontology_arenas()
                                .concept(only.target)
                                .get_concept_tag(),
                            only.negated ^ negate,
                        );
                    }

                    // Exact port of Konclude cpp 16929-16941:
                    //   for every clashed (eliminated) operand, create a
                    //   CONNECTION dependency and append its continuation to
                    //   the additional-dependency chain of ORONLYOPTION.
                    let mut dependencies: DepLinkId = Id::NONE;
                    let mut clash_con_des_linker_it = clash_con_des_linker;
                    while clash_con_des_linker_it.is_some() {
                        let (clashed_con_des, clashed_dep_track_point, next) = {
                            let clash = calc_alg_context
                                .process_context()
                                .clash_desc(clash_con_des_linker_it);
                            (
                                clash.get_concept_descriptor(),
                                clash.get_dependency_track_point(),
                                clash.get_next(),
                            )
                        };
                        let connection_dependency = self.create_connection_dependency(
                            process_indi,
                            clashed_con_des,
                            clashed_dep_track_point,
                            calc_alg_context,
                        );
                        if connection_dependency.is_some() {
                            let connection_track_point = calc_alg_context
                                .process_context_mut()
                                .materialize_continue_dependency_track_point(connection_dependency);
                            dependencies = calc_alg_context.process_context_mut().alloc_dep_link(
                                super::super::process::dependency::DependencyLink {
                                    dep_track_point: connection_track_point,
                                    next: dependencies,
                                },
                            );
                        }
                        clash_con_des_linker_it = next;
                    }

                    let mut new_dependency_track_point = TrackPointId::NONE;
                    self.create_oronly_option_dependency(
                        &mut new_dependency_track_point,
                        process_indi,
                        con_des,
                        dep_track_point,
                        dependencies,
                        calc_alg_context,
                    );
                    self.add_concept_to_individual(
                        only.target,
                        only.negated ^ negate,
                        process_indi,
                        new_dependency_track_point,
                        true,
                        false,
                        calc_alg_context,
                    );
                    if !calc_alg_context.has_pending_signal() {
                        self.test_individual_node_unsatisfiable_cached(
                            *process_indi,
                            calc_alg_context,
                        );
                    }
                }
                _ => {
                    if std::env::var_os("KM_HT_OR_TRACE").is_some() {
                        eprintln!("OR-EXEC branch survivors={}", remaining.len());
                    }
                    self.start_or_branching_in_process(
                        *process_indi,
                        *con_pro_des,
                        negate,
                        remaining,
                        clash_con_des_linker,
                        calc_alg_context,
                    );
                }
            }
            return;
        }

        // --- arena-resolved read heads (cpp 16744–16746) ---
        let con_des: ConDescId = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .get_concept_descriptor();
        let concept: ConceptId = calc_alg_context
            .process_context()
            .con_desc(con_des)
            .get_concept();
        let dep_track_point: TrackPointId = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .get_dependency_track_point();
        // W3-DEFER[api]: processIndi->getReapplyConceptLabelSet(false)
        let con_set: LabelSetId = Id::NONE;

        // CSortedNegLinker<CConcept*>* contained / first/second not-pos-and-neg-contained operands.
        // W3-DEFER[api]: not-yet-ported CSortedNegLinker chains → opaque Cint64 cursors.
        let mut contained_operand: Cint64 = INVALID;
        let mut first_not_pos_and_neg_contained_operand: Cint64 = INVALID;
        let mut second_not_pos_and_neg_contained_operand: Cint64 = INVALID;
        let mut first_not_pos_and_neg_contained_operand_branch_stats: Cint64 = INVALID;
        let mut second_not_pos_and_neg_contained_operand_branch_stats: Cint64 = INVALID;

        // CPROCESSINGLIST locals (cpp 16755–16756). [api] element types are the
        // deferred CSortedNegLinker / CDisjunctBranchingStatistics → Cint64.
        let mut not_contained_operands_list: Vec<Cint64> = Vec::new();
        let mut not_contained_branching_stats_list: Vec<Cint64> = Vec::new();

        let mut not_pos_and_neg_contained_operand_count: Cint64 = 0;
        if planned_branching_process_restriction != INVALID {
            // W3-DEFER[api]: plannedBranchingProcessRestriction->getContainedOperand()
            contained_operand = INVALID;
            // W3-DEFER[api]: plannedBranchingProcessRestriction->getFirstNotPosAndNegContainedOperand()
            first_not_pos_and_neg_contained_operand = INVALID;
            // W3-DEFER[api]: plannedBranchingProcessRestriction->getSecondNotPosAndNegContainedOperand()
            second_not_pos_and_neg_contained_operand = INVALID;
            // W3-DEFER[api]: plannedBranchingProcessRestriction->getFirstNotPosAndNegContainedOperandBranchingStatistics()
            first_not_pos_and_neg_contained_operand_branch_stats = INVALID;
            // W3-DEFER[api]: plannedBranchingProcessRestriction->getSecondNotPosAndNegContainedOperandBranchingStatistics()
            second_not_pos_and_neg_contained_operand_branch_stats = INVALID;
        }

        // W3-DEFER[api]: plannedBranchingProcessRestriction->getClashedConceptDescriptors()
        let mut clash_con_des_linker: Cint64 = INVALID;

        if contained_operand == INVALID {
            // check if one operand is already in the concept set
            if first_not_pos_and_neg_contained_operand != INVALID {
                // W3-DEFER[api]: firstNotPosAndNegContainedOperand->isNegated() ^ negate
                let correct_negation = negate;
                let mut op_checking_negation = correct_negation;
                // W3-DEFER[api]: firstNotPosAndNegContainedOperand->getData()
                let mut checking_concept: ConceptId = Id::NONE;
                // W3-DEFER[api]: conSet->getConceptDescriptor(checkingConcept, containedConDes, containedConDepTrackPoint)
                let mut contained_con_des: ConDescId = Id::NONE;
                let mut contained_con_dep_track_point: TrackPointId = Id::NONE;
                let mut contains = false;
                // W3-DEFER[api]: getAdditionalDisjunctCheckingConcept(checkingConcept, opCheckingNegation, &checkingConcept, &opCheckingNegation, calcAlgContext)
                let has_additional_checking_concept = false;
                if !contains && has_additional_checking_concept {
                    // W3-DEFER[api]: conSet->getConceptDescriptor(checkingConcept, containedConDes, containedConDepTrackPoint)
                    contains = false;
                }
                if contains {
                    // W3-DEFER[api]: containedConDes->isNegated()
                    let contains_negation = false;
                    if contains_negation == op_checking_negation {
                        contained_operand = first_not_pos_and_neg_contained_operand;
                        // update first/second not contained operands
                        first_not_pos_and_neg_contained_operand =
                            second_not_pos_and_neg_contained_operand;
                        first_not_pos_and_neg_contained_operand_branch_stats =
                            second_not_pos_and_neg_contained_operand_branch_stats;
                    } else {
                        first_not_pos_and_neg_contained_operand = INVALID;
                        // W3-DEFER[api]: createClashedConceptDescriptor(clashConDesLinker, processIndi, containedConDes, containedConDepTrackPoint, calcAlgContext)
                        clash_con_des_linker = INVALID;
                    }
                } else {
                    not_pos_and_neg_contained_operand_count += 1;
                    not_contained_operands_list.push(first_not_pos_and_neg_contained_operand);
                    not_contained_branching_stats_list
                        .push(first_not_pos_and_neg_contained_operand_branch_stats);
                }
                if contained_operand == INVALID
                    && second_not_pos_and_neg_contained_operand != INVALID
                {
                    let mut remaining_disjuncts_useless = false;
                    // W3-DEFER[api]: CSortedNegLinker<CConcept*>* containsOperandCheckIt = secondNotPosAndNegContainedOperand
                    let mut contains_operand_check_it: Cint64 =
                        second_not_pos_and_neg_contained_operand;
                    let mut disjunct_branch_stats_check_it: Cint64 =
                        second_not_pos_and_neg_contained_operand_branch_stats;
                    second_not_pos_and_neg_contained_operand = INVALID;
                    while contains_operand_check_it != INVALID {
                        // W3-DEFER[api]: containsOperandCheckIt->isNegated() ^ negate
                        let correct_negation = negate;
                        let mut op_checking_negation = correct_negation;
                        // W3-DEFER[api]: containsOperandCheckIt->getData()
                        let checking_concept: ConceptId = Id::NONE;
                        let mut contained_con_des: ConDescId = Id::NONE;
                        let mut contained_con_dep_track_point: TrackPointId = Id::NONE;
                        // W3-DEFER[api]: conSet->getConceptDescriptor(checkingConcept, containedConDes, containedConDepTrackPoint)
                        let mut contains = false;
                        // W3-DEFER[api]: getAdditionalDisjunctCheckingConcept(checkingConcept, opCheckingNegation, &checkingConcept, &opCheckingNegation, calcAlgContext)
                        let has_additional_checking_concept = false;
                        if !contains && has_additional_checking_concept {
                            // W3-DEFER[api]: conSet->getConceptDescriptor(checkingConcept, containedConDes, containedConDepTrackPoint)
                            contains = false;
                        }
                        if contains {
                            // W3-DEFER[api]: containedConDes->isNegated()
                            let contains_negation = false;
                            if contains_negation == op_checking_negation {
                                contained_operand = contains_operand_check_it;
                                break;
                            } else {
                                // W3-DEFER[api]: createClashedConceptDescriptor(clashConDesLinker, processIndi, containedConDes, containedConDepTrackPoint, calcAlgContext)
                                clash_con_des_linker = INVALID;
                            }
                        } else {
                            // W3-DEFER[api]: hasSaturatedClashedFlagForConcept(checkingConcept, opCheckingNegation, calcAlgContext)
                            let has_saturated_clashed_flag = false;
                            if !has_saturated_clashed_flag {
                                let mut critical_with_other_operand = false;
                                if remaining_disjuncts_useless {
                                    critical_with_other_operand = true;
                                }
                                for not_cont_op_linker in not_contained_operands_list.iter() {
                                    if critical_with_other_operand {
                                        break;
                                    }
                                    // W3-DEFER[api]: containsOperandCheckIt->getData() == notContOpLinker->getData()
                                    let same_concept = false;
                                    if same_concept {
                                        // W3-DEFER[api]: containsOperandCheckIt->isNegated() == notContOpLinker->isNegated()
                                        let same_negation = false;
                                        if same_negation {
                                            critical_with_other_operand = true;
                                        } else {
                                            remaining_disjuncts_useless = true;
                                        }
                                    }
                                }

                                if !critical_with_other_operand {
                                    not_pos_and_neg_contained_operand_count += 1;
                                    not_contained_operands_list.push(contains_operand_check_it);
                                    not_contained_branching_stats_list
                                        .push(disjunct_branch_stats_check_it);
                                    // update first/second not contained operands
                                    if first_not_pos_and_neg_contained_operand == INVALID {
                                        first_not_pos_and_neg_contained_operand =
                                            contains_operand_check_it;
                                        first_not_pos_and_neg_contained_operand_branch_stats =
                                            disjunct_branch_stats_check_it;
                                    } else {
                                        if second_not_pos_and_neg_contained_operand == INVALID {
                                            second_not_pos_and_neg_contained_operand =
                                                contains_operand_check_it;
                                            second_not_pos_and_neg_contained_operand_branch_stats =
                                                disjunct_branch_stats_check_it;
                                        }
                                    }
                                }
                            }
                        }
                        // W3-DEFER[api]: containsOperandCheckIt = containsOperandCheckIt->getNext()
                        contains_operand_check_it = INVALID;
                        if disjunct_branch_stats_check_it != INVALID {
                            // W3-DEFER[api]: disjunctBranchStatsCheckIt = disjunctBranchStatsCheckIt->getNext()
                            disjunct_branch_stats_check_it = INVALID;
                        }
                    }
                }
            }
        }

        if contained_operand == INVALID {
            // collect clashes / do branching
            if not_pos_and_neg_contained_operand_count == 1 {
                // W3-DEFER[macro]: STATINC(ORSINGLEBRANCHCOUNT, calc_alg_context)

                // W3-DEFER[api]: CDependency* dependencies = nullptr;
                let mut dependencies: Cint64 = INVALID;
                // W3-DEFER[api]: for clashConDesLinkerIt in clashConDesLinker chain:
                //   clashedConDes = (CClashedConceptDescriptor*)clashConDesLinkerIt;
                //   connDep = createCONNECTIONDependency(processIndi, clashedConDes->getConceptDescriptor(), clashConDesLinkerIt->getDependencyTrackPoint(), calcAlgContext);
                //   dependencies = connDep->append(dependencies);

                let mut new_dependency_track_point: TrackPointId = Id::NONE;
                // W3-DEFER[api]: createORONLYOPTIONDependency(newDependencyTrackPoint, processIndi, conDes, depTrackPoint, dependencies, calcAlgContext)
                new_dependency_track_point = Id::NONE;

                // W3-DEFER[api]: operandConcept = *notContainedOperandsList.constBegin()
                let operand_concept: Cint64 = not_contained_operands_list
                    .first()
                    .copied()
                    .unwrap_or(INVALID);
                let mut disj_branch_stats: Cint64 = INVALID;
                if not_contained_operands_list.len() == not_contained_branching_stats_list.len() {
                    // W3-DEFER[api]: disjBranchStats = *notContainedBranchingStatsList.constBegin()
                    disj_branch_stats = not_contained_branching_stats_list
                        .first()
                        .copied()
                        .unwrap_or(INVALID);
                }
                // W3-DEFER[api]: operandConcept->isNegated() ^ negate
                let add_op_negated = negate;
                // W3-DEFER[api]: addConceptToIndividual(operandConcept->getData(), addOpNegated, processIndi, newDependencyTrackPoint, true, false, calcAlgContext)

                // testUnsatisfiableCacheForBranchedDisjuncts (constant-true in the
                // generative strategy) → testIndividualNodeUnsatisfiableCached.
                // LIVE ELSEWHERE: this transcription path is dead (the in-process
                // branch machinery in u03 `initialize_or_processing` / u02's
                // disjunction advance carries the live probe after each disjunct
                // addition) — do not double-wire here.
                let test_unsat_cache = false;
                if test_unsat_cache {
                    // testIndividualNodeUnsatisfiableCached(processIndi, calcAlgContext)
                }
            } else if not_pos_and_neg_contained_operand_count > 1 {
                // W3-DEFER[macro]: STATINC(ORMULTIPLEBRANCHCOUNT, calc_alg_context)

                // testUnsatisfiableCacheForDisjunctionBranching (constant-true in
                // the generative strategy) → testIndividualNodeUnsatisfiableCached.
                // LIVE ELSEWHERE: dead transcription path — the live probes ride
                // the in-process branch machinery (u03 push / u02 advance).
                let test_unsat_cache = false;
                if test_unsat_cache {
                    // testIndividualNodeUnsatisfiableCached(processIndi, calcAlgContext)
                }

                // W3-DEFER[api]: createORDependency(processIndi, conDes, depTrackPoint, calcAlgContext)
                let or_dependency_node: Cint64 = INVALID;
                if or_dependency_node != INVALID && clash_con_des_linker != INVALID {
                    // W3-DEFER[api]: orDependencyNode->addBranchClashes(clashConDesLinker)
                }

                let new_task_list = self.create_dependend_branching_task_list(
                    not_pos_and_neg_contained_operand_count,
                    calc_alg_context,
                );
                // W6-DEFER[api]: processorContext = calcAlgContext->getUsedTaskProcessorContext()
                //
                // Per-branch task creation (cpp 16922–16996): for each new
                // CSatisfiableCalculationTask in the dependent list, the C++:
                //   - builds a fresh CCalculationAlgorithmContext via createCalculationAlgorithmContext,
                //   - bumps the new ProcessTagger branching/localization tags,
                //   - collects the semantic-branching addingConceptLinker over notContainedOperandsList
                //     (posOperand = (opIt == branchOpConIt); addOpNegated = !posOperand ^ operandConcept->isNegated() ^ negate;
                //      include when posOperand || mConfSemanticBranching ||
                //      mConfAtomicSemanticBranching && isConceptAdditionAtomaric(...)),
                //   - allocates a CBranchingInstructionAddIndividualConcepts and sets it on the new databox,
                //   - sets the new task priority via the TaskPriorityStrategy,
                //   - communicateTaskCreation(newTaskList), then throws CCalculationStopProcessingException.
                //
                // The semantic-branching INCLUSION test reads the ported config flags
                // live (mConfSemanticBranching / mConfAtomicSemanticBranching):
                let _conf_semantic_branching = self.conf_semantic_branching;
                let _conf_atomic_semantic_branching = self.conf_atomic_semantic_branching;
                // Child context/databox/strategy/scheduler machinery is
                // W6-DEFER[api]; the dependent task list itself is live.
                let _ = new_task_list;
                // throw CCalculationStopProcessingException(true)
                calc_alg_context.raise_stop(true);
                return;
            } else {
                // throw clash
                // createClashedConceptDescriptor(clashConDesLinker, processIndi, conDes, depTrackPoint, ...)
                // KONCLUDE-PORT-NOTE: the accumulated `clashConDesLinker` chain from the
                // (deferred) operand-contains checks above is the unported `Cint64` stub
                // (always INVALID here), so the new descriptor chains onto an empty prev.
                let _ = clash_con_des_linker;
                let clash_des: ClashDescId = self.create_clashed_concept_descriptor(
                    Id::NONE,
                    process_indi,
                    con_des,
                    dep_track_point,
                    calc_alg_context,
                );
                // throw CCalculationClashProcessingException(clashConDesLinker)
                calc_alg_context.raise_clash(clash_des);
                return;
            }
        } else {
            // contains at least one operand, branching is not necessary, ignoring or concept
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyORRule`.
    pub fn apply_or_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[macro]: STATINC(ORRULEAPPLICATIONCOUNT, calc_alg_context)

        // --- arena-resolved read heads (cpp 17024–17028) ---
        let con_des: ConDescId = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .get_concept_descriptor();
        let concept: ConceptId = calc_alg_context
            .process_context()
            .con_desc(con_des)
            .get_concept();
        let dep_track_point: TrackPointId = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .get_dependency_track_point();

        let op_count: Cint64 = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operand_count();
        if let Some(watch_tag) = std::env::var("KM_BRIDGE_WATCH_TAG")
            .ok()
            .and_then(|value| value.parse::<Cint64>().ok())
        {
            let operands = calc_alg_context
                .ontology_arenas()
                .concept(concept)
                .get_operand_list()
                .to_vec();
            if operands.iter().any(|link| {
                calc_alg_context
                    .ontology_arenas()
                    .concept(link.target)
                    .get_concept_tag()
                    == watch_tag
                    && !(link.negated ^ negate)
            }) {
                let label_set = calc_alg_context
                    .process_context()
                    .node(*process_indi)
                    .use_reapply_con_label_set;
                let operand_state: Vec<(Cint64, bool, bool)> = operands
                    .iter()
                    .map(|link| {
                        let operand_negated = link.negated ^ negate;
                        let tag = calc_alg_context
                            .ontology_arenas()
                            .concept(link.target)
                            .get_concept_tag();
                        let present = label_set != Id::NONE
                            && self.label_set_contains_concept_resolved(
                                label_set,
                                link.target,
                                operand_negated,
                                calc_alg_context,
                            );
                        (tag, operand_negated, present)
                    })
                    .collect();
                eprintln!(
                    "WATCH-OR-OPERAND tag={} node={} parent={} parent-op={} negate={} operands(tag,neg,present)={:?}",
                    watch_tag,
                    calc_alg_context
                        .process_context()
                        .node(*process_indi)
                        .individual_node_id(),
                    calc_alg_context
                        .ontology_arenas()
                        .concept(concept)
                        .get_concept_tag(),
                    calc_alg_context
                        .ontology_arenas()
                        .concept(concept)
                        .get_operator_code(),
                    negate,
                    operand_state,
                );
            }
        }

        if op_count <= 0 {
            // throw clash
            // createClashedConceptDescriptor(clashConDesLinker, processIndi, conDes, depTrackPoint, ...)
            let clash_con_des_linker: ClashDescId = self.create_clashed_concept_descriptor(
                Id::NONE,
                process_indi,
                con_des,
                dep_track_point,
                calc_alg_context,
            );
            // throw CCalculationClashProcessingException(clashConDesLinker)
            calc_alg_context.raise_clash(clash_con_des_linker);
            return;
        } else if op_count == 1 {
            // apply AND rule
            self.apply_and_rule(process_indi, con_pro_des, negate, calc_alg_context);
        } else {
            // CBranchingORProcessingRestrictionSpecification* plannedBranchingProcessRestriction.
            // KONCLUDE-PORT-NOTE[api]: the restriction-spec out-handle is `RestrictionSpecId`
            // for the plan_or_processing sibling (u03); execute_or_branching still carries it
            // as the opaque `Cint64` cursor (its body pivots on the unported spec), so the
            // built handle is not yet threaded across — passed as `INVALID` below.
            let mut planned_branching_process_restriction: RestrictionSpecId = Id::NONE;
            // planORProcessing(processIndi, conProDes, negate, &plannedBranchingProcessRestriction, ...) [u03]
            let plan_or_processing = self.plan_or_processing(
                *process_indi,
                *con_pro_des,
                negate,
                &mut planned_branching_process_restriction,
                calc_alg_context,
            );
            if !plan_or_processing {
                let has_sat_or_completion_cached = calc_alg_context
                    .process_context()
                    .node(*process_indi)
                    .has_partial_processing_restriction_flags(
                        IndividualProcessNode::PRF_SATISFIABLECACHED
                            | IndividualProcessNode::PRF_COMPLETIONGRAPHCACHED,
                    );
                if self.conf_sat_exp_cached_disj_absorp && has_sat_or_completion_cached {
                    // STATINC(SATCACHEDABSORBEDDISJUNCTIONCONCEPTSCOUNT). The
                    // descriptor is replayed by u10 if u21 later abolishes the
                    // satisfiable/completion-graph cache flag.
                    self.saturation_cached_absorbed_disjunction_count += 1;
                    self.add_satisfiable_cached_absorbed_disjunction_concept(
                        con_des,
                        *process_indi,
                        planned_branching_process_restriction,
                        dep_track_point,
                        calc_alg_context,
                    );
                } else {
                    // Delaying failed, execute the planned OR rule.
                    self.execute_or_branching(
                        process_indi,
                        con_pro_des,
                        negate,
                        planned_branching_process_restriction.raw,
                        calc_alg_context,
                    );
                }
            }
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyIMPLICATIONRule`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: `CTriggeredImplicationProcessingRestrictionSpecification`
    /// is not ported → opaque `Cint64`; its trigger cursor / dependency reads are
    /// deferred. The trigger-search loop structure is preserved.
    pub fn apply_implication_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[macro]: STATINC(IMPLICATIONRULEAPPLICATIONCOUNT, calc_alg_context)

        // --- arena-resolved read heads (cpp 17058–17063) ---
        let con_des: ConDescId = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .get_concept_descriptor();
        let concept: ConceptId = calc_alg_context
            .process_context()
            .con_desc(con_des)
            .get_concept();
        let dep_track_point: TrackPointId = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .get_dependency_track_point();
        let proc_rest: RestrictionSpecId = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .get_processing_restriction_specification();
        let op_count: Cint64 = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operand_count();
        let op_linker: Vec<NegLink<ConceptId>> = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operand_list()
            .to_vec();
        // W3-DEFER[memory-pool]: calcAlgContext->getUsedProcessTaskMemoryAllocationManager()
        let _ = (concept, op_count);

        // KONCLUDE-PORT-NOTE[api]: `CTriggeredImplicationProcessingRestrictionSpecification` is
        // unported. For the BASIC GCI/unfold the trigger cursor is reproduced DIRECTLY over the
        // operand list: Konclude installs `opLinker->getNext()` (every operand AFTER the implied
        // head) as the trigger sequence, and the implied concept is `opLinker->getData()` (the
        // first operand). An `A ⊑ B` GCI is stored as `¬A ⊔ B`: operands `[B(implied), ¬A(trigger)]`,
        // and the rule fires when each trigger concept is present with the OPPOSITE polarity of the
        // trigger linker (i.e. positive A for the negated `¬A` linker).
        //
        // The re-triggered case (`procRest != NONE`, reached only after `addConceptToReapplyQueue`
        // re-fires the rule once a previously-missing trigger appears) keeps the reapply-install
        // path W3-DEFER: a trigger that is ABSENT here simply does not (yet) fire the implication.
        // That is sound; it is incomplete only for inputs where a trigger is added to the node
        // strictly AFTER the implication concept is processed (closed once the condensed reapply
        // queue / `CTriggeredImplicationProcessingRestrictionSpecification` is ported). For the
        // basic unfold (all triggers already on the node) the implication fires here.
        let _ = proc_rest;

        // CReapplyConceptLabelSet* conSet = processIndi->getReapplyConceptLabelSet(true);
        let con_set: LabelSetId = calc_alg_context
            .process_context_mut()
            .node_reapply_concept_label_set(*process_indi);

        // search next not existing trigger — while (triggImpProcRes->hasConceptImplicationTrigger())
        let mut all_triggers_available = true;
        // the FIRST absent trigger (the C++ `triggerLinkerIt` cursor left at the
        // break position) — the install-to-trigger target below.
        let mut missing_trigger: Option<NegLink<ConceptId>> = None;
        // Satisfied triggers whose dependency differs from the implication's —
        // the CONNECTION-dependency chain hung onto the fired implication
        // (Konclude accumulates these on the triggered-implication restriction
        // spec; this port re-scans ALL triggers per invocation, so the chain
        // is built locally at fire time).
        let mut satisfied_trigger_deps: Vec<(ConDescId, TrackPointId)> = Vec::new();
        for trigger in op_linker.iter().skip(1) {
            // nextTrigger->getData() / nextTrigger->isNegated()
            let trigger_concept: ConceptId = trigger.target;
            let trigger_link_negated: bool = trigger.negated;
            let mut trigger_con_des: ConDescId = Id::NONE;
            let mut trigger_dep_track_point: TrackPointId = Id::NONE;
            // if (conSet->getConceptDescriptor(triggerConcept, triggerConDes, triggerDepTrackPoint))
            // KONCLUDE-PORT-NOTE[api]: `getConceptDescriptor(CConcept*)` keys by the
            // concept's tag (`CConcept::getConceptTag`), so resolve the real concept
            // tag against the arena and use the by-tag lookup — exactly as
            // `insert_concepts_to_individual_concept_set` resolves `new_con_tag`.
            let trigger_tag: Cint64 = calc_alg_context
                .ontology_arenas()
                .concept(trigger_concept)
                .get_concept_tag();
            let has_trigger_con_des = calc_alg_context
                .process_context()
                .label_set(con_set)
                .get_concept_descriptor_by_tag(
                    trigger_tag,
                    &mut trigger_con_des,
                    &mut trigger_dep_track_point,
                );
            if has_trigger_con_des {
                // The ls1 lookup cannot resolve the stored descriptor's track
                // point (ctx-less stub → NONE) — resolve it here, the C++
                // `triggerConDes->getDependencyTrackPoint()` (same caller-side
                // fix as the u36 insert-clash path).
                if trigger_dep_track_point.is_none() && trigger_con_des.is_some() {
                    trigger_dep_track_point = calc_alg_context
                        .process_context()
                        .con_desc(trigger_con_des)
                        .get_dependency_track_point();
                }
                // if (triggerConDes->isNegated() == nextTrigger->isNegated()) return;
                let trigger_con_des_negated = calc_alg_context
                    .process_context()
                    .con_desc(trigger_con_des)
                    .is_negated();
                if trigger_con_des_negated == trigger_link_negated {
                    return;
                }
                // else: present with the OPPOSITE polarity ⇒ trigger satisfied; advance.
                if trigger_dep_track_point != dep_track_point && trigger_dep_track_point.is_some() {
                    // createCONNECTIONDependency accumulation (cpp 10425–10429):
                    // WITHOUT this a head fired by a BRANCH-added trigger
                    // inherits only the implication concept's own (base) tag —
                    // clashes over it then trace to branching level 0 and
                    // wrongly cancel the root (measured: ore_ont_12653
                    // spurious=4 under KM_HT_DDB).
                    satisfied_trigger_deps.push((trigger_con_des, trigger_dep_track_point));
                }
            } else {
                // not present ⇒ break to install-to-trigger.
                all_triggers_available = false;
                missing_trigger = Some(*trigger);
                break;
            }
        }

        if !all_triggers_available {
            // install to trigger (cpp 10411-10419):
            //   bool triggerNegation = !nextTrigger->isNegated();
            //   if (!isConceptInReapplyQueue(conDes, triggerConcept, triggerNegation, ...))
            //     addConceptToReapplyQueue(conDes, triggerConcept, triggerNegation, ..., depTrackPoint, ...);
            // The registered descriptor re-queues THIS implication's concept
            // descriptor when the trigger concept lands on the node (fired by
            // `insert_concepts_to_individual_concept_set`'s reapply iterator →
            // `apply_reapply_queue_concepts_condensed_iterator`), so the rule is
            // re-run and either fires or installs on its NEXT missing trigger —
            // the dynamic condensed-reapply chaining.
            // W3-DEFER[macro]: STATINC(IMPLICATIONTRIGGERINGCOUNT, calc_alg_context)
            if let Some(trigger) = missing_trigger {
                let trigger_negation = !trigger.negated;
                if !self.is_concept_in_reapply_queue_concept(
                    con_des,
                    trigger.target,
                    trigger_negation,
                    *process_indi,
                    calc_alg_context,
                ) {
                    self.add_concept_to_reapply_queue_concept(
                        con_des,
                        trigger.target,
                        trigger_negation,
                        *process_indi,
                        false,
                        dep_track_point,
                        calc_alg_context,
                    );
                }
            }
        } else {
            // W3-DEFER[macro]: STATINC(IMPLICATIONEXECUTINGCOUNT, calc_alg_context)
            // The trigger CONNECTION-dependency chain (the accumulated
            // `triggImpProcRes->getImplicationDependency()` in Konclude; built
            // locally here because this port re-scans all triggers per
            // invocation). Each satisfied trigger with a different dependency
            // becomes a CONNECTION node whose continue track point rides an
            // additional-dependency link on the fired implication — so the
            // implication's branching tag is the MAX over the implication
            // concept AND every trigger (`depended_branching_tag` walks
            // `additional_after`), and the u29 closure unwind reaches the
            // trigger concepts.
            let mut trigger_deps: DepLinkId = Id::NONE;
            for &(t_con_des, t_tp) in &satisfied_trigger_deps {
                let conn = self.create_connection_dependency(
                    process_indi,
                    t_con_des,
                    t_tp,
                    calc_alg_context,
                );
                if conn.is_some() {
                    let conn_tp = calc_alg_context
                        .process_context_mut()
                        .materialize_continue_dependency_track_point(conn);
                    let link = calc_alg_context.process_context_mut().alloc_dep_link(
                        super::super::process::dependency::DependencyLink {
                            dep_track_point: conn_tp,
                            next: trigger_deps,
                        },
                    );
                    trigger_deps = link;
                }
            }
            let mut next_dep_track_point: TrackPointId = Id::NONE;
            // createIMPLICATIONDependency(nextDepTrackPoint, processIndi, conDes, depTrackPoint, triggerDeps, ...) [u29]
            self.create_implication_dependency(
                &mut next_dep_track_point,
                process_indi,
                con_des,
                dep_track_point,
                trigger_deps,
                calc_alg_context,
            );
            // CConcept* implConcept = opLinker->getData(); bool impConNeg = opLinker->isNegated();
            let impl_concept: ConceptId = op_linker.first().map(|l| l.target).unwrap_or(Id::NONE);
            let imp_con_neg: bool = op_linker.first().map(|l| l.negated).unwrap_or(false);
            // KM_BRIDGE_WATCH_TAG: when the fired head matches, dump the whole
            // implication (head + trigger linkers with polarities) so the
            // source clause is identifiable.
            if let Ok(w) = std::env::var("KM_BRIDGE_WATCH_TAG") {
                let head_tag = if impl_concept.is_some() {
                    calc_alg_context
                        .ontology_arenas()
                        .concept(impl_concept)
                        .get_concept_tag()
                } else {
                    -1
                };
                if w.parse::<Cint64>() == Ok(head_tag) && !imp_con_neg {
                    let source_tag = calc_alg_context
                        .ontology_arenas()
                        .concept(concept)
                        .get_concept_tag();
                    let branch_tag = |track_point: TrackPointId| {
                        track_point.is_some().then(|| {
                            calc_alg_context
                                .process_context()
                                .track_point(track_point)
                                .get_branching_tag()
                        })
                    };
                    let trigger_dependencies: Vec<String> = satisfied_trigger_deps
                        .iter()
                        .map(|&(descriptor, track_point)| {
                            let trigger = calc_alg_context
                                .process_context()
                                .con_desc(descriptor)
                                .get_concept();
                            format!(
                                "{}:{:?}:{:?}",
                                calc_alg_context
                                    .ontology_arenas()
                                    .concept(trigger)
                                    .get_concept_tag(),
                                track_point,
                                branch_tag(track_point),
                            )
                        })
                        .collect();
                    let ops: Vec<String> = op_linker
                        .iter()
                        .map(|l| {
                            format!(
                                "{}{}",
                                if l.negated { "¬" } else { "" },
                                calc_alg_context
                                    .ontology_arenas()
                                    .concept(l.target)
                                    .get_concept_tag()
                            )
                        })
                        .collect();
                    eprintln!(
                        "WATCH-IMPL fire source={source_tag} source-dependency={:?} source-branch={:?} head={head_tag} result-dependency={:?} result-branch={:?} trigger-dependencies=[{}] node={} ops=[{}]",
                        dep_track_point,
                        branch_tag(dep_track_point),
                        next_dep_track_point,
                        branch_tag(next_dep_track_point),
                        trigger_dependencies.join(" "),
                        calc_alg_context
                            .process_context()
                            .node(*process_indi)
                            .individual_node_id(),
                        ops.join(" ")
                    );
                }
            }
            // addConceptToIndividual(implConcept, impConNeg, processIndi, nextDepTrackPoint, true, false, ...) [u36]
            self.add_concept_to_individual(
                impl_concept,
                imp_con_neg,
                process_indi,
                next_dep_track_point,
                true,
                false,
                calc_alg_context,
            );
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyNOMINALIMPLICATIONRule`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: the `CIndividualMergingHash` /
    /// `CIndividualMergingHashData` / `CCondensedReapplyConceptDescriptor` satellite
    /// machinery is not ported → its reads/writes are deferred. The node + concept
    /// nominal-individual reads resolve live against the arena.
    pub fn apply_nominal_implication_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[macro]: STATINC(IMPLICATIONRULEAPPLICATIONCOUNT, calc_alg_context)

        // --- arena-resolved read heads (cpp 17132–17136) ---
        let con_des: ConDescId = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .get_concept_descriptor();
        let concept: ConceptId = calc_alg_context
            .process_context()
            .con_desc(con_des)
            .get_concept();
        let dep_track_point: TrackPointId = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .get_dependency_track_point();
        // W3-DEFER[memory-pool]: calcAlgContext->getUsedProcessTaskMemoryAllocationManager()
        let task_mem_man: Cint64 = INVALID;
        let op_linker: Vec<NegLink<ConceptId>> = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operand_list()
            .to_vec();

        if !op_linker.is_empty() {
            let mut triggers_available = false;
            let mut add_nom_trigger_dep_track_point: TrackPointId = Id::NONE;
            let indi: IndividualId = calc_alg_context
                .ontology_arenas()
                .concept(concept)
                .get_nominal_individual();
            if indi != Id::NONE {
                let process_nominal_indi: IndividualId = calc_alg_context
                    .process_context()
                    .node(*process_indi)
                    .nominal_individual();
                if process_nominal_indi != Id::NONE {
                    let process_nominal_indi_id: Cint64 = calc_alg_context
                        .ontology_arenas()
                        .individual(process_nominal_indi)
                        .get_individual_id();
                    let indi_id: Cint64 = calc_alg_context
                        .ontology_arenas()
                        .individual(indi)
                        .get_individual_id();
                    if process_nominal_indi_id == indi_id {
                        triggers_available = true;
                    } else {
                        // W3-DEFER[api]: processIndi->getIndividualMergingHash(false)
                        let merging_hash: Cint64 = INVALID;
                        if merging_hash != INVALID {
                            // W3-DEFER[api]: mergingHash->value(indi->getIndividualID())
                            // W3-DEFER[api]: mergedData.isMergedWithIndividual()
                            let is_merged_with_individual = false;
                            if is_merged_with_individual {
                                triggers_available = true;
                                // W3-DEFER[api]: mergedData.getDependencyTrackPoint()
                                let trigger_dep_track_point: TrackPointId = Id::NONE;
                                let process_dep_track_point: TrackPointId = calc_alg_context
                                    .process_context()
                                    .node(*process_indi)
                                    .dependency_track_point();
                                if trigger_dep_track_point != process_dep_track_point {
                                    add_nom_trigger_dep_track_point = trigger_dep_track_point;
                                }
                            }
                        }
                    }
                }
            }

            if !triggers_available {
                // W3-DEFER[api]: processIndi->getIndividualMergingHash(true)
                // W3-DEFER[api]: CIndividualMergingHashData& mergingHashData = (*mergingHash)[indi->getIndividualID()]
                // W3-DEFER[memory-pool]: allocate+construct CCondensedReapplyConceptDescriptor
                // W3-DEFER[api]: reapplyConDes->initReapllyDescriptor(conDes, depTrackPoint)
                // W3-DEFER[api]: mergingHashData.getReapplyQueue()->addReapplyConceptDescriptor(reapplyConDes)
            } else {
                // W3-DEFER[macro]: STATINC(IMPLICATIONEXECUTINGCOUNT, calc_alg_context)
                // W3-DEFER[api]: createCONNECTIONDependency(processIndi, nullptr, addNomTriggerDepTrackPoint, calcAlgContext)
                let conn_dep: Cint64 = INVALID;
                let mut next_dep_track_point: TrackPointId = Id::NONE;
                // W3-DEFER[api]: createIMPLICATIONDependency(nextDepTrackPoint, processIndi, conDes, depTrackPoint, connDep, calcAlgContext)
                next_dep_track_point = Id::NONE;
                // W3-DEFER[api]: addConceptsToIndividual(opLinker, false, processIndi, nextDepTrackPoint, true, false, nullptr, calcAlgContext)
            }
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applySELFRule`.
    pub fn apply_self_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[macro]: STATINC(SELFRULEAPPLICATIONCOUNT, calc_alg_context)

        // --- arena-resolved read heads (cpp 17245–17250) ---
        let con_des: ConDescId = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .get_concept_descriptor();
        let concept: ConceptId = calc_alg_context
            .process_context()
            .con_desc(con_des)
            .get_concept();
        let role: RoleId = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_role();
        let dep_track_point: TrackPointId = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .get_dependency_track_point();
        let reapplied: bool = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .is_concept_reapplied();
        let rest_link: EdgeId =
            self.get_link_processing_restriction(*con_pro_des, calc_alg_context);
        if !negate {
            let mut self_destination = *process_indi;
            let link: EdgeId = self.get_individual_node_link(
                process_indi,
                &mut self_destination,
                role,
                calc_alg_context,
            );
            if link == Id::NONE {
                // self edge/link does not exist
                // create dependency
                let mut next_dep_track_point: TrackPointId = Id::NONE;
                self.create_self_dependency(
                    &mut next_dep_track_point,
                    process_indi,
                    con_des,
                    dep_track_point,
                    calc_alg_context,
                );
                let indirect_super_role_list: Vec<NegLink<RoleId>> = calc_alg_context
                    .ontology_arenas()
                    .role(role)
                    .get_indirect_super_role_list()
                    .to_vec();
                self.create_new_individuals_links_reapplyed(
                    *process_indi,
                    *process_indi,
                    &indirect_super_role_list,
                    role,
                    next_dep_track_point,
                    true,
                    calc_alg_context,
                );
            }
        } else {
            if rest_link != Id::NONE {
                let self_restricted_link = {
                    let edge = calc_alg_context.process_context().edge(rest_link);
                    edge.get_destination_individual() == *process_indi
                        && edge.get_source_individual() == *process_indi
                };
                if self_restricted_link {
                    // throw clash
                    let rest_dep_track_point = calc_alg_context
                        .process_context()
                        .edge(rest_link)
                        .get_dependency_track_point();
                    let mut clash_des: ClashDescId = Id::NONE;
                    clash_des = self.create_clashed_individual_link_descriptor(
                        clash_des,
                        rest_link,
                        rest_dep_track_point,
                        calc_alg_context,
                    );
                    clash_des = self.create_clashed_concept_descriptor(
                        clash_des,
                        process_indi,
                        con_des,
                        dep_track_point,
                        calc_alg_context,
                    );
                    calc_alg_context.raise_clash(clash_des);
                    return;
                }
            } else {
                let mut self_destination = *process_indi;
                let link: EdgeId = self.get_individual_node_link(
                    process_indi,
                    &mut self_destination,
                    role,
                    calc_alg_context,
                );
                if link != Id::NONE {
                    // throw clash
                    let link_dep_track_point = calc_alg_context
                        .process_context()
                        .edge(link)
                        .get_dependency_track_point();
                    let mut clash_des: ClashDescId = Id::NONE;
                    clash_des = self.create_clashed_individual_link_descriptor(
                        clash_des,
                        link,
                        link_dep_track_point,
                        calc_alg_context,
                    );
                    clash_des = self.create_clashed_concept_descriptor(
                        clash_des,
                        process_indi,
                        con_des,
                        dep_track_point,
                        calc_alg_context,
                    );
                    calc_alg_context.raise_clash(clash_des);
                    return;
                }
            }
            if !reapplied {
                self.add_concept_to_reapply_queue_role(
                    con_des,
                    role,
                    *process_indi,
                    true,
                    dep_track_point,
                    calc_alg_context,
                );
            }
        }
    }
}
