//! `completion::u05` — Expansion-rule family, batch 1 (port unit #5 of 36).
//!
//! Faithful port of the first 15 expansion-rule methods of Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`
//! (manifest `01-completion-methods.md`, "Unit 5", cpp ranges 9552–11157):
//!
//!   * the 7 `applyNeg*Rule` polarity-flip delegations,
//!   * `applyAutomatChooseRule` / `applyAutomatANDRule` / `applyAutomatTransactions`
//!     (the qualified-`∀` automaton transition machinery),
//!   * the 5 `applyREPRESENTATIVE*Rule` rules (the representative variable-binding
//!     propagation calculus: GROUNDING / JOIN / BINDVARIABLE / IMPLICATION / ALL).
//!
//! KONCLUDE-PORT-NOTE[ownership]: a rule method is a member of
//! `CCalculationTableauCompletionTaskHandleAlgorithm`, so it becomes `&mut self`
//! plus the threaded per-thread context `calc_alg_context: &mut
//! CalculationAlgorithmContextBase` (the C++ `CCalculationAlgorithmContextBase*`).
//! The C++ `CIndividualProcessNode*&` / `CConceptProcessDescriptor*&` out/in-out
//! pointer-references become `&mut NodeId` / `&mut ConProcDescId` (arena ids).
//!
//! KONCLUDE-PORT-NOTE[api]: this is the FIRST completion method-body unit; no
//! predecessor has yet established how a rule body reaches the per-test ARENAS
//! (the concept / descriptor / node / dependency arenas live under the
//! context-owned `ProcessingDataBox`, but no accessor convention is wired). Every
//! operation in these rules therefore bottoms out in one of two not-yet-available
//! facilities, both flagged inline:
//!   1. an ARENA DEREFERENCE of a `*Id` (e.g. `conDes->getConcept()`), and
//!   2. a NOT-YET-PORTED SUBSYSTEM entry point — the dependency factory
//!      (`create*Dependency`), the queue/label/reapply helpers
//!      (`addConceptToIndividual`, `addConceptToReapplyQueue`,
//!      `addIndividualToProcessingQueue`, `getSuccessorIndividual`,
//!      `getLocalizedIndividual`, `getLinkProcessingRestriction`), the sibling
//!      `apply*Rule` methods (units u06–u09), and the ENTIRE representative
//!      variable-binding-path propagation subsystem
//!      (`CRepresentativePropagationSet`, `CRepresentativeVariableBindingPathSetData`,
//!      `CRepresentativeJoiningHash`, `CConceptNominalSchemaGroundingHandler`, …),
//!      none of which exist in the port yet.
//!
//! Following the porting convention: the 7 polarity-flip delegations are ported in
//! full (their entire logic is the forwarding call). `applyAutomatANDRule` is
//! ported as its forwarding skeleton with the two unavailable arena reads flagged
//! `// W3-DEFER[api]`. The remaining 7 rules are bodies whose control flow is
//! driven start-to-finish by unported-subsystem return values and typed locals of
//! not-yet-ported classes (representative descriptors, joining maps, variable
//! binding paths); they are kept as `// PORT-PENDING` with the faithful signature
//! and a structural transcription of the C++ so a later wave can fill them without
//! re-reading the source. Logic is documented, never silently dropped.

#![allow(dead_code)]
#![allow(unused_variables)]

use super::super::model::substrate::{Cint64, Id, NegLink, INVALID};
use super::super::model::{ConceptId, RoleId, VariableId};
use super::super::process::binding_hash::ConceptPropagationBindingSetHash;
use super::super::process::dependency::DependencyLink;
use super::super::process::propagation_binding::{
    PropagationBindingSet, PropagationVariableBindingTransitionExtension,
};
use super::super::process::representative::{
    ConceptRepresentativePropagationSetHash, RepresentativeJoiningAllDataExtension,
    RepresentativeJoiningHash, RepresentativePropagationDescriptor,
    RepresentativePropagationMapData, RepresentativePropagationSet,
    RepresentativeVariableBindingPathSetData, RepresentativeVariableBindingPathSetHash,
};
use super::super::process::varbind::{
    RepresentativeVariableBindingPathMapData, VariableBinding, VariableBindingDescriptor,
    VariableBindingPath,
};
use super::super::process::{
    ConDescId, ConProcDescId, DepLinkId, EdgeId, LabelSetId, NodeId, TrackPointId,
};
use super::context::CalculationAlgorithmContextBase;
use super::grounding::ConceptNominalSchemaGroundingHandler;

impl super::algorithm::CompletionTaskHandleAlgorithm {
    // =======================================================================
    // Negated-operator rules — polarity-flip delegations (cpp 9552–9579).
    //
    // Each forwards to the corresponding positive rule with the polarity
    // inverted (NOTE the ATMOST/ATLEAST pair forward to each OTHER, and pass
    // `negate` UNCHANGED — not `!negate` — exactly as the C++). The target
    // `apply*Rule` methods land in units u06–u09; the forwarding call IS the
    // whole logic of these rules and is ported verbatim.
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyNegAutomatChooseRule`.
    pub fn apply_neg_automat_choose_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        self.apply_automat_choose_rule(process_indi, con_pro_des, !negate, calc_alg_context);
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyNegANDRule`.
    pub fn apply_neg_and_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[api]: applyANDRule(...) — sibling rule, lands in unit u08.
        self.apply_and_rule(process_indi, con_pro_des, !negate, calc_alg_context);
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyNegSOMERule`.
    pub fn apply_neg_some_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[api]: applySOMERule(...) — sibling rule, lands in unit u08.
        self.apply_some_rule(process_indi, con_pro_des, !negate, calc_alg_context);
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyNegALLRule`.
    pub fn apply_neg_all_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[api]: applyALLRule(...) — sibling rule, lands in unit u09.
        self.apply_all_rule(process_indi, con_pro_des, !negate, calc_alg_context);
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyNegORRule`.
    pub fn apply_neg_or_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[api]: applyORRule(...) — sibling rule, lands in unit u09.
        self.apply_or_rule(process_indi, con_pro_des, !negate, calc_alg_context);
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyNegATMOSTRule`.
    ///
    /// NOTE: forwards to `applyATLEASTRule` and passes `negate` UNCHANGED.
    pub fn apply_neg_atmost_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[api]: applyATLEASTRule(...) — sibling rule, lands in unit u09.
        self.apply_atleast_rule(process_indi, con_pro_des, negate, calc_alg_context);
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyNegATLEASTRule`.
    ///
    /// NOTE: forwards to `applyATMOSTRule` and passes `negate` UNCHANGED.
    pub fn apply_neg_atleast_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[api]: applyATMOSTRule(...) — sibling rule, lands in unit u09.
        self.apply_atmost_rule(process_indi, con_pro_des, negate, calc_alg_context);
    }

    // =======================================================================
    // Automaton (qualified-∀) rules (cpp 9583–9752).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyAutomatChooseRule`.
    ///
    /// Faithful body (cpp 9583–9606): create the `AUTOMATCHOOSE` dependency, then
    /// for every operand whose negation matches `negate` add the operand concept
    /// (un-negated) to the individual.
    pub fn apply_automat_choose_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[macro]: STATINC(AUTOMATEINITCOUNT, calc_alg_context)
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

        // andDepNode = createAUTOMATCHOOSEDependency(nextDepTrackPoint, processIndi, conDes, depTrackPoint, ...)
        let mut next_dep_track_point: TrackPointId = Id::NONE;
        let _and_dep_node = self.create_automat_choose_dependency(
            &mut next_dep_track_point,
            process_indi,
            con_des,
            dep_track_point,
            calc_alg_context,
        );

        // KONCLUDE-PORT-NOTE[ownership]: the operand `CSortedNegLinker*` lives in the
        // (ctx-owned) concept arena, so it is collected to an owned `Vec` before the
        // `&mut self`/`&mut ctx` `add_concept_to_individual` calls (same idiom as
        // `apply_and_rule` in u08); contents and order are identical.
        let concept_op_linker_it: Vec<NegLink<ConceptId>> = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operand_list()
            .to_vec();
        for op_link in &concept_op_linker_it {
            let op_concept: ConceptId = op_link.target; // conceptOpLinkerIt->getData()
            let op_negation: bool = op_link.negated; // conceptOpLinkerIt->isNegated()
            if op_negation == negate {
                self.add_concept_to_individual(
                    op_concept,
                    false,
                    process_indi,
                    next_dep_track_point,
                    true,
                    false,
                    calc_alg_context,
                );
            }
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyAutomatANDRule`.
    ///
    /// Forwarding skeleton: extracts the concept from the process descriptor and
    /// delegates to `applyAutomatTransactions`. The two arena reads are flagged.
    pub fn apply_automat_and_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // conDes = conProDes->getConceptDescriptor(); concept = conDes->getConcept().
        let con_des: ConDescId = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .get_concept_descriptor();
        let concept: ConceptId = calc_alg_context
            .process_context()
            .con_desc(con_des)
            .get_concept();
        // conceptNegation = negate; depTrackPoint = conProDes->getDependencyTrackPoint();
        // (both computed in the C++ but unused before the delegation.)
        self.apply_automat_transactions(
            process_indi,
            con_pro_des,
            concept,
            negate,
            calc_alg_context,
        );
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyAutomatTransactions`
    /// — the qualified-`∀` automaton transition driver (cpp 9634–9752), LIVE since the
    /// role-chain-automata preprocessor landed as its producer. C++ structure for
    /// reference:
    /// ```text
    /// STATINC(AUTOMATERULEAPPLICATIONCOUNT)
    /// baseConDes = conProDes->getConceptDescriptor(); reapplied = conProDes->isConceptReapplied()
    /// restLink = getLinkProcessingRestriction(conProDes); depTrackPoint = conProDes->getDependencyTrackPoint()
    /// opCode = concept->getOperatorCode(); opConcepts = concept->getOperandList()
    /// if opCode in {CCAQAND, CCIMPLAQAND, CCBRANCHAQAND}:
    ///   for opCon in opConcepts: ++mAppliedALLRuleCount; STATINC(AUTOMATESTATECOUNT)
    ///     applyAutomatTransactions(processIndi, conProDes, opCon, opCon.isNegated(), ...)   // recurse
    /// else if opCode in {CCAQALL, CCIMPLAQALL, CCBRANCHAQALL}:
    ///   role = concept->getRole()
    ///   if restLink:
    ///     if restLink->getLinkRole() == role:
    ///       ++mAppliedALLRuleCount; STATINC(AUTOMATETRANSACTIONCOUNT)
    ///       succIndi = getSuccessorIndividual(processIndi, restLink)
    ///       if !isRestrictedTopObjectPropertyPropagation(processIndi, succIndi, concept, negated):
    ///         conLabelSet = succIndi->getReapplyConceptLabelSet(false); locSuccIndi = null
    ///         for opConcept in opConcepts (opConNeg = opConcept.isNegated() ^ negated):
    ///           if !conLabelSet->containsConcept(opConcept, opConNeg):
    ///             if !allDepNodeCreated: allDepNode = createAUTOMATTRANSACTIONDependency(nextDepTrackPoint, processIndi, baseConDes, depTrackPoint, restLink->getDependencyTrackPoint(), ...)
    ///             if !locSuccIndi: locSuccIndi = getLocalizedIndividual(succIndi, false); conLabelSet = locSuccIndi->getReapplyConceptLabelSet(true)
    ///             addConceptToIndividual(opConcept, opConNeg, locSuccIndi, nextDepTrackPoint, true, true, ...)
    ///         if locSuccIndi: addIndividualToProcessingQueue(locSuccIndi, ...)
    ///   else:
    ///     roleSuccHash = processIndi->getReapplyRoleSuccessorHash(false)
    ///     if roleSuccHash:
    ///       for link in roleSuccHash->getRoleSuccessorLinkIterator(role):   // hasNext / next(true)
    ///         ++mAppliedALLRuleCount; STATINC(AUTOMATETRANSACTIONCOUNT)
    ///         succIndi = getSuccessorIndividual(processIndi, link)
    ///         if !isRestrictedTopObjectPropertyPropagation(...): <same inner block as above, with link->getDependencyTrackPoint()>
    ///   if !reapplied: addConceptToReapplyQueue(baseConDes, role, processIndi, true, depTrackPoint, ...)
    /// else if !reapplied:
    ///   addConceptToIndividual(concept, negated, processIndi, depTrackPoint, true, true, ...)
    /// ```
    pub fn apply_automat_transactions(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        concept: ConceptId,
        negated: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        use super::super::model::op;
        // W3-DEFER[macro]: STATINC(AUTOMATERULEAPPLICATIONCOUNT, calcAlgContext)

        let base_con_des: ConDescId = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .get_concept_descriptor();
        let reapplied: bool = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .is_concept_reapplied();
        // KONCLUDE-PORT-NOTE[api]: getLinkProcessingRestriction(conProDes) is W2-DEFER
        // (the CLinkProcessingRestrictionSpecification subtype is unported), so
        // restLink == NONE and the all-successors arm always runs; the per-link
        // restLink arm (the reapply queue re-firing a state over ONE new edge,
        // cpp 9662–9700) is realised instead by the ∃-rule's
        // `ht_reapply_universal_restrictions` (u08), which re-walks the
        // predecessor's automaton states when a new edge is installed.
        let dep_track_point: TrackPointId = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .get_dependency_track_point();

        let op_code: Cint64 = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operator_code();
        let op_concepts: Vec<NegLink<ConceptId>> = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operand_list()
            .to_vec();

        if op_code == op::CCAQAND || op_code == op::CCIMPLAQAND || op_code == op::CCBRANCHAQAND {
            for op_link in &op_concepts {
                self.applied_all_rule_count += 1;
                // W3-DEFER[macro]: STATINC(AUTOMATESTATECOUNT, calcAlgContext)
                self.apply_automat_transactions(
                    process_indi,
                    con_pro_des,
                    op_link.target,
                    op_link.negated,
                    calc_alg_context,
                );
                if calc_alg_context.has_pending_signal() {
                    return;
                }
            }
        } else if op_code == op::CCAQALL
            || op_code == op::CCIMPLAQALL
            || op_code == op::CCBRANCHAQALL
        {
            let role: RoleId = calc_alg_context
                .ontology_arenas()
                .concept(concept)
                .get_role();
            // KONCLUDE-PORT-NOTE[api]: the C++ iterates
            // `processIndi->getReapplyRoleSuccessorHash(false)
            //     ->getRoleSuccessorLinkIterator(role)` — edges registered under
            // every indirect super role on install. The port resolves the role
            // hierarchy + the inverse direction at lookup via `ht_all_rule_targets`
            // (u10), exactly as `apply_all_rule` (u09) does.
            let role_targets = self.ht_all_rule_targets(*process_indi, role, calc_alg_context);
            for succ_indi in role_targets {
                self.applied_all_rule_count += 1;
                // W3-DEFER[macro]: STATINC(AUTOMATETRANSACTIONCOUNT, calcAlgContext)
                // W3-DEFER[api]: isRestrictedTopObjectPropertyPropagation — false (no
                // answerer binding-propagation adapter in this fragment).
                let mut next_dep_track_point: TrackPointId = Id::NONE;
                let mut all_dep_node_created = false;
                let mut loc_succ_indi: NodeId =
                    self.get_localized_individual(succ_indi, false, calc_alg_context);
                for op_link in &op_concepts {
                    let op_concept: ConceptId = op_link.target;
                    let op_con_neg: bool = op_link.negated ^ negated;
                    // conLabelSet->containsConcept(opConcept, opConNeg) — tag-RESOLVED
                    // (ls1::has_concept is a W2-DEFER stub: raw-index key + always-false
                    // negation; a raw/tag collision here would SKIP a required add).
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
                            // KONCLUDE-PORT-NOTE[api]: the link's own dependency track
                            // point (`link->getDependencyTrackPoint()`) is not threaded
                            // through `ht_all_rule_targets`; the descriptor's track
                            // point stands in (the same deferral `apply_all_rule`
                            // documents for createALLDependency).
                            let _all_dep_node = self.create_automat_transaction_dependency(
                                &mut next_dep_track_point,
                                process_indi,
                                base_con_des,
                                dep_track_point,
                                dep_track_point,
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
                self.add_individual_to_processing_queue(loc_succ_indi, calc_alg_context);
            }
            if !reapplied {
                // addConceptToReapplyQueue(baseConDes, role, processIndi, true, depTrackPoint, ...)
                self.add_concept_to_reapply_queue_role(
                    base_con_des,
                    role,
                    *process_indi,
                    true,
                    dep_track_point,
                    calc_alg_context,
                );
            }
        } else if !reapplied {
            self.add_concept_to_individual(
                concept,
                negated,
                process_indi,
                dep_track_point,
                true,
                true,
                calc_alg_context,
            );
        }
    }

    // =======================================================================
    // Representative variable-binding-path propagation rules (cpp 10310–11157).
    //
    // PORT-PENDING (all five): these rules ARE the representative-propagation
    // calculus. Their bodies are driven entirely by classes that have no port
    // yet — `CRepresentativePropagationSet`,
    // `CConceptRepresentativePropagationSetHash`, `CConceptPropagationBindingSetHash`,
    // `CRepresentativeVariableBindingPathSetData`/`…Map`/`…Hash`,
    // `CRepresentativeJoiningHash`/`…Data`/`…KeyMap`, `CVariableBinding(Path)`,
    // `CPropagationRepresentativeTransitionExtension`,
    // `CConceptNominalSchemaGroundingHandler` (`mGroundingHandler`) — plus the
    // dependency factory's REPRESENTATIVE* dependency-node creators and the
    // reapply-queue / concept-add helpers. The signatures are preserved and the
    // C++ control flow is summarised per method so a later wave can fill them in.
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyREPRESENTATIVEGROUNDINGRule`.
    ///
    /// C++ (cpp 10310–10364): fetch `repPropSet` for `concept` from the node's
    /// `ConceptRepresentativePropagationSetHash`; if it has an outgoing descriptor
    /// with migrate-data → `mGroundingHandler->getGroundingConceptLinker(...)`; for
    /// each grounded concept create a `REPRESENTATIVEGROUNDING` dependency (with the
    /// selected variable-binding path) and `addConceptToIndividual(...)`.
    pub fn apply_representative_grounding_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let con_pro_des_id = *con_pro_des;
        let con_des: ConDescId = calc_alg_context
            .process_context()
            .con_proc_desc(con_pro_des_id)
            .get_concept_descriptor();
        let _dep_track_point: TrackPointId = calc_alg_context
            .process_context()
            .con_proc_desc(con_pro_des_id)
            .get_dependency_track_point();
        let concept: ConceptId = calc_alg_context
            .process_context()
            .con_desc(con_des)
            .get_concept();
        let negated = calc_alg_context
            .process_context()
            .con_desc(con_des)
            .is_negated();
        let _op_count: Cint64 = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operand_count();
        let _con_set = calc_alg_context
            .process_context_mut()
            .node_reapply_concept_label_set(*process_indi);

        let rep_prop_set_hash = calc_alg_context
            .process_context()
            .node(*process_indi)
            .use_concept_rep_prop_set_hash;
        let rep_prop_set = if rep_prop_set_hash.is_some() {
            ConceptRepresentativePropagationSetHash::get_representative_propagation_set(
                calc_alg_context.process_context_mut(),
                rep_prop_set_hash,
                concept,
                false,
            )
        } else {
            Id::NONE
        };

        // W3-DEFER[macro]: STATINC(VARBINDRULEGROUNDINGAPPLICATIONCOUNT, calc_alg_context)

        if rep_prop_set.is_some() {
            let out_rep_prop_des = calc_alg_context
                .process_context()
                .rep_prop_set(rep_prop_set)
                .get_outgoing_representative_propagation_descriptor_linker();
            if out_rep_prop_des.is_some() {
                let rep_var_bind_path_set_data = calc_alg_context
                    .process_context()
                    .rep_prop_des(out_rep_prop_des)
                    .get_representative_variable_binding_path_set_data();
                if rep_var_bind_path_set_data.is_some() {
                    let rep_var_bind_path_set_mig_data = calc_alg_context
                        .process_context()
                        .rep_var_bind_path_set_data(rep_var_bind_path_set_data)
                        .use_migrate_data;
                    if rep_var_bind_path_set_mig_data.is_some() {
                        // W3-DEFER[macro]: KONCLUCE_TASK_ALGORITHM_MODEL_STRING_INSTRUCTION(mBeforeGroundingDebugIndiModelString = generateExtendedDebugIndiModelStringList(...))

                        let rep_var_bind_path_set_map = calc_alg_context
                            .process_context()
                            .rep_var_bind_path_set_migrate_data(rep_var_bind_path_set_mig_data)
                            .get_representative_variable_binding_path_map()
                            .clone();
                        let grounding_hash =
                            calc_alg_context.processing_data_box().use_grounding_hash;
                        let mut grounding_handler = ConceptNominalSchemaGroundingHandler::new();
                        let grounding_result = grounding_handler
                            .get_grounding_concept_linker_for_representative_varbind_path_map(
                                *process_indi,
                                &rep_var_bind_path_set_map,
                                concept,
                                negated,
                                grounding_hash,
                                &mut calc_alg_context.base,
                            );
                        let new_grounded_linker = grounding_result.new_linker;

                        if !new_grounded_linker.is_empty() {
                            for new_grounded_linker_it in new_grounded_linker.iter() {
                                // W3-DEFER[macro]: STATINC(VARBINDGROUNDINGCOUNT, calc_alg_context)
                                self.stat_var_binding_grounding_count += 1;
                                self.stat_representative_grounding_count += 1;
                                let new_grounded_concept: ConceptId = new_grounded_linker_it.target;
                                let new_grounded_concept_negation: bool =
                                    new_grounded_linker_it.negated;

                                let selected_var_bind_path = grounding_result
                                    .grounded_con_var_bind_path_hash
                                    .get(&new_grounded_concept)
                                    .copied()
                                    .unwrap_or(Id::NONE);
                                let prev_dep_track_point = calc_alg_context
                                    .process_context()
                                    .rep_prop_des(out_rep_prop_des)
                                    .get_dependency_track_point();
                                let mut next_dep_track_point: TrackPointId = Id::NONE;
                                let _grounding_dep = self
                                    .create_representative_grounding_dependency(
                                        &mut next_dep_track_point,
                                        process_indi,
                                        con_des,
                                        prev_dep_track_point,
                                        selected_var_bind_path,
                                        calc_alg_context,
                                    );
                                if next_dep_track_point.is_none() {
                                    next_dep_track_point = prev_dep_track_point;
                                }

                                self.add_concept_to_individual(
                                    new_grounded_concept,
                                    new_grounded_concept_negation,
                                    process_indi,
                                    next_dep_track_point,
                                    true,
                                    false,
                                    calc_alg_context,
                                );
                            }
                        }

                        // W3-DEFER[macro]: KONCLUCE_TASK_ALGORITHM_MODEL_STRING_INSTRUCTION(mAfterGroundingDebugIndiModelString = generateExtendedDebugIndiModelStringList(...))
                    }
                }
            }
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyREPRESENTATIVEJOINRule`.
    ///
    /// C++ (cpp 10366–10614): the largest of the five. Checks the label set for the
    /// join concept; installs missing triggers into the reapply queue or, when all
    /// triggers are present, examines the propagation-binding transition extension,
    /// tests `areRepresentativesJoinable`, builds the common joining key map
    /// (`createCommonJoiningKeyMap` / `createCommonJoiningAll`), threads the
    /// RESOLVE/REPRESENTATIVEAND/REPRESENTATIVEJOIN dependency chain, registers the
    /// joined representative propagation, and (on `propagationsDone &&
    /// !createJoinConcept`) calls `reapplyConceptUpdatedRepresentative`.
    pub fn apply_representative_join_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let _ = negate;
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
        let op_linker = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operand_list()
            .to_vec();
        if op_linker.len() < 3 {
            return;
        }
        let join_concept = op_linker[0].target;
        let join_concept_negation = op_linker[0].negated;
        let trigger_linker = &op_linker[1..];
        let var_linker = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_variable_linker()
            .to_vec();

        // W3-DEFER[stat]: STATINC(VARBINDRULEJOINAPPLICATIONCOUNT,calcAlgContext).
        let mut join_con_des: ConDescId = Id::NONE;
        let mut join_dep_track_point: TrackPointId = Id::NONE;
        let mut reapply_queue_empty = true;
        let mut propagate_joins = false;
        let mut create_join_concept = false;

        let mut con_set = calc_alg_context
            .process_context()
            .node(*process_indi)
            .use_reapply_con_label_set;
        let join_concept_tag = join_concept.raw;
        let join_present = con_set.is_some()
            && calc_alg_context
                .process_context()
                .label_set(con_set)
                .get_concept_descriptor_and_reapply_queue_state_by_tag(
                    join_concept_tag,
                    &mut join_con_des,
                    &mut join_dep_track_point,
                    &mut reapply_queue_empty,
                );

        if !join_present {
            let created_con_set = calc_alg_context
                .process_context_mut()
                .node_reapply_concept_label_set(*process_indi);
            con_set = created_con_set;
            let mut all_triggers_available = true;
            let mut next_missing_trigger = None;
            for next_trigger in trigger_linker.iter().copied() {
                let mut trigger_con_des: ConDescId = Id::NONE;
                let mut trigger_dep_track_point: TrackPointId = Id::NONE;
                if calc_alg_context
                    .process_context()
                    .label_set(con_set)
                    .get_concept_descriptor(
                        next_trigger.target,
                        &mut trigger_con_des,
                        &mut trigger_dep_track_point,
                    )
                {
                    if calc_alg_context
                        .process_context()
                        .con_desc(trigger_con_des)
                        .is_negated()
                        == next_trigger.negated
                    {
                        return;
                    }
                } else {
                    all_triggers_available = false;
                    next_missing_trigger = Some(next_trigger);
                    break;
                }
            }

            if !all_triggers_available {
                let next_trigger = next_missing_trigger.expect("missing trigger recorded");
                let trigger_negation = !next_trigger.negated;
                if !self.is_concept_in_reapply_queue_concept(
                    con_des,
                    next_trigger.target,
                    trigger_negation,
                    *process_indi,
                    calc_alg_context,
                ) {
                    self.add_concept_to_reapply_queue_concept(
                        con_des,
                        next_trigger.target,
                        trigger_negation,
                        *process_indi,
                        false,
                        dep_track_point,
                        calc_alg_context,
                    );
                }
            } else {
                propagate_joins = true;
                create_join_concept = true;
            }
        } else {
            propagate_joins = true;
        }

        let mut propagations_done = false;
        if propagate_joins {
            for next_trigger in trigger_linker.iter().copied() {
                if !self.is_concept_in_reapply_queue_concept(
                    con_des,
                    next_trigger.target,
                    false,
                    *process_indi,
                    calc_alg_context,
                ) {
                    self.add_concept_to_reapply_queue_concept(
                        con_des,
                        next_trigger.target,
                        false,
                        *process_indi,
                        false,
                        dep_track_point,
                        calc_alg_context,
                    );
                }
            }

            let con_prop_binding_set_hash = calc_alg_context
                .process_context()
                .node(*process_indi)
                .use_concept_prop_binding_set_hash;
            let rep_prop_set_hash = calc_alg_context
                .process_context()
                .node(*process_indi)
                .use_concept_rep_prop_set_hash;
            if con_prop_binding_set_hash.is_some() && rep_prop_set_hash.is_some() {
                let prop_binding_set =
                    ConceptPropagationBindingSetHash::get_propagation_binding_set(
                        calc_alg_context.process_context_mut(),
                        con_prop_binding_set_hash,
                        concept.raw,
                        false,
                    );
                if prop_binding_set.is_some() {
                    let prop_rep_trans_ext = calc_alg_context
                        .process_context()
                        .prop_binding_set(prop_binding_set)
                        .prop_rep_trans_extension;
                    let left_concept = trigger_linker[0].target;
                    let right_concept = trigger_linker[1].target;
                    let left_rep_prop_set =
                        ConceptRepresentativePropagationSetHash::get_representative_propagation_set(
                            calc_alg_context.process_context_mut(),
                            rep_prop_set_hash,
                            left_concept,
                            false,
                        );
                    let right_rep_prop_set =
                        ConceptRepresentativePropagationSetHash::get_representative_propagation_set(
                            calc_alg_context.process_context_mut(),
                            rep_prop_set_hash,
                            right_concept,
                            false,
                        );

                    let left_rep_prop_des = if left_rep_prop_set.is_some() {
                        calc_alg_context
                            .process_context()
                            .rep_prop_set(left_rep_prop_set)
                            .get_outgoing_representative_propagation_descriptor_linker()
                    } else {
                        Id::NONE
                    };
                    let right_rep_prop_des = if right_rep_prop_set.is_some() {
                        calc_alg_context
                            .process_context()
                            .rep_prop_set(right_rep_prop_set)
                            .get_outgoing_representative_propagation_descriptor_linker()
                    } else {
                        Id::NONE
                    };

                    let mut examine_trans_ext = false;
                    if left_rep_prop_set.is_some()
                        && right_rep_prop_set.is_some()
                        && left_rep_prop_des.is_some()
                        && right_rep_prop_des.is_some()
                    {
                        if prop_rep_trans_ext.is_none() {
                            examine_trans_ext = true;
                        } else {
                            let ext = calc_alg_context
                                .process_context()
                                .prop_rep_trans_ext(prop_rep_trans_ext);
                            let prop_set = calc_alg_context
                                .process_context()
                                .prop_binding_set(prop_binding_set);
                            if ext.get_last_analysed_propagate_all_flag()
                                != prop_set.get_propagate_all_flag()
                                || ext.get_last_analysed_propagation_binding_descriptor()
                                    != prop_set.get_propagation_binding_descriptor_linker()
                                || ext.get_left_last_representative_joining_descriptor()
                                    != left_rep_prop_des
                                || ext.get_right_last_representative_joining_descriptor()
                                    != right_rep_prop_des
                            {
                                examine_trans_ext = true;
                            }
                        }
                    }

                    if examine_trans_ext {
                        self.stat_representative_join_count += 1;

                        let con_prop_binding_set_hash = calc_alg_context
                            .process_context_mut()
                            .node_concept_propagation_binding_set_hash(*process_indi);
                        let rep_prop_set_hash = calc_alg_context
                            .process_context_mut()
                            .node_concept_representative_propagation_set_hash(*process_indi);
                        let prop_binding_set =
                            ConceptPropagationBindingSetHash::get_propagation_binding_set(
                                calc_alg_context.process_context_mut(),
                                con_prop_binding_set_hash,
                                concept.raw,
                                true,
                            );
                        let prop_rep_trans_ext =
                            PropagationBindingSet::get_propagation_representative_transition_extension(
                                calc_alg_context.process_context_mut(),
                                prop_binding_set,
                                true,
                            );
                        let mut prop_rep_trans_ext_work = calc_alg_context
                            .process_context()
                            .prop_rep_trans_ext(prop_rep_trans_ext)
                            .clone();

                        let join_rep_prop_set =
                            ConceptRepresentativePropagationSetHash::get_representative_propagation_set(
                                calc_alg_context.process_context_mut(),
                                rep_prop_set_hash,
                                join_concept,
                                true,
                            );
                        let prop_bind_des = calc_alg_context
                            .process_context()
                            .prop_binding_set(prop_binding_set)
                            .get_propagation_binding_descriptor_linker();
                        let prop_all_flag = calc_alg_context
                            .process_context()
                            .prop_binding_set(prop_binding_set)
                            .has_propagate_all_flag();
                        let mut left_rep_data = calc_alg_context
                            .process_context()
                            .rep_prop_des(left_rep_prop_des)
                            .get_representative_variable_binding_path_set_data();
                        let mut right_rep_data = calc_alg_context
                            .process_context()
                            .rep_prop_des(right_rep_prop_des)
                            .get_representative_variable_binding_path_set_data();

                        if self.are_representatives_joinable(
                            process_indi,
                            left_rep_data,
                            right_rep_data,
                            &var_linker,
                            calc_alg_context,
                        ) {
                            let mut join_data = Id::NONE;
                            let mut loc_join_data = Id::NONE;
                            let mut rep_joining_hash =
                                calc_alg_context.processing_data_box().use_rep_joining_hash;
                            if rep_joining_hash.is_some() {
                                join_data =
                                    RepresentativeJoiningHash::get_representative_joining_data(
                                        calc_alg_context.process_context_mut(),
                                        rep_joining_hash,
                                        left_rep_data,
                                        right_rep_data,
                                        false,
                                    );
                            }

                            if join_data.is_none() {
                                let mut rep_var_bind_path_set_hash = Id::NONE;
                                if !RepresentativeVariableBindingPathSetData::has_joining_data(
                                    calc_alg_context.process_context(),
                                    left_rep_data,
                                    concept,
                                ) {
                                    rep_var_bind_path_set_hash = calc_alg_context
                                        .representative_variable_binding_path_set_hash(true);
                                    left_rep_data = RepresentativeVariableBindingPathSetHash::get_representative_variable_binding_path_set_data_for_data(
                                        calc_alg_context.process_context_mut(),
                                        rep_var_bind_path_set_hash,
                                        left_rep_data,
                                        true,
                                    );
                                }
                                if !RepresentativeVariableBindingPathSetData::has_joining_data(
                                    calc_alg_context.process_context(),
                                    right_rep_data,
                                    concept,
                                ) {
                                    if rep_var_bind_path_set_hash.is_none() {
                                        rep_var_bind_path_set_hash = calc_alg_context
                                            .representative_variable_binding_path_set_hash(true);
                                    }
                                    right_rep_data = RepresentativeVariableBindingPathSetHash::get_representative_variable_binding_path_set_data_for_data(
                                        calc_alg_context.process_context_mut(),
                                        rep_var_bind_path_set_hash,
                                        right_rep_data,
                                        true,
                                    );
                                }

                                if loc_join_data.is_none() {
                                    rep_joining_hash =
                                        calc_alg_context.representative_joining_hash(true);
                                    loc_join_data =
                                        RepresentativeJoiningHash::get_representative_joining_data(
                                            calc_alg_context.process_context_mut(),
                                            rep_joining_hash,
                                            left_rep_data,
                                            right_rep_data,
                                            true,
                                        );
                                    join_data = loc_join_data;
                                }

                                let left_joining_key_map = self
                                    .get_representative_joining_key_data(
                                        left_rep_data,
                                        concept,
                                        calc_alg_context,
                                    );
                                let right_joining_key_map = self
                                    .get_representative_joining_key_data(
                                        right_rep_data,
                                        concept,
                                        calc_alg_context,
                                    );

                                let mut rep_join_common_key_map = calc_alg_context
                                    .process_context()
                                    .rep_joining_data(join_data)
                                    .get_representative_joining_common_key_map()
                                    .clone();
                                self.create_common_joining_key_map(
                                    &mut rep_join_common_key_map,
                                    &left_joining_key_map,
                                    left_rep_data,
                                    &right_joining_key_map,
                                    right_rep_data,
                                    true,
                                    calc_alg_context,
                                );
                                calc_alg_context
                                    .process_context_mut()
                                    .rep_joining_data_mut(join_data)
                                    .joining_common_key_map = rep_join_common_key_map;
                            }

                            let rep_join_common_key_map = calc_alg_context
                                .process_context()
                                .rep_joining_data(join_data)
                                .get_representative_joining_common_key_map()
                                .clone();
                            if rep_join_common_key_map.count() > 0 {
                                self.stat_representative_joined_count += 1;

                                if prop_all_flag {
                                    let mut join_all_ext_data = calc_alg_context
                                        .process_context()
                                        .rep_joining_data(join_data)
                                        .joining_all_extension
                                        .clone();
                                    if join_all_ext_data.is_none() {
                                        if loc_join_data.is_none() {
                                            rep_joining_hash =
                                                calc_alg_context.representative_joining_hash(true);
                                            loc_join_data =
                                                RepresentativeJoiningHash::get_representative_joining_data(
                                                    calc_alg_context.process_context_mut(),
                                                    rep_joining_hash,
                                                    left_rep_data,
                                                    right_rep_data,
                                                    true,
                                                );
                                            join_data = loc_join_data;
                                        }

                                        let process_context = calc_alg_context
                                            .process_context()
                                            .rep_joining_data(join_data)
                                            .process_context;
                                        let mut new_ext =
                                            RepresentativeJoiningAllDataExtension::new(
                                                process_context,
                                            );
                                        self.create_common_joining_all(
                                            &rep_join_common_key_map,
                                            &mut new_ext,
                                            left_rep_data,
                                            right_rep_data,
                                            calc_alg_context,
                                        );
                                        calc_alg_context
                                            .process_context_mut()
                                            .rep_joining_data_mut(join_data)
                                            .joining_all_extension = Some(new_ext.clone());
                                        join_all_ext_data = Some(new_ext);
                                    }

                                    let mut join_all_ext_data =
                                        join_all_ext_data.expect("joining all extension");
                                    let joined_rep_data = join_all_ext_data
                                        .get_representative_variable_binding_path_set_data();
                                    let left_rep_id = calc_alg_context
                                        .process_context()
                                        .rep_var_bind_path_set_data(left_rep_data)
                                        .get_representative_id();
                                    if !prop_rep_trans_ext_work
                                        .get_left_representative_propagation_map()
                                        .contains(left_rep_id)
                                    {
                                        let left_dep = calc_alg_context
                                            .process_context()
                                            .rep_prop_des(left_rep_prop_des)
                                            .get_dependency_track_point();
                                        let mut next_dep_track_point: TrackPointId = Id::NONE;
                                        let _rep_prop_dep_node = self
                                            .create_representative_and_dependency(
                                                &mut next_dep_track_point,
                                                process_indi,
                                                con_des,
                                                left_dep,
                                                calc_alg_context,
                                            );
                                        if next_dep_track_point.is_none() {
                                            next_dep_track_point = left_dep;
                                        }
                                        let propagate_rep_des = calc_alg_context
                                            .process_context_mut()
                                            .alloc_rep_prop_des(
                                                RepresentativePropagationDescriptor::new(),
                                            );
                                        calc_alg_context
                                            .process_context_mut()
                                            .rep_prop_des_mut(propagate_rep_des)
                                            .init_representative_descriptor(
                                                left_rep_data,
                                                next_dep_track_point,
                                            );
                                        prop_rep_trans_ext_work
                                            .get_left_representative_propagation_map_mut()
                                            .map
                                            .insert(
                                                left_rep_id,
                                                RepresentativePropagationMapData::new(
                                                    propagate_rep_des,
                                                ),
                                            );
                                    }
                                    let right_rep_id = calc_alg_context
                                        .process_context()
                                        .rep_var_bind_path_set_data(right_rep_data)
                                        .get_representative_id();
                                    if !prop_rep_trans_ext_work
                                        .get_right_representative_propagation_map()
                                        .contains(right_rep_id)
                                    {
                                        let right_dep = calc_alg_context
                                            .process_context()
                                            .rep_prop_des(right_rep_prop_des)
                                            .get_dependency_track_point();
                                        let mut next_dep_track_point: TrackPointId = Id::NONE;
                                        let _rep_prop_dep_node = self
                                            .create_representative_and_dependency(
                                                &mut next_dep_track_point,
                                                process_indi,
                                                con_des,
                                                right_dep,
                                                calc_alg_context,
                                            );
                                        if next_dep_track_point.is_none() {
                                            next_dep_track_point = right_dep;
                                        }
                                        let propagate_rep_des = calc_alg_context
                                            .process_context_mut()
                                            .alloc_rep_prop_des(
                                                RepresentativePropagationDescriptor::new(),
                                            );
                                        calc_alg_context
                                            .process_context_mut()
                                            .rep_prop_des_mut(propagate_rep_des)
                                            .init_representative_descriptor(
                                                right_rep_data,
                                                next_dep_track_point,
                                            );
                                        prop_rep_trans_ext_work
                                            .get_right_representative_propagation_map_mut()
                                            .map
                                            .insert(
                                                right_rep_id,
                                                RepresentativePropagationMapData::new(
                                                    propagate_rep_des,
                                                ),
                                            );
                                    }

                                    let left_resolve_map = join_all_ext_data
                                        .get_left_resolve_variable_binding_path_map(false)
                                        .map(|map| map.clone());
                                    let right_resolve_map = join_all_ext_data
                                        .get_right_resolve_variable_binding_path_map(false)
                                        .map(|map| map.clone());
                                    let left_rep_prop_map = prop_rep_trans_ext_work
                                        .get_left_representative_propagation_map()
                                        .clone();
                                    let right_rep_prop_map = prop_rep_trans_ext_work
                                        .get_right_representative_propagation_map()
                                        .clone();

                                    let left_dep = calc_alg_context
                                        .process_context()
                                        .rep_prop_des(left_rep_prop_des)
                                        .get_dependency_track_point();
                                    let mut left_next_resolve_dep_track_point: TrackPointId =
                                        Id::NONE;
                                    let _left_resolve_rep_node = self
                                        .create_resolve_representative_dependency(
                                            &mut left_next_resolve_dep_track_point,
                                            process_indi,
                                            Id::NONE,
                                            left_resolve_map.as_ref(),
                                            Some(&left_rep_prop_map),
                                            left_dep,
                                            Id::NONE,
                                            calc_alg_context,
                                        );
                                    if left_next_resolve_dep_track_point.is_none() {
                                        left_next_resolve_dep_track_point = left_dep;
                                    }

                                    let right_dep = calc_alg_context
                                        .process_context()
                                        .rep_prop_des(right_rep_prop_des)
                                        .get_dependency_track_point();
                                    let mut right_next_resolve_dep_track_point: TrackPointId =
                                        Id::NONE;
                                    let _right_resolve_rep_node = self
                                        .create_resolve_representative_dependency(
                                            &mut right_next_resolve_dep_track_point,
                                            process_indi,
                                            Id::NONE,
                                            right_resolve_map.as_ref(),
                                            Some(&right_rep_prop_map),
                                            right_dep,
                                            Id::NONE,
                                            calc_alg_context,
                                        );
                                    if right_next_resolve_dep_track_point.is_none() {
                                        right_next_resolve_dep_track_point = right_dep;
                                    }

                                    let mut join_next_dep_track_point: TrackPointId = Id::NONE;
                                    let _join_resolve_rep_node = self
                                        .create_representative_join_dependency(
                                            &mut join_next_dep_track_point,
                                            process_indi,
                                            con_des,
                                            left_next_resolve_dep_track_point,
                                            right_next_resolve_dep_track_point,
                                            calc_alg_context,
                                        );
                                    if join_next_dep_track_point.is_none() {
                                        join_next_dep_track_point =
                                            left_next_resolve_dep_track_point;
                                    }

                                    let propagate_rep_des =
                                        calc_alg_context.process_context_mut().alloc_rep_prop_des(
                                            RepresentativePropagationDescriptor::new(),
                                        );
                                    calc_alg_context
                                        .process_context_mut()
                                        .rep_prop_des_mut(propagate_rep_des)
                                        .init_representative_descriptor(
                                            joined_rep_data,
                                            join_next_dep_track_point,
                                        );
                                    RepresentativePropagationSet::add_incoming_representative_propagation(
                                        calc_alg_context.process_context_mut(),
                                        join_rep_prop_set,
                                        propagate_rep_des,
                                    );
                                    self.update_representative_propagation_set(
                                        process_indi,
                                        join_rep_prop_set,
                                        calc_alg_context,
                                    );

                                    if join_con_des.is_none() {
                                        join_dep_track_point = join_next_dep_track_point;
                                        join_con_des = self
                                            .add_concept_to_individual_return_concept_descriptor(
                                                join_concept,
                                                join_concept_negation,
                                                process_indi,
                                                join_next_dep_track_point,
                                                false,
                                                false,
                                                calc_alg_context,
                                            );
                                    }
                                } else {
                                    // Konclude leaves the non-propagate-all branch as
                                    // `// ToDo!`; keep that exact semantic gap.
                                }

                                propagations_done = true;
                            }
                        }

                        prop_rep_trans_ext_work
                            .set_left_last_representative_joining_descriptor(left_rep_prop_des)
                            .set_right_last_representative_joining_descriptor(right_rep_prop_des)
                            .set_last_analysed_propagation_binding_descriptor(prop_bind_des)
                            .set_last_analysed_propagate_all_flag(
                                calc_alg_context
                                    .process_context()
                                    .prop_binding_set(prop_binding_set)
                                    .has_propagate_all_flag(),
                            );
                        *calc_alg_context
                            .process_context_mut()
                            .prop_rep_trans_ext_mut(prop_rep_trans_ext) = prop_rep_trans_ext_work;
                    }
                }
            }
        }

        if propagations_done && !create_join_concept {
            self.reapply_concept_updated_representative(
                *process_indi,
                join_con_des,
                join_dep_track_point,
                con_set,
                0,
                calc_alg_context,
            );
            let _ = reapply_queue_empty;
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyREPRESENTATIVEBINDVARIABLERule`.
    ///
    /// C++ (cpp 10803–10923): if the propagation-variable-binding transition
    /// extension needs updating, builds a fresh `CVariableBinding(Path)` +
    /// representative path set data, creates the `REPRESENTATIVEBINDVARIABLE`
    /// dependency, adds the binding-trigger concept (or reapplies it), and registers
    /// the incoming representative propagation via `updateRepresentativePropagationSet`.
    pub fn apply_representative_bind_variable_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let con_des: ConDescId = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .get_concept_descriptor();
        let concept: ConceptId = calc_alg_context
            .process_context()
            .con_desc(con_des)
            .get_concept();
        let variable: VariableId = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_variable()
            .unwrap_or(Id::NONE);
        let dep_track_point: TrackPointId = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .get_dependency_track_point();
        let op_con_linker = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operand_list()
            .to_vec();
        if op_con_linker.is_empty() {
            return;
        }

        let binding_trigger_concept = op_con_linker[0].target;
        let binding_trigger_concept_negation = op_con_linker[0].negated;
        let binding_trigger_tag = calc_alg_context
            .ontology_arenas()
            .concept(binding_trigger_concept)
            .get_concept_tag();
        let concept_tag = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_concept_tag();

        let con_set: LabelSetId = calc_alg_context
            .process_context_mut()
            .node_reapply_concept_label_set(*process_indi);
        let mut binding_con_des: ConDescId = Id::NONE;
        let mut binding_dep_track_point: TrackPointId = Id::NONE;
        let mut reapply_queue_empty = true;

        // W3-DEFER[stat]: STATINC(VARBINDRULEBINDAPPLICATIONCOUNT,calcAlgContext).
        let mut update_ext = false;
        let con_prop_binding_set_hash = calc_alg_context
            .process_context()
            .node(*process_indi)
            .use_concept_prop_binding_set_hash;
        if con_prop_binding_set_hash.is_some() {
            let prop_binding_set = ConceptPropagationBindingSetHash::get_propagation_binding_set(
                calc_alg_context.process_context_mut(),
                con_prop_binding_set_hash,
                concept_tag,
                false,
            );
            if prop_binding_set.is_some() {
                let prop_var_bind_trans_ext = calc_alg_context
                    .process_context()
                    .prop_binding_set(prop_binding_set)
                    .prop_var_bind_trans_extension;
                let processing_not_completed = prop_var_bind_trans_ext.is_none()
                    || !calc_alg_context
                        .process_context()
                        .prop_var_bind_trans_ext(prop_var_bind_trans_ext)
                        .is_processing_completed();
                if processing_not_completed {
                    if prop_var_bind_trans_ext.is_none()
                        || calc_alg_context
                            .process_context()
                            .prop_binding_set(prop_binding_set)
                            .has_propagate_all_flag()
                    {
                        update_ext = true;
                    } else {
                        let last_analy_prop_bind_des = calc_alg_context
                            .process_context()
                            .prop_var_bind_trans_ext(prop_var_bind_trans_ext)
                            .get_last_analysed_propagation_binding_descriptor();
                        let prop_bind_des = calc_alg_context
                            .process_context()
                            .prop_binding_set(prop_binding_set)
                            .get_propagation_binding_descriptor_linker();
                        if last_analy_prop_bind_des != prop_bind_des {
                            update_ext = true;
                        }
                    }
                }
            }
        }

        if update_ext {
            let con_prop_binding_set_hash = calc_alg_context
                .process_context_mut()
                .node_concept_propagation_binding_set_hash(*process_indi);
            let prop_binding_set = ConceptPropagationBindingSetHash::get_propagation_binding_set(
                calc_alg_context.process_context_mut(),
                con_prop_binding_set_hash,
                concept_tag,
                true,
            );
            let prop_var_bind_trans_ext =
                PropagationBindingSet::get_propagation_variable_binding_transition_extension(
                    calc_alg_context.process_context_mut(),
                    prop_binding_set,
                    true,
                );

            let last_analy_prop_bind_des = calc_alg_context
                .process_context()
                .prop_var_bind_trans_ext(prop_var_bind_trans_ext)
                .get_last_analysed_propagation_binding_descriptor();
            let prop_bind_des = calc_alg_context
                .process_context()
                .prop_binding_set(prop_binding_set)
                .get_propagation_binding_descriptor_linker();

            {
                let indi_id = calc_alg_context
                    .process_context()
                    .node(*process_indi)
                    .individual_node_id();
                calc_alg_context
                    .process_context_mut()
                    .prop_var_bind_trans_ext_mut(prop_var_bind_trans_ext)
                    .set_triggered_variable_individual_pair_value((variable, indi_id));
            }
            let mut create_var_binding = calc_alg_context
                .process_context()
                .prop_binding_set(prop_binding_set)
                .has_propagate_all_flag();
            let mut prop_bind_des_it = prop_bind_des;
            while prop_bind_des_it != last_analy_prop_bind_des && prop_bind_des_it.is_some() {
                if PropagationVariableBindingTransitionExtension::add_analysed_propagation_binding_descriptor_return_matched(
                    calc_alg_context.process_context_mut(),
                    prop_var_bind_trans_ext,
                    prop_bind_des_it,
                    None,
                ) {
                    create_var_binding = true;
                }
                prop_bind_des_it = calc_alg_context
                    .process_context()
                    .prop_binding_des(prop_bind_des_it)
                    .get_next();
            }
            let propagate_all_flag = calc_alg_context
                .process_context()
                .prop_binding_set(prop_binding_set)
                .has_propagate_all_flag();
            calc_alg_context
                .process_context_mut()
                .prop_var_bind_trans_ext_mut(prop_var_bind_trans_ext)
                .set_last_analysed_propagation_binding_descriptor(prop_bind_des)
                .set_last_analysed_propagate_all_flag(propagate_all_flag);

            if create_var_binding {
                self.stat_representative_created_count += 1;
                // W3-DEFER[stat]: STATINC(VARBINDVARIABLEBINDCOUNT,calcAlgContext).
                calc_alg_context
                    .process_context_mut()
                    .prop_var_bind_trans_ext_mut(prop_var_bind_trans_ext)
                    .set_processing_completed(true);

                let con_rep_prop_set_hash = calc_alg_context
                    .process_context_mut()
                    .node_concept_representative_propagation_set_hash(*process_indi);
                let rep_prop_set =
                    ConceptRepresentativePropagationSetHash::get_representative_propagation_set(
                        calc_alg_context.process_context_mut(),
                        con_rep_prop_set_hash,
                        binding_trigger_concept,
                        true,
                    );

                let next_path_prop_id = calc_alg_context
                    .processing_data_box_mut()
                    .next_variable_binding_path_id(true);

                let mut next_dep_track_point: TrackPointId = Id::NONE;
                let _bind_dep_node = self.create_representative_bind_variable_dependency(
                    &mut next_dep_track_point,
                    process_indi,
                    con_des,
                    dep_track_point,
                    calc_alg_context,
                );
                if next_dep_track_point.is_none() {
                    next_dep_track_point = dep_track_point;
                }

                let has_binding = calc_alg_context
                    .process_context()
                    .label_set(con_set)
                    .get_concept_descriptor_and_reapply_queue_state_by_tag(
                        binding_trigger_tag,
                        &mut binding_con_des,
                        &mut binding_dep_track_point,
                        &mut reapply_queue_empty,
                    );
                if !has_binding {
                    binding_con_des = self.add_concept_to_individual_return_concept_descriptor(
                        binding_trigger_concept,
                        binding_trigger_concept_negation,
                        process_indi,
                        next_dep_track_point,
                        false,
                        false,
                        calc_alg_context,
                    );
                } else {
                    self.reapply_concept_updated_representative(
                        *process_indi,
                        binding_con_des,
                        binding_dep_track_point,
                        con_set,
                        0,
                        calc_alg_context,
                    );
                    let _ = reapply_queue_empty;
                }

                calc_alg_context
                    .process_context_mut()
                    .rep_prop_set_mut(rep_prop_set)
                    .set_concept_descriptor(binding_con_des);
                let var_binding = calc_alg_context
                    .process_context_mut()
                    .alloc_var_binding(VariableBinding::new());
                calc_alg_context
                    .process_context_mut()
                    .var_binding_mut(var_binding)
                    .init_variable_binding(next_dep_track_point, *process_indi, variable);
                let var_binding_des = calc_alg_context
                    .process_context_mut()
                    .alloc_var_binding_des(VariableBindingDescriptor::new());
                calc_alg_context
                    .process_context_mut()
                    .var_binding_des_mut(var_binding_des)
                    .init_variable_binding_descriptor(var_binding);
                let var_binding_path = calc_alg_context
                    .process_context_mut()
                    .alloc_vbpath(VariableBindingPath::new());
                calc_alg_context
                    .process_context_mut()
                    .vbpath_mut(var_binding_path)
                    .init_variable_binding_path(next_path_prop_id, var_binding_des);

                // W2-DEFER[api]: CRepresentativeVariableBindingPathHash is still a
                // databox placeholder, so this allocates the equivalent
                // CRepresentativeVariableBindingPathSetData directly and inserts it
                // into the live CRepresentativeVariableBindingPathSetHash below.
                let localization_tag = calc_alg_context
                    .process_context()
                    .used_process_tagger()
                    .get_current_localization_tag();
                let rep_data = calc_alg_context
                    .process_context_mut()
                    .alloc_rep_var_bind_path_set_data(
                        RepresentativeVariableBindingPathSetData::new(INVALID, localization_tag),
                    );
                let rep_id = calc_alg_context
                    .processing_data_box_mut()
                    .next_representative_variable_binding_path_id(true);
                calc_alg_context
                    .process_context_mut()
                    .rep_var_bind_path_set_data_mut(rep_data)
                    .init_representative_variable_binding_path_data(None)
                    .set_representative_id(rep_id)
                    .set_migratable(false)
                    .inc_use_count(1)
                    .inc_share_count(1)
                    .add_key_signature_value(rep_id);
                let rep_migrate_data = RepresentativeVariableBindingPathSetData::get_migrate_data(
                    calc_alg_context.process_context_mut(),
                    rep_data,
                    true,
                );
                {
                    let mut map_data =
                        RepresentativeVariableBindingPathMapData::new(var_binding_path, rep_data);
                    map_data.resolve_rep_var_bind_path_set_data_id = rep_id;
                    calc_alg_context
                        .process_context_mut()
                        .rep_var_bind_path_set_migrate_data_mut(rep_migrate_data)
                        .get_representative_variable_binding_path_map_mut()
                        .insert(next_path_prop_id, map_data);
                }
                calc_alg_context
                    .process_context_mut()
                    .rep_var_bind_path_set_migrate_data_mut(rep_migrate_data)
                    .get_representative_containing_map_mut()
                    .insert_contained_representative(rep_id, rep_data, false);

                let rep_var_bind_path_set_hash =
                    calc_alg_context.representative_variable_binding_path_set_hash(true);
                RepresentativeVariableBindingPathSetHash::insert_representative_variable_binding_path_set_data(
                    calc_alg_context.process_context_mut(),
                    rep_var_bind_path_set_hash,
                    rep_data,
                );

                let rep_prop_des = calc_alg_context
                    .process_context_mut()
                    .alloc_rep_prop_des(RepresentativePropagationDescriptor::new());
                calc_alg_context
                    .process_context_mut()
                    .rep_prop_des_mut(rep_prop_des)
                    .init_representative_descriptor(rep_data, next_dep_track_point);
                RepresentativePropagationSet::add_incoming_representative_propagation_descriptor_linker(
                    calc_alg_context.process_context_mut(),
                    rep_prop_set,
                    rep_prop_des,
                );
                self.update_representative_propagation_set(
                    process_indi,
                    rep_prop_set,
                    calc_alg_context,
                );
            }
        }
        let _ = negate;
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyREPRESENTATIVEIMPLICATIONRule`.
    ///
    /// C++ (cpp 10927–11047): two symmetric arms keyed on whether the binding
    /// trigger concept is already in the label set. Either installs the next missing
    /// trigger into the reapply queue, or — when all triggers are present — builds
    /// the CONNECTION dependency chain over the triggers, creates the
    /// `REPRESENTATIVEIMPLICATION` dependency, and calls `propagateRepresentative`
    /// (guarded by `requiresRepresentativePropagation` in the already-present arm),
    /// optionally `reapplyConceptUpdatedRepresentative`.
    pub fn apply_representative_implication_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
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
        let op_linker = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operand_list()
            .to_vec();
        if op_linker.is_empty() {
            return;
        }

        let con_set: LabelSetId = calc_alg_context
            .process_context_mut()
            .node_reapply_concept_label_set(*process_indi);
        let mut binding_con_des: ConDescId = Id::NONE;
        let mut binding_dep_track_point: TrackPointId = Id::NONE;
        let mut reapply_queue_empty = true;
        let binding_trigger_concept = op_linker[0].target;
        let binding_trigger_concept_negation = op_linker[0].negated;
        let trigger_linker = &op_linker[1..];
        let binding_trigger_tag = calc_alg_context
            .ontology_arenas()
            .concept(binding_trigger_concept)
            .get_concept_tag();

        // W3-DEFER[stat]: STATINC(VARBINDRULEIMPLICATIONAPPLICATIONCOUNT,calcAlgContext).
        let has_binding = calc_alg_context
            .process_context()
            .label_set(con_set)
            .get_concept_descriptor_and_reapply_queue_state_by_tag(
                binding_trigger_tag,
                &mut binding_con_des,
                &mut binding_dep_track_point,
                &mut reapply_queue_empty,
            );

        if !has_binding {
            let con_set = calc_alg_context
                .process_context_mut()
                .node_reapply_concept_label_set(*process_indi);
            let mut all_triggers_available = true;
            let mut next_missing_trigger = None;
            for next_trigger in trigger_linker.iter().copied() {
                let mut trigger_con_des: ConDescId = Id::NONE;
                let mut trigger_dep_track_point: TrackPointId = Id::NONE;
                if calc_alg_context
                    .process_context()
                    .label_set(con_set)
                    .get_concept_descriptor(
                        next_trigger.target,
                        &mut trigger_con_des,
                        &mut trigger_dep_track_point,
                    )
                {
                    if calc_alg_context
                        .process_context()
                        .con_desc(trigger_con_des)
                        .is_negated()
                        == next_trigger.negated
                    {
                        return;
                    }
                } else {
                    all_triggers_available = false;
                    next_missing_trigger = Some(next_trigger);
                    break;
                }
            }

            if !all_triggers_available {
                let next_trigger = next_missing_trigger.expect("missing trigger recorded");
                let trigger_negation = !next_trigger.negated;
                if !self.is_concept_in_reapply_queue_concept(
                    con_des,
                    next_trigger.target,
                    trigger_negation,
                    *process_indi,
                    calc_alg_context,
                ) {
                    self.add_concept_to_reapply_queue_concept(
                        con_des,
                        next_trigger.target,
                        trigger_negation,
                        *process_indi,
                        false,
                        dep_track_point,
                        calc_alg_context,
                    );
                }
            } else {
                let trigger_deps = self.create_representative_trigger_dependency_chain(
                    *process_indi,
                    trigger_linker,
                    con_set,
                    calc_alg_context,
                );
                self.stat_representative_implication_count += 1;

                let con_rep_prop_set_hash = calc_alg_context
                    .process_context_mut()
                    .node_concept_representative_propagation_set_hash(*process_indi);
                let prev_rep_prop_set =
                    ConceptRepresentativePropagationSetHash::get_representative_propagation_set(
                        calc_alg_context.process_context_mut(),
                        con_rep_prop_set_hash,
                        concept,
                        false,
                    );
                let rep_prop_set =
                    ConceptRepresentativePropagationSetHash::get_representative_propagation_set(
                        calc_alg_context.process_context_mut(),
                        con_rep_prop_set_hash,
                        binding_trigger_concept,
                        true,
                    );
                let proc_rep_prop_des = if prev_rep_prop_set.is_some() {
                    calc_alg_context
                        .process_context()
                        .rep_prop_set(prev_rep_prop_set)
                        .get_outgoing_representative_propagation_descriptor_linker()
                } else {
                    Id::NONE
                };
                if proc_rep_prop_des.is_some() {
                    let prop_dep_track_point = calc_alg_context
                        .process_context()
                        .rep_prop_des(proc_rep_prop_des)
                        .get_dependency_track_point();
                    calc_alg_context
                        .process_context_mut()
                        .rep_prop_set_mut(rep_prop_set)
                        .set_concept_descriptor(binding_con_des);
                    let mut next_dep_track_point: TrackPointId = Id::NONE;
                    let _impl_dep_node = self.create_representative_implication_dependency(
                        &mut next_dep_track_point,
                        process_indi,
                        con_des,
                        prop_dep_track_point,
                        trigger_deps,
                        calc_alg_context,
                    );
                    if next_dep_track_point.is_none() {
                        next_dep_track_point = prop_dep_track_point;
                    }
                    let _binding_con_des = self
                        .add_concept_to_individual_return_concept_descriptor(
                            binding_trigger_concept,
                            binding_trigger_concept_negation,
                            process_indi,
                            next_dep_track_point,
                            true,
                            false,
                            calc_alg_context,
                        );
                    self.propagate_representative(
                        process_indi,
                        proc_rep_prop_des,
                        rep_prop_set,
                        next_dep_track_point,
                        calc_alg_context,
                    );
                }
            }
        } else {
            let con_rep_prop_set_hash = calc_alg_context
                .process_context_mut()
                .node_concept_representative_propagation_set_hash(*process_indi);
            let prev_rep_prop_set =
                ConceptRepresentativePropagationSetHash::get_representative_propagation_set(
                    calc_alg_context.process_context_mut(),
                    con_rep_prop_set_hash,
                    concept,
                    false,
                );
            let rep_prop_set =
                ConceptRepresentativePropagationSetHash::get_representative_propagation_set(
                    calc_alg_context.process_context_mut(),
                    con_rep_prop_set_hash,
                    binding_trigger_concept,
                    true,
                );
            let proc_rep_prop_des = if prev_rep_prop_set.is_some() {
                calc_alg_context
                    .process_context()
                    .rep_prop_set(prev_rep_prop_set)
                    .get_outgoing_representative_propagation_descriptor_linker()
            } else {
                Id::NONE
            };
            if proc_rep_prop_des.is_some() {
                let prop_dep_track_point = calc_alg_context
                    .process_context()
                    .rep_prop_des(proc_rep_prop_des)
                    .get_dependency_track_point();
                if self.requires_representative_propagation(
                    process_indi,
                    proc_rep_prop_des,
                    rep_prop_set,
                    calc_alg_context,
                ) {
                    let trigger_deps = self.create_representative_trigger_dependency_chain(
                        *process_indi,
                        trigger_linker,
                        con_set,
                        calc_alg_context,
                    );
                    self.stat_representative_implication_count += 1;
                    let mut next_dep_track_point: TrackPointId = Id::NONE;
                    let _impl_dep_node = self.create_representative_implication_dependency(
                        &mut next_dep_track_point,
                        process_indi,
                        con_des,
                        prop_dep_track_point,
                        trigger_deps,
                        calc_alg_context,
                    );
                    if next_dep_track_point.is_none() {
                        next_dep_track_point = prop_dep_track_point;
                    }
                    self.propagate_representative(
                        process_indi,
                        proc_rep_prop_des,
                        rep_prop_set,
                        next_dep_track_point,
                        calc_alg_context,
                    );
                    self.reapply_concept_updated_representative(
                        *process_indi,
                        binding_con_des,
                        binding_dep_track_point,
                        con_set,
                        0,
                        calc_alg_context,
                    );
                    let _ = reapply_queue_empty;
                }
            }
        }
    }

    fn create_representative_trigger_dependency_chain(
        &mut self,
        process_indi: NodeId,
        trigger_linker: &[NegLink<ConceptId>],
        con_set: LabelSetId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DepLinkId {
        let mut trigger_deps: DepLinkId = Id::NONE;
        for trigger_linker_it in trigger_linker.iter().copied() {
            let mut trigger_con_des: ConDescId = Id::NONE;
            let mut trigger_dep_track_point: TrackPointId = Id::NONE;
            calc_alg_context
                .process_context()
                .label_set(con_set)
                .get_concept_descriptor(
                    trigger_linker_it.target,
                    &mut trigger_con_des,
                    &mut trigger_dep_track_point,
                );
            let mut process_indi_ref = process_indi;
            let conn_dep = self.create_connection_dependency(
                &mut process_indi_ref,
                trigger_con_des,
                trigger_dep_track_point,
                calc_alg_context,
            );
            if conn_dep.is_some() {
                let conn_dep_track_point = calc_alg_context
                    .process_context_mut()
                    .materialize_continue_dependency_track_point(conn_dep);
                let dep_link = calc_alg_context
                    .process_context_mut()
                    .alloc_dep_link(DependencyLink::new());
                {
                    let proc_ctx = calc_alg_context.process_context_mut();
                    proc_ctx
                        .dep_link_mut(dep_link)
                        .init_dependency(conn_dep_track_point);
                    proc_ctx.dep_link_mut(dep_link).next = trigger_deps;
                }
                trigger_deps = dep_link;
            }
        }
        trigger_deps
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyREPRESENTATIVEALLRule`.
    ///
    /// C++ (cpp 11121–11157): mirrors `applyAutomatTransactions`' AQALL arm but for
    /// representatives — `getLinkProcessingRestriction`; for the restricted link, or
    /// every role successor in `getReapplyRoleSuccessorHash`, calls
    /// `propagateRepresentativeToSuccessor(...)`; if not reapplied and not already
    /// queued, `addConceptToReapplyQueue(conDes, role, processIndi, true, depTrackPoint)`.
    pub fn apply_representative_all_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
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
        let concept_op_linker = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operand_list()
            .to_vec();

        // W3-DEFER[stat]: STATINC(VARBINDRULEALLAPPLICATIONCOUNT,calcAlgContext).
        let rest_link: EdgeId =
            self.get_link_processing_restriction(*con_pro_des, calc_alg_context);
        if rest_link.is_some() {
            let mut succ_indi =
                self.get_successor_individual(process_indi, rest_link, calc_alg_context);
            self.propagate_representative_to_successor(
                *process_indi,
                &mut succ_indi,
                &concept_op_linker,
                negate,
                con_des,
                rest_link,
                calc_alg_context,
            );
        } else {
            let role_succ_hash = calc_alg_context
                .process_context()
                .node_reapply_role_successor_hash_existing(*process_indi);
            if role_succ_hash.is_some() {
                let mut role_succ_it = {
                    let proc_ctx = calc_alg_context.process_context();
                    proc_ctx
                        .role_succ_hash(role_succ_hash)
                        .get_role_successor_link_iterator(proc_ctx.edges(), role)
                };
                while role_succ_it.has_next() {
                    let link = role_succ_it.next(true);
                    let mut succ_indi =
                        self.get_successor_individual(process_indi, link, calc_alg_context);
                    self.propagate_representative_to_successor(
                        *process_indi,
                        &mut succ_indi,
                        &concept_op_linker,
                        negate,
                        con_des,
                        link,
                        calc_alg_context,
                    );
                }
            }
        }

        if !calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .is_concept_reapplied()
            && !self.is_concept_in_reapply_queue_role(
                con_des,
                role,
                *process_indi,
                calc_alg_context,
            )
        {
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
