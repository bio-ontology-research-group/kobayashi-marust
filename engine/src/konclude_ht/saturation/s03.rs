//! `saturation::s03` — Approximate-saturation tableau rules core (port unit #3 of 12).
//!
//! Faithful port of the **non-cardinality** tableau saturation rules of Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauApproximationSaturationTaskHandleAlgorithm.cpp`
//! (manifest `03-saturation-calc.md`, "PU-SAT-3"):
//!
//!   * the rule dispatch `applyTableauSaturationRule` (cpp 5718–5740),
//!   * `applyAutomatChooseRule` (5743), `applyANDRule` (5973), `applyNONERule`
//!     (5983), `applyIMPLICATIONRule` (5987), `applyORRule` (6032),
//!     `applyELSERule` (6102), `applyEQCANDRule` (6145), `applyBOTTOMRule` (6150),
//!     `applySELFRule` (6856), `applySOMERule` (6925),
//!   * the disjunct-checking helper `getDisjunctCheckingConcept` (6006),
//!   * the qualified-`∀` automaton transition helpers `addAutomateTransitionOperands`
//!     (6682) and `testAutomateTransitionOperandsAddable` (6703).
//!
//! The cardinality rules (`applyALLRule` / `applyATMOSTRule` / `applyATLEASTRule` /
//! `applyVALUERule` / `applyNOMINALRule`), the datatype rules (`applyDATATYPERule` /
//! `applyNotDATATYPERule` / `applyDATALITERALRule`) and `applyBackwardPropagationConcepts`
//! live in the sibling saturation units (PU-SAT-4 / PU-SAT-5 / PU-SAT-6/7).
//!
//! CONTEXT CONVENTION. The saturation `.h` declares these rule methods as members
//! of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm` that read the
//! SHARED algorithm context via the member `mCalcAlgContext`
//! (`CCalculationAlgorithmContextBase*`). Per the port convention the member is
//! threaded as `calc_alg_context: &mut CalculationAlgorithmContextBase`; the static
//! TBox/RBox is reached through `calc_alg_context.ontology_arenas()` and the
//! per-test sat nodes through `calc_alg_context.process_context().sat_node(id)` /
//! `_mut` / `alloc_sat_node`.
//!
//! KONCLUDE-PORT-NOTE[ownership]: the C++ `CIndividualSaturationProcessNode*&
//! processIndi` out/in-out pointer-reference becomes `&mut SatNodeId`; the
//! `CConceptSaturationProcessLinker* conSatProLinker` payload becomes
//! `ConceptSaturationProcessLinkerId`; `CConcept*` / `CRole*` become
//! `ConceptId` / `RoleId`.
//!
//! KONCLUDE-PORT-NOTE[api]: the W1 concept/role terminology arenas and the W3.5
//! per-test process context ARE wired, so every rule whose body is pure
//! concept/role logic + sibling-method delegation is ported LIVE
//! (`applyNONERule`, `applySOMERule`, `applyELSERule`, `applyBOTTOMRule`,
//! `applyIMPLICATIONRule`, `getDisjunctCheckingConcept`, `addAutomateTransitionOperands`). The remaining
//! rules each open with `conDes = conSatProLinker->getConceptSaturationDescriptor()`
//! and then drive their control flow through the not-yet-ported saturation SATELLITE
//! classes (`CRoleBackwardSaturationPropagationHash`,
//! `CBackwardSaturationPropagation*`, `CSaturationConceptDataItem`, and
//! `CConceptSaturationReferenceLinkingData`). Those bodies keep the faithful
//! signature + a full structural transcription of the C++ and defer with
//! `todo!("W4-DEFER[api]: …")`; logic is documented, never dropped.

#![allow(dead_code)]
#![allow(unused_variables)]

use super::super::completion::context::CalculationAlgorithmContextBase;
use super::super::model::op::{
    CCALL, CCAND, CCAQALL, CCAQAND, CCAQCHOOCE, CCAQSOME, CCATLEAST, CCATMOST, CCATOM, CCBOTTOM,
    CCBRANCHALL, CCBRANCHAQALL, CCBRANCHAQAND, CCBRANCHIMPL, CCBRANCHTRIG, CCDATALITERAL,
    CCDATATYPE, CCEQ, CCEQCAND, CCFS_AQALL_TYPE, CCFS_AQAND_TYPE, CCIMPL, CCIMPLALL, CCIMPLAQALL,
    CCIMPLAQAND, CCIMPLTRIG, CCNOMINAL, CCOR, CCSELF, CCSOME, CCSUB, CCTOP, CCVALUE,
};
use super::super::model::substrate::Cint64;
use super::super::model::{ConceptId, NegLink, RoleId};
use super::super::process::sat_node::IndividualSaturationProcessNodeStatusFlags;
use super::super::process::stubs::ConceptSaturationProcessLinkerId;
use super::super::process::SatNodeId;
use super::satellites::{
    ConceptSaturationDescriptorId, ImplicationReapplyConceptSaturationDescriptor,
    ImplicationReapplyConceptSaturationDescriptorId,
};

// `CCriticalConceptType` enum tags used by `addCriticalConceptDescriptor`.
// File-local mirror of the (file-private) `CCT_*` copy in `s09.rs` — same C++
// enum values; the canonical owner is the critical-concept unit (PU-SAT-9).
const CCT_DISJUNCTION: Cint64 = 4;
const CCT_EQCANDIDATE: Cint64 = 5;

impl super::algorithm::SaturationTaskHandleAlgorithm {
    // =======================================================================
    // Rule dispatch (cpp 5718–5740).
    // =======================================================================

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::applyTableauSaturationRule`.
    ///
    /// The per-concept jump-table dispatch: pulls the descriptor's concept,
    /// indexes the polarity-appropriate `mPosJumpFuncVec` / `mNegJumpFuncVec` by
    /// the concept operator code and either invokes the matched rule member or
    /// falls through to `applyELSERule`.
    ///
    /// C++ structure:
    /// ```text
    /// conDes    = conSatProLinker->getConceptSaturationDescriptor()
    /// conNeg    = conDes->getNegation()
    /// concept   = conDes->getConcept()
    /// conOpCode = concept->getOperatorCode()
    /// if !conNeg:  func = mPosJumpFuncVec[conOpCode]; if func (this->*func)(processIndi, conSatProLinker) else applyELSERule(...)
    /// else:        func = mNegJumpFuncVec[conOpCode]; if func (this->*func)(processIndi, conSatProLinker) else applyELSERule(...)
    /// ```
    pub fn apply_tableau_saturation_rule(
        &mut self,
        process_indi: &mut SatNodeId,
        con_sat_pro_linker: ConceptSaturationProcessLinkerId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let con_des = calc_alg_context
            .process_context()
            .con_sat_proc_linker(con_sat_pro_linker)
            .get_concept_saturation_descriptor();
        let con_negation = calc_alg_context
            .process_context()
            .con_sat_desc(con_des)
            .get_negation();
        let concept = calc_alg_context
            .process_context()
            .con_sat_desc(con_des)
            .get_concept();
        let con_op_code = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operator_code();

        if !con_negation {
            match con_op_code {
                CCDATATYPE => {
                    self.apply_datatype_rule(process_indi, con_sat_pro_linker, calc_alg_context)
                }
                CCBOTTOM => {
                    self.apply_bottom_rule(process_indi, con_sat_pro_linker, calc_alg_context)
                }
                CCATOM => self.apply_none_rule(process_indi, con_sat_pro_linker, calc_alg_context),
                CCTOP | CCAND | CCAQAND | CCIMPLAQAND | CCBRANCHAQAND | CCSUB | CCIMPLTRIG
                | CCBRANCHTRIG | CCEQ => {
                    self.apply_and_rule(process_indi, con_sat_pro_linker, calc_alg_context)
                }
                CCALL | CCAQALL | CCIMPLALL | CCBRANCHALL | CCBRANCHAQALL | CCIMPLAQALL => {
                    self.apply_all_rule(process_indi, con_sat_pro_linker, calc_alg_context)
                }
                CCSOME | CCAQSOME => {
                    self.apply_some_rule(process_indi, con_sat_pro_linker, calc_alg_context)
                }
                CCAQCHOOCE => self.apply_automat_choose_rule(
                    process_indi,
                    con_sat_pro_linker,
                    calc_alg_context,
                ),
                CCOR => self.apply_or_rule(process_indi, con_sat_pro_linker, calc_alg_context),
                CCIMPL | CCBRANCHIMPL => {
                    self.apply_implication_rule(process_indi, con_sat_pro_linker, calc_alg_context)
                }
                CCEQCAND => {
                    self.apply_eqcand_rule(process_indi, con_sat_pro_linker, calc_alg_context)
                }
                CCSELF => self.apply_self_rule(process_indi, con_sat_pro_linker, calc_alg_context),
                CCATLEAST => {
                    self.apply_atleast_rule(process_indi, con_sat_pro_linker, calc_alg_context)
                }
                CCATMOST => {
                    self.apply_atmost_rule(process_indi, con_sat_pro_linker, calc_alg_context)
                }
                CCVALUE => {
                    self.apply_value_rule(process_indi, con_sat_pro_linker, calc_alg_context)
                }
                CCNOMINAL => {
                    self.apply_nominal_rule(process_indi, con_sat_pro_linker, calc_alg_context)
                }
                CCDATALITERAL => {
                    self.apply_data_literal_rule(process_indi, con_sat_pro_linker, calc_alg_context)
                }
                _ => self.apply_else_rule(process_indi, con_sat_pro_linker, calc_alg_context),
            }
        } else {
            match con_op_code {
                CCATMOST => {
                    self.apply_atleast_rule(process_indi, con_sat_pro_linker, calc_alg_context)
                }
                CCATLEAST => {
                    self.apply_atmost_rule(process_indi, con_sat_pro_linker, calc_alg_context)
                }
                CCOR => self.apply_and_rule(process_indi, con_sat_pro_linker, calc_alg_context),
                CCALL => self.apply_some_rule(process_indi, con_sat_pro_linker, calc_alg_context),
                CCSOME => self.apply_all_rule(process_indi, con_sat_pro_linker, calc_alg_context),
                CCAQCHOOCE => self.apply_automat_choose_rule(
                    process_indi,
                    con_sat_pro_linker,
                    calc_alg_context,
                ),
                CCAND | CCEQ => {
                    self.apply_or_rule(process_indi, con_sat_pro_linker, calc_alg_context)
                }
                CCSUB | CCATOM => {
                    self.apply_none_rule(process_indi, con_sat_pro_linker, calc_alg_context)
                }
                _ => self.apply_else_rule(process_indi, con_sat_pro_linker, calc_alg_context),
            }
        }
    }

    // =======================================================================
    // Automaton-choose rule (cpp 5743–5757).
    // =======================================================================

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::applyAutomatChooseRule`.
    ///
    /// C++ structure:
    /// ```text
    /// STATINC(AUTOMATEINITCOUNT)
    /// conDes      = conSatProLinker->getConceptSaturationDescriptor()
    /// conNegation = conDes->getNegation()
    /// concept     = conDes->getConcept()
    /// for opLink in concept->getOperandList():
    ///   opConcept  = opLink->getData(); opNegation = opLink->isNegated()
    ///   if opNegation == conNegation:
    ///     addConceptFilteredToIndividual(opConcept, false, processIndi, false, mCalcAlgContext)
    /// ```
    pub fn apply_automat_choose_rule(
        &mut self,
        process_indi: &mut SatNodeId,
        con_sat_pro_linker: ConceptSaturationProcessLinkerId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // STATINC(AUTOMATEINITCOUNT) — profiling stat, elided.
        let con_des = calc_alg_context
            .process_context()
            .con_sat_proc_linker(con_sat_pro_linker)
            .get_concept_saturation_descriptor();
        let con_negation = calc_alg_context
            .process_context()
            .con_sat_desc(con_des)
            .get_negation();
        let concept = calc_alg_context
            .process_context()
            .con_sat_desc(con_des)
            .get_concept();
        // KONCLUDE-PORT-NOTE[ownership]: snapshot the operand slice so the read borrow
        // of the terminology arena is released before the `&mut self` leaf calls.
        let operands: Vec<NegLink<ConceptId>> = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operand_list()
            .to_vec();
        for op_link in operands {
            let op_concept = op_link.target; // getData()
            let op_negation = op_link.negated; // isNegated()
            if op_negation == con_negation {
                // C++: addConceptFilteredToIndividual(opConcept, false, processIndi, false, mCalcAlgContext)
                //   — the choose rule adds the operand with negation `false`; the 4-arg
                //   sibling overload elides the (false) updateCopyDepended flag.
                self.add_concept_filtered_to_individual(
                    op_concept,
                    false,
                    process_indi,
                    calc_alg_context,
                );
            }
        }
    }

    // =======================================================================
    // AND rule (cpp 5973–5980).
    // =======================================================================

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::applyANDRule`.
    ///
    /// C++ structure:
    /// ```text
    /// STATINC(ANDRULEAPPLICATIONCOUNT)
    /// conDes      = conSatProLinker->getConceptSaturationDescriptor()
    /// conNegation = conDes->getNegation()
    /// concept     = conDes->getConcept()
    /// conceptOpLinkerIt = concept->getOperandList()
    /// addConceptsFilteredToIndividual(conceptOpLinkerIt, conNegation, processIndi, false, mCalcAlgContext)
    /// ```
    pub fn apply_and_rule(
        &mut self,
        process_indi: &mut SatNodeId,
        con_sat_pro_linker: ConceptSaturationProcessLinkerId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // STATINC(ANDRULEAPPLICATIONCOUNT) — profiling stat, elided.
        let con_des = calc_alg_context
            .process_context()
            .con_sat_proc_linker(con_sat_pro_linker)
            .get_concept_saturation_descriptor();
        let con_negation = calc_alg_context
            .process_context()
            .con_sat_desc(con_des)
            .get_negation();
        let concept = calc_alg_context
            .process_context()
            .con_sat_desc(con_des)
            .get_concept();
        // KONCLUDE-PORT-NOTE[ownership]: snapshot the operand-linker list before the
        // `&mut self` add so the terminology-arena read borrow is released first.
        let concept_op_linker: Vec<NegLink<ConceptId>> = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operand_list()
            .to_vec();
        self.add_concepts_filtered_to_individual(
            &concept_op_linker,
            con_negation,
            process_indi,
            calc_alg_context,
        );
    }

    // =======================================================================
    // NONE rule (cpp 5983–5984) — empty body, ported in full.
    // =======================================================================

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::applyNONERule`.
    ///
    /// The C++ body is intentionally empty (a no-op slot for operators that need
    /// no saturation action).
    pub fn apply_none_rule(
        &mut self,
        process_indi: &mut SatNodeId,
        con_sat_pro_linker: ConceptSaturationProcessLinkerId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let _ = (process_indi, con_sat_pro_linker, calc_alg_context);
    }

    // =======================================================================
    // IMPLICATION rule (cpp 5987–5995).
    // =======================================================================

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::applyIMPLICATIONRule`.
    ///
    /// C++ structure:
    /// ```text
    /// STATINC(ANDRULEAPPLICATIONCOUNT)
    /// conDes      = conSatProLinker->getConceptSaturationDescriptor()
    /// CImplicationReapplyConceptSaturationDescriptor tmpNewReapplyImpReapplyConSatDes;   // stack temp
    /// implConcept       = conDes->getConcept()
    /// nextTriggerConcept = implConcept->getOperandList()
    /// tmpNewReapplyImpReapplyConSatDes.initImplicationReapllyConceptSaturationDescriptor(implConcept, nextTriggerConcept)
    /// updateImplicationReapplyConceptSaturationDescriptor(&tmpNewReapplyImpReapplyConSatDes, processIndi,
    ///     processIndi->getReapplyConceptSaturationLabelSet(true), mCalcAlgContext)
    /// ```
    pub fn apply_implication_rule(
        &mut self,
        process_indi: &mut SatNodeId,
        con_sat_pro_linker: ConceptSaturationProcessLinkerId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // STATINC(ANDRULEAPPLICATIONCOUNT) — profiling stat, elided.
        let con_des = calc_alg_context
            .process_context()
            .con_sat_proc_linker(con_sat_pro_linker)
            .get_concept_saturation_descriptor();
        let impl_concept = calc_alg_context
            .process_context()
            .con_sat_desc(con_des)
            .get_concept();
        let next_trigger_concept: Vec<NegLink<ConceptId>> = calc_alg_context
            .ontology_arenas()
            .concept(impl_concept)
            .get_operand_list()
            .to_vec();
        let mut tmp_reapply = ImplicationReapplyConceptSaturationDescriptor::new();
        tmp_reapply.init_implication_reaplly_concept_saturation_descriptor(
            impl_concept,
            Some(&next_trigger_concept),
        );
        let tmp_reapply = calc_alg_context
            .process_context_mut()
            .alloc_imp_reapply_con_sat_desc(tmp_reapply);
        let label_set = calc_alg_context
            .process_context_mut()
            .sat_node_reapply_concept_saturation_label_set(*process_indi, true);
        self.update_implication_reapply_concept_saturation_descriptor(
            tmp_reapply,
            process_indi,
            label_set,
            calc_alg_context,
        );
    }

    // =======================================================================
    // Disjunct-checking helper (cpp 6006–6029) — ported LIVE.
    // =======================================================================

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::getDisjunctCheckingConcept`.
    ///
    /// For a `CCAQCHOOCE` (qualified-choose) operand whose own operand list
    /// contains exactly one same-polarity sub-operand, the rule sees through the
    /// choose wrapper and returns that single sub-operand (with the out-flag
    /// `*checkingNegation = false`); otherwise it returns the operand unchanged.
    /// Pure concept-arena logic, ported in full.
    pub fn get_disjunct_checking_concept(
        &mut self,
        op_concept: ConceptId,
        op_con_negation: bool,
        checking_negation: Option<&mut bool>,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> ConceptId {
        if calc_alg_context
            .ontology_arenas()
            .concept(op_concept)
            .get_operator_code()
            == CCAQCHOOCE
        {
            let mut replace_count: i64 = 0;
            // KONCLUDE-PORT-NOTE[ownership]: C++ `replaceCheckingConcept = nullptr`.
            let mut replace_checking_concept: ConceptId = ConceptId::NONE;
            // KONCLUDE-PORT-NOTE[ownership]: snapshot the operand slice so the read
            // borrow of the terminology arena does not outlive the loop.
            let op_concept_op_linker: Vec<NegLink<ConceptId>> = calc_alg_context
                .ontology_arenas()
                .concept(op_concept)
                .get_operand_list()
                .to_vec();
            for op_op_linker in op_concept_op_linker {
                let op_op_concept = op_op_linker.target; // getData()
                let op_op_negation = op_op_linker.negated; // isNegated()
                if op_op_negation == op_con_negation {
                    replace_checking_concept = op_op_concept;
                    replace_count += 1;
                }
            }

            if replace_count == 1 && replace_checking_concept != ConceptId::NONE {
                if let Some(cn) = checking_negation {
                    *cn = false;
                }
                return replace_checking_concept;
            }
        }
        op_concept
    }

    // =======================================================================
    // OR rule (cpp 6032–6099).
    // =======================================================================

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::applyORRule`.
    ///
    /// The over-approximating disjunction handling: an empty disjunction clashes,
    /// a singleton degenerates to an AND-style add, and a real disjunction marks
    /// the node CRITICAL, records the disjunction in the critical worklist, and —
    /// when the node represents the disjunction concept itself — either seeds the
    /// common-disjunct extraction or wires the dedicated disjunction node up
    /// (copy-dependency linker + already-extracted common-disjunct replay).
    ///
    /// C++ structure:
    /// ```text
    /// conDes = conSatProLinker->getConceptSaturationDescriptor()
    /// conNegation = conDes->getNegation(); concept = conDes->getConcept()
    /// if concept->getOperandCount() == 0:
    ///   updateDirectAddingIndividualStatusFlags(processIndi, INDSATFLAGCLASHED, ...)
    /// elif concept->getOperandCount() == 1:
    ///   STATINC(ANDRULEAPPLICATIONCOUNT)
    ///   addConceptsFilteredToIndividual(concept->getOperandList(), conNegation, processIndi, false, ...)
    /// else:
    ///   updateDirectAddingIndividualStatusFlags(processIndi, INDSATFLAGCRITICAL, ...)
    ///   addCriticalConceptDescriptor(conDes, CCT_DISJUNCTION, processIndi, ...)
    ///   conceptSatItem = processIndi->getSaturationConceptReferenceLinking()
    ///   if conceptSatItem:
    ///     indiConcept = conceptSatItem->getSaturationConcept(); indiConNegation = conceptSatItem->getSaturationNegation()
    ///     if concept == indiConcept && conNegation == indiConNegation:
    ///       initializeExtractDisjunctCommonConcept(processIndi, ...)
    ///     elif indiConcept:
    ///       disjunctionConProData = concept->getConceptData()
    ///       disjConRefLinking = disjunctionConProData->getConceptReferenceLinking()
    ///       if disjConRefLinking:
    ///         disjConceptSatItem = disjConRefLinking->getConceptSaturationReferenceLinkingData(conNegation)
    ///         if disjConceptSatItem:
    ///           disjunctionIndiNode = disjConceptSatItem->getIndividualProcessNodeForConcept()
    ///           separatedMode = processIndi->isSeparated() && !disjunctionIndiNode->isSeparated()
    ///           if !separatedMode: addUninitializedIndividualToProcessingQueue(disjunctionIndiNode, ...)
    ///           taskMemMan = mCalcAlgContext->getUsedProcessTaskMemoryAllocationManager()
    ///           requiresDisjunctionProcessing = true
    ///           copiedIndividualNode = processIndi->getCopyIndividualNode()
    ///           if copiedIndividualNode:
    ///             copiedNodeConSet = copiedIndividualNode->getReapplyConceptSaturationLabelSet(false)
    ///             if copiedNodeConSet->containsConcept(concept, conNegation):
    ///               requiresDisjunctionProcessing = false; ++mDisjunctionInitializedSkippedCount
    ///           if requiresDisjunctionProcessing:
    ///             if !separatedMode:
    ///               depCopyLinker = alloc CXNegLinker<...>(); depCopyLinker->initNegLinker(processIndi, false)
    ///               disjunctionIndiNode->addCopyDependingIndividualNodeLinker(depCopyLinker)
    ///             disjConSet = disjunctionIndiNode->getReapplyConceptSaturationLabelSet(false)
    ///             if disjConSet:
    ///               conSet = processIndi->getReapplyConceptSaturationLabelSet(true)
    ///               for disjConDesIt in disjConSet->getConceptSaturationDescriptionLinker():
    ///                 addConceptToIndividual(disjConDesIt->getConcept(), disjConDesIt->isNegated(), processIndi, conSet, true, ...)
    /// ```
    pub fn apply_or_rule(
        &mut self,
        process_indi: &mut SatNodeId,
        con_sat_pro_linker: ConceptSaturationProcessLinkerId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let con_des = calc_alg_context
            .process_context()
            .con_sat_proc_linker(con_sat_pro_linker)
            .get_concept_saturation_descriptor();
        let con_negation = calc_alg_context
            .process_context()
            .con_sat_desc(con_des)
            .get_negation();
        let concept = calc_alg_context
            .process_context()
            .con_sat_desc(con_des)
            .get_concept();
        let operand_count = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operand_count();
        if operand_count == 0 {
            // Empty disjunction ⇒ clash.
            self.update_direct_adding_individual_status_flags(
                *process_indi,
                IndividualSaturationProcessNodeStatusFlags::INDSATFLAGCLASHED,
                calc_alg_context,
            );
        } else if operand_count == 1 {
            // STATINC(ANDRULEAPPLICATIONCOUNT) — singleton degenerates to AND-add.
            let concept_op_linker: Vec<NegLink<ConceptId>> = calc_alg_context
                .ontology_arenas()
                .concept(concept)
                .get_operand_list()
                .to_vec();
            self.add_concepts_filtered_to_individual(
                &concept_op_linker,
                con_negation,
                process_indi,
                calc_alg_context,
            );
        } else {
            // Real disjunction: mark the node CRITICAL + record it on the critical
            // worklist.
            self.update_direct_adding_individual_status_flags(
                *process_indi,
                IndividualSaturationProcessNodeStatusFlags::INDSATFLAGCRITICAL,
                calc_alg_context,
            );
            self.add_critical_concept_descriptor(
                con_des,
                CCT_DISJUNCTION,
                process_indi,
                calc_alg_context,
            );
            // W4.5-DEFER[api]: the disjunction-node-wiring tail (.cpp 6044–6098) —
            //   conceptSatItem = processIndi->getSaturationConceptReferenceLinking();
            //   conceptSatItem->getSaturationConcept()/getSaturationNegation();
            //   initializeExtractDisjunctCommonConcept(...);
            //   concept->getConceptData()->getConceptReferenceLinking()
            //     ->getConceptSaturationReferenceLinkingData(conNegation)
            //     ->getIndividualProcessNodeForConcept();
            //   addUninitializedIndividualToProcessingQueue(...);
            //   copiedIndividualNode->getReapplyConceptSaturationLabelSet(false)
            //     ->containsConcept(concept, conNegation)  [++mDisjunctionInitializedSkippedCount];
            //   addCopyDependingIndividualNodeLinker(...);
            //   replay disjConSet->getConceptSaturationDescriptionLinker() via addConceptToIndividual.
            //   — needs the `CSaturationConceptDataItem` getSaturationConcept/Negation,
            //   the `CConceptSaturationReferenceLinkingData` chain, the label-set
            //   `containsConcept` deep body (W4.5-DEFER) + create-alloc, and
            //   `initializeExtractDisjunctCommonConcept` (disjunct-common-concept
            //   extraction, opaque). `mDisjunctionInitializedSkippedCount` is present on
            //   `self`. Faithful tail lands with those.
        }
    }

    // =======================================================================
    // ELSE rule (cpp 6102–6105) — ported LIVE (pure sibling delegation).
    // =======================================================================

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::applyELSERule`.
    ///
    /// The catch-all for operators the cheap saturation cannot handle precisely:
    /// flag the node INSUFFICIENT and record that an insufficient node occurred
    /// (so the complete algorithm revisits it).
    pub fn apply_else_rule(
        &mut self,
        process_indi: &mut SatNodeId,
        con_sat_pro_linker: ConceptSaturationProcessLinkerId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let _ = con_sat_pro_linker;
        // W4-DEFER[api]: the `INDSATFLAGINSUFFICIENT` mask + the sibling status/flag
        // helpers land with the saturation status-flag / loop units (group L / B,
        // PU-SAT-11 / PU-SAT-1); the forwarding calls are the whole logic of this rule.
        self.update_direct_adding_individual_status_flags(
            *process_indi,
            IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT,
            calc_alg_context,
        );
        self.set_insufficient_node_occured(calc_alg_context);
    }

    // =======================================================================
    // EQCAND rule (cpp 6145–6148).
    // =======================================================================

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::applyEQCANDRule`.
    ///
    /// C++ structure:
    /// ```text
    /// conDes = conSatProLinker->getConceptSaturationDescriptor()
    /// addCriticalConceptDescriptor(conDes, CCT_EQCANDIDATE, processIndi, mCalcAlgContext)
    /// ```
    pub fn apply_eqcand_rule(
        &mut self,
        process_indi: &mut SatNodeId,
        con_sat_pro_linker: ConceptSaturationProcessLinkerId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let con_des = calc_alg_context
            .process_context()
            .con_sat_proc_linker(con_sat_pro_linker)
            .get_concept_saturation_descriptor();
        self.add_critical_concept_descriptor(
            con_des,
            CCT_EQCANDIDATE,
            process_indi,
            calc_alg_context,
        );
    }

    // =======================================================================
    // BOTTOM rule (cpp 6150–6152) — ported LIVE (pure sibling delegation).
    // =======================================================================

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::applyBOTTOMRule`.
    ///
    /// `⊥` in the label: flag the node CLASHED.
    pub fn apply_bottom_rule(
        &mut self,
        process_indi: &mut SatNodeId,
        con_sat_pro_linker: ConceptSaturationProcessLinkerId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let _ = con_sat_pro_linker;
        // W4-DEFER[api]: the `INDSATFLAGCLASHED` mask + the sibling
        // `updateDirectAddingIndividualStatusFlags` land with the saturation
        // status-flag unit (group L, PU-SAT-11); the call is the whole rule.
        self.update_direct_adding_individual_status_flags(
            *process_indi,
            IndividualSaturationProcessNodeStatusFlags::INDSATFLAGCLASHED,
            calc_alg_context,
        );
    }

    // =======================================================================
    // Automaton transition helpers (cpp 6682–6726) — ported LIVE.
    // =======================================================================

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::addAutomateTransitionOperands`.
    ///
    /// Walks a qualified-`∀` automaton concept: recurse through `CCFS_AQAND_TYPE`
    /// conjuncts, and at a `CCFS_AQALL_TYPE` state whose role matches the
    /// transition role, add each `∀`-operand to the node. Pure concept/role-arena
    /// recursion; the per-operand leaf is the sibling `addConceptFilteredToIndividual`.
    pub fn add_automate_transition_operands(
        &mut self,
        process_indi: &mut SatNodeId,
        automat_concept: ConceptId,
        role: RoleId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let automat_concept_operator = calc_alg_context
            .ontology_arenas()
            .concept(automat_concept)
            .get_concept_operator();
        if automat_concept_operator.has_partial_operator_code_flag(CCFS_AQAND_TYPE) {
            // KONCLUDE-PORT-NOTE[ownership]: snapshot operands before the recursive
            // `&mut` calls so the terminology-arena read borrow is released first.
            let operands: Vec<NegLink<ConceptId>> = calc_alg_context
                .ontology_arenas()
                .concept(automat_concept)
                .get_operand_list()
                .to_vec();
            for op_link in operands {
                let automate_operand_concept = op_link.target;
                self.add_automate_transition_operands(
                    process_indi,
                    automate_operand_concept,
                    role,
                    calc_alg_context,
                );
            }
        } else if automat_concept_operator.has_partial_operator_code_flag(CCFS_AQALL_TYPE) {
            let automate_role = calc_alg_context
                .ontology_arenas()
                .concept(automat_concept)
                .get_role();
            if automate_role == role {
                let operands: Vec<NegLink<ConceptId>> = calc_alg_context
                    .ontology_arenas()
                    .concept(automat_concept)
                    .get_operand_list()
                    .to_vec();
                for op_link in operands {
                    let automate_operand_concept = op_link.target;
                    let automate_operand_concept_negation = op_link.negated;
                    // W4-DEFER[api]: addConceptFilteredToIndividual (4-arg overload) is a
                    // sibling (group K, PU-SAT-11); overload-name reconcile pending.
                    self.add_concept_filtered_to_individual(
                        automate_operand_concept,
                        automate_operand_concept_negation,
                        process_indi,
                        calc_alg_context,
                    );
                }
            }
        }
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::testAutomateTransitionOperandsAddable`.
    ///
    /// The pre-test twin of `addAutomateTransitionOperands`: returns whether any
    /// `∀`-operand of the matching automaton state is still missing from the
    /// node's saturation label.
    ///
    /// C++ structure:
    /// ```text
    /// if operator has CCFS_AQAND_TYPE:
    ///   for op in automatConcept->getOperandList():
    ///     if testAutomateTransitionOperandsAddable(processIndi, op, role, ...): return true
    /// elif operator has CCFS_AQALL_TYPE:
    ///   if automatConcept->getRole() == role:
    ///     conSet = processIndi->getReapplyConceptSaturationLabelSet(false)
    ///     for op in automatConcept->getOperandList() (opNeg = op->isNegated()):
    ///       if !conSet->containsConcept(op, opNeg): return true
    /// return false
    /// ```
    pub fn test_automate_transition_operands_addable(
        &mut self,
        process_indi: &mut SatNodeId,
        automat_concept: ConceptId,
        role: RoleId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let automat_concept_operator = calc_alg_context
            .ontology_arenas()
            .concept(automat_concept)
            .get_concept_operator();
        if automat_concept_operator.has_partial_operator_code_flag(CCFS_AQAND_TYPE) {
            let operands: Vec<NegLink<ConceptId>> = calc_alg_context
                .ontology_arenas()
                .concept(automat_concept)
                .get_operand_list()
                .to_vec();
            for op_link in operands {
                if self.test_automate_transition_operands_addable(
                    process_indi,
                    op_link.target,
                    role,
                    calc_alg_context,
                ) {
                    return true;
                }
            }
        } else if automat_concept_operator.has_partial_operator_code_flag(CCFS_AQALL_TYPE) {
            let automate_role = calc_alg_context
                .ontology_arenas()
                .concept(automat_concept)
                .get_role();
            if automate_role == role {
                let label_set = calc_alg_context
                    .process_context_mut()
                    .sat_node_reapply_concept_saturation_label_set(*process_indi, false);
                let operands: Vec<NegLink<ConceptId>> = calc_alg_context
                    .ontology_arenas()
                    .concept(automat_concept)
                    .get_operand_list()
                    .to_vec();
                for op_link in operands {
                    let operand_tag = calc_alg_context
                        .ontology_arenas()
                        .concept(op_link.target)
                        .get_concept_tag();
                    let mut con_sat_des = ConceptSaturationDescriptorId::NONE;
                    let mut imp_reapply_con_sat_des =
                        ImplicationReapplyConceptSaturationDescriptorId::NONE;
                    let contained = label_set.is_some()
                        && calc_alg_context
                            .process_context()
                            .reapply_con_sat_label_set(label_set)
                            .get_concept_saturation_descriptor_by_tag(
                                operand_tag,
                                &mut con_sat_des,
                                &mut imp_reapply_con_sat_des,
                            )
                        && con_sat_des.is_some()
                        && calc_alg_context
                            .process_context()
                            .con_sat_desc(con_sat_des)
                            .get_negation()
                            == op_link.negated;
                    if !contained {
                        return true;
                    }
                }
            }
        }
        false
    }

    // =======================================================================
    // SELF rule (cpp 6856–6905).
    // =======================================================================

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::applySELFRule`.
    ///
    /// A `∃R.Self` adds, for every indirect super-role, the role's domain and
    /// range concepts to the node and installs a self-connected backward-propagation
    /// link (replaying any newly applicable backward-propagation concepts).
    ///
    /// C++ structure:
    /// ```text
    /// STATINC(SELFRULEAPPLICATIONCOUNT)
    /// conDes = conSatProLinker->getConceptSaturationDescriptor()
    /// conNegation = conDes->getNegation(); concept = conDes->getConcept(); role = concept->getRole()
    /// taskMemMan = nullptr; backPropHash = nullptr; conSet = nullptr
    /// for superRoleIt in role->getIndirectSuperRoleList():
    ///   superRole = superRoleIt->getData()
    ///   for domainConLinkerIt in superRole->getDomainRangeConceptList(superRoleIt->isNegated()):
    ///     if !conSet: conSet = processIndi->getReapplyConceptSaturationLabelSet(true)
    ///     addConceptFilteredToIndividual(domainConcept, domainConceptNegation, processIndi, conSet, false, ...)
    ///   for rangeConLinkerIt in superRole->getDomainRangeConceptList(!superRoleIt->isNegated()):
    ///     if !conSet: conSet = processIndi->getReapplyConceptSaturationLabelSet(true)
    ///     addConceptFilteredToIndividual(rangeConcept, rangeConceptNegation, processIndi, conSet, false, ...)
    ///   if !taskMemMan: taskMemMan = mCalcAlgContext->getUsedProcessTaskMemoryAllocationManager()
    ///   backPropLink = alloc CBackwardSaturationPropagationLink(); backPropLink->initBackwardPropagationLink(processIndi, superRole)
    ///   if !backPropHash: backPropHash = processIndi->getRoleBackwardPropagationHash(true)
    ///   backPropReapplyDes = backPropHash->addSelfConnectedBackwardPropagationLink(superRole, backPropLink)
    ///   if backPropReapplyDes: applyBackwardPropagationConcepts(processIndi, backPropReapplyDes, mCalcAlgContext)
    /// ```
    pub fn apply_self_rule(
        &mut self,
        process_indi: &mut SatNodeId,
        con_sat_pro_linker: ConceptSaturationProcessLinkerId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // PORT-PENDING: see structural transcription above. The role->getIndirectSuperRoleList
        // / getDomainRangeConceptList iteration is pure role-arena logic, but the body
        // is interleaved with the node's saturation satellites and a sibling:
        // W4-DEFER[api]: conDes read (SAT-1); `getReapplyConceptSaturationLabelSet(true)`,
        //   `getRoleBackwardPropagationHash(true)` lazy getters; the
        //   `CBackwardSaturationPropagationLink` allocation +
        //   `initBackwardPropagationLink`; `CRoleBackwardSaturationPropagationHash::
        //   addSelfConnectedBackwardPropagationLink`; the `addConceptFilteredToIndividual`
        //   (6-arg label-set overload) sibling (PU-SAT-11) and the
        //   `applyBackwardPropagationConcepts` sibling (PU-SAT-6/7).
        let _ = (process_indi, con_sat_pro_linker, calc_alg_context);
        todo!("W4-DEFER: applySELFRule — gated by unported saturation backward-propagation satellites");
    }

    // =======================================================================
    // SOME rule (cpp 6925–6928) — ported LIVE (pure sibling delegation).
    // =======================================================================

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::applySOMERule`.
    ///
    /// An existential restriction creates exactly one successor (cardinality 1)
    /// for the concept — the whole body forwards to `createSuccessorForConcept`.
    pub fn apply_some_rule(
        &mut self,
        process_indi: &mut SatNodeId,
        con_sat_pro_linker: ConceptSaturationProcessLinkerId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W4-DEFER[api]: STATINC(SOMERULEAPPLICATIONCOUNT) — profiling stat, no-op port.
        // `createSuccessorForConcept` is a sibling (group C, PU-SAT-2); the call is
        // the whole rule.
        self.create_successor_for_concept(process_indi, con_sat_pro_linker, 1, calc_alg_context);
    }
}

#[cfg(test)]
mod tests {
    use super::super::super::model::concept::Concept;
    use super::super::super::model::op::CCATOM;
    use super::super::super::model::role::Role;
    use super::super::super::model::Id;
    use super::super::super::process::sat_node::IndividualSaturationProcessNode;
    use super::super::algorithm::SaturationTaskHandleAlgorithm;
    use super::super::satellites::{ConceptSaturationDescriptor, ConceptSaturationProcessLinker};
    use super::*;

    fn concept_process_linker(
        ctx: &mut CalculationAlgorithmContextBase,
        concept: ConceptId,
        negated: bool,
    ) -> ConceptSaturationProcessLinkerId {
        let mut descriptor = ConceptSaturationDescriptor::new();
        descriptor.init_concept_saturation_descriptor(concept, negated);
        let descriptor = ctx.process_context_mut().alloc_con_sat_desc(descriptor);
        let mut linker = ConceptSaturationProcessLinker::new();
        linker.init_concept_saturation_process_linker(descriptor);
        ctx.process_context_mut().alloc_con_sat_proc_linker(linker)
    }

    fn role(ctx: &mut CalculationAlgorithmContextBase, tag: Cint64) -> RoleId {
        let mut role = Role::new();
        role.set_role_tag(tag);
        ctx.ontology_arenas_mut().alloc_role(role)
    }

    #[test]
    fn s03_apply_implication_rule_executes_single_operand() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();

        let conclusion = {
            let mut concept = Concept::new();
            concept.set_operator_code(CCATOM).set_concept_tag(301);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };
        let implication = {
            let mut concept = Concept::new();
            concept
                .set_operator_code(CCATOM)
                .set_concept_tag(303)
                .add_operand_linker(conclusion, false)
                .set_operand_count(1);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };
        let mut node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let linker = concept_process_linker(&mut ctx, implication, false);

        algo.apply_implication_rule(&mut node, linker, &mut ctx);

        let label_set = ctx
            .process_context_mut()
            .sat_node_reapply_concept_saturation_label_set(node, false);
        let conclusion_tag = ctx.ontology_arenas().concept(conclusion).get_concept_tag();
        let mut conclusion_descriptor = Id::NONE;
        let mut imp_reapply = Id::NONE;
        assert!(ctx
            .process_context()
            .reapply_con_sat_label_set(label_set)
            .get_concept_saturation_descriptor_by_tag(
                conclusion_tag,
                &mut conclusion_descriptor,
                &mut imp_reapply,
            ));
        assert!(conclusion_descriptor.is_some());
    }

    #[test]
    fn s03_apply_implication_rule_queues_next_trigger() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();

        let conclusion = {
            let mut concept = Concept::new();
            concept.set_operator_code(CCATOM).set_concept_tag(311);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };
        let trigger = {
            let mut concept = Concept::new();
            concept.set_operator_code(CCATOM).set_concept_tag(313);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };
        let implication = {
            let mut concept = Concept::new();
            concept
                .set_operator_code(CCATOM)
                .set_concept_tag(315)
                .add_operand_linker(conclusion, false)
                .add_operand_linker(trigger, false)
                .set_operand_count(2);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };
        let mut node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let linker = concept_process_linker(&mut ctx, implication, false);

        algo.apply_implication_rule(&mut node, linker, &mut ctx);

        let label_set = ctx
            .process_context_mut()
            .sat_node_reapply_concept_saturation_label_set(node, false);
        let trigger_tag = ctx.ontology_arenas().concept(trigger).get_concept_tag();
        let trigger_data = ctx
            .process_context()
            .reapply_con_sat_label_set(label_set)
            .concept_des_dep_hash
            .get(&trigger_tag)
            .copied()
            .expect("trigger tag should receive an implication reapply entry");
        assert!(trigger_data.con_sat_des.is_none());
        assert!(trigger_data.imp_reapply_con_sat_des.is_some());
    }

    #[test]
    fn s03_tableau_dispatch_positive_bottom_flags_clash() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();

        let bottom = {
            let mut concept = Concept::new();
            concept.set_operator_code(CCBOTTOM).set_concept_tag(321);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };
        let mut node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let linker = concept_process_linker(&mut ctx, bottom, false);

        algo.apply_tableau_saturation_rule(&mut node, linker, &mut ctx);

        assert!(ctx
            .process_context()
            .sat_node(node)
            .direct_status_flags
            .has_clashed_flag());
    }

    #[test]
    fn s03_tableau_dispatch_unknown_operator_uses_else_rule() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();

        let unknown = {
            let mut concept = Concept::new();
            concept.set_operator_code(999).set_concept_tag(323);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };
        let mut node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let linker = concept_process_linker(&mut ctx, unknown, false);

        algo.apply_tableau_saturation_rule(&mut node, linker, &mut ctx);

        assert!(ctx
            .process_context()
            .sat_node(node)
            .direct_status_flags
            .has_insufficient_flag());
        assert!(ctx.processing_data_box().is_insufficient_node_occured());
    }

    #[test]
    fn s03_tableau_dispatch_positive_implication_executes_rule() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();

        let conclusion = {
            let mut concept = Concept::new();
            concept.set_operator_code(CCATOM).set_concept_tag(331);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };
        let implication = {
            let mut concept = Concept::new();
            concept
                .set_operator_code(CCIMPL)
                .set_concept_tag(333)
                .add_operand_linker(conclusion, false)
                .set_operand_count(1);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };
        let mut node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let linker = concept_process_linker(&mut ctx, implication, false);

        algo.apply_tableau_saturation_rule(&mut node, linker, &mut ctx);

        let label_set = ctx
            .process_context_mut()
            .sat_node_reapply_concept_saturation_label_set(node, false);
        let conclusion_tag = ctx.ontology_arenas().concept(conclusion).get_concept_tag();
        let mut conclusion_descriptor = Id::NONE;
        let mut imp_reapply = Id::NONE;
        assert!(ctx
            .process_context()
            .reapply_con_sat_label_set(label_set)
            .get_concept_saturation_descriptor_by_tag(
                conclusion_tag,
                &mut conclusion_descriptor,
                &mut imp_reapply,
            ));
        assert!(conclusion_descriptor.is_some());
    }

    #[test]
    fn s03_test_automate_transition_operands_addable_missing_aqall_operand() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();

        let role = role(&mut ctx, 401);
        let operand = {
            let mut concept = Concept::new();
            concept.set_operator_code(CCATOM).set_concept_tag(403);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };
        let aqall = {
            let mut concept = Concept::new();
            concept
                .set_operator_code(CCAQALL)
                .set_concept_tag(405)
                .set_role(role)
                .add_operand_linker(operand, false)
                .set_operand_count(1);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };
        let mut node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());

        assert!(algo.test_automate_transition_operands_addable(&mut node, aqall, role, &mut ctx));
    }

    #[test]
    fn s03_test_automate_transition_operands_addable_existing_operand_not_addable() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();

        let role = role(&mut ctx, 411);
        let operand = {
            let mut concept = Concept::new();
            concept.set_operator_code(CCATOM).set_concept_tag(413);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };
        let aqall = {
            let mut concept = Concept::new();
            concept
                .set_operator_code(CCAQALL)
                .set_concept_tag(415)
                .set_role(role)
                .add_operand_linker(operand, true)
                .set_operand_count(1);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };
        let mut node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        ctx.process_context_mut()
            .sat_node_reapply_concept_saturation_label_set(node, true);
        algo.add_concept_filtered_to_individual(operand, true, &mut node, &mut ctx);

        assert!(!algo.test_automate_transition_operands_addable(&mut node, aqall, role, &mut ctx));
    }

    #[test]
    fn s03_test_automate_transition_operands_addable_role_mismatch_is_false() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();

        let transition_role = role(&mut ctx, 421);
        let other_role = role(&mut ctx, 423);
        let operand = {
            let mut concept = Concept::new();
            concept.set_operator_code(CCATOM).set_concept_tag(425);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };
        let aqall = {
            let mut concept = Concept::new();
            concept
                .set_operator_code(CCAQALL)
                .set_concept_tag(427)
                .set_role(other_role)
                .add_operand_linker(operand, false)
                .set_operand_count(1);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };
        let mut node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());

        assert!(!algo.test_automate_transition_operands_addable(
            &mut node,
            aqall,
            transition_role,
            &mut ctx
        ));
    }

    #[test]
    fn s03_test_automate_transition_operands_addable_recurses_through_aqand() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();

        let role = role(&mut ctx, 431);
        let operand = {
            let mut concept = Concept::new();
            concept.set_operator_code(CCATOM).set_concept_tag(433);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };
        let aqall = {
            let mut concept = Concept::new();
            concept
                .set_operator_code(CCAQALL)
                .set_concept_tag(435)
                .set_role(role)
                .add_operand_linker(operand, false)
                .set_operand_count(1);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };
        let aqand = {
            let mut concept = Concept::new();
            concept
                .set_operator_code(CCAQAND)
                .set_concept_tag(437)
                .add_operand_linker(aqall, false)
                .set_operand_count(1);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };
        let mut node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());

        assert!(algo.test_automate_transition_operands_addable(&mut node, aqand, role, &mut ctx));
    }
}
