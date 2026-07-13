//! `saturation::s04` — Saturation tableau-rule family, batch 2 (port unit #4 of 12).
//!
//! Faithful port of port-unit **PU-SAT-4** of Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauApproximationSaturationTaskHandleAlgorithm.cpp`
//! (manifest `03-saturation-calc.md`, unit #4 — "ALL + ATMOST/ATLEAST rules +
//! VALUE/NOMINAL rules"):
//!
//!   * `applyATMOSTRule`  (cpp 6108–6129),
//!   * `applyATLEASTRule` (cpp 6132–6143),
//!   * `applyALLRule`     (cpp 6154–6204),
//!   * `applyVALUERule`   (cpp 6474–6671),
//!   * `applyNOMINALRule` (cpp 6731–6843).
//!
//! These five are the cardinality / universal-restriction / nominal saturation
//! expansion rules of the cheap non-branching pre-pass. (`applyEQCANDRule`,
//! `applyBOTTOMRule`, the `add*ConceptExtensionProcessingRole` helpers and
//! `delayNominalSaturationConceptProcessing` interleave in the same cpp line
//! range but belong to units #3 / #6 / #7 / #11 and are NOT ported here.)
//!
//! ## Context convention
//!
//! KONCLUDE-PORT-NOTE[api]: per the saturation header
//! (`CCalculationTableauApproximationSaturationTaskHandleAlgorithm.h` lines
//! 168–175) the `apply*Rule` methods take ONLY
//! `CIndividualSaturationProcessNode*& processIndi, CConceptSaturationProcessLinker* conProLinker`
//! and reach the shared per-thread context through the algorithm MEMBER
//! `mCalcAlgContext` (a `CCalculationAlgorithmContextBase*`; see cpp uses at
//! 6109/6116/6118/…). The port stores that member as an opaque `Cint64`
//! (`algorithm.rs::calc_alg_context`), so — matching the W3 completion-rule
//! convention (`completion/u05.rs` …) — the shared context is THREADED as an
//! explicit `calc_alg_context: &mut CalculationAlgorithmContextBase` parameter
//! instead of read from the field. The C++ `CIndividualSaturationProcessNode*&`
//! out/in-out pointer-reference becomes `&mut SatNodeId` (an arena id), and
//! `CConceptSaturationProcessLinker*` becomes `ConceptSaturationProcessLinkerId`.
//!
//! ## Remaining PORT-PENDING bodies
//!
//! KONCLUDE-PORT-NOTE[api]: the saturation descriptor chain
//! `conSatProLinker->getConceptSaturationDescriptor()->getNegation()/getConcept()`
//! is now live. The small cardinality rules are ported below; the remaining bodies
//! bottom out in three further not-yet-ported facilities:
//!   1. the saturation node accessors deferred to process unit **SAT-1**
//!      (`getRoleBackwardPropagationHash`, `getDirectStatusFlags`,
//!      `getReapplyConceptSaturationLabelSet`, `getNominalIndividual`,
//!      `getMultipleCardinalityAncestorNodesLinker`, `hasNominalIntegrated` /
//!      `setIntegratedNominal`, `getNominalHandlingData`);
//!   2. the saturation status-flag masks
//!      (`CIndividualSaturationProcessNodeStatusFlags::INDSATFLAG*`) and the
//!      critical-queue tags (`CCriticalSaturationConceptTypeQueues::CCT_*`), which
//!      land with the saturation status-flag unit;
//!   3. the SIBLING saturation-algorithm methods in OTHER PU-SAT units
//!      (`updateDirectAddingIndividualStatusFlags`, `updateMaxCardinalityCandidates`,
//!      `updateAddingSuccessorConnectedNominal`, `addCriticalConceptDescriptor`,
//!      `addFUNCTIONALConceptExtensionProcessingRole`,
//!      `addQualifiedFUNCTIONALAtmostConceptExtensionProcessing`,
//!      `addALLConceptExtensionProcessingRole`, `createSuccessorForConcept`,
//!      `addConceptFilteredToIndividual`, `addAutomateTransitionOperands`,
//!      `isConsistenceDataAvailable`, `getCorrectedNode`, `addInfluencedNominal`,
//!      `setInsufficientNodeOccured`, `addNominalDependentIndividualNode`,
//!      `delayNominalSaturationConceptProcessing`), plus the backend-association
//!      cache handler (`mBackendAssCaceHandler`, `W6-DEFER[api]`).
//!
//! Following the established porting convention (`completion/u05.rs`): the faithful
//! Rust signatures are written here, and each body is recorded as a `// PORT-PENDING`
//! line-by-line structural transcription of the C++ so the next wave fills it in
//! without re-reading the source. Logic is documented in full, never dropped.

#![allow(dead_code)]
#![allow(unused_variables)]

use super::super::completion::context::CalculationAlgorithmContextBase;
use super::super::model::concept_process::ConceptProcessDataId;
use super::super::model::op::{CCATLEAST, CCATMOST, CCATOM};
use super::super::model::substrate::Cint64;
use super::super::model::RoleId;
use super::super::model::{ConceptId, NegLink};
use super::super::process::sat_node::IndividualSaturationProcessNodeStatusFlags;
use super::super::process::stubs::ConceptSaturationProcessLinkerId;
use super::super::process::SatNodeId;
use super::satellites::ConceptSaturationDescriptorId;

// `CCriticalConceptType` enum tags used by `addCriticalConceptDescriptor`.
// File-local mirror of the (file-private) copies in `s08.rs` / `s09.rs`.
const CCT_FORALL: Cint64 = 0;
const CCT_ATMOST: Cint64 = 1;

impl super::algorithm::SaturationTaskHandleAlgorithm {
    // =======================================================================
    // applyATMOSTRule (cpp 6108–6129).
    // =======================================================================

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::applyATMOSTRule`.
    ///
    /// Live port. Uses the descriptor chain, concept role/parameter/operands,
    /// status-flag masks, and the siblings `updateMaxCardinalityCandidates` /
    /// `updateDirectAddingIndividualStatusFlags` /
    /// `addFUNCTIONALConceptExtensionProcessingRole` /
    /// `addQualifiedFUNCTIONALAtmostConceptExtensionProcessing` /
    /// `addCriticalConceptDescriptor`.
    ///
    /// C++ structure:
    /// ```text
    /// STATINC(ATMOSTRULEAPPLICATIONCOUNT, mCalcAlgContext)
    /// conDes      = conSatProLinker->getConceptSaturationDescriptor()
    /// conNegation = conDes->getNegation()
    /// concept     = conDes->getConcept()
    /// role        = concept->getRole()
    /// cardinality = concept->getParameter() - 1*conNegation
    /// if cardinality < 0:
    ///     updateDirectAddingIndividualStatusFlags(processIndi, INDSATFLAGCLASHED)
    /// else:
    ///     updateMaxCardinalityCandidates(processIndi, 0, cardinality)
    ///     updateDirectAddingIndividualStatusFlags(processIndi, INDSATFLAGCARDINALITYRESTRICTED)
    ///     if cardinality == 1:
    ///         if !concept->getOperandList():
    ///             addFUNCTIONALConceptExtensionProcessingRole(role, processIndi)
    ///         else:
    ///             addQualifiedFUNCTIONALAtmostConceptExtensionProcessing(conDes, processIndi)
    ///     addCriticalConceptDescriptor(conDes, CCT_ATMOST, processIndi)
    /// ```
    pub fn apply_atmost_rule(
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
        let (role, cardinality, has_operands): (RoleId, Cint64, bool) = {
            let concept_ref = calc_alg_context.ontology_arenas().concept(concept);
            (
                concept_ref.get_role(),
                concept_ref.get_parameter() - Cint64::from(con_negation),
                !concept_ref.get_operand_list().is_empty(),
            )
        };

        if cardinality < 0 {
            if super::sat_clash_trace_enabled() {
                let indi = calc_alg_context
                    .process_context()
                    .sat_node(*process_indi)
                    .get_individual_id();
                eprintln!(
                    "SAT-CLASH s04-neg-card node={:?} indi={} concept={:?}",
                    process_indi, indi, concept
                );
            }
            self.update_direct_adding_individual_status_flags(
                *process_indi,
                IndividualSaturationProcessNodeStatusFlags::INDSATFLAGCLASHED,
                calc_alg_context,
            );
        } else {
            self.update_max_cardinality_candidates(*process_indi, 0, cardinality, calc_alg_context);
            self.update_direct_adding_individual_status_flags(
                *process_indi,
                IndividualSaturationProcessNodeStatusFlags::INDSATFLAGCARDINALITYRESTRICTED,
                calc_alg_context,
            );
            if cardinality == 1 {
                if !has_operands {
                    self.add_functional_concept_extension_processing_role(
                        role,
                        process_indi,
                        calc_alg_context,
                    );
                } else {
                    self.add_qualified_functional_atmost_concept_extension_processing(
                        con_des,
                        process_indi,
                        calc_alg_context,
                    );
                }
            }
            self.add_critical_concept_descriptor(
                con_des,
                CCT_ATMOST,
                process_indi,
                calc_alg_context,
            );
        }
    }

    // =======================================================================
    // applyATLEASTRule (cpp 6132–6143).
    // =======================================================================

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::applyATLEASTRule`.
    ///
    /// Live port. Uses the descriptor chain and the siblings
    /// `updateMaxCardinalityCandidates` / `createSuccessorForConcept`.
    ///
    /// C++ structure:
    /// ```text
    /// STATINC(ATLEASTRULEAPPLICATIONCOUNT, mCalcAlgContext)
    /// conDes      = conSatProLinker->getConceptSaturationDescriptor()
    /// conNegation = conDes->getNegation()
    /// concept     = conDes->getConcept()
    /// role        = concept->getRole()                     // bound but unused below
    /// cardinality = concept->getParameter() + 1*conNegation
    /// if cardinality > 0:
    ///     updateMaxCardinalityCandidates(processIndi, cardinality, 0)
    ///     createSuccessorForConcept(processIndi, conSatProLinker, cardinality)
    /// ```
    pub fn apply_atleast_rule(
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
        let _role = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_role();
        let cardinality = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_parameter()
            + Cint64::from(con_negation);

        if cardinality > 0 {
            self.update_max_cardinality_candidates(*process_indi, cardinality, 0, calc_alg_context);
            self.create_successor_for_concept(
                process_indi,
                con_sat_pro_linker,
                cardinality,
                calc_alg_context,
            );
        }
    }

    // =======================================================================
    // applyALLRule (cpp 6154–6204).
    // =======================================================================

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::applyALLRule`.
    ///
    /// The universal-restriction saturation rule: registers a backward-propagation
    /// reapply descriptor for `role`, replays the `∀` operands onto every already
    /// backward-linked source node, then either queues forward ALL-concept
    /// extension processing or flags the node for an unregistered-propagation
    /// end-check.
    ///
    /// Live port (task #23 saturation-first). The one remaining seam:
    /// `CRoleProcessData::hasPropagationAndCreationConceptsFlag` is unported — the
    /// bridge never allocates role data, so the C++ `!roleProData` arm applies and
    /// the node is marked for the unregistered-propagation end check (see the
    /// KONCLUDE-PORT-NOTE in the body).
    ///
    /// C++ structure:
    /// ```text
    /// STATINC(ALLRULEAPPLICATIONCOUNT, mCalcAlgContext); g_ksat_allRule++
    /// conDes      = conSatProLinker->getConceptSaturationDescriptor()
    /// conNegation = conDes->getNegation()
    /// concept     = conDes->getConcept()
    /// role        = concept->getRole()
    ///
    /// taskMemMan          = mCalcAlgContext->getUsedProcessTaskMemoryAllocationManager()
    /// backPropHash        = processIndi->getRoleBackwardPropagationHash(true)
    /// backPropReapplyDes  = alloc CBackwardSaturationPropagationReapplyDescriptor(taskMemMan)
    /// backPropReapplyDes->initBackwardPropagationReapplyDescriptor(conDes)
    /// backPropHashData    = backPropHash->addBackwardPropagationConceptDescriptor(role, backPropReapplyDes)
    /// backPropLinkIt      = backPropHashData.mLinkLinker
    ///
    /// if backPropLinkIt:
    ///     while backPropLinkIt:
    ///         backPropIndiNode = backPropLinkIt->getSourceIndividual()
    ///         conceptOpLinkerIt = concept->getOperandList()
    ///         while conceptOpLinkerIt:
    ///             opConcept    = conceptOpLinkerIt->getData()
    ///             opConNegation = conceptOpLinkerIt->isNegated() ^ conNegation
    ///             STATINC(ALLROLERESTRICTIONCOUNT); g_ksat_allBackProp++
    ///             addConceptFilteredToIndividual(opConcept, opConNegation, backPropIndiNode, true)
    ///             conceptOpLinkerIt = conceptOpLinkerIt->getNext()
    ///         backPropLinkIt = backPropLinkIt->getNext()
    ///
    /// conProData = (CConceptProcessData*)concept->getConceptData()
    /// if role->isDataRole() || conProData:
    ///     if role->isDataRole() || conProData->hasPropagationIntoCreationDirection():
    ///         addALLConceptExtensionProcessingRole(role, backPropHashData, processIndi)
    ///         updateDirectAddingIndividualStatusFlags(processIndi, INDSATFLAGCRITICAL)
    ///         addCriticalConceptDescriptor(conDes, CCT_FORALL, processIndi)
    ///     else:
    ///         roleProData = (CRoleProcessData*)role->getRoleData()
    ///         if !roleProData || roleProData->hasPropagationAndCreationConceptsFlag():
    ///             updateDirectAddingIndividualStatusFlags(processIndi, INDSATFLAGUNREGISTEREDPROPAGATION)
    /// ```
    pub fn apply_all_rule(
        &mut self,
        process_indi: &mut SatNodeId,
        con_sat_pro_linker: ConceptSaturationProcessLinkerId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // STATINC(ALLRULEAPPLICATIONCOUNT) — profiling stat, elided.
        if self.diagnostic_counters_enabled {
            self.diagnostic_all_rule_count += 1;
        }
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
        let role = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_role();

        // backPropHash = processIndi->getRoleBackwardPropagationHash(true);
        // backPropReapplyDes = alloc; initBackwardPropagationReapplyDescriptor(conDes);
        // backPropHashData = backPropHash->addBackwardPropagationConceptDescriptor(role, backPropReapplyDes);
        //   (CRoleBackwardSaturationPropagationHash cpp 96–100: prepend the reapply
        //   descriptor onto the role's mReapplyLinker chain.)
        let back_prop_hash = calc_alg_context
            .process_context_mut()
            .sat_node_role_backward_propagation_hash(*process_indi, true);
        let back_prop_link_it = {
            let old_reapply = calc_alg_context
                .process_context()
                .role_backward_sat_prop_hash(back_prop_hash)
                .role_back_prop_data_hash
                .get(&role)
                .map(|data| data.reapply_linker)
                .unwrap_or(
                    super::satellites::BackwardSaturationPropagationReapplyDescriptorId::NONE,
                );
            let mut reapply_des =
                super::satellites::BackwardSaturationPropagationReapplyDescriptor::new();
            reapply_des.init_backward_propagation_reapply_descriptor(con_des);
            reapply_des.set_next(old_reapply);
            let reapply_des = calc_alg_context
                .process_context_mut()
                .alloc_backward_sat_prop_reapply_desc(reapply_des);
            let data = calc_alg_context
                .process_context_mut()
                .role_backward_sat_prop_hash_mut(back_prop_hash)
                .role_back_prop_data_hash
                .entry(role)
                .or_insert_with(super::satellites::RoleBackwardSaturationPropagationHashData::new);
            data.reapply_linker = reapply_des;
            data.link_linker
        };

        // Replay the ∀-operands onto every already backward-linked source node.
        if back_prop_link_it.is_some() {
            let operands: Vec<NegLink<ConceptId>> = calc_alg_context
                .ontology_arenas()
                .concept(concept)
                .get_operand_list()
                .to_vec();
            let mut link_it = back_prop_link_it;
            while link_it.is_some() {
                let mut back_prop_indi_node = calc_alg_context
                    .process_context()
                    .backward_sat_prop_link(link_it)
                    .get_source_individual();
                for op_link in &operands {
                    let op_concept = op_link.target; // getData()
                    let op_con_negation = op_link.negated ^ con_negation; // isNegated()^conNegation
                                                                          // STATINC(ALLROLERESTRICTIONCOUNT) — elided.
                    if self.diagnostic_counters_enabled {
                        self.diagnostic_all_back_prop_count += 1;
                    }
                    self.add_concept_filtered_to_individual_update_copy(
                        op_concept,
                        op_con_negation,
                        &mut back_prop_indi_node,
                        true,
                        calc_alg_context,
                    );
                }
                link_it = calc_alg_context
                    .process_context()
                    .backward_sat_prop_link(link_it)
                    .get_next();
            }
        }

        // conProData = (CConceptProcessData*)concept->getConceptData();
        // if (role->isDataRole() || conProData) { … }
        let is_data_role = calc_alg_context.ontology_arenas().role(role).is_data_role();
        let con_proc_data_id = {
            let c = calc_alg_context.ontology_arenas().concept(concept);
            if c.has_concept_data() {
                ConceptProcessDataId::new(c.get_concept_data())
            } else {
                ConceptProcessDataId::NONE
            }
        };
        if is_data_role || con_proc_data_id.is_some() {
            let propagation_into_creation_direction = con_proc_data_id.is_some()
                && calc_alg_context
                    .ontology_arenas()
                    .concept_process_data(con_proc_data_id)
                    .propagation_into_creation_direction;
            if is_data_role || propagation_into_creation_direction {
                // addALLConceptExtensionProcessingRole(role, backPropHashData, processIndi);
                // KONCLUDE-PORT-NOTE[ownership]: the C++ passes the hash-map entry by
                // reference; the port clones it out, calls the sibling (which mutates
                // only the queued flag on the entry plus node/queue state through the
                // context), and writes the entry back. Nothing else touches this
                // role's entry during the call.
                let mut data = calc_alg_context
                    .process_context()
                    .role_backward_sat_prop_hash(back_prop_hash)
                    .role_back_prop_data_hash
                    .get(&role)
                    .cloned()
                    .unwrap_or_else(
                        super::satellites::RoleBackwardSaturationPropagationHashData::new,
                    );
                self.add_all_concept_extension_processing_role(
                    role,
                    &mut data,
                    process_indi,
                    calc_alg_context,
                );
                calc_alg_context
                    .process_context_mut()
                    .role_backward_sat_prop_hash_mut(back_prop_hash)
                    .role_back_prop_data_hash
                    .insert(role, data);
                self.update_direct_adding_individual_status_flags(
                    *process_indi,
                    IndividualSaturationProcessNodeStatusFlags::INDSATFLAGCRITICAL,
                    calc_alg_context,
                );
                self.add_critical_concept_descriptor(
                    con_des,
                    CCT_FORALL,
                    process_indi,
                    calc_alg_context,
                );
            } else {
                // roleProData = (CRoleProcessData*)role->getRoleData();
                // if (!roleProData || roleProData->hasPropagationAndCreationConceptsFlag())
                // KONCLUDE-PORT-NOTE[api]: CRoleProcessData is unported and the bridge
                // never allocates role data, so the C++ `!roleProData` arm applies —
                // mark the node for the unregistered-propagation end check exactly as
                // Konclude does for data-less roles.
                let role_data_missing = calc_alg_context
                    .ontology_arenas()
                    .role(role)
                    .get_role_data()
                    .is_none();
                if role_data_missing {
                    self.update_direct_adding_individual_status_flags(
                        *process_indi,
                        IndividualSaturationProcessNodeStatusFlags::INDSATFLAGUNREGISTEREDPROPAGATION,
                        calc_alg_context,
                    );
                }
            }
        }
    }

    // =======================================================================
    // applyVALUERule (cpp 6474–6671).
    // =======================================================================

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::applyVALUERule`.
    ///
    /// The nominal-value (`∃role.{a}` / `role value a`) saturation rule. With
    /// nominal processing enabled it connects the node to the nominal, then —
    /// depending on whether consistence (cached completion-graph) data is
    /// available — either (A) replays the cached nominal node's role
    /// domain/range/reapply concepts and detects whether the connection is
    /// insufficient (disjoint roles / propagation-ALL / unhandled reapply ⇒
    /// insufficient; range concept absent on the nominal ⇒ nominal-influenced), or
    /// (B) does the same against the backend representative-memory cache label, or
    /// (C, no consistence data) adds only the domain/range concepts and delays the
    /// nominal concept. With nominal processing disabled the node is marked
    /// insufficient.
    ///
    /// PORT-PENDING — faithful structure recorded below. Needs: the descriptor
    /// chain; the concept reads (`getRole`/`getNominalIndividual`, model-ported)
    /// and `CIndividual::getIndividualID`; the saturation node accessors
    /// (`getDirectStatusFlags`/`getNominalIndividual`); the role reads
    /// (`getIndirectSuperRoleList`/`hasDisjointRoles`/`getDomainRangeConceptList`,
    /// model-ported); the unported `CReapplyConceptLabelSet` /
    /// `CReapplyRoleSuccessorHash` / `CReapplyQueueIterator` /
    /// `CReapplyConceptDescriptor` reads; `CConceptOperator::hasPartialOperatorCodeFlag`
    /// (model-ported) with the `CCFS_*` flag groups and the `CCSOME` code; the
    /// backend cache handler `mBackendAssCaceHandler` (`getIndividualAssociationData`
    /// / `hasConceptInAssociatedFullConceptSetLabel` /
    /// `visitConceptsOfAssociatedFullConceptSetLabel`, `W6-DEFER[api]`); the status
    /// masks (`INDSATFLAGNOMINALCONNECTION`/`INDSATFLAGINSUFFICIENT`) and the
    /// critical tag `CCT_VALUE`; and the siblings
    /// `updateDirectAddingIndividualStatusFlags` /
    /// `updateAddingSuccessorConnectedNominal` / `isConsistenceDataAvailable` /
    /// `getCorrectedNode` / `addConceptFilteredToIndividual` /
    /// `addAutomateTransitionOperands` / `addInfluencedNominal` /
    /// `setInsufficientNodeOccured` / `addCriticalConceptDescriptor` /
    /// `addNominalDependentIndividualNode` / `delayNominalSaturationConceptProcessing`.
    ///
    /// C++ structure:
    /// ```text
    /// STATINC(VALUERULEAPPLICATIONCOUNT, mCalcAlgContext)
    /// conDes      = conSatProLinker->getConceptSaturationDescriptor()
    /// conNegation = conDes->getNegation()
    /// concept     = conDes->getConcept()
    /// role        = concept->getRole()
    /// nominalIndividual = concept->getNominalIndividual()
    /// nominalID   = nominalIndividual->getIndividualID()
    ///
    /// if mConfNominalProcessing:
    ///     updateDirectAddingIndividualStatusFlags(processIndi, INDSATFLAGNOMINALCONNECTION)
    ///     updateAddingSuccessorConnectedNominal(processIndi, nominalID)
    ///
    ///     if isConsistenceDataAvailable(mCalcAlgContext):
    ///         nominalProcessNode = getCorrectedNode(nominalID, mDetCachedCGIndiVector)
    ///         if nominalProcessNode:                          // --- branch (A): cached CG node ---
    ///             nominalInfluenced = false; insufficientNominalConnection = false
    ///             nominalReapplyRoleSuccHash = nominalProcessNode->getReapplyRoleSuccessorHash(false)
    ///             for superRoleIt in role->getIndirectSuperRoleList():
    ///                 superRole = superRoleIt->getData(); inversedSuperRole = superRoleIt->isNegated()
    ///                 if superRole->hasDisjointRoles(): insufficientNominalConnection = true
    ///                 directStatFlags = processIndi->getDirectStatusFlags()
    ///                 for domainConLinkerIt in superRole->getDomainRangeConceptList(inversedSuperRole):
    ///                     addConceptFilteredToIndividual(domainConcept, domainConceptNegation, processIndi)
    ///                 for rangeConLinkerIt in superRole->getDomainRangeConceptList(!inversedSuperRole)
    ///                          while !directStatFlags->hasInsufficientFlag():
    ///                     nominalConSet = nominalProcessNode->getReapplyConceptLabelSet(false)
    ///                     if !nominalConSet || !nominalConSet->containsConcept(rangeConcept, rangeConceptNegation):
    ///                         nominalInfluenced = true
    ///                 if inversedSuperRole && nominalReapplyRoleSuccHash:
    ///                     reapplyRoleIt = nominalReapplyRoleSuccHash->getRoleReapplyIterator(superRole)
    ///                     while reapplyRoleIt.hasNext():
    ///                         reapplyDes  = reapplyRoleIt.next()
    ///                         reapplyConDes = reapplyDes->getConceptDescriptor()
    ///                         reapplyConcept = reapplyConDes->getConcept(); reapplyConceptNegation = reapplyConDes->isNegated()
    ///                         reapplyConceptCode = reapplyConcept->getOperatorCode()
    ///                         reapplyConceptOperator = reapplyConcept->getConceptOperator()
    ///                         if !neg && op.has(CCFS_PROPAGATION_ALL_TYPE):       insufficientNominalConnection = true
    ///                         elif (!neg && op.has(CCFS_ALL_AQALL_TYPE)) || (neg && code==CCSOME):
    ///                             for reapplyConceptOpLinkerIt in reapplyConcept->getOperandList():
    ///                                 addConceptFilteredToIndividual(reapplyOperandConcept,
    ///                                     reapplyConceptOpLinkerIt->isNegated()^reapplyConceptNegation, processIndi)
    ///                         elif !neg && op.has(CCFS_AQAND_TYPE): addAutomateTransitionOperands(processIndi, reapplyConcept, role)
    ///                         else:                                                insufficientNominalConnection = true
    ///             if nominalInfluenced:
    ///                 insufficientNominalConnection = true
    ///                 if !processIndi->getNominalIndividual(): addInfluencedNominal(nominalID)
    ///             if insufficientNominalConnection:
    ///                 updateDirectAddingIndividualStatusFlags(processIndi, INDSATFLAGINSUFFICIENT); setInsufficientNodeOccured()
    ///             if mNonDetConsistencyCG: addCriticalConceptDescriptor(conDes, CCT_VALUE, processIndi)
    ///             addNominalDependentIndividualNode(nominalID, processIndi, VALUECONNECTION)
    ///         else:                                            // --- branch (B): backend cache ---
    ///             nominalInfluenced = false; insufficientNominalConnection = false
    ///             indiAssData = mBackendAssCaceHandler->getIndividualAssociationData(nominalIndividual)
    ///             for superRoleIt in role->getIndirectSuperRoleList():
    ///                 superRole = ...; inversedSuperRole = ...
    ///                 if superRole->hasDisjointRoles(): insufficientNominalConnection = true
    ///                 directStatFlags = processIndi->getDirectStatusFlags()
    ///                 for domainConLinkerIt in superRole->getDomainRangeConceptList(inversedSuperRole):
    ///                     addConceptFilteredToIndividual(domainConcept, domainConceptNegation, processIndi)
    ///                 for rangeConLinkerIt in superRole->getDomainRangeConceptList(!inversedSuperRole)
    ///                          while !directStatFlags->hasInsufficientFlag():
    ///                     if !mBackendAssCaceHandler->hasConceptInAssociatedFullConceptSetLabel(
    ///                             indiAssData, indiAssData->getLabelCacheEntry(FULL_CONCEPT_SET_LABEL),
    ///                             rangeConcept, rangeConceptNegation):
    ///                         nominalInfluenced = true
    ///                 if inversedSuperRole:
    ///                     mBackendAssCaceHandler->visitConceptsOfAssociatedFullConceptSetLabel(
    ///                         indiAssData, indiAssData->getLabelCacheEntry(FULL_CONCEPT_SET_LABEL),
    ///                         lambda(reapplyConcept, reapplyConceptNegation, deterministic):
    ///                             if reapplyConcept->getRole() == superRole:
    ///                                 ... // SAME dispatch as branch (A): PROPAGATION_ALL/ALL_AQALL|SOME/AQAND/else
    ///                             return true,
    ///                         true, false)
    ///             if nominalInfluenced:
    ///                 insufficientNominalConnection = true
    ///                 if !processIndi->getNominalIndividual(): addInfluencedNominal(nominalID)
    ///             if insufficientNominalConnection:
    ///                 updateDirectAddingIndividualStatusFlags(processIndi, INDSATFLAGINSUFFICIENT); setInsufficientNodeOccured()
    ///             addNominalDependentIndividualNode(nominalID, processIndi, VALUECONNECTION)
    ///     else:                                                // --- branch (C): no consistence data ---
    ///         for superRoleIt in role->getIndirectSuperRoleList():
    ///             superRole = ...; inversedSuperRole = ...
    ///             for domainConLinkerIt in superRole->getDomainRangeConceptList(inversedSuperRole):
    ///                 addConceptFilteredToIndividual(domainConcept, domainConceptNegation, processIndi)
    ///         delayNominalSaturationConceptProcessing(processIndi, conSatProLinker, nominalID)
    /// else:
    ///     updateDirectAddingIndividualStatusFlags(processIndi, INDSATFLAGINSUFFICIENT); setInsufficientNodeOccured()
    /// ```
    pub fn apply_value_rule(
        &mut self,
        process_indi: &mut SatNodeId,
        con_sat_pro_linker: ConceptSaturationProcessLinkerId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // PORT-PENDING (see doc-comment transcription). W4-DEFER[api]: descriptor
        // chain, reapply label-set / role-succ-hash satellite reads, the backend
        // association cache handler (W6-DEFER[api]), the status/critical masks, and
        // the ~10 siblings are all not yet ported.
        let _ = (
            &mut *process_indi,
            con_sat_pro_linker,
            &mut *calc_alg_context,
        );
    }

    // =======================================================================
    // applyNOMINALRule (cpp 6731–6843).
    // =======================================================================

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::applyNOMINALRule`.
    ///
    /// The nominal (`{a}`) saturation rule. Integrates the nominal into the node,
    /// and with nominal processing enabled: connects the successor nominal, clashes
    /// every multiple-cardinality ancestor, then — if consistence data is available
    /// — replays the cached nominal node's full concept label (or, failing a cached
    /// node, the backend representative-memory full-concept-set label) onto the
    /// node, detecting whether the node is nominal-influenced (a saturation-label
    /// concept absent from the nominal's label, ignoring the self-nominal concept).
    /// Without consistence data it delays the nominal concept; with nominal
    /// processing disabled it marks the node insufficient.
    ///
    /// PORT-PENDING — faithful structure recorded below. Needs: the descriptor
    /// chain; the concept reads (`getRole`/`getNominalIndividual`, model-ported) +
    /// `CIndividual::getIndividualID`; the saturation node accessors
    /// (`hasNominalIntegrated`/`setIntegratedNominal`,
    /// `getMultipleCardinalityAncestorNodesLinker`,
    /// `getReapplyConceptSaturationLabelSet`/`getNominalIndividual`); the unported
    /// `CReapplyConceptLabelSet` / `CReapplyConceptSaturationLabelSet` /
    /// `CConceptSaturationDescriptor` / `CConceptDescriptor` chain reads;
    /// `getOperatorCode` with `CCNOMINAL` (model-ported); the backend cache handler
    /// `mBackendAssCaceHandler` (`getIndividualAssociationData`/`getLabelCacheEntry`/
    /// `hasConceptInAssociatedFullConceptSetLabel`/
    /// `visitConceptsOfAssociatedFullConceptSetLabel`, `W6-DEFER[api]`); the status
    /// masks (`INDSATFLAGNOMINALCONNECTION`/`INDSATFLAGCLASHED`/`INDSATFLAGINSUFFICIENT`)
    /// and the critical tag `CCT_NOMINAL`; and the siblings
    /// `updateDirectAddingIndividualStatusFlags` /
    /// `updateAddingSuccessorConnectedNominal` / `isConsistenceDataAvailable` /
    /// `getCorrectedNode` / `addInfluencedNominal` /
    /// `addConceptFilteredToIndividual` / `addCriticalConceptDescriptor` /
    /// `addNominalDependentIndividualNode` / `setInsufficientNodeOccured` /
    /// `delayNominalSaturationConceptProcessing`.
    ///
    /// C++ structure:
    /// ```text
    /// STATINC(NOMINALRULEAPPLICATIONCOUNT, mCalcAlgContext)
    /// conDes      = conSatProLinker->getConceptSaturationDescriptor()
    /// conNegation = conDes->getNegation()                 // bound, unused below
    /// concept     = conDes->getConcept()
    /// role        = concept->getRole()                    // bound, unused below
    /// nominalIndividual = concept->getNominalIndividual()
    /// nominalID   = nominalIndividual->getIndividualID()
    ///
    /// if !processIndi->hasNominalIntegrated():
    ///     processIndi->setIntegratedNominal(nominalIndividual)
    ///
    /// if mConfNominalProcessing:
    ///     updateDirectAddingIndividualStatusFlags(processIndi, INDSATFLAGNOMINALCONNECTION)
    ///     updateAddingSuccessorConnectedNominal(processIndi, nominalID)
    ///     for multipleCardinalityAncestorNodesLinkerIt in processIndi->getMultipleCardinalityAncestorNodesLinker():
    ///         updateDirectAddingIndividualStatusFlags(multipleCardinalityAncestorNode, INDSATFLAGCLASHED)
    ///
    ///     CBackendRepresentativeMemoryCacheIndividualAssociationData* indiAssData = nullptr  // (outer, shadowed inside)
    ///     if isConsistenceDataAvailable(mCalcAlgContext):
    ///         nominalProcessNode = getCorrectedNode(nominalID, mDetCachedCGIndiVector)
    ///         if nominalProcessNode:                          // --- cached CG node ---
    ///             nominalConSet = nominalProcessNode->getReapplyConceptLabelSet(false)
    ///             if nominalConSet:
    ///                 nominalInfluenced = false
    ///                 satConSet = processIndi->getReapplyConceptSaturationLabelSet(false)
    ///                 for satConDesIt in satConSet->getConceptSaturationDescriptionLinker() while !nominalInfluenced:
    ///                     if !nominalConSet->containsConcept(satConcept, satConceptNegation): nominalInfluenced = true
    ///                 if nominalInfluenced && !processIndi->getNominalIndividual(): addInfluencedNominal(nominalID)
    ///                 for nominalConDesIt in nominalConSet->getAddingSortedConceptDescriptionLinker():
    ///                     addConceptFilteredToIndividual(nominalConcept, nominalConceptNegation, processIndi)
    ///             if mNonDetConsistencyCG: addCriticalConceptDescriptor(conDes, CCT_NOMINAL, processIndi)
    ///         else:                                            // --- backend cache ---
    ///             indiAssData = mBackendAssCaceHandler->getIndividualAssociationData(nominalIndividual)
    ///             if indiAssData:
    ///                 labelCacheItem = indiAssData->getLabelCacheEntry(FULL_CONCEPT_SET_LABEL)
    ///                 if labelCacheItem:
    ///                     nominalInfluenced = false
    ///                     satConSet = processIndi->getReapplyConceptSaturationLabelSet(false)
    ///                     for satConDesIt in satConSet->getConceptSaturationDescriptionLinker() while !nominalInfluenced:
    ///                         if satConceptNegation || satConcept->getOperatorCode()!=CCNOMINAL
    ///                                 || satConcept->getNominalIndividual()!=nominalIndividual:
    ///                             if !mBackendAssCaceHandler->hasConceptInAssociatedFullConceptSetLabel(
    ///                                     indiAssData, labelCacheItem, satConcept, satConceptNegation):
    ///                                 nominalInfluenced = true
    ///                     if nominalInfluenced && !processIndi->getNominalIndividual(): addInfluencedNominal(nominalID)
    ///                     mBackendAssCaceHandler->visitConceptsOfAssociatedFullConceptSetLabel(
    ///                         indiAssData, indiAssData->getLabelCacheEntry(FULL_CONCEPT_SET_LABEL),
    ///                         lambda(addConcept, addConceptNegation, deterministic):
    ///                             addConceptFilteredToIndividual(addConcept, addConceptNegation, processIndi); return true,
    ///                         true, false)
    ///         addNominalDependentIndividualNode(nominalID, processIndi, NOMINALCONNECTION)
    ///     else:
    ///         delayNominalSaturationConceptProcessing(processIndi, conSatProLinker, nominalID)
    /// else:
    ///     updateDirectAddingIndividualStatusFlags(processIndi, INDSATFLAGINSUFFICIENT); setInsufficientNodeOccured()
    /// ```
    pub fn apply_nominal_rule(
        &mut self,
        process_indi: &mut SatNodeId,
        con_sat_pro_linker: ConceptSaturationProcessLinkerId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // PORT-PENDING (see doc-comment transcription). W4-DEFER[api]: descriptor
        // chain, the saturation/reapply label-set reads, the backend association
        // cache handler (W6-DEFER[api]), the status/critical masks, and the ~9
        // siblings are all not yet ported.
        let _ = (
            &mut *process_indi,
            con_sat_pro_linker,
            &mut *calc_alg_context,
        );
    }
}

#[cfg(test)]
mod tests {
    use super::super::super::model::concept::Concept;
    use super::super::super::model::role::Role;
    use super::super::super::model::ConceptId;
    use super::super::super::process::sat_node::IndividualSaturationProcessNode;
    use super::super::algorithm::SaturationTaskHandleAlgorithm;
    use super::super::satellites::{ConceptSaturationDescriptor, ConceptSaturationProcessLinker};
    use super::*;

    fn role(ctx: &mut CalculationAlgorithmContextBase, tag: Cint64) -> RoleId {
        let mut role = Role::new();
        role.set_role_tag(tag);
        ctx.ontology_arenas_mut().alloc_role(role)
    }

    fn atom(ctx: &mut CalculationAlgorithmContextBase, tag: Cint64) -> ConceptId {
        let mut concept = Concept::new();
        concept.set_operator_code(CCATOM).set_concept_tag(tag);
        ctx.ontology_arenas_mut().alloc_concept(concept)
    }

    fn cardinality_concept(
        ctx: &mut CalculationAlgorithmContextBase,
        op_code: Cint64,
        tag: Cint64,
        role: RoleId,
        parameter: Cint64,
        operand: Option<ConceptId>,
    ) -> ConceptId {
        let mut concept = Concept::new();
        concept
            .set_operator_code(op_code)
            .set_concept_tag(tag)
            .set_role(role)
            .set_parameter(parameter);
        if let Some(operand) = operand {
            concept
                .add_operand_linker(operand, false)
                .set_operand_count(1);
        }
        ctx.ontology_arenas_mut().alloc_concept(concept)
    }

    fn concept_process_linker(
        ctx: &mut CalculationAlgorithmContextBase,
        concept: ConceptId,
        negated: bool,
    ) -> (
        ConceptSaturationProcessLinkerId,
        ConceptSaturationDescriptorId,
    ) {
        let mut descriptor = ConceptSaturationDescriptor::new();
        descriptor.init_concept_saturation_descriptor(concept, negated);
        let descriptor = ctx.process_context_mut().alloc_con_sat_desc(descriptor);
        let mut linker = ConceptSaturationProcessLinker::new();
        linker.init_concept_saturation_process_linker(descriptor);
        (
            ctx.process_context_mut().alloc_con_sat_proc_linker(linker),
            descriptor,
        )
    }

    #[test]
    fn s04_apply_atleast_rule_updates_max_candidate() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();

        let role = role(&mut ctx, 501);
        let concept = cardinality_concept(&mut ctx, CCATLEAST, 503, role, 2, None);
        let (linker, _) = concept_process_linker(&mut ctx, concept, false);
        let mut node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());

        algo.apply_atleast_rule(&mut node, linker, &mut ctx);

        assert_eq!(
            ctx.process_context()
                .sat_node(node)
                .get_max_atleast_cardinality_candidate(),
            2
        );
        assert_eq!(
            ctx.process_context()
                .sat_node(node)
                .get_max_atmost_cardinality_candidate(),
            0
        );
    }

    #[test]
    fn s04_apply_atleast_rule_negated_increments_cardinality() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();

        let role = role(&mut ctx, 511);
        let concept = cardinality_concept(&mut ctx, CCATLEAST, 513, role, 2, None);
        let (linker, _) = concept_process_linker(&mut ctx, concept, true);
        let mut node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());

        algo.apply_atleast_rule(&mut node, linker, &mut ctx);

        assert_eq!(
            ctx.process_context()
                .sat_node(node)
                .get_max_atleast_cardinality_candidate(),
            3
        );
    }

    #[test]
    fn s04_apply_atmost_rule_sets_restricted_and_max_candidate() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();

        let role = role(&mut ctx, 521);
        let concept = cardinality_concept(&mut ctx, CCATMOST, 523, role, 2, None);
        let (linker, _) = concept_process_linker(&mut ctx, concept, false);
        let mut node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());

        algo.apply_atmost_rule(&mut node, linker, &mut ctx);

        let node_ref = ctx.process_context().sat_node(node);
        assert_eq!(node_ref.get_max_atleast_cardinality_candidate(), 0);
        assert_eq!(node_ref.get_max_atmost_cardinality_candidate(), 2);
        assert!(node_ref.direct_status_flags.has_flags_code(
            IndividualSaturationProcessNodeStatusFlags::INDSATFLAGCARDINALITYRESTRICTED,
            false,
        ));
    }

    #[test]
    fn s04_apply_atmost_rule_negative_cardinality_clashes() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();

        let role = role(&mut ctx, 531);
        let operand = atom(&mut ctx, 535);
        let concept = cardinality_concept(&mut ctx, CCATMOST, 533, role, 0, Some(operand));
        let (linker, _) = concept_process_linker(&mut ctx, concept, true);
        let mut node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());

        algo.apply_atmost_rule(&mut node, linker, &mut ctx);

        let node_ref = ctx.process_context().sat_node(node);
        assert!(node_ref.direct_status_flags.has_clashed_flag());
        assert_eq!(node_ref.get_max_atmost_cardinality_candidate(), 0);
    }
}
