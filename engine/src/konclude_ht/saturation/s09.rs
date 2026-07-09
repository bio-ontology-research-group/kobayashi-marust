//! `saturation::s09` — Critical-concept / insufficiency detection + disjunct
//! common-concept extraction (port unit #9 of 12).
//!
//! Faithful port of groups **H** (critical-concept / insufficiency markers) and
//! **I** (disjunct-common-concept over-approximation extraction) of Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauApproximationSaturationTaskHandleAlgorithm.cpp`
//! (manifest `03-saturation-calc.md`, PU-SAT-9). The exact `.cpp` definition
//! ranges ported here:
//!
//!   group H — critical-concept detection / insufficiency:
//!   * `hasNextCriticalConcepts`                       (cpp 838–847),
//!   * `checkNextCriticalConcepts`                     (cpp 850–870),
//!   * `checkCriticalIndividuals`                      (cpp 872–906),
//!   * `addCriticalORConceptTestedForDependentNodes`   (cpp 2933–2981),
//!   * `addCriticalConceptForDependentNodes`           (cpp 2985–2998),
//!   * `checkCriticalConceptsForNode`                  (cpp 3002–3189),
//!   * `addCriticalConceptDescriptor`                  (cpp 3386–3406),
//!   * `testInsufficientALLConcepts`                   (cpp 3412–3458),
//!   * `isCriticalALLConceptDescriptorInsufficient`    (cpp 3462–3578),
//!   * `isCriticalORConceptDescriptorInsufficient`     (cpp 3582–3602),
//!   * `isCriticalEQCANDConceptDescriptorProblematic`  (cpp 3606–3622),
//!   * `isCriticalATMOSTConceptDescriptorInsufficient` (cpp 3625–3770),
//!   * `isCriticalNOMINALConceptDescriptorInsufficient`(cpp 4843–4873),
//!   * `isCriticalVALUEConceptDescriptorInsufficient`  (cpp 4876–4933),
//!
//!   group I — disjunct common-concept extraction:
//!   * `updateExtractDisjunctCommonConcept`            (cpp 4936–4965),
//!   * `initializeExtractDisjunctCommonConcept`        (cpp 4970–5005),
//!   * `addDisjunctCommonConceptExtractionToProcessingQueue` (cpp 5009–5018).
//!
//! (The cpp interleaves group-F successor-collection helpers — `collectLinkedSuccessorNodes`
//! 3194, `addLinkedSuccessorNodeForRoleAssertion` 3234, `addLinkedSuccessorNodeForConcept`
//! 3250 — between these definitions; those belong to PU-SAT-7 and are NOT ported here,
//! only called as siblings.)
//!
//! KONCLUDE-PORT-NOTE[ownership]: each method is a member of
//! `CCalculationTableauApproximationSaturationTaskHandleAlgorithm` ⇒ `&mut self`.
//! Per the port-wide context convention the shared
//! `CCalculationAlgorithmContextBase*` is threaded explicitly as a trailing
//! `calc_alg_context: &mut CalculationAlgorithmContextBase` (the C++ methods take
//! it directly). The in/out node references `CIndividualSaturationProcessNode*&`
//! become `&mut SatNodeId` (an arena id into the per-test `sat_nodes` pool); plain
//! `CIndividualSaturationProcessNode*` value out-params (the ATMOST
//! `functionallyRestrictedSuccessorNode`) likewise `&mut SatNodeId`. The C++
//! `bool& ancestorPossiblyCriticalFlag` becomes `&mut bool`. Sibling
//! `apply*`/`update*`/`mark*`/pool/queue/resolve methods land in the other
//! `s01..s12` units and are called as `self.x(...)`.
//!
//! KONCLUDE-PORT-NOTE[api]: this whole family is the saturation *analysis* layer —
//! almost every line dereferences a not-yet-ported satellite:
//!   * `CConceptSaturationDescriptor*` (the per-concept saturation descriptor,
//!     `process::stubs::ConceptSaturationDescriptorId`) — its `getConcept()` /
//!     `isNegated()` and the `CConcept` operand/role/parameter/nominal accessors;
//!   * `CReapplyConceptSaturationLabelSet*` (the node saturated label) and its
//!     `containsConcept` / descriptor-linker iteration;
//!   * the `CCriticalSaturationConceptTypeQueues` / `CCriticalSaturationConceptQueue`
//!     per-node critical-concept worklists, the `CCriticalIndividualNodeProcessingQueue`,
//!     and the `CCriticalIndividualNodeConceptTestSet` tested-pair set;
//!   * the `CLinkedRoleSaturationSuccessorHash` / `CLinkedRoleSaturationSuccessorData`
//!     successor hashes and the `CRoleBackwardSaturationPropagationHash`;
//!   * the `CSaturationDisjunctCommonConceptExtractionData` extraction satellite
//!     (group I), its count-hash and extraction-linker chains.
//! None are concrete arena types yet (they are `process::stubs` markers, or opaque
//! `Cint64` handles on the sat-node). Control flow is transcribed faithfully with
//! every unported satellite deref flagged inline `// W4-DEFER[api]` and the C++
//! preserved; the genuinely-resolvable leaves (the `self.*` sibling critical /
//! status-flag / queue calls, the sat-node scalar getters, the `conf_*` member
//! gates, the databox queue getter) are emitted as real code. No logic is dropped;
//! the per-queue / per-descriptor iterations that cannot be materialised without
//! their satellite types fall through to the C++ default return.
//!
//! KONCLUDE-PORT-NOTE[api]: the `CCriticalSaturationConceptTypeQueues::CRITICALSATURATIONCONCEPTQUEUETYPE`
//! discriminants (`CCT_FORALL` / `CCT_ATMOST` / `CCT_VALUE` / `CCT_NOMINAL` /
//! `CCT_DISJUNCTION` / `CCT_EQCANDIDATE`) and the `INDSATFLAG*` status masks are
//! pending associated constants (see the sibling `s03`–`s05` units that already
//! reference the masks); modelled here as opaque `Cint64` pass-through tags until
//! `CCriticalSaturationConceptTypeQueues` / the status-flag mask unit land.

#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_mut)]

use super::super::completion::context::CalculationAlgorithmContextBase;
use super::super::model::substrate::{Cint64, INVALID};
use super::super::model::{ConceptId, NegLink, RoleId};
use super::super::process::sat_node::{
    IndividualSaturationProcessNode, IndividualSaturationProcessNodeStatusFlags,
};
use super::super::process::sat_queue::CriticalSaturationConceptQueueType;
use super::super::process::stubs::{
    ConceptSaturationDescriptorId, ConceptSaturationProcessLinkerId,
};
use super::super::process::SatNodeId;
use super::satellites::{
    IndividualSaturationSuccessorLinkDataLinkerId, SaturationSuccessorDataId,
};

// ---------------------------------------------------------------------------
// W4-DEFER[api]: pending `CCriticalSaturationConceptTypeQueues::CRITICALSATURATIONCONCEPTQUEUETYPE`
// discriminants — carried as opaque pass-through tags (the queue-type machinery
// they select is itself deferred). Real values resolve when the queue class lands.
// ---------------------------------------------------------------------------
const CCT_FORALL: Cint64 = 0;
const CCT_ATMOST: Cint64 = 1;
const CCT_DISJUNCTION: Cint64 = 2;
const CCT_EQCANDIDATE: Cint64 = 3;
const CCT_VALUE: Cint64 = 4;
const CCT_NOMINAL: Cint64 = 5;

impl super::algorithm::SaturationTaskHandleAlgorithm {
    // =======================================================================
    // Group H — main loop predicates / drivers (cpp 838–906)
    // =======================================================================

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::hasNextCriticalConcepts`
    /// (cpp 838–847).
    pub fn has_next_critical_concepts(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // CProcessingDataBox* procDataBox = calcAlgContext->getUsedProcessingDataBox();
        // CCriticalIndividualNodeProcessingQueue* critIndNodeProcQueue =
        //     procDataBox->getSaturationCriticalIndividualNodeProcessingQueue(false);
        let crit_ind_node_proc_queue =
            calc_alg_context.saturation_critical_individual_node_processing_queue(false);
        if !crit_ind_node_proc_queue.is_none() {
            if !calc_alg_context
                .process_context()
                .sat_critical_ind_node_proc_queue(crit_ind_node_proc_queue)
                .is_empty()
            {
                return true;
            }
        }
        false
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::checkNextCriticalConcepts`
    /// (cpp 850–870).
    pub fn check_next_critical_concepts(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // CProcessingDataBox* procDataBox = calcAlgContext->getUsedProcessingDataBox();
        // CCriticalIndividualNodeProcessingQueue* critIndNodeProcQueue =
        //     procDataBox->getSaturationCriticalIndividualNodeProcessingQueue(false);
        let crit_ind_node_proc_queue =
            calc_alg_context.saturation_critical_individual_node_processing_queue(false);
        if !crit_ind_node_proc_queue.is_none() {
            // CIndividualSaturationProcessNode* indiProcSatNode = critIndNodeProcQueue->takeNextProcessIndividual();
            let mut indi_proc_sat_node = calc_alg_context
                .process_context_mut()
                .sat_critical_ind_node_proc_queue_mut(crit_ind_node_proc_queue)
                .take_next_process_individual();
            if indi_proc_sat_node.is_some() {
                // bool checkCriticalConcepts = true;
                // if (indiProcSatNode->getDirectStatusFlags()->hasMissedABoxConsistencyFlag()) {
                //     if (!isConsistenceDataAvailable(calcAlgContext)) { checkCriticalConcepts = false; ... } }
                // W2-DEFER[api]: the `hasMissedABoxConsistencyFlag` status bit is not
                // ported (constant false, same deferral as the s01 driver), so
                // checkCriticalConcepts is always true here.
                self.check_critical_concepts_for_node(&mut indi_proc_sat_node, calc_alg_context);
            }
        }
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::checkCriticalIndividuals`
    /// (cpp 872–906).
    pub fn check_critical_individuals(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // CProcessingDataBox* procDataBox = calcAlgContext->getUsedProcessingDataBox();
        // CIndividualSaturationProcessNodeLinker* indiSaturationAnalysingNodeLinker =
        //     procDataBox->getIndividualSaturationAnalysationNodeLinker();
        // CCriticalIndividualNodeConceptTestSet* criticalIndiNodeConTestSet =
        //     procDataBox->getSaturationCriticalIndividualNodeConceptTestSet(true);
        //
        // W4-DEFER[api]: the whole body walks the unported
        //   CIndividualSaturationProcessNodeLinker analysation chain and, per node, the
        //   CReapplyConceptSaturationLabelSet descriptor linker, gated by
        //   CIndividualSaturationProcessNodeStatusFlags predicates and the
        //   CCriticalIndividualNodeConceptTestSet tested-pair set. Faithful transcription:
        //
        //   if (indiSaturationAnalysingNodeLinker && calcAlgContext->getSatisfiableCalculationTask()
        //          ->getSaturationIndividualsAnalysationObserver()) {
        //       for (...indiSaturationAnalysingNodeLinkerIt...) {
        //           CIndividualSaturationProcessNode* satIndiNode = ...->getProcessingIndividual();
        //           CIndividualSaturationProcessNodeStatusFlags* indStatFlags = satIndiNode->getIndirectStatusFlags();
        //           CIndividualSaturationProcessNodeStatusFlags* dirStatFlags = satIndiNode->getDirectStatusFlags();
        //           if (!indStatFlags->hasClashedFlag() && !dirStatFlags->hasPropagationIncompleteFlag()) {
        //               CReapplyConceptSaturationLabelSet* succConSet = satIndiNode->getReapplyConceptSaturationLabelSet(false);
        //               if (succConSet) {
        //                   for (CConceptSaturationDescriptor* conSatDesIt = succConSet->getConceptSaturationDescriptionLinker();
        //                        conSatDesIt && !dirStatFlags->hasPropagationIncompleteFlag(); conSatDesIt = conSatDesIt->getNext()) {
        //                       CConcept* concept = conSatDesIt->getConcept();
        //                       bool negation = conSatDesIt->isNegated();
        //                       if (!negation && concept->getConceptOperator()->hasPartialOperatorCodeFlag(CConceptOperator::CCFS_ALL_AQALL_TYPE)
        //                           || negation && concept->getConceptOperator()->hasPartialOperatorCodeFlag(CConceptOperator::CCFS_SOME_TYPE)) {
        //                           if (!criticalIndiNodeConTestSet->isConceptTestedForIndividual(conSatDesIt, satIndiNode)) {
        //                               criticalIndiNodeConTestSet->insertConceptTestedForIndividual(conSatDesIt, satIndiNode);
        //                               STATINC(SATURATIONCRITICALTESTCOUNT, calcAlgContext);
        //                               if (isCriticalALLConceptDescriptorInsufficient(conSatDesIt, satIndiNode, calcAlgContext)) {
        //                                   updateDirectAddingIndividualStatusFlags(satIndiNode, INDSATFLAGINSUFFICIENT, calcAlgContext);
        //                                   updateDirectAddingIndividualStatusFlags(satIndiNode, INDSATFLAGPROPAGATIONINCOMPLETE, calcAlgContext);
        //                                   setInsufficientNodeOccured(calcAlgContext);
        //                                   ++mInsufficientALLCount;
        //                               }
        //                           }
        //                       }
        //                   }
        //               }
        //           }
        //       }
        //   }
        //
        // Resolvable leaves: `self.is_critical_all_concept_descriptor_insufficient` (below),
        // `self.update_direct_adding_individual_status_flags` / `self.set_insufficient_node_occured`
        // (group L/B) and the `self.insufficient_all_count` counter — they fire per descriptor
        // once the label-set linker yields concrete `(ConceptSaturationDescriptorId, SatNodeId)`
        // pairs and the status-flag predicates land.
        let _ = calc_alg_context.saturation_critical_individual_node_concept_test_set(true);
    }

    // =======================================================================
    // Group H — critical-concept descriptor enqueue / fan-out (cpp 2933–3406)
    // =======================================================================

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::addCriticalORConceptTestedForDependentNodes`
    /// (cpp 2933–2981).
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: `CConceptSaturationDescriptor* conDes` →
    /// `ConceptSaturationDescriptorId`; the `CCriticalIndividualNodeConceptTestSet*`
    /// tested-pair set is an opaque `Cint64` until the satellite is ported.
    pub fn add_critical_or_concept_tested_for_dependent_nodes(
        &mut self,
        con_des: ConceptSaturationDescriptorId,
        concept_type: Cint64,
        indi_proc_sat_node: &mut SatNodeId,
        critical_indi_node_con_test_set: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // cint64 updatedNodes = 0;  cint64 currentUpdateLinkerCount = 1;
        // CIndividualSaturationProcessNodeStatusUpdateLinker* directUpdateLinker =
        //     createIndividualSaturationUpdateLinker(calcAlgContext);
        // directUpdateLinker->initUpdateNodeLinker(indiProcSatNode);
        //
        // W4-DEFER[api]: a work-list closure over the unported
        //   CIndividualSaturationProcessNodeStatusUpdateLinker pool + the per-node
        //   CXNegLinker<CIndividualSaturationProcessNode*> copy-depending chain, gated by
        //   the CIndividualSaturationProcessNodeStatusFlags INDSATFLAGINSUFFICIENT mask and
        //   the CCriticalIndividualNodeConceptTestSet tested-pair set. Faithful transcription:
        //
        //   while (directUpdateLinker) {
        //       nextUpdateLinker = directUpdateLinker; directUpdateLinker = directUpdateLinker->getNext();
        //       updateIndiNode = nextUpdateLinker->getData(); nextUpdateLinker->clearNext();
        //       releaseIndividualSaturationUpdateLinker(nextUpdateLinker, calcAlgContext);
        //       --currentUpdateLinkerCount; ++updatedNodes;
        //       for (depIndiIt : updateIndiNode->getCopyDependingIndividualNodeLinker()) {
        //           if (depIndiIt->isNegated()) {
        //               dependingIndiNode = depIndiIt->getData();
        //               statusFlag = dependingIndiNode->getDirectStatusFlags();
        //               bool continueDepending = false;
        //               if (!statusFlag->hasFlags(INDSATFLAGINSUFFICIENT, false)) {
        //                   if (!criticalIndiNodeConTestSet->isConceptTestedForIndividual(conDes, dependingIndiNode)) {
        //                       criticalIndiNodeConTestSet->insertConceptTestedForIndividual(conDes, dependingIndiNode);
        //                       STATINC(SATURATIONCRITICALTESTCOUNT, calcAlgContext);
        //                       if (isCriticalORConceptDescriptorInsufficient(conDes, dependingIndiNode, calcAlgContext)) {
        //                           updateDirectNotDependentAddingIndividualStatusFlags(dependingIndiNode, INDSATFLAGINSUFFICIENT, calcAlgContext);
        //                           setInsufficientNodeOccured(calcAlgContext);
        //                           continueDepending = true;
        //                       }
        //                   }
        //               } else { continueDepending = true; }
        //               if (continueDepending) {
        //                   nextUpdateLinker = createIndividualSaturationUpdateLinker(calcAlgContext);
        //                   nextUpdateLinker->initUpdateNodeLinker(dependingIndiNode);
        //                   directUpdateLinker = nextUpdateLinker->append(directUpdateLinker);
        //                   ++currentUpdateLinkerCount;
        //               }
        //           }
        //       }
        //   }
        //
        // Resolvable leaves: `self.create_individual_saturation_update_linker` /
        // `self.release_individual_saturation_update_linker` (group M pools),
        // `self.is_critical_or_concept_descriptor_insufficient` (below),
        // `self.update_direct_not_dependent_adding_individual_status_flags` /
        // `self.set_insufficient_node_occured`; they fire once the update-linker pool +
        // copy-depending chain yield concrete nodes and the tested-pair set is ported.
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::addCriticalConceptForDependentNodes`
    /// (cpp 2985–2998).
    pub fn add_critical_concept_for_dependent_nodes(
        &mut self,
        con_des: ConceptSaturationDescriptorId,
        concept_type: Cint64,
        indi_proc_sat_node: &mut SatNodeId,
        direct_flags_check: bool,
        check_flags: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let depending_nodes: Vec<SatNodeId> = calc_alg_context
            .process_context()
            .sat_node(*indi_proc_sat_node)
            .get_copy_depending_individual_node_linker()
            .iter()
            .map(|link| link.target)
            .collect();
        for mut depending_indi_node in depending_nodes {
            let has_check_flags = if check_flags == 0 {
                false
            } else {
                let depending_node_ref = calc_alg_context
                    .process_context()
                    .sat_node(depending_indi_node);
                let status_flags = if direct_flags_check {
                    &depending_node_ref.direct_status_flags
                } else {
                    &depending_node_ref.indirect_status_flags
                };
                status_flags.has_flags_code(check_flags, false)
            };
            if check_flags == 0 || !has_check_flags {
                self.add_critical_concept_descriptor(
                    con_des,
                    concept_type,
                    &mut depending_indi_node,
                    calc_alg_context,
                );
            }
        }
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::checkCriticalConceptsForNode`
    /// (cpp 3002–3189). The per-node critical-concept dispatch: drains the node's
    /// per-type critical-concept queues (FORALL, ATMOST, VALUE, NOMINAL, DISJUNCTION,
    /// EQCANDIDATE) and, for each untested descriptor, runs the matching
    /// `isCritical*ConceptDescriptorInsufficient` / `*Problematic` test, marking the
    /// node insufficient / propagation-incomplete / cardinality-problematic / eq-cand
    /// problematic or fanning the critical descriptor out to dependent nodes.
    pub fn check_critical_concepts_for_node(
        &mut self,
        indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // CCriticalSaturationConceptTypeQueues* criticalConceptQueues = indiProcSatNode->getCriticalConceptTypeQueues(false);
        let critical_concept_queues =
            IndividualSaturationProcessNode::get_critical_concept_type_queues_in_context(
                calc_alg_context.process_context_mut(),
                *indi_proc_sat_node,
                false,
            );
        // CCriticalIndividualNodeConceptTestSet* criticalIndiNodeConTestSet =
        //     processingDataBox->getSaturationCriticalIndividualNodeConceptTestSet(true);
        let critical_indi_node_con_test_set =
            calc_alg_context.saturation_critical_individual_node_concept_test_set(true);
        if critical_concept_queues.is_none() {
            // Queued without allocated typed queues — nothing to drain. (The C++
            // never queues a node before its queues satellite exists.)
            return;
        }
        // criticalConceptQueues->setProcessNodeQueued(false);
        calc_alg_context
            .process_context_mut()
            .critical_sat_concept_type_queues_mut(critical_concept_queues)
            .set_process_node_queued(false);

        // Drain helper reads, re-evaluated per iteration: the C++ holds live
        // pointers to the node's flag objects, which mutate inside the loops.
        macro_rules! indirect_flags {
            () => {{
                let flags = calc_alg_context
                    .process_context()
                    .sat_node(*indi_proc_sat_node)
                    .indirect_status_flags;
                (flags.has_insufficient_flag(), flags.has_clashed_flag())
            }};
        }
        macro_rules! take_untested {
            ($queue_type:expr) => {{
                let queue = calc_alg_context
                    .process_context()
                    .critical_sat_concept_type_queues(critical_concept_queues)
                    .get_critical_saturation_concept_queue_id($queue_type);
                if queue.is_none()
                    || !calc_alg_context
                        .process_context()
                        .critical_sat_concept_queue(queue)
                        .has_critical_concept_descriptor_linker()
                {
                    None
                } else {
                    let critical_con_proc_des = calc_alg_context
                        .process_context_mut()
                        .critical_sat_concept_queue_take_next_critical_concept_descriptor(queue);
                    let critical_con_des = calc_alg_context
                        .process_context()
                        .con_sat_proc_linker(critical_con_proc_des)
                        .get_concept_saturation_descriptor();
                    let concept = calc_alg_context
                        .process_context()
                        .con_sat_desc(critical_con_des)
                        .get_concept();
                    let already_tested = calc_alg_context
                        .process_context()
                        .sat_critical_ind_node_con_test_set(critical_indi_node_con_test_set)
                        .is_concept_tested_for_individual(concept, *indi_proc_sat_node);
                    if !already_tested {
                        calc_alg_context
                            .process_context_mut()
                            .sat_critical_ind_node_con_test_set_mut(critical_indi_node_con_test_set)
                            .insert_concept_tested_for_individual(concept, *indi_proc_sat_node);
                    }
                    Some((critical_con_proc_des, critical_con_des, already_tested))
                }
            }};
        }

        // ---- 1. CCT_FORALL (cpp 3010-3037) ----
        loop {
            let (insufficient, clashed) = indirect_flags!();
            if insufficient || clashed {
                break;
            }
            let Some((critical_con_proc_des, critical_con_des, already_tested)) =
                take_untested!(CriticalSaturationConceptQueueType::Forall)
            else {
                break;
            };
            if !already_tested {
                // STATINC(SATURATIONCRITICALTESTCOUNT, calcAlgContext);
                if self.is_critical_all_concept_descriptor_insufficient(
                    critical_con_des,
                    indi_proc_sat_node,
                    calc_alg_context,
                ) {
                    self.update_direct_adding_individual_status_flags(
                        *indi_proc_sat_node,
                        IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT,
                        calc_alg_context,
                    );
                    let is_abox = calc_alg_context
                        .process_context()
                        .sat_node(*indi_proc_sat_node)
                        .is_abox_individual_representation_node();
                    if is_abox {
                        self.update_direct_adding_individual_status_flags(
                            *indi_proc_sat_node,
                            IndividualSaturationProcessNodeStatusFlags::INDSATFLAGPROPAGATIONINCOMPLETE,
                            calc_alg_context,
                        );
                    }
                    self.set_insufficient_node_occured(calc_alg_context);
                    self.insufficient_all_count += 1;
                } else {
                    self.add_critical_concept_for_dependent_nodes(
                        critical_con_des,
                        CCT_FORALL,
                        indi_proc_sat_node,
                        false,
                        IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT,
                        calc_alg_context,
                    );
                }
            }
            self.release_concept_saturation_process_linker(critical_con_proc_des, calc_alg_context);
        }

        // ---- 2. CCT_ATMOST (cpp 3039-3091) ----
        loop {
            let (insufficient, clashed) = indirect_flags!();
            if insufficient || clashed {
                break;
            }
            let Some((critical_con_proc_des, critical_con_des, already_tested)) =
                take_untested!(CriticalSaturationConceptQueueType::Atmost)
            else {
                break;
            };
            if !already_tested {
                let mut ancestor_possibly_insufficient = false;
                let mut functionally_restricted_successor_node = SatNodeId::NONE;
                let mut functionally_restricted_successor_creation_role_linker: Vec<
                    NegLink<RoleId>,
                > = Vec::new();
                // STATINC(SATURATIONCRITICALTESTCOUNT, calcAlgContext);
                if self.is_critical_atmost_concept_descriptor_insufficient(
                    critical_con_des,
                    &mut ancestor_possibly_insufficient,
                    &mut functionally_restricted_successor_node,
                    &mut functionally_restricted_successor_creation_role_linker,
                    indi_proc_sat_node,
                    calc_alg_context,
                ) {
                    // KONCLUDE-PORT-NOTE[conservative]: the C++ delayed-merging arm
                    // (mConfDelayedMergingCriticalATMOSTConcepts && maxAtleastCardinality >
                    // threshold ⇒ queue via getATMOSTSuccessorMergingData +
                    // addSaturationATMOSTMergingProcessLinker + addMergingProcessingConcept)
                    // is deferred — the merging-queue enqueue plumbing has no live producer
                    // yet. Marking INSUFFICIENT immediately (the C++ else-arm) is strictly
                    // more conservative: the node reads as UNKNOWN and defers to the
                    // tableau probe. Costs saturation coverage only on nodes with
                    // atleast-cardinality > 100.
                    self.insufficient_atmost_count += 1;
                    self.update_direct_adding_individual_status_flags(
                        *indi_proc_sat_node,
                        IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT,
                        calc_alg_context,
                    );
                    self.set_insufficient_node_occured(calc_alg_context);
                } else {
                    self.add_critical_concept_for_dependent_nodes(
                        critical_con_des,
                        CCT_ATMOST,
                        indi_proc_sat_node,
                        false,
                        IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT,
                        calc_alg_context,
                    );
                }
                let nominal_integrated = calc_alg_context
                    .process_context()
                    .sat_node(*indi_proc_sat_node)
                    .has_nominal_integrated();
                if nominal_integrated {
                    self.mark_nominal_atmost_restricted_ancestors_as_insufficient(
                        critical_con_des,
                        indi_proc_sat_node,
                        calc_alg_context,
                    );
                }
                if ancestor_possibly_insufficient {
                    self.mark_atmost_restricted_ancestors_as_insufficient(
                        critical_con_des,
                        functionally_restricted_successor_node,
                        &functionally_restricted_successor_creation_role_linker,
                        indi_proc_sat_node,
                        calc_alg_context,
                    );
                    self.update_direct_adding_individual_status_flags(
                        *indi_proc_sat_node,
                        IndividualSaturationProcessNodeStatusFlags::INDSATFLAGCARDINALITYPROPLEMATIC,
                        calc_alg_context,
                    );
                }
            }
            self.release_concept_saturation_process_linker(critical_con_proc_des, calc_alg_context);
        }

        // ---- 3. CCT_VALUE (cpp 3096-3120) ----
        loop {
            let (insufficient, clashed) = indirect_flags!();
            if insufficient || clashed {
                break;
            }
            let Some((critical_con_proc_des, critical_con_des, already_tested)) =
                take_untested!(CriticalSaturationConceptQueueType::Value)
            else {
                break;
            };
            if !already_tested {
                if self.is_critical_value_concept_descriptor_insufficient(
                    critical_con_des,
                    indi_proc_sat_node,
                    calc_alg_context,
                ) {
                    self.insufficient_value_count += 1;
                    self.update_direct_adding_individual_status_flags(
                        *indi_proc_sat_node,
                        IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT,
                        calc_alg_context,
                    );
                    self.set_insufficient_node_occured(calc_alg_context);
                } else {
                    self.add_critical_concept_for_dependent_nodes(
                        critical_con_des,
                        CCT_VALUE,
                        indi_proc_sat_node,
                        false,
                        IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT,
                        calc_alg_context,
                    );
                }
            }
            self.release_concept_saturation_process_linker(critical_con_proc_des, calc_alg_context);
        }

        // ---- 4. CCT_NOMINAL (cpp 3124-3148) ----
        loop {
            let (insufficient, clashed) = indirect_flags!();
            if insufficient || clashed {
                break;
            }
            let Some((critical_con_proc_des, critical_con_des, already_tested)) =
                take_untested!(CriticalSaturationConceptQueueType::Nominal)
            else {
                break;
            };
            if !already_tested {
                if self.is_critical_nominal_concept_descriptor_insufficient(
                    critical_con_des,
                    indi_proc_sat_node,
                    calc_alg_context,
                ) {
                    self.insufficient_nominal_count += 1;
                    self.update_direct_adding_individual_status_flags(
                        *indi_proc_sat_node,
                        IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT,
                        calc_alg_context,
                    );
                    self.set_insufficient_node_occured(calc_alg_context);
                } else {
                    self.add_critical_concept_for_dependent_nodes(
                        critical_con_des,
                        CCT_NOMINAL,
                        indi_proc_sat_node,
                        false,
                        IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT,
                        calc_alg_context,
                    );
                }
            }
            self.release_concept_saturation_process_linker(critical_con_proc_des, calc_alg_context);
        }

        // ---- 5. CCT_DISJUNCTION (cpp 3153-3177) — guarded by !clashed only ----
        loop {
            let (_, clashed) = indirect_flags!();
            if clashed {
                break;
            }
            let Some((critical_con_proc_des, critical_con_des, already_tested)) =
                take_untested!(CriticalSaturationConceptQueueType::Disjunction)
            else {
                break;
            };
            if !already_tested {
                if self.is_critical_or_concept_descriptor_insufficient(
                    critical_con_des,
                    indi_proc_sat_node,
                    calc_alg_context,
                ) {
                    // KONCLUDE-PORT-NOTE[conservative]: the C++ pairs updateDirectNot-
                    // DependentAdding(INSUFFICIENT) with addCriticalORConceptTestedFor-
                    // DependentNodes (mark + tested-pair insert on every copy-depending
                    // node). That fan-out is deferred; the dependent-walking update below
                    // marks the same depending set (transitively) INSUFFICIENT — a
                    // conservative superset that only skips the tested-pair dedup.
                    self.insufficient_or_count += 1;
                    self.update_direct_adding_individual_status_flags(
                        *indi_proc_sat_node,
                        IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT,
                        calc_alg_context,
                    );
                    self.set_insufficient_node_occured(calc_alg_context);
                }
            }
            self.release_concept_saturation_process_linker(critical_con_proc_des, calc_alg_context);
        }

        // ---- 6. CCT_EQCANDIDATE (cpp 3169-3188) — guarded by !clashed only ----
        loop {
            let (_, clashed) = indirect_flags!();
            if clashed {
                break;
            }
            let Some((critical_con_proc_des, critical_con_des, already_tested)) =
                take_untested!(CriticalSaturationConceptQueueType::EqCandidate)
            else {
                break;
            };
            if !already_tested {
                if self.is_critical_eqcand_concept_descriptor_problematic(
                    critical_con_des,
                    indi_proc_sat_node,
                    calc_alg_context,
                ) {
                    self.insufficient_eqcand_count += 1;
                    self.update_direct_not_dependent_adding_individual_status_flags(
                        *indi_proc_sat_node,
                        IndividualSaturationProcessNodeStatusFlags::INDSATFLAGEQCANDPROPLEMATIC,
                        calc_alg_context,
                    );
                    self.set_problematic_eq_candidate_occured(calc_alg_context);
                    self.add_critical_concept_for_dependent_nodes(
                        critical_con_des,
                        CCT_EQCANDIDATE,
                        indi_proc_sat_node,
                        true,
                        0,
                        calc_alg_context,
                    );
                }
            }
            self.release_concept_saturation_process_linker(critical_con_proc_des, calc_alg_context);
        }
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::addCriticalConceptDescriptor`
    /// (cpp 3386–3406).
    pub fn add_critical_concept_descriptor(
        &mut self,
        con_des: ConceptSaturationDescriptorId,
        concept_type: Cint64,
        indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        if self.conf_add_critical_concepts_to_queues {
            // STATINC(SATURATIONCRITICALADDCOUNT, calcAlgContext);
            if let Some(queue_type) = Self::critical_concept_queue_type(concept_type) {
                let con_des_pro_linker_payload =
                    self.create_concept_saturation_process_linker(calc_alg_context);
                let con_des_pro_linker =
                    ConceptSaturationProcessLinkerId::new(con_des_pro_linker_payload.raw);
                calc_alg_context
                    .process_context_mut()
                    .con_sat_proc_linker_mut(con_des_pro_linker)
                    .init_concept_saturation_process_linker(con_des);

                let queues = calc_alg_context
                    .process_context_mut()
                    .sat_node_ext_critical_concept_type_queues(*indi_proc_sat_node, true);
                let critical_concept_queue = calc_alg_context
                    .process_context_mut()
                    .critical_sat_concept_type_queues_get_critical_saturation_concept_queue(
                        queues, queue_type, true,
                    );
                calc_alg_context
                    .process_context_mut()
                    .critical_sat_concept_queue_add_critical_concept_descriptor_linker(
                        critical_concept_queue,
                        con_des_pro_linker,
                    );

                let process_node_queued = calc_alg_context
                    .process_context()
                    .critical_sat_concept_type_queues(queues)
                    .is_process_node_queued();
                if !process_node_queued {
                    let critical_ind_node_proc_queue =
                        calc_alg_context.saturation_critical_individual_node_processing_queue(true);
                    let individual_id = calc_alg_context
                        .process_context()
                        .sat_node(*indi_proc_sat_node)
                        .get_individual_id();
                    calc_alg_context
                        .process_context_mut()
                        .sat_critical_ind_node_proc_queue_mut(critical_ind_node_proc_queue)
                        .insert_process_individual(*indi_proc_sat_node, individual_id);
                    calc_alg_context
                        .process_context_mut()
                        .critical_sat_concept_type_queues_mut(queues)
                        .set_process_node_queued(true);
                }
            }
        }
        if self.conf_directly_critical_to_insufficient {
            // KONCLUDE-PORT-NOTE[api]: C++ passes the member `mCalcAlgContext` here (an
            //   opaque alias of the threaded context); the port uses the threaded
            //   `calc_alg_context` consistently.
            self.update_direct_adding_individual_status_flags(
                *indi_proc_sat_node,
                IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT,
                calc_alg_context,
            );
            self.set_insufficient_node_occured(calc_alg_context);
        }
    }

    fn critical_concept_queue_type(
        concept_type: Cint64,
    ) -> Option<CriticalSaturationConceptQueueType> {
        match concept_type {
            CCT_FORALL => Some(CriticalSaturationConceptQueueType::Forall),
            CCT_ATMOST => Some(CriticalSaturationConceptQueueType::Atmost),
            CCT_DISJUNCTION => Some(CriticalSaturationConceptQueueType::Disjunction),
            CCT_EQCANDIDATE => Some(CriticalSaturationConceptQueueType::EqCandidate),
            CCT_VALUE => Some(CriticalSaturationConceptQueueType::Value),
            CCT_NOMINAL => Some(CriticalSaturationConceptQueueType::Nominal),
            _ => None,
        }
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::testInsufficientALLConcepts`
    /// (cpp 3412–3458).
    ///
    /// KONCLUDE-PORT-NOTE[api]: a debug-only consistency assertion — it re-collects
    /// linked successors and, for every backward-propagation ALL operand missing from
    /// a successor's label, dumps the saturation model to `saturation-model.txt` and
    /// trips a `bool bug = true` breakpoint. The dump/breakpoint carry no calculus
    /// effect; only the `collectLinkedSuccessorNodes` re-collection is a live leaf.
    pub fn test_insufficient_all_concepts(
        &mut self,
        indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // collectLinkedSuccessorNodes(indiProcSatNode, calcAlgContext);
        self.collect_linked_successor_nodes(indi_proc_sat_node, calc_alg_context, INVALID);
        // W4-DEFER[api]: the verification walk over the unported CLinkedRoleSaturationSuccessorHash
        //   / CRoleBackwardSaturationPropagationHash + CSaturationIndividualNodeSuccessorExtensionData
        //   + per-successor CReapplyConceptSaturationLabelSet; on a missing operand it builds the
        //   debug model string (generateExtendedDebugIndiModelStringList), writes saturation-model.txt
        //   and trips `bool bug = true`. Deferred whole — no calculus state change, debug-only.
        //
        //   CLinkedRoleSaturationSuccessorHash* linkedSuccHash = indiProcSatNode->getLinkedRoleSuccessorHash(false);
        //   CRoleBackwardSaturationPropagationHash* backwardPropHash = indiProcSatNode->getRoleBackwardPropagationHash(false);
        //   if (backwardPropHash && linkedSuccHash) { ...for each active successor + backward-prop ALL operand:
        //       if (!succConSet || !succConSet->containsConcept(opConcept, opNegation)) { dump+breakpoint } }
    }

    // =======================================================================
    // Group H — per-descriptor insufficiency tests (cpp 3462–4933)
    // =======================================================================

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::isCriticalALLConceptDescriptorInsufficient`
    /// (cpp 3462–3578). True iff some `∀r.C` successor (or matching asserted data-role,
    /// or VALUE-nominal connection) lacks a required operand in its saturated label.
    pub fn is_critical_all_concept_descriptor_insufficient(
        &mut self,
        con_des: ConceptSaturationDescriptorId,
        indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // STATINC(SATURATIONCRITICALALLCOUNT, calcAlgContext);
        // if (!indiProcSatNode->hasSubstituteIndividualNode()) {
        let has_substitute = calc_alg_context
            .process_context_mut()
            .sat_node_mut(*indi_proc_sat_node)
            .has_substitute_individual_node();
        if !has_substitute {
            // CConcept* concept = conDes->getConcept(); bool conceptNegation = conDes->isNegated();
            let concept = calc_alg_context
                .process_context()
                .con_sat_desc(con_des)
                .get_concept();
            let concept_negation = calc_alg_context
                .process_context()
                .con_sat_desc(con_des)
                .get_negation();
            // CRole* role = concept->getRole();
            let role = calc_alg_context.ontology_arenas().concept(concept).get_role();

            // if (role->isDataRole() && indiProcSatNode->getIndividualExtensionData(false)) { ... }
            // KONCLUDE-PORT-NOTE[conservative]: the asserted-data-role walk over
            // CLinkedDataValueAssertionSaturationData is deferred — a data-role ∀ is
            // reported insufficient outright (the C++ returns true exactly when a
            // matching assertion exists; without the walk, assuming "exists" is the
            // sound direction and only defers the subject to the tableau probe).
            if role.is_some()
                && calc_alg_context.ontology_arenas().role(role).is_data_role()
            {
                return true;
            }

            // collectLinkedSuccessorNodes(indiProcSatNode, calcAlgContext);
            self.collect_linked_successor_nodes(indi_proc_sat_node, calc_alg_context, INVALID);
            // CLinkedRoleSaturationSuccessorHash* linkedSuccHash = indiProcSatNode->getLinkedRoleSuccessorHash(false);
            let linked_succ_hash =
                IndividualSaturationProcessNode::get_linked_role_successor_hash_in_context(
                    calc_alg_context.process_context_mut(),
                    *indi_proc_sat_node,
                    false,
                );
            if linked_succ_hash.is_some() {
                // CLinkedRoleSaturationSuccessorData* succData = succHash->value(role);
                let succ_data = calc_alg_context
                    .process_context()
                    .linked_role_sat_succ_hash(linked_succ_hash)
                    .role_succ_data_hash
                    .get(&role)
                    .copied();
                if let Some(succ_data) = succ_data.filter(|d| d.is_some()) {
                    let indi_succ_datas: Vec<SaturationSuccessorDataId> = calc_alg_context
                        .process_context()
                        .linked_role_sat_succ_data(succ_data)
                        .succ_node_data_map
                        .values()
                        .copied()
                        .collect();
                    for indi_succ_data in indi_succ_datas {
                        let (active, value_nominal_connection, succ_node) = {
                            let d = calc_alg_context
                                .process_context()
                                .sat_succ_data(indi_succ_data);
                            (
                                d.active_count >= 1,
                                d.value_nominal_connection,
                                d.succ_indi_node,
                            )
                        };
                        if !active {
                            continue;
                        }
                        if value_nominal_connection {
                            // KONCLUDE-PORT-NOTE[conservative]: the C++ checks the
                            // corrected completion-graph nominal node's label under
                            // isConsistenceDataAvailable (and silently skips without
                            // consistence data — impossible there, saturation runs
                            // after ABox consistency). The getCorrectedNode label walk
                            // is deferred; a VALUE-nominal-connected successor is
                            // reported insufficient outright — sound defer.
                            return true;
                        }
                        // succConSet = succNode->getReapplyConceptSaturationLabelSet(false);
                        let succ_con_set = calc_alg_context
                            .process_context()
                            .sat_node(succ_node)
                            .reapply_con_sat_label_set;
                        let mut operants_contained = succ_con_set.is_some();
                        if operants_contained {
                            let op_linker: Vec<NegLink<ConceptId>> = calc_alg_context
                                .ontology_arenas()
                                .concept(concept)
                                .get_operand_list()
                                .to_vec();
                            for op_linker_it in op_linker {
                                // succConSet->containsConcept(opConcept, opLinker->isNegated() ^ conceptNegation)
                                let contained = Self::sat_label_set_contains_concept_get_negation(
                                    succ_con_set,
                                    op_linker_it.target,
                                    calc_alg_context,
                                ) == Some(op_linker_it.negated ^ concept_negation);
                                if !contained {
                                    operants_contained = false;
                                    break;
                                }
                            }
                        }
                        if !operants_contained {
                            return true;
                        }
                    }
                }
            }
        }
        false
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::isCriticalORConceptDescriptorInsufficient`
    /// (cpp 3582–3602). True iff NO disjunct (under disjunct-checking-concept
    /// substitution) is present in the node's saturated label.
    pub fn is_critical_or_concept_descriptor_insufficient(
        &mut self,
        con_des: ConceptSaturationDescriptorId,
        indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // STATINC(SATURATIONCRITICALORCOUNT, calcAlgContext);
        // CConcept* concept = conDes->getConcept(); bool conceptNegation = conDes->isNegated();
        let concept = calc_alg_context
            .process_context()
            .con_sat_desc(con_des)
            .get_concept();
        let concept_negation = calc_alg_context
            .process_context()
            .con_sat_desc(con_des)
            .get_negation();
        // CReapplyConceptSaturationLabelSet* conSet = indiProcSatNode->getReapplyConceptSaturationLabelSet(false);
        let con_set = calc_alg_context
            .process_context()
            .sat_node(*indi_proc_sat_node)
            .reapply_con_sat_label_set;
        if con_set.is_some() {
            let op_linker: Vec<NegLink<ConceptId>> = calc_alg_context
                .ontology_arenas()
                .concept(concept)
                .get_operand_list()
                .to_vec();
            for op_linker_it in op_linker {
                let op_concept = op_linker_it.target; // getData()
                let op_concept_negation = op_linker_it.negated ^ concept_negation;

                let mut checking_negation = op_concept_negation;
                let op_checking_concept = self.get_disjunct_checking_concept(
                    op_concept,
                    op_concept_negation,
                    Some(&mut checking_negation),
                    calc_alg_context,
                );

                // conSet->containsConcept(opCheckingConcept, checkingNegation)
                let contained = Self::sat_label_set_contains_concept_get_negation(
                    con_set,
                    op_checking_concept,
                    calc_alg_context,
                ) == Some(checking_negation);
                if contained {
                    return false;
                }
            }
        }
        true
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::isCriticalEQCANDConceptDescriptorProblematic`
    /// (cpp 3606–3622). Like the OR test but without disjunct-checking substitution:
    /// problematic iff NO operand is present in the node's saturated label.
    pub fn is_critical_eqcand_concept_descriptor_problematic(
        &mut self,
        con_des: ConceptSaturationDescriptorId,
        indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // STATINC(SATURATIONCRITICALORCOUNT, calcAlgContext);
        // CConcept* concept = conDes->getConcept(); bool conceptNegation = conDes->isNegated();
        let concept = calc_alg_context
            .process_context()
            .con_sat_desc(con_des)
            .get_concept();
        let concept_negation = calc_alg_context
            .process_context()
            .con_sat_desc(con_des)
            .get_negation();
        // CReapplyConceptSaturationLabelSet* conSet = indiProcSatNode->getReapplyConceptSaturationLabelSet(false);
        let con_set = calc_alg_context
            .process_context()
            .sat_node(*indi_proc_sat_node)
            .reapply_con_sat_label_set;
        if con_set.is_some() {
            let op_linker: Vec<NegLink<ConceptId>> = calc_alg_context
                .ontology_arenas()
                .concept(concept)
                .get_operand_list()
                .to_vec();
            for op_linker_it in op_linker {
                // conSet->containsConcept(opConcept, opLinker->isNegated() ^ conceptNegation)
                let contained = Self::sat_label_set_contains_concept_get_negation(
                    con_set,
                    op_linker_it.target,
                    calc_alg_context,
                ) == Some(op_linker_it.negated ^ concept_negation);
                if contained {
                    return false;
                }
            }
        }
        true
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::isCriticalATMOSTConceptDescriptorInsufficient`
    /// (cpp 3625–3770). The SHIQ-hard cardinality test: counts the relevant `≤n r.C`
    /// successors, attempts trivial / detailed cardinality merging, and reports
    /// whether the unmergeable cardinality exceeds the bound (insufficient) or meets
    /// it (ancestor possibly critical), surfacing the functionally-restricted
    /// successor for the bound==1 case.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: the C++ out-params
    /// `bool& ancestorPossiblyCriticalFlag`, `CIndividualSaturationProcessNode*& functionallyRestrictedSuccessorNode`
    /// and `CXNegLinker<CRole*>*& functionallyRestrictedSuccessorCreationRoleLinker`
    /// become `&mut bool`, `&mut SatNodeId` and `&mut Cint64` (the role-linker chain
    /// is an unported satellite, carried as an opaque `Cint64` handle).
    pub fn is_critical_atmost_concept_descriptor_insufficient(
        &mut self,
        con_des: ConceptSaturationDescriptorId,
        ancestor_possibly_critical_flag: &mut bool,
        functionally_restricted_successor_node: &mut SatNodeId,
        functionally_restricted_successor_creation_role_linker: &mut Vec<NegLink<RoleId>>,
        indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // STATINC(SATURATIONCRITICALATMOSTCOUNT, calcAlgContext);
        let (concept, concept_negation) = {
            let con_des_ref = calc_alg_context.process_context().con_sat_desc(con_des);
            (con_des_ref.get_concept(), con_des_ref.get_negation())
        };
        // CRole* role = concept->getRole();
        // cint64 allowedCardinality = concept->getParameter() - 1*conceptNegation;
        let (role, allowed_cardinality) = {
            let concept_ref = calc_alg_context.ontology_arenas().concept(concept);
            (
                concept_ref.get_role(),
                concept_ref.get_parameter() - Cint64::from(concept_negation),
            )
        };
        if allowed_cardinality < 0 {
            return true;
        }

        let mut found_cardinality: Cint64 = 0;
        // if (!indiProcSatNode->hasSubstituteIndividualNode()) {
        let has_substitute = calc_alg_context
            .process_context_mut()
            .sat_node_mut(*indi_proc_sat_node)
            .has_substitute_individual_node();
        if !has_substitute {
            // if (role->isDataRole() && indiProcSatNode->getIndividualExtensionData(false)) { ... }
            // KONCLUDE-PORT-NOTE[conservative]: the asserted data-value walk over
            // CLinkedDataValueAssertionSaturationData is deferred — a data-role ≤n
            // is reported insufficient outright (the C++ counts matching asserted
            // data roles against the bound; assuming "over the bound" is the sound
            // direction and only defers the subject to the tableau probe).
            if role.is_some() && calc_alg_context.ontology_arenas().role(role).is_data_role() {
                return true;
            }

            // collectLinkedSuccessorNodes(indiProcSatNode, calcAlgContext);
            self.collect_linked_successor_nodes(indi_proc_sat_node, calc_alg_context, INVALID);
            // CLinkedRoleSaturationSuccessorHash* linkedSuccHash = indiProcSatNode->getLinkedRoleSuccessorHash(false);
            let linked_succ_hash =
                IndividualSaturationProcessNode::get_linked_role_successor_hash_in_context(
                    calc_alg_context.process_context_mut(),
                    *indi_proc_sat_node,
                    false,
                );
            if linked_succ_hash.is_some() {
                let mut min_cardinality: Cint64 = 0;
                let mut merging_succ_data_linker = IndividualSaturationSuccessorLinkDataLinkerId::NONE;

                // CLinkedRoleSaturationSuccessorData* succData = succHash->value(role);
                let succ_data = calc_alg_context
                    .process_context()
                    .linked_role_sat_succ_hash(linked_succ_hash)
                    .role_succ_data_hash
                    .get(&role)
                    .copied();
                if let Some(succ_data) = succ_data.filter(|d| d.is_some()) {
                    // if (succData->mSuccCount >= allowedCardinality) {
                    let succ_count = calc_alg_context
                        .process_context()
                        .linked_role_sat_succ_data(succ_data)
                        .succ_count;
                    if succ_count >= allowed_cardinality {
                        let mut last_successor_node = SatNodeId::NONE;
                        let mut last_successor_creation_role_linker: Vec<NegLink<RoleId>> =
                            Vec::new();

                        found_cardinality += self.collect_atmost_concept_relevant_successors(
                            con_des,
                            indi_proc_sat_node,
                            succ_data,
                            &mut merging_succ_data_linker,
                            &mut last_successor_node,
                            &mut last_successor_creation_role_linker,
                            &mut min_cardinality,
                            calc_alg_context,
                        );

                        let mut mergeable_cardinality: Cint64 = 0;
                        if found_cardinality >= allowed_cardinality && found_cardinality > 1 {
                            // check whether some trivial merging is possible
                            let mut remain_mergeable_card_hash: std::collections::HashMap<
                                SaturationSuccessorDataId,
                                Cint64,
                            > = std::collections::HashMap::new();
                            let mut merge_distint_hash: std::collections::HashMap<
                                SaturationSuccessorDataId,
                                Vec<SaturationSuccessorDataId>,
                            > = std::collections::HashMap::new();
                            let mut merge_distint_set: std::collections::HashSet<(
                                SaturationSuccessorDataId,
                                SaturationSuccessorDataId,
                            )> = std::collections::HashSet::new();

                            if merging_succ_data_linker.is_some() {
                                if self.conf_simple_merging_test_for_atmost_critical_testing {
                                    let mut merging_it = merging_succ_data_linker;
                                    while merging_it.is_some()
                                        && found_cardinality - mergeable_cardinality
                                            >= allowed_cardinality
                                    {
                                        let (succ_link_data, next_linker) = {
                                            let linker = calc_alg_context
                                                .process_context()
                                                .indi_sat_succ_link_data_linker(merging_it);
                                            (linker.get_data(), linker.get_next())
                                        };
                                        let link_succ_count = calc_alg_context
                                            .process_context()
                                            .sat_succ_data(succ_link_data)
                                            .succ_count;
                                        if link_succ_count >= 1 {
                                            let max_required_merging_cardinality = found_cardinality
                                                - mergeable_cardinality
                                                - (allowed_cardinality - 1);
                                            let merging_cardinality = self
                                                .get_successor_link_simply_mergeable_cardinality_count(
                                                    indi_proc_sat_node,
                                                    succ_link_data,
                                                    merging_succ_data_linker,
                                                    &mut remain_mergeable_card_hash,
                                                    role,
                                                    max_required_merging_cardinality,
                                                    &mut merge_distint_hash,
                                                    &mut merge_distint_set,
                                                    calc_alg_context,
                                                );
                                            let remaining_cardinality =
                                                link_succ_count - merging_cardinality;
                                            remain_mergeable_card_hash
                                                .insert(succ_link_data, remaining_cardinality);
                                            mergeable_cardinality += merging_cardinality;
                                        }
                                        merging_it = next_linker;
                                    }
                                }

                                if self.conf_detailed_merging_test_for_atmost_critical_testing
                                    && found_cardinality - mergeable_cardinality
                                        >= allowed_cardinality
                                    && found_cardinality - mergeable_cardinality
                                        <= allowed_cardinality * 2
                                {
                                    let mut merging_it = merging_succ_data_linker;
                                    while merging_it.is_some()
                                        && found_cardinality - mergeable_cardinality
                                            >= allowed_cardinality
                                    {
                                        let (succ_link_data, next_linker) = {
                                            let linker = calc_alg_context
                                                .process_context()
                                                .indi_sat_succ_link_data_linker(merging_it);
                                            (linker.get_data(), linker.get_next())
                                        };
                                        let link_succ_count = calc_alg_context
                                            .process_context()
                                            .sat_succ_data(succ_link_data)
                                            .succ_count;
                                        if link_succ_count >= 1 {
                                            // remainMergeableCardHash->value(succLinkData, succLinkData->mSuccCount)
                                            let succ_remaining_cardinality =
                                                *remain_mergeable_card_hash
                                                    .get(&succ_link_data)
                                                    .unwrap_or(&link_succ_count);
                                            if succ_remaining_cardinality > 0 {
                                                let max_required_merging_cardinality =
                                                    found_cardinality
                                                        - mergeable_cardinality
                                                        - (allowed_cardinality - 1);
                                                let merging_cardinality = self
                                                    .get_successor_link_extended_mergeable_cardinality_count(
                                                        indi_proc_sat_node,
                                                        succ_link_data,
                                                        None,
                                                        next_linker,
                                                        &mut remain_mergeable_card_hash,
                                                        role,
                                                        max_required_merging_cardinality,
                                                        &mut merge_distint_hash,
                                                        &mut merge_distint_set,
                                                        calc_alg_context,
                                                    );
                                                if merging_cardinality > 0 {
                                                    let new_succ_card = succ_remaining_cardinality
                                                        .max(merging_cardinality);
                                                    remain_mergeable_card_hash
                                                        .insert(succ_link_data, new_succ_card);
                                                    let removed_succ_card =
                                                        succ_remaining_cardinality
                                                            .min(merging_cardinality);
                                                    mergeable_cardinality += removed_succ_card;
                                                }
                                            }
                                        }
                                        merging_it = next_linker;
                                    }
                                }
                            }
                            if merging_succ_data_linker.is_some() {
                                self.release_individual_saturation_successor_link_data_linker(
                                    merging_succ_data_linker,
                                    calc_alg_context,
                                );
                            }
                        }

                        if found_cardinality - mergeable_cardinality == allowed_cardinality
                            || min_cardinality >= allowed_cardinality
                        {
                            *ancestor_possibly_critical_flag = true;
                            if allowed_cardinality == 1 {
                                *functionally_restricted_successor_node = last_successor_node;
                                *functionally_restricted_successor_creation_role_linker =
                                    last_successor_creation_role_linker;
                            }
                        }
                        if found_cardinality - mergeable_cardinality > allowed_cardinality {
                            return true;
                        }
                    }
                }
            }
        }
        false
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::isCriticalNOMINALConceptDescriptorInsufficient`
    /// (cpp 4843–4873). True iff the cached completion-graph nominal node carries a
    /// non-deterministic concept (beyond the deterministic prefix) that the saturated
    /// node label lacks — or the nominal node / consistence data is unavailable.
    pub fn is_critical_nominal_concept_descriptor_insufficient(
        &mut self,
        con_des: ConceptSaturationDescriptorId,
        indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // CConcept* concept = conDes->getConcept(); CRole* role = concept->getRole();
        // CIndividual* nominal = concept->getNominalIndividual(); cint64 nominalID = nominal->getIndividualID();
        // if (isConsistenceDataAvailable(calcAlgContext)) {
        if self.is_consistence_data_available(calc_alg_context) {
            // W4-DEFER[api]: `concept->getNominalIndividual()->getIndividualID()` is an unported
            //   `CConcept`/`CIndividual` deref, so `nominalID` (the getCorrectedNode key) is deferred;
            //   the body then walks the cached det/non-det completion-graph nominal nodes:
            //   detNominalProcessNode = getCorrectedNode(nominalID, mDetCachedCGIndiVector, mCalcAlgContext);
            //   if (!detNominalProcessNode) return true;
            //   nonDetNominalProcessNode = getCorrectedNode(nominalID, mNonDetCachedCGIndiVector, mCalcAlgContext);
            //   detNominalReapplyConSet = detNominalProcessNode->getReapplyConceptLabelSet(false);
            //   nonDetNominalReapplyConSet = nonDetNominalProcessNode->getReapplyConceptLabelSet(false);
            //   satIndiNodeConSet = indiProcSatNode->getReapplyConceptSaturationLabelSet(false);
            //   lastDetConDesIt = detNominalReapplyConSet->getAddingSortedConceptDescriptionLinker();
            //   for (conDesIt = nonDetNominalReapplyConSet->getAddingSortedConceptDescriptionLinker();
            //        conDesIt && conDesIt != lastDetConDesIt; conDesIt = conDesIt->getNext())
            //       if (!satIndiNodeConSet->containsConcept(conDesIt->getConcept(), conDesIt->isNegated())) return true;
            //   return false;
            //   Live leaf: `self.get_corrected_node` (group C) over the cached det/non-det
            //   CG vectors `det_cached_cg_indi_vector` / `non_det_cached_cg_indi_vector`; the
            //   label sets + `containsConcept` are unported satellites.
            //
            // KONCLUDE-PORT-NOTE[conservative]: the deferred verdict must be
            // INSUFFICIENT (true), not the C++ all-checks-passed default (false):
            // assuming the cached nominal node carries no extra non-deterministic
            // concept without actually checking would let a nominal-dependent node
            // complete SAT-certain — unsound. Sound defer instead.
            let _ = (con_des, *indi_proc_sat_node);
            true
        } else {
            true
        }
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::isCriticalVALUEConceptDescriptorInsufficient`
    /// (cpp 4876–4933). Inspects the cached non-deterministic nominal node's reapply
    /// role-successor hash for super-role re-applications whose ALL/AQALL/SOME operands
    /// (deterministically held on the nominal) are not yet propagated into the saturated
    /// node — surfacing missing automaton transitions where needed.
    pub fn is_critical_value_concept_descriptor_insufficient(
        &mut self,
        con_des: ConceptSaturationDescriptorId,
        indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // CConcept* concept = conDes->getConcept(); CRole* role = concept->getRole();
        // CIndividual* nominal = concept->getNominalIndividual(); cint64 nominalID = nominal->getIndividualID();
        // if (isConsistenceDataAvailable(calcAlgContext)) {
        if self.is_consistence_data_available(calc_alg_context) {
            // W4-DEFER[api]: walks the cached non-det nominal node's CReapplyRoleSuccessorHash
            //   over each non-inverse super-role of `role`; for a deterministically-held,
            //   non-negated reapply concept it returns true on a PROPAGATION_ALL trigger, on a
            //   missing ALL/AQALL (or ¬SOME) operand in the saturated node label, or on an
            //   unhandled operator code; an AQAND trigger calls the sibling
            //   `testAutomateTransitionOperandsAddable`. The `CConcept`/`CRole`/`CIndividual`
            //   derefs, the getCorrectedNode label sets, the CReapplyRoleSuccessorHash reapply
            //   iterator and the CConceptOperator flag tests are unported satellites. Faithful body:
            //
            //   detNominalProcessNode = getCorrectedNode(nominalID, mDetCachedCGIndiVector, mCalcAlgContext);
            //   if (detNominalProcessNode) {
            //       nonDetNominalProcessNode = getCorrectedNode(nominalID, mNonDetCachedCGIndiVector, mCalcAlgContext);
            //       detNominalReapplyConSet = detNominalProcessNode->getReapplyConceptLabelSet(false);
            //       nonDetNominalReapplyRoleSuccHash = nonDetNominalProcessNode->getReapplyRoleSuccessorHash(false);
            //       satIndiNodeConSet = indiProcSatNode->getReapplyConceptSaturationLabelSet(false);
            //       if (nonDetNominalReapplyRoleSuccHash) for (superRoleIt : role->getIndirectSuperRoleList()) if (!inversed) {
            //           for (reapplyDes : nonDetNominalReapplyRoleSuccHash->getRoleReapplyIterator(superRole)) {
            //               reapplyConDes = reapplyDes->getConceptDescriptor(); reapplyConcept = reapplyConDes->getConcept();
            //               if (!reapplyConDes->isNegated() && detNominalReapplyConSet->containsConcept(reapplyConcept, false)) {
            //                   reapplyConceptOperator = reapplyConcept->getConceptOperator();
            //                   if (CCFS_PROPAGATION_ALL_TYPE) return true;
            //                   else if (CCFS_ALL_AQALL_TYPE || (negated && CCSOME))
            //                       for (op : reapplyConcept->getOperandList())
            //                           if (!satIndiNodeConSet->containsConcept(op, op.neg ^ reapplyNeg)) return true;
            //                   else if (CCFS_AQAND_TYPE) testAutomateTransitionOperandsAddable(indiProcSatNode, reapplyConcept, role, mCalcAlgContext);
            //                   else return true;
            //                   return false;
            //               }
            //           }
            //       }
            //   }
            //   return false;
            //   Live leaves: `self.get_corrected_node` (group C), `self.test_automate_transition_operands_addable`
            //   (group D, s03).
            //
            // KONCLUDE-PORT-NOTE[conservative]: the deferred verdict must be
            // INSUFFICIENT (true), not the C++ all-checks-passed default (false):
            // assuming no super-role reapplication is pending on the cached nominal
            // node without walking it would let a VALUE-connected node complete
            // SAT-certain — unsound. Sound defer instead.
            let _ = (con_des, *indi_proc_sat_node);
            true
        } else {
            true
        }
    }

    // =======================================================================
    // Group I — disjunct common-concept extraction (cpp 4936–5018)
    // =======================================================================

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::updateExtractDisjunctCommonConcept`
    /// (cpp 4936–4965). Re-scans each tracked disjunct node's newly-added saturation
    /// descriptors and, when a concept's common-occurrence count across all disjuncts
    /// reaches the disjunct count, folds it into the disjunction node's label (the OR
    /// over-approximation common-concept extraction).
    pub fn update_extract_disjunct_common_concept(
        &mut self,
        indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // CSaturationConceptDataItem* conceptSatItem = (CSaturationConceptDataItem*)indiProcSatNode->getSaturationConceptReferenceLinking();
        // CConcept* disjunctionConcept = conceptSatItem->getSaturationConcept();
        // bool disjunctionNegation = conceptSatItem->getSaturationNegation();
        // CSortedNegLinker<CConcept*>* disjunctConceptLinker = disjunctionConcept->getOperandList();
        // CSaturationDisjunctCommonConceptExtractionData* extractionData = indiProcSatNode->getDisjunctCommonConceptExtractionData(false);
        let extraction_data = calc_alg_context
            .process_context_mut()
            .sat_node_ext_disjunct_common_concept_extraction_data(*indi_proc_sat_node, false);
        if extraction_data.is_some() {
            // W4-DEFER[api]: walks the unported CSaturationDisjunctCommonConceptExtractionData
            //   (its CSaturationDisjunctCommonConceptCountHash + CSaturationDisjunctExtractionLinker
            //   chain) and, per disjunct node, the newly-added CConceptSaturationDescriptor span,
            //   incrementing the common-count; on reaching the max it adds the common concept to the
            //   disjunction node's label via the live sibling `addConceptFilteredToIndividual`
            //   (group K). Faithful body:
            //
            //   disjunctionConSet = indiProcSatNode->getReapplyConceptSaturationLabelSet(true);
            //   commonConceptCountHash = extractionData->getSaturationDisjunctCommonConceptCountHash();
            //   for (satDisjExtLinkerIt : extractionData->getDisjunctIndividualNodeExtractionLinker()) {
            //       disjConIndiNode = satDisjExtLinkerIt->getDisjunctIndividualSaturationProcessNode();
            //       lastExaminedDisjConSatDes = satDisjExtLinkerIt->getLastExaminedConceptSaturationDescriptor();
            //       disjConConSet = disjConIndiNode->getReapplyConceptSaturationLabelSet(false);
            //       if (disjConConSet) {
            //           newLast = disjConConSet->getConceptSaturationDescriptionLinker();
            //           satDisjExtLinkerIt->setLastExaminedConceptSaturationDescriptor(newLast);
            //           for (disjConSatDesIt = newLast; disjConSatDesIt != lastExaminedDisjConSatDes; disjConSatDesIt = disjConSatDesIt->getNext())
            //               if (commonConceptCountHash->incCommonConceptCountReturnMaxReached(disjConSatDesIt))
            //                   addConceptFilteredToIndividual(disjConSatDesIt->getConcept(), disjConSatDesIt->isNegated(),
            //                       indiProcSatNode, disjunctionConSet, true, calcAlgContext);
            //       }
            //   }
        }
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::initializeExtractDisjunctCommonConcept`
    /// (cpp 4970–5005). Seeds the disjunct-common-concept extraction: for every disjunct
    /// of the node's disjunction concept it resolves the per-disjunct saturation node,
    /// enqueues it uninitialized, registers an extraction linker + a modified-process
    /// update hook, records the disjunct count, then runs the first update pass.
    pub fn initialize_extract_disjunct_common_concept(
        &mut self,
        indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // CMemoryAllocationManager* taskMemMan = calcAlgContext->getUsedProcessTaskMemoryAllocationManager();
        // CSaturationDisjunctCommonConceptExtractionData* extractionData = indiProcSatNode->getDisjunctCommonConceptExtractionData(true);
        let _extraction_data = calc_alg_context
            .process_context_mut()
            .sat_node_ext_disjunct_common_concept_extraction_data(*indi_proc_sat_node, true);
        // W4-DEFER[api]: resolves the node's disjunction concept (CSaturationConceptDataItem
        //   ->getSaturationConcept()/getSaturationNegation()) and, per disjunct operand, the
        //   per-disjunct saturation node via the concept-reference linking (getConceptSaturationReferenceLinkingData
        //   ->getIndividualProcessNodeForConcept), then wires the extraction satellites.
        //   The `CConcept`/`CSaturationConceptDataItem`/reference-linking derefs and the
        //   CSaturationDisjunctExtractionLinker allocation is ported, and the
        //   CSaturationModifiedProcessUpdateLinker pool is live. The remaining
        //   unresolved concept/reference-linking derefs keep this body deferred.
        //   Faithful body (per disjunct):
        //
        //   for (disjunctConceptLinkerIt : disjunctionConcept->getOperandList()) { ++disjCount;
        //       disjunctConcept = disjunctConceptLinkerIt->getData();
        //       disjunctNegation = disjunctConceptLinkerIt->isNegated() ^ disjunctionNegation;
        //       checkingNegation = disjunctNegation;
        //       disjunctHandling = getDisjunctCheckingConcept(disjunctConcept, disjunctNegation, &checkingNegation, calcAlgContext);
        //       disConIndiNode = ((CConceptSaturationReferenceLinkingData*)disjunctHandling->getConceptData()->getConceptReferenceLinking())
        //           ->getConceptSaturationReferenceLinkingData(checkingNegation)->getIndividualProcessNodeForConcept();
        //       addUninitializedIndividualToProcessingQueue(disConIndiNode, calcAlgContext);
        //       disNodeExtLinker = CObjectAllocator<CSaturationDisjunctExtractionLinker>::allocateAndConstruct(taskMemMan);
        //       disNodeExtLinker->initSaturationDisjunctExtractionLinker(disConIndiNode, nullptr);
        //       extractionData->addDisjunctIndividualNodeExtractionLinker(disNodeExtLinker);
        //       modProcUpdLinker = createModifiedProcessUpdateLinker(calcAlgContext);
        //       modProcUpdLinker->initProcessUpdateLinker(indiProcSatNode, UPDATEPDISJUNCTCOMMONCONCEPTSEXTRACTION);
        //       disConIndiNode->getReapplyConceptSaturationLabelSet(true)->addModifiedUpdateLinker(modProcUpdLinker);
        //   }
        //   extractionData->getSaturationDisjunctCommonConceptCountHash()->setDisjunctCount(disjCount);
        //
        //   Live leaves: `self.get_disjunct_checking_concept` (s03), `self.add_uninitialized_individual_to_processing_queue`
        //   (s01), `self.create_modified_process_update_linker` (group M).
        //
        // updateExtractDisjunctCommonConcept(indiProcSatNode, calcAlgContext);  — live, unconditional first pass:
        self.update_extract_disjunct_common_concept(indi_proc_sat_node, calc_alg_context);
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::addDisjunctCommonConceptExtractionToProcessingQueue`
    /// (cpp 5009–5018). Re-enqueues the node's extraction continuation linker onto the
    /// databox disjunct-common-concept extract queue (idempotent on its queued flag).
    pub fn add_disjunct_common_concept_extraction_to_processing_queue(
        &mut self,
        indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // CSaturationDisjunctCommonConceptExtractionData* extractionData = indiProcSatNode->getDisjunctCommonConceptExtractionData(false);
        let extraction_data = calc_alg_context
            .process_context_mut()
            .sat_node_ext_disjunct_common_concept_extraction_data(*indi_proc_sat_node, false);
        if extraction_data.is_some() {
            let process_node_linker = calc_alg_context
                .process_context()
                .sat_disjunct_common_concept_extraction_data(extraction_data)
                .get_extraction_continue_process_linker();
            if process_node_linker.is_some()
                && !calc_alg_context
                    .process_context()
                    .indi_sat_process_node_linker(process_node_linker)
                    .is_processing_queued()
            {
                calc_alg_context
                    .process_context_mut()
                    .indi_sat_process_node_linker_mut(process_node_linker)
                    .set_processing_queued(true);
                calc_alg_context
                    .processing_data_box_mut()
                    .add_individual_disjunct_common_concept_extract_process_linker(
                        process_node_linker,
                    );
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::super::model::substrate::NegLink;
    use super::super::super::process::sat_node::IndividualSaturationProcessNode;
    use super::super::algorithm::SaturationTaskHandleAlgorithm;
    use super::*;

    fn queued_descriptor(
        ctx: &mut CalculationAlgorithmContextBase,
        node: SatNodeId,
        queue_type: CriticalSaturationConceptQueueType,
    ) -> ConceptSaturationDescriptorId {
        let queues = ctx
            .process_context_mut()
            .sat_node_ext_critical_concept_type_queues(node, false);
        if queues.is_none() {
            return ConceptSaturationDescriptorId::NONE;
        }
        let queue = ctx
            .process_context_mut()
            .critical_sat_concept_type_queues_get_critical_saturation_concept_queue(
                queues, queue_type, false,
            );
        if queue.is_none() {
            return ConceptSaturationDescriptorId::NONE;
        }
        let linker = ctx
            .process_context()
            .critical_sat_concept_queue(queue)
            .get_critical_concept_descriptor_linker();
        if linker.is_none() {
            return ConceptSaturationDescriptorId::NONE;
        }
        ctx.process_context()
            .con_sat_proc_linker(linker)
            .get_concept_saturation_descriptor()
    }

    #[test]
    fn s09_has_next_critical_concepts_reads_critical_queue() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(31));
        let queue = ctx.saturation_critical_individual_node_processing_queue(true);

        assert!(!algo.has_next_critical_concepts(&mut ctx));

        ctx.process_context_mut()
            .sat_critical_ind_node_proc_queue_mut(queue)
            .insert_process_individual(node, 31);

        assert!(algo.has_next_critical_concepts(&mut ctx));
    }

    #[test]
    fn s09_add_critical_concept_descriptor_enqueues_typed_queue_and_node_once() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        algo.conf_add_critical_concepts_to_queues = true;
        let mut ctx = CalculationAlgorithmContextBase::new();
        let mut node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(47));
        let first = ConceptSaturationDescriptorId::new(701);
        let second = ConceptSaturationDescriptorId::new(703);

        algo.add_critical_concept_descriptor(first, CCT_VALUE, &mut node, &mut ctx);

        let queues = ctx
            .process_context_mut()
            .sat_node_ext_critical_concept_type_queues(node, false);
        assert!(ctx
            .process_context()
            .critical_sat_concept_type_queues(queues)
            .is_process_node_queued());
        let value_queue = ctx
            .process_context_mut()
            .critical_sat_concept_type_queues_get_critical_saturation_concept_queue(
                queues,
                CriticalSaturationConceptQueueType::Value,
                false,
            );
        let value_linker = ctx
            .process_context()
            .critical_sat_concept_queue(value_queue)
            .get_critical_concept_descriptor_linker();
        assert_eq!(
            ctx.process_context()
                .con_sat_proc_linker(value_linker)
                .get_concept_saturation_descriptor(),
            first
        );

        let critical_node_queue = ctx.saturation_critical_individual_node_processing_queue(false);
        assert_eq!(
            ctx.process_context()
                .sat_critical_ind_node_proc_queue(critical_node_queue)
                .get_queued_individual_count(),
            1
        );
        assert_eq!(
            ctx.process_context()
                .sat_critical_ind_node_proc_queue(critical_node_queue)
                .get_next_process_individual(),
            node
        );

        algo.add_critical_concept_descriptor(second, CCT_DISJUNCTION, &mut node, &mut ctx);

        let disjunction_queue = ctx
            .process_context_mut()
            .critical_sat_concept_type_queues_get_critical_saturation_concept_queue(
                queues,
                CriticalSaturationConceptQueueType::Disjunction,
                false,
            );
        let disjunction_linker = ctx
            .process_context()
            .critical_sat_concept_queue(disjunction_queue)
            .get_critical_concept_descriptor_linker();
        assert_eq!(
            ctx.process_context()
                .con_sat_proc_linker(disjunction_linker)
                .get_concept_saturation_descriptor(),
            second
        );
        assert_eq!(
            ctx.process_context()
                .sat_critical_ind_node_proc_queue(critical_node_queue)
                .get_queued_individual_count(),
            1
        );
    }

    #[test]
    fn s09_add_critical_concept_descriptor_directly_marks_insufficient() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        algo.conf_directly_critical_to_insufficient = true;
        let mut ctx = CalculationAlgorithmContextBase::new();
        let mut node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(53));

        algo.add_critical_concept_descriptor(
            ConceptSaturationDescriptorId::new(709),
            CCT_FORALL,
            &mut node,
            &mut ctx,
        );

        assert!(ctx
            .process_context()
            .sat_node(node)
            .direct_status_flags
            .has_flags_code(
                IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT,
                false
            ));
        assert!(ctx.processing_data_box().is_insufficient_node_occured());
        assert!(ctx
            .saturation_critical_individual_node_processing_queue(false)
            .is_none());
    }

    #[test]
    fn s09_add_critical_concept_for_dependent_nodes_enqueues_all_without_flag_check() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        algo.conf_add_critical_concepts_to_queues = true;
        let mut ctx = CalculationAlgorithmContextBase::new();
        let mut source = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(61));
        let dep_a = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(63));
        let dep_b = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(65));
        ctx.process_context_mut()
            .sat_node_mut(dep_a)
            .set_individual_id(63);
        ctx.process_context_mut()
            .sat_node_mut(dep_b)
            .set_individual_id(65);
        ctx.process_context_mut()
            .sat_node_mut(source)
            .add_copy_depending_individual_node_linker(NegLink {
                target: dep_a,
                negated: false,
            })
            .add_copy_depending_individual_node_linker(NegLink {
                target: dep_b,
                negated: true,
            });
        let descriptor = ConceptSaturationDescriptorId::new(711);

        algo.add_critical_concept_for_dependent_nodes(
            descriptor,
            CCT_ATMOST,
            &mut source,
            false,
            0,
            &mut ctx,
        );

        assert_eq!(
            queued_descriptor(&mut ctx, dep_a, CriticalSaturationConceptQueueType::Atmost),
            descriptor
        );
        assert_eq!(
            queued_descriptor(&mut ctx, dep_b, CriticalSaturationConceptQueueType::Atmost),
            descriptor
        );
        let critical_node_queue = ctx.saturation_critical_individual_node_processing_queue(false);
        assert_eq!(
            ctx.process_context()
                .sat_critical_ind_node_proc_queue(critical_node_queue)
                .get_queued_individual_count(),
            2
        );
    }

    #[test]
    fn s09_add_critical_concept_for_dependent_nodes_respects_direct_or_indirect_flags() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        algo.conf_add_critical_concepts_to_queues = true;
        let mut ctx = CalculationAlgorithmContextBase::new();
        let mut source = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(67));
        let direct_blocked = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(69));
        let indirect_blocked = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(71));
        ctx.process_context_mut()
            .sat_node_mut(direct_blocked)
            .set_individual_id(69);
        ctx.process_context_mut()
            .sat_node_mut(indirect_blocked)
            .set_individual_id(71);
        ctx.process_context_mut()
            .sat_node_mut(source)
            .add_copy_depending_individual_node_linker(NegLink {
                target: direct_blocked,
                negated: false,
            })
            .add_copy_depending_individual_node_linker(NegLink {
                target: indirect_blocked,
                negated: false,
            });
        ctx.process_context_mut()
            .sat_node_mut(direct_blocked)
            .direct_status_flags
            .add_flags_code(IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT);
        ctx.process_context_mut()
            .sat_node_mut(indirect_blocked)
            .indirect_status_flags
            .add_flags_code(IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT);
        let direct_descriptor = ConceptSaturationDescriptorId::new(713);
        let indirect_descriptor = ConceptSaturationDescriptorId::new(715);

        algo.add_critical_concept_for_dependent_nodes(
            direct_descriptor,
            CCT_VALUE,
            &mut source,
            true,
            IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT,
            &mut ctx,
        );

        assert_eq!(
            queued_descriptor(
                &mut ctx,
                direct_blocked,
                CriticalSaturationConceptQueueType::Value
            ),
            ConceptSaturationDescriptorId::NONE
        );
        assert_eq!(
            queued_descriptor(
                &mut ctx,
                indirect_blocked,
                CriticalSaturationConceptQueueType::Value
            ),
            direct_descriptor
        );

        algo.add_critical_concept_for_dependent_nodes(
            indirect_descriptor,
            CCT_NOMINAL,
            &mut source,
            false,
            IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT,
            &mut ctx,
        );

        assert_eq!(
            queued_descriptor(
                &mut ctx,
                direct_blocked,
                CriticalSaturationConceptQueueType::Nominal
            ),
            indirect_descriptor
        );
        assert_eq!(
            queued_descriptor(
                &mut ctx,
                indirect_blocked,
                CriticalSaturationConceptQueueType::Nominal
            ),
            ConceptSaturationDescriptorId::NONE
        );
    }
}
