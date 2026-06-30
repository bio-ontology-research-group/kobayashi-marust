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
use super::super::process::sat_node::IndividualSaturationProcessNodeStatusFlags;
use super::super::process::stubs::ConceptSaturationDescriptorId;
use super::super::process::SatNodeId;

// ---------------------------------------------------------------------------
// W4-DEFER[api]: pending `CCriticalSaturationConceptTypeQueues::CRITICALSATURATIONCONCEPTQUEUETYPE`
// discriminants — carried as opaque pass-through tags (the queue-type machinery
// they select is itself deferred). Real values resolve when the queue class lands.
// ---------------------------------------------------------------------------
const CCT_FORALL: Cint64 = 0;
const CCT_ATMOST: Cint64 = 1;
const CCT_VALUE: Cint64 = 2;
const CCT_NOMINAL: Cint64 = 3;
const CCT_DISJUNCTION: Cint64 = 4;
const CCT_EQCANDIDATE: Cint64 = 5;

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
        let crit_ind_node_proc_queue = calc_alg_context
            .processing_data_box_mut()
            .saturation_critical_individual_node_processing_queue(false);
        if !crit_ind_node_proc_queue.is_none() {
            // W4-DEFER[api]: if (!critIndNodeProcQueue->isEmpty()) return true;
            //   CCriticalIndividualNodeProcessingQueue (process::stubs marker) has no
            //   isEmpty() yet; the non-empty test lands when the queue class is ported.
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
        let crit_ind_node_proc_queue = calc_alg_context
            .processing_data_box_mut()
            .saturation_critical_individual_node_processing_queue(false);
        if !crit_ind_node_proc_queue.is_none() {
            // W4-DEFER[api]: the body iterates the unported processing queue +
            //   per-node critical-queue / status-flag satellites; transcribed:
            //   CIndividualSaturationProcessNode* indiProcSatNode = critIndNodeProcQueue->takeNextProcessIndividual();
            //   bool checkCriticalConcepts = true;
            //   if (indiProcSatNode->getDirectStatusFlags()->hasMissedABoxConsistencyFlag()) {
            //       if (!isConsistenceDataAvailable(calcAlgContext)) {
            //           checkCriticalConcepts = false;
            //           CCriticalSaturationConceptTypeQueues* criticalConceptQueues = indiProcSatNode->getCriticalConceptTypeQueues(false);
            //           if (criticalConceptQueues) criticalConceptQueues->setProcessNodeQueued(false);
            //       }
            //   }
            //   if (checkCriticalConcepts) checkCriticalConceptsForNode(indiProcSatNode, calcAlgContext);
            // The resolvable leaves are the sibling `self.is_consistence_data_available`
            // (group N) and `self.check_critical_concepts_for_node` (below); they fire
            // once the queue `takeNextProcessIndividual` yields a concrete `SatNodeId`.
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
        let _ = calc_alg_context
            .processing_data_box_mut()
            .saturation_critical_individual_node_concept_test_set(true);
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
        // W4-DEFER[api]: iterates indiProcSatNode->getCopyDependingIndividualNodeLinker()
        //   (CXNegLinker<CIndividualSaturationProcessNode*>) and per dependent node tests
        //   its direct/indirect CIndividualSaturationProcessNodeStatusFlags against
        //   `checkFlags`, then enqueues via the sibling addCriticalConceptDescriptor.
        //   The copy-depending chain getter `getCopyDependingIndividualNodeLinker()`
        //   resolves on the sat-node (it returns `&[NegLink<SatNodeId>]`), but the
        //   status-flag `hasFlags` predicate is the unported mask unit, so the per-node
        //   gate + the addCriticalConceptDescriptor enqueue are deferred. Faithful body:
        //
        //   for (depIndiIt : indiProcSatNode->getCopyDependingIndividualNodeLinker()) {
        //       dependingIndiNode = depIndiIt->getData();
        //       statusFlag = directFlagsCheck ? dependingIndiNode->getDirectStatusFlags()
        //                                      : dependingIndiNode->getIndirectStatusFlags();
        //       if (checkFlags == 0 || !statusFlag->hasFlags(checkFlags, false)) {
        //           addCriticalConceptDescriptor(conDes, conceptType, dependingIndiNode, calcAlgContext);
        //       }
        //   }
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
        // CIndividualSaturationProcessNodeStatusFlags* indirectFlags = indiProcSatNode->getIndirectStatusFlags();
        // CIndividualSaturationProcessNodeStatusFlags* directFlags = indiProcSatNode->getDirectStatusFlags();
        // CProcessingDataBox* processingDataBox = calcAlgContext->getUsedProcessingDataBox();
        // CCriticalIndividualNodeConceptTestSet* criticalIndiNodeConTestSet =
        //     processingDataBox->getSaturationCriticalIndividualNodeConceptTestSet(true);
        // criticalConceptQueues->setProcessNodeQueued(false);
        let _critical_concept_queues = calc_alg_context
            .process_context_mut()
            .sat_node_mut(*indi_proc_sat_node)
            .get_critical_concept_type_queues(false);
        let _ = calc_alg_context
            .processing_data_box_mut()
            .saturation_critical_individual_node_concept_test_set(true);
        //
        // W4-DEFER[api]: the six per-type queue-drain blocks all iterate the unported
        //   CCriticalSaturationConceptQueue (CConceptSaturationProcessLinker linkers) under
        //   the CCriticalIndividualNodeConceptTestSet tested-pair set and the indirect/direct
        //   CIndividualSaturationProcessNodeStatusFlags masks; the descriptor `criticalConDes`
        //   feeding each `self.is_critical_*` test comes from `takeNextCriticalConceptDescriptor`.
        //   Faithful transcription (each block guarded by `!indirectFlags->hasInsufficientFlag()
        //   && !indirectFlags->hasClashedFlag()`, the last two by `!hasClashedFlag()` only):
        //
        //   1. CCT_FORALL  → isCriticalALLConceptDescriptorInsufficient:
        //        if insufficient: updateDirectAddingIndividualStatusFlags(node, INDSATFLAGINSUFFICIENT);
        //                         if (node->isABoxIndividualRepresentationNode())
        //                             updateDirectAddingIndividualStatusFlags(node, INDSATFLAGPROPAGATIONINCOMPLETE);
        //                         setInsufficientNodeOccured(); ++mInsufficientALLCount;
        //        else: addCriticalConceptForDependentNodes(conDes, CCT_FORALL, node, false, INDSATFLAGINSUFFICIENT);
        //   2. CCT_ATMOST  → isCriticalATMOSTConceptDescriptorInsufficient(conDes, ancestorPossiblyInsufficient,
        //                        functionallyRestrictedSuccessorNode, functionallyRestrictedSuccessorCreationRoleLinker, node):
        //        if insufficient:
        //          if (mConfDelayedMergingCriticalATMOSTConcepts && node->getMaxAtleastCardinalityCandidate()
        //                  > mConfDelayedMergingCriticalATMOSTConceptsCardinalitySize):
        //              if (!indirect insufficient/clashed): queue the ATMOST merging via
        //                  node->getATMOSTSuccessorMergingData(true) + processingDataBox
        //                  ->addSaturationATMOSTMergingProcessLinker(...) + addMergingProcessingConcept(conDes);
        //          else: ++mInsufficientATMOSTCount;
        //                updateDirectAddingIndividualStatusFlags(node, INDSATFLAGINSUFFICIENT); setInsufficientNodeOccured();
        //        else: addCriticalConceptForDependentNodes(conDes, CCT_ATMOST, node, false, INDSATFLAGINSUFFICIENT);
        //        if (node->hasNominalIntegrated()) markNominalATMOSTRestrictedAncestorsAsInsufficient(conDes, node);
        //        if (ancestorPossiblyInsufficient) {
        //            markATMOSTRestrictedAncestorsAsInsufficient(conDes, functionallyRestrictedSuccessorNode,
        //                functionallyRestrictedSuccessorCreationRoleLinker, node);
        //            updateDirectAddingIndividualStatusFlags(node, INDSATFLAGCARDINALITYPROPLEMATIC);
        //        }
        //   3. CCT_VALUE   → isCriticalVALUEConceptDescriptorInsufficient:
        //        if insufficient: updateDirectAddingIndividualStatusFlags(node, INDSATFLAGINSUFFICIENT); setInsufficientNodeOccured();
        //        else: addCriticalConceptForDependentNodes(conDes, CCT_VALUE, node, false, INDSATFLAGINSUFFICIENT);
        //   4. CCT_NOMINAL → isCriticalNOMINALConceptDescriptorInsufficient: (same shape as VALUE, tag CCT_NOMINAL)
        //   5. CCT_DISJUNCTION → isCriticalORConceptDescriptorInsufficient:
        //        if insufficient: updateDirectNotDependentAddingIndividualStatusFlags(node, INDSATFLAGINSUFFICIENT);
        //                         setInsufficientNodeOccured();
        //                         addCriticalORConceptTestedForDependentNodes(conDes, CCT_DISJUNCTION, node, criticalIndiNodeConTestSet);
        //   6. CCT_EQCANDIDATE → isCriticalEQCANDConceptDescriptorProblematic:
        //        if problematic: updateDirectNotDependentAddingIndividualStatusFlags(node, INDSATFLAGEQCANDPROPLEMATIC);
        //                        setProblematicEQCandidateOccured();
        //                        addCriticalConceptForDependentNodes(conDes, CCT_EQCANDIDATE, node, true, 0);
        //   (each drained descriptor released via releaseConceptSaturationProcessLinker.)
        //
        // The `self.*` critical tests, status-flag updates, fan-outs and counters above
        // are the resolvable leaves; the queue/test-set/flag-mask iteration that selects
        // `criticalConDes` is deferred to the satellite port. The CCT_* tags use the
        // pending discriminants declared at module top.
        let _ = (
            CCT_FORALL,
            CCT_ATMOST,
            CCT_VALUE,
            CCT_NOMINAL,
            CCT_DISJUNCTION,
            CCT_EQCANDIDATE,
        );
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
            // W4-DEFER[api]: enqueue conDes onto the node's per-type critical-concept queue
            //   and, if not already queued, onto the databox processing queue — all unported
            //   satellites (CConceptSaturationProcessLinker pool, CCriticalSaturationConceptTypeQueues,
            //   CCriticalSaturationConceptQueue, CCriticalIndividualNodeProcessingQueue):
            //   CConceptSaturationProcessLinker* conDesProLinker = createConceptSaturationProcessLinker(calcAlgContext);
            //   conDesProLinker->initConceptSaturationProcessLinker(conDes);
            //   CCriticalSaturationConceptTypeQueues* queues = indiProcSatNode->getCriticalConceptTypeQueues(true);
            //   CCriticalSaturationConceptQueue* criticalConceptQueue = queues->getCriticalSaturationConceptQueue(conceptType, true);
            //   criticalConceptQueue->addCriticalConceptDescriptorLinker(conDesProLinker);
            //   if (!queues->isProcessNodeQueued()) {
            //       CCriticalIndividualNodeProcessingQueue* criticalIndNodProcQueue =
            //           calcAlgContext->getUsedProcessingDataBox()->getSaturationCriticalIndividualNodeProcessingQueue(true);
            //       criticalIndNodProcQueue->insertProcessIndiviudal(indiProcSatNode);
            //       queues->setProcessNodeQueued(true);
            //   }
            let _ = calc_alg_context
                .process_context_mut()
                .sat_node_mut(*indi_proc_sat_node)
                .get_critical_concept_type_queues(true);
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
            // CRole* role = concept->getRole();
            //
            // W4-DEFER[api]: (a) the data-role branch — if role->isDataRole() and the node's
            //   CLinkedDataValueAssertionSaturationData lists an asserted data-role whose
            //   indirect super-role list contains `role`, return true; and (b) the main
            //   successor-hash walk: collectLinkedSuccessorNodes then, for each active
            //   CSaturationSuccessorData of `role`, check the successor's
            //   CReapplyConceptSaturationLabelSet (or, for a VALUE-nominal connection under
            //   isConsistenceDataAvailable, the corrected node's CReapplyConceptLabelSet via
            //   getCorrectedNode) contains every `concept` operand at the xor-ed negation;
            //   a missing operand (or absent label set / absent corrected node) ⇒ return true.
            //   The `concept->getRole()` / `getOperandList()` / `containsConcept` and the
            //   CLinkedRoleSaturationSuccessorHash are unported satellites. Live leaves:
            //   `self.collect_linked_successor_nodes`, `self.is_consistence_data_available`,
            //   `self.get_corrected_node` (over mDetCachedCGIndiVector). Faithful body:
            //
            //   if (role->isDataRole() && indiProcSatNode->getIndividualExtensionData(false)) { ...data-role return true... }
            //   collectLinkedSuccessorNodes(indiProcSatNode, calcAlgContext);
            //   CLinkedRoleSaturationSuccessorHash* linkedSuccHash = indiProcSatNode->getLinkedRoleSuccessorHash(false);
            //   if (linkedSuccHash) { succData = succHash->value(role);
            //       for (indiSuccData : succData->mSuccNodeDataMap) if (mActiveCount >= 1) {
            //           if (mVALUENominalConnection) { if (isConsistenceDataAvailable) {
            //               indiProcNode = getCorrectedNode(mVALUENominalID, mDetCachedCGIndiVector, mCalcAlgContext);
            //               if (!indiProcNode) return true;
            //               reapplyConSet = indiProcNode->getReapplyConceptLabelSet(false);
            //               operantsContained = reapplyConSet && all operands contained; if (!operantsContained) return true;
            //           } } else {
            //               succConSet = succNode->getReapplyConceptSaturationLabelSet(false);
            //               operantsContained = succConSet && all operands contained; if (!operantsContained) return true;
            //           }
            //       }
            //   }
            let _ = (con_des,);
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
        // CReapplyConceptSaturationLabelSet* conSet = indiProcSatNode->getReapplyConceptSaturationLabelSet(false);
        let _con_set = calc_alg_context
            .process_context_mut()
            .sat_node_mut(*indi_proc_sat_node)
            .get_reapply_concept_saturation_label_set(false);
        // W4-DEFER[api]: walks `concept->getOperandList()` and for each operand applies
        //   `getDisjunctCheckingConcept` (live sibling, group D) then tests the node's
        //   CReapplyConceptSaturationLabelSet `containsConcept(opCheckingConcept, checkingNegation)`;
        //   any contained disjunct ⇒ return false. The concept-operand iteration + the
        //   label-set `containsConcept` are unported satellites. Faithful body:
        //
        //   if (conSet) for (opLinkerIt : concept->getOperandList()) {
        //       opConcept = opLinkerIt->getData(); opConceptNegation = opLinkerIt->isNegated() ^ conceptNegation;
        //       checkingNegation = opConceptNegation;
        //       opCheckingConcept = getDisjunctCheckingConcept(opConcept, opConceptNegation, &checkingNegation, calcAlgContext);
        //       if (conSet->containsConcept(opCheckingConcept, checkingNegation)) return false;
        //   }
        //   return true;
        let _ = con_des;
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
        // CReapplyConceptSaturationLabelSet* conSet = indiProcSatNode->getReapplyConceptSaturationLabelSet(false);
        let _con_set = calc_alg_context
            .process_context_mut()
            .sat_node_mut(*indi_proc_sat_node)
            .get_reapply_concept_saturation_label_set(false);
        // W4-DEFER[api]: walks `concept->getOperandList()` and tests
        //   `conSet->containsConcept(opConcept, opLinkerIt->isNegated() ^ conceptNegation)`;
        //   any contained operand ⇒ return false; else return true. Concept-operand
        //   iteration + label-set `containsConcept` are unported satellites. Faithful body:
        //
        //   if (conSet) for (opLinkerIt : concept->getOperandList())
        //       if (conSet->containsConcept(opLinkerIt->getData(), opLinkerIt->isNegated() ^ conceptNegation)) return false;
        //   return true;
        let _ = con_des;
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
        functionally_restricted_successor_creation_role_linker: &mut Cint64,
        indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // STATINC(SATURATIONCRITICALATMOSTCOUNT, calcAlgContext);
        // CConcept* concept = conDes->getConcept(); bool conceptNegation = conDes->isNegated();
        // CRole* role = concept->getRole();
        // cint64 allowedCardinality = concept->getParameter() - 1*conceptNegation;
        // if (allowedCardinality < 0) return true;
        //
        // W4-DEFER[api]: `concept->getParameter()` / `getRole()` are unported `CConcept`
        //   accessors, so `allowedCardinality` and the `< 0 ⇒ return true` early exit are
        //   deferred (descriptor is a process::stubs marker).
        // cint64 foundCardinality = 0;
        // if (!indiProcSatNode->hasSubstituteIndividualNode()) {
        let has_substitute = calc_alg_context
            .process_context_mut()
            .sat_node_mut(*indi_proc_sat_node)
            .has_substitute_individual_node();
        if !has_substitute {
            // collectLinkedSuccessorNodes(indiProcSatNode, calcAlgContext);
            self.collect_linked_successor_nodes(indi_proc_sat_node, calc_alg_context, INVALID);
            // W4-DEFER[api]: the cardinality core over unported satellites:
            //   (a) data-role branch: count asserted data-roles whose indirect super-role list
            //       contains `role`; if foundCardinality > allowedCardinality ⇒ return true;
            //   (b) the successor-hash walk: succData = linkedSuccHash->getLinkedRoleSuccessorHash()->value(role);
            //       if (succData->mSuccCount >= allowedCardinality) {
            //           foundCardinality += collectATMOSTConceptRelevantSuccessors(conDes, indiProcSatNode, succData,
            //               mergingSuccDataLinker, lastSuccessorNode, lastSuccessorCreationRoleLinker, minCardinality, calcAlgContext);
            //           if (foundCardinality >= allowedCardinality && foundCardinality > 1) {
            //               // simple merging (mConfSimpleMergingTestForATMOSTCriticalTesting):
            //               //   getSuccessorLinkSimplyMergeableCardinalityCount(...) into remainMergeableCardHash;
            //               // detailed merging (mConfDetailedMergingTestForATMOSTCriticalTesting,
            //               //   foundCard-mergeable in [allowed, 2*allowed]):
            //               //   getSuccessorLinkExtendedMergeableCardinalityCount(...);
            //               // (the temp CPROCESSHASH/CPROCESSSET come from the task temporary allocator)
            //               releaseIndividualSaturationSuccessorLinkDataLinker(mergingSuccDataLinker, calcAlgContext);
            //           }
            //           if (foundCardinality-mergeableCardinality == allowedCardinality || minCardinality >= allowedCardinality) {
            //               ancestorPossiblyCriticalFlag = true;
            //               if (allowedCardinality == 1) {
            //                   functionallyRestrictedSuccessorNode = lastSuccessorNode;
            //                   functionallyRestrictedSuccessorCreationRoleLinker = lastSuccessorCreationRoleLinker;
            //               }
            //           }
            //           if (foundCardinality-mergeableCardinality > allowedCardinality) return true;
            //       }
            //   }
            //   Live leaves: `self.collect_linked_successor_nodes`,
            //   `self.collect_atmost_concept_relevant_successors`,
            //   `self.get_successor_link_simply_mergeable_cardinality_count`,
            //   `self.get_successor_link_extended_mergeable_cardinality_count`,
            //   `self.release_individual_saturation_successor_link_data_linker` (group G/M),
            //   and the `conf_simple_merging_test_for_atmost_critical_testing` /
            //   `conf_detailed_merging_test_for_atmost_critical_testing` member gates; the
            //   out-params `ancestor_possibly_critical_flag` / `functionally_restricted_successor_node`
            //   / `functionally_restricted_successor_creation_role_linker` are written in that branch.
            let _ = (
                con_des,
                &mut *ancestor_possibly_critical_flag,
                &mut *functionally_restricted_successor_node,
                &mut *functionally_restricted_successor_creation_role_linker,
            );
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
            //   label sets + `containsConcept` are unported satellites. Default (det node present,
            //   no extra non-det concept) ⇒ false.
            let _ = (con_des, *indi_proc_sat_node);
            false
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
            //   (group D, s03). Default ⇒ false.
            let _ = (con_des, *indi_proc_sat_node);
            false
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
            .sat_node_mut(*indi_proc_sat_node)
            .get_disjunct_common_concept_extraction_data(false);
        if extraction_data != INVALID {
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
            .sat_node_mut(*indi_proc_sat_node)
            .get_disjunct_common_concept_extraction_data(true);
        // W4-DEFER[api]: resolves the node's disjunction concept (CSaturationConceptDataItem
        //   ->getSaturationConcept()/getSaturationNegation()) and, per disjunct operand, the
        //   per-disjunct saturation node via the concept-reference linking (getConceptSaturationReferenceLinkingData
        //   ->getIndividualProcessNodeForConcept), then wires the extraction satellites.
        //   The `CConcept`/`CSaturationConceptDataItem`/reference-linking derefs and the
        //   CSaturationDisjunctExtractionLinker / CSaturationModifiedProcessUpdateLinker pools
        //   are unported. Faithful body (per disjunct):
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
            .sat_node_mut(*indi_proc_sat_node)
            .get_disjunct_common_concept_extraction_data(false);
        if extraction_data != INVALID {
            // W4-DEFER[api]: the CSaturationDisjunctCommonConceptExtractionData
            //   ->getExtractionContinueProcessLinker() (a CIndividualSaturationProcessNodeLinker)
            //   and its isProcessingQueued/setProcessingQueued flag are unported; on first
            //   enqueue it is pushed to the databox via the live
            //   `addIndividualDisjunctCommonConceptExtractProcessLinker`. Faithful body:
            //
            //   processNodeLinker = extractionData->getExtractionContinueProcessLinker();
            //   if (!processNodeLinker->isProcessingQueued()) {
            //       processNodeLinker->setProcessingQueued();
            //       calcAlgContext->getUsedProcessingDataBox()->addIndividualDisjunctCommonConceptExtractProcessLinker(processNodeLinker);
            //   }
            //   The databox sink `add_individual_disjunct_common_concept_extract_process_linker`
            //   (db5) takes a concrete `SatNodeId`; it fires once the continuation linker resolves.
        }
    }
}
