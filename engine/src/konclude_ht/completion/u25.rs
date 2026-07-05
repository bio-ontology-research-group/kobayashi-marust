//! `completion::u25` — Caching / backend-cache / saturation family, batch
//! (port unit #25 of 36).
//!
//! Faithful port of the methods that the manifest (`01-completion-methods.md`,
//! "Unit 25") groups under the representative-memory backend-cache reuse /
//! synchronisation / expansion-queue feeding of Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`.
//! cpp source line ranges (1-based) per method are noted on each item.
//!
//! Methods (cpp order):
//!   * `canDelayRepresentativeNeighbourExpansion`                  [24645–24679]  (u24 left this for u25)
//!   * `delayingRepresentativeNeighbourExpansion`                  [24683–24700]  (u24 left this for u25)
//!   * `prepareBackendIndividualFixedReuseExpansion`               [24889–24913]
//!   * `prepareBackendIndividualPrioritizedReuseExpansion`         [24916–25003]
//!   * `checkIndividualBackendExpansionReuseable`                  [25010–25086]
//!   * `reuseIndividualBackendExpansion`                           [25092–25373]
//!   * `testIndividualNodeBackendCacheConceptsSynchronization`     [26283–26362]
//!   * `validateBackendSynchronisationContinued`                   [26368–26407]
//!   * `isConceptUnsatisfiabilitySaturated`                        [26900–26921]
//!   * `addIndividualToBackendSynchronisationRetestQueue`          [27587–27596]
//!   * `addIndividualToBackendDirectInfluenceExpansionQueue`       [27598–27607]
//!   * `addIndividualToBackendIndirectCompatibilityExpansionQueue` [27609–27618]
//!   * `addIndividualToBackendReuseExpansionQueue`                 [27621–27630]
//!   * `addIndividualToBackendNeighbourExpansionQueue`             [27632–27641]
//!
//! KONCLUDE-PORT-NOTE[ownership]: each method is a member of
//! `CCalculationTableauCompletionTaskHandleAlgorithm`, so it becomes `&mut self`
//! plus the threaded per-thread context `calc_alg_context: &mut
//! CalculationAlgorithmContextBase`. C++ `CIndividualProcessNode*&` out/in-out
//! pointer-references become `&mut NodeId`; a plain `CIndividualProcessNode*` value
//! parameter becomes `NodeId`; `bool&` out-params become `&mut bool`; a `CConcept*`
//! value parameter becomes `ConceptId` resolved against
//! `calc_alg_context.ontology_arenas()`. The per-test arenas are reached through the
//! context as `calc_alg_context.process_context()` / `_mut()`, the databox as
//! `calc_alg_context.processing_data_box{,_mut}()`.
//!
//! KONCLUDE-PORT-NOTE[api]: every not-yet-ported backend-cache class
//! (`CBackendNeighbourExpansionQueueDataLinker`,
//! `CPROCESSHASH<…, …LabelNeighbourExpansionData>`,
//! `CBackendRepresentativeMemoryLabelCacheItem`,
//! `CBackendRepresentativeMemoryCacheIndividualAssociationData`,
//! `CIndividualNodeRepresentativeMemoryBackendCacheSynchronisationData` and its
//! `…LabelNeighbourExpansionData` satellite) appears in a faithful signature as an
//! opaque `Cint64` handle, the same convention u17/u23/u24 use for the
//! representative-memory backend-cache subsystem (the W6 Cache subtree).
//!
//! Deferral landscape. Like u24, this unit is dominated by the backend-cache
//! subsystem that is NOT yet ported (W6 Cache subtree) plus the saturation
//! subsystem (W4): the reuse / synchronisation / delaying methods bottom out in the
//! per-node sync data, the association/label cache items, `mBackendCacheHandler`
//! visitors, the dependency/clash-throw machinery, and the saturation reference
//! linking. Those ten bodies are kept `// PORT-PENDING` with the faithful signature
//! and a structural transcription so a later wave fills them without re-reading the
//! source. The five `addIndividualTo*Queue` feeders ARE substrate-portable in their
//! decisive part — the per-node "already queued" flag guard that fixes the boolean
//! return — so that control flow is ported LIVE (direct access to the public node
//! flag field, since node.rs exposes no `is_/set_` wrapper for these and this unit
//! may write only `u25.rs`); only the databox queue getter + `insertIndiviudalProcessNode`
//! + `STATINC` are held `// W3-DEFER[api]` (process-layer queue stubs, no arena).
//! Logic is documented, never silently dropped.

#![allow(dead_code)]
#![allow(unused_variables)]

use super::super::model::substrate::{Cint64, Id, INVALID};
use super::super::model::ConceptId;
use super::super::process::node::IndividualProcessNode;
use super::super::process::sat_node::IndividualSaturationProcessNodeStatusFlags;
use super::super::process::stubs::BackendSyncDataId;
use super::super::process::{ConDescId, NodeId, SatNodeId};
use super::context::CalculationAlgorithmContextBase;

impl super::algorithm::CompletionTaskHandleAlgorithm {
    // =======================================================================
    // Representative-neighbour-expansion delaying pair (cpp 24645–24700).
    // u24 (`queuedIndividualBackendNeighbourExpansion`) calls both of these as
    // "u25 (sibling)"; they live here.
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::canDelayRepresentativeNeighbourExpansion`.
    /// cpp 24645–24679.
    ///
    /// For one queued neighbour-array expansion, decides whether the neighbour at
    /// `neighbourIndiId` should be (a) skipped because its nominal node already
    /// exists, (b) delayed because the label-representative expansion is already
    /// installed, (c) representatively expanded (label not yet fully scheduled), or
    /// (d) plainly expanded. It threads the per-label
    /// `…LabelNeighbourExpansionData` slot (allocated/initialised on first sight)
    /// back through `delayingLabelNeighbourExpansionData` and writes the
    /// `expansionDelaying` / `representativeExpansion` out-flags; it also bumps the
    /// matching representative-expansion statistic. Always returns `true`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: `*&`/out-param
    /// `delayingLabelNeighbourExpansionData` becomes `&mut Cint64` (opaque backend
    /// handle); `expansionDelaying`/`representativeExpansion` become `&mut bool`.
    pub fn can_delay_representative_neighbour_expansion(
        &mut self,
        exp_indi_node: NodeId,
        backend_neighbour_exp_data_linker: Cint64,
        label_neighbour_exp_delay_data_hash: Cint64,
        expanding_label: Cint64,
        neighbour_ass_data: Cint64,
        array_pos: Cint64,
        last_cursor: Cint64,
        neighbour_indi_id: Cint64,
        delaying_label_neighbour_expansion_data: &mut Cint64,
        expansion_delaying: &mut bool,
        representative_expansion: &mut bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // PORT-PENDING: faithful transcription of cpp 24645–24679. Outline:
        //
        //   if labelNeighbourExpDelayDataHash:
        //     neighbourConSetLabel = neighbourAssData->getLabelCacheEntry(FULL_CONCEPT_SET_LABEL);
        //     if !expandingLabel || expandingLabel == neighbourConSetLabel:
        //       labelNeighbourExpansionData& = (*labelNeighbourExpDelayDataHash)[neighbourConSetLabel];
        //       delayingLabelNeighbourExpansionData = &labelNeighbourExpansionData;
        //       if labelNeighbourExpansionData.getNeighbourExpansionArrayId() < 0:
        //         labelNeighbourExpansionData.setNeighbourExpansionArrayId(arrayPos);
        //         labelNeighbourExpansionData.setConceptSetLabel(neighbourConSetLabel);
        //         labelNeighbourExpansionData.setExpandingIndividiaulNode(expIndiNode);
        //         labelNeighbourExpansionData.setExpandingQueueData(backendNeighbourExpDataLinker);
        //       if isNominalIndividualNodeAvailable(-neighbourIndiId, ctx):                 // u16 (sibling)
        //         expansionDelaying = false; representativeExpansion = false;
        //         ++mStatRepresentativeExpansionAlreadyExistingNeighbourIndividualCount;
        //       elif labelNeighbourExpansionData.isNeighbourLabelDelayedRepresentativeExpansion():
        //         expansionDelaying = true; representativeExpansion = false;
        //         ++mStatRepresentativeDelayedNeighbourIndividualExpansionCount;
        //       elif !labelNeighbourExpansionData.hasAllLabelNeighbourExpansionScheduled():
        //         expansionDelaying = false; representativeExpansion = true;
        //         ++mStatRepresentativeExpansionTryingNeighbourIndividualCount;
        //       else:
        //         expansionDelaying = false; representativeExpansion = false;
        //     else:
        //       expansionDelaying = true; representativeExpansion = false;
        //   return true;
        //
        // Held PORT-PENDING: `labelNeighbourExpDelayDataHash` /
        // `neighbourAssData->getLabelCacheEntry` /
        // `…LabelNeighbourExpansionData` are the not-yet-ported representative-memory
        // backend-cache classes (opaque `Cint64` here). The sibling
        // `is_nominal_individual_node_available` (u16) and the four stat counters
        // (`self.stat_representative_expansion_already_existing_neighbour_individual_count`
        // / `…_delayed_neighbour_individual_expansion_count` /
        // `…_expansion_trying_neighbour_individual_count`) become live on the
        // reconcile pass once the label-expansion data lands. The C++ ALWAYS returns
        // `true` (it never short-circuits the caller), so the faithful return is
        // `true` even while the body is deferred.
        let _ = (
            exp_indi_node,
            backend_neighbour_exp_data_linker,
            label_neighbour_exp_delay_data_hash,
            expanding_label,
            neighbour_ass_data,
            array_pos,
            last_cursor,
            neighbour_indi_id,
            &mut *delaying_label_neighbour_expansion_data,
            &mut *expansion_delaying,
            &mut *representative_expansion,
            calc_alg_context,
        );
        true
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::delayingRepresentativeNeighbourExpansion`.
    /// cpp 24683–24700.
    ///
    /// The post-expansion bookkeeping companion of
    /// `can_delay_representative_neighbour_expansion`: if the neighbour was
    /// representatively expanded it records the representative-expanded individual on
    /// the label slot (and flags the node's sync data) once; if expansion is being
    /// delayed it remembers the cursor to resume from. Always returns `false`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: `locBackendSyncData` /
    /// `labelNeighbourExpansionData` are opaque backend handles (`Cint64`).
    pub fn delaying_representative_neighbour_expansion(
        &mut self,
        loc_backend_sync_data: Cint64,
        expansion_delaying: bool,
        representative_expansion: bool,
        label_neighbour_expansion_data: Cint64,
        last_cursor: Cint64,
        neighbour_indi_id: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // PORT-PENDING: faithful transcription of cpp 24683–24700. Outline:
        //
        //   if labelNeighbourExpansionData:
        //     if representativeExpansion:
        //       ++mStatRepresentativeExpandedNeighbourIndividualCount;
        //       if !labelNeighbourExpansionData->isNeighbourLabelDelayedRepresentativeExpansion():
        //         labelNeighbourExpansionData->setNeighbourLabelDelayedRepresentativeExpansion(true);
        //         labelNeighbourExpansionData->setRepresentativeExpandedIndividual(neighbourIndiId);
        //         locBackendSyncData->setNeighbourLabelRepresentativeExpansion(true);
        //     if expansionDelaying:
        //       if labelNeighbourExpansionData->getNextLabelNeighbourExpansionIteratorCursor() < 0:
        //         labelNeighbourExpansionData->setNextLabelNeighbourExpansionIteratorCursor(lastCursor);
        //   return false;
        //
        // Held PORT-PENDING: the `…LabelNeighbourExpansionData` satellite and the
        // per-node `…BackendCacheSynchronisationData` are not yet ported; the stat
        // counter `self.stat_representative_expanded_neighbour_individual_count`
        // becomes live on the reconcile pass. The C++ ALWAYS returns `false`, so the
        // faithful return is `false`.
        let _ = (
            loc_backend_sync_data,
            expansion_delaying,
            representative_expansion,
            label_neighbour_expansion_data,
            last_cursor,
            neighbour_indi_id,
            calc_alg_context,
        );
        false
    }

    // =======================================================================
    // Backend-individual reuse expansion preparation (cpp 24889–25003).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::prepareBackendIndividualFixedReuseExpansion`.
    /// cpp 24889–24913.
    ///
    /// In the fixed-reuse alternative: installs a `REUSEBACKENDFIXEDINDIVIDUALEXPANSION`
    /// non-deterministic dependency + branch track-point on a freshly localized copy
    /// of the node, flags it `PRFBACKENDEXPANSIONREUSINGINDIVIDUAL`, and stamps the
    /// localized backend sync data with the reuse track-point (the reuse expansion
    /// itself runs directly afterwards — clashes are not problematic here). Returns
    /// whether the reuse-modes dependency node was present.
    pub fn prepare_backend_individual_fixed_reuse_expansion(
        &mut self,
        indi_proc_node: &mut NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // expContData = ctx->getUsedProcessingDataBox()->getBackendNeighbourExpansionControllingData(true);
        let exp_cont_data = calc_alg_context.backend_neighbour_expansion_controlling_data(true);
        // reuseModesDepNode = expContData->getReuseModesDependencyNode();
        let reuse_modes_dep_node = calc_alg_context
            .process_context()
            .backend_neighbour_expansion_controlling_data(exp_cont_data)
            .get_reuse_modes_dependency_node();
        if reuse_modes_dep_node.is_some() {
            let reuse_continuing_dependency_track_point = calc_alg_context
                .process_context()
                .backend_neighbour_expansion_controlling_data(exp_cont_data)
                .get_reuse_continuing_dependency_track_point();
            // reuseDepNode = createREUSEBACKENDFIXEDINDIVIDUALEXPANSIONDependency(indiProcNode,
            //               expContData->getReuseContinuingDependencyTrackPoint(), ctx);
            let reuse_dep_node = self.create_reuse_backend_fixed_individual_expansion_dependency(
                indi_proc_node,
                reuse_continuing_dependency_track_point,
                calc_alg_context,
            );
            // newDependencyTrackPoint = createNonDeterministicDependencyTrackPointBranch(reuseDepNode, true, ctx);
            let new_dependency_track_point = self
                .create_non_deterministic_dependency_track_point_branch(
                    reuse_dep_node,
                    true,
                    calc_alg_context,
                );

            // newIndiProcNode = getLocalizedIndividual(indiProcNode, false, ctx);
            let new_indi_proc_node =
                self.get_localized_individual(*indi_proc_node, false, calc_alg_context);
            // newIndiProcNode->addProcessingRestrictionFlags(PRFBACKENDEXPANSIONREUSINGINDIVIDUAL);
            calc_alg_context
                .process_context_mut()
                .node_mut(new_indi_proc_node)
                .add_processing_restriction_flags(
                    IndividualProcessNode::PRF_BACKENDEXPANSIONREUSINGINDIVIDUAL,
                );
            // locBackendSyncData = getLocalizedIndividualBackendCacheSnychronisationData(newIndiProcNode, ctx);
            let loc_backend_sync_data = self
                .get_localized_individual_backend_cache_snychronisation_data(
                    new_indi_proc_node,
                    calc_alg_context,
                );
            calc_alg_context
                .process_context_mut()
                .backend_sync_data_mut(loc_backend_sync_data)
                .set_backend_expansion_reuse_dependency_track_point(new_dependency_track_point);
            // directly do reuse expansion here, clashes are not problematic
            return true;
        }
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::prepareBackendIndividualPrioritizedReuseExpansion`.
    /// cpp 24916–25003.
    ///
    /// In the prioritized-reuse alternative: forks two dependent branching tasks off
    /// a `REUSEBACKENDPRIORITIZEDINDIVIDUALEXPANSION` dependency — task 0 is the
    /// fixed-reuse branch (localize, flag reusing, stamp reuse track-point, enqueue
    /// onto the backend-individual reuse-expansion queue), task 1 deactivates reuse
    /// (`PRFBACKENDEXPANSIONREUSEDISCARDED`) and enqueues onto the indirect-compatibility
    /// queue — sets each task's reuse priority, communicates the task creation, and
    /// aborts the current task with a stop-processing exception. Returns whether the
    /// reuse-modes dependency node was present.
    ///
    /// KONCLUDE-PORT-NOTE[exceptions]: the terminal `throw
    /// CCalculationStopProcessingException(true)` is control flow; in the port it
    /// becomes an early return once the task-fork machinery is wired.
    pub fn prepare_backend_individual_prioritized_reuse_expansion(
        &mut self,
        indi_proc_node: &mut NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // Faithful transcription of cpp 24916–25003. The branch-local task/context
        // split remains deferred, but the process-side dependency/flag/queue effects
        // for the two alternatives are live below.
        //
        //   expContData = ctx->getUsedProcessingDataBox()->getBackendNeighbourExpansionControllingData(true);
        //   reuseModesDepNode = expContData->getReuseModesDependencyNode();
        //   if reuseModesDepNode:
        //     processorContext  = ctx->getUsedTaskProcessorContext();
        //     processingDataBox = ctx->getUsedProcessingDataBox();
        //     taskCreationCount = 2;
        //     newTaskList = createDependendBranchingTaskList(taskCreationCount, ctx);                 // backtracking unit
        //     newTaskIt   = newTaskList;
        //     reuseDepNode = createREUSEBACKENDPRIORITIZEDINDIVIDUALEXPANSIONDependency(indiProcNode,
        //                       expContData->getReuseContinuingDependencyTrackPoint(), ctx);          // dep unit
        //     for i in 0..taskCreationCount:
        //       newSatCalcTask = newTaskIt; fixedReusingAlternative = (i == 0);
        //       newProcessContext = newSatCalcTask->getProcessContext(processorContext);
        //       newCalcAlgContext = createCalculationAlgorithmContext(processorContext, newProcessContext, newSatCalcTask);  // core unit
        //       newAllocMemMan    = newCalcAlgContext->getUsedProcessTaskMemoryAllocationManager();
        //       newProcessingDataBox = newSatCalcTask->getProcessingDataBox();
        //       if fixedReusingAlternative:
        //         newDependencyTrackPoint = createNonDeterministicDependencyTrackPointBranch(reuseDepNode, false, newCalcAlgContext);
        //         (re-fetch newProcessingDataBox / newProcessContext / newCalcAlgContext / newAllocMemMan)
        //         newProcessTagger = newCalcAlgContext->getUsedProcessTagger();
        //         newProcessTagger->incBranchingTag(); newProcessTagger->incLocalizationTag();
        //         newIndiProcNode = getLocalizedIndividual(indiProcNode, false, newCalcAlgContext);   // u17
        //         newIndiProcNode->addProcessingRestrictionFlags(PRFBACKENDEXPANSIONREUSINGINDIVIDUAL);
        //         locBackendSyncData = getLocalizedIndividualBackendCacheSnychronisationData(newIndiProcNode, calcAlgContext);  // u17
        //         locBackendSyncData->setBackendExpansionReuseDependencyTrackPoint(newDependencyTrackPoint);
        //         // add to reuse queue, don't do reuse expansion here in case of clashes
        //         newProcessingDataBox->getBackendIndividualReuseExpansionQueue(true)->insertIndiviudalProcessNode(newIndiProcNode);
        //         prepareBranchedTaskProcessing(newIndiProcNode, newSatCalcTask, newCalcAlgContext); // core unit
        //       else:
        //         newDependencyTrackPoint = createNonDeterministicDependencyTrackPointBranch(reuseDepNode, false, newCalcAlgContext);
        //         (re-fetch newProcessContext / newCalcAlgContext / newAllocMemMan)
        //         newIndiProcNode = getLocalizedIndividual(indiProcNode, false, newCalcAlgContext);   // u17
        //         newIndiProcNode->addProcessingRestrictionFlags(PRFBACKENDEXPANSIONREUSEDISCARDED);  // deactivate reuse
        //         newProcessingDataBox->getBackendIndirectCompatibilityExpansionQueue(true)->insertIndiviudalProcessNode(newIndiProcNode);
        //         prepareBranchedTaskProcessing(newIndiProcNode, newSatCalcTask, newCalcAlgContext);
        //       newTaskPriority = ctx->getUsedTaskPriorityStrategy()->getPriorityForTaskReusing(
        //                            newSatCalcTask, ctx->getUsedSatisfiableCalculationTask(), fixedReusingAlternative);
        //       newSatCalcTask->setTaskPriority(newTaskPriority);
        //       newTaskIt = newTaskIt->getNext();
        //     processorContext->getTaskProcessorCommunicator()->communicateTaskCreation(newTaskList);
        //     throw CCalculationStopProcessingException(true);   // [exceptions] -> early return once task-fork wired
        //   return false;
        //
        // W3-DEFER[task]: real dependent child task contexts, per-child process
        // tagger branch/localization increments, task priorities, scheduler
        // communication, and the terminal stop-processing throw.
        let exp_cont_data = calc_alg_context.backend_neighbour_expansion_controlling_data(true);
        let reuse_modes_dep_node = calc_alg_context
            .process_context()
            .backend_neighbour_expansion_controlling_data(exp_cont_data)
            .get_reuse_modes_dependency_node();
        if reuse_modes_dep_node.is_none() {
            return false;
        }

        let reuse_continuing_dependency_track_point = calc_alg_context
            .process_context()
            .backend_neighbour_expansion_controlling_data(exp_cont_data)
            .get_reuse_continuing_dependency_track_point();
        let reuse_dep_node = self.create_reuse_backend_prioritized_individual_expansion_dependency(
            indi_proc_node,
            reuse_continuing_dependency_track_point,
            calc_alg_context,
        );

        // fixed-reusing alternative (i == 0)
        let reuse_dependency_track_point = self
            .create_non_deterministic_dependency_track_point_branch(
                reuse_dep_node,
                false,
                calc_alg_context,
            );
        let new_indi_proc_node =
            self.get_localized_individual(*indi_proc_node, false, calc_alg_context);
        calc_alg_context
            .process_context_mut()
            .node_mut(new_indi_proc_node)
            .add_processing_restriction_flags(
                IndividualProcessNode::PRF_BACKENDEXPANSIONREUSINGINDIVIDUAL,
            );
        let loc_backend_sync_data = self
            .get_localized_individual_backend_cache_snychronisation_data(
                new_indi_proc_node,
                calc_alg_context,
            );
        calc_alg_context
            .process_context_mut()
            .backend_sync_data_mut(loc_backend_sync_data)
            .set_backend_expansion_reuse_dependency_track_point(reuse_dependency_track_point);
        let reuse_queue = calc_alg_context.get_backend_individual_reuse_expansion_queue(true);
        calc_alg_context
            .process_context_mut()
            .indi_unsorted_proc_queue_mut(reuse_queue)
            .insert_indiviudal_process_node(new_indi_proc_node);

        // reuse-discarding alternative (i == 1)
        let _discard_dependency_track_point = self
            .create_non_deterministic_dependency_track_point_branch(
                reuse_dep_node,
                false,
                calc_alg_context,
            );
        let discard_indi_proc_node =
            self.get_localized_individual(*indi_proc_node, false, calc_alg_context);
        calc_alg_context
            .process_context_mut()
            .node_mut(discard_indi_proc_node)
            .add_processing_restriction_flags(
                IndividualProcessNode::PRF_BACKENDEXPANSIONREUSEDISCARDED,
            );
        let indirect_queue =
            calc_alg_context.get_backend_indirect_compatibility_expansion_queue(true);
        calc_alg_context
            .process_context_mut()
            .indi_unsorted_proc_queue_mut(indirect_queue)
            .insert_indiviudal_process_node(discard_indi_proc_node);

        // W3-DEFER[core]: prepareBranchedTaskProcessing(...) for both alternatives.
        // W3-DEFER[exceptions]: CCalculationStopProcessingException(true).
        *indi_proc_node = new_indi_proc_node;
        true
    }

    // =======================================================================
    // Reuse reusability check + the reuse expansion itself (cpp 25010–25373).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::checkIndividualBackendExpansionReuseable`.
    /// cpp 25010–25086.
    ///
    /// Tests whether the node's backend-cached non-deterministic state can be reused:
    /// (a) no non-deterministic full-concept-set concept conflicts with the node's
    /// current label (a deterministically-present negation, or the negation already
    /// held, disables reuse), and (b) no non-deterministic different-individual is
    /// already deterministically merged into the node. On failure it flags the node
    /// `PRFBACKENDEXPANSIONREUSEDISCARDED`. Returns reusability.
    pub fn check_individual_backend_expansion_reuseable(
        &mut self,
        indi_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // PORT-PENDING: faithful transcription of cpp 25010–25086. Outline:
        //
        //   reusable = true;
        //   backendSyncData = indiNode->getIndividualBackendCacheSynchronisationData(false);
        //   assocData = backendSyncData->getAssocitaionData();
        //   if assocData:
        //     reuseExpDepTrackPoint = backendSyncData->getBackendExpansionReuseDependencyTrackPoint();
        //     conLabel = assocData->getLabelCacheEntry(FULL_CONCEPT_SET_LABEL);
        //     if conLabel && conLabel->hasNondeterministicElements():
        //       conSetLabel = indiNode->getReapplyConceptLabelSet(false);
        //       if conSetLabel:
        //         mBackendCacheHandler->visitConceptsOfAssociatedFullConceptSetLabel(assocData, conLabel,
        //           |concept, negation, deterministic| {
        //             if !deterministic:
        //               if conSetLabel->getConceptDescriptor(concept, conDes, depTrackPoint):
        //                 if conDes->isNegated() != negation:
        //                   // negation already present; disable reuse only if dependency is deterministic
        //                   if !hasNondeterministicDependency(depTrackPoint, ctx): reusable=false; return false;
        //               if conSetLabel->hasConcept(concept, !negation): reusable=false; return false;
        //             return true; }, false, true, ctx);
        //     nonDetDiffIndiLabel = assocData->getLabelCacheEntry(NONDETERMINISTIC_DIFFRENT_INDIVIDUAL_SET_LABEL);
        //     detSameIndiLabel    = assocData->getLabelCacheEntry(DETERMINISTIC_SAME_INDIVIDUAL_SET_LABEL);
        //     if nonDetDiffIndiLabel:
        //       mergedHash = indiNode->getIndividualMergingHash(false);
        //       if mergedHash:
        //         mBackendCacheHandler->visitIndividualIdsOfAssociatedIndividualSetLabel(assocData, nonDetDiffIndiLabel,
        //           |diffIndiId| {
        //             mergingData = mergedHash->value(diffIndiId);
        //             if diffIndiId != indiNode->getNominalIndividual()->getIndividualID()
        //                && !mBackendCacheHandler->hasIndividualIdsInAssociatedIndividualSetLabel(assocData, detSameIndiLabel, diffIndiId)
        //                && mergingData.isMergedWithIndividual():
        //               if !hasNondeterministicDependency(mergingData.getDependencyTrackPoint(), ctx): reusable=false; return false;
        //             return true; }, ctx);
        //   if !reusable: indiNode->addProcessingRestrictionFlags(PRFBACKENDEXPANSIONREUSEDISCARDED);
        //   return reusable;
        //
        // Held PORT-PENDING: the per-node backend sync + association/label cache items,
        // the `mBackendCacheHandler` concept/individual-set visitors, and the
        // individual merging hash are not yet ported; the sibling
        // `has_nondeterministic_dependency` (dep unit) and the
        // `PRFBACKENDEXPANSIONREUSEDISCARDED` node flag become live on the reconcile
        // pass. The C++ default is `reusable = true`, so the faithful default return
        // is `true`.
        let _ = (indi_node, calc_alg_context);
        true
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::reuseIndividualBackendExpansion`.
    /// cpp 25092–25373.
    ///
    /// Materialises the reusable backend-cached non-deterministic state onto the
    /// (merged-into) node, once each: (1) merges all non-deterministic possibly-same
    /// individuals into the smallest representative id (clash-throws if not
    /// mergeable); (2) adds all non-deterministic full-concept-set concepts; (3) for
    /// every non-deterministic combined neighbour-instantiated role, creates the
    /// missing neighbour links (ensuring deterministic links first, handling the
    /// inverse-role and merged-neighbour cases, building the right VALUE / REUSEBACKENDVALUE
    /// dependency), then re-queues the neighbour; (4) states all non-deterministic
    /// different individuals as distinct links (clash-throws on a present merge).
    /// Returns `lazyNeighboursExpansionSucceded` (always `true`).
    ///
    /// KONCLUDE-PORT-NOTE[exceptions]: the two `throw CCalculationClashProcessingException(clashDescriptors)`
    /// sites are control flow routed to backtracking; deferred with the body.
    pub fn reuse_individual_backend_expansion(
        &mut self,
        indi_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // PORT-PENDING: faithful transcription of cpp 25092–25373. Outline:
        //
        //   lazyNeighboursExpansionSucceded = true;
        //   locBackendSyncData = getLocalizedIndividualBackendCacheSnychronisationData(indiNode, ctx);   // u17
        //   backendSyncData = locBackendSyncData; assocData = backendSyncData->getAssocitaionData();
        //
        //   // (1) merge non-deterministic same-individuals:
        //   if !backendSyncData->hasReuseNonDeterministicSameIndividualMerged() && assocData:
        //     reuseExpDepTrackPoint = backendSyncData->getBackendExpansionReuseDependencyTrackPoint();
        //     nonDetSameIndiLabel = assocData->getLabelCacheEntry(NONDETERMINISTIC_SAME_INDIVIDUAL_SET_LABEL);
        //     if nonDetSameIndiLabel:
        //       mergingIntoId = assocData->getRepresentativeSameIndividualId();
        //       visitIndividualIdsOfAssociatedIndividualSetLabel(...) { mergingIntoId = min(mergingIntoId, sameIndiId); };
        //       visitIndividualIdsOfAssociatedIndividualSetLabel(..., |sameIndiId| {
        //         if sameIndiId != mergingIntoId:
        //           locMergingIntoIndiNode = getLocalizedForcedBackendInitializedNominalIndividualNode(mergingIntoId, ctx);  // u17/u23
        //           if !mergedHash->contains(sameIndiId):
        //             locMergingSameIndiNode = getLocalizedForcedBackendInitializedNominalIndividualNode(sameIndiId, ctx);
        //             if !mergedHash->contains(sameIndiId):
        //               if isIndividualNodesMergeable(into, same, clashDes, ctx):                  // merge unit
        //                 mergingSameIndiDepTrackPoint = base continue TP (or from merging hash);
        //                 createSAMEINDIVIDUALMERGEDependency(nextTP, into, reuseExpDepTrackPoint, mergingSameIndiDepTrackPoint, ctx);  // merge unit
        //                 locMergingIntoIndiNode = getMergedIndividualNodes(into, same, nextTP, ctx);                       // merge unit
        //               else:
        //                 build clashDescriptors (createClashedConceptDescriptor x3); throw CCalculationClashProcessingException;  // [exceptions]
        //         return true; }, ctx);
        //     locBackendSyncData->setReuseNonDeterministicSameIndividualMerged(true);
        //
        //   modifingIndiNode = getCorrectedMergedIntoIndividualNode(indiNode, ctx);                       // u14 (sibling)
        //
        //   // (2) add non-deterministic concepts:
        //   if !backendSyncData->hasReuseNonDeterministicConceptsAdded() && assocData:
        //     conLabel = assocData->getLabelCacheEntry(FULL_CONCEPT_SET_LABEL);
        //     if conLabel && conLabel->hasNondeterministicElements():
        //       visitConceptsOfAssociatedFullConceptSetLabel(assocData, conLabel, |concept, negation, deterministic| {
        //         if !deterministic: addConceptToIndividual(concept, negation, modifingIndiNode, reuseExpDepTrackPoint, false, false, ctx);  // expansion unit
        //         return true; }, false, true, ctx);
        //     locBackendSyncData->setReuseNonDeterministicConceptsAdded(true);
        //
        //   // (3) create missing non-deterministic neighbour role links:
        //   if assocData && assocData->getLabelCacheEntry(NONDETERMINISTIC_COMBINED_NEIGHBOUR_INSTANTIATED_ROLE_SET_LABEL):
        //     neighbourExpansionDataHash = locBackendSyncData->getNeighbourExpansionDataHash(true);
        //     neighbourRoleSetArray = assocData->getRoleSetNeighbourArray();
        //     if neighbourRoleSetArray:
        //       for i in 0..indexData->getArraySize():
        //         neighbourRoleSetlabel = indexData->getNeighbourRoleSetLabel(i);
        //         visitRolesOfAssociatedNeigbourRoleSetLabel(assocData, neighbourRoleSetlabel,
        //           |role, inversed, assertionLinkBase, nominalLinkBase, nondeterministic| {
        //             if nondeterministic && role && role->getRoleTag() > 1:
        //               markIndividualNodeBackendNonConceptSetRelatedAndNeighbourLabelRelatedProcessing(modifingIndiNode, ctx);  // u24
        //               neighbourRoleSetArray->at(i).visitNeighbourIndividualIds(|neighbourIndiId| {
        //                 if isNominalIndividualNodeAvailable(-neighbourIndiId, ctx):                                          // u16
        //                   neighbourNode = getCorrectedNominalIndividualNode(-neighbourIndiId, ctx);                          // u16
        //                   requireLinkCreation = (!neighbourNode) || link-missing-for(role/inverseRole);
        //                   if requireLinkCreation:
        //                     // ensure deterministic links first (expandIndividualNeighbourNodeFromBackendCache x up-to-4)  // u23
        //                     // plus merged-into-neighbour id variant;
        //                     locNeighbourNode = getLocalizedIndividual(neighbourNode, true, ctx);                            // u17
        //                     nominalConDepTrackPoint = (from neighbour merging hash);
        //                     if !inversed: build VALUE/REUSEBACKENDVALUE dep; createNewIndividualsLinksReapplyed(modifingIndiNode, locNeighbourNode, role->getIndirectSuperRoleList(), role, nextTP, true, ctx);  // reapply unit
        //                     else:          build VALUE/REUSEBACKENDVALUE dep; createNewIndividualsLinksReapplyed(locNeighbourNode, modifingIndiNode, ..., ctx);
        //                     propagateIndividualNodeModified(locNeighbourNode, ctx);                                          // sibling
        //                     addIndividualToProcessingQueue(locNeighbourNode, ctx);                                           // u04
        //                 return true; });
        //             return true; });
        //
        //   // (4) state non-deterministic different individuals as distinct:
        //   if !backendSyncData->hasReuseNonDeterministicDifferentIndividualStated() && assocData:
        //     nonDetDiffIndiLabel = assocData->getLabelCacheEntry(NONDETERMINISTIC_DIFFRENT_INDIVIDUAL_SET_LABEL);
        //     detSameIndiLabel    = assocData->getLabelCacheEntry(DETERMINISTIC_SAME_INDIVIDUAL_SET_LABEL);
        //     if nonDetDiffIndiLabel:
        //       visitIndividualIdsOfAssociatedIndividualSetLabel(assocData, nonDetDiffIndiLabel, |diffIndiId| {
        //         if diffIndiId != nominalId && !hasIndividualIdsInAssociatedIndividualSetLabel(assocData, detSameIndiLabel, diffIndiId):
        //           locDifferentIndiNode = getLocalizedForcedBackendInitializedNominalIndividualNode(diffIndiId, ctx);
        //           corrIndiNode = getCorrectedMergedIntoIndividualNode(modifingIndiNode, ctx);
        //           if mergedHash->hasMergedIndividual(diffIndiId):
        //             build clashDescriptors x2; throw CCalculationClashProcessingException;            // [exceptions]
        //           else: createIndividualsDistinct(corrIndiNode, locDifferentIndiNode, reuseExpDepTrackPoint, ctx);  // merge/nominal unit
        //         return true; }, ctx);
        //     locBackendSyncData->setReuseNonDeterministicDifferentIndividualStated(true);
        //
        //   return lazyNeighboursExpansionSucceded;
        //
        // Held PORT-PENDING: every typed local is a not-yet-ported backend-cache class
        // (sync data, association/label cache items, role-set neighbour array, the
        // `mBackendCacheHandler` visitors) plus the merge unit
        // (`isIndividualNodesMergeable`/`getMergedIndividualNodes`/SAMEINDIVIDUALMERGE
        // dependency), the per-neighbour expand helpers (u23), the
        // link-reapply/distinct creators, and the two clash-throw control-flow exits.
        // The siblings ported elsewhere
        // (`markIndividualNodeBackendNonConceptSetRelatedAndNeighbourLabelRelatedProcessing`
        // u24, `is_nominal_individual_node_available`/`get_corrected_nominal_individual_node`
        // u16, `get_corrected_merged_into_individual_node` u14,
        // `add_individual_to_processing_queue` u04) become live on the reconcile pass.
        // The C++ result `lazyNeighboursExpansionSucceded` is constant `true`.
        let _ = (indi_node, calc_alg_context);
        true
    }

    // =======================================================================
    // Backend-cache concept synchronisation tests (cpp 26283–26407).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::testIndividualNodeBackendCacheConceptsSynchronization`.
    /// cpp 26283–26362.
    ///
    /// Re-checks whether the node is still fully synchronised with its backend-cached
    /// association: it requires a completely-handled association, that every newly
    /// merged deterministic representative shares the same full-concept-set label,
    /// and that every newly added (non-nominal) concept descriptor is present in the
    /// associated full-concept-set label (respecting determinism). It advances the
    /// last-tested-merged / last-tested-concept cursors and, on desync, clears the
    /// node's `backendCacheSynchron` flag. Returns the synchronisation verdict.
    pub fn test_individual_node_backend_cache_concepts_synchronization(
        &mut self,
        indi_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // Faithful transcription of cpp 26283–26362. The live process-side
        // backend-sync state is wired below; W6 cache association/label semantics
        // are still held at their exact Konclude call sites.
        //
        //   backendSynched = true;
        //   backendSyncData    = indiNode->getIndividualBackendCacheSynchronisationData(false);
        //   locBackendSyncData = indiNode->getIndividualBackendCacheSynchronisationData(true);
        //   if backendSyncData && backendSyncData->isBackendCacheSynchron():
        //     assocData = backendSyncData->getAssocitaionData();
        //     if !assocData || !assocData->isCompletelyHandled():
        //       backendSynched = false;
        //     else:
        //       conceptLabelItem = assocData->getLabelCacheEntry(FULL_CONCEPT_SET_LABEL);
        //       testIndividualNodeBackendCacheNewMergings(indiNode, ctx);                              // merge unit
        //       backendSyncData = indiNode->getIndividualBackendCacheSynchronisationData(false);
        //       if mergedLinker != lastSynchronizedConceptsTestedMergedNodeLinker:
        //         visitNewlyMergedOnlyDeterministicRepresentativeIndividualsBackendSynchronisationData(indiNode,
        //             mergedLinker, lastSynchronizedConceptsTestedMergedNodeLinker, false,
        //             |base, locNode, backSyncTP| {
        //               mergedAssocData = locNode->getIndividualBackendCacheSynchronisationData(false)->getAssocitaionData();
        //               if mergedAssocData->getLabelCacheEntry(FULL_CONCEPT_SET_LABEL) != conceptLabelItem: backendSynched=false;
        //               return false; }, ctx);
        //         locBackendSyncData = getLocalizedIndividualBackendCacheSnychronisationData(indiNode, ctx);  // u17
        //         locBackendSyncData->setLastSynchronizedConceptsTestedMergedNodeLinker(mergedLinker);
        //       lastTestedConDes = backendSyncData->getLastSynchronizationTestedConceptDescriptor();
        //       conSet = indiNode->getReapplyConceptLabelSet(false);
        //       if conSet && backendSynched:
        //         conDesLinker = conSet->getAddingSortedConceptDescriptionLinker();
        //         if conDesLinker != lastTestedConDes:
        //           nominalConcept = indiNode->getNominalIndividual()->getIndividualNominalConcept();
        //           lastSyncConDes = lastTestedConDes;
        //           for conDesIt = conDesLinker; conDesIt && conDesIt != lastTestedConDes; conDesIt = conDesIt->getNext():
        //             if conDesIt->getConcept() != nominalConcept || conDesIt->isNegated():
        //               nondeterministic = hasNondeterministicDependency(conDesIt->getDependencyTrackPoint(), ctx);
        //               if !mBackendCacheHandler || !mBackendCacheHandler->hasConceptInAssociatedFullConceptSetLabel(
        //                       assocData, conceptLabelItem, conDesIt->getConcept(), conDesIt->isNegated(), !nondeterministic, ctx):
        //                 backendSynched=false; lastSyncConDes=conDesIt;
        //           if !backendSynched && lastSyncConDes: lastSyncConDes = lastSyncConDes->getNext();
        //           locBackendSyncData = getLocalizedIndividualBackendCacheSnychronisationData(indiNode, ctx);  // u17
        //           locBackendSyncData->setLastSynchronizationTestedConceptDescriptor(conDesLinker);
        //           locBackendSyncData->setLastSynchedConceptDescriptor(lastSyncConDes);
        //       else: backendSynched = false;
        //     if !backendSynched:
        //       locBackendSyncData = getLocalizedIndividualBackendCacheSnychronisationData(indiNode, ctx);  // u17
        //       locBackendSyncData->setBackendCacheSynchron(backendSynched);
        //   else: backendSynched = false;
        //   return backendSynched;
        //
        // Held W6-DEFER[api]: assocData->isCompletelyHandled(),
        // assocData->getLabelCacheEntry(FULL_CONCEPT_SET_LABEL), the backend
        // cache-handler concept-membership query, nominal-concept filtering, and
        // the newly-merged deterministic representative visitor's association
        // label comparison. NB the C++ has a dead duplicated `return backendSynched;`.
        let mut backend_synched = true;
        let mut backend_sync_data = calc_alg_context
            .process_context()
            .node(indi_node)
            .individual_backend_cache_synchronisation_data(false);

        if backend_sync_data.is_some()
            && calc_alg_context
                .process_context()
                .backend_sync_data(backend_sync_data)
                .is_backend_cache_synchron()
        {
            let assoc_data = calc_alg_context
                .process_context()
                .backend_sync_data(backend_sync_data)
                .get_associtaion_data();
            if assoc_data.is_none() {
                backend_synched = false;
            } else {
                // W6-DEFER[api]: assocData->isCompletelyHandled() and the
                // FULL_CONCEPT_SET_LABEL cache item read.
                self.test_individual_node_backend_cache_new_mergings(indi_node, calc_alg_context);
                backend_sync_data = calc_alg_context
                    .process_context()
                    .node(indi_node)
                    .individual_backend_cache_synchronisation_data(false);

                let (merged_linker, last_synchronized_merged_linker) = {
                    let sync_data = calc_alg_context
                        .process_context()
                        .backend_sync_data(backend_sync_data);
                    (
                        sync_data.get_merged_individual_node_linker().to_vec(),
                        sync_data
                            .get_last_synchronized_concepts_tested_merged_node_linker()
                            .to_vec(),
                    )
                };
                if merged_linker != last_synchronized_merged_linker {
                    // W6-DEFER[api]: visitNewlyMergedOnlyDeterministicRepresentativeIndividualsBackendSynchronisationData(...)
                    // and merged association full-concept-label equality check.
                    let loc_backend_sync_data = self
                        .get_localized_individual_backend_cache_snychronisation_data(
                            indi_node,
                            calc_alg_context,
                        );
                    calc_alg_context
                        .process_context_mut()
                        .backend_sync_data_mut(loc_backend_sync_data)
                        .set_last_synchronized_concepts_tested_merged_node_linker(merged_linker);
                    backend_sync_data = loc_backend_sync_data;
                }

                let last_tested_con_des = calc_alg_context
                    .process_context()
                    .backend_sync_data(backend_sync_data)
                    .get_last_synchronization_tested_concept_descriptor();
                let con_set = calc_alg_context
                    .process_context_mut()
                    .node_mut(indi_node)
                    .get_reapply_concept_label_set(false);
                if con_set.is_some() && backend_synched {
                    let con_des_linker = calc_alg_context
                        .process_context()
                        .label_set(con_set)
                        .get_adding_sorted_concept_description_linker();
                    if con_des_linker != last_tested_con_des {
                        // W6-DEFER[api]: nominalConcept lookup, exact descriptor-chain
                        // scan, nondeterminism test, and
                        // mBackendCacheHandler->hasConceptInAssociatedFullConceptSetLabel(...).
                        // Until that query is live, preserve Konclude's cursor writes
                        // at this update point over the real backend-sync object.
                        let loc_backend_sync_data = self
                            .get_localized_individual_backend_cache_snychronisation_data(
                                indi_node,
                                calc_alg_context,
                            );
                        calc_alg_context
                            .process_context_mut()
                            .backend_sync_data_mut(loc_backend_sync_data)
                            .set_last_synchronization_tested_concept_descriptor(con_des_linker)
                            .set_last_synched_concept_descriptor(con_des_linker);
                        backend_sync_data = loc_backend_sync_data;
                    }
                } else {
                    backend_synched = false;
                }
            }
            if !backend_synched {
                let loc_backend_sync_data = self
                    .get_localized_individual_backend_cache_snychronisation_data(
                        indi_node,
                        calc_alg_context,
                    );
                calc_alg_context
                    .process_context_mut()
                    .backend_sync_data_mut(loc_backend_sync_data)
                    .set_backend_cache_synchron(backend_synched);
            }
        } else {
            backend_synched = false;
        }
        backend_synched
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::validateBackendSynchronisationContinued`.
    /// cpp 26368–26407.
    ///
    /// The incremental counterpart of the full re-check above, run right after a
    /// concept was added: from the last-synchronisation-tested descriptor it walks
    /// the newly added (non-nominal) concept descriptors (skipping the just-added one)
    /// and confirms each is present in the associated full-concept-set label; it
    /// advances the last-synched / last-tested cursors and writes the
    /// `backendCacheSynchron` flag. Returns the (continued) synchronisation verdict.
    ///
    /// KONCLUDE-PORT-NOTE[api]: backend-sync state and label-set head access are
    /// live. The backend-cache-handler membership query and the exact descriptor
    /// chain scan remain deferred.
    pub fn validate_backend_synchronisation_continued(
        &mut self,
        indi: NodeId,
        backend_sync_data: BackendSyncDataId,
        added_concept: ConceptId,
        added_concept_negation: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut backend_synched = true;
        if backend_sync_data.is_some()
            && calc_alg_context
                .process_context()
                .backend_sync_data(backend_sync_data)
                .is_backend_cache_synchron()
        {
            let last_tested_con_des = calc_alg_context
                .process_context()
                .backend_sync_data(backend_sync_data)
                .get_last_synchronization_tested_concept_descriptor();
            let con_set = calc_alg_context
                .process_context_mut()
                .node_mut(indi)
                .get_reapply_concept_label_set(false);
            let assoc_data = calc_alg_context
                .process_context()
                .backend_sync_data(backend_sync_data)
                .get_associtaion_data();
            if con_set.is_some() && assoc_data.is_some() {
                let con_des_linker = calc_alg_context
                    .process_context()
                    .label_set(con_set)
                    .get_adding_sorted_concept_description_linker();
                let mut con_des_it: ConDescId = con_des_linker;
                if added_concept.is_some()
                    && con_des_it.is_some()
                    && con_des_it != last_tested_con_des
                {
                    if calc_alg_context
                        .process_context()
                        .con_desc(con_des_it)
                        .get_concept()
                        == added_concept
                        || calc_alg_context
                            .process_context()
                            .con_desc(con_des_it)
                            .is_negated()
                            == added_concept_negation
                    {
                        con_des_it = calc_alg_context.process_context().con_desc(con_des_it).next;
                    }
                }

                // W6-DEFER[api]: nominalConcept lookup, exact con-descriptor chain scan,
                // and mBackendCacheHandler->hasConceptInAssociatedFullConceptSetLabel(...).
                // With the cache-membership query still deferred, preserve the cursor
                // writes over the live backend-sync object at Konclude's update points.
                if backend_synched {
                    calc_alg_context
                        .process_context_mut()
                        .backend_sync_data_mut(backend_sync_data)
                        .set_last_synched_concept_descriptor(con_des_it);
                }
                calc_alg_context
                    .process_context_mut()
                    .backend_sync_data_mut(backend_sync_data)
                    .set_last_synchronization_tested_concept_descriptor(con_des_linker);
            } else {
                backend_synched = false;
            }
            calc_alg_context
                .process_context_mut()
                .backend_sync_data_mut(backend_sync_data)
                .set_backend_cache_synchron(backend_synched);
        } else {
            backend_synched = false;
        }
        backend_synched
    }

    // =======================================================================
    // Saturation-based concept-unsatisfiability test (cpp 26900–26921).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::isConceptUnsatisfiabilitySaturated`.
    /// cpp 26900–26921.
    ///
    /// Decides whether the (possibly negated) concept is already known unsatisfiable
    /// from the approximate saturation pre-pass: it follows the concept's process
    /// data → concept reference linking → saturation reference linking → the
    /// saturation individual process node, and returns `true` iff that node's
    /// indirect status flags carry the clashed flag. Returns `false` when any hop is
    /// absent.
    ///
    pub fn is_concept_unsatisfiability_saturated(
        &mut self,
        concept: ConceptId,
        negation: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        //   conceptData = concept->getConceptData();
        //   saturationIndiNode = nullptr;
        let concept_data = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_concept_data();
        let mut saturation_indi_node = SatNodeId::NONE;
        if concept_data != INVALID {
            // conProcData = (CConceptProcessData*)conceptData;
            let con_proc_data = Id::new(concept_data);
            // conRefLinking = conProcData->getConceptReferenceLinking();
            let con_ref_linking = calc_alg_context
                .ontology_arenas()
                .concept_process_data(con_proc_data)
                .get_concept_reference_linking();
            if con_ref_linking.is_some() {
                // confSatRefLinkingData = (CConceptSaturationReferenceLinkingData*)conRefLinking;
                let sat_calc_ref_link_data = calc_alg_context
                    .ontology_arenas()
                    .concept_saturation_reference_linking_data(con_ref_linking)
                    .get_concept_saturation_reference_linking_data(negation);
                if sat_calc_ref_link_data.is_some() {
                    saturation_indi_node = calc_alg_context
                        .ontology_arenas()
                        .saturation_concept_reference_linking(sat_calc_ref_link_data)
                        .get_individual_process_node_for_concept();
                }
            }
        }

        if saturation_indi_node.is_some() {
            return calc_alg_context
                .process_context()
                .sat_node(saturation_indi_node)
                .indirect_status_flags
                .has_flags_code(
                    IndividualSaturationProcessNodeStatusFlags::INDSATFLAGCLASHED,
                    false,
                );
        }
        false
    }

    // =======================================================================
    // Backend-cache expansion / synchronisation queue feeders (cpp 27587–27641).
    // The per-node "already queued" flag guard fixes the boolean return and is
    // substrate-portable, so it is ported LIVE; only the databox queue
    // getter + `insertIndiviudalProcessNode` + `STATINC` are deferred.
    //
    // KONCLUDE-PORT-NOTE[api]: node.rs exposes the queued flags as public bool
    // FIELDS (`backend_*_queued`) with no `is_/set_` wrapper, and this unit may
    // edit only `u25.rs`, so the C++ `isX()`/`setX(true)` becomes a direct read /
    // assignment of the public field through the arena accessor.
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addIndividualToBackendSynchronisationRetestQueue`.
    /// cpp 27587–27596.
    pub fn add_individual_to_backend_synchronisation_retest_queue(
        &mut self,
        individual: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // if (!individual->isBackendSynchronRetestProcessingQueued()) {
        //   individual->setBackendSynchronRetestProcessingQueued(true);
        //   backendCacheSyncQueue = calcAlgContext->getProcessingDataBox()->getBackendCacheSynchronizationProcessingQueue(true);
        //   backendCacheSyncQueue->insertIndiviudalProcessNode(individual);
        //   STATINC(INDINODESADDEDPROCESSINGQUEUECOUNT,calcAlgContext);
        //   return true; }
        // return false;
        if !calc_alg_context
            .process_context()
            .node(individual)
            .is_backend_synchron_retest_processing_queued()
        {
            calc_alg_context
                .process_context_mut()
                .node_mut(individual)
                .set_backend_synchron_retest_processing_queued(true);
            let backend_cache_sync_queue =
                calc_alg_context.get_backend_cache_synchronization_processing_queue(true);
            calc_alg_context
                .process_context_mut()
                .indi_unsorted_proc_queue_mut(backend_cache_sync_queue)
                .insert_indiviudal_process_node(individual);
            // W3-DEFER[api]: STATINC(INDINODESADDEDPROCESSINGQUEUECOUNT, calcAlgContext);
            return true;
        }
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addIndividualToBackendDirectInfluenceExpansionQueue`.
    /// cpp 27598–27607.
    pub fn add_individual_to_backend_direct_influence_expansion_queue(
        &mut self,
        individual: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // if (!individual->isBackendDirectInfluenceExpansionQueued()) {
        //   individual->setBackendDirectInfluenceExpansionQueued(true);
        //   backendCacheSyncQueue = calcAlgContext->getProcessingDataBox()->getBackendDirectInfluenceExpansionQueue(true);
        //   backendCacheSyncQueue->insertIndiviudalProcessNode(individual);
        //   STATINC(INDINODESADDEDPROCESSINGQUEUECOUNT, calcAlgContext);
        //   return true; }
        // return false;
        if !calc_alg_context
            .process_context()
            .node(individual)
            .is_backend_direct_influence_expansion_queued()
        {
            calc_alg_context
                .process_context_mut()
                .node_mut(individual)
                .set_backend_direct_influence_expansion_queued(true);
            let backend_cache_sync_queue =
                calc_alg_context.get_backend_direct_influence_expansion_queue(true);
            calc_alg_context
                .process_context_mut()
                .indi_unsorted_proc_queue_mut(backend_cache_sync_queue)
                .insert_indiviudal_process_node(individual);
            // W3-DEFER[api]: STATINC(INDINODESADDEDPROCESSINGQUEUECOUNT, calcAlgContext);
            return true;
        }
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addIndividualToBackendIndirectCompatibilityExpansionQueue`.
    /// cpp 27609–27618.
    pub fn add_individual_to_backend_indirect_compatibility_expansion_queue(
        &mut self,
        individual: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // if (!individual->isBackendIndirectCompatibilityExpansionQueued()) {
        //   individual->setBackendIndirectCompatibilityExpansionQueued(true);
        //   backendCacheSyncQueue = calcAlgContext->getProcessingDataBox()->getBackendIndirectCompatibilityExpansionQueue(true);
        //   backendCacheSyncQueue->insertIndiviudalProcessNode(individual);
        //   STATINC(INDINODESADDEDPROCESSINGQUEUECOUNT, calcAlgContext);
        //   return true; }
        // return false;
        if !calc_alg_context
            .process_context()
            .node(individual)
            .is_backend_indirect_compatibility_expansion_queued()
        {
            calc_alg_context
                .process_context_mut()
                .node_mut(individual)
                .set_backend_indirect_compatibility_expansion_queued(true);
            let backend_cache_sync_queue =
                calc_alg_context.get_backend_indirect_compatibility_expansion_queue(true);
            calc_alg_context
                .process_context_mut()
                .indi_unsorted_proc_queue_mut(backend_cache_sync_queue)
                .insert_indiviudal_process_node(individual);
            // W3-DEFER[api]: STATINC(INDINODESADDEDPROCESSINGQUEUECOUNT, calcAlgContext);
            return true;
        }
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addIndividualToBackendReuseExpansionQueue`.
    /// cpp 27621–27630.
    pub fn add_individual_to_backend_reuse_expansion_queue(
        &mut self,
        individual: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // if (!individual->isBackendReuseExpansionQueued()) {
        //   individual->setBackendReuseExpansionQueued(true);
        //   backendCacheSyncQueue = calcAlgContext->getProcessingDataBox()->getBackendIndividualReuseExpansionQueue(true);
        //   backendCacheSyncQueue->insertIndiviudalProcessNode(individual);
        //   STATINC(INDINODESADDEDPROCESSINGQUEUECOUNT, calcAlgContext);
        //   return true; }
        // return false;
        if !calc_alg_context
            .process_context()
            .node(individual)
            .backend_reuse_expansion_queued
        {
            calc_alg_context
                .process_context_mut()
                .node_mut(individual)
                .set_backend_reuse_expansion_queued(true);
            let backend_cache_sync_queue =
                calc_alg_context.get_backend_individual_reuse_expansion_queue(true);
            calc_alg_context
                .process_context_mut()
                .indi_unsorted_proc_queue_mut(backend_cache_sync_queue)
                .insert_indiviudal_process_node(individual);
            // W3-DEFER[api]: STATINC(INDINODESADDEDPROCESSINGQUEUECOUNT, calcAlgContext);
            return true;
        }
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addIndividualToBackendNeighbourExpansionQueue`.
    /// cpp 27632–27641.
    ///
    /// KONCLUDE-PORT-NOTE[api]: this one feeds the
    /// `CIndividualLinkerRotationProcessingQueue` (vs the unsorted queue of the other
    /// four); the deferred insert targets `getBackendIndividualNeighbourExpansionQueue`.
    pub fn add_individual_to_backend_neighbour_expansion_queue(
        &mut self,
        individual: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // if (!individual->isBackendNeighbourExpansionQueued()) {
        //   individual->setBackendNeighbourExpansionQueued(true);
        //   backendCacheSyncQueue = calcAlgContext->getProcessingDataBox()->getBackendIndividualNeighbourExpansionQueue(true);
        //   backendCacheSyncQueue->insertIndiviudalProcessNode(individual);
        //   STATINC(INDINODESADDEDPROCESSINGQUEUECOUNT, calcAlgContext);
        //   return true; }
        // return false;
        if !calc_alg_context
            .process_context()
            .node(individual)
            .is_backend_neighbour_expansion_queued()
        {
            calc_alg_context
                .process_context_mut()
                .node_mut(individual)
                .set_backend_neighbour_expansion_queued(true);
            let backend_cache_sync_queue =
                calc_alg_context.get_backend_individual_neighbour_expansion_queue(true);
            calc_alg_context
                .process_context_mut()
                .indi_rotation_proc_queue_mut(backend_cache_sync_queue)
                .insert_indiviudal_process_node(individual);
            // W3-DEFER[api]: STATINC(INDINODESADDEDPROCESSINGQUEUECOUNT, calcAlgContext);
            return true;
        }
        false
    }
}
