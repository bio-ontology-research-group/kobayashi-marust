//! `completion::u12` — Merge-handling family, batch 1 (port unit #12 of 36).
//!
//! Faithful port of the first 13 merge-handling methods of Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`
//! (manifest `01-completion-methods.md`, "Unit 12", cpp ranges 1686–15093):
//!
//!   * `findNextPossibleInstanceMergingIndividual` (the L15 attempt-loop wrapper +
//!     the L175 search workhorse),
//!   * `tryPossibleInstanceMerging` (the possible-instance branching-task launcher),
//!   * `incrementalMergeWithPreviousNondeterministicCompletionGraph` /
//!     `…DeterministicCompletionGraph` (the incremental-reasoning graph merge),
//!   * the 6 `createMERGE*Dependency` / `createSAMEINDIVIDUALMERGEDependency`
//!     dependency-node factory wrappers,
//!   * `generateDebugMergingQueueString` (debug),
//!   * `mergeMergingIndividualNodesPairwise` (pairwise `≤n` merge task fan-out).
//!
//! KONCLUDE-PORT-NOTE[ownership]: a method is a member of
//! `CCalculationTableauCompletionTaskHandleAlgorithm`, so it becomes `&mut self`
//! plus the threaded per-thread context `calc_alg_context: &mut
//! CalculationAlgorithmContextBase` (the C++ `CCalculationAlgorithmContextBase*`).
//! `CIndividualProcessNode*&` / `CConceptProcessDescriptor*&` out/in-out
//! pointer-references become `&mut NodeId` / `&mut ConProcDescId` (arena ids);
//! `CConceptDescriptor*` → `ConDescId`, `CDependencyTrackPoint*` → `TrackPointId`,
//! `CBranchingMergingProcessingRestrictionSpecification*` → `RestrictionSpecId`.
//! Per the W3.5 accessor convention, an `indi->getX()` deref resolves through
//! `ctx.used_process_context().node(id).get_x()` (read) / `…_mut(id)` (mutate),
//! concepts/roles through `ctx.ontology_arenas()`, the databox through
//! `ctx.processing_data_box{,_mut}()`.
//!
//! What ports faithfully here vs. what defers:
//!   * `createMERGEDCONCEPTDependency` is live; the remaining `createMERGE*`
//!     dependency-node creators preserve the gate `if (mConfBuildDependencies)
//!     depNode = …DependencyFactory->create…();` but still defer the concrete
//!     factory allocation.
//!   * The remaining 7 are `PORT-PENDING`: every one bottoms out in subsystems with
//!     no port yet — the Task machinery (`CSatisfiableCalculationTask`,
//!     `createDependendBranchingTaskList`, `createCalculationAlgorithmContext`,
//!     `prepareBranchedTaskProcessing`, `communicateTaskCreation`), the
//!     exceptions-as-control-flow (`CCalculationStopProcessingException`,
//!     `CCalculationClashProcessingException`), the backend cache
//!     (`mBackendCacheHandler`) and incremental-expansion handler (`mIncExpHandler`),
//!     the un-ported `CPossibleInstancesIndividualsMergingData`/`…Linker`, plus
//!     sibling merge helpers that land in units 13–15 (`getLocalizedIndividual`,
//!     `getMergedIndividualNodes`, `isIndividualNodesMergeable`,
//!     `isIndividualNodesMergeableWithoutNewRuleApplications`,
//!     `createIndividualMergeCausingDescriptors`, `createMergeBranchingTask`,
//!     `getSuccessorIndividual`, `createClashedConceptDescriptor`,
//!     `installIndividualNodeRoleLinkReapplied`, `applyReapplyQueueConcepts[Restricted]`,
//!     `pruneIncrementalRemovedSuccessors`, `identifyCompatibilityChangedNominalIndividualNodes`).
//!     Each keeps its faithful signature; the full C++ control flow (every branch)
//!     is transcribed in the doc-comment so a later wave fills the body without
//!     re-reading the source. Logic is documented, never silently dropped.

#![allow(dead_code)]
#![allow(unused_variables)]
// The 6 createMERGE* wrappers keep `let mut dep_node` (faithful to the C++ where it
// is reassigned inside the build-dependencies guard) even though the factory call
// is W6-DEFER'd, so the reassignment is currently absent.
#![allow(unused_mut)]

use super::super::model::substrate::{Cint64, Id};
use super::super::process::dependency::{DepKind, DependencyNode};
use super::super::process::{
    ConDescId, ConProcDescId, DepLinkId, DependencyId, NodeId, RestrictionSpecId, TrackPointId,
};
use super::context::CalculationAlgorithmContextBase;

impl super::algorithm::CompletionTaskHandleAlgorithm {
    // =======================================================================
    // Possible-instance merging search (cpp 1686–2023).
    //
    // KONCLUDE-PORT-NOTE[api]: `CPossibleInstancesIndividualsMergingData*` and its
    // `CPossibleInstancesIndividualsMergingLinker` chain are an un-ported Task/merge
    // data structure; the in/out scratch (`testConceptLabelSetHash`, the found-indi
    // out-params) is a Cache `CPROCESSHASH<…>` + raw out-pointers. Modelled as
    // opaque `Cint64` for the merging data / hash and `&mut` for the out-params.
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::findNextPossibleInstanceMergingIndividual`
    /// (the L15 attempt-loop wrapper, cpp 1686–1700).
    ///
    /// C++ control flow (every branch preserved):
    /// ```text
    /// processingDataBox = calcAlgContext->getProcessingDataBox()
    /// if (possInstanceMergingData->areAllPossibleInstancesIndividualsNonMerging()
    ///     || processingDataBox->getRemainingPossibleInstanceIndividualMergingLimit() == 0)
    ///   return false
    /// maxMergingAttemptCount = possInstanceMergingData->getMaxMergingAttemptCount()
    /// foundPossIndiMerging = false
    /// for (i = 0; i < maxMergingAttemptCount && !foundPossIndiMerging; ++i)
    ///   foundPossIndiMerging = findNextPossibleInstanceMergingIndividual(
    ///       processIndi, possInstanceMergingData, calcAlgContext, testConceptLabelSetHash,
    ///       i, foundMergingIndiNode, foundMergingIndiId, ruleApplicationFreeMerging)
    /// return foundPossIndiMerging
    /// ```
    pub fn find_next_possible_instance_merging_individual(
        &mut self,
        process_indi: NodeId,
        // W6-DEFER[api]: CPossibleInstancesIndividualsMergingData* — un-ported Task/merge data.
        poss_instance_merging_data: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
        // W6-DEFER[api]: CPROCESSHASH<CBackendRepresentativeMemoryLabelCacheItem*,bool>*& — Cache scratch.
        test_concept_label_set_hash: &mut Cint64,
        found_merging_indi_node: &mut NodeId,
        found_merging_indi_id: &mut Cint64,
        rule_application_free_merging: &mut bool,
    ) -> bool {
        let _ = (
            process_indi,
            poss_instance_merging_data,
            calc_alg_context,
            test_concept_label_set_hash,
            found_merging_indi_node,
            found_merging_indi_id,
            rule_application_free_merging,
        );
        // PORT-PENDING: see structural transcription above. Needs the databox
        // possible-instance merging-limit getters and the un-ported
        // CPossibleInstancesIndividualsMergingData (areAllPossibleInstancesIndividualsNonMerging /
        // getMaxMergingAttemptCount) before the attempt loop can be wired to the
        // L175 overload below.
        todo!(
            "W3-DEFER: findNextPossibleInstanceMergingIndividual (wrapper) — \
             CPossibleInstancesIndividualsMergingData + databox merging-limit getters unported"
        );
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::findNextPossibleInstanceMergingIndividual`
    /// (the L175 search workhorse, cpp 1704–1878).
    ///
    /// C++ control flow (every branch preserved):
    /// ```text
    /// processingDataBox = calcAlgContext->getProcessingDataBox()
    /// if (allNonMerging || remainingLimit == 0) return false
    /// if (remainingLimit == -1) { /* TODO set a limit */ }
    /// else if (remainingLimit > 0) processingDataBox->setRemaining…(remaining - 1)
    ///
    /// nextLinker = lastLinker ? lastLinker->getNext() : possData->getLinker() (+allNonMerging=true)
    /// initialLinker = lastLinker = processingDataBox->getLastMergedPossibleInstanceIndividualLinker()
    /// foundLinker = nullptr; allNonMerging seeded as above
    ///
    /// backendSyncData = processIndi->getIndividualBackendCacheSynchronisationData(false)
    /// if (backendSyncData && !backendSyncData->hasNonConceptSetBackendLabelRelatedProcessing()):
    ///   conceptSetBackendLabelOnlyRelevant = true
    ///   conceptSetBackendLabelOnlyHasher = getIndividualRepresentativeBackendCacheConceptSetLabelProcessingHasher(assoc)
    ///
    /// foundPossibleInstanceMerging = false
    /// while (nextLinker && !foundPossibleInstanceMerging):
    ///   if (!nextLinker->isSatisfiableMerged() && nextLinker->getMergingAttemptCount() <= individualMax
    ///       && !nextLinker->isFullTestingScheduled()):
    ///     allNonMerging = false; nextLinker->incMergingAttempt(); possData->incMergingAttempt()
    ///     ++mStatPossibleInstanceMergingSearchIndiCount
    ///     mergingIndiId = nextLinker->getMergingIndividualId()
    ///     mergingTryable = false; possiblyRequiresRuleApplication = true; mergingIndiNode = nullptr
    ///     if (isNominalIndividualNodeAvailable(-mergingIndiId)):
    ///       mergingIndiNode = getCorrectedNominalIndividualNode(-mergingIndiId)
    ///       possiblyRequiresRuleApplication = false
    ///       mergingTryable = isIndividualNodesMergeableWithoutNewRuleApplications(
    ///                            processIndi, mergingIndiNode, &possiblyRequiresRuleApplication,
    ///                            foundPossibleInstanceMerging)
    ///     else:
    ///       assData = mBackendCacheHandler->getIndividualAssociationData(mergingIndiId)
    ///       if (assData):
    ///         if (conceptSetBackendLabelOnlyRelevant):
    ///           hasher = getIndividualRepresentativeBackendCacheConceptSetLabelProcessingHasher(assData)
    ///           if (conceptSetBackendLabelOnlyHasher == hasher): mergingTryable=true; possiblyRequiresRuleApplication=false
    ///         if (!mergingTryable):
    ///           conceptSetLabelItem = assData->getLabelCacheEntry(FULL_CONCEPT_SET_LABEL)
    ///           if (testConceptLabelSetHash && testConceptLabelSetHash->contains(item)):
    ///             mergingTryable = testConceptLabelSetHash->value(item)
    ///           else:
    ///             containsAtomicClash = false; baseConceptSet = processIndi->getReapplyConceptLabelSet(false)
    ///             mBackendCacheHandler->visitConceptsOfAssociatedFullConceptSetLabel(assData,item,
    ///                 [concept,negation,deterministic]{ if baseConceptSet->containsConcept(concept,!negation){containsAtomicClash=true; return false} return true })
    ///             mergingTryable = !containsAtomicClash
    ///             if (!testConceptLabelSetHash) testConceptLabelSetHash = alloc<CPROCESSHASH<…>>()
    ///             testConceptLabelSetHash->insert(item, mergingTryable)
    ///     if (mergingTryable):
    ///       if (!possiblyRequiresRuleApplication):
    ///         nextLinker->incMergingAttempt(); possData->incMergingAttempt(); ++mStat…FoundIndiCount
    ///         if (!nextLinker->isSatisfiableMerged()):
    ///           ++mStat…SuccessSubmitCount; ++mStat…TriviallySuccessCount
    ///           possData->incMergingSuccess(); nextLinker->setSatisfiableMerged()
    ///       else:
    ///         if (!foundPossibleInstanceMerging):
    ///           ++mStat…MaybeMergeableCount; foundPossibleInstanceMerging = true
    ///           if (!mergingIndiNode) mergingIndiNode = getLocalizedForcedBackendInitializedNominalIndividualNode(mergingIndiId)
    ///           if (foundMergingIndiNode) *foundMergingIndiNode = mergingIndiNode
    ///           if (foundMergingIndiId)   *foundMergingIndiId   = mergingIndiId
    ///           foundLinker = nextLinker
    ///     else: ++mStat…NotMergeableCount
    ///   else: ++mStat…SkipIndiCount
    ///   if (!foundLinker) foundLinker = nextLinker
    ///   lastLinker = nextLinker; nextLinker = nextLinker->getNext()
    ///
    /// if (allNonMerging) possData->setAllPossibleInstancesIndividualsNonMerging(true)
    /// if (!foundLinker) foundLinker = lastLinker
    /// processingDataBox->setLastMergedPossibleInstanceIndividualLinker(foundLinker)
    /// return foundPossibleInstanceMerging
    /// ```
    pub fn find_next_possible_instance_merging_individual_attempt(
        &mut self,
        process_indi: NodeId,
        poss_instance_merging_data: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
        test_concept_label_set_hash: &mut Cint64,
        individual_max_merging_attempt_count: Cint64,
        found_merging_indi_node: &mut NodeId,
        found_merging_indi_id: &mut Cint64,
        rule_application_free_merging: &mut bool,
    ) -> bool {
        let _ = (
            process_indi,
            poss_instance_merging_data,
            calc_alg_context,
            test_concept_label_set_hash,
            individual_max_merging_attempt_count,
            found_merging_indi_node,
            found_merging_indi_id,
            rule_application_free_merging,
        );
        // PORT-PENDING: see structural transcription above. Bottoms out in the
        // backend cache handler (getIndividualAssociationData /
        // visitConceptsOfAssociatedFullConceptSetLabel /
        // getIndividualRepresentativeBackendCacheConceptSetLabelProcessingHasher), the
        // un-ported CPossibleInstancesIndividualsMergingLinker chain, and the sibling
        // helpers isNominalIndividualNodeAvailable / getCorrectedNominalIndividualNode /
        // isIndividualNodesMergeableWithoutNewRuleApplications (unit 14) /
        // getLocalizedForcedBackendInitializedNominalIndividualNode.
        todo!(
            "W3-DEFER: findNextPossibleInstanceMergingIndividual (search) — backend cache handler + \
             possible-instances merging linker chain + unit-14 mergeability helpers unported"
        );
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::tryPossibleInstanceMerging`
    /// (cpp 1885–2023).
    ///
    /// C++ control flow (every branch preserved):
    /// ```text
    /// processingDataBox = calcAlgContext->getProcessingDataBox()
    /// if (possInstanceMergingData && mConfPossibleInstanceIndividualsMerging):
    ///   processorContext = calcAlgContext->getUsedTaskProcessorContext()
    ///   ++mStatPossibleInstanceMergingTryingCount; testConceptLabelSetHash = nullptr
    ///   foundMergingIndiId = -1; foundMergingIndiNode = nullptr; ruleApplicationFreeMerging = false
    ///   initContinueDepTrackPoint = calcAlgContext->getBaseDependencyNode()->getContinueDependencyTrackPoint()
    ///   hasNextMergingIndi = findNextPossibleInstanceMergingIndividual(processIndi, possData, …, &node,&id,&free)
    ///   if (hasNextMergingIndi):
    ///     ++mStatPossibleInstanceMergingCount; taskCreationCount = 2
    ///     newTaskList = createDependendBranchingTaskList(taskCreationCount)
    ///     newTaskIt = newTaskList
    ///     reuseDepNode = createMERGEPOSSIBLEINSTANCEINDIVIDUALDependencyNode(processIndi, initContinueDepTrackPoint, foundMergingIndiNode)
    ///     for (i = 0; i < taskCreationCount; ++i):
    ///       newSatCalcTask = newTaskIt
    ///       newProcessContext = newSatCalcTask->getProcessContext(processorContext)
    ///       newCalcAlgContext = createCalculationAlgorithmContext(processorContext, newProcessContext, newSatCalcTask)
    ///       newAllocMemMan = newCalcAlgContext->getUsedProcessTaskMemoryAllocationManager()
    ///       mergingAlternative = (i == 0)
    ///       if (mergingAlternative):
    ///         mergeNonDetDepTrackPoint = createNonDeterministicDependencyTrackPointBranch(reuseDepNode, false, newCalcAlgContext)
    ///         newProcessingDataBox = newSatCalcTask->getProcessingDataBox()
    ///         newProcessingDataBox->initProcessingDataBox(processingDataBox)
    ///         newProcessingDataBox->setBackendCacheLoadedAssociationHash(processingDataBox->getBackendCacheLoadedAssociationHash(true))
    ///         newProcessingDataBox->setPossibleInstanceIndividualMergedCount(+1)
    ///         newProcessingDataBox->setPossibleInstanceIndividualCurrentMergingCount(1)
    ///         newProcessTagger->incBranchingTag()
    ///         newLocProcessIndiNode = getLocalizedIndividual(processIndi, false)
    ///         newLocMergingIndiNode = getLocalizedIndividual(foundMergingIndiNode, false)
    ///         locMergedIndiNode = getMergedIndividualNodes(newLocProcessIndiNode, newLocMergingIndiNode, mergeNonDetDepTrackPoint)
    ///         if (possData->getMergingStreakFailCount() <= 0):
    ///           furtherMergeCount = processingDataBox->getPossibleInstanceIndividualMergingSize()
    ///           if (furtherMergeCount > 1):
    ///             currentMergedLinkersLinker = alloc; currentMergedLinkersLinker->initLinker(processingDataBox->getLastMerged…Linker())
    ///             currentlyMerged = 1
    ///             while (hasNextMergingIndi && currentlyMerged <= furtherMergeCount):
    ///               reset found{Id,Indi,Node,free}; hasNextMergingIndi = findNextPossibleInstanceMergingIndividual(locMergedIndiNode, possData, newCalcAlgContext, …)
    ///               if (hasNextMergingIndi):
    ///                 ++mStat…Count; ++currentlyMerged
    ///                 newLocMergingIndiNode = getLocalizedIndividual(foundMergingIndiNode, false)
    ///                 locMergedIndiNode = getMergedIndividualNodes(locMergedIndiNode, newLocMergingIndiNode, mergeNonDetDepTrackPoint)
    ///                 nextLinkersLinker = alloc; nextLinkersLinker->initLinker(newProcessingDataBox->getLastMerged…Linker())
    ///                 currentMergedLinkersLinker = nextLinkersLinker->append(currentMergedLinkersLinker)
    ///             newProcessingDataBox->setPossibleInstanceIndividualCurrentMergingCount(currentlyMerged)
    ///             newProcessingDataBox->setPossibleInstanceIndividualMergedCount(+currentlyMerged)
    ///             newProcessingDataBox->setCurrentMergedPossibleInstanceIndividualLinkersLinker(currentMergedLinkersLinker)
    ///           furtherMergeCount = (furtherMergeCount < 10) ? *2 : *20
    ///           newProcessingDataBox->setPossibleInstanceIndividualMergingSize(furtherMergeCount)
    ///         prepareBranchedTaskProcessing(locMergedIndiNode, newSatCalcTask, newCalcAlgContext)
    ///       else:
    ///         createNonDeterministicDependencyTrackPointBranch(reuseDepNode, false, newCalcAlgContext)
    ///         newProcessingDataBox = newSatCalcTask->getProcessingDataBox()
    ///         newProcessingDataBox->setPossibleInstanceIndividualMergingStopped(true)
    ///         newProcessingDataBox->setBackendCacheLoadedAssociationHash(processingDataBox->getBackendCacheLoadedAssociationHash(true))
    ///         newLocIndiNode = getLocalizedIndividual(processIndi, false)
    ///         prepareBranchedTaskProcessing(newLocIndiNode, newSatCalcTask, newCalcAlgContext)
    ///       newTaskPriority = calcAlgContext->getUsedTaskPriorityStrategy()->getPriorityForTaskReusing(newSatCalcTask, used, mergingAlternative)
    ///       newSatCalcTask->setTaskPriority(newTaskPriority)
    ///       newTaskIt = newTaskIt->getNext()
    ///     processorContext->getTaskProcessorCommunicator()->communicateTaskCreation(newTaskList)
    ///     throw CCalculationStopProcessingException(true)
    /// return false
    /// ```
    pub fn try_possible_instance_merging(
        &mut self,
        process_indi: NodeId,
        poss_instance_merging_data: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let _ = (process_indi, poss_instance_merging_data, calc_alg_context);
        // PORT-PENDING: see structural transcription above. NOW AVAILABLE: the
        // terminal `throw CCalculationStopProcessingException(true)` ports to
        // `calc_alg_context.raise_stop(true); return false;` (completion/clash.rs), and
        // getLocalizedIndividual is ported (u36). STILL the whole body bottoms out in the
        // Task subsystem (createDependendBranchingTaskList / createCalculationAlgorithmContext /
        // getProcessContext / prepareBranchedTaskProcessing / communicateTaskCreation /
        // getPriorityForTaskReusing, W6), the non-deterministic dependency branch
        // (createNonDeterministicDependencyTrackPointBranch), the per-task databox cloning
        // (initProcessingDataBox / backend-cache-loaded-association hash), and the unit-14/15
        // merge helper getMergedIndividualNodes. The in-unit
        // createMERGEPOSSIBLEINSTANCEINDIVIDUALDependencyNode wrapper is live.
        todo!(
            "W3-DEFER: tryPossibleInstanceMerging — Task creation/branching subsystem + \
             per-task databox cloning + getMergedIndividualNodes (unit-14/15) unported \
             (raise_stop + getLocalizedIndividual now available)"
        );
    }

    // =======================================================================
    // Incremental completion-graph merge (cpp 3102–3372).
    //
    // KONCLUDE-PORT-NOTE[api]: `mIncExpHandler`
    // (CIncrementalCompletionGraphCompatibleExpansionHandler) is an Algorithm-layer
    // stub with no method bodies; the previous-task databoxes come via the Task
    // subsystem. Both methods rewrite the individual-node vector against a previous
    // test's graph — heavy arena + reapply-queue + sibling-helper traffic.
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::incrementalMergeWithPreviousNondeterministicCompletionGraph`
    /// (cpp 3102–3242).
    ///
    /// C++ (every branch preserved): fetches `indiNodeVec` from the databox and the
    /// previous deterministic / nondeterministic completion-graph tasks via
    /// `mIncExpHandler`. Only when both exist and differ: allocates a
    /// `transformNodeSet`, references a fresh merged node vector onto `indiNodeVec`
    /// and installs it on the databox, then for each index `i in [indiStart,indiCount)`
    ///   * `!indiNode && prevNondet`        → `mergedVec->setLocalData(i, prevNondet)`
    ///   * `indiNode == prevDet`            → if `prevNondet != prevDet` `setLocalData(i, prevNondet)`
    ///   * else (and not `PRFPURGEDBLOCKED`) if `PRFCOMPLETIONGRAPHCACHED` and not
    ///     `PRFCOMPLETIONGRAPHCACHINGINVALID|INVALIDATED` → `transformNodeSet->insert(i)`.
    /// Then for each `transformNodeID`: localize the node, copy the previous
    /// nondeterministic node's `ReapplyConceptLabelSet`; replay its successor links
    /// (skip `PRFPURGEDBLOCKED`, dedup via `hasRoleSuccessorToIndividual`, init a new
    /// `CIndividualLinkEdge`, `installIndividualNodeRoleLinkReapplied` +
    /// `applyReapplyQueueConceptsRestricted`); its connection-successor set, distinct
    /// hash (new `CDistinctEdge`), and individual-merging hash (replay reapply queue,
    /// copy merged-with + dependency-track-point). Returns `true` on the merge path,
    /// else `false`.
    pub fn incremental_merge_with_previous_nondeterministic_completion_graph(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let _ = calc_alg_context;
        // PORT-PENDING: see structural transcription above. Needs mIncExpHandler
        // (getPrevious{Det,Nondet}CompletionGraphTask), the Task-side databox/node
        // vectors, the node arena successor/connection/distinct/merging iterators, and
        // the reapply-queue helpers (installIndividualNodeRoleLinkReapplied /
        // applyReapplyQueueConcepts[Restricted]) + getLocalizedIndividual /
        // getUpToDateIndividual — none ported.
        todo!(
            "W3-DEFER: incrementalMergeWithPreviousNondeterministicCompletionGraph — \
             mIncExpHandler + Task databoxes + reapply-queue/localize helpers unported"
        );
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::incrementalMergeWithPreviousDeterministicCompletionGraph`
    /// (cpp 3250–3372).
    ///
    /// C++ (every branch preserved): fetches `indiNodeVec` and the previous
    /// deterministic task via `mIncExpHandler`. When present: allocates the four
    /// nominal-classification sets and calls
    /// `identifyCompatibilityChangedNominalIndividualNodes(nonCompatibleChanged,
    /// compatible, redundant, new)`; allocates a `pruningNodeSet`; references a merged
    /// node vector onto the previous vector and installs it. Then
    ///   * for each redundant nominal node → localize + `pruneIncrementalRemovedSuccessors`,
    ///   * for each non-compatible-changed node → localize + `pruneIncrementalRemovedSuccessors`,
    ///     then `mergedVec->setData(id, changedNode)` from the new vector,
    ///   * for each compatible nominal node → `setData(id, newCompNode)`, and when a
    ///     previous compatible node exists: localize, replay its nominal-connected
    ///     successor links (skip those already in the compatible/changed/pruning sets,
    ///     init new `CIndividualLinkEdge`, install + `applyReapplyQueueConceptsRestricted`),
    ///     copy its connection successors (same skip set), and enqueue the localized
    ///     node on the late or early reactivation queue per
    ///     `mConfDelayCompletionGraphCachingReactivation`.
    /// Finally copies any new-index nodes below `prevMin` and above `prevMax` into the
    /// merged vector. Returns `true` on the merge path, else `false`.
    pub fn incremental_merge_with_previous_deterministic_completion_graph(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let _ = calc_alg_context;
        // PORT-PENDING: see structural transcription above. Needs mIncExpHandler, the
        // Task-side databox/node vectors, identifyCompatibilityChangedNominalIndividualNodes
        // + pruneIncrementalRemovedSuccessors (nominal-handling units), the
        // reactivation-queue getters, and getLocalizedIndividual / the
        // reapply-queue helpers — none ported.
        todo!(
            "W3-DEFER: incrementalMergeWithPreviousDeterministicCompletionGraph — \
             mIncExpHandler + nominal compatibility/prune helpers + reactivation queues unported"
        );
    }

    // =======================================================================
    // MERGE* dependency-node factory wrappers (cpp 10057–10225).
    //
    // Each is the uniform guard `depNode = nullptr; if (mConfBuildDependencies)
    // depNode = calcAlgContext->getUsedDependencyFactory()->create…(); return
    // depNode;`. `createMERGEDCONCEPTDependency` is live; the remaining wrappers
    // still preserve the guard while their factory bodies are filled incrementally.
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::createMERGEDCONCEPTDependency`.
    pub fn create_merged_concept_dependency(
        &mut self,
        merged_concept_continue_dep_track_point: &mut TrackPointId,
        process_indi: &mut NodeId,
        con_des: ConDescId,
        merge_prev_dep_track_point: TrackPointId,
        concept_prev_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node: DependencyId = Id::NONE;
        if self.conf_build_dependencies {
            dep_node = calc_alg_context
                .process_context_mut()
                .alloc_det_link_dependency_node(DepKind::MergedConcept);
            {
                let process_context = calc_alg_context.process_context_mut();
                let dep = process_context.dep_node_mut(dep_node);
                dep.init_dependency_node(DepKind::MergedConcept, con_des);
                dep.base_mut().dep_track_point = concept_prev_dep_track_point;
            }
            // bind + CHAIN the merge back-edge (CMERGEDCONCEPTDependencyNode's
            // constructor `addAfterDependency(&mPrevLinkDep)` — chain membership
            // is what lets the branching-tag update and the u29 traversal see
            // the merge decision's taint).
            calc_alg_context
                .process_context_mut()
                .bind_det_link_prev(dep_node, merge_prev_dep_track_point);
            calc_alg_context
                .process_context_mut()
                .update_dependency_branching_tag(dep_node);
            *merged_concept_continue_dep_track_point = calc_alg_context
                .process_context_mut()
                .materialize_continue_dependency_track_point(dep_node);
            let _ = process_indi;
        }
        dep_node
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::createMERGEDLINKDependency`.
    pub fn create_merged_link_dependency(
        &mut self,
        merged_link_continue_dep_track_point: &mut TrackPointId,
        process_indi: &mut NodeId,
        merge_prev_dep_track_point: TrackPointId,
        link_prev_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node: DependencyId = Id::NONE;
        if self.conf_build_dependencies {
            dep_node = calc_alg_context
                .process_context_mut()
                .create_merged_link_dependency_node(
                    merged_link_continue_dep_track_point,
                    merge_prev_dep_track_point,
                    link_prev_dep_track_point,
                );
            let _ = process_indi;
        }
        dep_node
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::createMERGEDINDIVIDUALDependency`.
    ///
    /// KONCLUDE-PORT-NOTE[overload]: the C++ overload takes the narrower
    /// `CCalculationAlgorithmContext*`; threaded as `&mut CalculationAlgorithmContextBase`
    /// for uniformity (the `mUsedDepFactory` it reads lives on the folded-in base).
    pub fn create_merged_individual_dependency(
        &mut self,
        merged_individual_continue_dep_track_point: &mut TrackPointId,
        process_indi: &mut NodeId,
        merge_prev_dep_track_point: TrackPointId,
        individual_prev_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node: DependencyId = Id::NONE;
        if self.conf_build_dependencies {
            dep_node = calc_alg_context
                .process_context_mut()
                .create_merged_individual_dependency_node(
                    merged_individual_continue_dep_track_point,
                    merge_prev_dep_track_point,
                    individual_prev_dep_track_point,
                );
            let _ = process_indi;
        }
        dep_node
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::createMERGEDependency`.
    pub fn create_merge_dependency(
        &mut self,
        process_indi: &mut NodeId,
        con_des: ConDescId,
        prev_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node: DependencyId = Id::NONE;
        if self.conf_build_dependencies {
            let branch_node = calc_alg_context.base.used_branch_tree_node();
            dep_node = calc_alg_context
                .process_context_mut()
                .create_merge_dependency_node(branch_node, con_des, prev_dep_track_point);
            let _ = process_indi;
        }
        dep_node
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::createMERGEPOSSIBLEINSTANCEINDIVIDUALDependencyNode`.
    pub fn create_merge_possible_instance_individual_dependency_node(
        &mut self,
        process_indi: &mut NodeId,
        prev_dep_track_point: TrackPointId,
        merging_indi: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node: DependencyId = Id::NONE;
        if self.conf_build_dependencies {
            let branch_node = calc_alg_context.base.used_branch_tree_node();
            dep_node = calc_alg_context
                .process_context_mut()
                .create_merge_possible_instance_individual_dependency_node(
                    branch_node,
                    *process_indi,
                    prev_dep_track_point,
                );
            // Konclude passes `mergingIndi` through this wrapper, but the concrete
            // dependency-node init ignores it.
            let _ = merging_indi;
        }
        dep_node
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::createSAMEINDIVIDUALMERGEDependency`.
    pub fn create_same_individual_merge_dependency(
        &mut self,
        exp_continue_dep_track_point: &mut TrackPointId,
        process_indi: &mut NodeId,
        prev_dep_track_point: TrackPointId,
        prev_other_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node: DependencyId = Id::NONE;
        if self.conf_build_dependencies {
            dep_node = calc_alg_context
                .process_context_mut()
                .create_same_individual_merge_dependency_node(
                    exp_continue_dep_track_point,
                    prev_dep_track_point,
                    prev_other_dep_track_point,
                );
            let _ = process_indi;
        }
        dep_node
    }

    // =======================================================================
    // Debug merging-queue string + pairwise merge (cpp 15009–15093).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::generateDebugMergingQueueString`.
    ///
    /// C++ (every branch preserved): walks `branchingMergingProcRest->getMergingCandidateNodeLinker()`;
    /// for each candidate node builds `"[ <indiID> ] = "` and, over its
    /// `ReapplyConceptLabelSet` iterator, appends `"<-? sign><conTag><className?>"`
    /// for every descriptor whose `getConceptTag() != 1`; wraps the operands in
    /// `"{…} \n"` and concatenates. Returns the accumulated string.
    pub fn generate_debug_merging_queue_string(
        &mut self,
        branching_merging_proc_rest: RestrictionSpecId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> String {
        let _ = (branching_merging_proc_rest, calc_alg_context);
        // PORT-PENDING: debug-only. Needs the BranchingMergingProcessingRestrictionSpecification
        // merging-candidate linker chain, the CReapplyConceptLabelSetIterator, and
        // CIRIName::getRecentIRIName (concept class-name resolution) — not ported.
        String::new()
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::mergeMergingIndividualNodesPairwise`
    /// (cpp 15044–15093).
    ///
    /// C++ control flow (every branch preserved):
    /// ```text
    /// conDes = conProDes->getConceptDescriptor(); concept = conDes->getConcept()
    /// role = concept->getRole(); conceptOpLinkerIt = concept->getOperandList()
    /// baseDepTrackPoint = branchingMergingProcRest->getDependencyTrackPoint()
    /// indiCount = processIndi->getRoleSuccessorCount(role)
    /// if (indiCount > cardinality):
    ///   newTaskList = nullptr
    ///   mergeDependencyNode = createMERGEDependency(processIndi, nullptr, baseDepTrackPoint)   // sibling, this unit
    ///   clashDescriptors = nullptr
    ///   for (roleSuccIt1 over processIndi->getRoleSuccessorLinkIterator(role)):
    ///     link1 = roleSuccIt1.next(); succNode1 = getSuccessorIndividual(processIndi, link1)
    ///     clashDescriptors = createIndividualMergeCausingDescriptors(clashDescriptors, succNode1, link1, conceptOpLinkerIt)
    ///     for (roleSuccIt2 = roleSuccIt1; roleSuccIt2.hasNext():):
    ///       link2 = roleSuccIt2.next(); succNode2 = getSuccessorIndividual(processIndi, link2)
    ///       clashDescriptors = createIndividualMergeCausingDescriptors(clashDescriptors, succNode2, link2, conceptOpLinkerIt)
    ///       if (isIndividualNodesMergeable(succNode1, succNode2, clashDescriptors)):
    ///         newTask = createMergeBranchingTask(processIndi, conProDes, succNode1, succNode2, mergeDependencyNode, branchingMergingProcRest)
    ///         newTaskList = newTask->append(newTaskList)
    ///   if (mergeDependencyNode) mergeDependencyNode->addBranchClashes(clashDescriptors)
    ///   if (newTaskList):
    ///     processorContext->getTaskProcessorCommunicator()->communicateTaskCreation(newTaskList)
    ///   else:
    ///     clashDescriptors = createClashedConceptDescriptor(clashDescriptors, processIndi, nullptr, baseDepTrackPoint)
    ///     throw CCalculationClashProcessingException(clashDescriptors)
    ///   throw CCalculationStopProcessingException(true)
    /// return false
    /// ```
    pub fn merge_merging_individual_nodes_pairwise(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        link_count: Cint64,
        cardinality: Cint64,
        branching_merging_proc_rest: RestrictionSpecId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let _ = (
            process_indi,
            con_pro_des,
            link_count,
            cardinality,
            branching_merging_proc_rest,
            calc_alg_context,
        );
        // PORT-PENDING: see structural transcription above. NOW AVAILABLE: getSuccessorIndividual
        // (u36) and the two terminal throws — `throw CCalculationClashProcessingException(clashDescriptors)`
        // → `calc_alg_context.raise_clash(clashDescriptors); return false;` and
        // `throw CCalculationStopProcessingException(true)` → `calc_alg_context.raise_stop(true); return false;`
        // (completion/clash.rs). The body STILL bottoms out in the unit-14 helpers
        // (createIndividualMergeCausingDescriptors / isIndividualNodesMergeable), the unit-13
        // createMergeBranchingTask, the role-successor link iterators (getRoleSuccessorLinkIterator /
        // getRoleSuccessorCount), createClashedConceptDescriptor (clash-processing unit), and the
        // Task communicator (communicateTaskCreation) — none ported. The in-unit
        // create_merge_dependency wrapper used for mergeDependencyNode is live.
        todo!(
            "W3-DEFER: mergeMergingIndividualNodesPairwise — unit-13/14 merge helpers + \
             role-successor iterators + createClashedConceptDescriptor + Task communicator unported \
             (getSuccessorIndividual + raise_clash/raise_stop now available)"
        );
    }
}
