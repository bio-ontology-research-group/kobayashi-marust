//! `completion::u24` — Caching / backend-cache / saturation family, batch
//! (port unit #24 of 36).
//!
//! Faithful port of the 8 methods that the manifest (`01-completion-methods.md`,
//! "Unit 24") groups under the representative-memory backend-cache neighbour
//! expansion of Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`.
//! cpp source line ranges (1-based) per method are noted on each item.
//!
//! Methods (cpp order):
//!   * `expandDirectlyInfluencedIndividualNeighbourNodesFromBackendCache` [23995–24438]
//!   * `queuedIndividualBackendNeighbourExpansion`                        [24443–24632]
//!   * `markIndividualNodeBackendNonConceptSetRelatedAndNeighbourLabelRelatedProcessing` [24706–24711]
//!   * `markIndividualNodeBackendNonConceptSetRelatedAndNeighbourLabelRelatedProcessingForDisjointRoles` [24715–24725]
//!   * `markIndividualNodeBackendNonConceptSetRelatedProcessingForDisjointRoles`          [24727–24734]
//!   * `markIndividualNodeBackendNonConceptSetNeighbourLabelRelatedProcessingForDisjointRoles` [24736–24743]
//!   * `markIndividualNodeBackendNonConceptSetNeighbourLabelRelatedProcessing`            [24745–24797]
//!   * `prepareBackendExpansionReuseBranching`                            [24803–24881]
//!
//! KONCLUDE-PORT-NOTE[ownership]: each method is a member of
//! `CCalculationTableauCompletionTaskHandleAlgorithm`, so it becomes `&mut self`
//! plus the threaded per-thread context `calc_alg_context: &mut
//! CalculationAlgorithmContextBase`. C++ `CIndividualProcessNode*&` out/in-out
//! pointer-references become `&mut NodeId`; a plain `CIndividualProcessNode*`
//! value parameter becomes `NodeId`; a `CRole*` value parameter becomes `RoleId`
//! resolved against `calc_alg_context.ontology_arenas()`. The per-test arenas are
//! reached through the context as `calc_alg_context.process_context()` / `_mut()`,
//! the databox as `calc_alg_context.processing_data_box{,_mut}()`.
//!
//! Deferral landscape. This unit is the most deeply backend-cache-dependent of the
//! W3 batches: SEVEN of the eight methods bottom out in the
//! representative-memory backend cache subsystem that is NOT yet ported (the W6
//! Cache subtree), namely
//!   * `CIndividualNodeRepresentativeMemoryBackendCacheSynchronisationData` and its
//!     localized twin (per-node sync data: merged-node linkers, the
//!     deterministic/non-deterministic same/different-individual handling flags,
//!     the neighbour-expansion data hashes, the label representative-expansion
//!     linkers) — `process::stubs::BackendSyncDataId` is a zero-size marker today;
//!   * `CBackendRepresentativeMemoryCacheIndividualAssociationData` + the
//!     `CBackendRepresentativeMemoryLabelCacheItem` family + the role-set neighbour
//!     arrays — reached only through `mBackendCacheHandler`
//!     (`self.backend_cache_handler`, a zero-size `Id` stub);
//!   * `CBackendNeighbourExpansionQueue` / `CBackendNeighbourExpansionQueueDataLinker`
//!     / `CBackendNeighbourExpansionControllingData` — the per-node expansion
//!     work queues (process-layer `stub!` markers, no arena yet);
//!   * the satisfiable-task representative-backend-cache UPDATING adapter and the
//!     task-creation / dependency-track-point machinery used by the reuse
//!     branching (`createDependendBranchingTaskList`,
//!     `createNonDeterministicDependencyTrackPointBranch`, the
//!     `CCalculationStopProcessingException` / `CCalculationClashProcessingException`
//!     control-flow throws — all later units / W6).
//!
//! Following the porting convention, the four genuinely substrate-portable methods
//! are ported in full:
//!   * `markIndividualNodeBackendNonConceptSetRelatedAndNeighbourLabelRelatedProcessing`
//!     (the `marked |=` fan-out over two sibling mark helpers),
//!   * the three `*ForDisjointRoles` guards (the `getIndirectSuperRoleList()` scan
//!     for a super-role with `hasDisjointRoles()`, then the sibling mark call).
//! The remaining four bodies are driven start-to-finish by the deferred
//! backend-cache subsystem; they are kept `// PORT-PENDING` with the faithful
//! signature and a structural transcription of the C++ so a later wave fills them
//! without re-reading the source. Logic is documented, never silently dropped.

#![allow(dead_code)]
#![allow(unused_variables)]

use super::super::model::substrate::{Cint64, Id};
use super::super::model::RoleId;
use super::super::process::NodeId;
use super::context::CalculationAlgorithmContextBase;

impl super::algorithm::CompletionTaskHandleAlgorithm {
    // =======================================================================
    // Directly-influenced neighbour expansion from the backend cache
    // (cpp 23995–24438).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::expandDirectlyInfluencedIndividualNeighbourNodesFromBackendCache`.
    /// cpp 23995–24438.
    ///
    /// The directly-influenced neighbour-expansion driver for a (nominal) node:
    /// after testing for newly arrived backend mergings it (a) merges all
    /// deterministic same-individuals, (b) inferring- or all-neighbour-expands the
    /// newly merged representative nodes, (c) differentiates deterministic
    /// different-individuals (distinct links / clash), (d) establishes prioritised
    /// propagation-cut links, (e) expands directly-influenced neighbours with
    /// propagation for every newly added concept descriptor, and finally expands
    /// the indirectly-connected individuals.
    ///
    /// Returns `lazyNeighboursExpansionSucceded` (false if the node carries purged
    /// blocked processing-restriction flags).
    pub fn expand_directly_influenced_individual_neighbour_nodes_from_backend_cache(
        &mut self,
        indi_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // The one substrate-portable guard at the head of the method:
        //   bool lazyNeighboursExpansionSucceded = true;
        //   if (indiNode->hasPurgedBlockedProcessingRestrictionFlags()) return false;
        // KONCLUDE-PORT-NOTE[api]: `hasPurgedBlockedProcessingRestrictionFlags()` is
        // a `CIndividualProcessNode` processing-restriction-flag predicate. It is
        // part of the node, but the surrounding body cannot proceed without the
        // backend-cache subsystem, so the whole method is held PORT-PENDING (rather
        // than porting only the guard and stubbing the 440-line remainder).
        //
        // PORT-PENDING: faithful transcription of cpp 23995–24438. Outline:
        //
        //   lazyNeighboursExpansionSucceded = true;
        //   if indiNode->hasPurgedBlockedProcessingRestrictionFlags(): return false;
        //
        //   backendSyncData    = indiNode->getIndividualBackendCacheSynchronisationData(false);
        //   locBackendSyncData = indiNode->getIndividualBackendCacheSynchronisationData(true);
        //
        //   testIndividualNodeBackendCacheNewMergings(indiNode, ctx);            // merge unit
        //   backendSyncData = indiNode->getIndividualBackendCacheSynchronisationData(false);
        //
        //   // (1) merge all deterministic same-individuals of every newly merged node:
        //   visitNewlyMergedIndividualsBackendSynchronisationData(indiNode, mergedLinker,
        //       lastDirectExpansionHandledMergedLinker, !hasDeterministicSameIndividualMerged,
        //       |base, locNode, depTP| {
        //         assocData = locSyncData->getAssocitaionData();
        //         if !hasDeterministicSameIndividualMerged && assocData:
        //           locNode = getLocalizedIndividual(locNode, true, ctx);
        //           detSameIndiLabel = assocData->getLabelCacheEntry(DETERMINISTIC_SAME_INDIVIDUAL_SET_LABEL);
        //           if detSameIndiLabel:
        //             mergingIntoId = min(assocData->getRepresentativeSameIndividualId(),
        //                                 getCorrectedMergedIntoIndividualNode(indiNode,ctx)->...getIndividualID());
        //             mBackendCacheHandler->visitIndividualIdsOfAssociatedIndividualSetLabel(
        //                 assocData, detSameIndiLabel, |sameIndiId| {
        //                   if sameIndiId != mergingIntoId:
        //                     locMergingIntoIndiNode = getLocalizedForcedBackendInitializedNominalIndividualNode(mergingIntoId, ctx);
        //                     if not already merged:
        //                       locMergingSameIndiNode = getLocalizedForcedBackendInitializedNominalIndividualNode(sameIndiId, ctx);
        //                       if isIndividualNodesMergeable(into, same, clashDes, ctx):     // merge unit
        //                         create SAMEINDIVIDUALMERGE dependency; getMergedIndividualNodes(into, same, depTP, ctx);
        //                       else:
        //                         build clashDescriptors and throw CCalculationClashProcessingException;  // [exceptions]
        //                   true }, ctx);
        //             locSyncData->setDeterministicSameIndividualMerged(true);
        //         true }, ctx);
        //
        //   if indiNode->hasPurgedBlockedProcessingRestrictionFlags():
        //     locBackendSyncData = getLocalizedIndividualBackendCacheSnychronisationData(indiNode, ctx);  // u17
        //     locBackendSyncData->setLastDirectExpansionHandledMergedNodeLinker(backendSyncData->getMergedIndividualNodeLinker());
        //     return false;
        //
        //   // (2) inferring- vs all-neighbour expansion of newly merged representatives:
        //   newMergingsHandled = false; nonDeterministicMerged = backendSyncData->hasNonDeterministicallyMergedIndividuals();
        //   if mConfAllowBackendNeighbourExpansionBlocking && mConfNewMergingsOnlyInferringExpansion && !nonDeterministicMerged:
        //     checkingMergingsLinker = backendSyncData->getLastInferringExpansionHandledMergedNodeLinker(); newMergingsHandled = true;
        //     if mergedLinker != lastInferringExpansionHandledLinker:
        //       markIndividualNodeBackendNonConceptSetRelatedAndNeighbourLabelRelatedProcessing(indiNode, ctx);   // this unit
        //       visitNewlyMergedOnlyDeterministicRepresentativeIndividualsBackendSynchronisationData(..., |..| {
        //           mergedNode = getLocalizedIndividual(mergedNode, false, ctx);
        //           expandIndividualInferringNeighboursFromBackendCache(indiNode, mergedNode, true, depTP, ctx);   // u23
        //           true }, ctx);
        //       locSyncData->setNewlyMergedInferringNeighbourExpansion(true); setNewlyMergedIndividuals(true);
        //   if !newMergingsHandled && (!mConfAllowBackendNeighbourExpansionBlocking
        //                              || mergedLinker != lastDirectExpansionHandledLinker):
        //     checkingMergingsLinker = backendSyncData->getLastDirectExpansionHandledMergedNodeLinker(); newMergingsHandled = true;
        //     markIndividualNodeBackendNonConceptSetRelatedAndNeighbourLabelRelatedProcessing(indiNode, ctx);   // this unit
        //     visitNewlyMergedOnlyDeterministicRepresentativeIndividualsBackendSynchronisationData(..., |..| {
        //         mergedNode = getLocalizedIndividual(mergedNode, false, ctx);
        //         expandIndividualAllNeighboursFromBackendCache(indiNode, mergedNode, true, false, depTP, ctx);   // u23
        //         true }, ctx);
        //     locSyncData->setNewlyMergedAllNeighbourExpansion(true); setMergedIndividualsAllNeighbourExpanded(true);
        //     setAllNeighbourExpansionScheduled(true); setAllNeighbourForcedExpansionScheduled(true); setNewlyMergedIndividuals(true);
        //
        //   // (3) differentiate deterministic different-individuals (distinct links / clash):
        //   visitNewlyMergedOnlyDeterministicRepresentativeIndividualsBackendSynchronisationData(indiNode, mergedLinker,
        //       checkingMergingsLinker, !hasDeterministicDifferentIndividualDifferentiated, |base, locNode, depTP| {
        //         assocData = locSyncData->getAssocitaionData();
        //         if !hasDeterministicDifferentIndividualDifferentiated && assocData:
        //           detDiffIndiLabel = assocData->getLabelCacheEntry(DETERMINISTIC_DIFFRENT_INDIVIDUAL_SET_LABEL);
        //           detSameIndiLabel = assocData->getLabelCacheEntry(DETERMINISTIC_SAME_INDIVIDUAL_SET_LABEL);
        //           if detDiffIndiLabel:
        //             mBackendCacheHandler->visitIndividualIdsOfAssociatedIndividualSetLabel(assocData, detDiffIndiLabel, |diffIndiId| {
        //               if diffIndiId != locId && !inSameLabel:
        //                 if indiNode merged-with diffIndiId: build clashDescriptors, throw CCalculationClashProcessingException;  // [exceptions]
        //                 else: locDiff = getLocalizedForcedBackendInitializedNominalIndividualNode(diffIndiId, ctx);
        //                       createIndividualsDistinct(indiNode, locDiff, depTP, ctx);
        //               true }, ctx);
        //           locSyncData->setDeterministicDifferentIndividualDifferentiated(true);
        //         true }, ctx);
        //
        //   // (4) establish prioritised propagation-cut links:
        //   visitNewlyMergedOnlyDeterministicRepresentativeIndividualsBackendSynchronisationData(indiNode, mergedLinker,
        //       checkingMergingsLinker, !hasPrioritziedPropagationLinksEstablished, |base, locNode, depTP| {
        //         assocData = locSyncData->getAssocitaionData();
        //         if !hasPrioritziedPropagationLinksEstablished && assocData:
        //           neighRoleSetCompIndiLabel = assocData->getLabelCacheEntry(NEIGHBOUR_INSTANTIATED_ROLE_SET_COMBINATION_LABEL);
        //           if neighRoleSetCompIndiLabel:
        //             topRole = ctx->getProcessingDataBox()->getOntology()->getRBox()->getTopObjectRole();
        //             mBackendCacheHandler->visitNeighbourArrayIdsForRole(assocData, topRole, |arrayId, label, nondet| {
        //               if nondet && label->getCacheValueCount() == 1:
        //                 initializeNeighbourExpansionWithPropagation(indiNode, locNode, locSyncData, depTP, arrayId,
        //                     nullptr, false, true, nullptr, true, true, false, ctx);                                 // u27
        //               true }, false, ctx);
        //           locSyncData->setPrioritziedPropagationLinksEstablished(true);
        //         true }, ctx);
        //
        //   // (5) directly-influenced neighbour expansion per newly added concept descriptor:
        //   if !backendSyncData->hasAllNeighbourExpansionScheduled():
        //     visitNewlyMergedOnlyDeterministicRepresentativeIndividualsBackendSynchronisationData(..., true, |base, locNode, depTP| {
        //         locSyncData = getLocalizedIndividualBackendCacheSnychronisationData(locNode, ctx);                   // u17
        //         if backendSyncData && mBackendCacheHandler && locSyncData->getAssocitaionData():
        //           cardBlockCrit = testIndividualNodeBackendCacheExpansionBlockingCriticalCardinality(indiNode, ctx);  // u19/u20
        //           if cardBlockCrit || testIndividualNodeBackendCacheNeighbourExpansionBlockingCritical(indiNode, ctx):
        //             lastTestedConDes        = locSyncData->getLastNeighbourInfluenceTestedConceptDescriptor();
        //             lastNeighbourCriticalConDes = locSyncData->getLastCriticalNeighbourExpansionTestedConceptDescriptor();
        //             if cardBlockCrit && !locSyncData->hasNeighbourInfluenceTestingCriticalCardinalityReset(): reset both to null;
        //             if indiNode->getIndividualNodeID() != locNode->getIndividualNodeID()
        //                && indiNode->getIndividualNodeID() != locSyncData->getLastMergedIntoIndividualTestingCriticalCardinalityReset():
        //                 reset both to null;
        //             conSet = indiNode->getReapplyConceptLabelSet(false);
        //             if conSet:
        //               conDesLinker = conSet->getAddingSortedConceptDescriptionLinker();
        //               if conDesLinker != lastTestedConDes:
        //                 for conDesIt = conDesLinker; conDesIt && conDesIt != lastTestedConDes
        //                                 && conDesIt != lastNeighbourCriticalConDes; conDesIt = conDesIt->getNext():
        //                   concept = conDesIt->getConcept(); conNegation = conDesIt->getNegation();
        //                   nondeterministic = hasNondeterministicDependency(conDesIt->getDependencyTrackPoint(), ctx)
        //                                      || hasNondeterministicDependency(backSyncDepTrackPoint, ctx);          // dep unit
        //                   expandDirectlyInfluencedNeighboursWithPropagation(concept, conNegation, nondeterministic,
        //                       baseIndiNode, assocData, locNode, locSyncData, depTP, ctx);                           // u22
        //                 locSyncData->setLastNeighbourInfluenceTestedConceptDescriptor(conDesLinker);
        //                 locSyncData->hasNeighbourInfluenceTestingCriticalCardinalityReset(cardBlockCrit);
        //                 locSyncData->setLastMergedIntoIndividualTestingCriticalCardinalityReset(indiNode->getIndividualNodeID());
        //         true }, ctx);
        //
        //   // (6) advance the handled-merged-node cursor:
        //   if backendSyncData->getMergedIndividualNodeLinker() != checkingMergingsLinker:
        //     locBackendSyncData = getLocalizedIndividualBackendCacheSnychronisationData(indiNode, ctx);              // u17
        //     if lastDirectExpansionHandledLinker == checkingMergingsLinker:
        //          locBackendSyncData->setLastDirectExpansionHandledMergedNodeLinker(mergedLinker);
        //     else: locBackendSyncData->setLastInferringExpansionHandledMergedNodeLinker(mergedLinker);
        //
        //   expandIndirectlyConnectedIndividuals(indiNode, true, ctx);                                                // u23/u26
        //   return lazyNeighboursExpansionSucceded;
        //
        // Held PORT-PENDING: every typed local is a not-yet-ported backend-cache
        // class (sync data, association data, label cache items, merged-node
        // linkers) and the visitors are the merge-unit
        // `visitNewlyMerged*BackendSynchronisationData` helpers; the concept-set scan
        // and the two `markIndividualNodeBackendNonConceptSetRelatedAndNeighbourLabelRelatedProcessing`
        // calls (ported in THIS unit) become live on the reconcile pass.
        let _ = (indi_node, calc_alg_context);
        true
    }

    // =======================================================================
    // Queued backend neighbour expansion (cpp 24443–24632).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::queuedIndividualBackendNeighbourExpansion`.
    /// cpp 24443–24632.
    ///
    /// Drains (a batch of) the node's `CBackendNeighbourExpansionQueue`: for each
    /// queued role-neighbour-array expansion it visits the neighbour individual ids
    /// from a cursor, expands the directly/representatively influenced ones (with
    /// label-representative delaying), honours the total/batch expansion limits
    /// (recording a propagation cut + re-queueing the remainder when a limit is
    /// hit), and re-schedules the node onto the (late) backend neighbour-expansion
    /// queue when work remains.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: `CBackendNeighbourExpansionControllingData*
    /// expContData` is a process-layer `stub!` marker with no arena yet → opaque
    /// `Cint64`. Returns the expanded `CIndividualProcessNode*` (or `Id::NONE`).
    pub fn queued_individual_backend_neighbour_expansion(
        &mut self,
        base_indi_node: &mut NodeId,
        exp_cont_data: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        // PORT-PENDING: faithful transcription of cpp 24443–24632. Outline:
        //
        //   indiProcNode = nullptr;
        //   baseIndiNode = getLocalizedIndividual(baseIndiNode, true, ctx);
        //   mergedIntoBaseIndiNode = getLocalizedIndividual(getCorrectedMergedIntoIndividualNode(baseIndiNode, ctx), true, ctx);
        //   locBackendSyncData = getLocalizedIndividualBackendCacheSnychronisationData(baseIndiNode, ctx);  // u17
        //   indiNeighbourExpansionQueue = locBackendSyncData->getBackendNeighbourExpansionQueue(true);
        //
        //   diffNeighExpCount = 0; propagationCut = false;
        //   while !propagationCut && indiNeighbourExpansionQueue->hasQueuedNeighbourExpansions()
        //         && (diffNeighExpCount++ <= mOptQueuedBackendNeighbourExpansionRolesBatchCount
        //             || mOptQueuedBackendNeighbourExpansionRolesBatchCount < 0):
        //
        //     backendNeighbourExpDataLinker = indiNeighbourExpansionQueue->takeNextNeighbourExpansionQueueDataLinker();
        //     newLinker = allocate CBackendNeighbourExpansionQueueDataLinker; newLinker->initQueueData(backendNeighbourExpDataLinker);
        //     backendSyncDataIndiNode = newLinker->getBackendSyncDataIndividualNode();
        //     locHandlingBackendSyncData = locBackendSyncData;
        //     if backendSyncDataIndiNode != baseIndiNode:
        //         backendSyncDataIndiNode = getLocalizedIndividual(backendSyncDataIndiNode, true, ctx);
        //         locHandlingBackendSyncData = getLocalizedIndividualBackendCacheSnychronisationData(backendSyncDataIndiNode, ctx);
        //     assocData = locHandlingBackendSyncData->getAssocitaionData();
        //     backSyncDepTrackPoint = ctx->getBaseDependencyNode()->getContinueDependencyTrackPoint();
        //     if backendSyncDataIndiNode != mergedIntoBaseIndiNode:
        //         backSyncDepTrackPoint = mergedIntoBaseIndiNode->getIndividualMergingHash(true)
        //                                   ->value(-backendSyncDataIndiNode->getIndividualNodeID()).getDependencyTrackPoint();
        //
        //     expansionCount=0; newCursor=0; lastCursor=0; newLastExpandedNeighbourId=-1;
        //     currentNeighbourExpansionCount=0; maxDirectNeighbourExpansionReached=false;
        //     deterministicFoundSkippedNeighbourNodeCount=0; oneExpanded=false; finished=true; forceReadding=false;
        //
        //     if mOptNeighbourLabelRepresentativeExpansionDelaying:
        //         labelNeighbourExpDelayDataHash = locBackendSyncData->getNeighbourLabelExpansionDataHash(newLinker->getNeighbourArrayId(), true);
        //     neighbourExpansionDataHash = locBackendSyncData->getNeighbourExpansionDataHash(true);
        //
        //     mBackendCacheHandler->visitNeighbourIndividualIdsForNeighbourArrayIdFromCursor(assocData,
        //         newLinker->getNeighbourArrayId(), |neighbourIndiId, neighbourRoleSetLabel, nondeterministic, nextCursor| {
        //           expanded = false;
        //           if canExpansionPotentiallyInfluenceNeighbourWithPotentialPropagation(mergedIntoBaseIndiNode,
        //                 newLinker->getConcept(), newLinker->getConceptNegation(), newLinker->getConceptNondeterministic(),
        //                 assocData, neighbourIndiId, ctx):                                                    // u22
        //             neighbourExpansionData = neighbourExpansionDataHash[neighbourIndiId];
        //             if !neighbourExpansionData.isNeighbourPossiblyInfluenced():
        //               neighbourAssData = mBackendCacheHandler->getIndividualAssociationData(neighbourIndiId, ctx);
        //               if integrated-node-count >= mOptMaxBackendNeighbourTotalExpansionCount > 0
        //                  && (!neighbourAssData || !neighbourAssData->hasProblematicLevel()): maxDirectNeighbourExpansionReached = true;
        //               if !maxDirectNeighbourExpansionReached:
        //                 newLastExpandedNeighbourId = neighbourIndiId; newCursor = nextCursor;
        //                 representativeExpansion = mOptNeighbourLabelRepresentativeExpansionDelaying;
        //                 delaying = false; expandable = true; forceExpansion = newLinker->isForceExpansion();
        //                 if newLinker->getConcept():
        //                   expandable = canExpandDirectlyInfluencedNeighbourWithPropagation(mergedIntoBaseIndiNode,
        //                       locHandlingBackendSyncData, backSyncDepTrackPoint, concept, neg, nondet, assocData,
        //                       neighbourExpansionData, neighbourIndiId, neighbourAssData, ctx);                // u22
        //                   forceExpansion = true;
        //                 if newLinker->isMissingNondeterministicExpansionPropagation():
        //                   expandable = false;
        //                   neighbourConSetLabel = neighbourAssData->getLabelCacheEntry(FULL_CONCEPT_SET_LABEL);
        //                   cardExtData = neighbourConSetLabel->getExtensionData(CARDINALITY_HASH);
        //                   if cardExtData || neighbourConSetLabel->hasNondeterministicElements(): expandable = true;
        //                 if expandable:
        //                   canDelayRepresentativeNeighbourExpansion(baseIndiNode, newLinker, labelNeighbourExpDelayDataHash,
        //                       newLinker->getExpandingLabel(), neighbourAssData, newLinker->getNeighbourArrayId(),
        //                       lastCursor, neighbourIndiId, delayingLabelNeighbourExpansionData, delaying,
        //                       representativeExpansion, ctx);                                                  // u25 (sibling)
        //                   if !delaying:
        //                     representativeLabelNeighbourExpansionData = representativeExpansion ? delayingLabelNeighbourExpansionData : nullptr;
        //                     if mergedIntoBaseIndiNode != baseIndiNode && (!backSyncDepTrackPoint
        //                          || hasNondeterministicDependency(backSyncDepTrackPoint, ctx)):
        //                       expanded |= ensureBaseLinkExpansion(mergedIntoBaseIndiNode, mergedIntoBaseIndiNode, neighbourIndiId, ctx);  // u22
        //                     expanded |= expandIndividualNeighbourNodeFromBackendCache(mergedIntoBaseIndiNode, assocData,
        //                         neighbourIndiId, neighbourExpansionData, forceExpansion, forceExpansion,
        //                         &representativeLabelNeighbourExpansionData, backSyncDepTrackPoint, ctx);       // u23
        //                     if !representativeLabelNeighbourExpansionData: representativeExpansion = false;
        //                   delayingRepresentativeNeighbourExpansion(locBackendSyncData, delaying, representativeExpansion,
        //                       delayingLabelNeighbourExpansionData, lastCursor, neighbourIndiId, ctx);          // u25 (sibling)
        //                 lastCursor = nextCursor;
        //                 if expanded:
        //                   currentNeighbourExpansionCount++; oneExpanded = expanded;
        //                   if mOptQueuedBackendNeighbourExpansionIndisBatchSize > 0
        //                      && currentNeighbourExpansionCount >= mOptQueuedBackendNeighbourExpansionIndisBatchSize:
        //                       finished = false; return false;
        //                   return true;
        //                 return true;
        //               else:   // maxDirectNeighbourExpansionReached
        //                 propagationCut = true;
        //                 ctx->getSatisfiableCalculationTask()->getSatisfiableRepresentativeBackendCacheUpdatingAdapter()->setExpansionLimitReached();
        //                 indiLinker = allocate CXLinker<CIndividualProcessNode*>; indiLinker->initLinker(backendSyncDataIndiNode);
        //                 expContData->addCutBackendNeighbourExpansionIndividualLinker(indiLinker);
        //                 forceReadding = true; finished = false; return false;
        //             else:  // already possibly influenced
        //               lastCursor=nextCursor; newLastExpandedNeighbourId=neighbourIndiId; newCursor=nextCursor; return true;
        //           else:  // not potentially influenced
        //             lastCursor=nextCursor; newLastExpandedNeighbourId=neighbourIndiId; newCursor=nextCursor;
        //             deterministicFoundSkippedNeighbourNodeCount++; return true;
        //         }, newLinker->getNeighbourVisitingCursor(), false, ctx);
        //
        //     if oneExpanded: indiProcNode = mergedIntoBaseIndiNode;
        //     if !finished && (newCursor || forceReadding):
        //         newLinker->updateNeighbourExpansionCursor(newLastExpandedNeighbourId, newCursor);
        //         indiNeighbourExpansionQueue->addNeighbourExpansionQueueDataLinker(newLinker, false);
        //     if propagationCut && newLinker->isPropagationCutExpansion():
        //         indiNeighbourExpansionQueue->setCuttedPropagationCutPropagation(true);
        //
        //   if !indiNeighbourExpansionQueue->hasQueuedNeighbourExpansions() && !locBackendSyncData->hasNeighbourLabelRepresentativeExpansion():
        //     if locBackendSyncData->hasAllNeighbourExpansionScheduled(): locBackendSyncData->setAllNeighbourExpansion(true);
        //     if locBackendSyncData->hasAllNeighbourForcedExpansionScheduled(): locBackendSyncData->setAllNeighbourForcedExpansion(true);
        //   if propagationCut || !indiNeighbourExpansionQueue->hasQueuedNeighbourExpansions():
        //     baseIndiNode->setBackendNeighbourExpansionQueued(false);
        //   else:
        //     if integrated-node-count >= mOptCriticalBackendNeighbourTotalExpansionCount:
        //         mBackendLateNeighbourExpansionQueue = procDataBox->getBackendLateIndividualNeighbourExpansionQueue(true);
        //         mBackendLateNeighbourExpansionQueue->insertIndiviudalProcessNode(baseIndiNode);
        //     else: mBackendNeighbourExpansionQueue->insertIndiviudalProcessNode(baseIndiNode);
        //   return indiProcNode;
        //
        // Held PORT-PENDING: every typed local belongs to the not-yet-ported
        // backend-cache subsystem (sync data, association data, label cache items,
        // the `CBackendNeighbourExpansionQueue` + its data linkers, the
        // satisfiable-task representative-backend updating adapter); the
        // `canDelay*`/`delaying*` siblings land in u25 and the per-neighbour
        // expand helpers in u22/u23.
        let _ = (base_indi_node, exp_cont_data, calc_alg_context);
        Id::NONE
    }

    // =======================================================================
    // Non-concept-set / neighbour-label related processing marks
    // (cpp 24706–24797). The four guard helpers are substrate-portable.
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::markIndividualNodeBackendNonConceptSetRelatedAndNeighbourLabelRelatedProcessing`.
    /// cpp 24706–24711.
    ///
    /// Marks the node for BOTH non-concept-set related and neighbour-label related
    /// backend processing; returns whether either mark fired.
    pub fn mark_individual_node_backend_non_concept_set_related_and_neighbour_label_related_processing(
        &mut self,
        indi_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // bool marked = false;
        // marked |= markIndividualNodeBackendNonConceptSetRelatedProcessing(indiNode, ctx);
        // marked |= markIndividualNodeBackendNonConceptSetNeighbourLabelRelatedProcessing(indiNode, ctx);
        // return marked;
        let mut marked = false;
        // W3-DEFER[api]: `markIndividualNodeBackendNonConceptSetRelatedProcessing` is
        // a sibling helper ported in a different caching unit; faithful call shape.
        marked |= self.mark_individual_node_backend_non_concept_set_related_processing(
            indi_node,
            calc_alg_context,
        );
        marked |= self
            .mark_individual_node_backend_non_concept_set_neighbour_label_related_processing(
                indi_node,
                calc_alg_context,
            );
        marked
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::markIndividualNodeBackendNonConceptSetRelatedAndNeighbourLabelRelatedProcessingForDisjointRoles`.
    /// cpp 24715–24725.
    ///
    /// If any indirect super-role of `role` has disjoint roles, marks the node for
    /// both non-concept-set and neighbour-label related processing.
    pub fn mark_individual_node_backend_non_concept_set_related_and_neighbour_label_related_processing_for_disjoint_roles(
        &mut self,
        indi_node: NodeId,
        role: RoleId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // for (supRoleIt : role->getIndirectSuperRoleList()):
        //   if supRoleIt->getData()->hasDisjointRoles():
        //     marked |= markIndividualNodeBackendNonConceptSetRelatedProcessing(indiNode, ctx);
        //     marked |= markIndividualNodeBackendNonConceptSetNeighbourLabelRelatedProcessing(indiNode, ctx);
        //     return marked;
        // return false;
        let super_roles: Vec<RoleId> = calc_alg_context
            .ontology_arenas()
            .role(role)
            .get_indirect_super_role_list()
            .iter()
            .map(|nl| nl.target)
            .collect();
        for sup_role in super_roles {
            if calc_alg_context.ontology_arenas().role(sup_role).has_disjoint_roles() {
                let mut marked = false;
                // W3-DEFER[api]: sibling helper (other caching unit).
                marked |= self.mark_individual_node_backend_non_concept_set_related_processing(
                    indi_node,
                    calc_alg_context,
                );
                marked |= self
                    .mark_individual_node_backend_non_concept_set_neighbour_label_related_processing(
                        indi_node,
                        calc_alg_context,
                    );
                return marked;
            }
        }
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::markIndividualNodeBackendNonConceptSetRelatedProcessingForDisjointRoles`.
    /// cpp 24727–24734.
    ///
    /// If any indirect super-role of `role` has disjoint roles, marks the node for
    /// non-concept-set related backend processing.
    pub fn mark_individual_node_backend_non_concept_set_related_processing_for_disjoint_roles(
        &mut self,
        indi_node: NodeId,
        role: RoleId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // for (supRoleIt : role->getIndirectSuperRoleList()):
        //   if supRoleIt->getData()->hasDisjointRoles():
        //     return markIndividualNodeBackendNonConceptSetRelatedProcessing(indiNode, ctx);
        // return false;
        let super_roles: Vec<RoleId> = calc_alg_context
            .ontology_arenas()
            .role(role)
            .get_indirect_super_role_list()
            .iter()
            .map(|nl| nl.target)
            .collect();
        for sup_role in super_roles {
            if calc_alg_context.ontology_arenas().role(sup_role).has_disjoint_roles() {
                // W3-DEFER[api]: sibling helper (other caching unit).
                return self.mark_individual_node_backend_non_concept_set_related_processing(
                    indi_node,
                    calc_alg_context,
                );
            }
        }
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::markIndividualNodeBackendNonConceptSetNeighbourLabelRelatedProcessingForDisjointRoles`.
    /// cpp 24736–24743.
    ///
    /// If any indirect super-role of `role` has disjoint roles, marks the node for
    /// neighbour-label related backend processing.
    pub fn mark_individual_node_backend_non_concept_set_neighbour_label_related_processing_for_disjoint_roles(
        &mut self,
        indi_node: NodeId,
        role: RoleId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // for (supRoleIt : role->getIndirectSuperRoleList()):
        //   if supRoleIt->getData()->hasDisjointRoles():
        //     return markIndividualNodeBackendNonConceptSetNeighbourLabelRelatedProcessing(indiNode, ctx);
        // return false;
        let super_roles: Vec<RoleId> = calc_alg_context
            .ontology_arenas()
            .role(role)
            .get_indirect_super_role_list()
            .iter()
            .map(|nl| nl.target)
            .collect();
        for sup_role in super_roles {
            if calc_alg_context.ontology_arenas().role(sup_role).has_disjoint_roles() {
                return self
                    .mark_individual_node_backend_non_concept_set_neighbour_label_related_processing(
                        indi_node,
                        calc_alg_context,
                    );
            }
        }
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::markIndividualNodeBackendNonConceptSetNeighbourLabelRelatedProcessing`.
    /// cpp 24745–24797.
    ///
    /// Marks the node's localized backend sync data for non-concept-set neighbour-
    /// label related processing and, if it carries installed label-representative
    /// expansions, re-queues every such delayed representative expansion onto its
    /// expanding node's backend neighbour-expansion queue (scheduling that node on
    /// the late/normal backend neighbour-expansion queue as needed), then clears the
    /// representative-expansion linker.
    pub fn mark_individual_node_backend_non_concept_set_neighbour_label_related_processing(
        &mut self,
        indi_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // PORT-PENDING: faithful transcription of cpp 24745–24797. Outline:
        //
        //   backendSyncData = indiNode->getIndividualBackendCacheSynchronisationData(false);
        //   if backendSyncData && !backendSyncData->hasNonConceptSetBackendLabelRelatedProcessing()
        //      && backendSyncData->getAssocitaionData():
        //     locIndiNode = getLocalizedIndividual(indiNode, false, ctx);
        //     locBackendSyncData = getLocalizedIndividualBackendCacheSnychronisationData(locIndiNode, ctx);   // u17
        //     locBackendSyncData->setNonConceptSetBackendNeighbourLabelRelatedProcessing(true);
        //     if locBackendSyncData->hasNeighbourLabelRepresentativeExpansionInstalled():
        //       for expData in locBackendSyncData->getNeighbourLabelRepresentativeExpansionLinker():
        //         expBaseIndiNode = expData->getExpandingIndividiaulNode();
        //         expQueuData     = expData->getExpandingQueueData();
        //         newLinker = allocate CBackendNeighbourExpansionQueueDataLinker; newLinker->initQueueData(expQueuData);
        //         newLinker->setExpandingLabel(expData->getConceptSetLabel());
        //         newLinker->updateNeighbourExpansionCursor(expData->getRepresentativeExpandedIndividual(),
        //                                                   expData->getNextLabelNeighbourExpansionIteratorCursor());
        //         expLocBackendSyncData = getLocalizedIndividualBackendCacheSnychronisationData(expBaseIndiNode, ctx);  // u17
        //         indiNeighbourExpansionQueue = expLocBackendSyncData->getBackendNeighbourExpansionQueue(true);
        //         labelHash = expLocBackendSyncData->getNeighbourLabelExpansionDataHash(expData->getNeighbourExpansionArrayId(), true);
        //         labelHash[expData->getConceptSetLabel()].setAllLabelNeighbourExpansionScheduled(true);
        //         indiNeighbourExpansionQueue->addNeighbourExpansionQueueDataLinker(newLinker, false);
        //         if indiNeighbourExpansionQueue->hasQueuedNeighbourExpansions() && !expBaseIndiNode->isBackendNeighbourExpansionQueued():
        //           if integrated-node-count >= mOptCriticalBackendNeighbourTotalExpansionCount:
        //               ctx->getUsedProcessingDataBox()->getBackendLateIndividualNeighbourExpansionQueue(true)
        //                  ->insertIndiviudalProcessNode(expBaseIndiNode);
        //           else: ctx->getUsedProcessingDataBox()->getBackendIndividualNeighbourExpansionQueue(true)
        //                  ->insertIndiviudalProcessNode(expBaseIndiNode);
        //       locBackendSyncData->clearNeighbourLabelRepresentativeExpansionLinker();
        //   return false;
        //
        // Held PORT-PENDING: the per-node backend sync data, the
        // `CIndividualNodeRepresentativeMemoryBackendCacheSynchronisationLabelNeighbourExpansionData`
        // representative-expansion linker chain, the `CBackendNeighbourExpansionQueue`
        // + its data linkers, and the databox backend neighbour-expansion queue
        // getters are not yet ported (W6-DEFER[api]). The
        // `getLocalizedIndividualBackendCacheSnychronisationData` sibling lives in
        // u17 and becomes live on the reconcile pass.
        let _ = (indi_node, calc_alg_context);
        false
    }

    // =======================================================================
    // Backend expansion reuse branching (cpp 24803–24881).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::prepareBackendExpansionReuseBranching`.
    /// cpp 24803–24881.
    ///
    /// Installs the backend-expansion reuse-mode dependency node (once per test). If
    /// the representative-backend updating adapter has not hit its expansion limit it
    /// simply switches on the prioritized reuse-expansion mode; otherwise it forks
    /// two dependent branching tasks (a fixed-reuse and a prioritized-reuse
    /// alternative), communicates their creation, and aborts the current task with
    /// a stop-processing exception.
    ///
    /// KONCLUDE-PORT-NOTE[exceptions]: the C++ `throw
    /// CCalculationStopProcessingException(true)` is control flow, not an error; in
    /// the port it becomes an early return once the task-fork machinery is wired.
    pub fn prepare_backend_expansion_reuse_branching(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // PORT-PENDING: faithful transcription of cpp 24803–24881. Outline:
        //
        //   expContData = ctx->getUsedProcessingDataBox()->getBackendNeighbourExpansionControllingData(true);
        //   reuseModesDepNode = expContData->getReuseModesDependencyNode();
        //   if !reuseModesDepNode:
        //     processorContext  = ctx->getUsedTaskProcessorContext();
        //     processingDataBox = ctx->getUsedProcessingDataBox();
        //     reuseDepNode = createREUSEBACKENDEXPANSIONMODESDependency(nullptr, ctx);          // dep unit
        //     processingDataBox->getBackendNeighbourExpansionControllingData(true)->setReuseModesDependencyNode(reuseDepNode);
        //
        //     repBackCacheUpAdapter = ctx->getSatisfiableCalculationTask()->getSatisfiableRepresentativeBackendCacheUpdatingAdapter();
        //     if repBackCacheUpAdapter && !repBackCacheUpAdapter->hasExpansionLimitReached():
        //         processingDataBox->getBackendNeighbourExpansionControllingData(true)->setPrioritizedReuseExpansionMode(true);
        //         return true;
        //     else:
        //         taskCreationCount = 2;
        //         newTaskList = createDependendBranchingTaskList(taskCreationCount, ctx);        // backtracking unit
        //         newTaskIt = newTaskList;
        //         for i in 0..taskCreationCount:
        //           newSatCalcTask = newTaskIt; fixedReusingAlternative = (i == 0);
        //           newProcessContext  = newSatCalcTask->getProcessContext(processorContext);
        //           newCalcAlgContext  = createCalculationAlgorithmContext(processorContext, newProcessContext, newSatCalcTask);  // core unit
        //           newAllocMemMan     = newCalcAlgContext->getUsedProcessTaskMemoryAllocationManager();
        //           newProcessingDataBox = newSatCalcTask->getProcessingDataBox();
        //           newBackendExpControllingData = newProcessingDataBox->getBackendNeighbourExpansionControllingData(true);
        //           newDependencyTrackPoint = createNonDeterministicDependencyTrackPointBranch(reuseDepNode, false, newCalcAlgContext);  // dep unit
        //           if fixedReusingAlternative: reuseDepNode->setFixedReuseDependencyTrackPoint(newDependencyTrackPoint);
        //           else:                       reuseDepNode->setPriorizedReuseDependencyTrackPoint(newDependencyTrackPoint);
        //           newBackendExpControllingData->setReuseContinuingDependencyTrackPoint(newDependencyTrackPoint);
        //           if fixedReusingAlternative:
        //               newBackendExpControllingData->setFixedReuseExpansionMode(true);
        //               newProcessTagger = newCalcAlgContext->getUsedProcessTagger();
        //               newProcessTagger->incBranchingTag(); newProcessTagger->incLocalizationTag();
        //           else: newBackendExpControllingData->setPrioritizedReuseExpansionMode(true);
        //           newTaskPriority = ctx->getUsedTaskPriorityStrategy()->getPriorityForTaskReusing(
        //               newSatCalcTask, ctx->getUsedSatisfiableCalculationTask(), fixedReusingAlternative);
        //           newSatCalcTask->setTaskPriority(newTaskPriority);
        //           newTaskIt = newTaskIt->getNext();
        //         processorContext->getTaskProcessorCommunicator()->communicateTaskCreation(newTaskList);
        //         throw CCalculationStopProcessingException(true);     // [exceptions] -> early return once task-fork wired
        //   return false;
        //
        // Held PORT-PENDING: the `CBackendNeighbourExpansionControllingData`
        // (process-layer `stub!` marker, no arena/accessors yet), the
        // `CREUSEBACKENDEXPANSIONMODESDependencyNode` dependency node + its
        // create/track-point siblings, the satisfiable-task representative-backend
        // updating adapter, and the whole task-forking path
        // (`createDependendBranchingTaskList`, `createCalculationAlgorithmContext`,
        // the task-processor communicator) are W6 / later-unit deferrals. W3-DEFER[exceptions]
        // for the terminal stop-processing throw.
        let _ = calc_alg_context;
        false
    }
}
