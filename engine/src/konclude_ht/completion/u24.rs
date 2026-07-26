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
//! `expandDirectlyInfluencedIndividualNeighbourNodesFromBackendCache` is LIVE for
//! its decisive step (5) — the `!hasAllNeighbourExpansionScheduled()` /
//! `cardBlockCrit || testIndividualNodeBackendCacheNeighbourExpansionBlockingCritical`
//! gate driving `expandDirectlyInfluencedNeighboursWithPropagation` over only the
//! concept descriptors newer than the two incremental cursors — against the typed
//! native-ABox association (the `native_*` backend-cache accessors in u36). Its
//! merge-driven steps (1)-(4)/(6) iterate the merged-individual-node linker, which
//! is empty on that route, and stay documented in place.
//!
//! The other three bodies are driven start-to-finish by the deferred backend-cache
//! subsystem; they are kept `// PORT-PENDING` with the faithful signature and a
//! structural transcription of the C++ so a later wave fills them without
//! re-reading the source. Logic is documented, never silently dropped.

#![allow(dead_code)]
#![allow(unused_variables)]

use super::super::model::substrate::{Cint64, Id};
use super::super::model::RoleId;
use super::super::process::{ConDescId, LabelSetId, NodeId, TrackPointId};
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
        // bool lazyNeighboursExpansionSucceded = true;
        // if (indiNode->hasPurgedBlockedProcessingRestrictionFlags()) return false;
        if indi_node.is_none()
            || indi_node.index() >= calc_alg_context.process_context().node_count()
        {
            return false;
        }
        if calc_alg_context
            .process_context()
            .node(indi_node)
            .has_purged_blocked_processing_restriction_flags()
        {
            return false;
        }
        // backendSyncData / locBackendSyncData + assocData. The generic
        // representative-memory association is not ported; the typed native-ABox
        // association handle is the node's nominal individual tag (see the
        // `native_*` accessors in u36). Without an association there is nothing
        // cache-backed to expand and the caller must fall back to the raw
        // assertion replay, exactly as the C++ `!backendSyncData ||` disjunct at
        // cpp 8938 does.
        let Some(assoc_tag) = self.native_association_tag(indi_node, calc_alg_context) else {
            return false;
        };
        let loc_backend_sync_data =
            self.get_localized_individual_backend_cache_snychronisation_data(
                indi_node,
                calc_alg_context,
            );

        // W6-DEFER[api]: steps (1)-(4) and (6) of the C++ body are driven by the
        // newly-merged backend-representative visitors
        // (`visitNewlyMerged{,OnlyDeterministicRepresentative}IndividualsBackendSynchronisationData`,
        // merge unit) over the generic association's same/different-individual and
        // neighbour-role-set-combination labels:
        //   (1) cpp 24000–24072 merge all deterministic same-individuals of every
        //       newly merged node (DETERMINISTIC_SAME_INDIVIDUAL_SET_LABEL, then
        //       `getMergedIndividualNodes` or a clash);
        //   (2) cpp 24093–24151 inferring- vs all-neighbour expansion of the newly
        //       merged representatives (`expandIndividualInferringNeighboursFromBackendCache`
        //       / `expandIndividualAllNeighboursFromBackendCache`, u23);
        //   (3) cpp 24157–24215 differentiate deterministic different-individuals
        //       (DETERMINISTIC_DIFFRENT_INDIVIDUAL_SET_LABEL → `createIndividualsDistinct`
        //       or a clash);
        //   (4) cpp 24221–24270 establish prioritised propagation-cut links
        //       (NEIGHBOUR_INSTANTIATED_ROLE_SET_COMBINATION_LABEL over the top role →
        //       `initializeNeighbourExpansionWithPropagation`, u27);
        //   (6) cpp 24380–24398 advance the handled-merged-node cursor
        //       (`setLastDirectExpansionHandledMergedNodeLinker` /
        //       `setLastInferringExpansionHandledMergedNodeLinker`).
        // All five iterate the merged-individual-node linker, which stays EMPTY on
        // the typed native route: the bridge rejects source `SameIndividual`, so a
        // typed association never carries a deterministic same-individual merging.
        // The trace corroborates the same shape upstream — 0 of 198 roots merged
        // deterministically and DETERMINISTIC_SAME_INDIVIDUAL_SET_LABEL empty on all
        // 198 — so step (5) is the whole of this method on this route.

        // ---- (5) directly-influenced neighbour expansion, per newly added concept
        //          descriptor, bounded by the two incremental cursors.
        self.native_selective_neighbour_expansion_declined = false;
        // if (!backendSyncData->hasAllNeighbourExpansionScheduled())
        if calc_alg_context
            .process_context()
            .backend_sync_data(loc_backend_sync_data)
            .has_all_neighbour_expansion_scheduled()
        {
            return true;
        }
        // cardBlockCrit = testIndividualNodeBackendCacheExpansionBlockingCriticalCardinality(...)
        // if (cardBlockCrit || testIndividualNodeBackendCacheNeighbourExpansionBlockingCritical(...))
        let card_block_crit = self
            .test_individual_node_backend_cache_expansion_blocking_critical_cardinality(
                indi_node,
                calc_alg_context,
            );
        if !card_block_crit
            && !self.test_individual_node_backend_cache_neighbour_expansion_blocking_critical(
                indi_node,
                calc_alg_context,
            )
        {
            return true;
        }

        let mut last_tested_con_des: ConDescId = calc_alg_context
            .process_context()
            .backend_sync_data(loc_backend_sync_data)
            .get_last_neighbour_influence_tested_concept_descriptor();
        let mut last_neighbour_critical_con_des: ConDescId = calc_alg_context
            .process_context()
            .backend_sync_data(loc_backend_sync_data)
            .get_last_critical_neighbour_expansion_tested_concept_descriptor();
        // if (cardBlockCrit && !locSyncData->hasNeighbourInfluenceTestingCriticalCardinalityReset())
        //   reset both cursors — a newly critical cardinality invalidates every
        //   earlier "already influenced" decision.
        if card_block_crit
            && !calc_alg_context
                .process_context()
                .backend_sync_data(loc_backend_sync_data)
                .has_neighbour_influence_testing_critical_cardinality_reset()
        {
            last_tested_con_des = Id::NONE;
            last_neighbour_critical_con_des = Id::NONE;
        }
        // The second C++ reset —
        //   if (indiNode->getIndividualNodeID() != locNode->getIndividualNodeID()
        //       && indiNode->getIndividualNodeID()
        //          != locSyncData->getLastMergedIntoIndividualTestingCriticalCardinalityReset())
        // — distinguishes the node from the merged-into representative whose sync
        // data is being read. They coincide on the typed route (no deterministic
        // same-individual merging), so it never fires.

        // conSet = indiNode->getReapplyConceptLabelSet(false);
        let con_set: LabelSetId = calc_alg_context
            .process_context_mut()
            .node_mut(indi_node)
            .get_reapply_concept_label_set(false);
        if con_set.is_none() {
            return !self.native_selective_neighbour_expansion_declined;
        }
        let con_des_linker: ConDescId = calc_alg_context
            .process_context()
            .label_set(con_set)
            .get_adding_sorted_concept_description_linker();
        if con_des_linker == last_tested_con_des {
            return !self.native_selective_neighbour_expansion_declined;
        }
        let mut con_des_it = con_des_linker;
        let mut walked = 0usize;
        while con_des_it.is_some()
            && con_des_it != last_tested_con_des
            && con_des_it != last_neighbour_critical_con_des
        {
            if con_des_it.index() >= calc_alg_context.process_context().con_desc_count()
                || walked > calc_alg_context.process_context().con_desc_count()
            {
                // Malformed descriptor chain: decline the cache-backed route rather
                // than expanding a partial neighbour set.
                self.native_selective_neighbour_expansion_declined = true;
                break;
            }
            let (concept, con_negation, dep_track_point, next) = {
                let descriptor = calc_alg_context.process_context().con_desc(con_des_it);
                (
                    descriptor.get_concept(),
                    descriptor.is_negated(),
                    descriptor.get_dependency_track_point(),
                    descriptor.get_next_concept_descriptor(),
                )
            };
            // nondeterministic = hasNondeterministicDependency(conDes->getDependencyTrackPoint(), ctx)
            //                    || hasNondeterministicDependency(backSyncDepTrackPoint, ctx);
            // The typed association is consumed on the task's base dependency, so
            // `backSyncDepTrackPoint` is deterministic by construction.
            let nondeterministic =
                self.has_nondeterministic_dependency(dep_track_point, calc_alg_context);
            if concept.is_some() {
                self.expand_directly_influenced_neighbours_with_propagation(
                    concept,
                    con_negation,
                    nondeterministic,
                    indi_node,
                    assoc_tag,
                    indi_node,
                    loc_backend_sync_data.raw,
                    dep_track_point,
                    calc_alg_context,
                );
            }
            if calc_alg_context.has_pending_signal() {
                break;
            }
            con_des_it = next;
            walked += 1;
        }
        // locSyncData->setLastNeighbourInfluenceTestedConceptDescriptor(conDesLinker);
        // locSyncData->hasNeighbourInfluenceTestingCriticalCardinalityReset(cardBlockCrit);
        if !self.native_selective_neighbour_expansion_declined
            && !calc_alg_context.has_pending_signal()
        {
            let loc_backend_sync_data =
                self.get_localized_individual_backend_cache_snychronisation_data(
                    indi_node,
                    calc_alg_context,
                );
            calc_alg_context
                .process_context_mut()
                .backend_sync_data_mut(loc_backend_sync_data)
                .set_last_neighbour_influence_tested_concept_descriptor(con_des_linker)
                .set_neighbour_influence_testing_critical_cardinality_reset(card_block_crit);
        }

        // expandIndirectlyConnectedIndividuals(indiNode, true, ctx);
        // W6-DEFER[api]: u27's sibling is still PORT-PENDING; the typed route keeps
        // `PRFSYNCHRONIZEDBACKENDINDIRECTNOMINALEXPANSIONBLOCKED` set instead, which
        // never skips work.

        // return lazyNeighboursExpansionSucceded;
        !self.native_selective_neighbour_expansion_declined
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
            if calc_alg_context
                .ontology_arenas()
                .role(sup_role)
                .has_disjoint_roles()
            {
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
            if calc_alg_context
                .ontology_arenas()
                .role(sup_role)
                .has_disjoint_roles()
            {
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
            if calc_alg_context
                .ontology_arenas()
                .role(sup_role)
                .has_disjoint_roles()
            {
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
        let exp_cont_data = calc_alg_context.backend_neighbour_expansion_controlling_data(true);
        let reuse_modes_dep_node = calc_alg_context
            .process_context()
            .backend_neighbour_expansion_controlling_data(exp_cont_data)
            .get_reuse_modes_dependency_node();
        if reuse_modes_dep_node.is_some() {
            return false;
        }

        let reuse_dep_node = self
            .create_reuse_backend_expansion_modes_dependency(TrackPointId::NONE, calc_alg_context);
        calc_alg_context
            .process_context_mut()
            .backend_neighbour_expansion_controlling_data_mut(exp_cont_data)
            .set_reuse_modes_dependency_node(reuse_dep_node);

        // W6-DEFER[api]: the representative-backend updating adapter and the
        // expansion-limit branch that forks fixed/prioritized dependent tasks are
        // still not live. This ports the currently reachable no-limit branch.
        calc_alg_context
            .process_context_mut()
            .backend_neighbour_expansion_controlling_data_mut(exp_cont_data)
            .set_prioritized_reuse_expansion_mode(true);
        true
    }
}
