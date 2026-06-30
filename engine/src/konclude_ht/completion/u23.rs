//! `completion::u23` — Caching / backend-cache / saturation family, batch
//! (port unit #23 of 36).
//!
//! Faithful port of the 6 methods that the manifest (`01-completion-methods.md`,
//! "Unit 23") groups under the representative-memory backend-cache *neighbour-node*
//! expansion of Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`.
//! cpp source line ranges (1-based) per method are noted on each item.
//!
//! Methods (cpp order):
//!   * `expandIndirectCompatibleRequiredIndividualNeighbourNodesFromBackendCache`   [23282–23328] (entry, 1 indi)
//!   * `expandIndirectCompatibleRequiredIndividualNeighbourNodesFromBackendCache`   [23335–23595] (+checking node)
//!   * `expandIndividualInferringNeighboursFromBackendCache`                        [23603–23657]
//!   * `expandIndividualAllNeighboursFromBackendCache`                              [23663–23731]
//!   * `expandIndividualNeighbourNodeFromBackendCache`                              [23782–23812] (neighbourIndiId)
//!   * `expandIndividualNeighbourNodeFromBackendCache`                              [23819–23926] (assocData + …)
//!
//! KONCLUDE-PORT-NOTE[ownership]: each method is a member of
//! `CCalculationTableauCompletionTaskHandleAlgorithm`, so it becomes `&mut self`
//! plus the threaded per-thread context `calc_alg_context: &mut
//! CalculationAlgorithmContextBase`. A plain `CIndividualProcessNode*` value
//! parameter becomes `NodeId`; a `CDependencyTrackPoint*` becomes `TrackPointId`;
//! the per-test arenas are reached through the context as
//! `calc_alg_context.process_context()` / `_mut()`, the databox as
//! `calc_alg_context.processing_data_box{,_mut}()`, terminology via
//! `calc_alg_context.ontology_arenas()`.
//!
//! KONCLUDE-PORT-NOTE[overload]: Rust has no function overloading, so the two C++
//! same-name overload pairs get a disambiguating suffix preserving their
//! distinguishing parameter (the u10 convention):
//!   * `expandIndirectCompatibleRequiredIndividualNeighbourNodesFromBackendCache`
//!     (entry)            → `expand_indirect_compatible_required_individual_neighbour_nodes_from_backend_cache`
//!     (+checking node)   → `…_checking`
//!   * `expandIndividualNeighbourNodeFromBackendCache`
//!     (`neighbourIndiId`)→ `expand_individual_neighbour_node_from_backend_cache`
//!     (`assocData` + …)  → `…_assoc`
//!
//! Deferral landscape. Five of the six methods are driven start-to-finish by the
//! representative-memory backend cache subsystem that is NOT yet ported (the W6
//! Cache subtree), namely
//!   * `CIndividualNodeRepresentativeMemoryBackendCacheSynchronisationData` and its
//!     localized twin (per-node sync data: merged-node linkers, the
//!     same/different-individual handling flags, the neighbour-expansion data
//!     hashes, the all-neighbour-expansion scheduling flags, the label
//!     representative-expansion linkers) — `process::stubs::BackendSyncDataId` is a
//!     zero-size marker today;
//!   * `CBackendRepresentativeMemoryCacheIndividualAssociationData` + the
//!     `CBackendRepresentativeMemoryLabelCacheItem` family + the role-set neighbour
//!     arrays / index extension data — reached only through `mBackendCacheHandler`
//!     (`self.backend_cache_handler`, a zero-size `Id` stub);
//!   * `CBackendNeighbourExpansionQueue` — the per-node expansion work queue
//!     (process-layer `stub!` marker, no arena yet).
//! Following the porting convention, the one genuinely substrate-portable method —
//! the entry overload, which is pure sibling dispatch — is ported in full; the
//! other five are kept `// PORT-PENDING` with the faithful signature and a
//! structural transcription of the C++ so a later wave fills them without
//! re-reading the source. Logic is documented, never silently dropped.
//!
//! KONCLUDE-PORT-NOTE[api]: the deferred backend-cache value/reference parameters
//! (`CBackendRepresentativeMemoryCacheIndividualAssociationData* assocData`, the
//! `…NeighbourExpansionData&` in/out reference, the
//! `…LabelNeighbourExpansionData**` out double-pointer) are opaque `Cint64` /
//! `&mut Cint64` slots until the Cache subtree lands (`INVALID` == `nullptr`).

#![allow(dead_code)]
#![allow(unused_variables)]

use super::super::model::substrate::Cint64;
use super::super::process::{NodeId, TrackPointId};
use super::context::CalculationAlgorithmContextBase;

impl super::algorithm::CompletionTaskHandleAlgorithm {
    // =======================================================================
    // Indirect-compatible required neighbour expansion — entry overload
    // (cpp 23282–23328). Substrate-portable: pure sibling dispatch.
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::expandIndirectCompatibleRequiredIndividualNeighbourNodesFromBackendCache`
    /// (the entry, single-individual overload). cpp 23282–23328.
    ///
    /// Tests the node for newly arrived backend mergings, delegates to the
    /// `…_checking` overload against the node itself, then expands the indirectly
    /// connected individuals. Always returns `true`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: the large commented-out alternative in the C++ (the
    /// `locBackendSyncData` "remaining indirect-compatibility merged-individual
    /// checking set" iteration over `visitNewlyMergedIndividualsBackendSynchronisationData`,
    /// cpp 23287–23322) is dead code in the source and is intentionally not ported.
    pub fn expand_indirect_compatible_required_individual_neighbour_nodes_from_backend_cache(
        &mut self,
        indi_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // TODO (Konclude): try non-deterministic reusing first.

        // testIndividualNodeBackendCacheNewMergings(indiNode, calcAlgContext);
        // W3-DEFER[api]: merge-family sibling (later unit); faithful call shape.
        self.test_individual_node_backend_cache_new_mergings(indi_node, calc_alg_context);

        // expandIndirectCompatibleRequiredIndividualNeighbourNodesFromBackendCache(indiNode, indiNode, calcAlgContext);
        self.expand_indirect_compatible_required_individual_neighbour_nodes_from_backend_cache_checking(
            indi_node,
            indi_node,
            calc_alg_context,
        );

        // expandIndirectlyConnectedIndividuals(indiNode, true, calcAlgContext);
        // W3-DEFER[api]: sibling helper (incremental-expansion unit); faithful call shape.
        self.expand_indirectly_connected_individuals(indi_node, true, calc_alg_context);

        true
    }

    // =======================================================================
    // Indirect-compatible required neighbour expansion — +checking-node overload
    // (cpp 23335–23595).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::expandIndirectCompatibleRequiredIndividualNeighbourNodesFromBackendCache`
    /// (the `checkingBackendSyncDataIndiNode` overload). cpp 23335–23595.
    ///
    /// Decides whether `indiNode` needs neighbour integration from the backend cache
    /// of `checkingBackendSyncDataIndiNode`: neighbours have to be integrated if the
    /// cache carries (a) a non-deterministic concept not in the current label, (b) a
    /// non-deterministic same/different individual reference not yet present, or (c)
    /// a non-deterministic instantiated-role-set neighbour combination. For (a)–(b)
    /// it schedules an `expandIndividualAllNeighboursFromBackendCache`; for (c) it
    /// initialises a per-role-array neighbour expansion with propagation and signals
    /// that indirect-compatibility checking must continue.
    ///
    /// Returns `requiredCheckingContinuation`.
    pub fn expand_indirect_compatible_required_individual_neighbour_nodes_from_backend_cache_checking(
        &mut self,
        indi_node: NodeId,
        checking_backend_sync_data_indi_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // PORT-PENDING: faithful transcription of cpp 23335–23595. Outline:
        //
        //   requiredCheckingContinuation = false;
        //   backendSyncData    = checkingNode->getIndividualBackendCacheSynchronisationData(false);
        //   locBackendSyncData = checkingNode->getIndividualBackendCacheSynchronisationData(true);
        //
        //   backSyncDepTrackPoint = ctx->getBaseDependencyNode()->getContinueDependencyTrackPoint();
        //   mergingHash = indiNode->getIndividualMergingHash(false);
        //   if mergingHash && indiNode.id != checkingNode.id:
        //     mergingData = mergingHash->value(checkingNode->getNominalIndividual()->getIndividualID());
        //     backSyncDepTrackPoint = mergingData.getDependencyTrackPoint();
        //
        //   // neighbours have to be integrated if the cache holds
        //   //   - a non-deterministic concept not in the current label, or
        //   //   - a non-deterministic same/different individual reference not in the graph.
        //   assocData = backendSyncData->getAssocitaionData();
        //   conSet    = indiNode->getReapplyConceptLabelSet(false);
        //   requiredAllNeighbourExpansion       = backendSyncData->hasAllNeighbourExpansionScheduled();
        //   requiredAllNeighbourForcedExpansion = backendSyncData->hasAllNeighbourForcedExpansionScheduled();
        //   nonDeterministicConsequencesMissing = true;
        //
        //   // (a) non-deterministic concept test over the FULL_CONCEPT_SET_LABEL:
        //   if !requiredAllNeighbourExpansion && assocData:
        //     conSetLabel = assocData->getLabelCacheEntry(FULL_CONCEPT_SET_LABEL);
        //     if conSetLabel && conSetLabel->hasNondeterministicElements():
        //       mBackendCacheHandler->visitConceptsOfAssociatedFullConceptSetLabel(assocData, conSetLabel,
        //           |concept, negation, nondeterministic| {
        //             if !conSet->containsConcept(concept, negation):
        //               requiredAllNeighbourExpansion = true; nonDeterministicConsequencesMissing = true; return false;
        //             return true; }, false, true, ctx);
        //
        //   // (b) non-deterministic same-individual test over NONDETERMINISTIC_SAME_INDIVIDUAL_SET_LABEL:
        //   if !requiredAllNeighbourForcedExpansion && assocData:
        //     indiSetLabel = assocData->getLabelCacheEntry(NONDETERMINISTIC_SAME_INDIVIDUAL_SET_LABEL);
        //     if indiSetLabel:
        //       mBackendCacheHandler->visitIndividualIdsOfAssociatedIndividualSetLabel(assocData, indiSetLabel,
        //           |indiId| {
        //             if indiId != indiNode->getNominalIndividual()->getIndividualID()
        //                && (!mergingHash || !mergingHash->contains(indiId)):
        //               requiredAllNeighbourExpansion = true; requiredAllNeighbourForcedExpansion = true;
        //               nonDeterministicConsequencesMissing = true; return false;
        //             return true; }, ctx);
        //
        //   // (b') non-deterministic different-individual test over NONDETERMINISTIC_DIFFRENT_INDIVIDUAL_SET_LABEL:
        //   if !requiredAllNeighbourForcedExpansion && assocData:
        //     diffSetLabel = assocData->getLabelCacheEntry(NONDETERMINISTIC_DIFFRENT_INDIVIDUAL_SET_LABEL);
        //     if diffSetLabel:
        //       distinctHash = indiNode->getDistinctHash(false);
        //       mBackendCacheHandler->visitIndividualIdsOfAssociatedIndividualSetLabel(assocData, diffSetLabel,
        //           |indiId| {
        //             if indiId != indiNode->getNominalIndividual()->getIndividualID()
        //                && (!distinctHash || !distinctHash->contains(indiId)):
        //               requiredAllNeighbourExpansion = true; requiredAllNeighbourForcedExpansion = true;
        //               nonDeterministicConsequencesMissing = true; return false;
        //             return true; }, ctx);
        //
        //   // (c) non-deterministic instantiated-role-set neighbour combination:
        //   if !requiredAllNeighbourExpansion && assocData
        //      && assocData->getLabelCacheEntry(NEIGHBOUR_INSTANTIATED_ROLE_SET_COMBINATION_LABEL)->hasNondeterministicElements():
        //     locBackendSyncData = getLocalizedIndividualBackendCacheSnychronisationData(checkingNode, ctx);   // u17
        //     requiredCheckingContinuation = true;
        //     topRole = ctx->getProcessingDataBox()->getOntology()->getRBox()->getTopObjectRole();
        //     neighbourExpansionDataHash = locBackendSyncData->getNeighbourExpansionDataHash(true);
        //     neighbourRoleSetArray = assocData->getRoleSetNeighbourArray();
        //     if neighbourRoleSetArray:
        //       indexData = neighbourRoleSetArray->getIndexData();
        //       for i in 0..indexData->getArraySize():
        //         neighbourRoleSetLabel = indexData->getNeighbourRoleSetLabel(i);
        //         nondeterministic = neighbourRoleSetLabel->hasNondeterministicElements();
        //         if nondeterministic && (neighbourRoleSetLabel->getCacheValueCount() >= 1
        //              || neighbourRoleSetLabel->getCacheValueLinker()->getCacheValue().getTag() != topRole->getRoleTag()):
        //           markIndividualNodeBackendNonConceptSetRelatedAndNeighbourLabelRelatedProcessing(indiNode, ctx);  // u24
        //           initializeNeighbourExpansionWithPropagation(indiNode, checkingNode, locBackendSyncData,
        //               backSyncDepTrackPoint, i, nullptr, false, true, nullptr, true, false, true, ctx);            // u27
        //     // (the per-neighbour role-link presence check, cpp 23459–23584, is commented out in the source)
        //
        //   // schedule all-neighbour expansion if newly required:
        //   if (requiredAllNeighbourExpansion && !backendSyncData->hasAllNeighbourExpansionScheduled())
        //      || (requiredAllNeighbourForcedExpansion && !backendSyncData->hasAllNeighbourForcedExpansionScheduled()):
        //     expandIndividualAllNeighboursFromBackendCache(indiNode, checkingNode, requiredAllNeighbourForcedExpansion,
        //         nonDeterministicConsequencesMissing, backSyncDepTrackPoint, ctx);                                  // this unit
        //
        //   return requiredCheckingContinuation;
        //
        // Held PORT-PENDING: every typed local belongs to the not-yet-ported
        // backend-cache subsystem (sync data, association data, the label cache
        // items + their non-deterministic-element predicates, the role-set neighbour
        // array + index extension data), reached through `mBackendCacheHandler`; the
        // `markIndividualNodeBackendNonConceptSetRelatedAndNeighbourLabelRelatedProcessing`
        // (u24) and `initializeNeighbourExpansionWithPropagation` (u27) siblings and
        // the `expandIndividualAllNeighboursFromBackendCache` (this unit) call become
        // live on the reconcile pass.
        let _ = (indi_node, checking_backend_sync_data_indi_node, calc_alg_context);
        false
    }

    // =======================================================================
    // Inferring neighbour expansion (cpp 23603–23657).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::expandIndividualInferringNeighboursFromBackendCache`.
    /// cpp 23603–23657.
    ///
    /// For every role-set neighbour array of the merged node's association data,
    /// visits the neighbour individual ids: a neighbour already locally available, or
    /// whose recorded role-set label disagrees with the array's, is "potentially
    /// influenced" and gets expanded against each relevant merged backend-sync-data
    /// individual's association data; an unrecorded neighbour records the array's
    /// role-set label and is expanded against the checking node's localized
    /// association data. Always returns `true`.
    pub fn expand_individual_inferring_neighbours_from_backend_cache(
        &mut self,
        indi_node: NodeId,
        backend_sync_data_indi_node: NodeId,
        force_expansion: bool,
        back_sync_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // PORT-PENDING: faithful transcription of cpp 23603–23657. Outline:
        //
        //   indiBackendSyncData = getLocalizedIndividualBackendCacheSnychronisationData(indiNode, ctx);   // u17
        //   assocData = indiBackendSyncData->getAssocitaionData();
        //   neighbourExpansionDataHash = indiBackendSyncData->getNeighbourExpansionDataHash(true);
        //   indiNodeVec = ctx->getProcessingDataBox()->getIndividualProcessNodeVector();
        //   mergedAssocData = backendSyncDataIndiNode->getIndividualBackendCacheSynchronisationData(false)->getAssocitaionData();
        //   if mergedAssocData:
        //     neighbourRoleSetArray = mergedAssocData->getRoleSetNeighbourArray();
        //     if neighbourRoleSetArray:
        //       indexData = neighbourRoleSetArray->getIndexData();
        //       for i in 0..indexData->getArraySize():
        //         neighbourRoleSetlabel = indexData->getNeighbourRoleSetLabel(i);
        //         neighbourRoleSetArray->at(i).visitNeighbourIndividualIds(|neighbourIndiId| {
        //           neighbourPotentiallyInfluenced = false;
        //           neighbourExpansionData = neighbourExpansionDataHash[neighbourIndiId];
        //           if !neighbourExpansionData.isNeighbourPossiblyInfluenced():
        //             if isNominalIndividualNodeAvailable(-neighbourIndiId, ctx): neighbourPotentiallyInfluenced = true;
        //             if !neighbourExpansionData.getRoleSetLabel(): neighbourExpansionData.setRoleSetLabel(neighbourRoleSetlabel);
        //             else if neighbourExpansionData.getRoleSetLabel() != neighbourRoleSetlabel: neighbourPotentiallyInfluenced = true;
        //             if neighbourPotentiallyInfluenced:
        //               visitIndividualsRelevantBackendSynchronisationDataIndividuals(indiNode, true,
        //                   |base, mergedLocNode, mergedDepTP| {
        //                     mergedSyncData = mergedLocNode->getIndividualBackendCacheSynchronisationData(false);
        //                     expandIndividualNeighbourNodeFromBackendCache(indiNode, mergedSyncData->getAssocitaionData(),
        //                         neighbourIndiId, neighbourExpansionData, true, false, nullptr, mergedDepTP, ctx);   // this unit (assoc)
        //                     return true; }, ctx);
        //           else:
        //             mergedLocNode = getLocalizedIndividualBackendCacheSnychronisationData(backendSyncDataIndiNode, ctx);  // u17
        //             expandIndividualNeighbourNodeFromBackendCache(indiNode, mergedLocNode->getAssocitaionData(),
        //                 neighbourIndiId, neighbourExpansionData, true, false, nullptr, backSyncDepTrackPoint, ctx);  // this unit (assoc)
        //           return true; });
        //   return true;
        //
        // Held PORT-PENDING: the backend sync data + association data + role-set
        // neighbour array + the per-neighbour `NeighbourExpansionData` records are
        // not yet ported (W6-DEFER[api]); the
        // `getLocalizedIndividualBackendCacheSnychronisationData` (u17) and
        // `visitIndividualsRelevantBackendSynchronisationDataIndividuals` (merge-unit)
        // siblings and the `…_assoc` expand call (this unit) become live on the
        // reconcile pass.
        let _ = (
            indi_node,
            backend_sync_data_indi_node,
            force_expansion,
            back_sync_dep_track_point,
            calc_alg_context,
        );
        true
    }

    // =======================================================================
    // All-neighbour expansion (cpp 23663–23731).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::expandIndividualAllNeighboursFromBackendCache`.
    /// cpp 23663–23731.
    ///
    /// Schedules expansion of every neighbour of `backendSyncDataIndiNode`: flags the
    /// localized sync data as all-neighbour(-forced) scheduled, marks the node for
    /// non-concept-set/neighbour-label related processing, then for each role-set
    /// neighbour array initialises a neighbour expansion with propagation, and
    /// reactivates the (synchronisation-blocked) same/different related individual
    /// nodes. Finally, if no neighbour-expansion work was actually queued, marks the
    /// all-neighbour(-forced) expansion complete. Always returns `true`.
    pub fn expand_individual_all_neighbours_from_backend_cache(
        &mut self,
        indi_node: NodeId,
        backend_sync_data_indi_node: NodeId,
        force_expansion: bool,
        non_deterministic_consequences_missing_expansion: bool,
        back_sync_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // PORT-PENDING: faithful transcription of cpp 23663–23731. Outline:
        //
        //   locBackendSyncData = getLocalizedIndividualBackendCacheSnychronisationData(backendSyncDataIndiNode, ctx);  // u17
        //   assocData = locBackendSyncData->getAssocitaionData();
        //   locBackendSyncData->setAllNeighbourExpansionScheduled(true);
        //   if forceExpansion: locBackendSyncData->setAllNeighbourForcedExpansionScheduled(true);
        //   markIndividualNodeBackendNonConceptSetRelatedAndNeighbourLabelRelatedProcessing(indiNode, ctx);          // u24
        //
        //   if assocData:
        //     neighbourExpansionDataHash = locBackendSyncData->getNeighbourExpansionDataHash(true);
        //     neighbourRoleSetArray = assocData->getRoleSetNeighbourArray();
        //     if neighbourRoleSetArray:
        //       indexData = neighbourRoleSetArray->getIndexData();
        //       for i in 0..indexData->getArraySize():
        //         neighbourRoleSetlabel = indexData->getNeighbourRoleSetLabel(i);
        //         initializeNeighbourExpansionWithPropagation(indiNode, backendSyncDataIndiNode, locBackendSyncData,
        //             backSyncDepTrackPoint, i, nullptr, false, false, nullptr, forceExpansion, false,
        //             nonDeterministicConsequencesMissingExpansion, ctx);                                            // u27
        //
        //     // reactivate synchronisation-blocked same/different-related individual nodes:
        //     expandRelatedIndividualFunction = |indiSetLabel| {
        //       if indiSetLabel:
        //         mBackendCacheHandler->visitIndividualIdsOfAssociatedIndividualSetLabel(assocData, indiSetLabel,
        //             |neighbourIndiId| {
        //               if neighbourIndiId != indiNode->getNominalIndividual()->getIndividualID():
        //                 neighbourNode = getCorrectedNominalIndividualNode(-neighbourIndiId, ctx);
        //                 if neighbourNode != indiNode:
        //                   locNominalIndi = getLocalizedIndividual(neighbourNode, false, ctx);
        //                   if locNominalIndi->hasProcessingRestrictionFlags(PRFSYNCHRONIZEDBACKENDSUCCESSOREXPANSIONBLOCKED):
        //                     locNominalIndi->clearProcessingRestrictionFlags(PRFSYNCHRONIZEDBACKENDSUCCESSOREXPANSIONBLOCKED);
        //                     addIndividualToProcessingQueue(locNominalIndi, ctx);                                   // core unit
        //               return true; }, ctx); };
        //     expandRelatedIndividualFunction(assocData->getLabelCacheEntry(NONDETERMINISTIC_SAME_INDIVIDUAL_SET_LABEL));
        //     expandRelatedIndividualFunction(assocData->getLabelCacheEntry(NONDETERMINISTIC_DIFFRENT_INDIVIDUAL_SET_LABEL));
        //
        //   if indiNode->hasProcessingRestrictionFlags(PRFSYNCHRONIZEDBACKENDSUCCESSOREXPANSIONBLOCKED):
        //     indiNode->clearProcessingRestrictionFlags(PRFSYNCHRONIZEDBACKENDSUCCESSOREXPANSIONBLOCKED);
        //
        //   if !locBackendSyncData->getBackendNeighbourExpansionQueue(false)
        //      || !locBackendSyncData->getBackendNeighbourExpansionQueue(false)->hasQueuedNeighbourExpansions():
        //     locBackendSyncData->setAllNeighbourExpansion(true);
        //     if forceExpansion: locBackendSyncData->setAllNeighbourForcedExpansion(true);
        //
        //   return true;
        //
        // Held PORT-PENDING: the localized backend sync data + association data +
        // role-set neighbour array + the `CBackendNeighbourExpansionQueue`, all
        // W6-DEFER[api]. The substrate-portable fragments (the
        // `PRFSYNCHRONIZEDBACKENDSUCCESSOREXPANSIONBLOCKED` processing-restriction-flag
        // clears and the `addIndividualToProcessingQueue` re-queue) are interleaved
        // with the deferred cache walk, so the whole method is held PORT-PENDING
        // rather than porting only the flag fragments; they, plus the
        // `markIndividualNodeBackendNonConceptSetRelatedAndNeighbourLabelRelatedProcessing`
        // (u24), `getLocalizedIndividual`/`getCorrectedNominalIndividualNode` (helper
        // units) and `initializeNeighbourExpansionWithPropagation` (u27) siblings,
        // become live on the reconcile pass.
        let _ = (
            indi_node,
            backend_sync_data_indi_node,
            force_expansion,
            non_deterministic_consequences_missing_expansion,
            back_sync_dep_track_point,
            calc_alg_context,
        );
        true
    }

    // =======================================================================
    // Single neighbour-node expansion — neighbourIndiId overload (cpp 23782–23812).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::expandIndividualNeighbourNodeFromBackendCache`
    /// (the `neighbourIndiId` overload). cpp 23782–23812.
    ///
    /// Marks the node for non-concept-set/neighbour-label related processing, tests
    /// for new backend mergings, then over every newly merged only-deterministic
    /// representative individual whose association data is present and whose recorded
    /// neighbour-expansion data is not yet "possibly influenced", delegates to the
    /// `…_assoc` overload. Returns whether any expansion happened.
    pub fn expand_individual_neighbour_node_from_backend_cache(
        &mut self,
        indi_node: NodeId,
        neighbour_indi_id: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // PORT-PENDING: faithful transcription of cpp 23782–23812. Outline:
        //
        //   markIndividualNodeBackendNonConceptSetRelatedAndNeighbourLabelRelatedProcessing(indiNode, ctx);  // u24
        //   testIndividualNodeBackendCacheNewMergings(indiNode, ctx);                                        // merge unit
        //   backendSyncData = indiNode->getIndividualBackendCacheSynchronisationData(false);
        //   expanded = false;
        //   neighbourExpansionDataHash = backendSyncData->getNeighbourExpansionDataHash(false);
        //   visitNewlyMergedOnlyDeterministicRepresentativeIndividualsBackendSynchronisationData(indiNode,
        //       backendSyncData->getMergedIndividualNodeLinker(), nullptr, true,
        //       |base, mergedLocNode, mergedDepTP| {
        //         mergedBackendSyncData = mergedLocNode->getIndividualBackendCacheSynchronisationData(false);
        //         mergedAssocData = mergedBackendSyncData->getAssocitaionData();
        //         if mergedAssocData:
        //           neighbourExpansionData = neighbourExpansionDataHash ? neighbourExpansionDataHash->value(neighbourIndiId) : {};
        //           if !neighbourExpansionData.isNeighbourPossiblyInfluenced():
        //             locBackendSyncData = getLocalizedIndividualBackendCacheSnychronisationData(indiNode, ctx);   // u17
        //             locNeighbourExpansionData = mergedBackendSyncData->getNeighbourExpansionDataHash(true)[neighbourIndiId];
        //             expanded |= expandIndividualNeighbourNodeFromBackendCache(indiNode, mergedAssocData, neighbourIndiId,
        //                 locNeighbourExpansionData, true, true, nullptr, mergedDepTP, ctx);                       // this unit (assoc)
        //         return true; }, ctx);
        //   return expanded;
        //
        // Held PORT-PENDING: the backend sync data + association data + per-neighbour
        // expansion data (W6-DEFER[api]); the
        // `markIndividualNodeBackendNonConceptSetRelatedAndNeighbourLabelRelatedProcessing`
        // (u24), `testIndividualNodeBackendCacheNewMergings` /
        // `visitNewlyMergedOnlyDeterministicRepresentativeIndividualsBackendSynchronisationData`
        // (merge unit), `getLocalizedIndividualBackendCacheSnychronisationData` (u17)
        // siblings and the `…_assoc` recursive call become live on the reconcile pass.
        let _ = (indi_node, neighbour_indi_id, calc_alg_context);
        false
    }

    // =======================================================================
    // Single neighbour-node expansion — assocData overload (cpp 23819–23926).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::expandIndividualNeighbourNodeFromBackendCache`
    /// (the `assocData` + `neighbourExpansionData` + label-expansion-feedback
    /// overload). cpp 23819–23926.
    ///
    /// Integrates the (representative-same-) neighbour individual into the completion
    /// graph from the backend cache: forces a backend-initialised localized nominal
    /// node for it, optionally installs a representative-label-expansion feedback
    /// linker, recursively integrates the node's own nominal-merge predecessor when
    /// the merge dependency is non-deterministic, and for every deterministic
    /// asserted/nominal role to the neighbour creates the missing role link (with the
    /// matching `ROLEASSERTION`/`VALUE` dependency) in the correct direction,
    /// re-queueing the affected node. A non-deterministic link on a backend-expansion
    /// reusing individual schedules an indirect-compatibility re-expansion. Returns
    /// whether any node/link was added.
    ///
    /// KONCLUDE-PORT-NOTE[api]: `assocData` is the opaque
    /// `CBackendRepresentativeMemoryCacheIndividualAssociationData*`; the in/out
    /// `neighbourExpansionData` reference and the `representativeLabelExpansionData`
    /// out double-pointer are opaque `&mut Cint64` slots (W6 Cache subtree).
    pub fn expand_individual_neighbour_node_from_backend_cache_assoc(
        &mut self,
        indi_node: NodeId,
        assoc_data: Cint64,
        neighbour_indi_id: Cint64,
        neighbour_expansion_data: &mut Cint64,
        force_expansion: bool,
        force_processing: bool,
        representative_label_expansion_data: &mut Cint64,
        base_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // PORT-PENDING: faithful transcription of cpp 23819–23926. Outline:
        //   // TODO (Konclude): find a better strategy, e.g., only expand until a
        //   // certain number of individuals, maybe also use the representative cache
        //   // updating adapter.
        //
        //   expanded = false;
        //   neighbourAssData = mBackendCacheHandler->getIndividualAssociationData(neighbourIndiId, ctx);
        //   if !forceExpansion && !isNominalIndividualNodeAvailable(-neighbourIndiId, ctx):
        //     if !neighbourAssData || !neighbourAssData->isCompletelyHandled(): return false;
        //
        //   repNeighbourIndiId = neighbourAssData ? neighbourAssData->getRepresentativeSameIndividualId() : neighbourIndiId;
        //   neighbourExpansionData.setNeighbourPossiblyInfluenced(true);
        //   // add neighbour indi and directly create neighbouring role instantiations:
        //   if !isNominalIndividualNodeAvailable(-repNeighbourIndiId, ctx): expanded = true;
        //   locNominalIndi = getLocalizedForcedBackendInitializedNominalIndividualNode(repNeighbourIndiId, ctx);    // helper unit
        //   markIndividualNodeBackendNonConceptSetRelatedProcessing(locNominalIndi, ctx);                          // u24-sibling
        //
        //   if representativeLabelExpansionData:   // install representative expansion feedback
        //     nominalBackendSyncData = locNominalIndi->getIndividualBackendCacheSynchronisationData(false);
        //     if !nominalBackendSyncData->hasNonConceptSetBackendNeighbourLabelRelatedProcessing():
        //       locNominalBackendSyncData = getLocalizedIndividualBackendCacheSnychronisationData(locNominalIndi, ctx);  // u17
        //       neighbourLabelRepresentativeExpansionLinker = alloc CXLinker<…LabelNeighbourExpansionData*>;
        //       neighbourLabelRepresentativeExpansionLinker->initLinker(*representativeLabelExpansionData);
        //       locNominalBackendSyncData->installNeighbourLabelRepresentativeExpansion(neighbourLabelRepresentativeExpansionLinker);
        //     else: *representativeLabelExpansionData = nullptr;
        //
        //   if locNominalIndi->hasPurgedBlockedProcessingRestrictionFlags(): return false;
        //   if forceProcessing && locNominalIndi->hasProcessingRestrictionFlags(PRFSYNCHRONIZEDBACKENDSUCCESSOREXPANSIONBLOCKED):
        //     locNominalIndi->clearProcessingRestrictionFlags(PRFSYNCHRONIZEDBACKENDSUCCESSOREXPANSIONBLOCKED);
        //     addIndividualToProcessingQueue(locNominalIndi, ctx);                                                 // core unit
        //
        //   nominalConDepTrackPoint = nullptr;
        //   if locNominalIndi->getNominalIndividual() && -repNeighbourIndiId != locNominalIndi->getIndividualNodeID()
        //      && repNeighbourIndiId != locNominalIndi->getNominalIndividual()->getIndividualID()
        //      && locNominalIndi->getIndividualMergingHash(false):
        //     nominalConDepTrackPoint = locNominalIndi->getIndividualMergingHash(false)->value(repNeighbourIndiId).getDependencyTrackPoint();
        //     if !nominalConDepTrackPoint || hasNondeterministicDependency(nominalConDepTrackPoint, ctx):           // dep unit
        //       tmpNeighbourExpData = {};
        //       expanded |= expandIndividualNeighbourNodeFromBackendCache(indiNode, assocData,
        //           locNominalIndi->getNominalIndividual()->getIndividualID(), tmpNeighbourExpData,
        //           forceExpansion, forceProcessing, nullptr, baseDepTrackPoint, ctx);                             // this unit (recursive)
        //
        //   nonDeterministicallyLinked = false;
        //   mBackendCacheHandler->visitRolesToNeigbourInAssociatedNeighbourRoleSetLabel(assocData, neighbourIndiId,
        //       |role, inversed, aboxAsserted, nominalConnection, nondeterministic| {
        //         nonDeterministicallyLinked |= nondeterministic;
        //         if !nondeterministic && (aboxAsserted || nominalConnection):
        //           if !inversed:
        //             if !hasIndividualsLink(indiNode, locNominalIndi, role, true, ctx):                          // helper unit
        //               nextDepTrackPoint = nullptr;
        //               if aboxAsserted: createROLEASSERTIONDependency(nextDepTrackPoint, indiNode, baseDepTrackPoint,
        //                   nominalConDepTrackPoint, role, indiNode->getNominalIndividual(), ctx);                 // dep unit
        //               else if nominalConnection: createVALUEDependency(nextDepTrackPoint, indiNode, nullptr,
        //                   baseDepTrackPoint, nominalConDepTrackPoint, ctx);                                      // dep unit
        //               createNewIndividualsLinksReapplyed(indiNode, locNominalIndi, role->getIndirectSuperRoleList(),
        //                   role, nextDepTrackPoint, true, ctx);                                                   // reapply unit
        //               propagateIndividualNodeModified(locNominalIndi, ctx); addIndividualToProcessingQueue(locNominalIndi, ctx);
        //               expanded = true;
        //           else:  // inversed: link locNominalIndi -> indiNode
        //             if !hasIndividualsLink(locNominalIndi, indiNode, role, true, ctx):
        //               nextDepTrackPoint = nullptr;
        //               if aboxAsserted: createROLEASSERTIONDependency(nextDepTrackPoint, indiNode, baseDepTrackPoint,
        //                   nominalConDepTrackPoint, role, locNominalIndi->getNominalIndividual(), ctx);
        //               else if nominalConnection: createVALUEDependency(nextDepTrackPoint, indiNode, nullptr,
        //                   baseDepTrackPoint, nominalConDepTrackPoint, ctx);
        //               createNewIndividualsLinksReapplyed(locNominalIndi, indiNode, role->getIndirectSuperRoleList(),
        //                   role, nextDepTrackPoint, true, ctx);
        //               propagateIndividualNodeModified(locNominalIndi, ctx); addIndividualToProcessingQueue(locNominalIndi, ctx);
        //               expanded = true;
        //         return true; }, ctx);
        //
        //   if nonDeterministicallyLinked && locNominalIndi->hasPartialProcessingRestrictionFlags(PRFBACKENDEXPANSIONREUSINGINDIVIDUAL)
        //      && !locNominalIndi->isBackendIndirectCompatibilityExpansionQueued():
        //     addIndividualToBackendIndirectCompatibilityExpansionQueue(locNominalIndi, ctx);                      // core unit
        //
        //   return expanded;
        //
        // Held PORT-PENDING: the backend association data + per-neighbour expansion
        // data + the representative-label-expansion linker chain are W6-DEFER[api]
        // (reached through `mBackendCacheHandler`); the role-link creation path itself
        // (`hasIndividualsLink`, `createROLEASSERTIONDependency`/`createVALUEDependency`
        // — dep unit, `createNewIndividualsLinksReapplyed` — reapply unit,
        // `propagateIndividualNodeModified` / `addIndividualToProcessingQueue` /
        // `addIndividualToBackendIndirectCompatibilityExpansionQueue` — core unit,
        // `getLocalizedForcedBackendInitializedNominalIndividualNode` — helper unit,
        // `hasNondeterministicDependency` — dep unit) is gated behind the deferred
        // role-visiting cache walk, so the whole method is held PORT-PENDING; the
        // siblings become live on the reconcile pass.
        let _ = (
            indi_node,
            assoc_data,
            neighbour_indi_id,
            neighbour_expansion_data,
            force_expansion,
            force_processing,
            representative_label_expansion_data,
            base_dep_track_point,
            calc_alg_context,
        );
        false
    }
}
