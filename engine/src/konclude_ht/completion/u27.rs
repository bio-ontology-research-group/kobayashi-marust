//! `completion::u27` — Neighbour / backend-cache node expansion family, batch
//! (port unit #27 of 36).
//!
//! Faithful port of the 12 methods that the manifest (`01-completion-methods.md`,
//! "Unit 27") groups under the representative-memory backend-cache neighbour /
//! indirectly-connected node expansion of Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`.
//! cpp source line ranges (1-based) are noted per method.
//!
//! Methods (manifest order):
//!   * `anlyzeIndiviudalNodesConceptExpansion`                            [6009–6095]
//!   * `expandIndirectlyConnectedIndividuals`                             [23930–23977]
//!   * `canDelayRepresentativeNeighbourExpansion`                         [24645–24679]
//!   * `delayingRepresentativeNeighbourExpansion`                         [24683–24700]
//!   * `ensurePropagationCutLinksToExpandedIndividual`                    [25379–25427]
//!   * `expandDirectlyInfluencedNeighboursWithPropagation`               [25503–25539]
//!   * `ensureBaseLinkExpansion`                                          [25547–25573]
//!   * `initializeNeighbourExpansionWithPropagation`                      [25577–25702]
//!   * `isNeighbourExpansionWithPropagationAllowed`                       [25727–25742]
//!   * `canExpansionPotentiallyInfluenceNeighbourWithPotentialPropagation`[25745–25797]
//!   * `canExpandDirectlyInfluencedNeighbourWithPropagation`              [25801–25845]
//!   * `debugCheckDirectlyInfluencedNeighbourWithPropagationPossible`     [26209–26278]
//!
//! KONCLUDE-PORT-NOTE[ownership]: each method is a member of
//! `CCalculationTableauCompletionTaskHandleAlgorithm`, so it becomes `&mut self`
//! plus the threaded per-thread context `calc_alg_context: &mut
//! CalculationAlgorithmContextBase`. C++ `CIndividualProcessNode*&` out/in-out
//! pointer-references become `&mut NodeId`; a plain `CIndividualProcessNode*`
//! value parameter becomes `NodeId`; `CConcept*` → `ConceptId`, `CRole*` →
//! `RoleId` (resolved against `calc_alg_context.ontology_arenas()`),
//! `CDependencyTrackPoint*` → `TrackPointId`. `bool&` / `cint64&` out-params
//! become `&mut bool` / `&mut Cint64`.
//!
//! Deferral landscape. This unit is the representative-memory backend-cache
//! NEIGHBOUR-EXPANSION engine; like its sibling u24 it bottoms out, end-to-end,
//! in the W6 Cache subtree that is not yet ported:
//!   * `CIndividualNodeRepresentativeMemoryBackendCacheSynchronisationData` (per
//!     node: merged-node linkers, the neighbour-expansion data hashes, the
//!     label neighbour-expansion / representative-expansion delay records, the
//!     `CBackendNeighbourExpansionQueue`) and its localized twin;
//!   * `CBackendRepresentativeMemoryCacheIndividualAssociationData` +
//!     the `CBackendRepresentativeMemoryLabelCacheItem` family + the role-set
//!     neighbour arrays — reached only through `mBackendCacheHandler`
//!     (`self.backend_cache_handler`, a zero-size `Id` stub);
//!   * the `CIndividualNodeAnalizedConceptExpansionData` / `CAnalizedConceptExpansionLinker`
//!     analysed-expansion satellite (method 1) and the dependency-tracking siblings
//!     `isConceptSignatureBlockingCritical` /
//!     `isConceptFromDirectOrPredecessorOrNondeterminismusDependent` /
//!     `getConceptDependenciesToSameIndividualNode` (unit 28);
//!   * the answering-subsystem `CAnsweringPropagationSteeringController` (method 9);
//!   * the sibling drivers `getLocalizedIndividual(BackendCacheSnychronisationData)`,
//!     `getCorrectedMergedIntoIndividualNode`, `testIndividualNodeBackendCacheNewMergings`,
//!     `expandIndividualNeighbourNodeFromBackendCache`, `addIndividualToProcessingQueue`,
//!     `addIndividualToBackendNeighbourExpansionQueue`, the `visit*BackendSynchronisationData`
//!     walkers — all later units / W6.
//!
//! Following the porting convention (see u24/u09), the genuinely substrate-portable
//! methods and sub-structures are ported in full against the ported concept model:
//!   * `expandDirectlyInfluencedNeighboursWithPropagation` — the
//!     specialized-automat operand RECURSION and the operator-flag dispatch guard
//!     (`CConceptOperator::hasPartialOperatorCodeFlag`) that decide the return
//!     value; only the inner role-keyed backend visitation side effect is deferred;
//!   * `isNeighbourExpansionWithPropagationAllowed` — the config + variable gate
//!     (the answering steering refinement is W6-deferred ⇒ allow, the no-adapter
//!     default);
//!   * `canExpansionPotentiallyInfluenceNeighbourWithPotentialPropagation` /
//!     `canExpandDirectlyInfluencedNeighbourWithPropagation` — the operator-flag
//!     influence test, with the backend association-data lookup deferred to the
//!     genuine null-cache path (`!neighbourAssData ⇒ conservatively influenced`),
//!     and the deeper label-membership operand scan transcribed faithfully (it is
//!     reached only once the backend association data is ported).
//! The remaining backend-driven methods keep their faithful signature and a
//! structural transcription of the C++ as `// PORT-PENDING` so a later wave fills
//! them without re-reading the source. Logic is documented, never silently dropped.

#![allow(
    unused_variables,
    unused_mut,
    unused_assignments,
    dead_code,
    clippy::collapsible_if,
    clippy::collapsible_else_if,
    clippy::nonminimal_bool,
    clippy::needless_range_loop
)]

use super::super::model::op::{
    CCAQAND, CCBRANCHAQAND, CCF_ATLEAST, CCF_ATMOST, CCFS_ALL_AQALL_TYPE, CCFS_SOME_TYPE,
    CCIMPLAQAND,
};
use super::super::model::substrate::{Cint64, Id, INVALID};
use super::super::model::{ConceptId, RoleId};
use super::super::process::{NodeId, TrackPointId};
use super::context::CalculationAlgorithmContextBase;

impl super::algorithm::CompletionTaskHandleAlgorithm {
    // =======================================================================
    // Analysed-concept-expansion collection (cpp 6009–6095).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::anlyzeIndiviudalNodesConceptExpansion`.
    /// cpp 6009–6095. (Name keeps the C++ misspelling as the diff anchor.)
    ///
    /// Walks the node's newly added concept descriptors (head→`lastAnalyzedConDes`)
    /// and partitions them into analysed deterministic expansions (with their
    /// same-node dependency linkers) vs. non-deterministic expansions, caching the
    /// result on the node's `CIndividualNodeAnalizedConceptExpansionData`; flags
    /// signature-blocking-critical concepts as an invalid blocker. Returns true iff
    /// the analysis was (re)done.
    ///
    /// PORT-PENDING (cpp 6009–6095). Substrate gap: the analysed-expansion satellite
    /// (`CIndividualNodeAnalizedConceptExpansionData` / `CAnalizedConceptExpansionLinker`)
    /// is not yet ported, and the partitioning calls the unit-28 dependency-tracking
    /// siblings. Faithful outline:
    ///
    ///   conSet = individualNode->getReapplyConceptLabelSet(false);            // ported satellite
    ///   if !conSet: return false;
    ///   lastAddedConDes = conSet->getAddingSortedConceptDescriptionLinker();
    ///   anlConExpData = individualNode->getAnalizedConceptExpansionData(false); // W6-DEFER[api]
    ///   update = if anlConExpData { !invalidBlocker && lastAdded != lastAnalyzed }
    ///            else { lastAddedConDes != null };
    ///   if update:
    ///     conSignature = conSet->getConceptSignatureValue(); conceptCount = conSet->getConceptCount();
    ///     individualNode = getLocalizedIndividual(individualNode, false, ctx);   // W3-DEFER[api]
    ///     locAnlConExpData = individualNode->getAnalizedConceptExpansionData(true);
    ///     invalidBlocking = locAnlConExpData->isInvalidBlocker();
    ///     for conDesIt = lastAddedConDes; conDesIt && conDesIt != lastAnalizedConDes && !invalidBlocking:
    ///       depTrackPoint = conDes->getDependencyTrackPoint();
    ///       if isConceptSignatureBlockingCritical(individualNode, conDes, depTrackPoint, ctx):   // unit 28
    ///         invalidBlocking = true;
    ///       else if isConceptFromDirectOrPredecessorOrNondeterminismusDependent(...,&directDep,ctx): // unit 28
    ///         if !directDep: nonDetConLinker += conDes;
    ///       else if getConceptDependenciesToSameIndividualNode(...,depLinker,ctx):                 // unit 28
    ///         firstAnaConExpLinker += AnalizedConceptExpansion(depLinker, conDes);
    ///       else: nonDetConLinker += conDes;
    ///       conDesIt = conDesIt->getNextConceptDesciptor(); --currAnalizingCount;
    ///     locAnlConExpData->addAnalizedConceptExpansionLinker(firstAnaConExpLinker);
    ///     locAnlConExpData->addAnalysedNonDeterministicConceptExpansionLinker(nonDetConLinker);
    ///     locAnlConExpData->setInvalidBlocker(invalidBlocking);
    ///     locAnlConExpData->setLastConceptDescriptor(lastAddedConDes);
    ///     locAnlConExpData->setLastConceptSignature(conSignature);
    ///     locAnlConExpData->setLastConceptCount(conceptCount);
    ///     return true;
    ///   return false;
    pub fn anlyze_indiviudal_nodes_concept_expansion(
        &mut self,
        individual_node: &mut NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W6-DEFER[api]/W3-DEFER[api]: analysed-expansion satellite + unit-28
        // dependency-tracking siblings unported; faithful default (no analysis done).
        false
    }

    // =======================================================================
    // Indirectly-connected (nominal) individual expansion (cpp 23930–23977).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::expandIndirectlyConnectedIndividuals`.
    /// cpp 23930–23977.
    ///
    /// Activates indirectly-nominal-connected individuals from the backend cache
    /// when a cardinality restriction reaches a newly generated nominal or the
    /// concept label changed / is non-deterministic. Returns whether anything was
    /// expanded.
    ///
    /// PORT-PENDING (cpp 23930–23977). End-to-end backend cache. Faithful outline:
    ///   expanded = false;
    ///   backendSyncData    = indiNode->getIndividualBackendCacheSynchronisationData(false);
    ///   locBackendSyncData = indiNode->getIndividualBackendCacheSynchronisationData(true);
    ///   required = !checkExpansionRequired
    ///              || testIndividualNodeBackendCacheNominalIndirectConnectionBlockingCritical(indiNode,ctx);
    ///   if required:
    ///     testIndividualNodeBackendCacheNewMergings(indiNode, ctx);                  // unit 15/merge
    ///     backendSyncData = indiNode->getIndividualBackendCacheSynchronisationData(false);
    ///     locBackendSyncData = getLocalizedIndividualBackendCacheSnychronisationData(indiNode, ctx);
    ///     locBackendSyncData->setNominalIndirectConnectionIndividualExpanded(true);
    ///     visitNewlyMergedOnlyDeterministicRepresentativeIndividualsBackendSynchronisationData(
    ///         indiNode, mergedLinker, lastIndirectlyHandledMergedLinker, !hasExpanded,
    ///         |base, locNode, depTP| {
    ///             if !locNode.backendSyncData.hasNominalIndirectConnectionIndividualExpanded():
    ///                 locNode = getLocalizedIndividual(locNode, true, ctx);
    ///                 mBackendCacheHandler->visitNominalIndirectlyConnectedIndividualIds(
    ///                     assocData, nominalId, |connIndiId| {
    ///                         expanded = true;
    ///                         locConn = getLocalizedForcedBackendInitializedNominalIndividualNode(connIndiId,ctx);
    ///                         markIndividualNodeBackendNonConceptSetRelatedAndNeighbourLabelRelatedProcessing(locConn,ctx);
    ///                         if locConn.hasPartialProcessingRestrictionFlags(PRFSYNCHRONIZEDBACKENDSUCCESSOREXPANSIONBLOCKED):
    ///                             locConn.clearProcessingRestrictionFlags(...BLOCKED);
    ///                             addIndividualToProcessingQueue(locConn, ctx);
    ///                     });
    ///                 locNode.backendSyncData.setNominalIndirectConnectionIndividualExpanded(true);
    ///         });
    ///     locBackendSyncData->setLastIndirectlyConnectedNominalIndividualsHandledMergedNodeLinker(
    ///         backendSyncData->getMergedIndividualNodeLinker());
    ///   return expanded;
    pub fn expand_indirectly_connected_individuals(
        &mut self,
        indi_node: NodeId,
        check_expansion_required: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W6-DEFER[api]: representative-memory backend cache synchronisation data +
        // mBackendCacheHandler not yet ported; faithful default (nothing expanded).
        false
    }

    // =======================================================================
    // Propagation-cut link establishment (cpp 25379–25427).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::ensurePropagationCutLinksToExpandedIndividual`.
    /// cpp 25379–25427.
    ///
    /// Ensures the propagation-cut individual node carries the backend-cache link to
    /// a (possibly directly-influenced) neighbour, expanding that neighbour from the
    /// cache and queuing the base node for processing. Returns whether anything was
    /// expanded.
    ///
    /// PORT-PENDING (cpp 25379–25427). Backend cache + several siblings (merge /
    /// expand). Faithful outline:
    ///   baseIndiNode = getLocalizedIndividual(propCutIndiNode, true, ctx);
    ///   mergedIntoBaseIndiNode = getLocalizedIndividual(getCorrectedMergedIntoIndividualNode(baseIndiNode,ctx), true, ctx);
    ///   backendSyncDataIndiNode = backendNeighbourExpDataLinker ? linker.getBackendSyncDataIndividualNode() : propCutIndiNode;
    ///   locHandlingBackendSyncData = locPropCutIndiBackendSyncData (or relocalized if a different node);
    ///   assocData = locHandlingBackendSyncData->getAssocitaionData();
    ///   backSyncDepTrackPoint = ctx->getBaseDependencyNode()->getContinueDependencyTrackPoint();
    ///   neighbourExpansionData = (*locBackendSyncData->getNeighbourExpansionDataHash(true))[neighbourIndiId];
    ///   if !neighbourExpansionData.isNeighbourPossiblyInfluenced():
    ///     neighbourAssData = mBackendCacheHandler->getIndividualAssociationData(neighbourIndiId, ctx);
    ///     expandable = true; forceExpansion = linker ? linker.isForceExpansion() : true;
    ///     if linker && linker.getConcept():
    ///       expandable = canExpandDirectlyInfluencedNeighbourWithPropagation(mergedIntoBaseIndiNode, locHandlingBackendSyncData,
    ///                       backSyncDepTrackPoint, linker.getConcept(), linker.getConceptNegation(), linker.getConceptNondeterministic(),
    ///                       assocData, neighbourExpansionData, neighbourIndiId, neighbourAssData, ctx);
    ///       forceExpansion = true;
    ///     if expandable:
    ///       expanded = expandIndividualNeighbourNodeFromBackendCache(mergedIntoBaseIndiNode, assocData, neighbourIndiId,
    ///                     neighbourExpansionData, forceExpansion, forceExpansion, null, backSyncDepTrackPoint, ctx);
    ///   if expanded: addIndividualToProcessingQueue(mergedIntoBaseIndiNode, ctx);
    ///   return expanded;
    pub fn ensure_propagation_cut_links_to_expanded_individual(
        &mut self,
        prop_cut_indi_node: NodeId,
        loc_prop_cut_indi_backend_sync_data: Cint64,
        backend_neighbour_exp_data_linker: Cint64,
        neighbour_indi_id: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W6-DEFER[api]: backend cache + merge/expand siblings unported; faithful
        // default (nothing expanded).
        false
    }

    // =======================================================================
    // Directly-influenced neighbour expansion with propagation (cpp 25503–25539).
    // PORTED: operand recursion + operator-flag return-value dispatch.
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::expandDirectlyInfluencedNeighboursWithPropagation`.
    /// cpp 25503–25539.
    ///
    /// For a (possibly compound) concept, recurses through specialized-automat AND
    /// operands and, for a critical `∀`/`≤` (or negated `∃`/`≥`) operator over a
    /// role, initialises neighbour expansion with propagation for every neighbour
    /// array of that role. Returns true iff `concept` is a neighbour-influencing
    /// operator (the contract used by `ensurePropagationCutLinksToExpandedIndividual`
    /// et al.).
    ///
    /// The specialized-automat operand RECURSION and the operator-flag return-value
    /// guard are ported in full against the concept model; only the inner
    /// role-keyed backend visitation that drives `initializeNeighbourExpansionWithPropagation`
    /// per neighbour array id is W6-deferred (the side effect, not the return value).
    pub fn expand_directly_influenced_neighbours_with_propagation(
        &mut self,
        concept: ConceptId,
        con_negation: bool,
        nondeterministic: bool,
        indi_node: NodeId,
        assoc_data: Cint64,
        loc_backend_sync_data_indi_node: NodeId,
        loc_backend_sync_data: Cint64,
        back_sync_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let con_operator = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_concept_operator();
        let role: RoleId = calc_alg_context.ontology_arenas().concept(concept).get_role();
        let op_code: Cint64 = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operator_code();
        let op_concepts = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operand_list()
            .to_vec();

        if self.conf_specialized_automate_rules
            && (op_code == CCAQAND || op_code == CCIMPLAQAND || op_code == CCBRANCHAQAND)
        {
            for op_link in op_concepts.iter() {
                let op_con: ConceptId = op_link.target;
                let op_con_neg: bool = op_link.negated;
                self.expand_directly_influenced_neighbours_with_propagation(
                    op_con,
                    op_con_neg,
                    nondeterministic,
                    indi_node,
                    assoc_data,
                    loc_backend_sync_data_indi_node,
                    loc_backend_sync_data,
                    back_sync_dep_track_point,
                    calc_alg_context,
                );
            }
            return true;
        } else if !con_negation
            && con_operator.has_partial_operator_code_flag(CCFS_ALL_AQALL_TYPE | CCF_ATMOST)
            || con_negation
                && con_operator.has_partial_operator_code_flag(CCFS_SOME_TYPE | CCF_ATLEAST)
        {
            // TODO (Konclude): verify cardinality is indeed critical
            //
            // W6-DEFER[api] (cpp 25520–25534): the neighbour visitation that drives
            // the side effect is backend-cache (W6). Faithful outline:
            //   if conOperator.hasFlag(CCF_ATMOST|CCF_ATLEAST)
            //      || mBackendCacheHandler->hasRoleInAssociatedCombinedNeigbourRoleSetLabel(
            //             assocData, DETERMINISTIC_COMBINED_NEIGHBOUR_INSTANTIATED_ROLE_SET_LABEL, role, false)
            //      || mBackendCacheHandler->hasRoleInAssociatedCombinedNeigbourRoleSetLabel(
            //             assocData, NONDETERMINISTIC_COMBINED_NEIGHBOUR_INSTANTIATED_ROLE_SET_LABEL, role, false):
            //        if role:
            //           mBackendCacheHandler->visitNeighbourArrayIdsForRole(assocData, role,
            //              |arrayId, neighbourRoleSetLabel, nondet| {
            //                 self.initialize_neighbour_expansion_with_propagation(
            //                     indiNode, locBackendSyncDataIndiNode, locBackendSyncData,
            //                     backSyncDepTrackPoint, arrayId, concept, conNegation, nondet,
            //                     role, true, false, false, ctx);
            //              }, false, ctx);
            // The return contract (true for a neighbour-influencing operator) holds
            // regardless of whether the (deferred) visitation fires.
            let _ = (
                role,
                assoc_data,
                loc_backend_sync_data,
                loc_backend_sync_data_indi_node,
                back_sync_dep_track_point,
                nondeterministic,
                indi_node,
            );
            return true;
        }

        false
    }

    // =======================================================================
    // Base-link expansion (cpp 25547–25573).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::ensureBaseLinkExpansion`.
    /// cpp 25547–25573.
    ///
    /// Expands the base backend-cache link between `indiNode` and the neighbour
    /// identified by `neighbourNodeId`, choosing the forward or reverse direction by
    /// whether a neighbour role-set label exists. Returns whether anything expanded.
    ///
    /// PORT-PENDING (cpp 25547–25573). End-to-end backend cache. Faithful outline:
    ///   baseDepTrackPoint = ctx->getBaseDependencyNode()->getContinueDependencyTrackPoint();
    ///   indiNodeBackendSyncData = getLocalizedIndividualBackendCacheSnychronisationData(indiNode, ctx);
    ///   indiNodeAssocData = indiNodeBackendSyncData->getAssocitaionData();
    ///   if indiNodeAssocData:
    ///     neighbourLabel = indiNodeAssocData->getNeighbourRoleSetHash()?.getNeighbourRoleSetLabel(neighbourNodeId);
    ///     if neighbourLabel:
    ///       expanded = expandIndividualNeighbourNodeFromBackendCache(indiNode, indiNodeAssocData, neighbourNodeId,
    ///                     tmpExpansionData, true, false, null, baseDepTrackPoint, ctx);
    ///     else:
    ///       neighbourIndiNode = getLocalizedIndividual(-neighbourNodeId, ctx);
    ///       neighbourAssocData = getLocalizedIndividualBackendCacheSnychronisationData(neighbourIndiNode, ctx)->getAssocitaionData();
    ///       expanded = expandIndividualNeighbourNodeFromBackendCache(neighbourIndiNode, neighbourAssocData,
    ///                     expIndiNode->getNominalIndividual()->getIndividualID(), tmpExpansionData, true, false, null, baseDepTrackPoint, ctx);
    ///   return expanded;
    pub fn ensure_base_link_expansion(
        &mut self,
        exp_indi_node: NodeId,
        indi_node: NodeId,
        neighbour_node_id: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W6-DEFER[api]: backend cache association data + expand sibling unported;
        // faithful default (nothing expanded).
        false
    }

    // =======================================================================
    // Neighbour-expansion initialisation with propagation (cpp 25577–25702).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::initializeNeighbourExpansionWithPropagation`.
    /// cpp 25577–25702.
    ///
    /// Iterates the neighbour individuals of one role neighbour-array (from a saved
    /// cursor), and for each neighbour the expansion can potentially influence,
    /// expands it directly from the backend cache (subject to the direct-expansion
    /// count limit / critical-reduction policy), queuing the remainder into the
    /// node's backend neighbour-expansion queue. Always returns true.
    ///
    /// PORT-PENDING (cpp 25577–25702). The substrate-portable head is noted; the
    /// body is driven by the backend cache neighbour-array iterator. Faithful outline:
    ///   markIndividualNodeBackendNonConceptSetRelatedAndNeighbourLabelRelatedProcessing(indiNode, ctx); // unit 24
    ///   assocData = locBackendSyncData->getAssocitaionData();
    ///   // [PORTABLE config head]
    ///   forceAllDirectExpansion = mConfAtmostAllDirectBackendNeighbourExpansion && concept
    ///       && concept.conceptOperator.hasFlag(CCF_ATMOST|CCF_ATLEAST);
    ///   minBackendNeighbourDirectExpansionCount = mOptMinBackendNeighbourDirectExpansionCount;
    ///   expandedCount = ctx->getUsedProcessingDataBox()->getBackendCacheIntegratedIndividualNodeCount();
    ///   if expandedCount > mOptCriticalBackendNeighbourTotalExpansionCount:
    ///     if mOptMinDirectNeighbourExpansionOverCriticalReductionSize > 0:
    ///       minBackendNeighbourDirectExpansionCount = max(min - (expandedCount-critical)/reductionSize, 0);
    ///     else if < 0: minBackendNeighbourDirectExpansionCount = 0;
    ///   // [BACKEND iterator]
    ///   mBackendCacheHandler->visitNeighbourIndividualIdsForNeighbourArrayIdFromCursor(assocData, arrayId,
    ///       |neighbourIndiId, neighbourRoleSetLabel, nondet, nextCursor| {
    ///         if canExpansionPotentiallyInfluenceNeighbourWithPotentialPropagation(indiNode, concept, conNegation, nondet, assocData, neighbourIndiId, ctx):
    ///           neighbourExpansionData = (*neighbourExpansionDataHash)[neighbourIndiId];
    ///           if !neighbourExpansionData.isNeighbourPossiblyInfluenced():
    ///             neighbourAssData = mBackendCacheHandler->getIndividualAssociationData(neighbourIndiId, ctx);
    ///             if !forceAllDirectExpansion && mOptLimitBackendNeighbourExpansion && currentDirect >= minDirect
    ///                && (!mConfAllProblematicBackendNeighbourDirectExpansion || !neighbourAssData || !neighbourAssData->hasProblematicLevel()):
    ///               maxDirectNeighbourExpansionReached = true;
    ///             if !maxDirectNeighbourExpansionReached:
    ///               expandable = concept ? canExpandDirectlyInfluencedNeighbourWithPropagation(...) : true;
    ///               if nonDeterministicConsequencesMissingExpansion: expandable = (cardinality ext || nondet elements);
    ///               if expandable:
    ///                 if indiNode != locBackendSyncDataIndiNode && (!backSyncDepTrackPoint || hasNondeterministicDependency(backSyncDepTrackPoint, ctx)):
    ///                   expanded |= ensureBaseLinkExpansion(indiNode, indiNode, neighbourIndiId, ctx);
    ///                 expanded |= expandIndividualNeighbourNodeFromBackendCache(indiNode, assocData, neighbourIndiId, neighbourExpansionData, forceExpansion, forceExpansion, null, backSyncDepTrackPoint, ctx);
    ///               if expanded: ctx->...->getBackendNeighbourExpansionControllingData(true)->incExpandedNeighbourLinkCount(); ++currentDirect;
    ///             else:
    ///               // queue the remainder
    ///               expQueueData = new CBackendNeighbourExpansionQueueDataLinker(arrayId, role, concept, ...);
    ///               locBackendSyncData->getBackendNeighbourExpansionQueue(true)->addNeighbourExpansionQueueDataLinker(expQueueData, false);
    ///               addIndividualToBackendNeighbourExpansionQueue(locBackendSyncDataIndiNode, ctx);
    ///       }, lastCursor, false, ctx);
    ///   return true;
    pub fn initialize_neighbour_expansion_with_propagation(
        &mut self,
        indi_node: NodeId,
        loc_backend_sync_data_indi_node: NodeId,
        loc_backend_sync_data: Cint64,
        back_sync_dep_track_point: TrackPointId,
        array_id: Cint64,
        concept: ConceptId,
        con_negation: bool,
        nondeterministic: bool,
        role: RoleId,
        force_expansion: bool,
        prop_cut_expansion: bool,
        non_deterministic_consequences_missing_expansion: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W6-DEFER[api]: backend cache neighbour-array iterator + expansion queue
        // unported; the C++ always returns true after driving the (deferred) side
        // effects — faithfully reproduced.
        true
    }

    // =======================================================================
    // Neighbour-expansion propagation gate (cpp 25727–25742). PORTED.
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::isNeighbourExpansionWithPropagationAllowed`.
    /// cpp 25727–25742.
    ///
    /// When variable-binding-steered backend neighbour expansion is configured and
    /// the concept carries a destination variable, defers to the answering
    /// propagation-steering controller to decide whether this neighbour may receive
    /// the binding. Otherwise (the default consistency/classification path) allow.
    pub fn is_neighbour_expansion_with_propagation_allowed(
        &mut self,
        indi_node: NodeId,
        concept: ConceptId,
        con_negation: bool,
        neighbour_indi_id: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        if self.conf_variable_binding_steering_backend_neighbour_expansion
            && calc_alg_context
                .ontology_arenas()
                .concept(concept)
                .get_variable()
                .is_some()
        {
            // W6-DEFER[api] (cpp 25729–25738): getPropagationSteeringController bottoms
            // out in the satisfiable-task answerer binding-propagation adapter (the
            // answering subsystem, not yet ported). With no adapter the C++ controller
            // is null and the `isPreparationBinding{AllIndividuals,NominalIndividual}`
            // refinement is skipped, so the method falls through to allow. Faithful to
            // the no-answering-adapter default (consistency / classification tests).
            //
            // PORT-PENDING: when the answering subsystem lands, resolve
            //   controller = getPropagationSteeringController(ctx);
            //   if controller:
            //     destVar = concept->getVariable();
            //     allow = controller->isPreparationBindingAllIndividuals(destVar)
            //          || controller->isPreparationBindingNominalIndividual(destVar, neighbourIndiId);
            //     if !allow: return false;
            let _ = (indi_node, con_negation, neighbour_indi_id);
        }
        true
    }

    // =======================================================================
    // Potential-influence test (cpp 25745–25797). PORTED (null-cache path) +
    // transcribed deeper operand scan.
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::canExpansionPotentiallyInfluenceNeighbourWithPotentialPropagation`.
    /// cpp 25745–25797.
    ///
    /// Decides whether expanding `concept` on `indiNode` can potentially influence
    /// the neighbour `neighbourIndiId`: a null concept always can; otherwise the
    /// decision is by operator family (`¬value` / unqualified `≤`/`≥` always
    /// influence; qualified `∀`/`≤`/`∃` influence only if an operand is not already
    /// in the neighbour's cached full-concept-set label).
    ///
    /// The concept-model operator-flag dispatch is ported in full. The backend
    /// association-data lookup (`mBackendCacheHandler->getIndividualAssociationData`)
    /// is W6-deferred to the genuine null-cache path: with no association data the
    /// neighbour is conservatively assumed potentially influenced (sound
    /// over-approximation, the C++ `!neighbourAssData` branch). The deeper
    /// label-membership operand scan (reached only with association data present) is
    /// transcribed faithfully for the reconcile wave.
    pub fn can_expansion_potentially_influence_neighbour_with_potential_propagation(
        &mut self,
        indi_node: NodeId,
        concept: ConceptId,
        con_negation: bool,
        nondeterministic: bool,
        ass_data: Cint64,
        neighbour_indi_id: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        if concept == Id::NONE {
            return true;
        }

        let con_operator = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_concept_operator();

        if self.is_neighbour_expansion_with_propagation_allowed(
            indi_node,
            concept,
            con_negation,
            neighbour_indi_id,
            calc_alg_context,
        ) {
            let mut neighbour_potentially_influenced = false;

            // W6-DEFER[api]: mBackendCacheHandler->getIndividualAssociationData(
            //   neighbourIndiId, false, ctx) is backend cache (W6); deferred → null.
            let neighbour_ass_data: Cint64 = INVALID;
            if neighbour_ass_data == INVALID {
                neighbour_potentially_influenced = true;

                // mConfExpandDeterministicMergedHandledNeighbours must be true,
                // otherwise the cache may be incomplete (Konclude comment).
            } else if self.conf_expand_deterministic_merged_handled_neighbours
            /* W6-DEFER[api]: || !neighbourAssData->hasDeterministicSameIndividualMerging() */
            {
                // PORT-PENDING (cpp 25762–25787): the operand scan needs the backend
                // label predicate `mBackendCacheHandler->hasConceptInAssociatedFullConceptSetLabel`.
                // Faithful transcription:
                //   opConLinker = concept->getOperandList();
                //   if conNegation && conOperator.hasFlag(CCF_VALUE): influenced = true;
                //   if !influenced && !opConLinker && conOperator.hasFlag(CCF_ATMOST|CCF_ATLEAST): influenced = true;
                //   if !influenced && opConLinker && conOperator.hasFlag(CCF_ATMOST|CCF_ATLEAST|CCFS_ALL_AQALL_TYPE|CCFS_SOME_TYPE):
                //     for opLink in opConLinker (until influenced):
                //       opConceptTestingNegation = opLink.negated;
                //       if conOperator.hasFlag(CCF_ATMOST|CCF_ATLEAST): testNeg = !testNeg;
                //       if conNegation && conOperator.hasFlag(CCFS_ALL_AQALL_TYPE|CCFS_SOME_TYPE): testNeg = !testNeg;
                //       if !mBackendCacheHandler->hasConceptInAssociatedFullConceptSetLabel(
                //              neighbourAssData, FULL_CONCEPT_SET_LABEL, opLink.target, testNeg, true, ctx):
                //         influenced = true;
                //   if !influenced && !opConLinker && conOperator.hasFlag(CCF_ATMOST|CCF_ATLEAST): influenced = true;
                let _ = (con_operator, con_negation, nondeterministic, ass_data);
            }

            if neighbour_potentially_influenced {
                return true;
            }
        }
        false
    }

    // =======================================================================
    // Direct-influence expansion test (cpp 25801–25845). PORTED (null-cache path)
    // + transcribed deeper operand scan.
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::canExpandDirectlyInfluencedNeighbourWithPropagation`.
    /// cpp 25801–25845.
    ///
    /// As `canExpansionPotentiallyInfluence…` but for an already-located neighbour
    /// (`neighbourAssData` passed in), additionally requiring the operand to be
    /// missing under non-deterministic membership when `nondeterministic`. The
    /// operator-flag dispatch is ported; `neighbour_ass_data` arrives W6-deferred
    /// (null) from the callers in this port state, so the conservative
    /// `!neighbourAssData ⇒ influenced` path is taken; the deeper label scan is
    /// transcribed faithfully.
    pub fn can_expand_directly_influenced_neighbour_with_propagation(
        &mut self,
        indi_node: NodeId,
        loc_backend_sync_data: Cint64,
        back_sync_dep_track_point: TrackPointId,
        concept: ConceptId,
        con_negation: bool,
        nondeterministic: bool,
        ass_data: Cint64,
        neighbour_expansion_data: Cint64,
        neighbour_indi_id: Cint64,
        neighbour_ass_data: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let con_operator = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_concept_operator();

        if self.is_neighbour_expansion_with_propagation_allowed(
            indi_node,
            concept,
            con_negation,
            neighbour_indi_id,
            calc_alg_context,
        ) {
            let mut neighbour_potentially_influenced = false;

            // `neighbour_ass_data` is the backend association data (Cint64); W6-deferred
            // to null by the callers in this port state ⇒ conservative influence.
            if neighbour_ass_data == INVALID {
                neighbour_potentially_influenced = true;
            } else {
                // PORT-PENDING (cpp 25810–25838): operand scan needs the backend label
                // predicate `mBackendCacheHandler->hasConceptInAssociatedFullConceptSetLabel`.
                // Faithful transcription:
                //   opConLinker = concept->getOperandList();
                //   if conNegation && conOperator.hasFlag(CCF_VALUE): influenced = true;
                //   if !influenced && !opConLinker && conOperator.hasFlag(CCF_ATMOST|CCF_ATLEAST): influenced = true;
                //   if !influenced && opConLinker && conOperator.hasFlag(CCF_ATMOST|CCF_ATLEAST|CCFS_ALL_AQALL_TYPE|CCFS_SOME_TYPE):
                //     for opLink (until influenced):
                //       testNeg = opLink.negated;
                //       if conOperator.hasFlag(CCF_ATMOST|CCF_ATLEAST): testNeg = !testNeg;
                //       if conNegation && conOperator.hasFlag(CCFS_ALL_AQALL_TYPE|CCFS_SOME_TYPE): testNeg = !testNeg;
                //       if !backend.hasConceptInAssociatedFullConceptSetLabel(neighbourAssData, FULL_CONCEPT_SET_LABEL, opLink.target, testNeg, true, ctx)
                //          || (nondeterministic && !backend.hasConceptInAssociatedFullConceptSetLabel(..., testNeg, false, ctx)):
                //         influenced = true;
                //   if !influenced && !opConLinker && conOperator.hasFlag(CCF_ATMOST|CCF_ATLEAST): influenced = true;
                let _ = (
                    con_operator,
                    con_negation,
                    nondeterministic,
                    ass_data,
                    loc_backend_sync_data,
                    back_sync_dep_track_point,
                    neighbour_expansion_data,
                );
            }

            if neighbour_potentially_influenced {
                return true;
            }
        }
        false
    }

    // =======================================================================
    // Debug direct-influence possibility check (cpp 26209–26278).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::debugCheckDirectlyInfluencedNeighbourWithPropagationPossible`.
    /// cpp 26209–26278.
    ///
    /// Debug-only mirror of `expandDirectlyInfluencedNeighboursWithPropagation` that,
    /// instead of expanding, returns whether SOME neighbour of the critical role
    /// could be potentially influenced (used in assertions). Recurses through the
    /// specialized-automat operands.
    ///
    /// PORT-PENDING (cpp 26209–26278). The operand recursion + operator-flag guard
    /// are portable, but the per-neighbour influence test bottoms out in the backend
    /// label predicate; as a debug-only assertion helper it is kept as a faithful
    /// transcription. Outline:
    ///   if mConfSpecializedAutomateRules && opCode in {CCAQAND,CCIMPLAQAND,CCBRANCHAQAND}:
    ///     for op in operands: result |= debugCheck...(op, op.negated, indiNode, assocData, locBackendSyncData, ctx);
    ///   else if neighbour-influencing operator guard (as in expandDirectly...):
    ///     if conOperator.hasFlag(CCF_ATMOST|CCF_ATLEAST)
    ///        || backend.hasRoleInAssociatedCombinedNeigbourRoleSetLabel(DET..., role)
    ///        || backend.hasRoleInAssociatedCombinedNeigbourRoleSetLabel(NONDET..., role):
    ///        if role:
    ///          backend.visitNeighbourIndividualIdsForRole(assocData, role, |neighbourIndiId, ...| {
    ///            // same operand/label influence test as canExpandDirectly...,
    ///            // returns false (stops) and sets result on the first influenced neighbour
    ///          });
    ///   return someNeighbourPotentiallyInfluenced;
    pub fn debug_check_directly_influenced_neighbour_with_propagation_possible(
        &mut self,
        concept: ConceptId,
        con_negation: bool,
        indi_node: NodeId,
        assoc_data: Cint64,
        loc_backend_sync_data: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W6-DEFER[api]: debug-only; the per-neighbour influence test needs the
        // backend label predicate (W6). Faithful default (no neighbour influenced).
        false
    }
}
