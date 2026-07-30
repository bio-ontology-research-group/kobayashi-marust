//! `completion::u03` — completion port unit #3 (Core processing loop / driver).
//!
//! Ports 15 methods of Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`
//! (see `manifest/01-completion-methods.md`, "Unit 3"):
//!   - `initialNodeInitialize`                              [cpp 8720-9038]
//!   - `individualNodeInitializing`                         [cpp 9061-9169]
//!   - `individualNodeConclusion`                           [cpp 9480-9494]
//!   - `tableauRuleProcessing`                              [cpp 9496-9519]
//!   - `tableauRuleChoice`                                  [cpp 9522-9549]
//!   - `initializeORProcessing`                             [cpp 16396-16430]
//!   - `planORProcessing`                                   [cpp 16493-16664]
//!   - `prepareBranchedTaskProcessing`                      [cpp 17201-17203]
//!   - `getLinkProcessingRestriction`                       [cpp 17286-17294]
//!   - `propagateProcessingRestrictionToAncestor`           [cpp 19762-19764]
//!   - `propagateAddingProcessingRestrictionToAncestor`     [cpp 19767-19778]
//!   - `propagateProcessingRestrictionToSuccessors`         [cpp 19783-19785]
//!   - `propagateAddingProcessingRestrictionToSuccessors`   [cpp 19810-19827]
//!   - `propagateClearingProcessingRestrictionToSuccessors` [cpp 19831-19848]
//!   - `propagateIndividualProcessedAndReactivate`          [cpp 19887-19899]
//!
//! KONCLUDE-PORT-NOTE[ownership]: every raw `CIndividualProcessNode*&` /
//! `CConceptProcessDescriptor*` / `CConcept*` becomes its arena id (`NodeId` /
//! `ConProcDescId` / `ConceptId`); the `CCalculationAlgorithmContextBase*` becomes
//! a `&mut CalculationAlgorithmContextBase` threaded through (it owns the per-test
//! databox + arenas — the "two-arena `&mut` → params" convention from the task
//! brief and `PORT.md` §5).
//!
//! KONCLUDE-PORT-NOTE[api]: at this wave the per-test individual-node / descriptor /
//! concept arenas are still "owned by the not-yet-ported CProcessContext"
//! (`process/db1.rs`, `process/db2.rs`), so the algorithm layer cannot yet resolve
//! a `NodeId`/`ConProcDescId`/`ConceptId` into a `&IndividualProcessNode` /
//! `&ConceptProcessDescriptor` / `&Concept`. Methods whose bodies dereference those
//! ids are therefore `// PORT-PENDING` + `todo!`, with their EXACT C++ control flow
//! kept as a faithful outline (each not-yet-ported subsystem call tagged
//! `// W3-DEFER[api]`) so no logic is dropped — they fill in once the arena
//! plumbing (CProcessContext) lands in a later wave. Some methods in the
//! processing-restriction cluster now call live process-context accessors; their
//! lower-level sibling calls retain their own deferral status.

#![allow(unused_variables, dead_code)]

use super::super::model::op;
use super::super::model::substrate::Cint64;
use super::super::model::substrate::{Id, NegLink, INVALID};
use super::super::model::ConceptId;
use super::super::process::dependency::BranchTreeNode;
use super::super::process::node::IndividualProcessNode;
use super::super::process::{
    BranchNodeId, ClashDescId, ConDescId, ConProcDescId, DependencyId, EdgeId, NodeId,
    RestrictionSpecId, TrackPointId,
};
use super::algorithm::{
    BranchKind, IndiNodeQueueType, OrBranchPoint, DETERMINISTIC_PROCESS_PRIORITY,
};
use super::context::CalculationAlgorithmContextBase;
use super::stubs::SatisfiableCalculationTask;

impl super::algorithm::CompletionTaskHandleAlgorithm {
    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::initialNodeInitialize`.
    ///
    /// PORT-PENDING: too entangled — the whole body dereferences the individual node
    /// (`indiProcNode->...`), its assertion/init-concept linkers, the backend-cache
    /// synchronisation data, and the ontology/databox, all of which need the
    /// CProcessContext arena access not yet wired into the algorithm layer. Faithful
    /// control-flow outline (cpp 8720-9038):
    ///
    /// ```text
    /// initialized = false; assInitSignatureBuilded = false
    /// if node is a real (non-fake) nominal && mBackendCacheHandler && !backendDataLoaded && !mOptIncrementalCompatibleExpansion:
    ///     // W3-DEFER[api]: loadIndividualNodeDataFromBackendCache(...)
    ///     if loaded && backendSyncData not initialised:
    ///         if !allowPreprocess || initRequired || !mOptDelayedBackendInitializiation
    ///            || !tryDelayIndividualNodeInitializationWithBackendConceptSetLabel(...):
    ///             // W3-DEFER[api]: initializeIndividualNodeWithBackendCache / setNominalIndividualRepresentativeBackendDataLoaded(true)
    ///             // W3-DEFER[api]: tryEstablishExpansionBlockingWithBackendCacheSynchronisation
    ///             // node.clearProcessingRestrictionFlags(PRF SYNCHRONIZEDBACKENPROCESSINGDELAYING)
    ///         else:
    ///             // node.addProcessingRestrictionFlags(PRF SYNCHRONIZEDBACKENPROCESSINGDELAYING); return false
    /// backendExpanded = false
    /// if node.isNominalIndividualRepresentativeBackendDataLoaded():
    ///     backendExpanded = true; detectIndividualNodeBackendCacheSynchronized(...)
    ///     if !PRF SYNCHRONIZEDBACKENDNEIGHBOUREXPANSIONBLOCKED && !PRF ...NEIGHBOURDFULLEXPANSION:
    ///         if allowPreprocess || mCurrentRecProcDepth < mCurrentRecProcDepthLimit:
    ///             if mConfAllowBackendNeighbourExpansionBlocking: add PRF ...NEIGHBOURDPARTIALEXPANSION
    ///             if !expandDirectlyInfluencedIndividualNeighbourNodesFromBackendCache(...): (toggle PARTIAL->FULL flags) backendExpanded = false
    ///             if node.hasPurgedBlockedProcessingRestrictionFlags(): return false
    ///         else: roleAssertionExpansionProcessingQueue.insert(node)
    /// if node.hasNominalIndividualTriplesAssertions() && !areNominalIndividualTriplesAssertionsLoaded():
    ///     // W3-DEFER[api]: ontology triples-assertion accessor → visit individual assertions, set nominal individual + assertion linkers
    ///     node.setNominalIndividualTriplesAssertionsLoaded(true)
    /// read assertionConceptLinker / assertionRoleLinker / assertionDataLinker / reverseAssertionRoleLinker / addProc{Role,Data}AssertionsLinker / initConceptLinker / reapplyConceptLabelSet
    /// if !node.hasBaseConceptsInitialized():
    ///     datatypeNode = PRF CONCRETEDATAINDINODE
    ///     if assertionConceptLinker || initConceptLinker || !conSet:
    ///         scan assertion & init concept linkers for CCFS_DATATYPE_RELATED_TYPE → datatypeNode
    ///         if !datatypeNode: addConceptToIndividual(ontologyTopConcept, false, node, depTrackPoint, allowPreprocess, true)
    ///         else: addConceptToIndividual(ontologyTopDataRangeConcept, ...); add PRF CONCRETEDATAINDINODE
    ///         initialized = true
    ///     if node.isNominalIndividualNode() && !PRF SUCCESSORNOMINALCONNECTION: propagateIndividualNodeNominalConnectionToAncestors(...)
    ///     node.setBaseConceptsInitialized(true)
    /// if !node.hasUniversallyConnectionIndividualInitialized():
    ///     univConnNomValueConcept = tbox.getUniversalConnectionNominalValueConcept()
    ///     if univConnNomValueConcept: if (assertion||init concepts||nominal) && !datatypeNode: addConceptToIndividual(univConnNomValueConcept, ...)
    ///     node.setUniversallyConnectionIndividualInitialized(true)
    /// if assertionConceptLinker:
    ///     build assInitSignature (skip CCNOMINAL); if mOptIncrementalCompatibleExpansion || !backendDataLoaded:
    ///         addConceptsToIndividual(assertionConceptLinker, ...); add nominalConcept if present
    ///     initialized = true; node.clearAssertionConcepts()
    /// if initConceptLinker:
    ///     if !databox.hasConstructedIndividualNodeInitialized(): set(true); tryCompletionGraphReuse(...)
    ///     if !mConfExpandCreatedSuccessorsFromSaturation || !tryInitalizingFromSaturatedData(...) || initConceptLinker.hasNext():
    ///         addConceptsToIndividual(initConceptLinker, ...)
    ///     node.clearProcessInitializingConcepts(); initialized = true; build assInitSignature from init concepts
    /// if assertionRoleLinker || reverseAssertionRoleLinker || addProcRoleAssertionsLinker:
    ///     detectIndividualNodeBackendCacheSynchronized(...); if !PRF SYNCHRONIZEDBACKENDNEIGHBOUREXPANSIONBLOCKED:
    ///         if allowPreprocess || mCurrentRecProcDepth < mCurrentRecProcDepthLimit:
    ///             (partial-expansion flag handling); if no backend sync data or !expand...FromBackendCache(...):
    ///                 clear assertion/reverse/additional role linkers; addRoleAssertion(...) loop + additional;
    ///                 setRoleAssertionsInitialized(true); addReverseRoleAssertion(...) loop + additional; setReverseRoleAssertionsInitialized(true)
    ///         else: roleAssertionExpansionProcessingQueue.insert(node)
    ///         initialized = true
    /// if node.getLastAssertedDataLiteralLinker() != node.getAssertedDataLiteralLinker():
    ///     for each new asserted data-literal: if mDatatypeHandler && mConfDatatypeReasoning: addDataLiteral(...); add datatype concept
    ///     node.setLastAssertedDataLiteralLinker(node.getAssertedDataLiteralLinker())
    /// if assertionDataLinker || addProcDataAssertionsLinker:
    ///     addDataAssertion(...) loop up to last processed; additional data-assertion linkers loop; advance last-processed cursors
    /// if assInitSignatureBuilded && mOptDetExpPreporcessing:
    ///     node.setAssertionInitialisationSignatureValue(sig); signatureNominalDelayingCandidateHash.insert(sig, node)
    /// if mConfAddCachedComputedConsequences && node.isNominalIndividualNode() && !mOptIncrementalExpansion: addCachedComputedTypes(node)
    /// return initialized
    /// ```
    pub fn initial_node_initialize(
        &mut self,
        indi_proc_node: NodeId,
        allow_preprocess: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // PORT-PENDING
        todo!(
            "W3-DEFER: initialNodeInitialize — needs CProcessContext arena access \
             (node/concept/backend-cache resolution) + the addConcept*/backend-cache/\
             saturation helper units, not yet wired into the algorithm layer"
        )
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::individualNodeInitializing`.
    ///
    /// PORT-PENDING: too entangled — relocalizes the node, flips its per-queue
    /// "queued" flags, and dispatches into backend-cache / value-space / unsat-cache
    /// helpers, all needing arena access + other units. Faithful outline (cpp 9061-9169):
    ///
    /// ```text
    /// lastIndiProcNode = indiProcNode
    /// // W3-DEFER[api]: indiProcNode = getLocalizedIndividual(indiProcNode, true, ctx)
    /// node.setProcessingQueued(false); node.setExtendedQueueProcessing(true); ctx.setCurrentIndividualNode(node)
    /// match mIndiNodeFromQueueType:
    ///   INQT_IMMEDIATE  -> node.setImmediatelyProcessingQueued(false)
    ///   INQT_DELAYEDBACKENDINIT -> if !backendSyncData.isBackendConceptSetInitializationRequired():
    ///        decQueuedNodeInitializingCount on the backendCacheConceptSetLabelProcessingHash entry;
    ///        ensure localized backend sync data; setBackendConceptSetInitializationRequired(true)
    ///   INQT_DETEXP     -> node.setDeterministicExpandingProcessingQueued(false)
    ///   INQT_DEPTHNORMAL | INQT_NOMINAL -> node.setRegularDepthProcessingQueued(false)
    ///   INQT_BLOCKREACT -> node.setBlockedReactivationProcessingQueued(false)
    ///   INQT_DELAYEDNOMINAL -> node.setDelayedNominalProcessingQueued(false)
    ///   INQT_BACKENDSYNCRETEST -> node.setBackendSynchronRetestProcessingQueued(false)
    ///   INQT_BACKENDDIRECTINFLUENCEEXPANSION -> node.setBackendDirectInfluenceExpansionQueued(false)
    ///   INQT_BACKENDINDIRECTCOMPATIBILITYEXPANSION -> node.setBackendIndirectCompatibilityExpansionQueued(false)
    /// node.resetLastProcessingPriority()
    /// if !node.hasPurgedBlockedProcessingRestrictionFlags():
    ///     initialNodeInitialize(node, true, ctx)
    ///     match mIndiNodeFromQueueType:
    ///       INQT_CACHETEST -> testIndividualNodeUnsatisfiableCached(...)
    ///       INQT_VSTSATTESTING -> checkValueSpaceDistinctSatisfiability(...)
    ///       INQT_VSTRIGGERING -> triggerValueSpaceConcepts(...)
    ///       INQT_BACKENDEXPANSIONREUSE -> node.setBackendReuseExpansionQueued(false);
    ///            if !purgedBlocked: (fixed/prioritized reuse-expansion prep + reuseIndividualBackendExpansion)
    ///     if isIndividualNodeProcessingBlocked(node, ctx): eliminiateBlockedIndividuals(node, ctx); return false
    ///     if mConfSignatureSaving: addSignatureIndividualNodeBlockerCandidate(node, ctx)
    ///     return true
    /// return false
    /// ```
    pub fn individual_node_initializing(
        &mut self,
        indi_proc_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W8: the per-node setup that runs before the concept queue is drained.
        // The queue-flag resets + current-node set + the unblocked-path `return true`
        // are ported live; the heavy initialNodeInitialize / blocking-test / value-space
        // arms (whose sub-helpers cascade into still-`todo!` saturation / signature /
        // backend-cache `detect_*` units) stay deferred and are inert on the trivial
        // (non-merge / non-cache / non-blocked) driver path.

        // CIndividualProcessNode* lastIndiProcNode = indiProcNode;
        // W8-DEFER[api]: indiProcNode = getLocalizedIndividual(indiProcNode, true, ctx)
        //   — relocalisation; the trivial driver performs no merges/relocalisation, so
        //   the node is already up to date.

        // indiProcNode->setProcessingQueued(false); indiProcNode->setExtendedQueueProcessing(true);
        {
            let n = calc_alg_context
                .process_context_mut()
                .node_mut(indi_proc_node);
            n.set_processing_queued(false);
            n.set_extended_queue_processing(true);
        }
        // calcAlgContext->setCurrentIndividualNode(indiProcNode);
        calc_alg_context
            .base
            .set_current_individual_node(indi_proc_node);

        // switch (mIndiNodeFromQueueType) — clear the queue-specific "queued" flag of
        // the queue the node was taken from (cpp 9070-9123).
        match self.indi_node_from_queue_type {
            IndiNodeQueueType::Inqt_Immediate => {
                calc_alg_context
                    .process_context_mut()
                    .node_mut(indi_proc_node)
                    .set_immediately_processing_queued(false);
            }
            IndiNodeQueueType::Inqt_DetExp => {
                calc_alg_context
                    .process_context_mut()
                    .node_mut(indi_proc_node)
                    .set_deterministic_expanding_processing_queued(false);
            }
            IndiNodeQueueType::Inqt_DepthNormal | IndiNodeQueueType::Inqt_Nominal => {
                calc_alg_context
                    .process_context_mut()
                    .node_mut(indi_proc_node)
                    .set_regular_depth_processing_queued(false);
            }
            IndiNodeQueueType::Inqt_BlockReact => {
                calc_alg_context
                    .process_context_mut()
                    .node_mut(indi_proc_node)
                    .set_blocked_reactivation_processing_queued(false);
            }
            IndiNodeQueueType::Inqt_BackendSyncRetest => {
                calc_alg_context
                    .process_context_mut()
                    .node_mut(indi_proc_node)
                    .set_backend_synchron_retest_processing_queued(false);
            }
            IndiNodeQueueType::Inqt_BackendDirectInfluenceExpansion => {
                calc_alg_context
                    .process_context_mut()
                    .node_mut(indi_proc_node)
                    .set_backend_direct_influence_expansion_queued(false);
            }
            // W8-DEFER[api]: the remaining INQT_* arms (DELAYEDBACKENDINIT /
            //   DELAYEDNOMINAL / BACKENDSYNCRETEST / BACKENDDIRECTINFLUENCEEXPANSION /
            //   BACKENDINDIRECTCOMPATIBILITYEXPANSION) flip queue-specific flags whose
            //   setters / backend-sync data are still W*-DEFER; inert on the trivial
            //   driver path.
            _ => {}
        }

        // `initialNodeInitialize`'s FIRST block (cpp 8713-8730): the per-node
        // backend-cache initialization, whose activation tail (cpp 22736-22771)
        // is what puts a nominal on the reuse-expansion queue. This is the
        // second of Konclude's two activation sites and the ONLY one a retained
        // class job can take — the other (`u36::get_up_to_date_individual_by_id`,
        // cpp 22524-22527) fires only when the individual is materialized for
        // the first time, and a retained job inherits the ABox node vector via
        // COW, so it never materializes one. Reaching this line means a rule
        // actually scheduled the node, which is exactly Konclude's
        // "reached/influenced" condition: nothing here walks the association
        // set, so the retained roots are never scheduled up front.
        //
        // KM-DEVIATION[timing], scoped to RETAINED nodes only: Konclude lets the
        // freshly initialized node continue its round, because the concepts its
        // initialization just added went in with
        // `addConceptToIndividualSkipANDProcessing(..., false)` — unprocessed —
        // so the node's concept-processing queue is effectively empty and the
        // reuse round comes first anyway. A node inherited from the retained
        // deterministic consistency base is different: it arrives with THAT
        // base's concept-processing queue, which still holds precisely the
        // disjunctions the base could not decide. Draining those before the
        // reuse round would open the individual's own branch points first and
        // defeat the mechanism, so a retained node with a PENDING reuse decision
        // defers its round instead. Nothing is lost: the concept queue is
        // untouched, `take_next_process_individual` (Probes 19/34) drains the
        // reuse queue — Probe 18 always selects the prioritized mode
        // (`u24::prepare_backend_expansion_reuse_branching`), so `take_next`
        // cannot return NONE while that queue is non-empty and no node can
        // starve — and `individual_node_conclusion` re-queues the node for
        // ordinary processing afterwards.
        //
        // `retained_base_node_count` is 0 on every route that does not run on a
        // retained base, so a freshly materialized node keeps Konclude's exact
        // timing there.
        if self.indi_node_from_queue_type != IndiNodeQueueType::Inqt_BackendExpansionReuse
            && !calc_alg_context
                .process_context()
                .node(indi_proc_node)
                .has_purged_blocked_processing_restriction_flags()
        {
            self.activate_backend_individual_expansion_reuse(indi_proc_node, calc_alg_context);
            if indi_proc_node.index() < self.retained_base_node_count
                && self.has_pending_backend_expansion_reuse(indi_proc_node, calc_alg_context)
            {
                self.native_reuse_pending_defer_count += 1;
                return false;
            }
        }

        // Native representative associations use the same queue discipline as
        // Konclude's backend cache, but their typed labels live on the bridge
        // replay record rather than the generic backend-sync stub. Retest
        // before ordinary concept processing so an incomplete association can
        // keep its raw role linkers blocked or selectively materialize only
        // concept/cardinality-influenced neighbours.
        if !self.process_native_nominal_backend_retest(indi_proc_node, calc_alg_context) {
            calc_alg_context.raise_stop(false);
            return false;
        }
        if calc_alg_context.has_pending_signal() {
            return false;
        }

        // indiProcNode->resetLastProcessingPriority();
        calc_alg_context
            .process_context_mut()
            .node_mut(indi_proc_node)
            .reset_last_processing_priority();

        // if (!indiProcNode->hasPurgedBlockedProcessingRestrictionFlags()) {
        if !calc_alg_context
            .process_context()
            .node(indi_proc_node)
            .has_purged_blocked_processing_restriction_flags()
        {
            // W8-DEFER[api]: initialNodeInitialize(indiProcNode, true, ctx) — the per-node
            //   cache/signature/backend setup (still a `todo!`); the INQT_CACHETEST /
            //   INQT_VST* dispatch arms.

            // INQT_BACKENDEXPANSIONREUSE (cpp 9119-9138). QUEUE TIMING: this runs
            // BEFORE the node's concept processing queue is drained, so the recorded
            // ABox model is adopted (or explicitly discarded) before any of the
            // individual's own disjunctions is opened — which is the whole point of
            // the mechanism. `take_next_process_individual` (u02, Probes 19/34)
            // likewise drains the reuse queue ahead of the individual-processing
            // queue, so a queued retained-ABox node never reaches ordinary
            // processing first.
            //
            //   indiProcNode->setBackendReuseExpansionQueued(false);
            //   if !purgedBlocked:
            //     if !PRFDISCARDED && !backendSyncData->getBackendExpansionReuseDependencyTrackPoint()
            //         && checkIndividualBackendExpansionReuseable(indiProcNode, ctx):
            //       if expContData->isFixedReuseExpansionMode():       prepareBackendIndividualFixedReuseExpansion(...)
            //       if expContData->isPrioritizedReuseExpansionMode(): prepareBackendIndividualPrioritizedReuseExpansion(...)
            //     if !PRFDISCARDED: reuseIndividualBackendExpansion(indiProcNode, ctx);
            if self.indi_node_from_queue_type == IndiNodeQueueType::Inqt_BackendExpansionReuse
                && !self.handle_backend_expansion_reuse_queue_node(indi_proc_node, calc_alg_context)
            {
                // The prioritized preparation opened the two-way reuse branch and
                // re-queued the individual under alternative 0's track point;
                // Konclude's `throw CCalculationStopProcessingException(true)` ends
                // this individual's processing here.
                return false;
            }
            if calc_alg_context.has_pending_signal() {
                return false;
            }

            if self.is_individual_node_processing_blocked(indi_proc_node, calc_alg_context) {
                self.eliminiate_blocked_individuals(indi_proc_node, calc_alg_context);
                return false;
            }
            // if (mConfSignatureSaving) addSignatureIndividualNodeBlockerCandidate(...) [W8-DEFER]
            return true;
        }
        // return false;
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::individualNodeConclusion`.
    ///
    /// PORT-PENDING: the two calls (`testIndividualNodeUnsatisfiableCached`,
    /// `addIndividualToProcessingQueue`) are unported sibling units, and the node ref
    /// passed to them needs arena access; `setCurrentIndividualNode(nullptr)` IS
    /// expressible but the surrounding control flow is gated on those calls. Faithful
    /// outline (cpp 9480-9494):
    ///
    /// ```text
    /// if mIndiNodeConcludeUnsatCaching:
    ///     // W3-DEFER[api]: testIndividualNodeUnsatisfiableCached(indiProcNode, ctx)
    /// ctx.setCurrentIndividualNode(nullptr)
    /// // W3-DEFER[api]: addIndividualToProcessingQueue(indiProcNode, ctx)
    /// ```
    pub fn individual_node_conclusion(
        &mut self,
        indi_proc_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        if self.indi_node_conclude_unsat_caching && !calc_alg_context.has_pending_signal() {
            self.test_individual_node_unsatisfiable_cached(indi_proc_node, calc_alg_context);
        }

        calc_alg_context
            .base
            .set_current_individual_node(NodeId::NONE);
        self.add_individual_to_processing_queue(indi_proc_node, calc_alg_context);
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::tableauRuleProcessing`.
    ///
    /// PORT-PENDING: reads `conProcDes->getConceptDescriptor()` / `conDes->getNegation()`
    /// / `concept->getOperatorCode()` (descriptor + concept arena) and gates on
    /// unported nominal-delay / expansion-blocking predicates before delegating to
    /// `tableauRuleChoice`. Faithful outline (cpp 9496-9519):
    ///
    /// ```text
    /// conDes = conProcDes.getConceptDescriptor(); conNeg = conDes.getNegation()
    /// concept = conDes.getConcept(); conOpCode = concept.getOperatorCode()
    /// if tryDelayNominalProcessing(conProcDes, indiProcNode, ctx): return false
    /// if needsIndividualNodeExpansionBlockingTest(conProcDes, indiProcNode, ctx):
    ///     if isIndividualNodeBackendCacheSynchronizationProcessingBlocked(indiProcNode, ctx): return false
    ///     if isIndividualNodeExpansionBlocked(indiProcNode, ctx): return false
    /// tableauRuleChoice(indiProcNode, conProcDes, ctx)
    /// return true
    /// ```
    pub fn tableau_rule_processing(
        &mut self,
        indi_proc_node: NodeId,
        con_proc_des: ConProcDescId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // CConceptDescriptor* conDes = conProcDes->getConceptDescriptor();
        // bool conNeg = conDes->getNegation();
        // CConcept* concept = conDes->getConcept();
        // cint64 conOpCode = concept->getOperatorCode();
        // (Faithful C++ prelude: these locals are read but only consumed by
        // `tableauRuleChoice`, which recomputes them; omitted here to avoid an
        // unused arena read — the descriptor/concept reads happen in the choice.)

        // if (tryDelayNominalProcessing(conProcDes,indiProcNode,calcAlgContext)) return false;
        if self.try_delay_nominal_processing(con_proc_des, indi_proc_node, calc_alg_context) {
            return false;
        }

        // if (needsIndividualNodeExpansionBlockingTest(conProcDes,indiProcNode,calcAlgContext)) {
        if self.needs_individual_node_expansion_blocking_test(
            con_proc_des,
            indi_proc_node,
            calc_alg_context,
        ) {
            // if (isIndividualNodeBackendCacheSynchronizationProcessingBlocked(...)) return false;
            if self.is_individual_node_backend_cache_synchronization_processing_blocked(
                indi_proc_node,
                calc_alg_context,
            ) {
                return false;
            }
            // if (isIndividualNodeExpansionBlocked(indiProcNode,calcAlgContext)) return false;
            if self.is_individual_node_expansion_blocked(indi_proc_node, calc_alg_context) {
                return false;
            }
        }

        // tableauRuleChoice(indiProcNode,conProcDes,calcAlgContext);
        self.tableau_rule_choice(indi_proc_node, con_proc_des, calc_alg_context);

        // return true;
        true
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::tableauRuleChoice`.
    ///
    /// PORT-PENDING: the core is a member-function-pointer jump-table dispatch
    /// (`mPosJumpFuncVec[conOpCode]` / `(this->*func)(...)`) into the `apply*Rule`
    /// engine; the jump tables are opaque `[Cint64; N]` until those rules are ported,
    /// and `conOpCode` needs descriptor+concept arena reads. The recursion-depth
    /// bookkeeping (`++/--mCurrentRecProcDepth`) and `mLastJumpFunc` ARE port-able but
    /// meaningless without the dispatch, so the whole method is deferred. Faithful
    /// outline (cpp 9522-9549):
    ///
    /// ```text
    /// conDes = conProcDes.getConceptDescriptor(); conNeg = conDes.getNegation()
    /// concept = conDes.getConcept(); conOpCode = concept.getOperatorCode()
    /// ++mCurrentRecProcDepth
    /// if !conNeg: func = mPosJumpFuncVec[conOpCode]; if func: (this->*func)(indi, conProcDes, false, ctx); mLastJumpFunc = func
    /// else:       func = mNegJumpFuncVec[conOpCode]; if func: (this->*func)(indi, conProcDes, true,  ctx); mLastJumpFunc = func
    /// --mCurrentRecProcDepth
    /// ```
    pub fn tableau_rule_choice(
        &mut self,
        indi_proc_node: NodeId,
        con_proc_des: ConProcDescId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // CConceptDescriptor* conDes = conProcDes->getConceptDescriptor();
        let con_des: ConDescId = calc_alg_context
            .process_context()
            .con_proc_desc(con_proc_des)
            .get_concept_descriptor();
        // bool conNeg = conDes->getNegation();
        let con_neg: bool = calc_alg_context
            .process_context()
            .con_desc(con_des)
            .is_negated();
        // CConcept* concept = conDes->getConcept();
        let concept: ConceptId = calc_alg_context
            .process_context()
            .con_desc(con_des)
            .get_concept();
        // cint64 conOpCode = concept->getOperatorCode();
        let con_op_code: Cint64 = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operator_code();

        // ++mCurrentRecProcDepth;
        self.current_rec_proc_depth += 1;

        // KONCLUDE-PORT-NOTE[pointer-alias]: the C++ dispatch is a member-function-
        // pointer jump table — `func = mPosJumpFuncVec[conOpCode]` (resp.
        // `mNegJumpFuncVec`), then `(this->*func)(indiProcNode,conProcDes,negate,ctx)`.
        // Rust cannot store the algorithm's `apply*Rule` methods as member-fn pointers
        // in the struct (`PORT.md` keeps `m{Pos,Neg}JumpFuncVec` opaque), so the
        // indirect call is ported as an explicit `match` on the operator code that
        // mirrors the table built in the algorithm ctor 1:1 (cpp 238-345). Positive
        // entries are invoked with `negate == false`, negative entries with
        // `negate == true`, exactly as the two `(this->*func)(...)` call sites. The two
        // config gates select the alternative entries the C++ overwrites:
        //   - mConfSpecializedAutomateRules → AQAND family uses applyAutomatANDRule;
        //   - mConfRepresentativePropagationRules → VARBIND family uses the
        //     applyREPRESENTATIVE* rules instead of the applyVARBIND*/applyVARIABLE*.
        // `func == nullptr` (no table entry) ⇒ no rule fired (the `_` arms).
        // The C++ passes `indiProcNode` / `conProcDes` by reference (`*&`) so an
        // apply rule can advance them; mirror with mutable locals (`&mut` into the
        // rules). The caller does not observe the advance (tableauRuleChoice returns
        // void and tableauRuleProcessing discards it), so local copies are faithful.
        let mut indi = indi_proc_node;
        let mut cpd = con_proc_des;
        let indi = &mut indi;
        let cpd = &mut cpd;
        let mut dispatched = true;

        // KM_BRIDGE_SEARCH_LOG: every rule dispatch — node, concept tag,
        // polarity, op, epoch depth (the queued-descriptor provenance trace).
        if super::bridge_search_log_enabled() {
            let tag = calc_alg_context
                .ontology_arenas()
                .concept(concept)
                .get_concept_tag();
            let in_label = {
                let pc = calc_alg_context.process_context();
                let ls = pc.node(*indi).use_reapply_con_label_set;
                ls.is_some()
                    && pc.label_set(ls).has_concept_in_context(
                        pc,
                        calc_alg_context.ontology_arenas(),
                        concept,
                        con_neg,
                    )
            };
            let m = format!(
                "proc node={} tag={}{} op={} depth={} in_label={}",
                indi.index(),
                if con_neg { "-" } else { "" },
                tag,
                con_op_code,
                calc_alg_context.process_context().branch_epoch_depth(),
                in_label
            );
            self.ht_search_log(&m);
        }

        if !con_neg {
            // func = mPosJumpFuncVec[conOpCode];
            match con_op_code {
                op::CCTOP => self.apply_and_rule(indi, cpd, false, calc_alg_context),
                op::CCBOTTOM => self.apply_bottom_rule(indi, cpd, false, calc_alg_context),
                op::CCAND | op::CCSUB | op::CCEQ | op::CCIMPLTRIG | op::CCBRANCHTRIG => {
                    self.apply_and_rule(indi, cpd, false, calc_alg_context)
                }
                op::CCAQAND | op::CCIMPLAQAND | op::CCBRANCHAQAND => {
                    if self.conf_specialized_automate_rules {
                        self.apply_automat_and_rule(indi, cpd, false, calc_alg_context)
                    } else {
                        self.apply_and_rule(indi, cpd, false, calc_alg_context)
                    }
                }
                op::CCDATATYPE => self.apply_datatype_rule(indi, cpd, false, calc_alg_context),
                op::CCDATALITERAL => {
                    self.apply_data_literal_rule(indi, cpd, false, calc_alg_context)
                }
                op::CCDATARESTRICTION => {
                    self.apply_data_restriction_rule(indi, cpd, false, calc_alg_context)
                }
                op::CCOR => self.apply_or_rule(indi, cpd, false, calc_alg_context),
                op::CCALL
                | op::CCAQALL
                | op::CCIMPLAQALL
                | op::CCBRANCHAQALL
                | op::CCIMPLALL
                | op::CCBRANCHALL => self.apply_all_rule(indi, cpd, false, calc_alg_context),
                op::CCSOME | op::CCAQSOME => {
                    self.apply_some_rule(indi, cpd, false, calc_alg_context)
                }
                op::CCAQCHOOCE => {
                    self.apply_automat_choose_rule(indi, cpd, false, calc_alg_context)
                }
                op::CCNOT => self.apply_neg_and_rule(indi, cpd, false, calc_alg_context),
                op::CCSELF => self.apply_self_rule(indi, cpd, false, calc_alg_context),
                op::CCATLEAST => self.apply_atleast_rule(indi, cpd, false, calc_alg_context),
                op::CCATMOST => self.apply_atmost_rule(indi, cpd, false, calc_alg_context),
                op::CCNOMINAL => self.apply_nominal_rule(indi, cpd, false, calc_alg_context),
                op::CCVALUE => self.apply_value_rule(indi, cpd, false, calc_alg_context),
                op::CCIMPL => self.apply_implication_rule(indi, cpd, false, calc_alg_context),
                op::CCPBINDVARIABLE => {
                    self.apply_bind_variable_rule(indi, cpd, false, calc_alg_context)
                }
                op::CCPBINDTRIG | op::CCPBINDAND | op::CCPBINDAQAND => {
                    self.apply_bind_propagate_and_rule(indi, cpd, false, calc_alg_context)
                }
                op::CCPBINDIMPL => {
                    self.apply_bind_propagate_implication_rule(indi, cpd, false, calc_alg_context)
                }
                op::CCPBINDALL | op::CCPBINDAQALL => {
                    self.apply_bind_propagate_all_rule(indi, cpd, false, calc_alg_context)
                }
                op::CCPBINDCYCLE => {
                    self.apply_bind_propagate_cycle_rule(indi, cpd, false, calc_alg_context)
                }
                op::CCPBINDGROUND => {
                    self.apply_bind_propagate_grounding_rule(indi, cpd, false, calc_alg_context)
                }
                op::CCVARBINDVARIABLE => {
                    if self.conf_representative_propagation_rules {
                        self.apply_representative_bind_variable_rule(
                            indi,
                            cpd,
                            false,
                            calc_alg_context,
                        )
                    } else {
                        self.apply_varbind_variable_rule(indi, cpd, false, calc_alg_context)
                    }
                }
                op::CCVARBINDTRIG | op::CCVARBINDAND | op::CCVARBINDAQAND => {
                    if self.conf_representative_propagation_rules {
                        self.apply_representative_and_rule(indi, cpd, false, calc_alg_context)
                    } else {
                        self.apply_variable_binding_and_rule(indi, cpd, false, calc_alg_context)
                    }
                }
                op::CCVARBINDIMPL => {
                    if self.conf_representative_propagation_rules {
                        self.apply_representative_implication_rule(
                            indi,
                            cpd,
                            false,
                            calc_alg_context,
                        )
                    } else {
                        self.apply_varbind_propagate_implication_rule(
                            indi,
                            cpd,
                            false,
                            calc_alg_context,
                        )
                    }
                }
                op::CCVARBINDALL | op::CCVARBINDAQALL => {
                    if self.conf_representative_propagation_rules {
                        self.apply_representative_all_rule(indi, cpd, false, calc_alg_context)
                    } else {
                        self.apply_varbind_propagate_all_rule(indi, cpd, false, calc_alg_context)
                    }
                }
                op::CCVARBINDJOIN => {
                    if self.conf_representative_propagation_rules {
                        self.apply_representative_join_rule(indi, cpd, false, calc_alg_context)
                    } else {
                        self.apply_varbind_propagate_join_rule(indi, cpd, false, calc_alg_context)
                    }
                }
                op::CCVARBINDGROUND => {
                    if self.conf_representative_propagation_rules {
                        self.apply_representative_grounding_rule(indi, cpd, false, calc_alg_context)
                    } else {
                        self.apply_varbind_propagate_grounding_rule(
                            indi,
                            cpd,
                            false,
                            calc_alg_context,
                        )
                    }
                }
                op::CCBACKACTIVTRIG => {
                    self.apply_bind_propagate_and_flag_all_rule(indi, cpd, false, calc_alg_context)
                }
                op::CCVARPBACKTRIG | op::CCVARPBACKAQAND => {
                    self.apply_bind_propagate_and_rule(indi, cpd, false, calc_alg_context)
                }
                op::CCVARPBACKALL | op::CCVARPBACKAQALL => {
                    self.apply_bind_propagate_all_rule(indi, cpd, false, calc_alg_context)
                }
                op::CCBACKACTIVIMPL => {
                    self.apply_bind_propagate_implication_rule(indi, cpd, false, calc_alg_context)
                }
                op::CCNOMINALIMPLI => {
                    self.apply_nominal_implication_rule(indi, cpd, false, calc_alg_context)
                }
                op::CCDATATYPEIMPLI => {
                    self.apply_datatype_implication_rule(indi, cpd, false, calc_alg_context)
                }
                op::CCDATALITERALIMPLI => {
                    self.apply_data_literal_implication_rule(indi, cpd, false, calc_alg_context)
                }
                op::CCDATARESTRICTIONIMPLI => {
                    self.apply_data_restriction_implication_rule(indi, cpd, false, calc_alg_context)
                }
                op::CCVARBINDPREPARE => {
                    self.apply_varbind_prepare_rule(indi, cpd, false, calc_alg_context)
                }
                op::CCVARBINDFINALZE => {
                    self.apply_varbind_finalize_rule(indi, cpd, false, calc_alg_context)
                }
                _ => dispatched = false,
            }
        } else {
            // func = mNegJumpFuncVec[conOpCode];
            match con_op_code {
                op::CCDATATYPE => self.apply_datatype_rule(indi, cpd, true, calc_alg_context),
                op::CCDATALITERAL => {
                    self.apply_data_literal_rule(indi, cpd, true, calc_alg_context)
                }
                op::CCDATARESTRICTION => {
                    self.apply_data_restriction_rule(indi, cpd, true, calc_alg_context)
                }
                op::CCAND => self.apply_or_rule(indi, cpd, true, calc_alg_context),
                op::CCOR => self.apply_and_rule(indi, cpd, true, calc_alg_context),
                op::CCEQ => self.apply_or_rule(indi, cpd, true, calc_alg_context),
                op::CCALL => self.apply_some_rule(indi, cpd, true, calc_alg_context),
                op::CCNOT => self.apply_neg_and_rule(indi, cpd, true, calc_alg_context),
                op::CCSOME => self.apply_all_rule(indi, cpd, true, calc_alg_context),
                op::CCAQCHOOCE => self.apply_automat_choose_rule(indi, cpd, true, calc_alg_context),
                op::CCSELF => self.apply_self_rule(indi, cpd, true, calc_alg_context),
                op::CCATMOST => self.apply_atleast_rule(indi, cpd, true, calc_alg_context),
                op::CCATLEAST => self.apply_atmost_rule(indi, cpd, true, calc_alg_context),
                op::CCNOMINAL => self.apply_nominal_rule(indi, cpd, true, calc_alg_context),
                op::CCVALUE => self.apply_value_rule(indi, cpd, true, calc_alg_context),
                op::CCPBINDGROUND => {
                    self.apply_bind_propagate_grounding_rule(indi, cpd, true, calc_alg_context)
                }
                op::CCVARBINDGROUND => {
                    if self.conf_representative_propagation_rules {
                        self.apply_representative_grounding_rule(indi, cpd, true, calc_alg_context)
                    } else {
                        self.apply_varbind_propagate_grounding_rule(
                            indi,
                            cpd,
                            true,
                            calc_alg_context,
                        )
                    }
                }
                _ => dispatched = false,
            }
        }

        // mLastJumpFunc = func;
        // W3-DEFER[pointer-alias]: the C++ records the dispatched member-fn pointer
        // (or nullptr) for later identity comparison; with the `match` port there is
        // no fn-pointer value to store, so we record only whether a rule fired
        // (no current reader depends on the precise identity).
        self.last_jump_func = if dispatched { 1 } else { INVALID };

        // --mCurrentRecProcDepth;
        self.current_rec_proc_depth -= 1;
    }

    /// Port of Konclude `initializeORProcessing` (completion cpp
    /// 16448-16482).  Replacement concepts are consumed here once their typed
    /// preprocessing arena is available; the priority gate and delayed queue
    /// are fully live now and deliberately precede operand planning.
    pub fn initialize_or_processing(
        &mut self,
        process_indi: NodeId,
        con_pro_des: ConProcDescId,
        _negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let (con_des, dep_track_point, process_priority) = {
            let cpd = calc_alg_context
                .process_context()
                .con_proc_desc(con_pro_des);
            (
                cpd.get_concept_descriptor(),
                cpd.get_dependency_track_point(),
                cpd.get_process_priority().get_priority(),
            )
        };
        let concept = calc_alg_context
            .process_context()
            .con_desc(con_des)
            .get_concept();
        let default_priority = self
            .priority_for_concept(con_des, process_indi, calc_alg_context)
            .get_priority();

        if process_priority >= DETERMINISTIC_PROCESS_PRIORITY as f64
            && process_priority >= default_priority
        {
            let replacement = {
                let concept_data = calc_alg_context
                    .ontology_arenas()
                    .concept(concept)
                    .get_concept_data();
                if concept_data == INVALID {
                    None
                } else {
                    let replacement_id = calc_alg_context
                        .ontology_arenas()
                        .concept_process_data(Id::new(concept_data))
                        .get_replacement_data();
                    replacement_id.is_some().then(|| {
                        let data = calc_alg_context
                            .ontology_arenas()
                            .replacement_data(replacement_id);
                        (
                            data.implication_replacement_concept,
                            data.common_disjunct_concepts.clone(),
                        )
                    })
                }
            };
            if let Some((implication, common)) = replacement {
                if super::ht_or_trace_enabled() {
                    let tags: Vec<_> = common
                        .iter()
                        .map(|link| {
                            (
                                calc_alg_context
                                    .ontology_arenas()
                                    .concept(link.target)
                                    .get_concept_tag(),
                                link.negated,
                            )
                        })
                        .collect();
                    eprintln!(
                        "OR-REPLACEMENT concept={} implication={} common={tags:?}",
                        calc_alg_context
                            .ontology_arenas()
                            .concept(concept)
                            .get_concept_tag(),
                        implication.raw,
                    );
                }
                let mut node = process_indi;
                if !common.is_empty() {
                    self.add_concepts_to_individual(
                        &common,
                        false,
                        &mut node,
                        dep_track_point,
                        true,
                        false,
                        None,
                        calc_alg_context,
                    );
                }
                if implication.is_some() {
                    self.add_concept_to_individual(
                        implication,
                        false,
                        &mut node,
                        dep_track_point,
                        true,
                        false,
                        calc_alg_context,
                    );
                    return true;
                }
            }

            let priority_offset = calc_alg_context
                .base
                .used_concept_priority_strategy()
                .expect("concept priority strategy")
                .get_priority_offset_for_disjunction_delayed_considering(con_des, process_indi);
            let queue = calc_alg_context
                .process_context_mut()
                .node_concept_processing_queue(process_indi, true);
            self.add_concept_restricted_to_processing_queue_offset(
                con_des,
                dep_track_point,
                queue,
                process_indi,
                true,
                INVALID,
                priority_offset,
                calc_alg_context,
            );
            if super::ht_or_trace_enabled() {
                eprintln!(
                    "OR-DELAY-CONSIDER concept={} priority={} offset={}",
                    calc_alg_context
                        .ontology_arenas()
                        .concept(concept)
                        .get_concept_tag(),
                    process_priority,
                    priority_offset,
                );
            }
            return true;
        }
        false
    }

    /// Execute the port's in-process equivalent of Konclude's dependent OR
    /// task list for a set of operands already selected by `planORProcessing`.
    ///
    /// PORT-PENDING: reads the concept descriptor / concept-process-data / replacement
    /// data, queries the concept-priority strategy, and routes to the addConcept* /
    /// addConceptRestrictedToProcessingQueue helper units (all arena + unported).
    /// Faithful outline (cpp 16396-16430):
    ///
    /// ```text
    /// conDes = conProDes.getConceptDescriptor(); concept = conDes.getConcept(); depTrackPoint = conProDes.getDependencyTrackPoint()
    /// disjunctionDefaultPriority = usedConceptPriorityStrategy.getPriorityForConcept(conDes, processIndi)
    /// if conProDes.processPriority >= mDeterministicProcessPriority && >= disjunctionDefaultPriority:
    ///     conProData = concept.getConceptData()
    ///     if conProData: repData = conProData.getReplacementData()
    ///         if repData: impConcept = repData.getImplicationReplacementConcept(); commDisConLinker = repData.getCommonDisjunctConceptLinker()
    ///         if commDisConLinker: addConceptsToIndividual(commDisConLinker, false, processIndi, depTrackPoint, true, false, null, ctx)
    ///         if impConcept: addConceptToIndividual(impConcept, false, processIndi, depTrackPoint, true, false, ctx); return true
    ///     conProQueue = processIndi.getConceptProcessingQueue(true)
    ///     priorityOffset = usedConceptPriorityStrategy.getPriorityOffsetForDisjunctionDelayedConsidering(conDes, processIndi)
    ///     addConceptRestrictedToProcessingQueue(conDes, depTrackPoint, conProQueue, processIndi, true, null, priorityOffset, ctx)
    ///     return true
    /// return false
    /// ```
    pub(super) fn start_or_branching_in_process(
        &mut self,
        process_indi: NodeId,
        con_pro_des: ConProcDescId,
        negate: bool,
        mut operands: Vec<NegLink<ConceptId>>,
        branch_clashes: ClashDescId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // KONCLUDE-PORT-NOTE[branching]: the faithful `initializeORProcessing` (cpp
        // 16396-16430) only handles the priority-DELAY / replacement-concept fast
        // paths and returns false otherwise, letting `planORProcessing` →
        // `executeORBranching` (u09) do the real disjunction work by FORKING one
        // `CSatisfiableCalculationTask` per alternative and throwing a stop. That
        // task-fork machinery + the dependency-directed `clashedBacktracking` (u29)
        // are still unported (the Task/scheduler layer + the u29 tracking-line
        // records). To run disjunction end-to-end the port performs the branch
        // IN-PROCESS here: create the branch-tree node + OR dependency node, push one
        // `OrBranchPoint`, add the FIRST unexplored alternative to the individual, and
        // return true (so `apply_or_rule`'s u09 path does NOT also fire the deferred
        // task-fork `execute_or_branching`). The chronological backtrack over the
        // remaining alternatives is driven by `run_completion_on` (u02). The faithful
        // priority-delay/replacement arms (the concept-priority strategy +
        // `addConceptRestrictedToProcessingQueue`) stay deferred and are inert here
        // (`disjunctionDefaultPriority` would route them to the queue); the documented
        // gap is the per-alternative task fork + dependency-directed backjump.
        // conDes = conProDes->getConceptDescriptor(); concept = conDes->getConcept();
        // depTrackPoint = conProDes->getDependencyTrackPoint();
        let con_des: ConDescId = calc_alg_context
            .process_context()
            .con_proc_desc(con_pro_des)
            .get_concept_descriptor();
        let concept: ConceptId = calc_alg_context
            .process_context()
            .con_desc(con_des)
            .get_concept();
        let dep_track_point: TrackPointId = calc_alg_context
            .process_context()
            .con_proc_desc(con_pro_des)
            .get_dependency_track_point();

        // concept->getOperandList() — the disjunction's operands (lives in the
        // ctx-owned concept arena; collected to an owned Vec before the &mut calls,
        // exactly as `apply_and_rule`/`execute_or_branching` do).
        if operands.len() < 2 {
            // 0/1-operand disjunctions are handled upstream in `apply_or_rule`
            // (clash / AND-rule); nothing to branch — let `plan_or_processing` fall
            // through.
            return false;
        }
        // Konclude keeps the semantic partition in sorted operand order and
        // schedules the child tasks separately by ontology-local learned
        // priority. Do not reorder `operands`: branch i must always mean
        // O_i together with the negations of O_0..O_{i-1}.
        let original_operand_count = usize::try_from(
            calc_alg_context
                .ontology_arenas()
                .concept(concept)
                .get_operand_count(),
        )
        .unwrap_or(0)
        .max(operands.len());
        let alternative_order =
            self.ht_or_branch_alternative_order(concept, &operands, negate, original_operand_count);
        let first_alt = alternative_order[0];
        let first_sem_branch: Vec<NegLink<ConceptId>> =
            if self.conf_semantic_branching || self.conf_atomic_semantic_branching {
                operands[..first_alt]
                    .iter()
                    .map(|link| NegLink {
                        target: link.target,
                        negated: !(link.negated ^ negate),
                    })
                    .collect()
            } else {
                Vec::new()
            };

        // --- createBranchingTreeNode / createORDependency (the ported records). ---
        // The parent / root branch nodes chain chronologically (the topmost open
        // branch is this one's parent), mirroring `CBranchTreeNode`'s parent/root
        // wiring; `branching_increment` / `getDependencyTrackPointBranch` binding is
        // W3-DEFER (the branch-tree branching counters need the unported tagger).
        let parent_branch: BranchNodeId = self
            .or_branch_stack
            .last()
            .map(|bp| bp.branch_node)
            .unwrap_or(BranchNodeId::NONE);
        let root_branch: BranchNodeId = self
            .or_branch_stack
            .first()
            .map(|bp| bp.branch_node)
            .unwrap_or(BranchNodeId::NONE);
        let or_dependency_node: DependencyId = if self.conf_build_dependencies {
            // The faithful `createORDependency` (u28, cpp 10115–10121): the OR
            // node records the disjunction's concept descriptor + previous track
            // point, so the tracked-clash analysis (u29) walks THROUGH the OR to
            // the concepts that produced it.
            let mut pi = process_indi;
            self.create_or_dependency(&mut pi, con_des, dep_track_point, calc_alg_context)
        } else {
            calc_alg_context
                .process_context_mut()
                .alloc_or_dependency_node()
        };
        // `executeORBranching`: `orDependencyNode->addBranchClashes(...)`.
        // These are the opposite-polarity facts that eliminated operands
        // before the true multi-way branch was opened.
        if self.conf_build_dependencies {
            self.ht_add_branch_clashes(or_dependency_node, branch_clashes, calc_alg_context);
        }

        // DDB: mint ONE non-deterministic track point PER ALTERNATIVE, upfront
        // (Konclude's `executeORBranching` per-forked-task
        // `createNonDeterministicDependencyTrackPointBranch`; each child task's
        // used branch tree node is a fresh copy of the parent's, so every
        // sibling gets branching tag = parent level + 1 on its OWN branch node).
        // Upfront minting is a soundness requirement: the u29 propagation reads
        // "all sibling track points clashed" as "the whole disjunction is
        // refuted"; lazily-minted siblings would fire it early.
        let parent_used_branch_node = calc_alg_context.base.used_branch_tree_node;
        let alt_track_points: Vec<TrackPointId> = self.ht_mint_alternative_track_points(
            or_dependency_node,
            operands.len(),
            parent_used_branch_node,
            calc_alg_context,
        );
        let branch_node: BranchNodeId =
            calc_alg_context
                .process_context_mut()
                .alloc_branch_node(BranchTreeNode {
                    process_tag: 0,
                    parent_node: parent_branch,
                    // a root branch node is its own root (`CBranchTreeNode::mRootNode`).
                    root_node: root_branch,
                    branched_dep_track_point: Id::NONE,
                    sat_calc_task: INVALID,
                });

        // SOUND-BACKTRACK: snapshot the node's label set BEFORE any disjunct is
        // added, so backtracking can restore the clean pre-disjunction state and
        // undo the failed alternative's derivations (fixes the chronological-
        // backtrack unsoundness for same-node disjunctions).
        let node_count_at_push = calc_alg_context.process_context().node_count();
        // Under in-process COW the branch epoch restores the COMPLETE state,
        // so the single-node snapshots are redundant — keep them empty.
        let node_label_snapshot = if self.conf_inprocess_cow {
            Default::default()
        } else {
            let ls_id = calc_alg_context
                .process_context_mut()
                .node_reapply_concept_label_set(process_indi);
            calc_alg_context.process_context().label_set(ls_id).clone()
        };
        // The processing queue is snapshotted TOGETHER with the label set (they are
        // coupled through trigger-reapply registration; see `OrBranchPoint`). The
        // disjunction's own descriptor was already taken from the queue, so it is
        // NOT in the snapshot and cannot re-fire after a restore.
        let node_queue_snapshot = if self.conf_inprocess_cow {
            Default::default()
        } else {
            let q_id = calc_alg_context
                .process_context_mut()
                .node_concept_processing_queue(process_indi, true);
            calc_alg_context
                .process_context()
                .concept_proc_queue(q_id)
                .clone()
        };

        // In-process COW: open the alternative's branch epoch AFTER the
        // per-disjunction records (OR dependency, alternative track points,
        // snapshots) — those belong to the PARENT state and survive
        // alternative pops — and BEFORE the first disjunct is added.
        if self.conf_inprocess_cow {
            calc_alg_context.push_branch_epoch();
        }

        // Push the open branch point; the FIRST alternative is added now, so the
        // next unexplored alternative is index 1.
        let first: NegLink<ConceptId> = operands[first_alt];
        let first_alt_tp = alt_track_points.get(first_alt).copied().unwrap_or(Id::NONE);
        self.record_or_branch_open(process_indi, calc_alg_context);
        self.or_branch_stack.push(OrBranchPoint {
            node: process_indi,
            disjuncts: operands,
            alternative_order,
            current_alt: first_alt,
            branching_concept: concept,
            negate,
            next_alt: 1,
            dep_track_point,
            branch_node,
            or_dependency_node,
            alt_track_points,
            parent_used_branch_node,
            node_label_snapshot,
            node_queue_snapshot,
            node_count_at_push,
            kind: BranchKind::Disjunction,
            own_epoch: self.conf_inprocess_cow,
        });

        // addConceptToIndividual(operand, opNegated, processIndi, depTrackPoint, ...).
        // The chosen disjunct's effective negation is `operand.isNegated() ^ negate`
        // (the `executeORBranching` `addOpNegated` rule). Under DDB the disjunct is
        // added under ITS alternative's non-deterministic track point (Konclude's
        // per-branch `CORDisjunctDependencyTrackPoint`), and that alternative's
        // branch node becomes the used branch tree node so nested disjunctions
        // nest one branching level deeper.
        let mut process_indi_m = process_indi;
        let op_negated = first.negated ^ negate;
        let add_tp = if first_alt_tp.is_some() {
            calc_alg_context.base.used_branch_tree_node = calc_alg_context
                .process_context()
                .track_point(first_alt_tp)
                .get_branch_node();
            first_alt_tp
        } else {
            dep_track_point
        };
        self.add_concept_to_individual(
            first.target,
            op_negated,
            &mut process_indi_m,
            add_tp,
            true,
            true,
            calc_alg_context,
        );
        // Atomic semantic branching belongs to the semantic child partition,
        // not to chronological exploration order. A learned child can be
        // scheduled first while still carrying the negations of all earlier
        // sorted atomic operands.
        if !calc_alg_context.has_pending_signal() {
            for link in first_sem_branch {
                if self.conf_semantic_branching
                    || self.is_concept_addition_atomaric(
                        link.target,
                        link.negated,
                        calc_alg_context,
                    )
                {
                    let mut node = process_indi_m;
                    self.add_concept_to_individual(
                        link.target,
                        link.negated,
                        &mut node,
                        add_tp,
                        true,
                        true,
                        calc_alg_context,
                    );
                    if calc_alg_context.has_pending_signal() {
                        break;
                    }
                }
            }
        }

        // Unsat-cache probe after the branched disjunct lands (cpp 16908:
        // `testUnsatisfiableCacheForBranchedDisjuncts` is constant-true in the
        // generative strategy). A hit clashes this alternative immediately —
        // a learned nogood short-circuits the whole subtree. Pending-gated:
        // `raise_clash` OVERWRITES the signal, so a clash already raised by
        // the disjunct addition itself must win.
        if !calc_alg_context.has_pending_signal() {
            self.test_individual_node_unsatisfiable_cached(process_indi_m, calc_alg_context);
        }

        true
    }

    /// Cache-oriented disjunct scheduling from
    /// `CEqualDepthCacheOrientatedProcessingPriorityStrategy`. Parent depth and
    /// the ordinary (non-completion-graph-cached) `0.2` sub-offset are equal
    /// for siblings, so this reproduces the remaining branch-number and
    /// learned-statistics terms exactly.
    fn ht_or_branch_alternative_order(
        &self,
        concept: ConceptId,
        operands: &[NegLink<ConceptId>],
        negate: bool,
        original_operand_count: usize,
    ) -> Vec<usize> {
        let alternative_count = operands.len();
        let mut order: Vec<usize> = (0..alternative_count).collect();
        if !self.conf_cache_oriented_or_ordering {
            if self.conf_or_reverse {
                order.reverse();
            }
            return order;
        }
        let score = |alternative: usize| {
            let operand = operands[alternative];
            let statistics = self
                .or_branch_learning_stats
                .get(&(concept, operand.target, operand.negated ^ negate))
                .copied()
                .unwrap_or_default();
            // Konclude's priority strategy normalizes against the original
            // OR operand count, not this task's independently filtered
            // survivor count.
            let max_branch_count = original_operand_count.max(1) as f64;
            let branch_number = (alternative + 1) as f64;
            if statistics.expanded == 0 && statistics.clashed == 0 && statistics.satisfiable == 0 {
                return -branch_number / (10.0 * max_branch_count);
            }

            let expanded = statistics.expanded as f64;
            let clash_factor = if statistics.expanded > 0 {
                (statistics.clashed as f64 / expanded).clamp(0.0, 1.0)
            } else if statistics.clashed > 0 {
                1.0 / (statistics.clashed as f64 * 10.0)
            } else {
                0.0
            };
            let satisfiable_factor = if statistics.expanded > 0 {
                (statistics.satisfiable as f64 / expanded).clamp(0.0, 1.0)
            } else if statistics.satisfiable > 0 {
                1.0 / (statistics.satisfiable as f64 * 10.0)
            } else {
                0.0
            };
            let expansion_bonus = if statistics.expanded > 0 {
                1.0 / (expanded * 10_000.0)
            } else {
                0.0
            };
            (satisfiable_factor - clash_factor) / 10.0 + expansion_bonus
                - branch_number / (100_000.0 * max_branch_count)
        };
        order.sort_by(|left, right| {
            score(*right)
                .total_cmp(&score(*left))
                .then_with(|| left.cmp(right))
        });
        if self.conf_or_reverse {
            order.reverse();
        }
        order
    }

    /// DDB: mint ONE non-deterministic track point PER ALTERNATIVE of a branch
    /// point, upfront (Konclude's per-forked-task
    /// `createNonDeterministicDependencyTrackPointBranch` in `executeORBranching`
    /// / `createMergeBranchingTask`; each child task's used branch tree node is a
    /// fresh copy of the parent's, so every sibling gets branching tag = parent
    /// level + 1 on its OWN branch node). Upfront minting is a soundness
    /// requirement: the u29 propagation reads "all sibling track points clashed"
    /// as "the whole decision is refuted"; lazily-minted siblings would fire it
    /// early. Shared by the OR rule and the at-most merge branching. Konclude
    /// creates these non-deterministic track points whenever dependency building
    /// is enabled; dependency-directed backjumping only changes how a later clash
    /// consumes them. Empty only when dependency building is off or the decision
    /// has no dependency node.
    pub(super) fn ht_mint_alternative_track_points(
        &mut self,
        dependency_node: DependencyId,
        n_alternatives: usize,
        parent_used_branch_node: BranchNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> Vec<TrackPointId> {
        if !self.conf_build_dependencies || dependency_node.is_none() {
            return Vec::new();
        }
        let (parent_level, parent_root) = if parent_used_branch_node.is_some() {
            let pb = calc_alg_context
                .process_context()
                .branch_node(parent_used_branch_node);
            (pb.get_branching_level(), pb.get_root_node())
        } else {
            (0, BranchNodeId::NONE)
        };
        (0..n_alternatives)
            .map(|_| {
                let pc = calc_alg_context.process_context_mut();
                // `initBranchingChildNode`: tag = parent level, then
                // `branchingIncrement` bumps it to parent level + 1.
                let alt_branch = pc.alloc_branch_node(BranchTreeNode {
                    process_tag: parent_level,
                    parent_node: parent_used_branch_node,
                    root_node: parent_root,
                    branched_dep_track_point: Id::NONE,
                    sat_calc_task: INVALID,
                });
                let tp = pc.dependency_track_point_branch(dependency_node);
                pc.branch_node_mut(alt_branch).branching_increment(tp);
                // `CNonDeterministicDependencyTrackPoint::initBranch`.
                let level = pc.branch_node(alt_branch).get_branching_level();
                let t = pc.track_point_mut(tp);
                t.branch_node = alt_branch;
                t.add_maximum_branching_tag_candidate(level);
                tp
            })
            .collect()
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::planORProcessing`.
    ///
    /// PORT-PENDING: too entangled — scans the disjunction operand list against the
    /// node's reapply concept-label set, checks saturated-clash flags, builds a
    /// `CBranchingORProcessingRestrictionSpecification` (allocator), drives branch
    /// triggering, and routes to the queue/trigger helper units. Faithful outline
    /// (cpp 16493-16664):
    ///
    /// ```text
    /// conDes = conProDes.getConceptDescriptor(); concept = conDes.getConcept(); depTrackPoint = conProDes.getDependencyTrackPoint()
    /// procRest = conProDes.getProcessingRestrictionSpecification()
    /// if initializeORProcessing(processIndi, conProDes, negate, plannedBranchingProcessRestriction, ctx): return true
    /// if !procRest:   // first time the concept is processed
    ///     conSet = processIndi.getReapplyConceptLabelSet(false)
    ///     firstNotContained = secondNotContained = containedOperand = null; clashConDesLinker = null
    ///     opLinker = concept.getOperandList(); disjunctBranchStats from concept process-data branching stats
    ///     while opLinker && !containedOperand:
    ///         opConcept = opLinker.getData(); opConNegation = opLinker.isNegated() ^ negate
    ///         contains = conSet.getConceptDescriptor(opConcept, ...)
    ///         if !contains && getAdditionalDisjunctCheckingConcept(...): contains = conSet.getConceptDescriptor(altConcept, ...)
    ///         if !contains:
    ///             if !hasSaturatedClashedFlagForConcept(opConcept, opNeg, ctx): record first/second-not-contained operand (+branch stats)
    ///         else:
    ///             if containsNegation == opCheckingNegation: containedOperand = opLinker
    ///             else: clashConDesLinker = createClashedConceptDescriptor(...)
    ///         opLinker = opLinker.getNext(); advance disjunctBranchStats
    ///     if containedOperand || !secondNotContained:    // only one branch applicable
    ///         if plannedBranchingProcessRestriction: alloc+init CBranchingORProcessingRestrictionSpecification; set contained/first/second/stats; addClashedConceptDescriptors; *out = it
    ///         return false
    ///     else:    // try to trigger branching
    ///         alloc+init branchORProcRest; set first/second/stats + clash descriptors
    ///         if mConfBranchTriggering: conRoleBranchTrigger = conProcessData.getConceptRoleBranchTrigger()
    ///         if conRoleBranchTrigger: conRoleBranchTrigger = searchNextConceptRoleBranchTrigger(processIndi, it, ctx)
    ///         if conRoleBranchTrigger: branchORProcRest.setConceptRoleBranchingTrigger(next); installConceptRoleBranchTrigger(...); return true
    ///         else: priorityOffset = ...getPriorityOffsetForDisjunctionDelayedProcessing(...); branchORProcRest.setPriorityOffset; addConceptRestrictedToProcessingQueue(...); return true
    /// else:   // OR concept already considered before — try triggering again
    ///     branchORProcRest = (CBranchingORProcessingRestrictionSpecification*)procRest
    ///     if branchORProcRest.getContainedOperand() || !branchORProcRest.getSecondNotPosAndNegContainedOperand(): *out = it; return false
    ///     conRoleBranchTrigger = branchORProcRest.getConceptRoleBranchingTrigger()
    ///     if !conRoleBranchTrigger: if plannedBranchingProcessRestriction: *out = it; return false
    ///     else: conRoleBranchTrigger = searchNextConceptRoleBranchTrigger(processIndi, it, ctx)
    ///     alloc+init nextBranchORProcRest from branchORProcRest
    ///     if conRoleBranchTrigger: nextBranchORProcRest.setConceptRoleBranchingTrigger(next); installConceptRoleBranchTrigger(...); return true
    ///     else: priorityOffset = ...; nextBranchORProcRest.setPriorityOffset; setConceptRoleBranchingTrigger(null); addConceptRestrictedToProcessingQueue(...); return true
    /// ```
    pub fn plan_or_processing(
        &mut self,
        process_indi: NodeId,
        con_pro_des: ConProcDescId,
        negate: bool,
        planned_branching_process_restriction: &mut RestrictionSpecId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let (con_des, dep_track_point, proc_rest) = {
            let cpd = calc_alg_context
                .process_context()
                .con_proc_desc(con_pro_des);
            (
                cpd.get_concept_descriptor(),
                cpd.get_dependency_track_point(),
                cpd.get_processing_restriction_specification(),
            )
        };
        let concept = calc_alg_context
            .process_context()
            .con_desc(con_des)
            .get_concept();

        if self.initialize_or_processing(process_indi, con_pro_des, negate, calc_alg_context) {
            return true;
        }

        // A delayed OR with no remaining concept-role trigger executes from
        // the stored restriction specification.  This is Konclude's
        // `procRest` re-entry arm (cpp 16680-16696).
        if proc_rest.is_some()
            && calc_alg_context
                .process_context()
                .restriction_spec(proc_rest)
                .is_branching_or
        {
            *planned_branching_process_restriction = proc_rest;
            return false;
        }

        let label_set = calc_alg_context
            .process_context()
            .node(process_indi)
            .use_reapply_con_label_set;
        let operands = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operand_list()
            .to_vec();
        let mut survivors = Vec::new();
        let mut contained_operand = None;
        let mut clashes = Id::NONE;

        for operand in operands {
            let effective_negation = operand.negated ^ negate;
            let mut checking_concept = operand.target;
            let mut checking_negation = effective_negation;
            let mut contained_negation = false;
            let mut contains = label_set.is_some()
                && self.label_set_contains_concept_get_negated_resolved(
                    label_set,
                    checking_concept,
                    Some(&mut contained_negation),
                    calc_alg_context,
                );
            if !contains
                && self.get_additional_disjunct_checking_concept(
                    operand.target,
                    effective_negation,
                    Some(&mut checking_concept),
                    Some(&mut checking_negation),
                    calc_alg_context,
                )
            {
                contains = label_set.is_some()
                    && self.label_set_contains_concept_get_negated_resolved(
                        label_set,
                        checking_concept,
                        Some(&mut contained_negation),
                        calc_alg_context,
                    );
            }

            if contains {
                if contained_negation == checking_negation {
                    contained_operand = Some(operand);
                    break;
                }

                // Preserve the opposite-polarity descriptor as a dependency
                // for ORONLYOPTION/clash construction.
                let tag = calc_alg_context
                    .ontology_arenas()
                    .concept(checking_concept)
                    .get_concept_tag();
                let mut contained_des = Id::NONE;
                let mut contained_tp = Id::NONE;
                let contained_with_dependency = {
                    let process_context = calc_alg_context.process_context();
                    process_context
                        .label_set(label_set)
                        .get_concept_descriptor_by_tag_in_context(
                            process_context,
                            tag,
                            &mut contained_des,
                            &mut contained_tp,
                        )
                };
                if contained_with_dependency && contained_des.is_some() {
                    let mut node = process_indi;
                    clashes = self.create_clashed_concept_descriptor(
                        clashes,
                        &mut node,
                        contained_des,
                        contained_tp,
                        calc_alg_context,
                    );
                }
            } else if !self.has_saturated_clashed_flag_for_concept(
                checking_concept,
                checking_negation,
                calc_alg_context,
            ) {
                survivors.push(operand);
            }
        }

        let mut rest =
            super::super::process::satellites::BranchingMergingProcessingRestrictionSpecification::new(
                INVALID,
            );
        rest.init_branching_or_processing_restriction(None);
        rest.or_contained_operand = contained_operand;
        rest.or_operands = survivors;
        rest.or_clashed_concept_descriptors = clashes;
        let rest_id = calc_alg_context
            .process_context_mut()
            .alloc_restriction_spec(rest);

        if super::ht_or_trace_enabled() {
            let rest = calc_alg_context.process_context().restriction_spec(rest_id);
            eprintln!(
                "OR-PLAN concept={} contained={} survivors={} clashes={}",
                calc_alg_context
                    .ontology_arenas()
                    .concept(concept)
                    .get_concept_tag(),
                rest.or_contained_operand.is_some(),
                rest.or_operands.len(),
                rest.or_clashed_concept_descriptors.raw,
            );
        }

        if contained_operand.is_some()
            || calc_alg_context
                .process_context()
                .restriction_spec(rest_id)
                .or_operands
                .len()
                < 2
        {
            *planned_branching_process_restriction = rest_id;
            return false;
        }

        // No typed CConceptRoleBranchingTrigger is attached yet.  This is the
        // exact no-trigger arm: park the planned OR with the delayed-processing
        // offset, then execute it when it is dequeued again.
        let priority_offset = calc_alg_context
            .base
            .used_concept_priority_strategy()
            .expect("concept priority strategy")
            .get_priority_offset_for_disjunction_delayed_processing(con_des, process_indi);
        calc_alg_context
            .process_context_mut()
            .restriction_spec_mut(rest_id)
            .set_priority_offset(priority_offset);
        let queue = calc_alg_context
            .process_context_mut()
            .node_concept_processing_queue(process_indi, true);
        self.add_concept_restricted_to_processing_queue_offset(
            con_des,
            dep_track_point,
            queue,
            process_indi,
            true,
            rest_id.raw,
            priority_offset,
            calc_alg_context,
        );
        true
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::prepareBranchedTaskProcessing`.
    ///
    /// The C++ body is a single delegation to `addIndividualToProcessingQueue`, which
    /// is an unported sibling unit needing arena access; preserved as a deferred call.
    /// Faithful outline (cpp 17201-17203):
    ///
    /// ```text
    /// addIndividualToProcessingQueue(individual, ctx)
    /// ```
    pub fn prepare_branched_task_processing(
        &mut self,
        individual: NodeId,
        new_task: Id<SatisfiableCalculationTask>,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[api]: addIndividualToProcessingQueue(individual, calcAlgContext)
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getLinkProcessingRestriction`.
    ///
    /// PORT-PENDING: casts the concept descriptor's processing-restriction spec to a
    /// `CLinkProcessingRestrictionSpecification` and reads its link restriction; both
    /// the descriptor read and the link-restriction-spec subtype need arena access.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: the C++ method has no context parameter (it
    /// dereferences the raw `conProDes` pointer directly); the id model forces an
    /// arena, so a `&CalculationAlgorithmContextBase` is threaded in to resolve it.
    /// Faithful outline (cpp 17286-17294):
    ///
    /// ```text
    /// procRestSpec = conProDes.getProcessingRestrictionSpecification(); restLink = null
    /// if procRestSpec: restLink = ((CLinkProcessingRestrictionSpecification*)procRestSpec).getLinkRestriction()
    /// return restLink
    /// ```
    pub fn get_link_processing_restriction(
        &self,
        con_pro_des: ConProcDescId,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> EdgeId {
        let proc_rest_spec = calc_alg_context
            .process_context()
            .con_proc_desc(con_pro_des)
            .get_processing_restriction_specification();
        if proc_rest_spec.is_some() {
            calc_alg_context
                .process_context()
                .restriction_spec(proc_rest_spec)
                .get_link_restriction()
        } else {
            EdgeId::NONE
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::propagateProcessingRestrictionToAncestor`.
    ///
    /// Pure sibling delegation (cpp 19762-19764) — ported in full.
    pub fn propagate_processing_restriction_to_ancestor(
        &mut self,
        indi: NodeId,
        add_restriction_flags: Cint64,
        recursive: bool,
        while_not_contains_flags: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        self.propagate_adding_processing_restriction_to_ancestor(
            indi,
            add_restriction_flags,
            recursive,
            while_not_contains_flags,
            calc_alg_context,
        );
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::propagateAddingProcessingRestrictionToAncestor`.
    ///
    /// Walks to the ancestor node and (recursively) adds restriction flags.
    /// cpp 19767-19778.
    ///
    /// ```text
    /// if indi.hasIndividualAncestor():
    ///     ancIndi = getAncestorIndividual(indi, ctx)
    ///     if !ancIndi.hasPartialProcessingRestrictionFlags(whileNotContainsFlags):
    ///         locAncIndi = getLocalizedIndividual(ancIndi, false, ctx)
    ///         locAncIndi.addProcessingRestrictionFlags(addRestrictionFlags)
    ///         if recursive: propagateAddingProcessingRestrictionToAncestor(locAncIndi, addRestrictionFlags, recursive, whileNotContainsFlags, ctx)
    /// ```
    pub fn propagate_adding_processing_restriction_to_ancestor(
        &mut self,
        indi: NodeId,
        add_restriction_flags: Cint64,
        recursive: bool,
        while_not_contains_flags: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        if calc_alg_context
            .process_context()
            .node(indi)
            .has_individual_ancestor()
        {
            let mut test_indi = indi;
            let anc_indi = self.get_ancestor_individual(&mut test_indi, calc_alg_context);
            if anc_indi.is_some()
                && !calc_alg_context
                    .process_context()
                    .node(anc_indi)
                    .has_partial_processing_restriction_flags(while_not_contains_flags)
            {
                let loc_anc_indi = self.get_localized_individual(anc_indi, false, calc_alg_context);
                calc_alg_context
                    .process_context_mut()
                    .node_mut(loc_anc_indi)
                    .add_processing_restriction_flags(add_restriction_flags);
                if recursive {
                    self.propagate_adding_processing_restriction_to_ancestor(
                        loc_anc_indi,
                        add_restriction_flags,
                        recursive,
                        while_not_contains_flags,
                        calc_alg_context,
                    );
                }
            }
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::propagateProcessingRestrictionToSuccessors`.
    ///
    /// Pure sibling delegation (cpp 19783-19785) — ported in full.
    pub fn propagate_processing_restriction_to_successors(
        &mut self,
        indi: NodeId,
        add_restriction_flags: Cint64,
        recursive: bool,
        while_not_contains_flags: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        self.propagate_adding_processing_restriction_to_successors(
            indi,
            add_restriction_flags,
            recursive,
            while_not_contains_flags,
            calc_alg_context,
        );
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::propagateAddingProcessingRestrictionToSuccessors`.
    ///
    /// Iterates strictly deeper successor links and recursively adds restriction
    /// flags while the stop-mask is absent. Uses the existing successor/localization
    /// siblings for the C++ pointer-resolution steps.
    pub fn propagate_adding_processing_restriction_to_successors(
        &mut self,
        indi: NodeId,
        add_restriction_flags: Cint64,
        recursive: bool,
        while_not_contains_flags: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let mut succ_it = calc_alg_context
            .process_context()
            .node_successor_iterator(indi);
        let anc_depth = calc_alg_context
            .process_context()
            .node(indi)
            .individual_ancestor_depth();
        while succ_it.has_next() {
            let succ_link = succ_it.next_link(true);
            let mut source_indi = indi;
            let succ_indi =
                self.get_successor_individual(&mut source_indi, succ_link, calc_alg_context);
            if succ_indi.is_some()
                && calc_alg_context
                    .process_context()
                    .node(succ_indi)
                    .individual_ancestor_depth()
                    > anc_depth
                && !calc_alg_context
                    .process_context()
                    .node(succ_indi)
                    .has_partial_processing_restriction_flags(while_not_contains_flags)
            {
                let loc_succ_indi =
                    self.get_localized_individual(succ_indi, false, calc_alg_context);
                calc_alg_context
                    .process_context_mut()
                    .node_mut(loc_succ_indi)
                    .add_processing_restriction_flags(add_restriction_flags);
                if recursive {
                    self.propagate_adding_processing_restriction_to_successors(
                        loc_succ_indi,
                        add_restriction_flags,
                        recursive,
                        while_not_contains_flags,
                        calc_alg_context,
                    );
                }
            }
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::propagateClearingProcessingRestrictionToSuccessors`.
    ///
    /// Mirror of the adding variant, clearing flags while the required mask is
    /// present on strictly deeper successors.
    pub fn propagate_clearing_processing_restriction_to_successors(
        &mut self,
        indi: NodeId,
        clear_restriction_flags: Cint64,
        recursive: bool,
        while_contains_flags: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let mut succ_it = calc_alg_context
            .process_context()
            .node_successor_iterator(indi);
        let anc_depth = calc_alg_context
            .process_context()
            .node(indi)
            .individual_ancestor_depth();
        while succ_it.has_next() {
            let succ_link = succ_it.next_link(true);
            let mut source_indi = indi;
            let succ_indi =
                self.get_successor_individual(&mut source_indi, succ_link, calc_alg_context);
            if succ_indi.is_some()
                && calc_alg_context
                    .process_context()
                    .node(succ_indi)
                    .individual_ancestor_depth()
                    > anc_depth
                && calc_alg_context
                    .process_context()
                    .node(succ_indi)
                    .has_partial_processing_restriction_flags(while_contains_flags)
            {
                let loc_succ_indi =
                    self.get_localized_individual(succ_indi, false, calc_alg_context);
                calc_alg_context
                    .process_context_mut()
                    .node_mut(loc_succ_indi)
                    .clear_processing_restriction_flags(clear_restriction_flags);
                if recursive {
                    self.propagate_clearing_processing_restriction_to_successors(
                        loc_succ_indi,
                        clear_restriction_flags,
                        recursive,
                        while_contains_flags,
                        calc_alg_context,
                    );
                }
            }
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::propagateIndividualProcessedAndReactivate`.
    ///
    /// Marks the node processing-completed and, when all ancestors are processed
    /// (or the node has no ancestor), delegates reactivation to unit 4. The
    /// delegated `search_reactivate_individuals_processed_propagated` still holds
    /// its own lower-level W3-DEFERs.
    pub fn propagate_individual_processed_and_reactivate(
        &mut self,
        indi: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        if self.opt_processed_node_propagation
            || (self.opt_processed_cons_node_propagation
                && calc_alg_context
                    .process_context()
                    .node(indi)
                    .has_partial_processing_restriction_flags(
                        IndividualProcessNode::PRF_CONSNODEPREPARATIONINDINODE,
                    ))
        {
            if !calc_alg_context
                .process_context()
                .node(indi)
                .has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_PROCESSINGCOMPLETED,
                )
            {
                calc_alg_context
                    .process_context_mut()
                    .node_mut(indi)
                    .add_processing_restriction_flags(
                        IndividualProcessNode::PRF_PROCESSINGCOMPLETED,
                    );
                let mut process_indi = indi;
                if calc_alg_context
                    .process_context()
                    .node(indi)
                    .has_partial_processing_restriction_flags(
                        IndividualProcessNode::PRF_ANCESTORALLPROCESSED,
                    )
                    || !self.has_ancestor_individual_node(&mut process_indi, calc_alg_context)
                {
                    self.search_reactivate_individuals_processed_propagated(indi, calc_alg_context);
                }
            }
        }
    }
}

#[cfg(test)]
mod branch_learning_tests {
    use super::*;
    use crate::konclude_ht::completion::algorithm::{
        CompletionTaskHandleAlgorithm, OrBranchLearningStats,
    };

    #[test]
    fn cache_oriented_order_is_cold_stable_then_prefers_satisfiable_operand() {
        let mut algorithm = CompletionTaskHandleAlgorithm::new();
        algorithm.conf_cache_oriented_or_ordering = true;
        let disjunction = ConceptId::new(7);
        let operands = vec![
            NegLink {
                target: ConceptId::new(70),
                negated: false,
            },
            NegLink {
                target: ConceptId::new(71),
                negated: false,
            },
            NegLink {
                target: ConceptId::new(72),
                negated: false,
            },
        ];
        assert_eq!(
            algorithm.ht_or_branch_alternative_order(disjunction, &operands, false, 3),
            vec![0, 1, 2]
        );

        algorithm.or_branch_learning_stats.insert(
            (disjunction, operands[0].target, false),
            OrBranchLearningStats {
                expanded: 1,
                clashed: 1,
                satisfiable: 0,
            },
        );
        algorithm.or_branch_learning_stats.insert(
            (disjunction, operands[2].target, false),
            OrBranchLearningStats {
                expanded: 1,
                clashed: 0,
                satisfiable: 1,
            },
        );
        assert_eq!(
            algorithm.ht_or_branch_alternative_order(disjunction, &operands, false, 3),
            vec![2, 1, 0],
            "learned SAT-minus-clash rate must dominate the stable cold tie"
        );
    }

    #[test]
    fn cache_oriented_order_uses_equal_depth_expansion_bonus() {
        let mut algorithm = CompletionTaskHandleAlgorithm::new();
        algorithm.conf_cache_oriented_or_ordering = true;
        let disjunction = ConceptId::new(9);
        let operands = vec![
            NegLink {
                target: ConceptId::new(90),
                negated: false,
            },
            NegLink {
                target: ConceptId::new(91),
                negated: false,
            },
            NegLink {
                target: ConceptId::new(92),
                negated: false,
            },
        ];
        algorithm.or_branch_learning_stats.insert(
            (disjunction, operands[0].target, false),
            OrBranchLearningStats {
                expanded: 2,
                clashed: 0,
                satisfiable: 0,
            },
        );
        algorithm.or_branch_learning_stats.insert(
            (disjunction, operands[1].target, false),
            OrBranchLearningStats {
                expanded: 1,
                clashed: 0,
                satisfiable: 0,
            },
        );
        assert_eq!(
            algorithm.ht_or_branch_alternative_order(disjunction, &operands, false, 3),
            vec![1, 0, 2],
            "Konclude's 1/(expanded*10000) bonus must break equal-rate ties"
        );
    }
}
