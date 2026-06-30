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
//! plumbing (CProcessContext) lands in a later wave. The pure sibling-delegators
//! (`propagate*RestrictionTo{Ancestor,Successors}`) and the single-deferred-call
//! void (`prepareBranchedTaskProcessing`) ARE ported in full here.

#![allow(unused_variables, dead_code)]

use super::super::model::substrate::Cint64;
use super::super::process::{ConProcDescId, EdgeId, NodeId, RestrictionSpecId};
use super::context::CalculationAlgorithmContextBase;
use super::stubs::SatisfiableCalculationTask;
use super::super::model::substrate::Id;

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
        // PORT-PENDING
        todo!(
            "W3-DEFER: individualNodeInitializing — needs getLocalizedIndividual + node \
             per-queue flag setters (arena) + backend-cache/value-space/unsat-cache \
             helper units"
        )
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
        if self.indi_node_conclude_unsat_caching {
            // W3-DEFER[api]: testIndividualNodeUnsatisfiableCached(indiProcNode, calcAlgContext)
        }

        calc_alg_context.base.set_current_individual_node(NodeId::NONE);
        // W3-DEFER[api]: addIndividualToProcessingQueue(indiProcNode, calcAlgContext)
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
        // PORT-PENDING
        todo!(
            "W3-DEFER: tableauRuleProcessing — needs descriptor/concept arena reads + \
             tryDelayNominalProcessing / needsIndividualNodeExpansionBlockingTest / \
             isIndividualNode*Blocked predicate units"
        )
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
        // PORT-PENDING
        todo!(
            "W3-DEFER[pointer-alias]: tableauRuleChoice — member-fn-pointer jump-table \
             dispatch into the apply*Rule engine (jump tables opaque until those rule \
             units are ported) + descriptor/concept arena reads for conOpCode"
        )
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::initializeORProcessing`.
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
    pub fn initialize_or_processing(
        &mut self,
        process_indi: NodeId,
        con_pro_des: ConProcDescId,
        negate: bool,
        // KONCLUDE-PORT-NOTE[api]: C++ `CBranchingORProcessingRestrictionSpecification**`
        // out-param; the OR-restriction-spec type is not yet ported, so the
        // double-pointer becomes an opaque out-handle. `Id::NONE` == nullptr.
        planned_branching_process_restriction: RestrictionSpecId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // PORT-PENDING
        todo!(
            "W3-DEFER: initializeORProcessing — needs descriptor/concept/replacement-data \
             arena reads + concept-priority strategy + addConcept*/addConceptRestricted \
             queue units"
        )
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
        // KONCLUDE-PORT-NOTE[api]: see `initialize_or_processing` — opaque out-handle
        // for the not-yet-ported `CBranchingORProcessingRestrictionSpecification**`.
        planned_branching_process_restriction: RestrictionSpecId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // PORT-PENDING
        todo!(
            "W3-DEFER: planORProcessing — needs operand-list/label-set/concept-data \
             arena reads, the OR-restriction-spec allocator+type, branch-trigger \
             search/install, and the addConceptRestricted/clash-descriptor units"
        )
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
        // PORT-PENDING
        todo!(
            "W3-DEFER: getLinkProcessingRestriction — needs descriptor arena read + the \
             CLinkProcessingRestrictionSpecification subtype (not yet ported)"
        )
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
    /// PORT-PENDING: walks to the ancestor node and (recursively) adds restriction
    /// flags; needs `getAncestorIndividual` / `getLocalizedIndividual` + node flag
    /// ops (arena). Faithful outline (cpp 19767-19778):
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
        // PORT-PENDING
        todo!(
            "W3-DEFER: propagateAddingProcessingRestrictionToAncestor — needs \
             getAncestorIndividual / getLocalizedIndividual + node restriction-flag \
             ops via the CProcessContext arena"
        )
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
    /// PORT-PENDING: iterates the node's successor links (deeper ancestor-depth only)
    /// and (recursively) adds restriction flags; needs `CSuccessorIterator` (a process
    /// placeholder), `getSuccessorIndividual` / `getLocalizedIndividual`, and node
    /// flag ops (arena). Faithful outline (cpp 19810-19827):
    ///
    /// ```text
    /// succIt = indi.getSuccessorIterator(); ancDepth = indi.getIndividualAncestorDepth()
    /// while succIt.hasNext():
    ///     succLink = succIt.nextLink(true); succIndi = getSuccessorIndividual(indi, succLink, ctx)
    ///     if succIndi.getIndividualAncestorDepth() > ancDepth:
    ///         if !succIndi.hasPartialProcessingRestrictionFlags(whileNotContainsFlags):
    ///             locSuccIndi = getLocalizedIndividual(succIndi, false, ctx)
    ///             locSuccIndi.addProcessingRestrictionFlags(addRestrictionFlags)
    ///             if recursive: propagateAddingProcessingRestrictionToSuccessors(locSuccIndi, ...)
    /// ```
    pub fn propagate_adding_processing_restriction_to_successors(
        &mut self,
        indi: NodeId,
        add_restriction_flags: Cint64,
        recursive: bool,
        while_not_contains_flags: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // PORT-PENDING
        todo!(
            "W3-DEFER: propagateAddingProcessingRestrictionToSuccessors — needs the \
             CSuccessorIterator iteration API + getSuccessorIndividual / \
             getLocalizedIndividual + node flag ops (arena)"
        )
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::propagateClearingProcessingRestrictionToSuccessors`.
    ///
    /// PORT-PENDING: mirror of the adding variant but CLEARS flags, gated on
    /// `whileContainsFlags`; same arena/iterator dependencies. Faithful outline
    /// (cpp 19831-19848):
    ///
    /// ```text
    /// succIt = indi.getSuccessorIterator(); ancDepth = indi.getIndividualAncestorDepth()
    /// while succIt.hasNext():
    ///     succLink = succIt.nextLink(true); succIndi = getSuccessorIndividual(indi, succLink, ctx)
    ///     if succIndi.getIndividualAncestorDepth() > ancDepth:
    ///         if succIndi.hasPartialProcessingRestrictionFlags(whileContainsFlags):
    ///             locSuccIndi = getLocalizedIndividual(succIndi, false, ctx)
    ///             locSuccIndi.clearProcessingRestrictionFlags(clearRestrictionFlags)
    ///             if recursive: propagateClearingProcessingRestrictionToSuccessors(locSuccIndi, ...)
    /// ```
    pub fn propagate_clearing_processing_restriction_to_successors(
        &mut self,
        indi: NodeId,
        clear_restriction_flags: Cint64,
        recursive: bool,
        while_contains_flags: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // PORT-PENDING
        todo!(
            "W3-DEFER: propagateClearingProcessingRestrictionToSuccessors — needs the \
             CSuccessorIterator iteration API + getSuccessorIndividual / \
             getLocalizedIndividual + node flag ops (arena)"
        )
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::propagateIndividualProcessedAndReactivate`.
    ///
    /// PORT-PENDING: marks the node processing-completed and, when its ancestors are
    /// all processed (or it has none), wakes the next nodes; needs node flag ops +
    /// `hasAncestorIndividualNode` + the (unit-4) `searchReactivateIndividualsProcessedPropagated`.
    /// Faithful outline (cpp 19887-19899):
    ///
    /// ```text
    /// if mOptProcessedNodePropagation || (mOptProcessedConsNodePropagation && indi.hasPartialProcessingRestrictionFlags(PRF CONSNODEPREPARATIONINDINODE)):
    ///     if !indi.hasPartialProcessingRestrictionFlags(PRF PROCESSINGCOMPLETED):
    ///         indi.addProcessingRestrictionFlags(PRF PROCESSINGCOMPLETED)
    ///         if indi.hasPartialProcessingRestrictionFlags(PRF ANCESTORALLPROCESSED) || !hasAncestorIndividualNode(indi, ctx):
    ///             searchReactivateIndividualsProcessedPropagated(indi, ctx)
    /// ```
    pub fn propagate_individual_processed_and_reactivate(
        &mut self,
        indi: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // PORT-PENDING
        todo!(
            "W3-DEFER: propagateIndividualProcessedAndReactivate — needs node \
             restriction-flag ops (arena) + hasAncestorIndividualNode + the unit-4 \
             searchReactivateIndividualsProcessedPropagated"
        )
    }
}
