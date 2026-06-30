//! `completion::u26` — Incremental-expansion / compatibility family
//! (port unit #26 of 36).
//!
//! Faithful port of the 20 methods that the manifest (`01-completion-methods.md`,
//! "Unit 26") groups under the incremental (re)classification subsystem of Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`.
//! cpp source line ranges (1-based) per method are noted on each item.
//!
//! Methods (cpp order):
//!   * `initializeIncrementalIndividualExpansion`              [2937–3052]
//!   * `getNextIncrementalExpansionIndividual`                 [3058–3071]
//!   * `incrementalNodeExpansion`                              [3075–3084]
//!   * `requiresIncrementalNodeExpansion`                      [3088–3094]
//!   * `pruneIncrementalRemovedSuccessors`                     [3384–3431]
//!   * `checkCompatibilityUpdateDirectlyChangedPropagation`   [3476–3493]
//!   * `linkCreationDirectlyChangedNeighbourConnectionUpdate`  [3497–3508]
//!   * `establishDirectlyChangedNeighbourConnection`          [3512–3529]
//!   * `propagateDirectlyChangedNeighbourNodeConnection`      [3534–3634]
//!   * `searchDirectlyChangedNeighbourNodeConnection`         [3639–3702]
//!   * `clearDirectlyChangedNeighbourConnection`              [3706–3718]
//!   * `clearPropagatedDirectlyChangedNeighbourConnection`    [3722–3761]
//!   * `hasCompatibleConceptSetReuse`                         [4955–4972]
//!   * `hasCompatibleConceptSetSignature`                     [5960–6004]
//!   * `generateDebugIncrementalExpansionString`              [8014–8036]
//!   * `areVariablePropagationBindingsCompatible`             [17990–18013]
//!   * `getConceptsForCompatibleVariablePropagationBindings`  [18017–18050]
//!   * `getBindingsCompatibleConceptSetsHashValue`            [18262–18277]
//!   * `addIndividualToIncrementalCompatibilityCheckingQueue`  [27554–27563]
//!   * `addIndividualToIncrementalExpansionQueue`             [27565–27584]
//!
//! KONCLUDE-PORT-NOTE[ownership]: each method is a member of
//! `CCalculationTableauCompletionTaskHandleAlgorithm`, so it becomes `&mut self`
//! plus the threaded per-thread context `calc_alg_context: &mut
//! CalculationAlgorithmContextBase` (the C++ `CCalculationAlgorithmContextBase*`).
//! `CIndividualProcessNode*` value params become arena `NodeId`s resolved against
//! the context-owned `ProcessContext`
//! (`calc_alg_context.process_context().node(id)` for reads,
//! `…process_context_mut().node_mut(id)` for mutation — the W3.5 convention);
//! `CIndividualProcessNode*&` out/in-out → `&mut NodeId`; `CIndividual*` →
//! `IndividualId`; `CConcept*` → `ConceptId` (resolved against
//! `calc_alg_context.ontology_arenas()`); `CReapplyConceptLabelSet*` → `LabelSetId`.
//!
//! Deferral landscape. This unit is dominated by the per-node
//! `CIndividualNodeIncrementalExpansionData` satellite (the
//! `getIncrementalExpansionData(bool)` lazy getter and its
//! `isPreviousCompletionGraphCompatible` / `isDirectlyChanged` /
//! `hasDirectlyChangedNeighbourConnection` / `setDirectlyChangedNeighbourConnectionNode`
//! / `addNeighbourPropagatedDirectlyChanged` / incremental-expansion-list state) and
//! by `mIncExpHandler`
//! (`CIncrementalCompletionGraphCompatibleExpansionHandler`, an Algorithm-layer
//! stub). The satellite is `process::stubs::IncExpDataId`, a zero-size marker with no
//! method bodies and no node accessor yet (W2-DEFER[api]). Sixteen of the twenty
//! methods bottom out start-to-finish in that satellite (and in the
//! variable-binding-path subsystem `CVariableBindingPath` / `CVariableBinding`,
//! likewise unported), so they are kept PORT-PENDING with the faithful signature and
//! a structural transcription of the C++; logic is documented, never silently
//! dropped.
//!
//! Four methods port in full / as faithful control flow against the available
//! substrate:
//!   * `getBindingsCompatibleConceptSetsHashValue` (pure order-independent hash over
//!     concept tags) — FULLY PORTED;
//!   * `addIndividualToIncrementalCompatibilityCheckingQueue` (node queue-flag guard
//!     + databox queue getter) — FULLY PORTED bar the deferred `insertProcessIndiviudal`
//!     queue-method body + `STATINC` counter (the same W3-DEFER[api] shape as u04);
//!   * `linkCreationDirectlyChangedNeighbourConnectionUpdate` (pure sibling-call
//!     control flow over `establish*` / `propagate*`) — FULLY PORTED;
//!   * `incrementalNodeExpansion` (outer driver structure; the inner expand block is
//!     the deferred `getUpToDateIndividual` + queue re-add).

#![allow(dead_code)]
#![allow(unused_variables)]

use super::super::model::substrate::{Cint64, Id};
use super::super::model::{ConceptId, IndividualId};
use super::super::process::varbind::{VarBindingPathId, VariableBindingPath};
use super::super::process::{LabelSetId, NodeId};
use super::context::CalculationAlgorithmContextBase;

impl super::algorithm::CompletionTaskHandleAlgorithm {
    // =======================================================================
    // Incremental individual-expansion initialization (cpp 2937–3052).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::initializeIncrementalIndividualExpansion`.
    /// cpp 2937–3052.
    ///
    /// One-time build of the node's incremental-expansion work list against the
    /// previous deterministic completion graph: (a) for the previous-graph
    /// correspondence node, replays every previous concept whose dependencies are all
    /// unchanged (`areAllDependentFactsUnchanged` → `addConceptToIndividual`); then
    /// (b) breadth-first walks the previous graph from this node over successors /
    /// connection-successors / merged individuals, collecting the not-yet-present
    /// nominal individuals into the expansion list; finally marks the list
    /// initialized and enqueues the node for incremental expansion.
    pub fn initialize_incremental_individual_expansion(
        &mut self,
        individual_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // PORT-PENDING: faithful transcription of cpp 2937–3052. Outline:
        //
        //   incExpData = individualNode->getIncrementalExpansionData(false);
        //   if !incExpData || !incExpData->isIncremetnalExpansionListInitialized():
        //     incExpData = individualNode->getIncrementalExpansionData(true);
        //     indiNodeVec = ctx->getUsedProcessingDataBox()->getIndividualProcessNodeVector();
        //     searchingNodeSet  = alloc CPROCESSINGSET<cint64>;   // temp
        //     searchingNodeList = alloc CPROCESSINGLIST<cint64>;  // temp
        //     expList = nullptr;
        //     prevCalcTask = mIncExpHandler->getPreviousDeterministicCompletionGraphTask(ctx);
        //     prevDataBox  = prevCalcTask->getProcessingDataBox();
        //     prevIndiNodeVec = prevDataBox->getIndividualProcessNodeVector();
        //     prevIndiNode = incExpData->getPreviousCompletionGraphCorrespondenceIndividualNode();
        //     if prevIndiNode:
        //       conSet     = individualNode->getReapplyConceptLabelSet(false);
        //       prevConSet = prevIndiNode->getReapplyConceptLabelSet(false);
        //       if conSet && prevConSet:
        //         // merge-walk the two sorted concept-label-set iterators by data tag:
        //         while conSetIt.hasNext() && prevConSetIt.hasNext():
        //           if conTag == prevConTag: advance both;
        //           elif prevConTag < conTag:   // concept missing in current
        //             if areAllDependentFactsUnchanged(individualNode,null,prevConDepTP,prevIndiNodeVec,15,ctx):
        //               addConceptToIndividual(prevConDes->getConcept(),prevConDes->isNegated(),individualNode,prevConDepTP,false,false,ctx);
        //             advance prev;
        //           else: advance cur;
        //         while prevConSetIt.hasNext():  // remaining missing concepts
        //           if areAllDependentFactsUnchanged(...): addConceptToIndividual(...);
        //           advance prev;
        //     searchingNodeSet->insert(individualNode->getIndividualNodeID());
        //     searchingNodeList->append(individualNode->getIndividualNodeID());
        //     while !searchingNodeList->isEmpty():
        //       searchIndiNodeID = searchingNodeList->takeFirst();
        //       searchIndiNode = prevIndiNodeVec->getData(searchIndiNodeID);
        //       if searchIndiNode:
        //         nominalIndi = searchIndiNode->getNominalIndividual();
        //         if searchIndiNode->getIndividualNodeID() != individualNode->getIndividualNodeID() && nominalIndi:
        //           if !indiNodeVec->getData(-nominalIndi->getIndividualID()):
        //             if !expList: expList = incExpData->getIncrementalExpansionList(true);
        //             expList->append(nominalIndi);
        //         if (!nominalIndi && searchIndiNode->hasPartialProcessingRestrictionFlags(PRFSUCCESSORNOMINALCONNECTION))
        //            || searchIndiNodeID == individualNode->getIndividualNodeID():
        //           for succLink in searchIndiNode->getSuccessorIterator():
        //             succIndiID = succLink->getOppositeIndividualID(searchIndiNodeID); enqueue if unseen;
        //           for connIndiID in searchIndiNode->getConnectionSuccessorIterator(): enqueue if unseen;
        //           mergeHash = searchIndiNode->getIndividualMergingHash(false);
        //           if mergeHash: for (id,data) in mergeHash: if data.isMergedWithIndividual(): enqueue if unseen;
        //     incExpData->setIncremetnalExpansionListInitialized(true);
        //     addIndividualToIncrementalExpansionQueue(individualNode,ctx);   // this unit
        //     return true;
        //   return false;
        //
        // Held PORT-PENDING: `CIndividualNodeIncrementalExpansionData`
        // (process::stubs::IncExpDataId — no method bodies / node accessor yet),
        // `mIncExpHandler` (Algorithm-layer stub) + the previous-graph task, and the
        // sibling helpers `areAllDependentFactsUnchanged` (dep unit) /
        // `addConceptToIndividual` (core unit). The label-set iterators
        // (`getConceptLabelSetIterator`), the node successor / connection-successor /
        // merging-hash iterators, and the individual-process-node vector getter are
        // available substrate; they go live with the satellite on the reconcile pass.
        let _ = (individual_node, calc_alg_context);
        false
    }

    // =======================================================================
    // Incremental expansion individual cursor + node expansion
    // (cpp 3058–3094).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getNextIncrementalExpansionIndividual`.
    /// cpp 3058–3071.
    ///
    /// Returns the next previous-graph nominal individual queued for incremental
    /// expansion that does not yet have a node in the current graph (`Id::NONE` when
    /// none remain).
    pub fn get_next_incremental_expansion_individual(
        &mut self,
        individual_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> IndividualId {
        // PORT-PENDING: faithful transcription of cpp 3058–3071. Outline:
        //
        //   incExpData = individualNode->getIncrementalExpansionData(false);
        //   if incExpData && incExpData->requiresFurtherIncrementalExpansion():
        //     incExpData = individualNode->getIncrementalExpansionData(true);
        //     while incExpData->requiresFurtherIncrementalExpansion():
        //       nextIndi = incExpData->takeNextIncrementalExpansionIndividual();
        //       indiProcNodeVec = ctx->getProcessingDataBox()->getIndividualProcessNodeVector();
        //       if !indiProcNodeVec->getData(-nextIndi->getIndividualID()): return nextIndi;
        //   return nullptr;
        //
        // Held PORT-PENDING on the `CIndividualNodeIncrementalExpansionData` satellite
        // (`requiresFurtherIncrementalExpansion` / `takeNextIncrementalExpansionIndividual`,
        // no bodies yet). The individual-process-node vector getter is available.
        let _ = (individual_node, calc_alg_context);
        Id::NONE
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::incrementalNodeExpansion`.
    /// cpp 3075–3084.
    ///
    /// Expands one queued incremental-expansion individual for `expandNode`: takes the
    /// next individual, loads/creates its up-to-date node, re-enqueues `expandNode`
    /// for any remaining work, and returns the freshly expanded node (`Id::NONE` when
    /// nothing remains to expand).
    pub fn incremental_node_expansion(
        &mut self,
        expand_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        // expIndi = getNextIncrementalExpansionIndividual(expandNode,ctx);
        // if expIndi:
        //   expandedIndiNode = getUpToDateIndividual(-expIndi->getIndividualID(),ctx);
        //   addIndividualToIncrementalExpansionQueue(expandNode,ctx);
        //   return expandedIndiNode;
        // return nullptr;
        let exp_indi = self.get_next_incremental_expansion_individual(expand_node, calc_alg_context);
        if exp_indi.is_some() {
            // W3-DEFER[api]: expandedIndiNode = getUpToDateIndividual(-expIndi->getIndividualID(),ctx);
            //   (`getUpToDateIndividual` is a neighbour/core sibling not ported in this unit.)
            self.add_individual_to_incremental_expansion_queue(expand_node, calc_alg_context);
            // PORT-PENDING: return the loaded up-to-date node once `getUpToDateIndividual` lands.
            return Id::NONE;
        }
        Id::NONE
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::requiresIncrementalNodeExpansion`.
    /// cpp 3088–3094.
    ///
    /// True iff the node's previous-graph correspondence is incompatible AND it is
    /// flagged directly-changed-neighbour-connection or directly-changed.
    pub fn requires_incremental_node_expansion(
        &mut self,
        individual_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // incExpData = individualNode->getIncrementalExpansionData(false);
        let inc_exp_data = calc_alg_context
            .process_context_mut()
            .node_mut(individual_node)
            .incremental_expansion_data(false);
        // if !incExpData->isPreviousCompletionGraphCompatible()
        //    && (incExpData->hasDirectlyChangedNeighbourConnection() || incExpData->isDirectlyChanged()):
        //   return true;
        // return false;
        //
        // W2.7 reconcile: the `CIndividualNodeIncrementalExpansionData` satellite is now
        // arena-backed (`process::reapply_sat`); the change predicate goes live via the
        // process-context accessor. C++ derefs `incExpData` unconditionally here (the
        // node always carries the data when this is reached) — mirrored, no guard.
        let pc = calc_alg_context.process_context();
        if !pc
            .inc_exp_data(inc_exp_data)
            .is_previous_completion_graph_compatible()
            && (pc
                .inc_exp_data(inc_exp_data)
                .has_directly_changed_neighbour_connection()
                || pc.inc_exp_data(inc_exp_data).is_directly_changed())
        {
            return true;
        }
        false
    }

    // =======================================================================
    // Pruning of incrementally removed successors (cpp 3384–3431).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::pruneIncrementalRemovedSuccessors`.
    /// cpp 3384–3431.
    ///
    /// Breadth-first prunes (marks `PRFPURGEDBLOCKED` + eliminates blocked
    /// individuals) the blockable subtree reachable from `indi` over connection-
    /// successors and ordinary successors, skipping nominals and any node already in
    /// `pruningNodeSet` / `compatibleNominalNodeSet`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: `CPROCESSINGSET<cint64>*` work sets become opaque
    /// `Cint64` handles until the temp processing-set allocator is ported.
    pub fn prune_incremental_removed_successors(
        &mut self,
        indi: &mut NodeId,
        compatible_nominal_node_set: Cint64,
        pruning_node_set: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // PORT-PENDING: faithful transcription of cpp 3384–3431. Outline:
        //
        //   pruningNodeList = alloc CPROCESSINGLIST<CIndividualProcessNode*>; pruningNodeList->append(indi);
        //   while !pruningNodeList->isEmpty():
        //     pruningNode = pruningNodeList->takeFirst();
        //     if pruningNode != indi && !pruningNode->hasPartialProcessingRestrictionFlags(PRFPURGEDBLOCKED):
        //       pruningNode->addProcessingRestrictionFlags(PRFPURGEDBLOCKED);
        //       eliminiateBlockedIndividuals(pruningNode,ctx);                              // backtracking unit
        //     connSuccSet = pruningNode->getConnectionSuccessorSet(false);
        //     if connSuccSet && connSuccSet->getConnectionSuccessorCount() > 0:
        //       for connID in connSuccSet->getConnectionSuccessorIterator():
        //         if !pruningNodeSet->contains(connID) && !compatibleNominalNodeSet->contains(connID):
        //           nomIndi = getUpToDateIndividual(connID,ctx);
        //           if !nomIndi->getNominalIndividual() && !nomIndi->hasPartialProcessingRestrictionFlags(PRFPURGEDBLOCKED):
        //             pruningNodeSet->insert(connID);
        //             pruningNodeList->append(getLocalizedIndividual(nomIndi,false,ctx));
        //     ancDepth = pruningNode->getIndividualAncestorDepth();
        //     for succLink in pruningNode->getSuccessorIterator():
        //       succIndi = getSuccessorIndividual(pruningNode,succLink,ctx);
        //       if !succIndi->getNominalIndividual() && !succIndi->hasPartialProcessingRestrictionFlags(PRFPURGEDBLOCKED):
        //         succIndiID = succIndi->getIndividualNodeID();
        //         if !pruningNodeSet->contains(succIndiID) && !compatibleNominalNodeSet->contains(succIndiID):
        //           pruningNodeSet->insert(succIndiID);
        //           pruningNodeList->append(getLocalizedIndividual(succIndi,false,ctx));
        //
        // Held PORT-PENDING: the temp `CPROCESSINGSET`/`CPROCESSINGLIST` allocators
        // ([api] opaque here), and the siblings `eliminiateBlockedIndividuals`
        // (backtracking unit), `getUpToDateIndividual` / `getSuccessorIndividual` /
        // `getLocalizedIndividual` (neighbour/core units). The node accessors
        // (`getConnectionSuccessorSet`, `getSuccessorIterator`,
        // `getIndividualAncestorDepth`, `addProcessingRestrictionFlags`) are available
        // substrate; this body goes live once the sibling helpers land.
        let _ = (indi, compatible_nominal_node_set, pruning_node_set, calc_alg_context);
    }

    // =======================================================================
    // Directly-changed neighbour-connection propagation (cpp 3476–3761).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::checkCompatibilityUpdateDirectlyChangedPropagation`.
    /// cpp 3476–3493.
    ///
    /// Asks `mIncExpHandler` whether the node is previous-graph compatible: if so,
    /// clears the propagated directly-changed-neighbour connection; otherwise (re)queues
    /// incremental expansion for a directly-changed node and, when neither directly-
    /// changed nor changed-connection yet, searches for a directly-changed neighbour and
    /// establishes + propagates the connection.
    pub fn check_compatibility_update_directly_changed_propagation(
        &mut self,
        individual_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // compatible = mIncExpHandler->isIndividualNodePreviousCompletionGraphCompatible(individualNode,ctx);
        // incExpData = individualNode->getIncrementalExpansionData(false);
        // if compatible:
        //   clearPropagatedDirectlyChangedNeighbourConnection(individualNode,true,ctx);
        // else:
        //   if incExpData->isDirectlyChanged(): addIndividualToIncrementalExpansionQueue(individualNode,ctx);
        //   if !incExpData->isDirectlyChanged() && !incExpData->hasDirectlyChangedNeighbourConnection():
        //     directlyChangedConnNode = searchDirectlyChangedNeighbourNodeConnection(individualNode,ctx);
        //     if directlyChangedConnNode && establishDirectlyChangedNeighbourConnection(individualNode,directlyChangedConnNode,true,ctx):
        //       propagateDirectlyChangedNeighbourNodeConnection(individualNode,true,ctx);
        // return compatible;
        //
        // Held PORT-PENDING on `mIncExpHandler`
        // (`isIndividualNodePreviousCompletionGraphCompatible`, Algorithm-layer stub)
        // and the `CIndividualNodeIncrementalExpansionData` satellite. The siblings it
        // dispatches to (clear/search/establish/propagate) are this-unit PORT-PENDING.
        let _ = (individual_node, calc_alg_context);
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::linkCreationDirectlyChangedNeighbourConnectionUpdate`.
    /// cpp 3497–3508. FULLY PORTED (pure sibling-call control flow).
    ///
    /// On a new link between `sourceIndi` and `destIndi`, establishes + propagates the
    /// directly-changed-neighbour connection in both directions; returns whether either
    /// direction updated.
    ///
    /// KONCLUDE-PORT-NOTE: the C++ ignores its `queueIncrementalExpansion` parameter,
    /// hard-coding `true` in both `establishDirectlyChangedNeighbourConnection` calls —
    /// transcribed verbatim (the param is intentionally unused).
    pub fn link_creation_directly_changed_neighbour_connection_update(
        &mut self,
        source_indi: NodeId,
        dest_indi: NodeId,
        queue_incremental_expansion: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut updated_neighbour_connection = false;
        if self.establish_directly_changed_neighbour_connection(
            source_indi,
            dest_indi,
            true,
            calc_alg_context,
        ) {
            self.propagate_directly_changed_neighbour_node_connection(
                source_indi,
                true,
                calc_alg_context,
            );
            updated_neighbour_connection = true;
        }
        if self.establish_directly_changed_neighbour_connection(
            dest_indi,
            source_indi,
            true,
            calc_alg_context,
        ) {
            self.propagate_directly_changed_neighbour_node_connection(
                dest_indi,
                true,
                calc_alg_context,
            );
            updated_neighbour_connection = true;
        }
        updated_neighbour_connection
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::establishDirectlyChangedNeighbourConnection`.
    /// cpp 3512–3529.
    ///
    /// If `individualNode` is not itself changed/changed-connection but
    /// `neighbourNodeCandidate` is, records the candidate as this node's directly-
    /// changed-connection node and back-registers this node on the candidate; queues
    /// incremental expansion when this node is a nominal. Returns whether the
    /// connection was established.
    pub fn establish_directly_changed_neighbour_connection(
        &mut self,
        individual_node: NodeId,
        neighbour_node_candidate: NodeId,
        queue_incremental_expansion: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // incExpData = individualNode->getIncrementalExpansionData(false);
        // if !incExpData || (!incExpData->hasDirectlyChangedNeighbourConnection() && !incExpData->isDirectlyChanged()):
        //   candIncExpData = neighbourNodeCandidate->getIncrementalExpansionData(false);
        //   if candIncExpData && (candIncExpData->hasDirectlyChangedNeighbourConnection() || candIncExpData->isDirectlyChanged()):
        //     locIncExpData = individualNode->getIncrementalExpansionData(true);
        //     locNeighbourNodeCandidate = getLocalizedIndividual(neighbourNodeCandidate,false,ctx);
        //     locIncExpData->setDirectlyChangedNeighbourConnectionNode(locNeighbourNodeCandidate);
        //     locCandIncExpData = locNeighbourNodeCandidate->getIncrementalExpansionData(true);
        //     locCandIncExpData->addNeighbourPropagatedDirectlyChanged(individualNode);
        //     if queueIncrementalExpansion && individualNode->getNominalIndividual():
        //       addIndividualToIncrementalExpansionQueue(individualNode,ctx);
        //     return true;
        // return false;
        //
        // Held PORT-PENDING on the `CIndividualNodeIncrementalExpansionData` satellite
        // (no bodies / node accessor) and the `getLocalizedIndividual` sibling
        // (neighbour/core unit). `getNominalIndividual` is available substrate.
        let _ = (individual_node, neighbour_node_candidate, queue_incremental_expansion, calc_alg_context);
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::propagateDirectlyChangedNeighbourNodeConnection`.
    /// cpp 3534–3634.
    ///
    /// Breadth-first propagates the directly-changed-neighbour connection outward from
    /// `individualNode` over successors, connection-successors and — for nodes carrying
    /// `PRFSUCCESSORNOMINALCONNECTION` — blocked / processing-blocked / follow-set /
    /// blocker / following individuals, establishing the connection on each newly
    /// reached node.
    pub fn propagate_directly_changed_neighbour_node_connection(
        &mut self,
        individual_node: NodeId,
        queue_incremental_expansion: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // PORT-PENDING: faithful transcription of cpp 3534–3634. Outline:
        //
        //   propNodeList(ctx); propNodeList.append(individualNode); propagatedDirectlyChanged = false;
        //   while !propNodeList.isEmpty():
        //     propIndiNode = propNodeList.takeFirst();
        //     for succLink in propIndiNode->getSuccessorIterator():
        //       succIndi = getSuccessorIndividual(propIndiNode,succLink,ctx);
        //       incExpData = succIndi->getIncrementalExpansionData(false);
        //       if !incExpData || (!hasDirectlyChangedNeighbourConnection && !isDirectlyChanged && !isPreviousCompletionGraphCompatible):
        //         locSuccIndi = getLocalizedIndividual(succIndi,false,ctx);
        //         if establishDirectlyChangedNeighbourConnection(locSuccIndi,propIndiNode,queueIncrementalExpansion,ctx):
        //           propagatedDirectlyChanged = true; propNodeList.append(locSuccIndi);
        //     for connID in propIndiNode->getConnectionSuccessorIterator():
        //       connIndiNode = getUpToDateIndividual(connID,ctx);   // same guard + establish + append
        //     if propIndiNode->hasPartialProcessingRestrictionFlags(PRFSUCCESSORNOMINALCONNECTION):
        //       for blockedIndiNode in propIndiNode->getBlockedIndividualsLinker():           // same guard/establish/append
        //       for blockedIndiNode in propIndiNode->getProcessingBlockedIndividualsLinker(): // same
        //       followSet = propIndiNode->getBlockingFollowSet(false);
        //       if followSet: for blockedIndiNodeID in followSet:                              // same
        //       blockerIndiNode = propIndiNode->getBlockerIndividualNode();   if set: same
        //       followingIndiNode = propIndiNode->getFollowingIndividualNode(); if set: same
        //   return propagatedDirectlyChanged;
        //
        // Held PORT-PENDING: the `CIndividualNodeIncrementalExpansionData` satellite
        // (the guard predicate on every reached node) + the temp processing list, and
        // the siblings `getSuccessorIndividual` / `getUpToDateIndividual` /
        // `getLocalizedIndividual` and `establishDirectlyChangedNeighbourConnection`
        // (this unit, PORT-PENDING). The node iterators / blocked-linker / follow-set /
        // blocker / following getters are available substrate.
        let _ = (individual_node, queue_incremental_expansion, calc_alg_context);
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::searchDirectlyChangedNeighbourNodeConnection`.
    /// cpp 3639–3702.
    ///
    /// Scans the node's successors, connection-successors and (for
    /// `PRFSUCCESSORNOMINALCONNECTION` nodes) blocked / follow-set / blocker /
    /// following individuals for the first one already flagged directly-changed or
    /// changed-connection, returning it (`Id::NONE` when none).
    pub fn search_directly_changed_neighbour_node_connection(
        &mut self,
        individual_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        // PORT-PENDING: faithful transcription of cpp 3639–3702. Outline:
        //
        //   for succLink in individualNode->getSuccessorIterator():
        //     succIndi = getSuccessorIndividual(individualNode,succLink,ctx);
        //     if succIndi->getIncrementalExpansionData(false) is directly-changed/changed-connection: return succIndi;
        //   for connID in individualNode->getConnectionSuccessorIterator():
        //     connIndiNode = getUpToDateIndividual(connID,ctx);  if changed: return connIndiNode;
        //   if individualNode->hasPartialProcessingRestrictionFlags(PRFSUCCESSORNOMINALCONNECTION):
        //     scan getBlockedIndividualsLinker / getProcessingBlockedIndividualsLinker / getBlockingFollowSet(false)
        //       / getBlockerIndividualNode() / getFollowingIndividualNode() (each via getUpToDateIndividual),
        //       returning the first directly-changed/changed-connection node;
        //   return nullptr;
        //
        // Held PORT-PENDING on the `CIndividualNodeIncrementalExpansionData` satellite
        // (the per-candidate change predicate) + the `getSuccessorIndividual` /
        // `getUpToDateIndividual` siblings; the node iterators and linker getters are
        // available substrate.
        let _ = (individual_node, calc_alg_context);
        Id::NONE
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::clearDirectlyChangedNeighbourConnection`.
    /// cpp 3706–3718.
    ///
    /// Clears this node's directly-changed-neighbour-connection node (queueing a
    /// nominal compatibility recheck) and then clears the propagated connection;
    /// returns whether anything was cleared.
    pub fn clear_directly_changed_neighbour_connection(
        &mut self,
        individual_node: NodeId,
        queue_compatibility_checks: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // incExpData = individualNode->getIncrementalExpansionData(false);
        // if incExpData && incExpData->hasDirectlyChangedNeighbourConnection():
        //   locIncExpData = individualNode->getIncrementalExpansionData(true);
        //   locIncExpData->setDirectlyChangedNeighbourConnectionNode(nullptr);
        //   if queueCompatibilityChecks && individualNode->isNominalIndividualNode():
        //     ctx->getUsedProcessingDataBox()->getIncrementalCompatibilityCheckingQueue(true)->insertProcessIndiviudal(individualNode);
        //   clearPropagatedDirectlyChangedNeighbourConnection(individualNode,true,ctx);
        //   return true;
        // return false;
        //
        // Held PORT-PENDING on the `CIndividualNodeIncrementalExpansionData` satellite.
        // The databox `getIncrementalCompatibilityCheckingQueue` getter is available
        // substrate; `insertProcessIndiviudal` is a deferred queue method (W3-DEFER[api]).
        let _ = (individual_node, queue_compatibility_checks, calc_alg_context);
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::clearPropagatedDirectlyChangedNeighbourConnection`.
    /// cpp 3722–3761.
    ///
    /// Breadth-first clears the directly-changed-neighbour connection on every node
    /// that propagated it from `individualNode` (matching the connection back-pointer),
    /// re-queueing nominal compatibility checks as it goes; the C++ returns `false`
    /// unconditionally (the local `propCleared` is computed but not returned).
    pub fn clear_propagated_directly_changed_neighbour_connection(
        &mut self,
        individual_node: NodeId,
        queue_compatibility_checks: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // PORT-PENDING: faithful transcription of cpp 3722–3761. Outline:
        //
        //   propCleared = false;
        //   incExpData = individualNode->getIncrementalExpansionData(false);
        //   if incExpData && incExpData->hasNeighbourPropagatedDirectlyChanged():
        //     clearPropNodeList(ctx); clearPropNodeList.append(individualNode);
        //     while !clearPropNodeList.isEmpty():
        //       clearPropIndiNode = clearPropNodeList.takeFirst();
        //       clearIncExpData = clearPropIndiNode->getIncrementalExpansionData(false);
        //       propIndiNodeList = clearIncExpData->getNeighbourPropagatedDirectlyChangedList(false);
        //       if propIndiNodeList && !propIndiNodeList->isEmpty():
        //         clearIncExpData = clearPropIndiNode->getIncrementalExpansionData(true);
        //         propIndiNodeList = clearIncExpData->getNeighbourPropagatedDirectlyChangedList(true);
        //         for propNode in propIndiNodeList:
        //           propNode = getUpToDateIndividual(propNode,ctx);
        //           propIncExpData = propNode->getIncrementalExpansionData(false);
        //           if propIncExpData && propIncExpData->hasDirectlyChangedNeighbourConnection()
        //              && propIncExpData->getDirectlyChangedNeighbourConnectionNode()->getIndividualNodeID() == clearPropIndiNode->getIndividualNodeID():
        //             propCleared = true;
        //             propNode = getLocalizedIndividual(propNode,false,ctx);
        //             propIncExpData = propNode->getIncrementalExpansionData(true);
        //             propIncExpData->setDirectlyChangedNeighbourConnectionNode(nullptr);
        //             if propIncExpData->hasNeighbourPropagatedDirectlyChanged(): clearPropNodeList.append(propNode);
        //             if queueCompatibilityChecks && individualNode->isNominalIndividualNode():
        //               ctx->getUsedProcessingDataBox()->getIncrementalCompatibilityCheckingQueue(true)->insertProcessIndiviudal(individualNode);
        //         clearIncExpData->clearNeighbourPropagatedDirectlyChangedList();
        //   return false;   // C++ returns false unconditionally (propCleared is unused)
        //
        // Held PORT-PENDING on the `CIndividualNodeIncrementalExpansionData` satellite
        // (the neighbour-propagated list + change accessors) and the
        // `getUpToDateIndividual` / `getLocalizedIndividual` siblings; the databox
        // compatibility-checking queue getter is available substrate
        // (`insertProcessIndiviudal` is the deferred queue method).
        let _ = (individual_node, queue_compatibility_checks, calc_alg_context);
        false
    }

    // =======================================================================
    // Compatible concept-set reuse / signature checks (cpp 4955–6004).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::hasCompatibleConceptSetReuse`.
    /// cpp 4955–4972.
    ///
    /// True iff `subConceptSet` is a label-subset of `reuseNodeCand`'s concept set and
    /// none of the super-set's concepts are signature-blocking-critical for the reuse
    /// candidate (marking the candidate's signature blocking invalid otherwise).
    pub fn has_compatible_concept_set_reuse(
        &mut self,
        indi_node: NodeId,
        sub_concept_set: LabelSetId,
        reuse_node_cand: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // superConceptSet = reuseNodeCand->getReapplyConceptLabelSet(false);
        // isSubset = isLabelConceptSubSet(subConceptSet,superConceptSet,nullptr,nullptr,ctx);
        // if !isSubset: return false;
        // for conDes in superConceptSet->getConceptLabelSetIterator(false,false,false):
        //   if isConceptSignatureBlockingCritical(reuseNodeCand,conDes,conDes->getDependencyTrackPoint(),ctx):
        //     indiNode->setInvalidSignatureBlocking(true);
        //     return false;
        // return true;
        //
        // Held PORT-PENDING on the siblings `isLabelConceptSubSet` (blocking/label-test
        // unit) and `isConceptSignatureBlockingCritical` (blocking unit). The node
        // `getReapplyConceptLabelSet` + `setInvalidSignatureBlocking` and the label-set
        // iterator are available substrate; this body goes live once the two label/
        // signature siblings land.
        let _ = (indi_node, sub_concept_set, reuse_node_cand, calc_alg_context);
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::hasCompatibleConceptSetSignature`.
    /// cpp 5960–6004.
    ///
    /// Checks whether `conSet` is an order-/content-compatible suffix of
    /// `compatibleTestNode`'s concept set (aligning the sorted adding-linkers by the
    /// size difference), bailing to `false` on any signature-blocking-critical concept
    /// (which also marks `blockingNode`'s signature blocking invalid) or a missing
    /// concept once ordering compatibility is lost.
    pub fn has_compatible_concept_set_signature(
        &mut self,
        blocking_node: &mut NodeId,
        con_set: LabelSetId,
        compatible_test_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // PORT-PENDING: faithful transcription of cpp 5960–6004. Outline:
        //
        //   compTestConSet = compatibleTestNode->getReapplyConceptLabelSet(false);
        //   conCount = conSet->getConceptCount(); compTestConCount = compTestConSet->getConceptCount();
        //   if conCount <= 0 || compTestConCount < conCount: return false;
        //   diffCount = compTestConCount - conCount;
        //   compTestConDesIt = compTestConSet->getAddingSortedConceptDescriptionLinker();
        //   conDesIt         = conSet->getAddingSortedConceptDescriptionLinker();
        //   while diffCount-- > 0: compTestConDesIt = compTestConDesIt->getNext();
        //   orderingCompatible = true;
        //   while orderingCompatible && conDesIt:
        //     concept = conDesIt->getConcept(); conNeg = conDesIt->getNegation();
        //     if compTestConDesIt->getData() == concept && compTestConDesIt->getNegation() == conNeg:
        //       if isConceptSignatureBlockingCritical(blockingNode,conDesIt,conDesIt->getDependencyTrackPoint(),ctx):
        //         blockingNode->setInvalidSignatureBlocking(true); return false;
        //       advance both;
        //     else: orderingCompatible = false;
        //   if !orderingCompatible:
        //     while conDesIt:
        //       concept = conDesIt->getConcept(); conNeg = conDesIt->getNegation();
        //       if isConceptSignatureBlockingCritical(blockingNode,conDesIt,conDesIt->getDependencyTrackPoint(),ctx):
        //         blockingNode->setInvalidSignatureBlocking(true); return false;
        //       if !conSet->containsConcept(concept,conNeg): return false;
        //       advance conDesIt;
        //   return true;
        //
        // Held PORT-PENDING on the `isConceptSignatureBlockingCritical` sibling
        // (blocking unit). The node `getReapplyConceptLabelSet` + `setInvalidSignatureBlocking`
        // and the label-set accessors (`getConceptCount` /
        // `getAddingSortedConceptDescriptionLinker` / `containsConcept`) are available
        // substrate; this body goes live once the signature-critical sibling lands.
        let _ = (blocking_node, con_set, compatible_test_node, calc_alg_context);
        false
    }

    // =======================================================================
    // Debug rendering (cpp 8014–8036).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::generateDebugIncrementalExpansionString`.
    /// cpp 8014–8036.
    ///
    /// Renders the node's incremental-expansion status (compatible / directly-changed-
    /// connection / directly-changed-node), the changed-connection neighbour id, and
    /// the expansion priority into a debug string.
    pub fn generate_debug_incremental_expansion_string(
        &mut self,
        indi: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> String {
        // incExpData = indi->getIncrementalExpansionData(false);
        // if incExpData:
        //   collect status tokens from isPreviousCompletionGraphCompatible /
        //     hasDirectlyChangedNeighbourConnection / isDirectlyChanged;
        //   dirChangedNeighConnNodeID = incExpData->getDirectlyChangedNeighbourConnectionNode()?->getIndividualNodeID() ?? "-";
        //   expansionPriority = incExpData->getExpansionPriority();
        //   format "Incremental-Expansion-Status: … / Directly-Changed-Connection-Neighbour: … / Expansion-Priority: …";
        // return incExpString;
        //
        // Held PORT-PENDING on the `CIndividualNodeIncrementalExpansionData` satellite
        // (status / priority / changed-connection accessors). Debug-only; empty string
        // until the satellite lands.
        let _ = (indi, calc_alg_context);
        String::new()
    }

    // =======================================================================
    // Variable-propagation-binding compatibility (cpp 17990–18050).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::areVariablePropagationBindingsCompatible`.
    /// cpp 17990–18013.
    ///
    /// Two variable-binding paths are compatible iff they share a propagation id, or no
    /// variable bound in the smaller path is bound to a different individual in the
    /// larger path.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: `CVariableBindingPath*` → `VarBindingPathId`; the
    /// `CVariableBinding` / `CVariableBindingDescriptor` chain it walks is now the
    /// arena-backed variable-binding-path subsystem (`process::varbind`), reached
    /// through `calc_alg_context.process_context()`.
    pub fn are_variable_propagation_bindings_compatible(
        &mut self,
        var_bind_path1: VarBindingPathId,
        var_bind_path2: VarBindingPathId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let pc = calc_alg_context.process_context();
        // if varBindPath1->getPropagationID() == varBindPath2->getPropagationID(): return true;
        if pc.vbpath(var_bind_path1).get_propagation_id()
            == pc.vbpath(var_bind_path2).get_propagation_id()
        {
            return true;
        }
        // pick lessVarBindPath / moreVarBindPath by getVariableBindingCount();
        let count1 = VariableBindingPath::get_variable_binding_count(pc, var_bind_path1);
        let count2 = VariableBindingPath::get_variable_binding_count(pc, var_bind_path2);
        let (less_var_bind_path, more_var_bind_path) = if count1 <= count2 {
            (var_bind_path1, var_bind_path2)
        } else {
            (var_bind_path2, var_bind_path1)
        };
        // for lessVarBindDes in lessVarBindPath->getVariableBindingDescriptorLinker():
        //   variable  = lessVarBindDes->getVariableBinding()->getBindedVariable();
        //   boundIndi = lessVarBindDes->getVariableBinding()->getBindedIndividual();
        //   for moreVarBindDes in moreVarBindPath->getVariableBindingDescriptorLinker():
        //     if moreBinding->getBindedVariable() == variable
        //        && moreBinding->getBindedIndividual()->getIndividualNodeID() != boundIndi->getIndividualNodeID(): return false;
        let mut less_var_bind_des = pc
            .vbpath(less_var_bind_path)
            .get_variable_binding_descriptor_linker();
        while less_var_bind_des.is_some() {
            let less_binding = pc.var_binding_des(less_var_bind_des).get_variable_binding();
            let variable = pc.var_binding(less_binding).get_binded_variable();
            let bound_indi = pc.var_binding(less_binding).get_binded_individual();
            let bound_indi_node_id = pc.node(bound_indi).individual_node_id();
            let mut more_var_bind_des = pc
                .vbpath(more_var_bind_path)
                .get_variable_binding_descriptor_linker();
            while more_var_bind_des.is_some() {
                let more_binding = pc.var_binding_des(more_var_bind_des).get_variable_binding();
                if pc.var_binding(more_binding).get_binded_variable() == variable {
                    let more_bound_indi = pc.var_binding(more_binding).get_binded_individual();
                    if pc.node(more_bound_indi).individual_node_id() != bound_indi_node_id {
                        return false;
                    }
                }
                more_var_bind_des = pc.var_binding_des(more_var_bind_des).get_next();
            }
            less_var_bind_des = pc.var_binding_des(less_var_bind_des).get_next();
        }
        true
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getConceptsForCompatibleVariablePropagationBindings`.
    /// cpp 18017–18050.
    ///
    /// Collects the trigger concepts of every concept-variable-binding-path-set on
    /// `individualNode` whose binding path is compatible (per
    /// `areVariablePropagationBindingsCompatible`) with `varBindPath`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: returns the C++ `QSet<CConcept*>` as a `Vec<ConceptId>`;
    /// the `CConceptVariableBindingPathSetHash` / `CVariableBindingPathSet` /
    /// `CVariableBindingPath` subsystem it walks is not yet ported (`varBindPath`
    /// opaque `Cint64`).
    pub fn get_concepts_for_compatible_variable_propagation_bindings(
        &mut self,
        individual_node: &mut NodeId,
        var_bind_path: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> Vec<ConceptId> {
        // conceptSet = {};
        // conVarBindSetHash = individualNode->getConceptVariableBindingPathSetHash(false);
        // if conVarBindSetHash:
        //   for hashData in conVarBindSetHash:
        //     varBindSet = hashData.mUseVariableBindingPathSet; conDes = varBindSet->getConceptDescriptor();
        //     if varBindSet && conDes:
        //       concept = conDes->getConcept(); conceptsVarBindsCompatible = false;
        //       for mapData in varBindSet->getVariableBindingPathMap():
        //         varBindDes = mapData.getVariableBindingPathDescriptor();
        //         if varBindDes && areVariablePropagationBindingsCompatible(varBindPath, varBindDes->getVariableBindingPath(), ctx):
        //           conceptsVarBindsCompatible = true; break;
        //       if conceptsVarBindsCompatible: conceptSet.insert(concept);
        // return conceptSet;
        //
        // Held PORT-PENDING on `CConceptVariableBindingPathSetHash` (node satellite) +
        // the variable-binding-path subsystem; the `areVariablePropagationBindingsCompatible`
        // sibling lives in this unit (PORT-PENDING).
        let _ = (individual_node, var_bind_path, calc_alg_context);
        Vec::new()
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getBindingsCompatibleConceptSetsHashValue`.
    /// cpp 18262–18277. FULLY PORTED.
    ///
    /// Order-independent hash of a set of concept sets: `|sets| + Σ_set (|set| +
    /// Σ_concept tag) * |set|`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: the C++ `const QSet<QSet<CConcept*>>&` becomes
    /// `&[Vec<ConceptId>]`; the inner/outer iteration order is irrelevant (the
    /// accumulation is commutative), so the hash matches the C++ regardless of
    /// container ordering.
    pub fn get_bindings_compatible_concept_sets_hash_value(
        &mut self,
        associated_concept_sets: &[Vec<ConceptId>],
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> Cint64 {
        let mut hash_value: Cint64 = associated_concept_sets.len() as Cint64;
        for con_set in associated_concept_sets {
            let mut con_set_hash_value: Cint64 = con_set.len() as Cint64;
            for &concept in con_set {
                con_set_hash_value += calc_alg_context
                    .ontology_arenas()
                    .concept(concept)
                    .get_concept_tag();
            }
            hash_value += con_set_hash_value * con_set.len() as Cint64;
        }
        hash_value
    }

    // =======================================================================
    // Incremental processing-queue insertion (cpp 27554–27584).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addIndividualToIncrementalCompatibilityCheckingQueue`.
    /// cpp 27554–27563. FULLY PORTED (bar the deferred queue-insert body + stat counter).
    ///
    /// Enqueues an un-queued nominal node onto the incremental-compatibility-checking
    /// queue; returns whether it was enqueued.
    pub fn add_individual_to_incremental_compatibility_checking_queue(
        &mut self,
        individual: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let is_queued = calc_alg_context
            .process_context()
            .node(individual)
            .is_incremental_compatibility_checking_queued();
        let is_nominal = calc_alg_context
            .process_context()
            .node(individual)
            .is_nominal_individual_node();
        if !is_queued && is_nominal {
            calc_alg_context
                .process_context_mut()
                .node_mut(individual)
                .set_incremental_compatibility_checking_queued(true);
            let _inc_comp_checking_queue = calc_alg_context
                .processing_data_box_mut()
                .get_incremental_compatibility_checking_queue(true);
            // W3-DEFER[api]: incCompCheckingQueue->insertProcessIndiviudal(individual);
            //   (`CIndividualDepthProcessingQueue::insertProcessIndiviudal` is a
            //   Process-layer queue method not yet ported.)
            // W3-DEFER[api]: STATINC(INDINODESADDEDPROCESSINGQUEUECOUNT,calcAlgContext);
            return true;
        }
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addIndividualToIncrementalExpansionQueue`.
    /// cpp 27565–27584.
    ///
    /// Enqueues an un-queued node onto the incremental-expansion-list-initializing
    /// queue (when its expansion list is not yet initialized) or, once initialized and
    /// further expansion is required, onto the priority incremental-expansion queue at
    /// the node's next expansion priority; returns whether it was enqueued.
    pub fn add_individual_to_incremental_expansion_queue(
        &mut self,
        individual: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W2.7 reconcile: the `CIndividualNodeIncrementalExpansionData` satellite
        // (`process::reapply_sat`) is now arena-backed, so the branch selection goes
        // live. The terminal queue `insertProcessIndiviudal` / `insertIndiviudal`
        // methods + `STATINC` stay `W3-DEFER` (the same accepted leaves as the ported
        // sibling `add_individual_to_incremental_compatibility_checking_queue`).
        //
        // if !individual->isIncrementalExpansionQueued():
        if !calc_alg_context
            .process_context()
            .node(individual)
            .is_incremental_expansion_queued()
        {
            // incExpData = individual->getIncrementalExpansionData(false);
            let inc_exp_data = calc_alg_context
                .process_context_mut()
                .node_mut(individual)
                .incremental_expansion_data(false);
            // if !incExpData || !incExpData->isIncremetnalExpansionListInitialized():
            let list_initialized = inc_exp_data.is_some()
                && calc_alg_context
                    .process_context()
                    .inc_exp_data(inc_exp_data)
                    .is_incremetnal_expansion_list_initialized();
            if !list_initialized {
                // individual->setIncrementalExpansionQueued(true);
                calc_alg_context
                    .process_context_mut()
                    .node_mut(individual)
                    .set_incremental_expansion_queued(true);
                // incExpInitQueue = ctx->getProcessingDataBox()->getIncrementalExpansionInitializingProcessingQueue(true);
                let _inc_exp_init_queue = calc_alg_context
                    .processing_data_box_mut()
                    .get_incremental_expansion_initializing_processing_queue(true);
                // W3-DEFER[api]: incExpInitQueue->insertProcessIndiviudal(individual);
                // W3-DEFER[macro]: STATINC(INDINODESADDEDPROCESSINGQUEUECOUNT, ctx);
                return true;
            } else if calc_alg_context
                .process_context()
                .inc_exp_data(inc_exp_data)
                .requires_further_incremental_expansion()
            {
                // individual->setIncrementalExpansionQueued(true);
                calc_alg_context
                    .process_context_mut()
                    .node_mut(individual)
                    .set_incremental_expansion_queued(true);
                // nextExpPriority = incExpData->getNextIncrementalExpansionPriority();
                let _next_exp_priority = calc_alg_context
                    .process_context()
                    .inc_exp_data(inc_exp_data)
                    .get_next_incremental_expansion_priority();
                // incExpQueue = ctx->getProcessingDataBox()->getIncrementalExpansionProcessingQueue(true);
                let _inc_exp_queue = calc_alg_context
                    .processing_data_box_mut()
                    .get_incremental_expansion_processing_queue(true);
                // W3-DEFER[api]: incExpQueue->insertIndiviudal(nextExpPriority, individual);
                // W3-DEFER[macro]: STATINC(INDINODESADDEDPROCESSINGQUEUECOUNT, ctx);
                return true;
            }
        }
        false
    }
}
