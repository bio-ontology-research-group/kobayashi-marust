//! `completion::u14` — Merge-handling family, batch 3 (port unit #14 of 36).
//!
//! Faithful port of 11 merge-handling methods of Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`
//! (manifest `01-completion-methods.md`, "Unit 14", cpp ranges 15820–21006):
//!
//!   * `initializeMergingIndividualNodes`              [15820–16063]
//!   * `getCorrectedMergedIntoIndividualNode`          [16264–16270]
//!   * `createIndividualMergeCausingDescriptors`       [16690–16713]
//!   * `isIndividualNodesMergeableWithoutNewRuleApplications` [20481–20639]
//!   * `expandBackendCacheIndividualNodesNominalMerging`      [20644–20651]
//!   * `expandBackendCacheIndividualNodesNominalMergingNeighbouringConnections` [20655–20710]
//!   * `isIndividualNodesMergeable`                    [20714–20751]
//!   * `areIndividualNodesDisjointRolesMergeable`      [20754–20764]
//!   * `isIndividualNodeDisjointRolesMergeable`        [20767–20863]
//!   * `getMergedIndividualNodes`                      [20936–20985]
//!   * `getIntoEmptyMergedIndividualNode`              [20990–21006]
//!
//! These methods decide WHETHER two completion-graph nodes can be merged (≤n /
//! nominal / functional merging), gather the clash descriptors that explain a
//! failed merge, and pick / construct the surviving node before the actual graft
//! (`mergeIndividualNodeInto`, unit u15).
//!
//! KONCLUDE-PORT-NOTE[ownership]: each method is a member of
//! `CCalculationTableauCompletionTaskHandleAlgorithm`, so it becomes `&mut self`
//! plus the threaded per-thread context `calc_alg_context: &mut
//! CalculationAlgorithmContextBase` (the C++ `CCalculationAlgorithmContextBase*`).
//! `CIndividualProcessNode*` parameters become arena `NodeId`s resolved against
//! the context-owned `ProcessContext`
//! (`calc_alg_context.process_context().node(id)` for reads,
//! `…process_context_mut().node_mut(id)` for mutation — the W3.5 convention).
//! `CIndividualLinkEdge*` → `EdgeId`; `CClashedDependencyDescriptor*` → `ClashDescId`;
//! `CSortedNegLinker<CConcept*>*` → `&[NegLink<ConceptId>]` (the u06 convention);
//! `CIndividualProcessNode*&` out/in-out → `&mut NodeId`.
//!
//! Five methods port in full against the available arena accessors + sibling
//! method calls (`get_corrected_merged_into_individual_node`,
//! `expand_backend_cache_individual_nodes_nominal_merging`,
//! `are_individual_nodes_disjoint_roles_mergeable`, `get_merged_individual_nodes`,
//! `get_into_empty_merged_individual_node`). The remaining six are PORT-PENDING:
//! their control flow is driven start-to-finish by Process-layer subsystems that
//! are still struct-only stubs — `CDistinctHash` (distinct-edge lookup),
//! `CConnectionSuccessorSet` + its iterator, `CDisjointSuccessorRoleIterator` /
//! `CNegationDisjointEdge`, `CReapplyConceptLabelSet` iterators,
//! `CBranchingMergingProcessingRestrictionSpecification` + its candidate linkers,
//! the backend-cache synchronisation data, and the not-yet-ported clash-descriptor
//! factory (`createClashed*Descriptor`). Each keeps its faithful signature and a
//! full structural transcription of the C++ so a later wave fills it in without
//! re-reading the source; no logic is dropped.

#![allow(dead_code)]
#![allow(unused_variables)]

use super::super::model::substrate::{Cint64, NegLink};
use super::super::model::ConceptId;
use super::super::process::node::IndividualType;
use super::super::process::rs1::RoleSuccessorLinkIterator;
use super::super::process::{ClashDescId, ConProcDescId, EdgeId, NodeId, RestrictionSpecId, TrackPointId};
use super::context::CalculationAlgorithmContextBase;

impl super::algorithm::CompletionTaskHandleAlgorithm {
    // =======================================================================
    // initializeMergingIndividualNodes (cpp 15820–16063).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::initializeMergingIndividualNodes`.
    ///
    /// PORT-PENDING: the ≤n / choose-rule merging-candidate collector. The body is
    /// driven entirely by the `CBranchingMergingProcessingRestrictionSpecification`
    /// candidate-linker subsystem (`CBranchingMergingIndividualNodeCandidateLinker`),
    /// the `CSuccessorIndividualATMOSTReactivationData` reactivation linker, the
    /// `CDistinctHash` distinct bookkeeping, the ATMOST reapply descriptor
    /// (`CExtendedCondensedReapplyConceptDescriptorATMOSTReactivation`), the
    /// concept-role branching triggers (`CConceptRoleBranchingTrigger` off the
    /// concept's `CConceptProcessData`), and the clash-descriptor factory — none of
    /// which are ported. The clash path also `throw`s `CCalculationClashProcessingException`.
    ///
    /// C++ structure (cpp 15820–16063):
    /// ```text
    /// conDes = conProDes->getConceptDescriptor(); negate = conDes->getNegation()
    /// depTrackPoint = conProDes->getDependencyTrackPoint(); concept = conDes->getConcept()
    /// cardinality = concept->getParameter() - 1*negate
    /// chooseTriggerLinker = ((CConceptProcessData*)concept->getConceptData())->getConceptRoleBranchTrigger()
    /// firstLink = usingLastLink; collectMaxDistinctMergingNodes = true
    /// canInitMerging = !branchingMergingProcRest->hasMergingInitializationCandidates()
    /// // pick up newly-installed ATMOST-reactivation successor links (succ-choice triggering)
    /// if branchingMergingProcRest->hasSuccessorChoiceTriggeringInstalled() && count>0:
    ///   newTriggeredSuccLinker = succIndiATMOSTReactivationData->getReactivationSuccessorIndividualLinkLinker(conDes)
    ///   lastCheckedTriggeredSuccLinker = branchingMergingProcRest->getLastCheckedSuccessorChoiceTriggerLinker()
    ///   if differ: branchingMergingProcRest->setLastCheckedSuccessorChoiceTriggerLinker(newTriggeredSuccLinker)
    /// while roleSuccIt->hasNext() || newTriggeredSuccLinker != lastCheckedTriggeredSuccLinker:
    ///   link = roleSuccIt->next()  OR  next triggered-succ link (dec installed count, advance)
    ///   succIndi = getSuccessorIndividual(processIndi,link)
    ///   if containsIndividualNodeConcepts(succIndi,conceptOpLinkerIt,&containsNegation):
    ///     mergeIndiNodeCandLinker = new CBranchingMergingIndividualNodeCandidateLinker(succIndi,link)
    ///     if !containsNegation:
    ///       disHash = succIndi->getDistinctHash(false)
    ///       if collectMaxDistinctMergingNodes && disHash:   // grow the maximal mutually-distinct chain
    ///         if disIndiNodeCandLinker: test distinctToAllPrev via disHash->isIndividualDistinct(...);
    ///           if distinctToAllPrev: prepend, ++count, delayedCandAdded
    ///           else: flush current chain to branchingMergingProcRest->addMergingCandidateNodeLinker(...),
    ///                 keep the longer of {current,max} as max; reset chain
    ///         if !disIndiNodeCandLinker && disHash->getDistinctCount() >= maxDisIndiNodeCandCount:
    ///           start new chain with this cand
    ///       if !delayedCandAdded: branchingMergingProcRest->addMergingCandidateNodeLinker(mergeIndiNodeCandLinker)
    ///   else:   // concept not yet present on succ → either install a choose-trigger reapply, or queue both-qualify
    ///     scan chooseTriggerLinker for a concept-trigger already present on succIndi (matching negation):
    ///       if found: branchingMergingProcRest->setSuccessorChoiceTriggeringInstalled(true); inc count;
    ///                 reapplyQueue = processIndi->getConceptReapplyQueue(triggeringConcept,triggerNegation,true)
    ///                 reapplyATMOSTConDes = new CExtendedCondensedReapplyConceptDescriptorATMOSTReactivation;
    ///                 reapplyATMOSTConDes->initAtmostExtendedReapllyDescriptor(conDes,depTrackPoint,!triggerNegation,branchingMergingProcRest,processIndi,link)
    ///                 reapplyQueue->addReapplyConceptDescriptor(reapplyATMOSTConDes)
    ///       else: branchingMergingProcRest->addBothQualifyCandidateNodeLinker(new cand(succIndi,link))
    ///   if !firstLink: firstLink = link
    /// // flush trailing distinct chain, keep the longest as max
    /// if maxDisIndiNodeCandLinker:
    ///   if canInitMerging || maxDisIndiNodeCandCount > cardinality:
    ///     // collect pairwise distinct-edge clashes among the first (cardinality+1) candidates
    ///     for cand in maxChain (<= cardinality+1):
    ///       for cand2 in rest: disEdge = cand.disHash->getIndividualDistinctEdge(cand2.id);
    ///         if disEdge.depTrackPoint not yet seen: insert; (2nd distinct ⇒ multipleDistinctInitClashes)
    ///           distinctInitClashes = createClashedIndividualDistinctDescriptor(distinctInitClashes,disEdge,dtp)
    ///       distinctInitClashes = createIndividualMergeCausingDescriptors(distinctInitClashes,cand,cand.link,conceptOpLinkerIt)
    ///     if maxDisIndiNodeCandCount > cardinality:   // too many mutually-distinct ⇒ clash
    ///       distinctInitClashes = createClashedConceptDescriptor(distinctInitClashes,processIndi,conDes,depTrackPoint)
    ///       throw CCalculationClashProcessingException(distinctInitClashes)
    ///     branchingMergingProcRest->set{Multiple,}MergingNodesInitializationClashesDescriptors(distinctInitClashes)
    ///     branchingMergingProcRest->addMergingInitializationCandidateNodeLinker(maxDisIndiNodeCandLinker)
    ///   else: branchingMergingProcRest->addMergingCandidateNodeLinker(maxDisIndiNodeCandLinker)
    /// if firstLink: branchingMergingProcRest->setLastIndividualLink(firstLink)
    /// // qualify the pos/neg-only candidate nodes: add the operand concepts (qualifying polarity) to a localized copy
    /// for i in {0,1}: qualPosNeg = (i==1); linker = get{Only,}{Pos,Neg}QualifyCandidateNodeLinker()
    ///   for cand in linker:
    ///     locQualifyIndiNode = getLocalizedIndividual(cand,true)
    ///     addConceptsToIndividual(conceptOpLinkerIt,qualPosNeg,locQualifyIndiNode,null,true,true,null)
    ///     addIndividualToProcessingQueue(locQualifyIndiNode)
    ///     if !qualPosNeg: branchingMergingProcRest->addMergingCandidateNodeLinker(cand)
    /// branchingMergingProcRest->clearOnly{Neg,Pos}QualifyCandidateNodeLinker()
    /// ```
    pub fn initialize_merging_individual_nodes(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        role_succ_it: &mut RoleSuccessorLinkIterator,
        using_last_link: EdgeId,
        concept_op_linker_it: &[NegLink<ConceptId>],
        branching_merging_proc_rest: RestrictionSpecId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let _ = (
            process_indi,
            con_pro_des,
            role_succ_it,
            using_last_link,
            concept_op_linker_it,
            branching_merging_proc_rest,
            calc_alg_context,
        );
        // PORT-PENDING: see structural transcription above. Needs the
        // branching-merging restriction-spec candidate-linker subsystem, the
        // distinct hash, the ATMOST-reactivation reapply descriptor, the
        // concept-role branching triggers, the localization / queue / clash-factory
        // helpers, and the clash-processing exception — none ported yet.
        todo!(
            "W6-DEFER: initializeMergingIndividualNodes — branching-merging candidate \
             subsystem + distinct hash + ATMOST reapply + clash factory unported"
        );
    }

    // =======================================================================
    // getCorrectedMergedIntoIndividualNode (cpp 16264–16270). FULLY PORTED.
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getCorrectedMergedIntoIndividualNode`.
    ///
    /// Follows the merged-into chain to the surviving node: while `indi` has been
    /// merged into another node, replace it by the up-to-date version of that node.
    pub fn get_corrected_merged_into_individual_node(
        &mut self,
        mut indi: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        while calc_alg_context
            .process_context()
            .node(indi)
            .has_merged_into_individual_node_id()
        {
            let merged_into_id = calc_alg_context
                .process_context()
                .node(indi)
                .merged_into_individual_node_id();
            indi = self.get_up_to_date_individual_by_id(merged_into_id, calc_alg_context);
        }
        indi
    }

    // =======================================================================
    // createIndividualMergeCausingDescriptors (cpp 16690–16713).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::createIndividualMergeCausingDescriptors`.
    ///
    /// PORT-PENDING: gathers the clash descriptors that explain why a merge would be
    /// forced — the link dependency (when it differs from the node's) plus, for each
    /// concept to be added, the descriptor of that concept already present in the
    /// node's label set. Driven by the not-yet-ported clash-descriptor factory
    /// (`createClashedIndividualLinkDescriptor` / `createClashedConceptDescriptor`)
    /// and the `CReapplyConceptLabelSet::getConceptDescriptor` out-param lookup.
    ///
    /// C++ structure (cpp 16690–16713):
    /// ```text
    /// clashDes = prevClashes
    /// if link->getDependencyTrackPoint() != processIndi->getDependencyTrackPoint():
    ///   clashDes = createClashedIndividualLinkDescriptor(clashDes,link,link->getDependencyTrackPoint())
    /// conSet = processIndi->getReapplyConceptLabelSet(false)
    /// for (concept,conNegation) in conceptAddLinker:
    ///   conSet->getConceptDescriptor(concept,&containedConDes,&containedDepTrackPoint)
    ///   clashDes = createClashedConceptDescriptor(clashDes,processIndi,containedConDes,containedDepTrackPoint)
    /// return clashDes
    /// ```
    pub fn create_individual_merge_causing_descriptors(
        &mut self,
        prev_clashes: ClashDescId,
        process_indi: &mut NodeId,
        link: EdgeId,
        concept_add_linker: &[NegLink<ConceptId>],
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> ClashDescId {
        let _ = (
            prev_clashes,
            process_indi,
            link,
            concept_add_linker,
            calc_alg_context,
        );
        // PORT-PENDING: clash-descriptor factory (createClashedIndividualLinkDescriptor /
        // createClashedConceptDescriptor) + label-set getConceptDescriptor unported.
        todo!(
            "W6-DEFER: createIndividualMergeCausingDescriptors — clash-descriptor factory unported"
        );
    }

    // =======================================================================
    // isIndividualNodesMergeableWithoutNewRuleApplications (cpp 20481–20639).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::isIndividualNodesMergeableWithoutNewRuleApplications`.
    ///
    /// PORT-PENDING: the cheap "can these two nodes be merged without triggering new
    /// rule applications" pre-test used by possible-instance / nominal merging.
    /// Driven by the `CReapplyConceptLabelSet` iterators + `containsConcept`, the
    /// `CConceptOperator` operator-flag tests, the role-successor iterators
    /// (`getRoleSuccessorLinkIterator` / `getRoleSuccessorCount`), the
    /// `CDistinctHash` distinct-edge lookup, the clash-descriptor factory, and the
    /// sibling `isLabelConceptClashSet` (unit u18/u19) + `areIndividualNodesDisjointRolesMergeable`.
    ///
    /// C++ structure (cpp 20481–20639):
    /// ```text
    /// disHash = mergeIntoIndi1->getDistinctHash(false)
    /// if isLabelConceptClashSet(indi2.label, mergeIntoIndi1.label, &labelIsSubsetByIgnoringNominals, true):
    ///   return false
    /// else if mergingPossiblyRequiresRuleApplications && !labelIsSubsetByIgnoringNominals:
    ///   *mergingPossiblyRequiresRuleApplications = true; if cancelOnPossiblyNewRuleApplications: return false
    /// if mergingPossiblyRequiresRuleApplications && labelIsSubsetByIgnoringNominals:
    ///   for conDes in mergeIntoIndi1.label (while !*flag):
    ///     concept=conDes.concept; conNeg=conDes.negated; opCode=concept.opCode; role=concept.role; opLinker=concept.operands
    ///     if (!conNeg && operator.hasPartialOperatorCodeFlag(CCFS_ALL_AQALL_TYPE)) || (conNeg && opCode==CCSOME):
    ///       for link in indi2.roleSuccessors(role): succIndi=getSuccessorIndividual(indi2,link)
    ///         for opConcept in opLinker (opConNeg = opLinker.negated ^ conNeg):
    ///           if succIndi.label.containsConcept(concept,&containsNeg):
    ///             if containsNeg != opConNeg: return false
    ///           else: *flag=true; if cancel: return false
    ///     else if (!conNeg && opCode==CCATMOST) || (conNeg && opCode==CCATLEAST):
    ///       cardinality = concept.parameter - (conNeg?1:0)
    ///       usedCount=mergeIntoIndi1.roleSuccessorCount(role); requiredCount=indi2.roleSuccessorCount(role)
    ///       if usedCount+requiredCount > cardinality:
    ///         // count trivially (non)mergable successors until the bound is decided
    ///         for link in indi2.roleSuccessors(role) while bound undecided:
    ///           succIndi=getSuccessorIndividual(indi2,link); mergeable=true; successorRelevant=false
    ///           if succIndi.isNominal: ... (relevant if any operand concept missing/matching) ; if relevant && !mergeIntoIndi1.hasRoleSuccessorToIndividual(role,succIndi): mergeable=false
    ///           else if succIndi.hasPartialProcessingRestrictionFlags(PRFCONCRETEDATAINDINODE): successorRelevant=true
    ///           tally triviallyMergableCount / triviallyNonMergableCount
    ///         if usedCount+requiredCount-triviallyMergableCount > cardinality: *flag=true; if cancel: return false
    /// // distinct / UNA / disjoint-role clash gates
    /// if disHash && disHash->getIndividualDistinctEdge(indi2.id): createClashedIndividualDistinctDescriptor; return false
    /// if mConfUniqueNameAssumption && both nominal && differing nominal individual: createClashedConceptDescriptor x2; return false
    /// if !areIndividualNodesDisjointRolesMergeable(mergeIntoIndi1,indi2,clashDescriptors): return false
    /// return true
    /// ```
    pub fn is_individual_nodes_mergeable_without_new_rule_applications(
        &mut self,
        merge_into_indi1: NodeId,
        indi2: NodeId,
        merging_possibly_requires_rule_applications: Option<&mut bool>,
        cancel_on_possibly_new_rule_applications: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let _ = (
            merge_into_indi1,
            indi2,
            merging_possibly_requires_rule_applications,
            cancel_on_possibly_new_rule_applications,
            calc_alg_context,
        );
        // PORT-PENDING: label-set iterators + concept-operator flags + role-successor
        // iterators + distinct hash + clash factory + sibling isLabelConceptClashSet
        // unported.
        todo!(
            "W6-DEFER: isIndividualNodesMergeableWithoutNewRuleApplications — label/role/distinct \
             subsystems + clash factory unported"
        );
    }

    // =======================================================================
    // expandBackendCacheIndividualNodesNominalMerging (cpp 20644–20651). FULLY PORTED.
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::expandBackendCacheIndividualNodesNominalMerging`.
    ///
    /// For each neighbour of `indi1`/`indi2`, expand the backend-cache neighbouring
    /// connections in both directions; returns whether anything was expanded.
    pub fn expand_backend_cache_individual_nodes_nominal_merging(
        &mut self,
        indi1: NodeId,
        indi2: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // check for each neighbour of indi1, whether there is a neighbouring link in
        // the backend cache to that individual for indi2 and vice versa
        let mut expanded = false;
        expanded |= self
            .expand_backend_cache_individual_nodes_nominal_merging_neighbouring_connections(
                indi1,
                indi2,
                calc_alg_context,
            );
        expanded |= self
            .expand_backend_cache_individual_nodes_nominal_merging_neighbouring_connections(
                indi2,
                indi1,
                calc_alg_context,
            );
        expanded
    }

    // =======================================================================
    // expandBackendCacheIndividualNodesNominalMergingNeighbouringConnections
    // (cpp 20655–20710).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::expandBackendCacheIndividualNodesNominalMergingNeighbouringConnections`.
    ///
    /// PORT-PENDING: walks `indi1`'s connection-successor set and, for each nominal
    /// neighbour that `indi2` lacks but the backend cache records, expands that
    /// neighbour for `indi2` from the cache. Driven by the unported
    /// `CConnectionSuccessorSet` iterator and the backend-cache synchronisation /
    /// association / neighbour-role-set subsystem
    /// (`CIndividualNodeRepresentativeMemoryBackendCacheSynchronisationData`,
    /// `CBackendRepresentativeMemoryCacheIndividualAssociationData`,
    /// `CBackendRepresentativeMemoryCacheIndividualNeighbourRoleSetHash`) plus the
    /// sibling `expandIndividualNeighbourNodeFromBackendCache` (unit u27).
    ///
    /// C++ structure (cpp 20655–20710):
    /// ```text
    /// connSuccSet1 = indi1->getConnectionSuccessorSet(false)
    /// if connSuccSet1 && !indi1->getNominalIndividual():
    ///   backendSyncData2 = indi2->getIndividualBackendCacheSynchronisationData(false)
    ///   assData2 = backendSyncData2->getAssocitaionData()
    ///   neighbourRoleSetHash2 = assData2->getNeighbourRoleSetHash()
    ///   if neighbourRoleSetHash2:
    ///     for conn1ID in connSuccSet1:
    ///       if conn1ID == indi1ID: if !indi2->hasSuccessorIndividualNode(indi2ID) && hash2.label(indi2ID): list += indi2ID
    ///       else if conn1ID <= 0: if !indi2->hasSuccessorIndividualNode(conn1ID) && hash2.label(conn1ID): list += conn1ID
    ///     for id in list: expanded |= expandIndividualNeighbourNodeFromBackendCache(indi2,id)
    ///     return expanded
    /// return false
    /// ```
    pub fn expand_backend_cache_individual_nodes_nominal_merging_neighbouring_connections(
        &mut self,
        indi1: NodeId,
        indi2: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let _ = (indi1, indi2, calc_alg_context);
        // PORT-PENDING: connection-successor set iterator + backend-cache
        // synchronisation/association/neighbour-role-set subsystem +
        // expandIndividualNeighbourNodeFromBackendCache unported.
        todo!(
            "W6-DEFER: expandBackendCacheIndividualNodesNominalMergingNeighbouringConnections — \
             connection-successor set + backend cache subsystem unported"
        );
    }

    // =======================================================================
    // isIndividualNodesMergeable (cpp 20714–20751).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::isIndividualNodesMergeable`.
    ///
    /// PORT-PENDING: the full mergeability test (distinct-edge / UNA / label-clash /
    /// disjoint-role gates), accumulating clash descriptors. Driven by the
    /// `CDistinctHash` distinct-edge lookup, the clash-descriptor factory, and the
    /// siblings `expandBackendCacheIndividualNodesNominalMerging` (this unit),
    /// `isLabelConceptClashSet` (unit u18/u19), `areIndividualNodesDisjointRolesMergeable`
    /// (this unit).
    ///
    /// C++ structure (cpp 20714–20751):
    /// ```text
    /// disHash = indi1->getDistinctHash(false)
    /// expandBackendCacheIndividualNodesNominalMerging(indi1,indi2)
    /// if disHash && disHash->getIndividualDistinctEdge(indi2.id):
    ///   clashDescriptors = createClashedIndividualDistinctDescriptor(...); return false
    /// if mConfUniqueNameAssumption && indi1.nominal && indi2.nominal && indi1.nominalIndividual != indi2.nominalIndividual:
    ///   clashDescriptors = createClashedConceptDescriptor(...) x2; return false
    /// if isLabelConceptClashSet(indi1,indi2,clashDescriptors): return false
    /// if !areIndividualNodesDisjointRolesMergeable(indi1,indi2,clashDescriptors): return false
    /// return true
    /// ```
    pub fn is_individual_nodes_mergeable(
        &mut self,
        indi1: NodeId,
        indi2: NodeId,
        clash_descriptors: &mut ClashDescId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let _ = (indi1, indi2, clash_descriptors, calc_alg_context);
        // PORT-PENDING: distinct hash distinct-edge lookup + clash-descriptor factory
        // + sibling isLabelConceptClashSet unported.
        todo!(
            "W6-DEFER: isIndividualNodesMergeable — distinct hash + clash factory + \
             isLabelConceptClashSet unported"
        );
    }

    // =======================================================================
    // areIndividualNodesDisjointRolesMergeable (cpp 20754–20764). FULLY PORTED.
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::areIndividualNodesDisjointRolesMergeable`.
    ///
    /// If either node has disjoint-role connections, the disjoint-role test must hold
    /// in both directions for the merge to be admissible.
    pub fn are_individual_nodes_disjoint_roles_mergeable(
        &mut self,
        indi1: NodeId,
        indi2: NodeId,
        clash_descriptors: &mut ClashDescId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let indi1_disjoint = calc_alg_context
            .process_context()
            .node(indi1)
            .has_disjoint_role_connections();
        let indi2_disjoint = calc_alg_context
            .process_context()
            .node(indi2)
            .has_disjoint_role_connections();
        if indi1_disjoint || indi2_disjoint {
            if !self.is_individual_node_disjoint_roles_mergeable(
                indi1,
                indi2,
                clash_descriptors,
                calc_alg_context,
            ) {
                return false;
            }
            if !self.is_individual_node_disjoint_roles_mergeable(
                indi2,
                indi1,
                clash_descriptors,
                calc_alg_context,
            ) {
                return false;
            }
        }
        true
    }

    // =======================================================================
    // isIndividualNodeDisjointRolesMergeable (cpp 20767–20863).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::isIndividualNodeDisjointRolesMergeable`.
    ///
    /// PORT-PENDING: tests the directed half of the disjoint-role merge check — for
    /// each connection of `indi1`, whether merging would create a role link on a role
    /// declared disjoint from one already present, which clashes. Driven by the
    /// unported `CConnectionSuccessorSet` iterator, the
    /// `CDisjointSuccessorRoleIterator` / `CNegationDisjointEdge` machinery,
    /// `getRoleSuccessorToIndividualLink`, the clash-descriptor factory, and the
    /// sibling `getUpToDateIndividual`.
    ///
    /// C++ structure (cpp 20767–20863):
    /// ```text
    /// connSuccSet = indi1->getConnectionSuccessorSet(false); indiID=indi1.id; othIndiID=indi2.id
    /// if connSuccSet:
    ///   for connID in connSuccSet:
    ///     if connID == indiID:               // self links
    ///       for disNegLink in indi1->getDisjointSuccessorRoleIterator(indi1):
    ///         link = indi2->getRoleSuccessorToIndividualLink(disNegLink.role,indi2,false)
    ///         if link: clash(link)+clash(disNegLink); return false
    ///     else if othIndiID == connID:       // ancestor/successor merging link clashes (4 self tests)
    ///       for disNegLink in indi2->getDisjointSuccessorRoleIterator(indi1):
    ///         test indi2→indi2, indi1→indi1, indi2→indi1, indi1→indi2 role-successor links; on hit clash+clash; return false
    ///     else:                              // a third connected node connIndi
    ///       connIndi = getUpToDateIndividual(connID)
    ///       for disNegLink in connIndi->getDisjointSuccessorRoleIterator(indi1):
    ///         link = connIndi->getRoleSuccessorToIndividualLink(disNegLink.role,indi2,false); on hit clash+clash; return false
    ///       for disNegLink in indi1->getDisjointSuccessorRoleIterator(connIndi):
    ///         link = indi2->getRoleSuccessorToIndividualLink(disNegLink.role,connIndi,false); on hit clash+clash; return false
    /// return true
    /// ```
    pub fn is_individual_node_disjoint_roles_mergeable(
        &mut self,
        indi1: NodeId,
        indi2: NodeId,
        clash_descriptors: &mut ClashDescId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let _ = (indi1, indi2, clash_descriptors, calc_alg_context);
        // PORT-PENDING: connection-successor set iterator + disjoint-successor-role
        // iterator / negation-disjoint edges + clash factory + getUpToDateIndividual
        // unported.
        todo!(
            "W6-DEFER: isIndividualNodeDisjointRolesMergeable — connection/disjoint-role \
             iterators + clash factory unported"
        );
    }

    // =======================================================================
    // getMergedIndividualNodes (cpp 20936–20985). FULLY PORTED.
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getMergedIndividualNodes`.
    ///
    /// Picks which of the two nodes survives the merge (`switchNodes` decision tree:
    /// constructed node / nominal level / nominal preference / ancestor depth), then
    /// grafts the other into it via `mergeIndividualNodeInto` (unit u15) and returns
    /// the survivor.
    pub fn get_merged_individual_nodes(
        &mut self,
        prefered_merge_into_individual_node: &mut NodeId,
        individual2: &mut NodeId,
        merge_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        let prefered = *prefered_merge_into_individual_node;
        let indiv2 = *individual2;

        let mut switch_nodes = false;

        // KONCLUDE-PORT-NOTE[ownership]: `individualComputation` is
        // `getUsedSatisfiableCalculationTask()->getSatisfiableRepresentativeBackendCacheUpdatingAdapter() != nullptr`.
        // W6-DEFER[api]: the satisfiable-calculation-task adapter (Task subsystem) is
        // not ported; with no adapter present this is `false` (the default
        // completion-graph case), preserving the decision-tree structure below.
        let individual_computation = false;

        // Pre-read the node scalars the decision tree compares (all `&self` reads).
        let prefered_id = calc_alg_context.process_context().node(prefered).individual_node_id();
        let indiv2_id = calc_alg_context.process_context().node(indiv2).individual_node_id();
        let prefered_nominal = calc_alg_context.process_context().node(prefered).is_nominal_individual_node();
        let indiv2_nominal = calc_alg_context.process_context().node(indiv2).is_nominal_individual_node();
        let prefered_nom_level = calc_alg_context.process_context().node(prefered).individual_nominal_level();
        let indiv2_nom_level = calc_alg_context.process_context().node(indiv2).individual_nominal_level();
        let prefered_anc_depth = calc_alg_context.process_context().node(prefered).individual_ancestor_depth();
        let indiv2_anc_depth = calc_alg_context.process_context().node(indiv2).individual_ancestor_depth();
        let indiv2_nominal_individual_null =
            calc_alg_context.process_context().node(indiv2).nominal_individual().is_none();
        let opt_merge_constructed = self.opt_merge_constructed_individual_node;

        // `procDataBox->getConstructedIndividualNode()->getIndividualNodeID()`.
        let constructed_node = calc_alg_context.processing_data_box().constructed_individual_node();
        let constructed_id = if constructed_node.is_none() {
            // No constructed node yet ⇒ cannot match either id; matches the C++ where
            // the constructed-node arms are only reached once it has been created.
            Cint64::MIN
        } else {
            calc_alg_context.process_context().node(constructed_node).individual_node_id()
        };

        if !individual_computation && !opt_merge_constructed && constructed_id == prefered_id {
            switch_nodes = false;
        } else if !individual_computation
            && !opt_merge_constructed
            && indiv2_nominal_individual_null
            && constructed_id == indiv2_id
        {
            switch_nodes = true;
        } else if prefered_nominal && indiv2_nominal {
            if indiv2_nom_level < prefered_nom_level {
                switch_nodes = true;
            } else if indiv2_nom_level == prefered_nom_level {
                if indiv2_id > prefered_id {
                    switch_nodes = true;
                }
            }
        } else if prefered_nominal {
            switch_nodes = false;
        } else if indiv2_nominal {
            switch_nodes = true;
        } else if calc_alg_context
            .process_context()
            .node(prefered)
            .is_individual_ancestor(calc_alg_context.process_context().node(indiv2))
        {
            switch_nodes = false;
        } else if calc_alg_context
            .process_context()
            .node(indiv2)
            .is_individual_ancestor(calc_alg_context.process_context().node(prefered))
        {
            switch_nodes = true;
        } else if indiv2_anc_depth < prefered_anc_depth {
            switch_nodes = true;
            // TODO (Konclude): a secondary tie-break on individual id is commented out.
        }

        let mut merged_individual;
        let mut adding_individual;
        if !switch_nodes {
            merged_individual = prefered;
            adding_individual = indiv2;
        } else {
            merged_individual = indiv2;
            adding_individual = prefered;
        }
        self.merge_individual_node_into(
            merged_individual,
            adding_individual,
            merge_dep_track_point,
            calc_alg_context,
        );
        merged_individual
    }

    // =======================================================================
    // getIntoEmptyMergedIndividualNode (cpp 20990–21006). FULLY PORTED.
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getIntoEmptyMergedIndividualNode`.
    ///
    /// Creates a fresh empty node (carrying the merging node's nominal level / ancestor
    /// depth / type, or made a fresh nominal one level below `mergerNode`), grafts the
    /// merging node into it via `mergeIndividualNodeInto` (unit u15), and returns it.
    pub fn get_into_empty_merged_individual_node(
        &mut self,
        merging_individual_node: &mut NodeId,
        create_as_nominal: bool,
        merger_node: NodeId,
        merge_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        let new_empty_indi_node = self.create_new_empty_individual(calc_alg_context);
        if !create_as_nominal {
            let merging = *merging_individual_node;
            let nominal_level = calc_alg_context.process_context().node(merging).individual_nominal_level();
            let ancestor_depth = calc_alg_context.process_context().node(merging).individual_ancestor_depth();
            let merging_is_nominal = calc_alg_context.process_context().node(merging).is_nominal_individual_node();
            {
                let node = calc_alg_context.process_context_mut().node_mut(new_empty_indi_node);
                node.set_individual_nominal_level(nominal_level);
                node.set_individual_ancestor_depth(ancestor_depth);
                if merging_is_nominal {
                    node.set_individual_type(IndividualType::Nominal);
                } else {
                    node.set_individual_type(IndividualType::Blockable);
                }
            }
        } else {
            let merger_nom_level =
                calc_alg_context.process_context().node(merger_node).individual_nominal_level();
            {
                let node = calc_alg_context.process_context_mut().node_mut(new_empty_indi_node);
                node.set_individual_type(IndividualType::Nominal);
                node.set_individual_nominal_level(merger_nom_level + 1);
            }
        }
        let mut new_empty_indi_node_ref = new_empty_indi_node;
        self.merge_individual_node_into(
            new_empty_indi_node_ref,
            *merging_individual_node,
            merge_dep_track_point,
            calc_alg_context,
        );
        new_empty_indi_node
    }
}
