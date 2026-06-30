//! `completion::u20` — port unit #20 of the completion task-handle algorithm
//! (family: Blocking (pairwise / label-optimized / dynamic); 17 methods,
//! cpp ranges 19326–27648).
//!
//! Source (READ-ONLY): Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`.
//! Ported methods (in cpp order):
//!   - `getAnywhereBlockingIndividualNodeLinkedCanidateHashed`           [19326]
//!   - `getAnywhereBlockingIndividualNodeCanidateHashed`                 [19467]
//!   - `getBlockingIndividualNodeCandidateIterator`                      [19571]
//!   - `propagateIndirectSuccessorBlocking`                              [19690]
//!   - `propagateAddingBlockedProcessingRestrictionToSuccessors`        [19789]
//!   - `reactivateIndirectBlockedSuccessors`                             [19851]
//!   - `reactivateBlockedIndividuals`                                    [19871]
//!   - `isIndividualNodeProcessingBlocked`                               [19997]
//!   - `isIndividualNodeExpansionBlocked`                               [20042]
//!   - `needsIndividualNodeExpansionBlockingTest`                        [20049]
//!   - `propagateIndirectSuccessorSaturationBlocked`                     [21861]
//!   - `tryEstablishExpansionBlockingWithBackendCacheSynchronisation`    [22587]
//!   - `testIndividualNodeBackendCacheExpansionBlockingCriticalCardinality` [23196]
//!   - `testIndividualNodeBackendCacheNeighbourExpansionBlockingCritical`   [26037]
//!   - `testIndividualNodeConceptBackendCacheNeighbourExpansionBlockingCritical` [26177]
//!   - `addBlockingCoreConcept`                                          [26871]
//!   - `addIndividualToBlockingUpdateReviewProcessingQueue`             [27643]
//!
//! KONCLUDE-PORT-NOTE[ownership]: pointers become arena ids
//! (`CIndividualProcessNode*` → `NodeId`, `CConceptDescriptor*` → `ConDescId`,
//! `CConceptProcessDescriptor*` → `ConProcDescId`, `CIndividualLinkEdge*` →
//! `EdgeId`); the `calcAlgContext` pointer becomes a threaded
//! `&mut CalculationAlgorithmContextBase`. Per the W3.5 accessor convention a C++
//! `indi->getX()` resolves to `calc_alg_context.process_context().node(id).get_x()`
//! (read) / `…process_context_mut().node_mut(id).set_x(v)` (mutate); the static
//! `concept->...` resolves through `calc_alg_context.ontology_arenas().concept(id)`;
//! the databox is reached via `calc_alg_context.processing_data_box_mut()`.
//!
//! KONCLUDE-PORT-NOTE[api]: the anywhere-blocking + backend-cache machinery is
//! built on per-node SATELLITE / backend-cache types that are not yet ported —
//! `CIndividualNodeBlockingTestData` (`IndiBlockDataId`),
//! `CBlockingAlternativeData**` (opaque handle),
//! `CBlockingIndividualNodeLinkedCandidateHash` / `…CandidateData` / `…Linker`,
//! `CBlockingIndividualNodeCandidateHash` / `…Iterator`, `CNodeSwitchHistory`,
//! `CReapplyConceptLabelSet` (core-concept / adding-sorted descriptor chains),
//! `CReapplyRoleSuccessorHash`, `CIndividualNodeRepresentativeMemoryBackendCacheSynchronisationData`
//! and `CBackendRepresentativeMemoryCacheIndividualAssociationData` (+ their label /
//! cardinality cache entries), and `mBackendCacheHandler`. Each method on one of
//! these types is reproduced as a `// W6-DEFER[api]` stub returning the
//! null/empty value (`Id::NONE` / `INVALID` / `false` / empty `Vec`), so the
//! branch + loop structure and order of operations are preserved EXACTLY without
//! fabricating the absent behaviour. The node-flag operations, the databox / node
//! arena getters, the concept-arena reads, and the cross-unit `self.x(...)`
//! sibling completion calls are reproduced verbatim. No logic is dropped — only
//! the unported satellite-method dereferences are stubbed.
//!
//! Cross-unit sibling completion methods land in later units and are invoked as
//! `self.x(...)` per the port convention (`clear_blocking_cache`,
//! `continue_individual_node_block`, `signature_cached_individual_node_block`,
//! `is_individual_node_valid_blocker` (u18), `is_individual_node_blocking`,
//! `is_individual_node_concept_label_set_modified`, `get_up_to_date_individual`,
//! `get_up_to_date_individual_by_id`, `get_localized_individual`,
//! `get_ancestor_individual`, `get_successor_individual`,
//! `propagate_adding_blocked_processing_restriction_to_successors`,
//! `propagate_clearing_processing_restriction_to_successors` (u03),
//! `eliminiate_blocked_individuals` (u18), `add_individual_to_processing_queue`
//! (u04), `is_saturation_cached_processing_blocked`,
//! `is_individual_node_completion_graph_cached`,
//! `is_satisfiable_cached_processing_blocked`,
//! `is_signature_blocked_processing_blocked`,
//! `detect_individual_node_blocked_status`,
//! `test_individual_node_backend_cache_concepts_synchronization`,
//! `test_individual_node_backend_cache_new_mergings`,
//! `get_localized_individual_backend_cache_snychronisation_data`,
//! `get_backend_cache_role_representative_neighbour_count`,
//! `has_nondeterministic_dependency`).

#![allow(dead_code, unused_variables, unused_mut, unused_assignments)]

use super::super::model::op::{
    CCALL, CCAND, CCAQAND, CCAQSOME, CCATLEAST, CCATMOST, CCBRANCHAQAND, CCEQ, CCF_ATLEAST,
    CCF_ATMOST, CCF_VALUE, CCFS_ALL_AQALL_TYPE, CCFS_SOME_TYPE, CCIMPLAQAND, CCOR, CCSOME,
};
use super::super::model::substrate::{Cint64, Id, NegLink, INVALID};
use super::super::model::{ConceptId, RoleId};
use super::super::process::node::IndividualProcessNode;
use super::super::process::stubs::{BackendSyncDataId, IndiBlockDataId};
use super::super::process::{ConDescId, ConProcDescId, EdgeId, LabelSetId, NodeId};

use super::context::CalculationAlgorithmContextBase;

/// KONCLUDE-PORT-NOTE[api]: `CBlockingAlternativeData*` / `**` is not yet ported;
/// modelled as an opaque handle (`INVALID` == `nullptr`), matching `u18`.
type BlockingAlternativeDataHandle = Cint64;

/// KONCLUDE-PORT-NOTE[api]: `CBlockingIndividualNodeCandidateIterator` (a stack
/// value returned by `getBlockingIndividualNodeCandidateIterator`) is not yet
/// ported; modelled as an opaque handle (`INVALID` == an exhausted iterator).
type BlockingIndividualNodeCandidateIteratorHandle = Cint64;

impl super::algorithm::CompletionTaskHandleAlgorithm {
    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getAnywhereBlockingIndividualNodeLinkedCanidateHashed`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: the `CIndividualNodeBlockingTestData` (`locBlockData`)
    /// core-concept-descriptor cursors and the `CBlockingIndividualNodeLinkedCandidateHash`
    /// minimum-candidate-count search are on not-yet-ported satellites; `coreConDesLinker`
    /// (from the unported `CReapplyConceptLabelSet::getCoreConceptDescriptorLinker`) is
    /// `INVALID`, so the faithful translation currently takes the `!coreConDesLinker`
    /// branch and delegates to `getAnywhereBlockingIndividualNodeCanidateHashed`. The
    /// else-branch's per-candidate validity / descendant / blocking test is reproduced
    /// over the (currently empty) candidate node list.
    pub fn get_anywhere_blocking_individual_node_linked_canidate_hashed(
        &mut self,
        blocking_test_indi: NodeId,
        mut block_alt_data: BlockingAlternativeDataHandle,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        self.clear_blocking_cache(calc_alg_context);
        // W3-DEFER[memory-pool]: taskMemMan = calcAlgContext->getUsedProcessTaskMemoryAllocationManager();
        let mut blocker_node: NodeId = Id::NONE;
        let block_data: IndiBlockDataId = calc_alg_context
            .process_context()
            .node(blocking_test_indi)
            .individual_block_data(false);
        let mut loc_block_data: IndiBlockDataId = calc_alg_context
            .process_context()
            .node(blocking_test_indi)
            .individual_block_data(true);
        if loc_block_data == Id::NONE {
            // W6-DEFER[memory-pool]: locBlockData = alloc CIndividualNodeBlockingTestData;
            //   locBlockData->initBlockData(blockData);
            calc_alg_context
                .process_context_mut()
                .node_mut(blocking_test_indi)
                .set_individual_block_data(loc_block_data);
        }

        let mut continue_blocking_indi_node: NodeId = Id::NONE;
        if self.continue_individual_node_block(
            blocking_test_indi,
            loc_block_data,
            &mut continue_blocking_indi_node,
            &mut block_alt_data,
            calc_alg_context,
        ) {
            blocker_node = continue_blocking_indi_node;
        } else {
            // W6-DEFER[api]: locBlockData->clearBlockingIndividualNode();
            if self.signature_cached_individual_node_block(
                blocking_test_indi,
                loc_block_data,
                &mut continue_blocking_indi_node,
                &mut block_alt_data,
                calc_alg_context,
            ) {
                blocker_node = continue_blocking_indi_node;
            } else {
                let mut last_continue_tested_blocking_indi_node_id: Cint64 = -1;
                // W6-DEFER[api]: if (locBlockData->getBlockingIndividualNode())
                //   lastContinueTestedBlockingIndiNodeID =
                //     locBlockData->getBlockingIndividualNode()->getIndividualNodeID();

                // procDataBox->getBlockingIndividualNodeLinkedCandidateHash(false)
                let _blocking_cand_hash = calc_alg_context
                    .processing_data_box_mut()
                    .blocking_individual_node_linked_candidate_hash(false);
                // conSet = blockingTestIndi->getReapplyConceptLabelSet(false)
                let _con_set: LabelSetId = calc_alg_context
                    .process_context_mut()
                    .node_mut(blocking_test_indi)
                    .get_reapply_concept_label_set(false);
                // W6-DEFER[api]: coreConDesLinker = conSet->getCoreConceptDescriptorLinker();
                let core_con_des_linker: Cint64 = INVALID;
                let blocking_test_indi_id = calc_alg_context
                    .process_context()
                    .node(blocking_test_indi)
                    .individual_node_id();

                if core_con_des_linker == INVALID {
                    blocker_node = self.get_anywhere_blocking_individual_node_canidate_hashed(
                        blocking_test_indi,
                        block_alt_data,
                        calc_alg_context,
                    );
                } else {
                    // W6-DEFER[api]: minimum-candidate-count search over the core-concept
                    //   descriptor chain (locBlockData last-core cursors +
                    //   blockingCandHash->getBlockingIndividualCandidateData(conDes)->getCandidateCount());
                    //   yields `minBlockingIndNodeCandData->getBlockingCandidatesIndividualNodeLinker()`.
                    //   All operands are on unported satellites; the resulting candidate
                    //   node list is currently empty. The per-candidate test below is faithful.
                    let blocking_cand_nodes: Vec<NodeId> = Vec::new();
                    for blocker_cand_indi_node in blocking_cand_nodes {
                        if blocker_node != Id::NONE {
                            break;
                        }
                        let blocker_cand_indi_node_id = calc_alg_context
                            .process_context()
                            .node(blocker_cand_indi_node)
                            .individual_node_id();
                        if blocker_cand_indi_node_id != last_continue_tested_blocking_indi_node_id
                            && blocker_cand_indi_node_id != blocking_test_indi_id
                        {
                            // W6-DEFER[macro]: STATINC(ANYWHERECORECONCEPTBLOCKINGCANDIDATEHASHSEARCHINDINODECOUNT)
                            let up_blocker_cand_indi_node = self
                                .get_up_to_date_individual(blocker_cand_indi_node, calc_alg_context);

                            if self.is_individual_node_valid_blocker(
                                up_blocker_cand_indi_node,
                                calc_alg_context,
                            ) {
                                let mut invalid_descendant = false;
                                if calc_alg_context
                                    .process_context()
                                    .node(up_blocker_cand_indi_node)
                                    .individual_ancestor_depth()
                                    >= calc_alg_context
                                        .process_context()
                                        .node(blocking_test_indi)
                                        .individual_ancestor_depth()
                                {
                                    // make sure the candidate is not a descendant
                                    let mut anc_prev_indi_node = up_blocker_cand_indi_node;
                                    while calc_alg_context
                                        .process_context()
                                        .node(anc_prev_indi_node)
                                        .individual_ancestor_depth()
                                        >= calc_alg_context
                                            .process_context()
                                            .node(blocking_test_indi)
                                            .individual_ancestor_depth()
                                        && !invalid_descendant
                                    {
                                        if calc_alg_context
                                            .process_context()
                                            .node(anc_prev_indi_node)
                                            .individual_node_id()
                                            == calc_alg_context
                                                .process_context()
                                                .node(blocking_test_indi)
                                                .individual_node_id()
                                        {
                                            invalid_descendant = true;
                                        }
                                        anc_prev_indi_node = self.get_ancestor_individual(
                                            &mut anc_prev_indi_node,
                                            calc_alg_context,
                                        );
                                    }
                                }

                                if !invalid_descendant {
                                    if self.is_individual_node_blocking(
                                        blocking_test_indi,
                                        up_blocker_cand_indi_node,
                                        loc_block_data,
                                        false,
                                        &mut block_alt_data,
                                        calc_alg_context,
                                    ) {
                                        blocker_node = up_blocker_cand_indi_node;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        blocker_node
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getAnywhereBlockingIndividualNodeCanidateHashed`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: the `CIndividualNodeBlockingTestData` (`locBlockData`)
    /// node-switch / concept-label-modification tags and the `CNodeSwitchHistory`
    /// minimum-ancestor lookup are on unported satellites; their reads are deferred
    /// to the null/zero defaults. The two candidate-traversal branches (hash-iterator
    /// vs. descending-id scan) are reproduced; the hash-iterator branch traverses a
    /// (currently exhausted) `CBlockingIndividualNodeCandidateIterator`, while the
    /// descending-id scan over `getUpToDateIndividual(prevIndiID)` is faithful.
    pub fn get_anywhere_blocking_individual_node_canidate_hashed(
        &mut self,
        blocking_test_indi: NodeId,
        mut block_alt_data: BlockingAlternativeDataHandle,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        self.clear_blocking_cache(calc_alg_context);
        // W3-DEFER[memory-pool]: taskMemMan = calcAlgContext->getUsedProcessTaskMemoryAllocationManager();
        let mut blocker_node: NodeId = Id::NONE;
        // nodeSwitchHistory = calcAlgContext->getUsedProcessingDataBox()->getNodeSwitchHistory(false);
        let node_switch_history = calc_alg_context
            .processing_data_box_mut()
            .node_switch_history(false);
        let block_data: IndiBlockDataId = calc_alg_context
            .process_context()
            .node(blocking_test_indi)
            .individual_block_data(false);
        let mut loc_block_data: IndiBlockDataId = calc_alg_context
            .process_context()
            .node(blocking_test_indi)
            .individual_block_data(true);
        if loc_block_data == Id::NONE {
            // W6-DEFER[memory-pool]: locBlockData = alloc CIndividualNodeBlockingTestData;
            //   locBlockData->initBlockData(blockData);
            calc_alg_context
                .process_context_mut()
                .node_mut(blocking_test_indi)
                .set_individual_block_data(loc_block_data);
        }
        // W6-DEFER[api]: prevNodeSwitchTag = locBlockData->getNodeSwitchTag();
        let prev_node_switch_tag: Cint64 = 0;
        // W6-DEFER[api]: prevNodeConceptLabelModTag = locBlockData->getConceptLabelSetModificationTag();
        let prev_node_concept_label_mod_tag: Cint64 = 0;
        let mut min_test_indi_node_id: Cint64 = 0;
        let mut min_test_anc_indi_depth: Cint64 = 0;

        let mut continue_blocking_indi_node: NodeId = Id::NONE;
        if self.continue_individual_node_block(
            blocking_test_indi,
            loc_block_data,
            &mut continue_blocking_indi_node,
            &mut block_alt_data,
            calc_alg_context,
        ) {
            blocker_node = continue_blocking_indi_node;
        } else {
            let mut last_continue_tested_blocking_indi_node_id: Cint64 = -1;
            // W6-DEFER[api]: if (locBlockData->getBlockingIndividualNode())
            //   lastContinueTestedBlockingIndiNodeID =
            //     locBlockData->getBlockingIndividualNode()->getIndividualNodeID();
            if node_switch_history != Id::NONE && loc_block_data != Id::NONE && prev_node_switch_tag > 0
            {
                // W6-DEFER[api]: nodeSwitchHistory->getMinIndividualAncestorDepthAndNodeID(
                //   prevNodeSwitchTag, minTestAncIndiDepth, minTestIndiNodeID);
                min_test_indi_node_id = min_test_indi_node_id.max(0);
                min_test_anc_indi_depth = min_test_anc_indi_depth.max(0);
            }
            if calc_alg_context
                .process_context()
                .node(blocking_test_indi)
                .individual_initialization_concept()
                != Id::NONE
            {
                let mut indi_node_cand_it = self
                    .get_blocking_individual_node_candidate_iterator(blocking_test_indi, calc_alg_context);
                // W6-DEFER[api]: while (!blockerNode && indiNodeCandIt.hasNext()) — the
                //   CBlockingIndividualNodeCandidateIterator is unported, so it is
                //   exhausted; the faithful per-candidate body (getUpToDateIndividual +
                //   purged/blockable removal + valid-blocker + label-set-modified gate +
                //   isIndividualNodeBlocking) is reproduced over the empty candidate list.
                let cand_nodes: Vec<NodeId> = Vec::new();
                let _ = &mut indi_node_cand_it;
                for indi_node in cand_nodes {
                    if blocker_node != Id::NONE {
                        break;
                    }
                    let mut up_indi_node = self.get_up_to_date_individual(indi_node, calc_alg_context);
                    let up_indi_node_id = calc_alg_context
                        .process_context()
                        .node(up_indi_node)
                        .individual_node_id();
                    if up_indi_node_id != last_continue_tested_blocking_indi_node_id {
                        if calc_alg_context
                            .process_context()
                            .node(up_indi_node)
                            .has_purged_blocked_processing_restriction_flags()
                            || !calc_alg_context
                                .process_context()
                                .node(up_indi_node)
                                .is_blockable_individual()
                        {
                            // W6-DEFER[macro]: STATINC(ANYWHEREBLOCKINGCANDIDATEHASHUDATEREMOVECOUNT)
                            // W6-DEFER[api]: indiNodeCandIt.removeLastIndividualCandidate();
                        } else if self.is_individual_node_valid_blocker(up_indi_node, calc_alg_context)
                            && self.is_individual_node_concept_label_set_modified(
                                &mut up_indi_node,
                                prev_node_concept_label_mod_tag,
                                calc_alg_context,
                            )
                        {
                            // W6-DEFER[macro]: STATINC(ANYWHEREBLOCKINGCANDIDATEHASHSEARCHINDINODECOUNT)
                            if self.is_individual_node_blocking(
                                blocking_test_indi,
                                up_indi_node,
                                loc_block_data,
                                false,
                                &mut block_alt_data,
                                calc_alg_context,
                            ) {
                                blocker_node = up_indi_node;
                            }
                        }
                    }
                }
            } else {
                let mut prev_indi_id = calc_alg_context
                    .process_context()
                    .node(blocking_test_indi)
                    .individual_node_id()
                    - 1;
                let mut prev_indi_node: NodeId;
                while blocker_node == Id::NONE && prev_indi_id > 0 && prev_indi_id >= min_test_indi_node_id
                {
                    if prev_indi_id != last_continue_tested_blocking_indi_node_id {
                        prev_indi_node =
                            self.get_up_to_date_individual_by_id(prev_indi_id, calc_alg_context);
                        if prev_indi_node != Id::NONE
                            && self.is_individual_node_valid_blocker(prev_indi_node, calc_alg_context)
                            && self.is_individual_node_concept_label_set_modified(
                                &mut prev_indi_node,
                                prev_node_concept_label_mod_tag,
                                calc_alg_context,
                            )
                        {
                            // W6-DEFER[macro]: STATINC(ANYWHEREBLOCKINGCANDIDATEHASHSEARCHINDINODECOUNT)
                            if self.is_individual_node_blocking(
                                blocking_test_indi,
                                prev_indi_node,
                                loc_block_data,
                                false,
                                &mut block_alt_data,
                                calc_alg_context,
                            ) {
                                blocker_node = prev_indi_node;
                            }
                        }
                    }
                    prev_indi_id -= 1;
                }
            }
        }
        // W6-DEFER[api]: locBlockData->setBlockingIndividualNode(blockerNode);
        if blocker_node == Id::NONE {
            // W6-DEFER[api]: locBlockData->updateNodeSwitchTag(calcAlgContext->getUsedProcessTagger());
            // W6-DEFER[api]: locBlockData->updateConceptLabelSetModificationTag(calcAlgContext->getUsedProcessTagger());
        }
        blocker_node
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getBlockingIndividualNodeCandidateIterator`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: the returned `CBlockingIndividualNodeCandidateIterator`,
    /// the `CBlockingIndividualNodeCandidateHash` / `…CandidateData` lazy-hash update
    /// (max-valid-id / tag bookkeeping + descending-id rebuild) and the
    /// `CNodeSwitchHistory` min-ancestor lookup are unported satellites; the structure
    /// of the lazy-exact-hashing rebuild loop is reproduced (it reads node arena +
    /// the deferred candidate-data tags) and the method returns the opaque exhausted
    /// iterator handle.
    pub fn get_blocking_individual_node_candidate_iterator(
        &mut self,
        blocking_test_indi: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> BlockingIndividualNodeCandidateIteratorHandle {
        // W3-DEFER[memory-pool]: taskMemMan = nullptr;
        let testing_indi_id = calc_alg_context
            .process_context()
            .node(blocking_test_indi)
            .individual_node_id();
        let initialization_concept_des: ConDescId = calc_alg_context
            .process_context()
            .node(blocking_test_indi)
            .individual_initialization_concept();
        // procDataBox->getNodeSwitchHistory(false)
        let node_switch_history = calc_alg_context
            .processing_data_box_mut()
            .node_switch_history(false);
        // test whether hash has to be updated
        let mut needs_hash_update = true;
        // blockingCandHash = procDataBox->getBlockingIndividualNodeCandidateHash(true);
        let _blocking_cand_hash = calc_alg_context
            .processing_data_box_mut()
            .blocking_individual_node_candidate_hash(true);
        // W6-DEFER[api]: blockingCandData =
        //   blockingCandHash->getBlockingIndividualCandidateData(initializationConceptDes, true);

        if self.conf_anywhere_blocking_lazy_exact_hashing {
            // W6-DEFER[api]: maxValidIndiID = blockingCandData->getMaxValidIndividualID()+1;
            let mut max_valid_indi_id: Cint64 = 1;
            // W6-DEFER[api]: conLabelSetModTag = blockingCandData->getConceptLabelSetModificationTag();
            let con_label_set_mod_tag: Cint64 = 0;
            // W6-DEFER[api]: nodeSwitchTag = blockingCandData->getNodeSwitchTag();
            let node_switch_tag: Cint64 = 0;
            let mut min_test_indi_node_id: Cint64 = 1;
            let mut min_test_anc_indi_depth: Cint64 = 0;
            if node_switch_history != Id::NONE && node_switch_tag > 0 {
                // W6-DEFER[api]: nodeSwitchHistory->getMinIndividualAncestorDepthAndNodeID(
                //   nodeSwitchTag, minTestAncIndiDepth, minTestIndiNodeID);
                min_test_indi_node_id = min_test_indi_node_id.max(1);
                min_test_anc_indi_depth = min_test_anc_indi_depth.max(0);
            }
            if max_valid_indi_id >= testing_indi_id && min_test_indi_node_id >= testing_indi_id {
                needs_hash_update = false;
            }
            if needs_hash_update {
                // W6-DEFER[macro]: STATINC(ANYWHEREBLOCKINGCANDIDATEHASHUDATECOUNT)
                if max_valid_indi_id != testing_indi_id {
                    // insert testing node
                    // W6-DEFER[macro]: STATINC(ANYWHEREBLOCKINGCANDIDATEHASHUDATEADDCOUNT)
                    // W6-DEFER[api]: blockingCandData->insertBlockingCandidateIndividualNode(blockingTestIndi);
                }
                let mut dest_indi_id = max_valid_indi_id.min(min_test_indi_node_id);
                dest_indi_id = dest_indi_id.max(0);
                let mut indi_id = testing_indi_id - 1;
                while indi_id >= dest_indi_id {
                    let mut indi = self.get_up_to_date_individual_by_id(indi_id, calc_alg_context);
                    if indi != Id::NONE
                        && calc_alg_context
                            .process_context()
                            .node(indi)
                            .is_blockable_individual()
                        && !calc_alg_context
                            .process_context()
                            .node(indi)
                            .has_purged_blocked_processing_restriction_flags()
                    {
                        if indi_id >= max_valid_indi_id
                            || self.is_individual_node_concept_label_set_modified(
                                &mut indi,
                                con_label_set_mod_tag,
                                calc_alg_context,
                            )
                        {
                            // W6-DEFER[api]: if (indi->getReapplyConceptLabelSet(false)
                            //     ->containsConceptDescriptor(initializationConceptDes)) {
                            //   STATINC(ANYWHEREBLOCKINGCANDIDATEHASHUDATEADDCOUNT)
                            //   blockingCandData->insertBlockingCandidateIndividualNode(indi);
                            // }
                            let _label_set: LabelSetId = calc_alg_context
                                .process_context_mut()
                                .node_mut(indi)
                                .get_reapply_concept_label_set(false);
                            let _ = initialization_concept_des;
                        }
                    }
                    indi_id -= 1;
                }
                // W3-DEFER[api]: processTagger = calcAlgContext->getUsedProcessTagger();
                // W6-DEFER[api]: blockingCandData->updateConceptLabelSetModificationTag(processTagger);
                // W6-DEFER[api]: blockingCandData->updateNodeSwitchTag(processTagger);
                // W6-DEFER[api]: blockingCandData->setMaxValidIndividualID(qMax(maxValidIndiID, testingIndiID));
                max_valid_indi_id = max_valid_indi_id.max(testing_indi_id);
            }
        }

        // W6-DEFER[api]: return blockingCandData->getBlockingCandidatesIndividualNodeIterator(blockingTestIndi);
        INVALID
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::propagateIndirectSuccessorBlocking`.
    pub fn propagate_indirect_successor_blocking(
        &mut self,
        indi: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        self.propagate_adding_blocked_processing_restriction_to_successors(
            indi,
            IndividualProcessNode::PRF_INDIRECTBLOCKED,
            true,
            IndividualProcessNode::PRF_INDIRECTBLOCKED,
            calc_alg_context,
        );
        self.propagate_clearing_processing_restriction_to_successors(
            indi,
            IndividualProcessNode::PRF_BLOCKINGRETESTDUEINDIRECTBLOCKERLOSS,
            true,
            IndividualProcessNode::PRF_INDIRECTBLOCKED,
            calc_alg_context,
        );
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::propagateAddingBlockedProcessingRestrictionToSuccessors`.
    pub fn propagate_adding_blocked_processing_restriction_to_successors(
        &mut self,
        mut indi: NodeId,
        add_restriction_flags: Cint64,
        recursive: bool,
        while_not_contains_flags: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W6-DEFER[api]: succIt = indi->getSuccessorIterator(); — getSuccessorIterator
        //   returns the zero-size SuccessorIterator stub; the edge list is empty until
        //   the role-successor-link iteration API lands.
        let succ_it: Vec<EdgeId> = Vec::new();
        let anc_depth = calc_alg_context
            .process_context()
            .node(indi)
            .individual_ancestor_depth();
        for succ_link in succ_it {
            let succ_indi = self.get_successor_individual(&mut indi, succ_link, calc_alg_context);
            let succ_anc_depth = calc_alg_context
                .process_context()
                .node(succ_indi)
                .individual_ancestor_depth();
            if succ_anc_depth > anc_depth {
                if !calc_alg_context
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
                        self.propagate_adding_blocked_processing_restriction_to_successors(
                            loc_succ_indi,
                            add_restriction_flags,
                            recursive,
                            while_not_contains_flags,
                            calc_alg_context,
                        );
                    }
                    self.eliminiate_blocked_individuals(loc_succ_indi, calc_alg_context);
                }
            }
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::reactivateIndirectBlockedSuccessors`.
    pub fn reactivate_indirect_blocked_successors(
        &mut self,
        mut indi: NodeId,
        recursive: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let _ = recursive;
        // W6-DEFER[api]: succIt = indi->getSuccessorIterator(); (see above)
        let succ_it: Vec<EdgeId> = Vec::new();
        let anc_depth = calc_alg_context
            .process_context()
            .node(indi)
            .individual_ancestor_depth();
        for succ_link in succ_it {
            let succ_indi = self.get_successor_individual(&mut indi, succ_link, calc_alg_context);
            let succ_anc_depth = calc_alg_context
                .process_context()
                .node(succ_indi)
                .individual_ancestor_depth();
            if succ_anc_depth > anc_depth {
                if calc_alg_context
                    .process_context()
                    .node(succ_indi)
                    .has_partial_processing_restriction_flags(
                        IndividualProcessNode::PRF_INDIRECTBLOCKED,
                    )
                {
                    if !calc_alg_context
                        .process_context()
                        .node(succ_indi)
                        .has_partial_processing_restriction_flags(
                            IndividualProcessNode::PRF_BLOCKINGRETESTDUEINDIRECTBLOCKERLOSS,
                        )
                    {
                        let loc_blocked_indi_node =
                            self.get_localized_individual(succ_indi, true, calc_alg_context);
                        calc_alg_context
                            .process_context_mut()
                            .node_mut(loc_blocked_indi_node)
                            .add_processing_restriction_flags(
                                IndividualProcessNode::PRF_BLOCKINGRETESTDUEINDIRECTBLOCKERLOSS,
                            );
                        self.add_individual_to_processing_queue(
                            loc_blocked_indi_node,
                            calc_alg_context,
                        );
                    }
                }
            }
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::reactivateBlockedIndividuals`.
    pub fn reactivate_blocked_individuals(
        &mut self,
        indi: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // KONCLUDE-PORT-NOTE[ownership]: `CXLinker<CIndividualProcessNode*>*` blocked
        //   linker → `&[NodeId]`; cloned to a `Vec` so the node arena can be mutated
        //   inside the loop without aliasing the borrow.
        let blocked_indi_nodes: Vec<NodeId> = calc_alg_context
            .process_context()
            .node(indi)
            .get_blocked_individuals_linker()
            .to_vec();
        for blocked_indi_node in blocked_indi_nodes {
            if !calc_alg_context
                .process_context()
                .node(blocked_indi_node)
                .has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_BLOCKINGRETESTDUEBLOCKERMODIFIED,
                )
            {
                let loc_blocked_indi_node =
                    self.get_localized_individual(blocked_indi_node, true, calc_alg_context);
                calc_alg_context
                    .process_context_mut()
                    .node_mut(loc_blocked_indi_node)
                    .add_processing_restriction_flags(
                        IndividualProcessNode::PRF_BLOCKINGRETESTDUEBLOCKERMODIFIED,
                    );
                self.add_individual_to_processing_queue(loc_blocked_indi_node, calc_alg_context);
            }
        }
        calc_alg_context
            .process_context_mut()
            .node_mut(indi)
            .clear_blocked_individuals_linker();
        true
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::isIndividualNodeProcessingBlocked`.
    pub fn is_individual_node_processing_blocked(
        &mut self,
        blocking_test_indi: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W6-DEFER[macro]: STATINC(INDINODEPROCESSINGBLOCKINGTESTCOUNT)
        if calc_alg_context
            .process_context()
            .node(blocking_test_indi)
            .has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_SYNCHRONIZEDBACKENPROCESSINGDELAYING,
            )
        {
            return true;
        }
        if calc_alg_context
            .process_context()
            .node(blocking_test_indi)
            .has_purged_blocked_processing_restriction_flags()
        {
            return true;
        }
        if self.is_saturation_cached_processing_blocked(blocking_test_indi, calc_alg_context) {
            return true;
        }
        if self.is_individual_node_completion_graph_cached(blocking_test_indi, calc_alg_context) {
            return true;
        }
        if self.is_satisfiable_cached_processing_blocked(blocking_test_indi, calc_alg_context) {
            return true;
        }
        if self.is_signature_blocked_processing_blocked(blocking_test_indi, calc_alg_context) {
            return true;
        }
        if calc_alg_context
            .process_context()
            .node(blocking_test_indi)
            .has_partial_processing_restriction_flags(IndividualProcessNode::PRF_PROCESSINGBLOCKED)
        {
            if self.opt_det_exp_preporcessing {
                return true;
            } else {
                return self.detect_individual_node_blocked_status(blocking_test_indi, calc_alg_context);
            }
        }
        if calc_alg_context
            .process_context()
            .node(blocking_test_indi)
            .has_partial_processing_restriction_flags(IndividualProcessNode::PRF_INDIRECTBLOCKED)
        {
            if calc_alg_context
                .process_context()
                .node(blocking_test_indi)
                .has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_BLOCKINGRETESTDUEINDIRECTBLOCKERLOSS,
                )
            {
                return self.detect_individual_node_blocked_status(blocking_test_indi, calc_alg_context);
            } else {
                return true;
            }
        }
        if calc_alg_context
            .process_context()
            .node(blocking_test_indi)
            .has_partial_processing_restriction_flags(IndividualProcessNode::PRF_DIRECTBLOCKED)
        {
            if calc_alg_context
                .process_context()
                .node(blocking_test_indi)
                .has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_BLOCKINGRETESTDUEDIRECTMODIFIED
                        | IndividualProcessNode::PRF_BLOCKINGRETESTDUEBLOCKERMODIFIED,
                )
            {
                return self.detect_individual_node_blocked_status(blocking_test_indi, calc_alg_context);
            } else {
                return true;
            }
        }
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::isIndividualNodeExpansionBlocked`.
    pub fn is_individual_node_expansion_blocked(
        &mut self,
        blocking_test_indi: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W6-DEFER[macro]: STATINC(INDINODEEXPANSIONBLOCKINGTESTCOUNT)
        self.detect_individual_node_blocked_status(blocking_test_indi, calc_alg_context)
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::needsIndividualNodeExpansionBlockingTest`.
    pub fn needs_individual_node_expansion_blocking_test(
        &mut self,
        con_pro_des: ConProcDescId,
        blocking_test_indi: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let _ = blocking_test_indi;
        let con_des: ConDescId = calc_alg_context
            .process_context()
            .con_proc_desc(con_pro_des)
            .get_concept_descriptor();
        let concept: ConceptId = calc_alg_context
            .process_context()
            .con_desc(con_des)
            .get_concept();
        let con_priority: f64 = calc_alg_context
            .process_context()
            .con_proc_desc(con_pro_des)
            .get_process_priority()
            .get_priority();
        let _ = con_priority;
        let con_neg: bool = calc_alg_context
            .process_context()
            .con_desc(con_des)
            .is_negated();
        let op_code: Cint64 = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operator_code();
        let op_count: Cint64 = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operand_count();
        let parameter: Cint64 = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_parameter();
        let mut needs_blocking_test = false;
        if !con_neg {
            if op_code == CCSOME || op_code == CCATLEAST || op_code == CCAQSOME {
                needs_blocking_test = true;
            } else if op_code == CCOR {
                if self.opt_non_strict_indi_node_processing {
                    if op_count >= 1 {
                        needs_blocking_test = true;
                    }
                }
            } else if op_code == CCATMOST {
                if self.opt_non_strict_indi_node_processing {
                    if parameter > 1 {
                        needs_blocking_test = true;
                    }
                }
            }
        } else {
            if op_code == CCALL || op_code == CCATMOST {
                needs_blocking_test = true;
            } else if op_code == CCAND || op_code == CCEQ {
                if self.opt_non_strict_indi_node_processing {
                    if op_count >= 1 {
                        needs_blocking_test = true;
                    }
                }
            } else if op_code == CCATLEAST {
                if self.opt_non_strict_indi_node_processing {
                    if parameter > 2 {
                        needs_blocking_test = true;
                    }
                }
            }
        }
        needs_blocking_test
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::propagateIndirectSuccessorSaturationBlocked`.
    pub fn propagate_indirect_successor_saturation_blocked(
        &mut self,
        indi: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        self.propagate_adding_blocked_processing_restriction_to_successors(
            indi,
            IndividualProcessNode::PRF_ANCESTORSATURATIONBLOCKINGCACHED,
            true,
            IndividualProcessNode::PRF_ANCESTORSATURATIONBLOCKINGCACHED,
            calc_alg_context,
        );
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::tryEstablishExpansionBlockingWithBackendCacheSynchronisation`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: `CBackendRepresentativeMemoryCacheIndividualAssociationData`
    /// (`assocData`) and the backend-sync-data accessors are unported; their reads are
    /// deferred to null/false. The `if (assocData)` body is reproduced (so the
    /// node-flag additions and the `testIndividualNodeBackendCacheConceptsSynchronization`
    /// sibling call are preserved); it currently short-circuits because `assocData`
    /// is null, exactly as the faithful translation requires until the backend cache lands.
    pub fn try_establish_expansion_blocking_with_backend_cache_synchronisation(
        &mut self,
        indi_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut expansion_blocked = false;
        let backend_sync_data: BackendSyncDataId = calc_alg_context
            .process_context()
            .node(indi_node)
            .individual_backend_cache_synchronisation_data(false);
        if backend_sync_data != Id::NONE {
            // W6-DEFER[api]: assocData = backendSyncData->getAssocitaionData();
            let assoc_data: Cint64 = INVALID;
            if assoc_data != INVALID {
                // W6-DEFER[api]: backendExpBlocking = assocData->isCompletelyHandled()
                //   && !assocData->hasRepresentativeSameIndividualMerging();
                let mut backend_exp_blocking = false;
                // W6-DEFER[api]: if (backendExpBlocking && assocData->getDeterministicMergedSameConsideredLabelCacheEntry()
                //     != assocData->getLabelCacheEntry(DETERMINISTIC_SAME_INDIVIDUAL_SET_LABEL))
                //   backendExpBlocking = false;
                if backend_exp_blocking
                    && self.test_individual_node_backend_cache_concepts_synchronization(
                        indi_node,
                        calc_alg_context,
                    )
                {
                    if !calc_alg_context
                        .process_context()
                        .node(indi_node)
                        .has_processing_restriction_flags(
                            IndividualProcessNode::PRF_INVALIDBLOCKINGORCACHING,
                        )
                        && self.conf_allow_backend_successor_expansion_blocking
                    {
                        calc_alg_context
                            .process_context_mut()
                            .node_mut(indi_node)
                            .add_processing_restriction_flags(
                                IndividualProcessNode::PRF_SYNCHRONIZEDBACKEND
                                    | IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDSUCCESSOREXPANSIONBLOCKED
                                    | IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDINDIRECTNOMINALEXPANSIONBLOCKED,
                            );
                    }
                    expansion_blocked = true;
                }
                if self.conf_allow_backend_neighbour_expansion_blocking {
                    calc_alg_context
                        .process_context_mut()
                        .node_mut(indi_node)
                        .add_processing_restriction_flags(
                            IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDNEIGHBOUREXPANSIONBLOCKED
                                | IndividualProcessNode::PRF_RETESTBACKENDSYNCHRONIZATIONDUEDIRECTMODIFIED,
                        );
                }
            }
        }

        expansion_blocked
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::testIndividualNodeBackendCacheExpansionBlockingCriticalCardinality`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: the backend-representative-memory synchronisation data,
    /// its association data + full-concept-set / cardinality label-cache entries, and the
    /// `CReapplyRoleSuccessorHash` are unported satellites. The outer control flow is
    /// reproduced — the `!isCriticalCardinalityExpansionBlocking() && assocData` gate, the
    /// newly-merged-deterministic visit (sets `expansionBlockingCritical`), the
    /// per-role cardinality-data loop, and the final localized-cache write — with every
    /// satellite read deferred to its null/false default (so the `else` arm
    /// `expansionBlockingCritical = true` of the missing-association case is preserved).
    /// The role-cardinality hash iteration is over a currently-empty cache and is marked.
    pub fn test_individual_node_backend_cache_expansion_blocking_critical_cardinality(
        &mut self,
        indi_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut expansion_blocking_critical = false;
        let backend_sync_data: BackendSyncDataId = calc_alg_context
            .process_context()
            .node(indi_node)
            .individual_backend_cache_synchronisation_data(false);
        let mut loc_backend_sync_data: BackendSyncDataId = calc_alg_context
            .process_context()
            .node(indi_node)
            .individual_backend_cache_synchronisation_data(true);

        if backend_sync_data != Id::NONE {
            // W6-DEFER[api]: assocData = backendSyncData->getAssocitaionData();
            let assoc_data: Cint64 = INVALID;
            // W6-DEFER[api]: !backendSyncData->isCriticalCardinalityExpansionBlocking() && assocData
            let is_critical_cardinality_expansion_blocking = false;
            if !is_critical_cardinality_expansion_blocking && assoc_data != INVALID {
                self.test_individual_node_backend_cache_new_mergings(indi_node, calc_alg_context);
                // backendSyncData = indiNode->getIndividualBackendCacheSynchronisationData(false);
                let _backend_sync_data: BackendSyncDataId = calc_alg_context
                    .process_context()
                    .node(indi_node)
                    .individual_backend_cache_synchronisation_data(false);

                // W6-DEFER[api]: if (backendSyncData->getMergedIndividualNodeLinker()
                //     != backendSyncData->getLastCriticalNeighboursTestedMergedNodeLinker()) {
                //   visitNewlyMergedOnlyDeterministicRepresentativeIndividualsBackendSynchronisationData(
                //     indiNode, ..., [&](...) { expansionBlockingCritical = true; return false; }, ...);
                //   locBackendSyncData = getLocalizedIndividualBackendCacheSnychronisationData(indiNode, ...);
                //   locBackendSyncData->setLastCriticalNeighboursTestedMergedNodeLinker(...);
                // }

                // W6-DEFER[api]: fullConSetLabelCacheItem =
                //   assocData->getLabelCacheEntry(FULL_CONCEPT_SET_LABEL);
                let full_con_set_label_cache_item: Cint64 = INVALID;
                if full_con_set_label_cache_item != INVALID && !expansion_blocking_critical {
                    // W6-DEFER[api]: cardExtensionData =
                    //   fullConSetLabelCacheItem->getExtensionData(CARDINALITY_HASH);
                    let card_extension_data: Cint64 = INVALID;
                    // roleSuccHash = indiNode->getReapplyRoleSuccessorHash(false);
                    let role_succ_hash = calc_alg_context
                        .process_context_mut()
                        .node_mut(indi_node)
                        .get_reapply_role_successor_hash(false);
                    if role_succ_hash != Id::NONE && card_extension_data != INVALID {
                        let _last_added_link_edge: EdgeId = calc_alg_context
                            .process_context()
                            .node(indi_node)
                            .get_last_added_role_link();
                        // W6-DEFER[api]: lastTestedLinkEdge = backendSyncData->getLastCriticalCardinalityLinkEdge();
                        // W6-DEFER[api]: assocData = backendSyncData->getAssocitaionData();

                        // W6-DEFER[api]: if (lastTestedLinkEdge != lastAddedLinkEdge
                        //     || !assocData->isCompletelyHandled() && !backendSyncData->hasCriticalCardinalityInitiallyChecked()) {
                        //   roleVector = calcAlgContext->getProcessingDataBox()->getOntology()->getRBox()->getRoleVector();
                        //   for each (roleId -> cardData) in cardExtensionData->getRoleCardinalityDataHash() while !critical:
                        //     role = roleVector->getData(roleId);
                        //     linkCount = roleSuccHash->getRoleSuccessorCount(role);
                        //     if (indiNode->hasPartialProcessingRestrictionFlags(PRFSYNCHRONIZEDBACKENDSUCCESSOREXPANSIONBLOCKED))
                        //       linkCount += cardData->getExistentialMaxUsedCardinality();
                        //     if (!backendSyncData->hasAllNeighbourForcedExpansion())
                        //       linkCount += getBackendCacheRoleRepresentativeNeighbourCount(indiNode, backendSyncData, assocData, role, ...);
                        //     minCard = cardData->getMinimumRestrictingCardinality();
                        //     if (linkCount > minCard) expansionBlockingCritical = true;
                        //   locBackendSyncData = getLocalizedIndividualBackendCacheSnychronisationData(indiNode, ...);
                        //   locBackendSyncData->setLastCriticalCardinalityLinkEdge(lastAddedLinkEdge);
                        //   locBackendSyncData->setCriticalCardinalityInitiallyChecked(true);
                        // }
                        // The per-role cardinality loop is over the unported role-cardinality
                        // hash; reproduced as the (currently empty) faithful skeleton below.
                        let role_card_data: Vec<(RoleId, Cint64)> = Vec::new();
                        for (role, _card_data) in role_card_data {
                            if expansion_blocking_critical {
                                break;
                            }
                            let mut link_count: Cint64 = calc_alg_context
                                .process_context()
                                .node(indi_node)
                                .get_role_successor_count(role);
                            if calc_alg_context
                                .process_context()
                                .node(indi_node)
                                .has_partial_processing_restriction_flags(
                                    IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDSUCCESSOREXPANSIONBLOCKED,
                                )
                            {
                                // W6-DEFER[api]: linkCount += cardData->getExistentialMaxUsedCardinality();
                            }
                            // W6-DEFER[api]: if (!backendSyncData->hasAllNeighbourForcedExpansion())
                            //   linkCount += getBackendCacheRoleRepresentativeNeighbourCount(...);
                            // W6-DEFER[api]: minCard = cardData->getMinimumRestrictingCardinality();
                            let min_card: Cint64 = 0;
                            if link_count > min_card {
                                expansion_blocking_critical = true;
                            }
                            let _ = &mut link_count;
                        }
                    }
                }

                if expansion_blocking_critical {
                    loc_backend_sync_data = self
                        .get_localized_individual_backend_cache_snychronisation_data(
                            indi_node,
                            calc_alg_context,
                        );
                    // W6-DEFER[api]: locBackendSyncData->setCriticalCardinalityExpansionBlocking(expansionBlockingCritical);
                }
            } else {
                expansion_blocking_critical = true;
            }
        }

        let _ = loc_backend_sync_data;
        expansion_blocking_critical
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::testIndividualNodeBackendCacheNeighbourExpansionBlockingCritical`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: same backend-cache satellite family as the cardinality
    /// variant above (all reads deferred to null/false). The outer flow is reproduced —
    /// the `assocData && !isCriticalNeighbourExpansionBlocking()` gate, the newly-merged
    /// visit, the merged-linker short-circuit, and the adding-sorted-concept-descriptor
    /// scan that calls `testIndividualNodeConceptBackendCacheNeighbourExpansionBlockingCritical`
    /// per concept. The commented-out festo.com debug block in the source is omitted
    /// (dead debug code). The concept-descriptor scan iterates the unported
    /// `CReapplyConceptLabelSet` adding-sorted chain (currently empty); the `hasNondeterministicDependency`
    /// and per-concept sibling calls are preserved on the skeleton.
    pub fn test_individual_node_backend_cache_neighbour_expansion_blocking_critical(
        &mut self,
        indi_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut expansion_blocking_critical = false;

        let backend_sync_data: BackendSyncDataId = calc_alg_context
            .process_context()
            .node(indi_node)
            .individual_backend_cache_synchronisation_data(false);
        let mut loc_backend_sync_data: BackendSyncDataId = calc_alg_context
            .process_context()
            .node(indi_node)
            .individual_backend_cache_synchronisation_data(true);

        if backend_sync_data != Id::NONE {
            // W6-DEFER[api]: assocData = backendSyncData->getAssocitaionData();
            let assoc_data: Cint64 = INVALID;
            // W6-DEFER[api]: assocData && !backendSyncData->isCriticalNeighbourExpansionBlocking()
            let is_critical_neighbour_expansion_blocking = false;
            if assoc_data != INVALID && !is_critical_neighbour_expansion_blocking {
                self.test_individual_node_backend_cache_new_mergings(indi_node, calc_alg_context);
                let _backend_sync_data: BackendSyncDataId = calc_alg_context
                    .process_context()
                    .node(indi_node)
                    .individual_backend_cache_synchronisation_data(false);

                // W6-DEFER[api]: if (backendSyncData->getMergedIndividualNodeLinker()
                //     != backendSyncData->getLastCriticalNeighboursTestedMergedNodeLinker()) {
                //   visitNewlyMergedOnlyDeterministicRepresentativeIndividualsBackendSynchronisationData(
                //     indiNode, ..., [&](...) { expansionBlockingCritical = true; return false; }, ...);
                //   locBackendSyncData = getLocalizedIndividualBackendCacheSnychronisationData(indiNode, ...);
                //   locBackendSyncData->setLastCriticalNeighboursTestedMergedNodeLinker(...);
                // }

                // W6-DEFER[api]: if (backendSyncData->getMergedIndividualNodeLinker())
                let has_merged_individual_node_linker = false;
                if has_merged_individual_node_linker {
                    expansion_blocking_critical = true;
                } else {
                    if !self.test_individual_node_backend_cache_concepts_synchronization(
                        indi_node,
                        calc_alg_context,
                    ) {
                        // W6-DEFER[api]: lastTestedConDes = backendSyncData->getLastCriticalNeighbourExpansionTestedConceptDescriptor();
                        let last_tested_con_des: ConDescId = Id::NONE;
                        // W6-DEFER[api]: lastSynchedConDes = backendSyncData->getLastSynchedConceptDescriptor();
                        let mut last_synched_con_des: ConDescId = Id::NONE;
                        // W6-DEFER[api]: if (!assocData->isCompletelyPropagated()) lastSynchedConDes = nullptr;
                        last_synched_con_des = Id::NONE;
                        // conSet = indiNode->getReapplyConceptLabelSet(false);
                        let con_set: LabelSetId = calc_alg_context
                            .process_context_mut()
                            .node_mut(indi_node)
                            .get_reapply_concept_label_set(false);
                        if con_set != Id::NONE {
                            // W6-DEFER[api]: conDesLinker = conSet->getAddingSortedConceptDescriptionLinker();
                            let con_des_linker: ConDescId = Id::NONE;
                            let mut new_last_tested_con_des: ConDescId = con_des_linker;
                            if con_des_linker != last_tested_con_des {
                                // W6-DEFER[api]: the adding-sorted concept-descriptor chain is
                                //   on the unported CReapplyConceptLabelSet; the per-concept loop
                                //   is reproduced over the (currently empty) descriptor list.
                                let con_des_chain: Vec<ConDescId> = Vec::new();
                                let mut concept_expansion_blocking_critical = false;
                                for con_des_it in con_des_chain {
                                    if con_des_it == last_tested_con_des
                                        || con_des_it == last_synched_con_des
                                    {
                                        break;
                                    }
                                    let concept: ConceptId = calc_alg_context
                                        .process_context()
                                        .con_desc(con_des_it)
                                        .get_concept();
                                    let con_negation: bool = calc_alg_context
                                        .process_context()
                                        .con_desc(con_des_it)
                                        .is_negated();

                                    let dep_track_point = calc_alg_context
                                        .process_context()
                                        .con_desc(con_des_it)
                                        .get_dependency_track_point();
                                    let nondeterministic = self
                                        .has_nondeterministic_dependency(dep_track_point, calc_alg_context);

                                    if assoc_data != INVALID
                                        && self
                                            .test_individual_node_concept_backend_cache_neighbour_expansion_blocking_critical(
                                                concept,
                                                con_negation,
                                                nondeterministic,
                                                assoc_data,
                                                calc_alg_context,
                                            )
                                    {
                                        concept_expansion_blocking_critical = true;
                                        new_last_tested_con_des = con_des_it;
                                    }
                                    // conDesIt = conDesIt->getNext();
                                }
                                loc_backend_sync_data = self
                                    .get_localized_individual_backend_cache_snychronisation_data(
                                        indi_node,
                                        calc_alg_context,
                                    );
                                if concept_expansion_blocking_critical
                                    && new_last_tested_con_des != Id::NONE
                                {
                                    // W6-DEFER[api]: newLastTestedConDes = newLastTestedConDes->getNext();
                                }
                                // W6-DEFER[api]: locBackendSyncData->setLastCriticalNeighbourExpansionTestedConceptDescriptor(newLastTestedConDes);
                                if concept_expansion_blocking_critical {
                                    expansion_blocking_critical = true;
                                }
                            }
                        }
                    }
                }

                if expansion_blocking_critical {
                    loc_backend_sync_data = self
                        .get_localized_individual_backend_cache_snychronisation_data(
                            indi_node,
                            calc_alg_context,
                        );
                    // W6-DEFER[api]: locBackendSyncData->setCriticalNeighbourExpansionBlocking(expansionBlockingCritical);
                }
            } else {
                expansion_blocking_critical = true;
            }
        }

        let _ = loc_backend_sync_data;
        expansion_blocking_critical
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::testIndividualNodeConceptBackendCacheNeighbourExpansionBlockingCritical`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: the concept-operator dispatch and the recursive AQ-AND
    /// descent are reproduced in FULL over the concept arena. The terminal label-cache
    /// queries (`mBackendCacheHandler->hasConceptInAssociatedFullConceptSetLabel` /
    /// `hasRoleInAssociatedCompinationRoleSetLabel`) and `assocData->isCompletelyPropagated()`
    /// are on the unported backend-cache handler / association data; they are deferred —
    /// with `mBackendCacheHandler` null the `!mBackendCacheHandler || ...` disjunction is
    /// true, so a matching `∀/⩽` / `∃/⩾/value` concept is flagged critical, exactly as the
    /// faithful translation requires.
    pub fn test_individual_node_concept_backend_cache_neighbour_expansion_blocking_critical(
        &mut self,
        concept: ConceptId,
        con_negation: bool,
        nondeterministic: bool,
        assoc_data: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut expansion_blocking_critical = false;
        let con_operator = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_concept_operator();
        let op_code: Cint64 = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operator_code();
        let op_concepts: Vec<NegLink<ConceptId>> = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operand_list()
            .to_vec();
        if self.conf_specialized_automate_rules
            && (op_code == CCAQAND || op_code == CCIMPLAQAND || op_code == CCBRANCHAQAND)
        {
            for op in op_concepts {
                if expansion_blocking_critical {
                    break;
                }
                let op_con: ConceptId = op.target;
                let op_con_neg: bool = op.negated;
                expansion_blocking_critical |= self
                    .test_individual_node_concept_backend_cache_neighbour_expansion_blocking_critical(
                        op_con,
                        op_con_neg,
                        nondeterministic,
                        assoc_data,
                        calc_alg_context,
                    );
            }
        } else if !con_negation
            && con_operator
                .has_partial_operator_code_flag(CCFS_ALL_AQALL_TYPE | CCF_ATMOST)
            || con_negation
                && con_operator
                    .has_partial_operator_code_flag(CCFS_SOME_TYPE | CCF_ATLEAST | CCF_VALUE)
        {
            let role: RoleId = calc_alg_context.ontology_arenas().concept(concept).get_role();
            // W6-DEFER[api]: if (assocData->isCompletelyPropagated())
            let is_completely_propagated = false;
            if is_completely_propagated {
                // W6-DEFER[api]: if (!mBackendCacheHandler
                //     || !mBackendCacheHandler->hasConceptInAssociatedFullConceptSetLabel(
                //          assocData, assocData->getLabelCacheEntry(FULL_CONCEPT_SET_LABEL),
                //          concept, conNegation, !nondeterministic, calcAlgContext))
                //   expansionBlockingCritical = true;
                if self.backend_cache_handler == Id::NONE {
                    expansion_blocking_critical = true;
                } else {
                    expansion_blocking_critical = true;
                }
            } else {
                // W6-DEFER[api]: if (!mBackendCacheHandler
                //     || mBackendCacheHandler->hasRoleInAssociatedCompinationRoleSetLabel(
                //          assocData, getLabelCacheEntry(DETERMINISTIC_COMBINED_NEIGHBOUR_INSTANTIATED_ROLE_SET_LABEL), role, false)
                //     || mBackendCacheHandler->hasRoleInAssociatedCompinationRoleSetLabel(
                //          assocData, getLabelCacheEntry(NONDETERMINISTIC_COMBINED_NEIGHBOUR_INSTANTIATED_ROLE_SET_LABEL), role, false))
                //   expansionBlockingCritical = true;
                let _ = role;
                if self.backend_cache_handler == Id::NONE {
                    expansion_blocking_critical = true;
                } else {
                    expansion_blocking_critical = true;
                }
            }
        }
        expansion_blocking_critical
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addBlockingCoreConcept`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: `CConceptProcessData::isCoreBlockingConcept`, the
    /// `CCoreConceptDescriptor` allocation + `CReapplyConceptLabelSet::addCoreConceptDescriptor`,
    /// and the `CBlockingIndividualNodeLinkedCandidateHash` candidate insertion are on
    /// unported types. The `mConfSaveCoreBlockingConceptsCandidates` gate, the concept-data
    /// fetch, the nominal-node guard, and the databox candidate-hash getter are reproduced;
    /// the core-blocking-concept test is deferred (false) so the body short-circuits until
    /// the concept-process-data + candidate-hash satellites land.
    pub fn add_blocking_core_concept(
        &mut self,
        concept_descriptor: ConDescId,
        process_indi: NodeId,
        con_label_set: LabelSetId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        if self.conf_save_core_blocking_concepts_candidates {
            let concept: ConceptId = calc_alg_context
                .process_context()
                .con_desc(concept_descriptor)
                .get_concept();
            let con_data: Cint64 = calc_alg_context
                .ontology_arenas()
                .concept(concept)
                .get_concept_data();
            if con_data != INVALID && con_data != 0 {
                let is_negated: bool = calc_alg_context
                    .process_context()
                    .con_desc(concept_descriptor)
                    .is_negated();
                // W6-DEFER[api]: conProData = (CConceptProcessData*)conData;
                //   if (conProData->isCoreBlockingConcept(conceptDescriptor->isNegated()))
                let is_core_blocking_concept = false;
                let _ = is_negated;
                if is_core_blocking_concept {
                    if !calc_alg_context
                        .process_context()
                        .node(process_indi)
                        .is_nominal_individual_node()
                    {
                        // W6-DEFER[macro]: STATINC(CORECONCEPTSADDEDINDINODELABELSETCOUNT)
                        // W3-DEFER[memory-pool]: taskMemMan = calcAlgContext->getUsedProcessTaskMemoryAllocationManager();
                        // W6-DEFER[api]: coreConceptDescriptor = alloc CCoreConceptDescriptor;
                        //   coreConceptDescriptor->initCoreConceptDescriptor(conceptDescriptor);
                        //   conLabelSet->addCoreConceptDescriptor(coreConceptDescriptor);
                        let _ = con_label_set;

                        // procDataBox->getBlockingIndividualNodeLinkedCandidateHash(true)
                        let _blocking_cand_hash = calc_alg_context
                            .processing_data_box_mut()
                            .blocking_individual_node_linked_candidate_hash(true);
                        // W6-DEFER[api]: blockingCandData =
                        //   blockingCandHash->getBlockingIndividualCandidateData(conceptDescriptor, true);
                        //   blockingCandData->addBlockingCandidateIndividualNode(processIndi);
                    }

                    return true;
                }
            }
        }
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addIndividualToBlockingUpdateReviewProcessingQueue`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: `CIndividualDepthProcessingQueue::insertProcessIndiviudal`
    /// is not yet ported; the databox getter is reproduced and the enqueue is deferred.
    pub fn add_individual_to_blocking_update_review_processing_queue(
        &mut self,
        individual: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let _sig_block_upd_pro_queue = calc_alg_context
            .get_blocking_update_review_processing_queue(true);
        // W6-DEFER[api]: sigBlockUpdProQueue->insertProcessIndiviudal(individual);
        let _ = individual;
        // W6-DEFER[macro]: STATINC(INDINODESADDEDPROCESSINGQUEUECOUNT)
        true
    }
}
