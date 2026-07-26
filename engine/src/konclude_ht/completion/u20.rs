//! `completion::u20` — port unit #20 of the completion task-handle algorithm
//! (family: Blocking (pairwise / label-optimized / dynamic); 24 methods,
//! cpp ranges 19326–27675).
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
//!   - `getAppliedANDRuleCount`                                         [27650]
//!   - `getAppliedORRuleCount`                                          [27654]
//!   - `getAppliedSOMERuleCount`                                        [27658]
//!   - `getAppliedATLEASTRuleCount`                                     [27662]
//!   - `getAppliedALLRuleCount`                                         [27666]
//!   - `getAppliedATMOSTRuleCount`                                      [27670]
//!   - `getAppliedTotalRuleCount`                                       [27674]
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
    CCALL, CCAND, CCAQAND, CCAQSOME, CCATLEAST, CCATMOST, CCBRANCHAQAND, CCEQ, CCFS_ALL_AQALL_TYPE,
    CCFS_SOME_TYPE, CCF_ATLEAST, CCF_ATMOST, CCF_VALUE, CCIMPLAQAND, CCOR, CCSOME,
};
use super::super::model::substrate::{Cint64, Id, NegLink, INVALID};
use super::super::model::{ConceptId, ConceptProcessDataId, RoleId};
use super::super::process::blocking_hash::{
    BlockingIndividualNodeCandidateData, BlockingIndividualNodeCandidateHash,
    BlockingIndividualNodeCandidateIterator, BlockingIndividualNodeLinkedCandidateHash,
};
use super::super::process::node::IndividualProcessNode;
use super::super::process::reapply_sat::{BlockingAltDataId, IndividualNodeBlockingTestData};
use super::super::process::satellites::CoreConceptDescriptorId;
use super::super::process::stubs::{BackendSyncDataId, IndiBlockDataId};
use super::super::process::{ConDescId, ConProcDescId, EdgeId, LabelSetId, NodeId};

use super::context::CalculationAlgorithmContextBase;

type BlockingAlternativeDataHandle = BlockingAltDataId;

/// Stack value returned by `getBlockingIndividualNodeCandidateIterator`.
type BlockingIndividualNodeCandidateIteratorHandle = BlockingIndividualNodeCandidateIterator;

impl super::algorithm::CompletionTaskHandleAlgorithm {
    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getAnywhereBlockingIndividualNodeLinkedCanidateHashed`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: the localized `CIndividualNodeBlockingTestData`
    /// setup/clear and `CReapplyConceptLabelSet::getCoreConceptDescriptorLinker`
    /// are live. The `CBlockingIndividualNodeLinkedCandidateHash` minimum-candidate
    /// search remains deferred; if a core linker exists and no linked candidate
    /// data is available, the method records the same block-data cursors Konclude
    /// would after an empty search and the candidate loop stays empty.
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
            // locBlockData = CObjectAllocator<CIndividualNodeBlockingTestData>::allocateAndConstruct(taskMemMan);
            // locBlockData->initBlockData(blockData); blockingTestIndi->setIndividualBlockData(locBlockData);
            let pc = calc_alg_context.process_context_mut();
            let new_block_data = pc.alloc_blocking_test_data(IndividualNodeBlockingTestData::new());
            if !block_data.is_none() {
                let taken = std::mem::replace(
                    pc.blocking_test_data_mut(block_data),
                    IndividualNodeBlockingTestData::new(),
                );
                pc.blocking_test_data_mut(new_block_data)
                    .init_block_data(Some(&taken));
                *pc.blocking_test_data_mut(block_data) = taken;
            } else {
                pc.blocking_test_data_mut(new_block_data)
                    .init_block_data(None);
            }
            pc.node_mut(blocking_test_indi)
                .set_individual_block_data(new_block_data);
            loc_block_data = new_block_data;
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
            calc_alg_context
                .process_context_mut()
                .blocking_test_data_mut(loc_block_data)
                .clear_blocking_individual_node();
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
                let previous_blocking_node = calc_alg_context
                    .process_context()
                    .blocking_test_data(loc_block_data)
                    .get_blocking_individual_node();
                if previous_blocking_node.is_some() {
                    last_continue_tested_blocking_indi_node_id = calc_alg_context
                        .process_context()
                        .node(previous_blocking_node)
                        .individual_node_id();
                }

                let blocking_cand_hash =
                    calc_alg_context.blocking_individual_node_linked_candidate_hash(false);
                // conSet = blockingTestIndi->getReapplyConceptLabelSet(false)
                let con_set: LabelSetId = calc_alg_context
                    .process_context_mut()
                    .node_mut(blocking_test_indi)
                    .get_reapply_concept_label_set(false);
                let core_con_des_linker = if con_set.is_some() {
                    calc_alg_context
                        .process_context()
                        .label_set(con_set)
                        .get_core_concept_descriptor_linker()
                } else {
                    CoreConceptDescriptorId::NONE
                };
                let blocking_test_indi_id = calc_alg_context
                    .process_context()
                    .node(blocking_test_indi)
                    .individual_node_id();

                if core_con_des_linker.is_none() {
                    blocker_node = self.get_anywhere_blocking_individual_node_canidate_hashed(
                        blocking_test_indi,
                        block_alt_data,
                        calc_alg_context,
                    );
                } else {
                    let mut min_blocking_ind_node_cand_data = Id::NONE;
                    let mut min_blocking_ind_node_cand_data_count: Cint64 = 0;
                    let mut min_blocking_con_des = ConDescId::NONE;
                    let mut last_min_blocking_ind_node_cand_data = Id::NONE;

                    let last_added_core_con_des = calc_alg_context
                        .process_context()
                        .blocking_test_data(loc_block_data)
                        .get_last_added_core_concept_descriptor();
                    let mut last_con_des = calc_alg_context
                        .process_context()
                        .blocking_test_data(loc_block_data)
                        .get_last_core_blocking_candidate_concept_descriptor();
                    let last_node_diff = calc_alg_context
                        .process_context()
                        .blocking_test_data(loc_block_data)
                        .get_last_core_blocking_candidate_concept_node_difference();
                    if last_added_core_con_des != core_con_des_linker {
                        last_con_des = ConDescId::NONE;
                    }

                    if blocking_cand_hash.is_some() && last_con_des.is_some() {
                        let blocking_cand_data =
                            BlockingIndividualNodeLinkedCandidateHash::get_blocking_individual_candidate_data_for_concept_descriptor(
                                calc_alg_context.process_context_mut(),
                                blocking_cand_hash,
                                last_con_des,
                                false,
                            );
                        if blocking_cand_data.is_some() {
                            let blocking_ind_node_cand_data_count = calc_alg_context
                                .process_context()
                                .blocking_indi_node_linked_cand_data(blocking_cand_data)
                                .get_candidate_count();
                            if blocking_ind_node_cand_data_count <= last_node_diff {
                                min_blocking_ind_node_cand_data = blocking_cand_data;
                                min_blocking_ind_node_cand_data_count =
                                    blocking_ind_node_cand_data_count;
                            }
                        }
                    }

                    if blocking_cand_hash.is_some() && min_blocking_ind_node_cand_data.is_none() {
                        let mut core_con_des_linker_it = core_con_des_linker;
                        while core_con_des_linker_it.is_some() {
                            let con_des = calc_alg_context
                                .process_context()
                                .core_con_desc(core_con_des_linker_it)
                                .get_concept_desciptor();
                            let blocking_cand_data =
                                BlockingIndividualNodeLinkedCandidateHash::get_blocking_individual_candidate_data_for_concept_descriptor(
                                    calc_alg_context.process_context_mut(),
                                    blocking_cand_hash,
                                    con_des,
                                    false,
                                );
                            if blocking_cand_data.is_some() {
                                let blocking_ind_node_cand_data_count = calc_alg_context
                                    .process_context()
                                    .blocking_indi_node_linked_cand_data(blocking_cand_data)
                                    .get_candidate_count();
                                if min_blocking_ind_node_cand_data.is_none()
                                    || blocking_ind_node_cand_data_count
                                        < min_blocking_ind_node_cand_data_count
                                {
                                    last_min_blocking_ind_node_cand_data =
                                        min_blocking_ind_node_cand_data;
                                    min_blocking_ind_node_cand_data_count =
                                        blocking_ind_node_cand_data_count;
                                    min_blocking_ind_node_cand_data = blocking_cand_data;
                                    min_blocking_con_des = con_des;
                                } else if last_min_blocking_ind_node_cand_data.is_none() {
                                    last_min_blocking_ind_node_cand_data = blocking_cand_data;
                                }
                            }
                            core_con_des_linker_it = calc_alg_context
                                .process_context()
                                .core_con_desc(core_con_des_linker_it)
                                .get_next();
                        }
                    }

                    calc_alg_context
                        .process_context_mut()
                        .blocking_test_data_mut(loc_block_data)
                        .set_last_added_core_concept_descriptor(core_con_des_linker)
                        .set_last_core_blocking_candidate_concept_descriptor(min_blocking_con_des)
                        .set_last_core_blocking_candidate_concept_node_difference(0);
                    if last_min_blocking_ind_node_cand_data.is_some() {
                        let diff_count = calc_alg_context
                            .process_context()
                            .blocking_indi_node_linked_cand_data(
                                last_min_blocking_ind_node_cand_data,
                            )
                            .get_candidate_count();
                        calc_alg_context
                            .process_context_mut()
                            .blocking_test_data_mut(loc_block_data)
                            .set_last_core_blocking_candidate_concept_node_difference(diff_count);
                    }

                    let blocking_cand_data = min_blocking_ind_node_cand_data;
                    let mut blocking_ind_node_linker = if blocking_cand_data.is_some() {
                        calc_alg_context
                            .process_context()
                            .blocking_indi_node_linked_cand_data(blocking_cand_data)
                            .get_blocking_candidates_individual_node_linker()
                    } else {
                        Id::NONE
                    };
                    while blocking_ind_node_linker.is_some() && blocker_node.is_none() {
                        let blocker_cand_indi_node = calc_alg_context
                            .process_context()
                            .blocking_indi_node_linker(blocking_ind_node_linker)
                            .get_candidate_individual_node();
                        if blocker_cand_indi_node.is_none() {
                            calc_alg_context.raise_stop(false);
                            return Id::NONE;
                        }
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
                            let up_blocker_cand_indi_node = self.get_up_to_date_individual(
                                blocker_cand_indi_node,
                                calc_alg_context,
                            );
                            if up_blocker_cand_indi_node.is_none() {
                                calc_alg_context.raise_stop(false);
                                return Id::NONE;
                            }

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
                                    while !anc_prev_indi_node.is_none()
                                        && calc_alg_context
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
                        blocking_ind_node_linker = calc_alg_context
                            .process_context()
                            .blocking_indi_node_linker(blocking_ind_node_linker)
                            .get_next();
                    }
                }
            }
        }

        blocker_node
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getAnywhereBlockingIndividualNodeCanidateHashed`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: the localized `CIndividualNodeBlockingTestData`
    /// and `CNodeSwitchHistory` tag/min-bound bookkeeping are live. The
    /// candidate-traversal branches are reproduced over the typed candidate
    /// iterator or the descending-id scan; remaining deferrals inside the
    /// downstream blocker predicates stay at their own call sites.
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
            // locBlockData = CObjectAllocator<CIndividualNodeBlockingTestData>::allocateAndConstruct(taskMemMan);
            // locBlockData->initBlockData(blockData); blockingTestIndi->setIndividualBlockData(locBlockData);
            let pc = calc_alg_context.process_context_mut();
            let new_block_data = pc.alloc_blocking_test_data(IndividualNodeBlockingTestData::new());
            if !block_data.is_none() {
                let taken = std::mem::replace(
                    pc.blocking_test_data_mut(block_data),
                    IndividualNodeBlockingTestData::new(),
                );
                pc.blocking_test_data_mut(new_block_data)
                    .init_block_data(Some(&taken));
                *pc.blocking_test_data_mut(block_data) = taken;
            } else {
                pc.blocking_test_data_mut(new_block_data)
                    .init_block_data(None);
            }
            pc.node_mut(blocking_test_indi)
                .set_individual_block_data(new_block_data);
            loc_block_data = new_block_data;
        }
        let prev_node_switch_tag = calc_alg_context
            .process_context()
            .blocking_test_data(loc_block_data)
            .get_node_switch_tag();
        let prev_node_concept_label_mod_tag = calc_alg_context
            .process_context()
            .blocking_test_data(loc_block_data)
            .get_concept_label_set_modification_tag();
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
            let previous_blocking_node = calc_alg_context
                .process_context()
                .blocking_test_data(loc_block_data)
                .get_blocking_individual_node();
            if previous_blocking_node.is_some() {
                last_continue_tested_blocking_indi_node_id = calc_alg_context
                    .process_context()
                    .node(previous_blocking_node)
                    .individual_node_id();
            }
            if node_switch_history != Id::NONE && prev_node_switch_tag > 0 {
                (min_test_indi_node_id, min_test_anc_indi_depth) = calc_alg_context
                    .node_switch_history_min_bounds(
                        node_switch_history,
                        prev_node_switch_tag,
                        0,
                        0,
                    );
            }
            if calc_alg_context
                .process_context()
                .node(blocking_test_indi)
                .individual_initialization_concept()
                != Id::NONE
            {
                let mut indi_node_cand_it = self.get_blocking_individual_node_candidate_iterator(
                    blocking_test_indi,
                    calc_alg_context,
                );
                while blocker_node == Id::NONE && indi_node_cand_it.has_next() {
                    let Some(indi_node) = indi_node_cand_it.next_individual_candidate(true) else {
                        continue;
                    };
                    if indi_node.is_none() {
                        calc_alg_context.raise_stop(false);
                        return Id::NONE;
                    }
                    let mut up_indi_node =
                        self.get_up_to_date_individual(indi_node, calc_alg_context);
                    if up_indi_node.is_none() {
                        calc_alg_context.raise_stop(false);
                        return Id::NONE;
                    }
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
                            indi_node_cand_it.remove_last_individual_candidate_in_context(
                                calc_alg_context.process_context_mut(),
                            );
                        } else if self
                            .is_individual_node_valid_blocker(up_indi_node, calc_alg_context)
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
                while blocker_node == Id::NONE
                    && prev_indi_id > 0
                    && prev_indi_id >= min_test_indi_node_id
                {
                    if prev_indi_id != last_continue_tested_blocking_indi_node_id {
                        prev_indi_node =
                            self.get_up_to_date_individual_by_id(prev_indi_id, calc_alg_context);
                        if prev_indi_node != Id::NONE
                            && self
                                .is_individual_node_valid_blocker(prev_indi_node, calc_alg_context)
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
        calc_alg_context
            .process_context_mut()
            .blocking_test_data_mut(loc_block_data)
            .set_blocking_individual_node(blocker_node);
        if blocker_node == Id::NONE {
            let (current_node_switch_tag, current_label_mod_tag) = {
                let process_tagger = calc_alg_context.process_context().used_process_tagger();
                (
                    process_tagger.get_current_node_switch_tag(),
                    process_tagger.get_current_concept_label_set_modification_tag(),
                )
            };
            let loc_block_data_ref = calc_alg_context
                .process_context_mut()
                .blocking_test_data_mut(loc_block_data);
            loc_block_data_ref.update_node_switch_tag(current_node_switch_tag);
            loc_block_data_ref.update_concept_label_set_modification_tag(current_label_mod_tag);
        }
        blocker_node
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getBlockingIndividualNodeCandidateIterator`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: the returned `CBlockingIndividualNodeCandidateIterator`,
    /// the `CBlockingIndividualNodeCandidateHash` / `…CandidateData` lazy-hash update
    /// (max-valid-id / tag bookkeeping + descending-id rebuild) and the
    /// `CNodeSwitchHistory` min-ancestor lookup are live over the Rust arenas. The
    /// remaining explicit deferrals in this method are statistics/memory-pool
    /// bookkeeping and whatever downstream blocker checks still defer.
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
        if initialization_concept_des.is_none() {
            return BlockingIndividualNodeCandidateIterator::empty();
        }
        // procDataBox->getNodeSwitchHistory(false)
        let node_switch_history = calc_alg_context.node_switch_history(false);
        // test whether hash has to be updated
        let mut needs_hash_update = true;
        // blockingCandHash = procDataBox->getBlockingIndividualNodeCandidateHash(true);
        let blocking_cand_hash = calc_alg_context.blocking_individual_node_candidate_hash(true);
        let blocking_cand_data = BlockingIndividualNodeCandidateHash::get_blocking_individual_candidate_data_for_concept_descriptor(
            calc_alg_context.process_context_mut(),
            blocking_cand_hash,
            initialization_concept_des,
            true,
        );

        if self.conf_anywhere_blocking_lazy_exact_hashing {
            let mut max_valid_indi_id = calc_alg_context
                .process_context()
                .blocking_indi_node_cand_data(blocking_cand_data)
                .get_max_valid_individual_id()
                + 1;
            let con_label_set_mod_tag = calc_alg_context
                .process_context()
                .blocking_indi_node_cand_data(blocking_cand_data)
                .get_concept_label_set_modification_tag();
            let node_switch_tag = calc_alg_context
                .process_context()
                .blocking_indi_node_cand_data(blocking_cand_data)
                .get_node_switch_tag();
            let mut min_test_indi_node_id: Cint64 = 1;
            let mut min_test_anc_indi_depth: Cint64 = 0;
            if node_switch_history != Id::NONE && node_switch_tag > 0 {
                (min_test_indi_node_id, min_test_anc_indi_depth) = calc_alg_context
                    .node_switch_history_min_bounds(node_switch_history, node_switch_tag, 1, 0);
            }
            if max_valid_indi_id >= testing_indi_id && min_test_indi_node_id >= testing_indi_id {
                needs_hash_update = false;
            }
            if needs_hash_update {
                // W6-DEFER[macro]: STATINC(ANYWHEREBLOCKINGCANDIDATEHASHUDATECOUNT)
                if max_valid_indi_id != testing_indi_id {
                    // insert testing node
                    // W6-DEFER[macro]: STATINC(ANYWHEREBLOCKINGCANDIDATEHASHUDATEADDCOUNT)
                    calc_alg_context
                        .process_context_mut()
                        .blocking_indi_node_cand_data_insert_blocking_candidate_individual_node(
                            blocking_cand_data,
                            blocking_test_indi,
                        );
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
                            let label_set: LabelSetId = calc_alg_context
                                .process_context_mut()
                                .node_mut(indi)
                                .get_reapply_concept_label_set(false);
                            if label_set.is_some()
                                && calc_alg_context
                                    .process_context()
                                    .label_set(label_set)
                                    .contains_concept_descriptor_in_context(
                                        calc_alg_context.process_context(),
                                        calc_alg_context.ontology_arenas(),
                                        initialization_concept_des,
                                    )
                            {
                                // W6-DEFER[macro]: STATINC(ANYWHEREBLOCKINGCANDIDATEHASHUDATEADDCOUNT)
                                calc_alg_context
                                    .process_context_mut()
                                    .blocking_indi_node_cand_data_insert_blocking_candidate_individual_node(
                                        blocking_cand_data,
                                        indi,
                                    );
                            }
                        }
                    }
                    indi_id -= 1;
                }
                let (current_label_mod_tag, current_node_switch_tag) = {
                    let process_tagger = calc_alg_context.process_context().used_process_tagger();
                    (
                        process_tagger.get_current_concept_label_set_modification_tag(),
                        process_tagger.get_current_node_switch_tag(),
                    )
                };
                {
                    let blocking_cand_data_ref = calc_alg_context
                        .process_context_mut()
                        .blocking_indi_node_cand_data_mut(blocking_cand_data);
                    blocking_cand_data_ref
                        .update_concept_label_set_modification_tag(current_label_mod_tag);
                    blocking_cand_data_ref.update_node_switch_tag(current_node_switch_tag);
                    blocking_cand_data_ref
                        .set_max_valid_individual_id(max_valid_indi_id.max(testing_indi_id));
                }
                max_valid_indi_id = max_valid_indi_id.max(testing_indi_id);
            }
        }

        BlockingIndividualNodeCandidateData::get_blocking_candidates_individual_node_iterator_for_node_in_context(
            calc_alg_context.process_context(),
            blocking_cand_data,
            blocking_test_indi,
        )
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
            if succ_indi.is_none() {
                continue;
            }
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
            if succ_indi.is_none() {
                continue;
            }
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
                return self
                    .detect_individual_node_blocked_status(blocking_test_indi, calc_alg_context);
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
                return self
                    .detect_individual_node_blocked_status(blocking_test_indi, calc_alg_context);
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
                return self
                    .detect_individual_node_blocked_status(blocking_test_indi, calc_alg_context);
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
    /// KONCLUDE-PORT-NOTE[api]: the backend-sync object is live, so the `assocData`
    /// null gate now reads `backendSyncData->getAssocitaionData()`. The downstream
    /// association-data completeness / label-cache tests still depend on backend
    /// cache handler semantics and remain deferred.
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
            let assoc_data = calc_alg_context
                .process_context()
                .backend_sync_data(backend_sync_data)
                .get_associtaion_data();
            if assoc_data.is_some() {
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
    /// KONCLUDE-PORT-NOTE[api]: the backend-sync data object is live and this method
    /// reads/writes the sync-owned criticality flags and cursors exactly at the
    /// Konclude call sites. The per-role cardinality loop is LIVE against the typed
    /// native-ABox association's cardinality extension (`cached_at_most_cardinalities`
    /// / `cached_existential_max_cardinalities`); the generic
    /// `CBackendRepresentativeMemoryLabelCacheItemCardinalityExtensionData` lookup
    /// stays deferred to the cache-handler wave.
    ///
    /// The newly-merged test runs through the live u15 visitor. Note that — unlike
    /// `testIndividualNodeBackendCacheNeighbourExpansionBlockingCritical` — this
    /// predicate has NO unconditional `getMergedIndividualNodeLinker()` test after
    /// it: a merged node only makes the cardinality critical when it is itself a
    /// backend-cache representative (it carries synchronisation data).
    pub fn test_individual_node_backend_cache_expansion_blocking_critical_cardinality(
        &mut self,
        indi_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut expansion_blocking_critical = false;
        // The typed native-ABox association is held in the bridge replay journal
        // instead of the generic representative-memory cache. Ensure the localized
        // backend-sync data that carries this predicate's gate + cursors exists, so
        // the C++ control flow below runs unchanged against either association.
        let native_assoc_tag = self.native_association_tag(indi_node, calc_alg_context);
        if native_assoc_tag.is_some()
            && calc_alg_context
                .process_context()
                .node(indi_node)
                .individual_backend_cache_synchronisation_data(false)
                == Id::NONE
        {
            self.get_localized_individual_backend_cache_snychronisation_data(
                indi_node,
                calc_alg_context,
            );
        }
        let backend_sync_data: BackendSyncDataId = calc_alg_context
            .process_context()
            .node(indi_node)
            .individual_backend_cache_synchronisation_data(false);
        let mut loc_backend_sync_data: BackendSyncDataId = calc_alg_context
            .process_context()
            .node(indi_node)
            .individual_backend_cache_synchronisation_data(true);

        if backend_sync_data != Id::NONE {
            let assoc_data = calc_alg_context
                .process_context()
                .backend_sync_data(backend_sync_data)
                .get_associtaion_data();
            let is_critical_cardinality_expansion_blocking = calc_alg_context
                .process_context()
                .backend_sync_data(backend_sync_data)
                .is_critical_cardinality_expansion_blocking();
            if !is_critical_cardinality_expansion_blocking
                && (assoc_data.is_some() || native_assoc_tag.is_some())
            {
                self.test_individual_node_backend_cache_new_mergings(indi_node, calc_alg_context);
                // backendSyncData = indiNode->getIndividualBackendCacheSynchronisationData(false);
                let backend_sync_data: BackendSyncDataId = calc_alg_context
                    .process_context()
                    .node(indi_node)
                    .individual_backend_cache_synchronisation_data(false);

                let (merged_linker_changed, merged_linker_snapshot, last_tested_linker_snapshot) = {
                    let sync = calc_alg_context
                        .process_context()
                        .backend_sync_data(backend_sync_data);
                    (
                        sync.get_merged_individual_node_linker()
                            != sync.get_last_critical_neighbours_tested_merged_node_linker(),
                        sync.get_merged_individual_node_linker().to_vec(),
                        sync.get_last_critical_neighbours_tested_merged_node_linker()
                            .to_vec(),
                    )
                };
                if merged_linker_changed {
                    // visitNewlyMergedOnlyDeterministicRepresentativeIndividualsBackendSynchronisationData(
                    //   indiNode, mergedLinker, lastTested, false,
                    //   [&](…) { expansionBlockingCritical = true; return false; }, ctx);
                    //
                    // The visitor stops on its FIRST visited node, but it only visits a
                    // newly merged node that ITSELF carries backend-cache
                    // synchronisation data (u15). A changed-but-non-representative
                    // merged linker is therefore NOT critical here — unlike the
                    // neighbour variant, this predicate has no unconditional
                    // `getMergedIndividualNodeLinker()` test after the visit.
                    let mut newly_merged_representative = false;
                    self.visit_newly_merged_only_deterministic_representative_individuals_backend_synchronisation_data(
                        indi_node,
                        &merged_linker_snapshot,
                        &last_tested_linker_snapshot,
                        false,
                        &mut |_base_indi_node, _loc_indi_node, _back_sync_dep_track_point| {
                            newly_merged_representative = true;
                            false
                        },
                        calc_alg_context,
                    );
                    if newly_merged_representative {
                        expansion_blocking_critical = true;
                    }
                    loc_backend_sync_data = self
                        .get_localized_individual_backend_cache_snychronisation_data(
                            indi_node,
                            calc_alg_context,
                        );
                    calc_alg_context
                        .process_context_mut()
                        .backend_sync_data_mut(loc_backend_sync_data)
                        .set_last_critical_neighbours_tested_merged_node_linker(
                            merged_linker_snapshot,
                        );
                }

                // fullConSetLabelCacheItem = assocData->getLabelCacheEntry(FULL_CONCEPT_SET_LABEL);
                // cardExtensionData = fullConSetLabelCacheItem->getExtensionData(CARDINALITY_HASH);
                // On the typed route the cardinality extension is the replay
                // record's at-most / existential-max cardinality pairs.
                if let Some(assoc_tag) = native_assoc_tag {
                    if !expansion_blocking_critical {
                        let replay = self.native_nominal_backend_replay.get(&assoc_tag).cloned();
                        let has_cardinality_extension = replay
                            .as_ref()
                            .is_some_and(|replay| !replay.cached_at_most_cardinalities.is_empty());
                        let role_succ_hash = calc_alg_context
                            .process_context_mut()
                            .node_mut(indi_node)
                            .get_reapply_role_successor_hash(false);
                        if role_succ_hash != Id::NONE && has_cardinality_extension {
                            let replay = replay.expect("cardinality extension implies a replay");
                            let last_added_link_edge: EdgeId = calc_alg_context
                                .process_context()
                                .node(indi_node)
                                .get_last_added_role_link();
                            let last_tested_link_edge = calc_alg_context
                                .process_context()
                                .backend_sync_data(backend_sync_data)
                                .get_last_critical_cardinality_link_edge();
                            let critical_cardinality_initially_checked = calc_alg_context
                                .process_context()
                                .backend_sync_data(backend_sync_data)
                                .has_critical_cardinality_initially_checked();
                            // if (lastTestedLinkEdge != lastAddedLinkEdge
                            //     || !assocData->isCompletelyHandled()
                            //        && !backendSyncData->hasCriticalCardinalityInitiallyChecked())
                            //
                            // `expansion_blocking_candidate` is the typed record's
                            // `isCompletelyHandled() && …` conjunction, so its negation
                            // is the exact "not completely handled" disjunct here.
                            if last_tested_link_edge != last_added_link_edge
                                || !replay.expansion_blocking_candidate
                                    && !critical_cardinality_initially_checked
                            {
                                // The per-role loop (linkCount = roleSuccHash count
                                // + existentialMaxUsedCardinality when the successor
                                // expansion is blocked + the cached representative
                                // neighbour count; critical iff > minimumRestrictingCardinality).
                                expansion_blocking_critical = !self
                                    .native_cardinality_critical_roles(
                                        indi_node,
                                        &replay,
                                        calc_alg_context,
                                    )
                                    .is_empty();
                                loc_backend_sync_data = self
                                    .get_localized_individual_backend_cache_snychronisation_data(
                                        indi_node,
                                        calc_alg_context,
                                    );
                                calc_alg_context
                                    .process_context_mut()
                                    .backend_sync_data_mut(loc_backend_sync_data)
                                    .set_last_critical_cardinality_link_edge(last_added_link_edge)
                                    .set_critical_cardinality_initially_checked(true);
                            }
                        }
                    }
                }

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
                        let last_added_link_edge: EdgeId = calc_alg_context
                            .process_context()
                            .node(indi_node)
                            .get_last_added_role_link();
                        let last_tested_link_edge = calc_alg_context
                            .process_context()
                            .backend_sync_data(backend_sync_data)
                            .get_last_critical_cardinality_link_edge();
                        let _assoc_data = calc_alg_context
                            .process_context()
                            .backend_sync_data(backend_sync_data)
                            .get_associtaion_data();
                        let critical_cardinality_initially_checked = calc_alg_context
                            .process_context()
                            .backend_sync_data(backend_sync_data)
                            .has_critical_cardinality_initially_checked();
                        let _ = (
                            last_tested_link_edge,
                            last_added_link_edge,
                            critical_cardinality_initially_checked,
                        );

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
                            let _all_neighbour_forced_expansion = calc_alg_context
                                .process_context()
                                .backend_sync_data(backend_sync_data)
                                .has_all_neighbour_forced_expansion();
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
                    calc_alg_context
                        .process_context_mut()
                        .backend_sync_data_mut(loc_backend_sync_data)
                        .set_critical_cardinality_expansion_blocking(expansion_blocking_critical);
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
    /// KONCLUDE-PORT-NOTE[api]: LIVE. The backend-sync-owned gates/cursors, the
    /// concept-descriptor scan with BOTH incremental cut-offs
    /// (`lastCriticalNeighbourExpansionTestedConceptDescriptor` and, when the
    /// association is completely propagated, `lastSynchedConceptDescriptor`), the
    /// newly-merged-representative test and the per-concept sibling all run. The
    /// association is resolved as either the generic representative-memory id or the
    /// typed native-ABox handle (the nominal tag; see the `native_*` backend-cache
    /// accessors in u36). The commented-out festo.com debug block in the source is
    /// omitted (dead debug code).
    pub fn test_individual_node_backend_cache_neighbour_expansion_blocking_critical(
        &mut self,
        indi_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut expansion_blocking_critical = false;

        // The typed native-ABox association is held in the bridge replay journal
        // instead of the generic representative-memory cache; ensure the localized
        // backend-sync data that owns this predicate's gate + cursors exists so the
        // C++ control flow below runs unchanged against either association.
        let native_assoc_tag = self.native_association_tag(indi_node, calc_alg_context);
        if native_assoc_tag.is_some()
            && calc_alg_context
                .process_context()
                .node(indi_node)
                .individual_backend_cache_synchronisation_data(false)
                == Id::NONE
        {
            self.get_localized_individual_backend_cache_snychronisation_data(
                indi_node,
                calc_alg_context,
            );
        }
        let backend_sync_data: BackendSyncDataId = calc_alg_context
            .process_context()
            .node(indi_node)
            .individual_backend_cache_synchronisation_data(false);
        let mut loc_backend_sync_data: BackendSyncDataId = calc_alg_context
            .process_context()
            .node(indi_node)
            .individual_backend_cache_synchronisation_data(true);

        if backend_sync_data != Id::NONE {
            let assoc_data = calc_alg_context
                .process_context()
                .backend_sync_data(backend_sync_data)
                .get_associtaion_data();
            // The opaque association handle passed to the per-concept sibling: the
            // nominal tag on the typed route, the generic association id otherwise.
            let assoc_handle: Cint64 = match native_assoc_tag {
                Some(tag) => tag,
                None => assoc_data.raw,
            };
            let is_critical_neighbour_expansion_blocking = calc_alg_context
                .process_context()
                .backend_sync_data(backend_sync_data)
                .is_critical_neighbour_expansion_blocking();
            if (assoc_data.is_some() || native_assoc_tag.is_some())
                && !is_critical_neighbour_expansion_blocking
            {
                self.test_individual_node_backend_cache_new_mergings(indi_node, calc_alg_context);
                let backend_sync_data: BackendSyncDataId = calc_alg_context
                    .process_context()
                    .node(indi_node)
                    .individual_backend_cache_synchronisation_data(false);

                let (
                    merged_linker_changed,
                    merged_linker_snapshot,
                    last_tested_linker_snapshot,
                    has_merged_individual_node_linker,
                ) = {
                    let sync = calc_alg_context
                        .process_context()
                        .backend_sync_data(backend_sync_data);
                    (
                        sync.get_merged_individual_node_linker()
                            != sync.get_last_critical_neighbours_tested_merged_node_linker(),
                        sync.get_merged_individual_node_linker().to_vec(),
                        sync.get_last_critical_neighbours_tested_merged_node_linker()
                            .to_vec(),
                        !sync.get_merged_individual_node_linker().is_empty(),
                    )
                };
                if merged_linker_changed {
                    // visitNewlyMergedOnlyDeterministicRepresentativeIndividualsBackendSynchronisationData(
                    //   indiNode, mergedLinker, lastCriticalNeighboursTestedLinker, false,
                    //   [&](…) { expansionBlockingCritical = true; return false; }, ctx);
                    // Visits only a newly merged node that itself carries backend-cache
                    // synchronisation data (u15). Subsumed by the unconditional
                    // `getMergedIndividualNodeLinker()` test right below, which the C++
                    // also performs here — kept for exactness.
                    let mut newly_merged_representative = false;
                    self.visit_newly_merged_only_deterministic_representative_individuals_backend_synchronisation_data(
                        indi_node,
                        &merged_linker_snapshot,
                        &last_tested_linker_snapshot,
                        false,
                        &mut |_base_indi_node, _loc_indi_node, _back_sync_dep_track_point| {
                            newly_merged_representative = true;
                            false
                        },
                        calc_alg_context,
                    );
                    if newly_merged_representative {
                        expansion_blocking_critical = true;
                    }
                    loc_backend_sync_data = self
                        .get_localized_individual_backend_cache_snychronisation_data(
                            indi_node,
                            calc_alg_context,
                        );
                    calc_alg_context
                        .process_context_mut()
                        .backend_sync_data_mut(loc_backend_sync_data)
                        .set_last_critical_neighbours_tested_merged_node_linker(
                            merged_linker_snapshot,
                        );
                }
                if has_merged_individual_node_linker {
                    expansion_blocking_critical = true;
                } else {
                    if !self.test_individual_node_backend_cache_concepts_synchronization(
                        indi_node,
                        calc_alg_context,
                    ) {
                        let last_tested_con_des: ConDescId = calc_alg_context
                            .process_context()
                            .backend_sync_data(backend_sync_data)
                            .get_last_critical_neighbour_expansion_tested_concept_descriptor();
                        let mut last_synched_con_des: ConDescId = calc_alg_context
                            .process_context()
                            .backend_sync_data(backend_sync_data)
                            .get_last_synched_concept_descriptor();
                        // if (!assocData->isCompletelyPropagated()) lastSynchedConDes = nullptr;
                        //
                        // Dropping the cursor makes the scan reach every descriptor;
                        // keeping it is the second incremental cut-off that bounds the
                        // scan to the descriptors added since the last synchronization.
                        if !native_assoc_tag.is_some_and(|tag| {
                            self.native_association_completely_propagated(tag)
                        }) {
                            last_synched_con_des = Id::NONE;
                        }
                        // conSet = indiNode->getReapplyConceptLabelSet(false);
                        let con_set: LabelSetId = calc_alg_context
                            .process_context_mut()
                            .node_mut(indi_node)
                            .get_reapply_concept_label_set(false);
                        if con_set != Id::NONE {
                            let con_des_linker = calc_alg_context
                                .process_context()
                                .label_set(con_set)
                                .get_adding_sorted_concept_description_linker();
                            let mut new_last_tested_con_des: ConDescId = con_des_linker;
                            if con_des_linker != last_tested_con_des {
                                let mut concept_expansion_blocking_critical = false;
                                let mut con_des_it = con_des_linker;
                                while con_des_it.is_some()
                                    && con_des_it != last_tested_con_des
                                    && con_des_it != last_synched_con_des
                                {
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
                                    let nondeterministic = self.has_nondeterministic_dependency(
                                        dep_track_point,
                                        calc_alg_context,
                                    );

                                    if assoc_handle >= 0
                                        && self
                                            .test_individual_node_concept_backend_cache_neighbour_expansion_blocking_critical(
                                                concept,
                                                con_negation,
                                                nondeterministic,
                                                assoc_handle,
                                                calc_alg_context,
                                            )
                                    {
                                        concept_expansion_blocking_critical = true;
                                        new_last_tested_con_des = con_des_it;
                                    }
                                    con_des_it = calc_alg_context
                                        .process_context()
                                        .con_desc(con_des_it)
                                        .get_next_concept_descriptor();
                                }
                                loc_backend_sync_data = self
                                    .get_localized_individual_backend_cache_snychronisation_data(
                                        indi_node,
                                        calc_alg_context,
                                    );
                                if concept_expansion_blocking_critical
                                    && new_last_tested_con_des != Id::NONE
                                {
                                    new_last_tested_con_des = calc_alg_context
                                        .process_context()
                                        .con_desc(new_last_tested_con_des)
                                        .get_next_concept_descriptor();
                                }
                                calc_alg_context
                                    .process_context_mut()
                                    .backend_sync_data_mut(loc_backend_sync_data)
                                    .set_last_critical_neighbour_expansion_tested_concept_descriptor(
                                        new_last_tested_con_des,
                                    );
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
                    calc_alg_context
                        .process_context_mut()
                        .backend_sync_data_mut(loc_backend_sync_data)
                        .set_critical_neighbour_expansion_blocking(expansion_blocking_critical);
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
    /// KONCLUDE-PORT-NOTE[api]: LIVE. The concept-operator dispatch and the recursive
    /// AQ-AND descent are reproduced in FULL over the concept arena; the terminal
    /// label-cache queries (`hasConceptInAssociatedFullConceptSetLabel` /
    /// `hasRoleInAssociatedCompinationRoleSetLabel`) and
    /// `assocData->isCompletelyPropagated()` run against the typed native-ABox
    /// association (`assoc_data` is its opaque handle — the nominal individual tag).
    /// An unresolvable handle reproduces the C++ `!mBackendCacheHandler || ...`
    /// disjunction, so a matching `∀/⩽` / `∃/⩾/value` concept is then flagged
    /// critical, which never skips work.
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
            && con_operator.has_partial_operator_code_flag(CCFS_ALL_AQALL_TYPE | CCF_ATMOST)
            || con_negation
                && con_operator
                    .has_partial_operator_code_flag(CCFS_SOME_TYPE | CCF_ATLEAST | CCF_VALUE)
        {
            let role: RoleId = calc_alg_context
                .ontology_arenas()
                .concept(concept)
                .get_role();
            // `assocData` arrives as the opaque association handle: the nominal tag
            // of the typed native-ABox association, or the generic association id.
            // A handle with no typed association behind it reproduces the C++
            // `!mBackendCacheHandler ||` disjunct — every matching operator is then
            // critical, which never skips work.
            if assoc_data < 0
                || self.native_association_handle_for_individual(assoc_data) != assoc_data
            {
                expansion_blocking_critical = true;
            } else if self.native_association_completely_propagated(assoc_data) {
                // if (!mBackendCacheHandler
                //     || !nondeterministic && !mBackendCacheHandler->hasConceptInAssociatedFullConceptSetLabel(
                //          assocData, FULL_CONCEPT_SET_LABEL, concept, conNegation,
                //          !nondeterministic, calcAlgContext))
                //   expansionBlockingCritical = true;
                if !nondeterministic
                    && !self.native_has_concept_in_full_concept_set_label(
                        assoc_data,
                        concept,
                        con_negation,
                        !nondeterministic,
                    )
                {
                    expansion_blocking_critical = true;
                }
            } else {
                // if (!mBackendCacheHandler
                //     || mBackendCacheHandler->hasRoleInAssociatedCompinationRoleSetLabel(
                //          assocData, DETERMINISTIC_COMBINED_NEIGHBOUR_INSTANTIATED_ROLE_SET_LABEL, role, false)
                //     || mBackendCacheHandler->hasRoleInAssociatedCompinationRoleSetLabel(
                //          assocData, NONDETERMINISTIC_COMBINED_NEIGHBOUR_INSTANTIATED_ROLE_SET_LABEL, role, false))
                //   expansionBlockingCritical = true;
                if self.native_has_role_in_combined_neighbour_role_set_label(
                    assoc_data, role, true, false,
                ) || self.native_has_role_in_combined_neighbour_role_set_label(
                    assoc_data, role, false, false,
                ) {
                    expansion_blocking_critical = true;
                }
            }
        }
        expansion_blocking_critical
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addBlockingCoreConcept`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: `CConceptProcessData::isCoreBlockingConcept` and
    /// `CReapplyConceptLabelSet::addCoreConceptDescriptor` are live. The
    /// `CCoreConceptDescriptor` wrapper is folded to the original `CConceptDescriptor`
    /// id, as in the rest of this port's core-concept linker substrate. The
    /// `CBlockingIndividualNodeLinkedCandidateHash` candidate insertion is live.
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
            if con_data != INVALID {
                let is_negated: bool = calc_alg_context
                    .process_context()
                    .con_desc(concept_descriptor)
                    .is_negated();
                let con_pro_data = ConceptProcessDataId::new(con_data);
                let is_core_blocking_concept = calc_alg_context
                    .ontology_arenas()
                    .concept_process_data(con_pro_data)
                    .is_core_blocking_concept(is_negated);
                if is_core_blocking_concept {
                    if !calc_alg_context
                        .process_context()
                        .node(process_indi)
                        .is_nominal_individual_node()
                    {
                        // W6-DEFER[macro]: STATINC(CORECONCEPTSADDEDINDINODELABELSETCOUNT)
                        // W3-DEFER[memory-pool]: taskMemMan = calcAlgContext->getUsedProcessTaskMemoryAllocationManager();
                        calc_alg_context
                            .process_context_mut()
                            .label_set_add_core_concept_descriptor(
                                con_label_set,
                                concept_descriptor,
                            );

                        let blocking_cand_hash =
                            calc_alg_context.blocking_individual_node_linked_candidate_hash(true);
                        let blocking_cand_data =
                            BlockingIndividualNodeLinkedCandidateHash::get_blocking_individual_candidate_data_for_concept_descriptor(
                                calc_alg_context.process_context_mut(),
                                blocking_cand_hash,
                                concept_descriptor,
                                true,
                            );
                        calc_alg_context
                            .process_context_mut()
                            .blocking_indi_node_linked_cand_data_add_blocking_candidate_individual_node(
                                blocking_cand_data,
                                process_indi,
                            );
                    }

                    return true;
                }
            }
        }
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addIndividualToBlockingUpdateReviewProcessingQueue`.
    pub fn add_individual_to_blocking_update_review_processing_queue(
        &mut self,
        individual: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let sig_block_upd_pro_queue =
            calc_alg_context.get_blocking_update_review_processing_queue(true);
        calc_alg_context
            .process_context_mut()
            .indi_depth_queue_insert(sig_block_upd_pro_queue, individual);
        // W6-DEFER[macro]: STATINC(INDINODESADDEDPROCESSINGQUEUECOUNT)
        true
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getAppliedANDRuleCount`.
    pub fn get_applied_and_rule_count(&self) -> Cint64 {
        self.applied_and_rule_count
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getAppliedORRuleCount`.
    pub fn get_applied_or_rule_count(&self) -> Cint64 {
        self.applied_or_rule_count
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getAppliedSOMERuleCount`.
    pub fn get_applied_some_rule_count(&self) -> Cint64 {
        self.applied_some_rule_count
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getAppliedATLEASTRuleCount`.
    pub fn get_applied_atleast_rule_count(&self) -> Cint64 {
        self.applied_atleast_rule_count
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getAppliedALLRuleCount`.
    pub fn get_applied_all_rule_count(&self) -> Cint64 {
        self.applied_all_rule_count
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getAppliedATMOSTRuleCount`.
    pub fn get_applied_atmost_rule_count(&self) -> Cint64 {
        self.applied_atmost_rule_count
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getAppliedTotalRuleCount`.
    pub fn get_applied_total_rule_count(&self) -> Cint64 {
        self.applied_total_rule_count
    }
}
