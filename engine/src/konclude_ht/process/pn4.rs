//! `process::pn4` — method-batch unit **PN-4** of `CIndividualProcessNode`:
//! model/cache/blocking-data accessors + nominal-level-or-depth + processing-
//! blocked linkers + satisfiable-cached absorbed linkers + processing-restriction
//! flag ops + blocker-candidate counts
//! (`Source/Reasoner/Kernel/Process/CIndividualProcessNode.cpp` lines 1275–1671).
//!
//! All of PN-4 is plain self-local accessor/flag logic — no sibling node is read,
//! so every method stays a `&mut self`/`&self` method (no associated-fn-over-Arena
//! split needed for this unit).
//!
//! SKIPPED here (already ported in `node.rs` PN simple-accessor block): the
//! ancestor-depth / nominal-level / merged-into-id / processing-restriction-flag
//! getters that PN-4 also declares —
//! `getIndividualAncestorDepth`/`setIndividualAncestorDepth` (1452/1456),
//! `getIndividualNominalLevel`/`setIndividualNominalLevel` (1461/1465),
//! `getMergedIntoIndividualNodeID` (1478), `setMergedIntoIndividualNodeID` (1486),
//! `getProcessingRestrictionFlags` (1551), `hasProcessingRestrictionFlags` (1567),
//! `hasPartialProcessingRestrictionFlags` (1571).
//!
//! KONCLUDE-PORT-NOTE[unclear]: `node.rs::has_merged_into_individual_node_id`
//! (the ported `hasMergedIntoIndividualNodeID`) tests `merge_into_id != 0`, but
//! the C++ at `.cpp` 1482 tests `mMergeIntoID != mIndiID`. PN-4 does not re-port
//! it (it lives in `node.rs`); flagged here so the `node.rs` version can be
//! reconciled to `merge_into_id != indi_id`.

#![allow(dead_code)]

use super::super::model::{Cint64, Id};
use super::node::IndividualProcessNode;
use super::stubs::{
    AnalizedConExpDataId, BackendSyncDataId, BlockingFollowSetId, IndiBlockDataId,
    IndiSatBlockDataId, IndividualNodeModelDataId, ReapplyConDescId, ReusingConExpDataId,
    SatCacheRetDataId, SatCacheStoringDataId, SigBlockConExpDataId, UnsatCacheRetId,
    VarPropBlockDataId,
};
use super::{ConDescId, NodeId};

impl IndividualProcessNode {
    // ===================================================================
    // Model + cache data accessors (1275–1345).
    // ===================================================================

    /// Port of `CIndividualProcessNode::getIndividualModelData`.
    pub fn individual_model_data(&self) -> IndividualNodeModelDataId {
        self.indi_model
    }

    /// Port of `CIndividualProcessNode::setIndividualModelData`.
    pub fn set_individual_model_data(
        &mut self,
        individual_model: IndividualNodeModelDataId,
    ) -> &mut Self {
        self.indi_model = individual_model;
        self
    }

    /// Port of `CIndividualProcessNode::getIndividualSatisfiableCacheRetrievalData`.
    pub fn individual_satisfiable_cache_retrieval_data(
        &self,
        local_cache_data: bool,
    ) -> SatCacheRetDataId {
        if local_cache_data {
            self.sat_cache_ret_data
        } else {
            self.prev_sat_cache_ret_data
        }
    }

    /// Port of `CIndividualProcessNode::setIndividualSatisfiableCacheRetrievalData`.
    pub fn set_individual_satisfiable_cache_retrieval_data(
        &mut self,
        sat_cache_retrieval_data: SatCacheRetDataId,
    ) -> &mut Self {
        self.sat_cache_ret_data = sat_cache_retrieval_data;
        self.prev_sat_cache_ret_data = self.sat_cache_ret_data;
        self
    }

    /// Port of `CIndividualProcessNode::getIndividualBackendCacheSynchronisationData`.
    pub fn individual_backend_cache_synchronisation_data(
        &self,
        local_cache_data: bool,
    ) -> BackendSyncDataId {
        if local_cache_data {
            self.backend_sync_data
        } else {
            self.prev_backend_sync_data
        }
    }

    /// Port of `CIndividualProcessNode::setIndividualBackendCacheSynchronisationData`.
    pub fn set_individual_backend_cache_synchronisation_data(
        &mut self,
        backend_sync_data: BackendSyncDataId,
    ) -> &mut Self {
        self.backend_sync_data = backend_sync_data;
        self.prev_backend_sync_data = backend_sync_data;
        self
    }

    /// Port of `CIndividualProcessNode::getIndividualSatisfiableCacheStoringData`.
    pub fn individual_satisfiable_cache_storing_data(
        &self,
        local_cache_data: bool,
    ) -> SatCacheStoringDataId {
        if local_cache_data {
            self.sat_cache_storing_data
        } else {
            self.prev_sat_cache_storing_data
        }
    }

    /// Port of `CIndividualProcessNode::setIndividualSatisfiableCacheStoringData`.
    pub fn set_individual_satisfiable_cache_storing_data(
        &mut self,
        sat_cache_storing_data: SatCacheStoringDataId,
    ) -> &mut Self {
        self.sat_cache_storing_data = sat_cache_storing_data;
        self.prev_sat_cache_storing_data = self.sat_cache_storing_data;
        self
    }

    /// Port of `CIndividualProcessNode::getIndividualUnsatisfiableCacheRetrievalData`.
    pub fn individual_unsatisfiable_cache_retrieval_data(
        &self,
        local_unsat_cache_ret_data: bool,
    ) -> UnsatCacheRetId {
        if local_unsat_cache_ret_data {
            self.indi_unsat_cache_ret
        } else {
            self.prev_indi_unsat_cache_ret
        }
    }

    /// Port of `CIndividualProcessNode::setIndividualUnsatisfiableCacheRetrievalData`.
    pub fn set_individual_unsatisfiable_cache_retrieval_data(
        &mut self,
        individual_unsat_cache_ret_data: UnsatCacheRetId,
    ) -> &mut Self {
        self.indi_unsat_cache_ret = individual_unsat_cache_ret_data;
        self.prev_indi_unsat_cache_ret = self.indi_unsat_cache_ret;
        self
    }

    // ===================================================================
    // Signature-blocking / reusing concept-expansion data (1348–1404).
    // ===================================================================

    /// Port of `CIndividualProcessNode::getSignatureBlockingIndividualNodeConceptExpansionData`.
    pub fn signature_blocking_individual_node_concept_expansion_data(
        &self,
        local_blocking_data: bool,
    ) -> SigBlockConExpDataId {
        if local_blocking_data {
            self.sig_block_con_exp_data
        } else {
            self.prev_sig_block_con_exp_data
        }
    }

    /// Port of `CIndividualProcessNode::setSignatureBlockingIndividualNodeConceptExpansionData`.
    pub fn set_signature_blocking_individual_node_concept_expansion_data(
        &mut self,
        individual_blocking_data: SigBlockConExpDataId,
    ) -> &mut Self {
        self.sig_block_con_exp_data = individual_blocking_data;
        self.prev_sig_block_con_exp_data = self.sig_block_con_exp_data;
        self
    }

    /// Port of `CIndividualProcessNode::getReusingIndividualNodeConceptExpansionData`.
    pub fn reusing_individual_node_concept_expansion_data(
        &self,
        local_blocking_data: bool,
    ) -> ReusingConExpDataId {
        if local_blocking_data {
            self.reusing_con_exp_data
        } else {
            self.prev_reusing_con_exp_data
        }
    }

    /// Port of `CIndividualProcessNode::setReusingIndividualNodeConceptExpansionData`.
    pub fn set_reusing_individual_node_concept_expansion_data(
        &mut self,
        individual_blocking_data: ReusingConExpDataId,
    ) -> &mut Self {
        self.reusing_con_exp_data = individual_blocking_data;
        self.prev_reusing_con_exp_data = self.reusing_con_exp_data;
        self
    }

    /// Port of `CIndividualProcessNode::getAnalizedConceptExpansionData`.
    pub fn analized_concept_expansion_data(
        &mut self,
        create_or_localize: bool,
    ) -> AnalizedConExpDataId {
        if self.sig_block_ind_expl_data.is_none() && create_or_localize {
            // W2-DEFER[api]: CObjectAllocator<CIndividualNodeAnalizedConceptExpansionData>
            // ::allocateAndConstruct(mMemAllocMan) then
            // initBlockingExplorationData(mPrevSigBlockIndExplData) — both need the
            // process-context arena, not reachable from `&mut self`. The
            // `mUseX = mX` handoff that follows is preserved; `mX` stays NONE until
            // the allocator is wired.
            // self.sig_block_ind_expl_data = <allocated id>;
            self.use_sig_block_ind_expl_data = self.sig_block_ind_expl_data;
        }
        self.use_sig_block_ind_expl_data
    }

    /// Port of `CIndividualProcessNode::getBlockingFollowSet`.
    pub fn blocking_follow_set(&mut self, create_or_localize: bool) -> BlockingFollowSetId {
        if self.sig_block_follow_set.is_none() && create_or_localize {
            // W2-DEFER[api]: CObjectParameterizingAllocator<CBlockingFollowSet,
            // CProcessContext*>::allocateAndConstructAndParameterize(mMemAllocMan,
            // mProcessContext) then initBlockingFollowSet(mPrevSigBlockFollowSet) —
            // needs the process-context arena. The `mUseX = mX` handoff is preserved.
            // self.sig_block_follow_set = <allocated id>;
            self.use_sig_block_follow_set = self.sig_block_follow_set;
        }
        self.use_sig_block_follow_set
    }

    /// Port of `CIndividualProcessNode::hasBlockingFollower`.
    pub fn has_blocking_follower(&self) -> bool {
        if self.use_sig_block_follow_set.is_none() {
            false
        } else {
            // W2-DEFER[api]: CBlockingFollowSet::empty() — not yet ported (stub).
            // Faithful expression is `!self.use_sig_block_follow_set.empty()`; until
            // the follow-set is ported a present set is treated as non-empty.
            true
        }
    }

    // ===================================================================
    // Saturation/individual/var-prop block data (1407–1449).
    // ===================================================================

    /// Port of `CIndividualProcessNode::getIndividualSaturationBlockingData`.
    pub fn individual_saturation_blocking_data(&self, local_block_data: bool) -> IndiSatBlockDataId {
        if local_block_data {
            self.indi_sat_block_data
        } else {
            self.prev_indi_sat_block_data
        }
    }

    /// Port of `CIndividualProcessNode::setIndividualSaturationBlockingData`.
    pub fn set_individual_saturation_blocking_data(
        &mut self,
        individual_block: IndiSatBlockDataId,
    ) -> &mut Self {
        self.indi_sat_block_data = individual_block;
        self.prev_indi_sat_block_data = individual_block;
        self
    }

    /// Port of `CIndividualProcessNode::getIndividualBlockData`.
    pub fn individual_block_data(&self, local_block_data: bool) -> IndiBlockDataId {
        if local_block_data {
            self.indi_block
        } else {
            self.prev_indi_block
        }
    }

    /// Port of `CIndividualProcessNode::setIndividualBlockData`.
    pub fn set_individual_block_data(&mut self, individual_block: IndiBlockDataId) -> &mut Self {
        self.indi_block = individual_block;
        self.prev_indi_block = self.indi_block;
        self
    }

    /// Port of `CIndividualProcessNode::getVariableBindingsPropagationBlockingData`.
    pub fn variable_bindings_propagation_blocking_data(
        &self,
        local_block_data: bool,
    ) -> VarPropBlockDataId {
        if local_block_data {
            self.indi_var_prop_block_data
        } else {
            self.prev_indi_var_prop_block_data
        }
    }

    /// Port of `CIndividualProcessNode::setVariableBindingsPropagationBlockingData`.
    pub fn set_variable_bindings_propagation_blocking_data(
        &mut self,
        block_data: VarPropBlockDataId,
    ) -> &mut Self {
        self.indi_var_prop_block_data = block_data;
        self.prev_indi_var_prop_block_data = block_data;
        self
    }

    // ===================================================================
    // Nominal-level-or-ancestor-depth (1470).
    // ===================================================================

    /// Port of `CIndividualProcessNode::getIndividualNominalLevelOrAncestorDepth`.
    pub fn individual_nominal_level_or_ancestor_depth(&self) -> Cint64 {
        if self.is_nominal_individual_node() {
            return self.individual_nominal_level();
        }
        self.individual_ancestor_depth()
    }

    // ===================================================================
    // Processing-blocked individuals linker (1492–1506).
    // ===================================================================
    // KONCLUDE-PORT-NOTE[ownership]: `mProcessingBlockedIndividualsLinker` is a
    // `CXLinker<CIndividualProcessNode*>` chain, modelled in `node.rs` as
    // `Vec<NodeId>` (the whole chain by value). The linker arguments below are the
    // chain itself; `linker->append(existing)` (splice `linker` ahead of the
    // existing chain) becomes a `Vec` prepend; assignment of a chain head becomes
    // a whole-`Vec` move; `if (linker)` becomes `if !linker.is_empty()`.

    /// Port of `CIndividualProcessNode::addProcessingBlockedIndividualsLinker`.
    pub fn add_processing_blocked_individuals_linker(&mut self, linker: Vec<NodeId>) -> &mut Self {
        if !linker.is_empty() {
            let mut chain = linker;
            chain.append(&mut self.processing_blocked_individuals_linker);
            self.processing_blocked_individuals_linker = chain;
        }
        self
    }

    /// Port of `CIndividualProcessNode::setIndirectBlockedIndividualsLinker`.
    pub fn set_indirect_blocked_individuals_linker(&mut self, linker: Vec<NodeId>) -> &mut Self {
        self.processing_blocked_individuals_linker = linker;
        self
    }

    /// Port of `CIndividualProcessNode::getProcessingBlockedIndividualsLinker`.
    pub fn get_processing_blocked_individuals_linker(&self) -> &[NodeId] {
        &self.processing_blocked_individuals_linker
    }

    // ===================================================================
    // Satisfiable-cached absorbed disjunctions / generating linkers (1509–1547).
    // ===================================================================

    /// Port of `CIndividualProcessNode::getSatisfiableCachedAbsorbedDisjunctionsLinker`.
    pub fn satisfiable_cached_absorbed_disjunctions_linker(&self) -> ReapplyConDescId {
        self.sat_cached_absorbed_disjunctions_reapply_con_des
    }

    /// Port of `CIndividualProcessNode::clearSatisfiableCachedAbsorbedDisjunctionsLinker`.
    pub fn clear_satisfiable_cached_absorbed_disjunctions_linker(&mut self) -> &mut Self {
        self.sat_cached_absorbed_disjunctions_reapply_con_des = Id::NONE;
        self
    }

    /// Port of `CIndividualProcessNode::addSatisfiableCachedAbsorbedDisjunctionsLinker`.
    pub fn add_satisfiable_cached_absorbed_disjunctions_linker(
        &mut self,
        disjunction_reapply_con_des: ReapplyConDescId,
    ) -> &mut Self {
        if self.sat_cached_absorbed_disjunctions_reapply_con_des.is_none() {
            self.sat_cached_absorbed_disjunctions_reapply_con_des = disjunction_reapply_con_des;
        } else {
            // W2-DEFER[api]: disjunctionReapplyConDes->setNext(
            //   mSatCachedAbsorbedDisjunctionsReapplyConDes) — CReapplyConceptDescriptor
            // is a stub; the intrusive next-splice needs its arena. The head
            // reassignment (prepend) is preserved.
            self.sat_cached_absorbed_disjunctions_reapply_con_des = disjunction_reapply_con_des;
        }
        self
    }

    /// Port of `CIndividualProcessNode::clearSatisfiableCachedAbsorbedGeneratingLinker`.
    pub fn clear_satisfiable_cached_absorbed_generating_linker(&mut self) -> &mut Self {
        self.sat_cached_absorbed_successor_reapply_con_des = Id::NONE;
        self
    }

    /// Port of `CIndividualProcessNode::getSatisfiableCachedAbsorbedGeneratingLinker`.
    pub fn satisfiable_cached_absorbed_generating_linker(&self) -> ReapplyConDescId {
        self.sat_cached_absorbed_successor_reapply_con_des
    }

    /// Port of `CIndividualProcessNode::addSatisfiableCachedAbsorbedGeneratingLinker`.
    pub fn add_satisfiable_cached_absorbed_generating_linker(
        &mut self,
        successor_generating_reapply_con_des: ReapplyConDescId,
    ) -> &mut Self {
        if self.sat_cached_absorbed_successor_reapply_con_des.is_none() {
            self.sat_cached_absorbed_successor_reapply_con_des =
                successor_generating_reapply_con_des;
        } else {
            // W2-DEFER[api]: successorGeneratingReapplyConDes->setNext(
            //   mSatCachedAbsorbedSuccessorReapplyConDes) — stub CReapplyConceptDescriptor;
            // next-splice needs its arena. Head reassignment (prepend) preserved.
            self.sat_cached_absorbed_successor_reapply_con_des =
                successor_generating_reapply_con_des;
        }
        self
    }

    // ===================================================================
    // Processing-restriction flag add/clear (1555–1565).
    // ===================================================================

    /// Port of `CIndividualProcessNode::addProcessingRestrictionFlags`.
    pub fn add_processing_restriction_flags(&mut self, flags: Cint64) -> bool {
        let flags_backup = self.processing_restriction_flags;
        self.processing_restriction_flags |= flags;
        self.processing_restriction_flags != flags_backup
    }

    /// Port of `CIndividualProcessNode::clearProcessingRestrictionFlags`.
    pub fn clear_processing_restriction_flags(&mut self, flags: Cint64) -> bool {
        let flags_backup = self.processing_restriction_flags;
        self.processing_restriction_flags &= !flags;
        self.processing_restriction_flags != flags_backup
    }

    // ===================================================================
    // Individual initialization concept (1576–1583).
    // ===================================================================

    /// Port of `CIndividualProcessNode::getIndividualInitializationConcept`.
    pub fn individual_initialization_concept(&self) -> ConDescId {
        self.init_concept_descriptor
    }

    /// Port of `CIndividualProcessNode::setIndividualInitializationConcept`.
    pub fn set_individual_initialization_concept(&mut self, init_con_des: ConDescId) -> &mut Self {
        self.init_concept_descriptor = init_con_des;
        self
    }

    // ===================================================================
    // Blocking-retest / blocked processing-restriction flag predicates (1585–1615).
    // ===================================================================

    /// Port of `CIndividualProcessNode::hasBlockingRetestProcessingRestrictionFlags`.
    pub fn has_blocking_retest_processing_restriction_flags(&self) -> bool {
        self.has_partial_processing_restriction_flags(
            Self::PRF_BLOCKINGRETESTDUEANCESTORMODIFIED
                | Self::PRF_BLOCKINGRETESTDUEDIRECTMODIFIED
                | Self::PRF_BLOCKINGRETESTDUEBLOCKERMODIFIED
                | Self::PRF_BLOCKINGRETESTDUEINDIRECTBLOCKERLOSS
                | Self::PRF_BLOCKINGRETESTDUEPROCESSINGCOMPLETED,
        )
    }

    /// Port of `CIndividualProcessNode::clearBlockingRetestProcessingRestrictionFlags`.
    pub fn clear_blocking_retest_processing_restriction_flags(&mut self) -> bool {
        self.clear_processing_restriction_flags(
            Self::PRF_BLOCKINGRETESTDUEANCESTORMODIFIED
                | Self::PRF_BLOCKINGRETESTDUEDIRECTMODIFIED
                | Self::PRF_BLOCKINGRETESTDUEBLOCKERMODIFIED
                | Self::PRF_BLOCKINGRETESTDUEINDIRECTBLOCKERLOSS
                | Self::PRF_BLOCKINGRETESTDUEPROCESSINGCOMPLETED,
        )
    }

    /// Port of `CIndividualProcessNode::hasBlockedProcessingRestrictionFlags`.
    pub fn has_blocked_processing_restriction_flags(&self) -> bool {
        self.has_partial_processing_restriction_flags(
            Self::PRF_DIRECTBLOCKED | Self::PRF_INDIRECTBLOCKED | Self::PRF_PROCESSINGBLOCKED,
        )
    }

    /// Port of `CIndividualProcessNode::hasDirectBlockedProcessingRestrictionFlags`.
    pub fn has_direct_blocked_processing_restriction_flags(&self) -> bool {
        self.has_partial_processing_restriction_flags(Self::PRF_DIRECTBLOCKED)
    }

    /// Port of `CIndividualProcessNode::hasProcessingBlockedProcessingRestrictionFlags`.
    pub fn has_processing_blocked_processing_restriction_flags(&self) -> bool {
        self.has_partial_processing_restriction_flags(Self::PRF_PROCESSINGBLOCKED)
    }

    /// Port of `CIndividualProcessNode::hasPurgedBlockedProcessingRestrictionFlags`.
    pub fn has_purged_blocked_processing_restriction_flags(&self) -> bool {
        self.has_partial_processing_restriction_flags(Self::PRF_PURGEDBLOCKED)
    }

    /// Port of `CIndividualProcessNode::hasIndirectBlockedProcessingRestrictionFlags`.
    pub fn has_indirect_blocked_processing_restriction_flags(&self) -> bool {
        self.has_partial_processing_restriction_flags(Self::PRF_INDIRECTBLOCKED)
    }

    /// Port of `CIndividualProcessNode::clearBlockedProcessingRestrictionFlags`.
    pub fn clear_blocked_processing_restriction_flags(&mut self) -> bool {
        self.clear_processing_restriction_flags(
            Self::PRF_DIRECTBLOCKED | Self::PRF_INDIRECTBLOCKED | Self::PRF_PROCESSINGBLOCKED,
        )
    }

    // ===================================================================
    // Blocker-candidate counts / signatures (1619–1670).
    // ===================================================================

    /// Port of `CIndividualProcessNode::setLastConceptCountCachedBlockingCandidate`.
    pub fn set_last_concept_count_cached_blocking_candidate(&mut self, con_count: Cint64) -> &mut Self {
        self.last_concept_count_cached_blocker_candidate = con_count;
        self
    }

    /// Port of `CIndividualProcessNode::getLastConceptCountCachedBlockingCandidate`.
    pub fn last_concept_count_cached_blocking_candidate(&self) -> Cint64 {
        self.last_concept_count_cached_blocker_candidate
    }

    /// Port of `CIndividualProcessNode::getLastConceptCountSearchBlockingCandidate`.
    pub fn last_concept_count_search_blocking_candidate(&self) -> Cint64 {
        self.last_concept_count_search_blocker_candidate
    }

    /// Port of `CIndividualProcessNode::setLastConceptCountSearchBlockingCandidate`.
    pub fn set_last_concept_count_search_blocking_candidate(&mut self, con_count: Cint64) -> &mut Self {
        self.last_concept_count_search_blocker_candidate = con_count;
        self
    }

    /// Port of `CIndividualProcessNode::getBlockingCachingSavedCandidateCount`.
    pub fn blocking_caching_saved_candidate_count(&self) -> Cint64 {
        self.blocking_caching_saved_candidate_count
    }

    /// Port of `CIndividualProcessNode::setBlockingCachingSavedCandidateCount`.
    pub fn set_blocking_caching_saved_candidate_count(&mut self, con_count: Cint64) -> &mut Self {
        self.blocking_caching_saved_candidate_count = con_count;
        self
    }

    /// Port of `CIndividualProcessNode::incBlockingCachingSavedCandidateCount`.
    pub fn inc_blocking_caching_saved_candidate_count(&mut self, inc_count: Cint64) -> &mut Self {
        self.blocking_caching_saved_candidate_count += inc_count;
        self
    }

    /// Port of `CIndividualProcessNode::getLastSearchBlockerCandidateCount`.
    pub fn last_search_blocker_candidate_count(&self) -> Cint64 {
        self.last_search_blocker_candidate_count
    }

    /// Port of `CIndividualProcessNode::setLastSearchBlockerCandidateCount`.
    pub fn set_last_search_blocker_candidate_count(&mut self, can_count: Cint64) -> &mut Self {
        self.last_search_blocker_candidate_count = can_count;
        self
    }

    /// Port of `CIndividualProcessNode::getLastSearchBlockerCandidateSignature`.
    pub fn last_search_blocker_candidate_signature(&self) -> Cint64 {
        self.last_search_blocker_candidate_signature
    }

    /// Port of `CIndividualProcessNode::setLastSearchBlockerCandidateSignature`.
    pub fn set_last_search_blocker_candidate_signature(&mut self, can_count: Cint64) -> &mut Self {
        self.last_search_blocker_candidate_signature = can_count;
        self
    }
}
