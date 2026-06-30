//! `process::bm1` (port unit **BM-1**) — the method bodies of
//! `CBranchingMergingProcessingRestrictionSpecification`.
//!
//! Port of
//! `Source/Reasoner/Kernel/Process/CBranchingMergingProcessingRestrictionSpecification.cpp`
//! (lines 33–448). The struct definition + the trivial getters/setters that were
//! already needed at struct-def time live in `process/satellites.rs`; this unit
//! fills the remaining methods (the init/branch-clone, the distinct-merged-nodes
//! copy-on-write, the six candidate-linker take/add/clear chains, the
//! remaining-candidate counters, the merging-dependency / clash-descriptor
//! accessors, and the successor-choice-trigger handling).
//!
//! KONCLUDE-PORT-NOTE[ownership]: the intrusive
//! `CBranchingMergingIndividualNodeCandidateLinker*` chains become
//! `CandidateLinkerId` head ids. The linker class itself, plus the edge/node
//! accessors it forwards to (`getNext`/`clearNext`/`append`/
//! `isCandidateBlockableAndCreator`/`getMergingIndividualLink`/
//! `getMergingIndividualNodeCandidate` and the edge `getDependencyTrackPoint` /
//! node `isNominalIndividualNode`), are not yet ported — every such call site is
//! marked `// W2-DEFER[api]` and routed through the stub helpers at the bottom.
//!
//! KONCLUDE-PORT-NOTE[ownership]: the distinct-merged-nodes copy-on-write pair
//! (`mDistinctMergedNodesSet` + `mLastDistinctMergedNodesSet`) is a shared
//! `CPROCESSSET<cint64>*` in C++ (`mLast` aliases another spec's set until a write
//! localises a fresh copy). Rust cannot alias two owned `Option<HashSet>`s, so the
//! port keeps the live contents in `last_distinct_merged_nodes_set` (the read view,
//! == C++ `mLast`) and uses `distinct_merged_nodes_set`'s `Some`/`None` purely as
//! the C++ pointer null-state (the localised-owner marker that gates
//! `create_localized_distinct_merged_node_set`). `init`'s pointer-share becomes a
//! deep clone; this is observationally identical because a shared set is only ever
//! read (any mutator localises first), so its contents are immutable.

#![allow(dead_code)]

use std::collections::HashSet;

use super::super::model::substrate::Cint64;
use super::stubs::CandidateLinkerId;
use super::{ClashDescId, DependencyId, EdgeId, NodeId, TrackPointId};

impl super::satellites::BranchingMergingProcessingRestrictionSpecification {
    /// Port of `initBranchingMergingProcessingRestriction`.
    pub fn init_branching_merging_processing_restriction(
        &mut self,
        prev_rest: Option<&Self>,
    ) -> &mut Self {
        // W2-DEFER[api]: CProcessingRestrictionSpecification::initProcessingRestriction(prev_rest)
        // (the `CProcessingRestrictionSpecification` base init — priority offset /
        // next-restriction chain — is a separate not-yet-ported unit).
        if let Some(prev_rest) = prev_rest {
            self.distinct_merged_nodes_set = None;
            self.last_distinct_merged_nodes_set = None;
            if let Some(prev_last) = &prev_rest.last_distinct_merged_nodes_set {
                self.last_distinct_merged_nodes_set = Some(prev_last.clone());
            }
            self.nominal_merging_nodes_linker = prev_rest.nominal_merging_nodes_linker;
            self.merging_nodes_linker = prev_rest.merging_nodes_linker;
            self.merging_init_nodes_linker = prev_rest.merging_init_nodes_linker;
            self.only_pos_qualify_nodes_linker = prev_rest.only_pos_qualify_nodes_linker;
            self.only_neg_qualify_nodes_linker = prev_rest.only_neg_qualify_nodes_linker;
            self.both_qualify_nodes_linker = prev_rest.both_qualify_nodes_linker;
            self.indi_link = prev_rest.indi_link;
            self.remaining_linker_merging_candidate_indi_node_count =
                prev_rest.remaining_linker_merging_candidate_indi_node_count;
            self.remaining_valid_merging_candidate_indi_node_count =
                prev_rest.remaining_valid_merging_candidate_indi_node_count;
            self.distinct_set_fixed = prev_rest.distinct_set_fixed;
            self.has_merging_init_candidates = prev_rest.has_merging_init_candidates;
            self.remaining_nominal_creation_count = prev_rest.remaining_nominal_creation_count;
            self.added_blockable_pred_merging_node_candidate =
                prev_rest.added_blockable_pred_merging_node_candidate;
            self.added_blockable_pred_dep_track_point =
                prev_rest.added_blockable_pred_dep_track_point;
            self.dependency_track_point = prev_rest.dependency_track_point;
            self.merging_dependency_node = prev_rest.merging_dependency_node;
            self.init_merging_nodes_clashes = prev_rest.init_merging_nodes_clashes;
            self.multiple_init_merging_nodes_clashes = prev_rest.multiple_init_merging_nodes_clashes;
            self.distinct_set_node_relocated = prev_rest.distinct_set_node_relocated;
            self.succ_choice_triggering_installed = prev_rest.succ_choice_triggering_installed;
            self.succ_choice_triggering_installed_count =
                prev_rest.succ_choice_triggering_installed_count;
            self.last_checked_succ_choice_trigger_linker =
                prev_rest.last_checked_succ_choice_trigger_linker.clone();
        } else {
            self.last_checked_succ_choice_trigger_linker.clear();
            self.succ_choice_triggering_installed_count = 0;
            self.succ_choice_triggering_installed = false;
            self.distinct_set_node_relocated = false;
            self.distinct_merged_nodes_set = None;
            self.merging_nodes_linker = super::stubs::CandidateLinkerId::NONE;
            self.nominal_merging_nodes_linker = super::stubs::CandidateLinkerId::NONE;
            self.merging_init_nodes_linker = super::stubs::CandidateLinkerId::NONE;
            self.only_pos_qualify_nodes_linker = super::stubs::CandidateLinkerId::NONE;
            self.only_neg_qualify_nodes_linker = super::stubs::CandidateLinkerId::NONE;
            self.both_qualify_nodes_linker = super::stubs::CandidateLinkerId::NONE;
            self.indi_link = super::EdgeId::NONE;
            self.remaining_linker_merging_candidate_indi_node_count = 0;
            self.remaining_valid_merging_candidate_indi_node_count = 0;
            self.distinct_set_fixed = false;
            self.has_merging_init_candidates = false;
            self.remaining_nominal_creation_count = 0;
            self.added_blockable_pred_merging_node_candidate = false;
            self.added_blockable_pred_dep_track_point = super::TrackPointId::NONE;
            self.dependency_track_point = super::TrackPointId::NONE;
            self.merging_dependency_node = super::DependencyId::NONE;
            self.init_merging_nodes_clashes = super::ClashDescId::NONE;
            self.multiple_init_merging_nodes_clashes = super::ClashDescId::NONE;
        }
        self
    }

    /// Port of `getDistinctMergedNodesSet(bool create)`.
    /// Returns the read view (`mLastDistinctMergedNodesSet`); `None` == `nullptr`.
    pub fn get_distinct_merged_nodes_set(&mut self, create: bool) -> Option<&HashSet<Cint64>> {
        if self.distinct_merged_nodes_set.is_none() && create {
            self.create_localized_distinct_merged_node_set();
        }
        self.last_distinct_merged_nodes_set.as_ref()
    }

    /// Port of `createLocalizedDistinctMergedNodeSet`.
    /// Returns the localised read view (`mLastDistinctMergedNodesSet`).
    pub fn create_localized_distinct_merged_node_set(&mut self) -> Option<&HashSet<Cint64>> {
        if self.distinct_merged_nodes_set.is_none() {
            // C++: allocate a fresh `CPROCESSSET<cint64>` (`mDistinctMergedNodesSet`),
            // copy the shared `mLastDistinctMergedNodesSet` into it, then alias
            // `mLast` onto the new allocation. [ownership]: the live contents stay in
            // `last_distinct_merged_nodes_set` (already an independent deep clone since
            // `init`); `distinct_merged_nodes_set` becomes the non-null owner marker.
            let localized = self
                .last_distinct_merged_nodes_set
                .clone()
                .unwrap_or_default();
            self.last_distinct_merged_nodes_set = Some(localized);
            self.distinct_merged_nodes_set = Some(HashSet::new());
        }
        self.last_distinct_merged_nodes_set.as_ref()
    }

    /// Port of `addDistinctMergedNode`.
    pub fn add_distinct_merged_node(&mut self, merged_indi_node: Cint64) -> &mut Self {
        self.create_localized_distinct_merged_node_set();
        self.last_distinct_merged_nodes_set
            .as_mut()
            .unwrap()
            .insert(merged_indi_node);
        self
    }

    /// Port of `removeDistinctMergedNode`.
    pub fn remove_distinct_merged_node(&mut self, merged_indi_node: Cint64) -> &mut Self {
        self.create_localized_distinct_merged_node_set();
        self.last_distinct_merged_nodes_set
            .as_mut()
            .unwrap()
            .remove(&merged_indi_node);
        self
    }

    /// Port of `getMergingCandidateNodeLinker`.
    pub fn get_merging_candidate_node_linker(&self) -> CandidateLinkerId {
        self.merging_nodes_linker
    }

    /// Port of `takeNextMergingCandidateNodeLinker`.
    pub fn take_next_merging_candidate_node_linker(&mut self) -> CandidateLinkerId {
        let mut tmp_merging_node_linker;
        tmp_merging_node_linker = self.take_next_merging_initialization_candidate_node_linker();
        if tmp_merging_node_linker.is_none() {
            tmp_merging_node_linker = self.nominal_merging_nodes_linker;
            if self.nominal_merging_nodes_linker.is_some() {
                self.remaining_linker_merging_candidate_indi_node_count -= 1;
                self.remaining_valid_merging_candidate_indi_node_count -= 1;
                // W2-DEFER[api]: CBranchingMergingIndividualNodeCandidateLinker::getNext
                self.nominal_merging_nodes_linker =
                    self.cl_get_next(self.nominal_merging_nodes_linker);
            }
            if tmp_merging_node_linker.is_none() {
                tmp_merging_node_linker = self.merging_nodes_linker;
                if self.merging_nodes_linker.is_some() {
                    self.remaining_linker_merging_candidate_indi_node_count -= 1;
                    self.remaining_valid_merging_candidate_indi_node_count -= 1;
                    // W2-DEFER[api]: CBranchingMergingIndividualNodeCandidateLinker::getNext
                    self.merging_nodes_linker = self.cl_get_next(self.merging_nodes_linker);
                }
            }
        }
        tmp_merging_node_linker
    }

    /// Port of `addMergingCandidateNodeLinker`.
    pub fn add_merging_candidate_node_linker(
        &mut self,
        mut linker: CandidateLinkerId,
    ) -> &mut Self {
        while linker.is_some() {
            let linker_it = linker;
            // W2-DEFER[api]: CBranchingMergingIndividualNodeCandidateLinker::getNext
            linker = self.cl_get_next(linker);
            // W2-DEFER[api]: CBranchingMergingIndividualNodeCandidateLinker::clearNext
            self.cl_clear_next(linker_it);
            // W2-DEFER[api]: CBranchingMergingIndividualNodeCandidateLinker::isCandidateBlockableAndCreator
            if !self.added_blockable_pred_merging_node_candidate
                && self.cl_is_candidate_blockable_and_creator(linker_it)
            {
                // W2-DEFER[api]: linkerIt->getMergingIndividualLink()->getDependencyTrackPoint()
                let merging_individual_link = self.cl_get_merging_individual_link(linker_it);
                self.added_blockable_pred_dep_track_point =
                    self.edge_get_dependency_track_point(merging_individual_link);
                self.added_blockable_pred_merging_node_candidate = true;
            }
            self.remaining_linker_merging_candidate_indi_node_count += 1;
            self.remaining_valid_merging_candidate_indi_node_count += 1;
            // W2-DEFER[api]: linkerIt->getMergingIndividualNodeCandidate()->isNominalIndividualNode()
            let merging_candidate = self.cl_get_merging_individual_node_candidate(linker_it);
            if self.node_is_nominal_individual_node(merging_candidate) {
                // W2-DEFER[api]: CBranchingMergingIndividualNodeCandidateLinker::append
                self.nominal_merging_nodes_linker =
                    self.cl_append(linker_it, self.nominal_merging_nodes_linker);
            } else {
                // W2-DEFER[api]: CBranchingMergingIndividualNodeCandidateLinker::append
                self.merging_nodes_linker = self.cl_append(linker_it, self.merging_nodes_linker);
            }
        }
        self
    }

    /// Port of `getMergingInitializationCandidateNodeLinker`.
    pub fn get_merging_initialization_candidate_node_linker(&self) -> CandidateLinkerId {
        self.merging_init_nodes_linker
    }

    /// Port of `takeNextMergingInitializationCandidateNodeLinker`.
    pub fn take_next_merging_initialization_candidate_node_linker(&mut self) -> CandidateLinkerId {
        let tmp_merging_node_linker = self.merging_init_nodes_linker;
        if self.merging_init_nodes_linker.is_some() {
            self.remaining_linker_merging_candidate_indi_node_count -= 1;
            self.remaining_valid_merging_candidate_indi_node_count -= 1;
            // W2-DEFER[api]: CBranchingMergingIndividualNodeCandidateLinker::getNext
            self.merging_init_nodes_linker = self.cl_get_next(self.merging_init_nodes_linker);
        }
        tmp_merging_node_linker
    }

    /// Port of `addMergingInitializationCandidateNodeLinker`.
    pub fn add_merging_initialization_candidate_node_linker(
        &mut self,
        linker: CandidateLinkerId,
    ) -> &mut Self {
        if linker.is_some() {
            self.has_merging_init_candidates = true;
            let mut linker_it = linker;
            while linker_it.is_some() {
                // W2-DEFER[api]: CBranchingMergingIndividualNodeCandidateLinker::isCandidateBlockableAndCreator
                if !self.added_blockable_pred_merging_node_candidate
                    && self.cl_is_candidate_blockable_and_creator(linker_it)
                {
                    // W2-DEFER[api]: linkerIt->getMergingIndividualLink()->getDependencyTrackPoint()
                    let merging_individual_link = self.cl_get_merging_individual_link(linker_it);
                    self.added_blockable_pred_dep_track_point =
                        self.edge_get_dependency_track_point(merging_individual_link);
                    self.added_blockable_pred_merging_node_candidate = true;
                }
                self.remaining_linker_merging_candidate_indi_node_count += 1;
                self.remaining_valid_merging_candidate_indi_node_count += 1;
                // W2-DEFER[api]: CBranchingMergingIndividualNodeCandidateLinker::getNext
                linker_it = self.cl_get_next(linker_it);
            }
            // W2-DEFER[api]: CBranchingMergingIndividualNodeCandidateLinker::append
            self.merging_init_nodes_linker = self.cl_append(linker, self.merging_init_nodes_linker);
        }
        self
    }

    /// Port of `getOnlyPosQualifyCandidateNodeLinker`.
    pub fn get_only_pos_qualify_candidate_node_linker(&self) -> CandidateLinkerId {
        self.only_pos_qualify_nodes_linker
    }

    /// Port of `addOnlyPosQualifyCandidateNodeLinker`.
    pub fn add_only_pos_qualify_candidate_node_linker(
        &mut self,
        linker: CandidateLinkerId,
    ) -> &mut Self {
        if linker.is_some() {
            // W2-DEFER[api]: CBranchingMergingIndividualNodeCandidateLinker::append
            self.only_pos_qualify_nodes_linker =
                self.cl_append(linker, self.only_pos_qualify_nodes_linker);
        }
        self
    }

    /// Port of `clearOnlyPosQualifyCandidateNodeLinker`.
    pub fn clear_only_pos_qualify_candidate_node_linker(&mut self) -> &mut Self {
        self.only_pos_qualify_nodes_linker = super::stubs::CandidateLinkerId::NONE;
        self
    }

    /// Port of `getOnlyNegQualifyCandidateNodeLinker`.
    pub fn get_only_neg_qualify_candidate_node_linker(&self) -> CandidateLinkerId {
        self.only_neg_qualify_nodes_linker
    }

    /// Port of `addOnlyNegQualifyCandidateNodeLinker`.
    pub fn add_only_neg_qualify_candidate_node_linker(
        &mut self,
        linker: CandidateLinkerId,
    ) -> &mut Self {
        if linker.is_some() {
            // W2-DEFER[api]: CBranchingMergingIndividualNodeCandidateLinker::append
            self.only_neg_qualify_nodes_linker =
                self.cl_append(linker, self.only_neg_qualify_nodes_linker);
        }
        self
    }

    /// Port of `clearOnlyNegQualifyCandidateNodeLinker`.
    pub fn clear_only_neg_qualify_candidate_node_linker(&mut self) -> &mut Self {
        self.only_neg_qualify_nodes_linker = super::stubs::CandidateLinkerId::NONE;
        self
    }

    /// Port of `getBothQualifyCandidateNodeLinker`.
    pub fn get_both_qualify_candidate_node_linker(&self) -> CandidateLinkerId {
        self.both_qualify_nodes_linker
    }

    /// Port of `addBothQualifyCandidateNodeLinker`.
    pub fn add_both_qualify_candidate_node_linker(
        &mut self,
        linker: CandidateLinkerId,
    ) -> &mut Self {
        if linker.is_some() {
            // W2-DEFER[api]: CBranchingMergingIndividualNodeCandidateLinker::append
            self.both_qualify_nodes_linker =
                self.cl_append(linker, self.both_qualify_nodes_linker);
        }
        self
    }

    /// Port of `setBothQualifyCandidateNodeLinker`.
    pub fn set_both_qualify_candidate_node_linker(
        &mut self,
        linker: CandidateLinkerId,
    ) -> &mut Self {
        self.both_qualify_nodes_linker = linker;
        self
    }

    /// Port of `getRemainingLinkerMergingCandidateIndividualNodeCount`.
    pub fn get_remaining_linker_merging_candidate_individual_node_count(&self) -> Cint64 {
        self.remaining_linker_merging_candidate_indi_node_count
    }

    /// Port of `setRemainingLinkerMergingCandidateIndividualNodeCount`.
    pub fn set_remaining_linker_merging_candidate_individual_node_count(
        &mut self,
        remaining_canidate_count: Cint64,
    ) -> &mut Self {
        self.remaining_linker_merging_candidate_indi_node_count = remaining_canidate_count;
        self
    }

    /// Port of `getLastIndividualLink`.
    pub fn get_last_individual_link(&self) -> EdgeId {
        self.indi_link
    }

    /// Port of `setLastIndividualLink`.
    pub fn set_last_individual_link(&mut self, indi_link: EdgeId) -> &mut Self {
        self.indi_link = indi_link;
        self
    }

    /// Port of `getRemainingValidMergingCandidateIndividualNodeCount`.
    pub fn get_remaining_valid_merging_candidate_individual_node_count(&self) -> Cint64 {
        self.remaining_valid_merging_candidate_indi_node_count
    }

    /// Port of `setRemainingValidMergingCandidateIndividualNodeCount`.
    pub fn set_remaining_valid_merging_candidate_individual_node_count(
        &mut self,
        remaining_canidate_count: Cint64,
    ) -> &mut Self {
        self.remaining_valid_merging_candidate_indi_node_count = remaining_canidate_count;
        self
    }

    /// Port of `incRemainingValidMergingCandidateIndividualNodeCount`.
    pub fn inc_remaining_valid_merging_candidate_individual_node_count(&mut self) -> &mut Self {
        self.remaining_valid_merging_candidate_indi_node_count += 1;
        self
    }

    /// Port of `hasValidRemainingMergingCandidates`.
    pub fn has_valid_remaining_merging_candidates(&self) -> bool {
        self.remaining_valid_merging_candidate_indi_node_count
            == self.remaining_linker_merging_candidate_indi_node_count
    }

    /// Port of `hasRemainingMergingCandidates`.
    pub fn has_remaining_merging_candidates(&self) -> bool {
        self.nominal_merging_nodes_linker.is_some()
            || self.merging_nodes_linker.is_some()
            || self.merging_init_nodes_linker.is_some()
    }

    /// Port of `hasMergingInitializationCandidates`.
    pub fn has_merging_initialization_candidates(&self) -> bool {
        self.has_merging_init_candidates
    }

    /// Port of `hasRemainingMergingInitializationCandidates`.
    pub fn has_remaining_merging_initialization_candidates(&self) -> bool {
        self.merging_init_nodes_linker.is_some()
    }

    /// Port of `decRemainingNominalCreationCount`.
    pub fn dec_remaining_nominal_creation_count(&mut self, dec_count: Cint64) -> &mut Self {
        self.remaining_nominal_creation_count -= dec_count;
        self
    }

    /// Port of `hasAddedBlockablePredecessorMergingNodeCandidate`.
    pub fn has_added_blockable_predecessor_merging_node_candidate(&self) -> bool {
        self.added_blockable_pred_merging_node_candidate
    }

    /// Port of `getAddedBlockablePredecessorDependencyTrackPoint`.
    pub fn get_added_blockable_predecessor_dependency_track_point(&self) -> TrackPointId {
        self.added_blockable_pred_dep_track_point
    }

    /// Port of `initMergingDependencyNode`.
    pub fn init_merging_dependency_node(&mut self, dep_node: DependencyId) -> &mut Self {
        self.merging_dependency_node = dep_node;
        self
    }

    /// Port of `getMergingDependencyNode`.
    pub fn get_merging_dependency_node(&self) -> DependencyId {
        self.merging_dependency_node
    }

    /// Port of `setMergingNodesInitializationClashesDescriptors`.
    pub fn set_merging_nodes_initialization_clashes_descriptors(
        &mut self,
        clashes: ClashDescId,
    ) -> &mut Self {
        self.init_merging_nodes_clashes = clashes;
        self
    }

    /// Port of `getMergingNodesInitializationClashesDescriptors`.
    pub fn get_merging_nodes_initialization_clashes_descriptors(&self) -> ClashDescId {
        self.init_merging_nodes_clashes
    }

    /// Port of `setMultipleMergingNodesInitializationClashesDescriptors`.
    pub fn set_multiple_merging_nodes_initialization_clashes_descriptors(
        &mut self,
        clashes: ClashDescId,
    ) -> &mut Self {
        self.multiple_init_merging_nodes_clashes = clashes;
        self
    }

    /// Port of `getMultipleMergingNodesInitializationClashesDescriptors`.
    pub fn get_multiple_merging_nodes_initialization_clashes_descriptors(&self) -> ClashDescId {
        self.multiple_init_merging_nodes_clashes
    }

    /// Port of `isDistinctSetNodeRelocated`.
    pub fn is_distinct_set_node_relocated(&self) -> bool {
        self.distinct_set_node_relocated
    }

    /// Port of `setDistinctSetNodeRelocated`.
    pub fn set_distinct_set_node_relocated(
        &mut self,
        distinct_set_node_relocated: bool,
    ) -> &mut Self {
        self.distinct_set_node_relocated = distinct_set_node_relocated;
        self
    }

    /// Port of `hasSuccessorChoiceTriggeringInstalled`.
    pub fn has_successor_choice_triggering_installed(&self) -> bool {
        self.succ_choice_triggering_installed
    }

    /// Port of `setSuccessorChoiceTriggeringInstalled`.
    pub fn set_successor_choice_triggering_installed(
        &mut self,
        succ_choice_triggering_installed: bool,
    ) -> &mut Self {
        self.succ_choice_triggering_installed = succ_choice_triggering_installed;
        self
    }

    /// Port of `getSuccessorChoiceTriggeringInstalledCount`.
    pub fn get_successor_choice_triggering_installed_count(&self) -> Cint64 {
        self.succ_choice_triggering_installed_count
    }

    /// Port of `incSuccessorChoiceTriggeringInstalledCount`.
    pub fn inc_successor_choice_triggering_installed_count(&mut self, count: Cint64) -> &mut Self {
        self.succ_choice_triggering_installed_count += count;
        self
    }

    /// Port of `decSuccessorChoiceTriggeringInstalledCount`.
    pub fn dec_successor_choice_triggering_installed_count(&mut self, count: Cint64) -> &mut Self {
        self.succ_choice_triggering_installed_count -= count;
        self
    }

    /// Port of `getLastCheckedSuccessorChoiceTriggerLinker`.
    /// KONCLUDE-PORT-NOTE[ownership]: `CXLinker<CIndividualLinkEdge*>*` → `&[EdgeId]`.
    pub fn get_last_checked_successor_choice_trigger_linker(&self) -> &[EdgeId] {
        &self.last_checked_succ_choice_trigger_linker
    }

    /// Port of `setLastCheckedSuccessorChoiceTriggerLinker`.
    pub fn set_last_checked_successor_choice_trigger_linker(
        &mut self,
        indi_linker: Vec<EdgeId>,
    ) -> &mut Self {
        self.last_checked_succ_choice_trigger_linker = indi_linker;
        self
    }

    // =======================================================================
    // W2-DEFER[api] stub helpers for the not-yet-ported candidate-linker class
    // (`CBranchingMergingIndividualNodeCandidateLinker`) and the edge/node
    // accessors it forwards to. These reproduce the exact call sites above; the
    // real bodies land when the candidate-linker arena + edge/node access are
    // threaded through a process context (units SD-1 / SD-3 + the linker unit).
    // =======================================================================

    /// W2-DEFER[api]: `CBranchingMergingIndividualNodeCandidateLinker::getNext()`.
    fn cl_get_next(&self, _linker: CandidateLinkerId) -> CandidateLinkerId {
        todo!("W2-DEFER[api]: candidate-linker getNext (arena not yet ported)")
    }

    /// W2-DEFER[api]: `CBranchingMergingIndividualNodeCandidateLinker::clearNext()`.
    fn cl_clear_next(&mut self, _linker: CandidateLinkerId) {
        todo!("W2-DEFER[api]: candidate-linker clearNext (arena not yet ported)")
    }

    /// W2-DEFER[api]: `CBranchingMergingIndividualNodeCandidateLinker::append(list)`
    /// — appends `list` after `linker` and returns the new head (`linker`).
    fn cl_append(
        &mut self,
        _linker: CandidateLinkerId,
        _list: CandidateLinkerId,
    ) -> CandidateLinkerId {
        todo!("W2-DEFER[api]: candidate-linker append (arena not yet ported)")
    }

    /// W2-DEFER[api]: `CBranchingMergingIndividualNodeCandidateLinker::isCandidateBlockableAndCreator()`.
    fn cl_is_candidate_blockable_and_creator(&self, _linker: CandidateLinkerId) -> bool {
        todo!("W2-DEFER[api]: candidate-linker isCandidateBlockableAndCreator")
    }

    /// W2-DEFER[api]: `CBranchingMergingIndividualNodeCandidateLinker::getMergingIndividualLink()`.
    fn cl_get_merging_individual_link(&self, _linker: CandidateLinkerId) -> EdgeId {
        todo!("W2-DEFER[api]: candidate-linker getMergingIndividualLink")
    }

    /// W2-DEFER[api]: `CBranchingMergingIndividualNodeCandidateLinker::getMergingIndividualNodeCandidate()`.
    fn cl_get_merging_individual_node_candidate(&self, _linker: CandidateLinkerId) -> NodeId {
        todo!("W2-DEFER[api]: candidate-linker getMergingIndividualNodeCandidate")
    }

    /// W2-DEFER[api]: `CIndividualLinkEdge::getDependencyTrackPoint()`.
    fn edge_get_dependency_track_point(&self, _edge: EdgeId) -> TrackPointId {
        todo!("W2-DEFER[api]: edge getDependencyTrackPoint (edge arena not threaded here)")
    }

    /// W2-DEFER[api]: `CIndividualProcessNode::isNominalIndividualNode()`.
    fn node_is_nominal_individual_node(&self, _node: NodeId) -> bool {
        todo!("W2-DEFER[api]: node isNominalIndividualNode (node arena not threaded here)")
    }
}
