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
//! `CandidateLinkerId` head ids. The linker class is arena-owned by
//! `ProcessContext`, so the candidate-chain methods take the ambient context
//! when they need to follow or mutate `next` links, read edge dependencies, or
//! distinguish nominal/blockable candidate nodes.
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
use super::context::ProcessContext;
use super::stubs::CandidateLinkerId;
use super::{ClashDescId, DependencyId, EdgeId, NodeId, TrackPointId};

impl super::satellites::BranchingMergingProcessingRestrictionSpecification {
    /// Port of `initBranchingMergingProcessingRestriction`.
    pub fn init_branching_merging_processing_restriction(
        &mut self,
        prev_rest: Option<&Self>,
    ) -> &mut Self {
        self.init_processing_restriction(prev_rest);
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
            self.multiple_init_merging_nodes_clashes =
                prev_rest.multiple_init_merging_nodes_clashes;
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
    pub fn take_next_merging_candidate_node_linker(
        &mut self,
        process_context: &ProcessContext,
    ) -> CandidateLinkerId {
        let mut tmp_merging_node_linker;
        tmp_merging_node_linker =
            self.take_next_merging_initialization_candidate_node_linker(process_context);
        if tmp_merging_node_linker.is_none() {
            tmp_merging_node_linker = self.nominal_merging_nodes_linker;
            if self.nominal_merging_nodes_linker.is_some() {
                self.remaining_linker_merging_candidate_indi_node_count -= 1;
                self.remaining_valid_merging_candidate_indi_node_count -= 1;
                self.nominal_merging_nodes_linker =
                    Self::cl_get_next(process_context, self.nominal_merging_nodes_linker);
            }
            if tmp_merging_node_linker.is_none() {
                tmp_merging_node_linker = self.merging_nodes_linker;
                if self.merging_nodes_linker.is_some() {
                    self.remaining_linker_merging_candidate_indi_node_count -= 1;
                    self.remaining_valid_merging_candidate_indi_node_count -= 1;
                    self.merging_nodes_linker =
                        Self::cl_get_next(process_context, self.merging_nodes_linker);
                }
            }
        }
        tmp_merging_node_linker
    }

    /// Port of `addMergingCandidateNodeLinker`.
    pub fn add_merging_candidate_node_linker(
        &mut self,
        mut linker: CandidateLinkerId,
        process_context: &mut ProcessContext,
    ) -> &mut Self {
        while linker.is_some() {
            let linker_it = linker;
            linker = Self::cl_get_next(process_context, linker);
            Self::cl_clear_next(process_context, linker_it);
            if !self.added_blockable_pred_merging_node_candidate
                && Self::cl_is_candidate_blockable_and_creator(process_context, linker_it)
            {
                let merging_individual_link =
                    Self::cl_get_merging_individual_link(process_context, linker_it);
                self.added_blockable_pred_dep_track_point =
                    Self::edge_get_dependency_track_point(process_context, merging_individual_link);
                self.added_blockable_pred_merging_node_candidate = true;
            }
            self.remaining_linker_merging_candidate_indi_node_count += 1;
            self.remaining_valid_merging_candidate_indi_node_count += 1;
            let merging_candidate =
                Self::cl_get_merging_individual_node_candidate(process_context, linker_it);
            if Self::node_is_nominal_individual_node(process_context, merging_candidate) {
                self.nominal_merging_nodes_linker = Self::cl_append(
                    process_context,
                    linker_it,
                    self.nominal_merging_nodes_linker,
                );
            } else {
                self.merging_nodes_linker =
                    Self::cl_append(process_context, linker_it, self.merging_nodes_linker);
            }
        }
        self
    }

    /// Port of `getMergingInitializationCandidateNodeLinker`.
    pub fn get_merging_initialization_candidate_node_linker(&self) -> CandidateLinkerId {
        self.merging_init_nodes_linker
    }

    /// Port of `takeNextMergingInitializationCandidateNodeLinker`.
    pub fn take_next_merging_initialization_candidate_node_linker(
        &mut self,
        process_context: &ProcessContext,
    ) -> CandidateLinkerId {
        let tmp_merging_node_linker = self.merging_init_nodes_linker;
        if self.merging_init_nodes_linker.is_some() {
            self.remaining_linker_merging_candidate_indi_node_count -= 1;
            self.remaining_valid_merging_candidate_indi_node_count -= 1;
            self.merging_init_nodes_linker =
                Self::cl_get_next(process_context, self.merging_init_nodes_linker);
        }
        tmp_merging_node_linker
    }

    /// Port of `addMergingInitializationCandidateNodeLinker`.
    pub fn add_merging_initialization_candidate_node_linker(
        &mut self,
        linker: CandidateLinkerId,
        process_context: &mut ProcessContext,
    ) -> &mut Self {
        if linker.is_some() {
            self.has_merging_init_candidates = true;
            let mut linker_it = linker;
            while linker_it.is_some() {
                if !self.added_blockable_pred_merging_node_candidate
                    && Self::cl_is_candidate_blockable_and_creator(process_context, linker_it)
                {
                    let merging_individual_link =
                        Self::cl_get_merging_individual_link(process_context, linker_it);
                    self.added_blockable_pred_dep_track_point =
                        Self::edge_get_dependency_track_point(
                            process_context,
                            merging_individual_link,
                        );
                    self.added_blockable_pred_merging_node_candidate = true;
                }
                self.remaining_linker_merging_candidate_indi_node_count += 1;
                self.remaining_valid_merging_candidate_indi_node_count += 1;
                linker_it = Self::cl_get_next(process_context, linker_it);
            }
            self.merging_init_nodes_linker =
                Self::cl_append(process_context, linker, self.merging_init_nodes_linker);
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
        process_context: &mut ProcessContext,
    ) -> &mut Self {
        if linker.is_some() {
            self.only_pos_qualify_nodes_linker =
                Self::cl_append(process_context, linker, self.only_pos_qualify_nodes_linker);
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
        process_context: &mut ProcessContext,
    ) -> &mut Self {
        if linker.is_some() {
            self.only_neg_qualify_nodes_linker =
                Self::cl_append(process_context, linker, self.only_neg_qualify_nodes_linker);
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
        process_context: &mut ProcessContext,
    ) -> &mut Self {
        if linker.is_some() {
            self.both_qualify_nodes_linker =
                Self::cl_append(process_context, linker, self.both_qualify_nodes_linker);
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

    fn cl_get_next(
        process_context: &ProcessContext,
        linker: CandidateLinkerId,
    ) -> CandidateLinkerId {
        process_context
            .branching_merging_candidate_linker(linker)
            .get_next()
    }

    fn cl_clear_next(process_context: &mut ProcessContext, linker: CandidateLinkerId) {
        process_context
            .branching_merging_candidate_linker_mut(linker)
            .clear_next();
    }

    fn cl_append(
        process_context: &mut ProcessContext,
        linker: CandidateLinkerId,
        list: CandidateLinkerId,
    ) -> CandidateLinkerId {
        if linker.is_none() {
            return list;
        }
        let mut last = linker;
        loop {
            let next = process_context
                .branching_merging_candidate_linker(last)
                .get_next();
            if next.is_none() {
                break;
            }
            last = next;
        }
        process_context
            .branching_merging_candidate_linker_mut(last)
            .next = list;
        linker
    }

    fn cl_is_candidate_blockable_and_creator(
        process_context: &ProcessContext,
        linker: CandidateLinkerId,
    ) -> bool {
        let linker = process_context.branching_merging_candidate_linker(linker);
        let merging_candidate = linker.get_merging_individual_node_candidate();
        let merging_link = linker.get_merging_individual_link();
        merging_candidate.is_some()
            && merging_link.is_some()
            && process_context
                .node(merging_candidate)
                .is_blockable_individual()
            && process_context.edge(merging_link).get_creator_individual() == merging_candidate
    }

    fn cl_get_merging_individual_link(
        process_context: &ProcessContext,
        linker: CandidateLinkerId,
    ) -> EdgeId {
        process_context
            .branching_merging_candidate_linker(linker)
            .get_merging_individual_link()
    }

    fn cl_get_merging_individual_node_candidate(
        process_context: &ProcessContext,
        linker: CandidateLinkerId,
    ) -> NodeId {
        process_context
            .branching_merging_candidate_linker(linker)
            .get_merging_individual_node_candidate()
    }

    fn edge_get_dependency_track_point(
        process_context: &ProcessContext,
        edge: EdgeId,
    ) -> TrackPointId {
        process_context.edge(edge).get_dependency_track_point()
    }

    fn node_is_nominal_individual_node(process_context: &ProcessContext, node: NodeId) -> bool {
        process_context.node(node).is_nominal_individual_node()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::konclude_ht::model::RoleId;
    use crate::konclude_ht::process::edge::IndividualLinkEdge;
    use crate::konclude_ht::process::node::{IndividualProcessNode, IndividualType};
    use crate::konclude_ht::process::satellites::BranchingMergingProcessingRestrictionSpecification;
    use crate::konclude_ht::process::stubs::{
        BranchingMergingIndividualNodeCandidateLinker, ProcessContextId,
    };

    fn alloc_node(process_context: &mut ProcessContext, individual_type: IndividualType) -> NodeId {
        let mut node = IndividualProcessNode::new(ProcessContextId::NONE);
        node.set_individual_type(individual_type);
        process_context.alloc_node(node)
    }

    fn alloc_edge(
        process_context: &mut ProcessContext,
        creator: NodeId,
        dep_track_point: TrackPointId,
    ) -> EdgeId {
        let mut edge = IndividualLinkEdge::new();
        edge.init_individual_link_edge(
            creator,
            creator,
            NodeId::NONE,
            RoleId::NONE,
            dep_track_point,
        );
        process_context.alloc_edge(edge)
    }

    fn alloc_candidate(
        process_context: &mut ProcessContext,
        node: NodeId,
        edge: EdgeId,
    ) -> CandidateLinkerId {
        let mut linker = BranchingMergingIndividualNodeCandidateLinker::new();
        linker.init_branching_merging_individual_node_candidate(node, edge);
        process_context.alloc_branching_merging_candidate_linker(linker)
    }

    #[test]
    fn bm_candidate_linkers_split_nominal_and_take_in_konclude_order() {
        let mut ctx = ProcessContext::new();
        let blockable_node = alloc_node(&mut ctx, IndividualType::Blockable);
        let nominal_node = alloc_node(&mut ctx, IndividualType::Nominal);
        let init_node = alloc_node(&mut ctx, IndividualType::Blockable);
        let dep = TrackPointId::new(77);
        let blockable_edge = alloc_edge(&mut ctx, blockable_node, dep);
        let nominal_edge = alloc_edge(&mut ctx, nominal_node, TrackPointId::new(78));
        let init_edge = alloc_edge(&mut ctx, init_node, TrackPointId::new(79));

        let blockable_candidate = alloc_candidate(&mut ctx, blockable_node, blockable_edge);
        let nominal_candidate = alloc_candidate(&mut ctx, nominal_node, nominal_edge);
        ctx.branching_merging_candidate_linker_mut(blockable_candidate)
            .next = nominal_candidate;
        let init_candidate = alloc_candidate(&mut ctx, init_node, init_edge);

        let mut rest = BranchingMergingProcessingRestrictionSpecification::default();
        rest.add_merging_candidate_node_linker(blockable_candidate, &mut ctx);
        rest.add_merging_initialization_candidate_node_linker(init_candidate, &mut ctx);

        assert_eq!(
            rest.get_merging_candidate_node_linker(),
            blockable_candidate
        );
        assert_eq!(
            rest.get_merging_initialization_candidate_node_linker(),
            init_candidate
        );
        assert_eq!(rest.nominal_merging_nodes_linker, nominal_candidate);
        assert!(rest.has_added_blockable_predecessor_merging_node_candidate());
        assert_eq!(
            rest.get_added_blockable_predecessor_dependency_track_point(),
            dep
        );
        assert_eq!(
            rest.get_remaining_linker_merging_candidate_individual_node_count(),
            3
        );

        assert_eq!(
            rest.take_next_merging_candidate_node_linker(&ctx),
            init_candidate
        );
        assert_eq!(
            rest.take_next_merging_candidate_node_linker(&ctx),
            nominal_candidate
        );
        assert_eq!(
            rest.take_next_merging_candidate_node_linker(&ctx),
            blockable_candidate
        );
        assert_eq!(
            rest.take_next_merging_candidate_node_linker(&ctx),
            CandidateLinkerId::NONE
        );
        assert_eq!(
            rest.get_remaining_linker_merging_candidate_individual_node_count(),
            0
        );
        assert_eq!(
            rest.get_remaining_valid_merging_candidate_individual_node_count(),
            0
        );
    }

    #[test]
    fn bm_qualify_candidate_linkers_append_chain_to_existing_head() {
        let mut ctx = ProcessContext::new();
        let node = alloc_node(&mut ctx, IndividualType::Blockable);
        let edge = alloc_edge(&mut ctx, node, TrackPointId::new(81));
        let first = alloc_candidate(&mut ctx, node, edge);
        let second = alloc_candidate(&mut ctx, node, edge);
        let old_head = alloc_candidate(&mut ctx, node, edge);
        ctx.branching_merging_candidate_linker_mut(first).next = second;

        let mut rest = BranchingMergingProcessingRestrictionSpecification::default();
        rest.set_both_qualify_candidate_node_linker(old_head);
        rest.add_both_qualify_candidate_node_linker(first, &mut ctx);

        assert_eq!(rest.get_both_qualify_candidate_node_linker(), first);
        assert_eq!(
            ctx.branching_merging_candidate_linker(first).get_next(),
            second
        );
        assert_eq!(
            ctx.branching_merging_candidate_linker(second).get_next(),
            old_head
        );
    }

    #[test]
    fn bm_init_processing_restriction_copies_and_resets_priority_offset() {
        let mut prev = BranchingMergingProcessingRestrictionSpecification::default();
        prev.set_priority_offset(12.5);
        prev.next_restriction = crate::konclude_ht::process::RestrictionSpecId::new(99);
        prev.remaining_nominal_creation_count = 3;

        let mut copied = BranchingMergingProcessingRestrictionSpecification::default();
        copied.next_restriction = crate::konclude_ht::process::RestrictionSpecId::new(7);
        copied.init_branching_merging_processing_restriction(Some(&prev));
        assert_eq!(copied.get_priority_offset(), 12.5);
        assert_eq!(
            copied.get_next_processing_restriction_specification(),
            crate::konclude_ht::process::RestrictionSpecId::new(7)
        );
        assert_eq!(copied.remaining_nominal_creation_count, 3);

        copied.set_priority_offset(4.0);
        copied.init_branching_merging_processing_restriction(None);
        assert_eq!(copied.get_priority_offset(), 0.0);
        assert_eq!(
            copied.get_next_processing_restriction_specification(),
            crate::konclude_ht::process::RestrictionSpecId::new(7)
        );
    }
}
