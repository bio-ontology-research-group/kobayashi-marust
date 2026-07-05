//! `completion::u30` — Clash processing family, batch (port unit #30 of 36).
//!
//! Faithful port of the 18 methods the manifest (`01-completion-methods.md`,
//! "Unit 30") groups under clash-descriptor construction, tracked-clash
//! descriptor handling and the label-concept clash tests of Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`.
//! cpp source line ranges (1-based) are noted on each item.
//!
//! Methods (cpp order):
//!   * `createClashedIndividualNodeDescriptor`                       [4395–4405]
//!   * `generateDebugTrackedClashedDescriptorSummaryString`          [6569–6585]
//!   * `generateDebugTrackedClashedDescriptorString`                 [6588–6718]
//!   * `getFreeTrackedClashedDescriptor`                             [6952–6959]
//!   * `markRelevanceForTrackedClashedDescriptors`                   [7352–7357]
//!   * `addIndiNodeSignatureOfUnsatisfiableClashedDescriptors`       [7545–7552]
//!   * `isClashedDescriptorSortedBefore`                             [7554–7556]
//!   * `getSortedClashedDescriptors`                                 [7559–7583]
//!   * `writeUnsatisfiableClashedDescriptors`                        [7586–7592]
//!   * `getCollectedFilteredClashedDescriptorsFromBranch`           [7595–7652]
//!   * `createTrackedClashesDescriptors`                            [7921–7935]
//!   * `createTrackedClashesDescriptor`                             [7939–7973]
//!   * `createClashedConceptDescriptor`                            [16717–16720]
//!   * `createClashedIndividualLinkDescriptor`                     [16722–16725]
//!   * `createClashedIndividualDistinctDescriptor`                 [16727–16730]
//!   * `createClashedNegationDisjointDescriptor`                   [16732–16735]
//!   * `isLabelConceptClashSet` (label-set / label-set)            [17323–17391]
//!   * `isLabelConceptClashSet` (node / node, builds clashes)      [20867–20932]
//!
//! KONCLUDE-PORT-NOTE[ownership]: each method is a member of
//! `CCalculationTableauCompletionTaskHandleAlgorithm`, so it becomes `&mut self`
//! plus the threaded per-thread context `calc_alg_context: &mut
//! CalculationAlgorithmContextBase`. C++ `CIndividualProcessNode*&` in/out
//! pointer-references become `&mut NodeId`; a plain value `CIndividualProcessNode*`
//! becomes `NodeId`; `CConceptDescriptor*` → `ConDescId`; `CClashedDependencyDescriptor*`
//! → `ClashDescId`; `CDependencyTrackPoint*` → `TrackPointId`; the edge value
//! params → `EdgeId` / `DistinctEdgeId` / `DisjointEdgeId`; the
//! `CNonDeterministicDependencyNode*` branch node → `DependencyId`. The per-test
//! arenas are reached through the context (`calc_alg_context.process_context()` /
//! `_mut()`), the databox as `calc_alg_context.processing_data_box{,_mut}()`.
//!
//! Deferral landscape. Two subsystems gate the bulk of this unit:
//!   * `CTrackedClashedDescriptor`, `CTrackedClashedDescriptorHasher`, and the
//!     stack-local `CTrackedClashedDependencyLine` substrate are now ported as the
//!     folded tracked clash descriptor payload plus Rust stack containers. The
//!     adjacent consumers whose bodies depend on the still-unported backtracking,
//!     cache-writer, branch-filtered collection, and tracking-line debug flows
//!     remain `// PORT-PENDING` with faithful C++ transcriptions.
//!   * the `CClashedDependencyFactory` (`used_clash_descriptor_factory`, a zero-size
//!     `Id` stub) has been resolved for the concrete non-datatype folded
//!     descriptor payloads; the remaining datatype exclusion subtype is separate
//!     substrate work.
//!
//! Fully ported here (concrete arena resolution): the `createClashedIndividualNodeDescriptor`
//! adding-sorted concept-descriptor walk (only the LS-1-deferred chain-head getter
//! stays a stub), the four non-datatype `createClashed*Descriptor` factory wrappers,
//! the null-handler guard of `writeUnsatisfiableClashedDescriptors`, and — mirroring the
//! u16/u34 label-set comparison ports — the count/threshold branch selection plus
//! the node-version label-set fetch+swap of the two `isLabelConceptClashSet`
//! methods (the per-concept iterator walks are `CReapplyConceptLabelSetIterator`,
//! an unported LS-1 stub, so they stay `W6-DEFER[api]` with logic in-comment).
//! Logic is documented, never silently dropped.

#![allow(dead_code)]
#![allow(unused_variables)]

use std::collections::HashSet;
use std::hash::{Hash, Hasher};

use super::super::model::op::CCNOMINAL;
use super::super::model::substrate::{Cint64, Id, INVALID};
use super::super::process::varbind::VarBindingPathId;
use super::super::process::{
    ClashDescId, ConDescId, DependencyId, DisjointEdgeId, DistinctEdgeId, EdgeId, LabelSetId,
    NodeId, TrackPointId,
};
use super::context::CalculationAlgorithmContextBase;

#[derive(Copy, Clone, Debug, Eq)]
pub struct TrackedClashedDescriptorHasher {
    tracked_clashed_des: ClashDescId,
    hash_value: Cint64,
    individual_id: Cint64,
    concept: super::super::model::ConceptId,
    concept_negated: bool,
    dep_track_point: TrackPointId,
    var_bind_path: VarBindingPathId,
}

impl TrackedClashedDescriptorHasher {
    /// Port of `CTrackedClashedDescriptorHasher::CTrackedClashedDescriptorHasher`.
    pub fn new(
        tracked_clashed_descriptor: ClashDescId,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> Self {
        let mut hasher = TrackedClashedDescriptorHasher {
            tracked_clashed_des: tracked_clashed_descriptor,
            hash_value: 0,
            individual_id: INVALID,
            concept: super::super::model::ConceptId::NONE,
            concept_negated: false,
            dep_track_point: TrackPointId::NONE,
            var_bind_path: VarBindingPathId::NONE,
        };
        hasher.calculate(calc_alg_context);
        hasher
    }

    /// Port of `CTrackedClashedDescriptorHasher::getDescriptorHashValue`.
    pub fn get_descriptor_hash_value(&self) -> Cint64 {
        self.hash_value
    }

    /// Port of `CTrackedClashedDescriptorHasher::calculateDescriptorHashValue`.
    fn calculate(&mut self, calc_alg_context: &CalculationAlgorithmContextBase) {
        let ctx = calc_alg_context.process_context();
        let des = ctx.clash_desc(self.tracked_clashed_des);
        self.individual_id = des.get_appropriated_individual_id();
        self.dep_track_point = des.get_dependency_track_point();
        self.var_bind_path = des.get_variable_binding_path();

        let mut hash_value = 0;
        hash_value += self.individual_id;
        let con_des = des.get_concept_descriptor();
        if con_des.is_some() {
            let con_des_ref = ctx.con_desc(con_des);
            self.concept = con_des_ref.get_concept();
            self.concept_negated = con_des_ref.is_negated();
            hash_value += self.concept.raw;
            if self.concept_negated {
                hash_value = (hash_value << 1) + 13;
            }
        }
        hash_value += self.dep_track_point.raw;
        hash_value += self.var_bind_path.raw;
        self.hash_value = hash_value;
    }
}

impl PartialEq for TrackedClashedDescriptorHasher {
    fn eq(&self, other: &Self) -> bool {
        self.hash_value == other.hash_value
            && self.individual_id == other.individual_id
            && self.concept == other.concept
            && self.concept_negated == other.concept_negated
            && self.dep_track_point == other.dep_track_point
            && self.var_bind_path == other.var_bind_path
    }
}

impl Hash for TrackedClashedDescriptorHasher {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.hash_value.hash(state);
    }
}

/// Port of `CTrackedClashedDependencyLine`.
pub struct TrackedClashedDependencyLine {
    exact_individual_tracking: bool,
    individual_track_level: Cint64,
    branching_level: Cint64,
    independent_tracked_clashes: ClashDescId,
    level_tracked_clashes: ClashDescId,
    level_tracked_branching_clashes: ClashDescId,
    prev_levels_tracked_clashes: ClashDescId,
    prev_levels_tracked_non_det_clashes: ClashDescId,
    prev_levels_tracked_non_det_branching_clashes: ClashDescId,
    free_tracked_clashed_descriptors: ClashDescId,
    clashed_set: HashSet<TrackedClashedDescriptorHasher>,
    involved_individual_set: Option<HashSet<Cint64>>,
}

impl Default for TrackedClashedDependencyLine {
    fn default() -> Self {
        TrackedClashedDependencyLine {
            exact_individual_tracking: false,
            individual_track_level: INVALID,
            branching_level: INVALID,
            independent_tracked_clashes: ClashDescId::NONE,
            level_tracked_clashes: ClashDescId::NONE,
            level_tracked_branching_clashes: ClashDescId::NONE,
            prev_levels_tracked_clashes: ClashDescId::NONE,
            prev_levels_tracked_non_det_clashes: ClashDescId::NONE,
            prev_levels_tracked_non_det_branching_clashes: ClashDescId::NONE,
            free_tracked_clashed_descriptors: ClashDescId::NONE,
            clashed_set: HashSet::new(),
            involved_individual_set: None,
        }
    }
}

impl TrackedClashedDependencyLine {
    /// Port of `CTrackedClashedDependencyLine::CTrackedClashedDependencyLine`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `CTrackedClashedDependencyLine::initTrackedClashedDependencyLine`.
    pub fn init_tracked_clashed_dependency_line(
        &mut self,
        exact_indi_node_tracking: bool,
        individual_node_track_level: Cint64,
        branching_level: Cint64,
    ) -> &mut Self {
        self.exact_individual_tracking = exact_indi_node_tracking;
        self.individual_track_level = individual_node_track_level;
        self.branching_level = branching_level;
        self.level_tracked_clashes = ClashDescId::NONE;
        self.level_tracked_branching_clashes = ClashDescId::NONE;
        self.prev_levels_tracked_clashes = ClashDescId::NONE;
        self.prev_levels_tracked_non_det_clashes = ClashDescId::NONE;
        self.prev_levels_tracked_non_det_branching_clashes = ClashDescId::NONE;
        self.independent_tracked_clashes = ClashDescId::NONE;
        self
    }

    /// Port of `CTrackedClashedDependencyLine::sortInTrackedClashedDescriptors`.
    pub fn sort_in_tracked_clashed_descriptors(
        &mut self,
        mut clashed_des: ClashDescId,
        force_insertion: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> &mut Self {
        while clashed_des.is_some() {
            let clashed_des_tmp = clashed_des;
            clashed_des = calc_alg_context
                .process_context()
                .clash_desc(clashed_des_tmp)
                .get_next_descriptor();
            calc_alg_context
                .process_context_mut()
                .clash_desc_mut(clashed_des_tmp)
                .set_next(ClashDescId::NONE);
            let des_hasher = TrackedClashedDescriptorHasher::new(clashed_des_tmp, calc_alg_context);
            let mut clash_des_insertion = force_insertion;
            if !self.clashed_set.contains(&des_hasher) {
                self.clashed_set.insert(des_hasher);
                clash_des_insertion = true;
            }
            if clash_des_insertion {
                if calc_alg_context
                    .process_context()
                    .clash_desc(clashed_des_tmp)
                    .is_pointing_to_independent_dependency_node()
                {
                    self.independent_tracked_clashes = self.prepend(
                        clashed_des_tmp,
                        self.independent_tracked_clashes,
                        calc_alg_context,
                    );
                } else if calc_alg_context
                    .process_context()
                    .clash_desc(clashed_des_tmp)
                    .get_appropriated_individual_level()
                    > self.individual_track_level
                {
                    if calc_alg_context
                        .process_context()
                        .clash_desc(clashed_des_tmp)
                        .is_pointing_to_non_deterministic_dependency_node()
                    {
                        if calc_alg_context
                            .process_context()
                            .clash_desc(clashed_des_tmp)
                            .get_branching_level_tag()
                            == self.branching_level
                        {
                            self.prev_levels_tracked_non_det_branching_clashes = self.prepend(
                                clashed_des_tmp,
                                self.prev_levels_tracked_non_det_branching_clashes,
                                calc_alg_context,
                            );
                        } else {
                            self.prev_levels_tracked_non_det_clashes = self.prepend(
                                clashed_des_tmp,
                                self.prev_levels_tracked_non_det_clashes,
                                calc_alg_context,
                            );
                        }
                    } else {
                        self.prev_levels_tracked_clashes = self.prepend(
                            clashed_des_tmp,
                            self.prev_levels_tracked_clashes,
                            calc_alg_context,
                        );
                    }
                } else if calc_alg_context
                    .process_context()
                    .clash_desc(clashed_des_tmp)
                    .get_branching_level_tag()
                    == self.branching_level
                {
                    self.level_tracked_branching_clashes = self.prepend(
                        clashed_des_tmp,
                        self.level_tracked_branching_clashes,
                        calc_alg_context,
                    );
                } else {
                    self.level_tracked_clashes = self.prepend(
                        clashed_des_tmp,
                        self.level_tracked_clashes,
                        calc_alg_context,
                    );
                }
            } else {
                self.add_free_tracked_clashed_descriptor(clashed_des_tmp, calc_alg_context);
            }
        }
        self
    }

    /// Port of `CTrackedClashedDependencyLine::moveToNextIndividualNodeLevel`.
    pub fn move_to_next_individual_node_level(
        &mut self,
        new_level: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> &mut Self {
        self.individual_track_level = new_level;
        let level_tracked_clashes = self.level_tracked_clashes;
        self.level_tracked_clashes = ClashDescId::NONE;
        self.sort_in_tracked_clashed_descriptors(level_tracked_clashes, true, calc_alg_context);

        let level_tracked_branching_clashes = self.level_tracked_branching_clashes;
        self.level_tracked_branching_clashes = ClashDescId::NONE;
        self.sort_in_tracked_clashed_descriptors(
            level_tracked_branching_clashes,
            true,
            calc_alg_context,
        );
        self
    }

    /// Port of `CTrackedClashedDependencyLine::analyseInvolvedIndividuals`.
    pub fn analyse_involved_individuals(
        &mut self,
        mut clashed_des: ClashDescId,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> &mut Self {
        if self.involved_individual_set.is_some() {
            while clashed_des.is_some() {
                let indi_node = calc_alg_context
                    .process_context()
                    .clash_desc(clashed_des)
                    .get_appropriated_individual();
                self.add_involved_individual_node(indi_node, calc_alg_context);
                clashed_des = calc_alg_context
                    .process_context()
                    .clash_desc(clashed_des)
                    .get_next_descriptor();
            }
        }
        self
    }

    /// Port of `CTrackedClashedDependencyLine::addInvolvedIndividual(CIndividualProcessNode*)`.
    pub fn add_involved_individual_node(
        &mut self,
        indi_node: NodeId,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> &mut Self {
        if let Some(set) = &mut self.involved_individual_set {
            if indi_node.is_some() {
                let indi = calc_alg_context.process_context().node(indi_node);
                if indi.nominal_individual().is_some() {
                    set.insert(indi.nominal_individual().raw);
                }
            }
        }
        self
    }

    /// Port of `CTrackedClashedDependencyLine::addInvolvedIndividual(cint64)`.
    pub fn add_involved_individual_id(&mut self, indi_id: Cint64) -> &mut Self {
        if let Some(set) = &mut self.involved_individual_set {
            set.insert(indi_id);
        }
        self
    }

    pub fn has_independent_tracked_clashed_descriptors(&self) -> bool {
        self.independent_tracked_clashes.is_some()
    }
    pub fn take_next_independent_tracked_clashed_descriptor(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> ClashDescId {
        self.take_from_bucket(Bucket::Independent, calc_alg_context)
    }
    pub fn get_independent_tracked_clashed_descriptors(&self) -> ClashDescId {
        self.independent_tracked_clashes
    }

    pub fn has_level_tracked_clashed_descriptors(&self) -> bool {
        self.level_tracked_clashes.is_some()
    }
    pub fn take_next_level_tracked_clashed_descriptor(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> ClashDescId {
        self.take_from_bucket(Bucket::Level, calc_alg_context)
    }
    pub fn get_level_tracked_clashed_descriptors(&self) -> ClashDescId {
        self.level_tracked_clashes
    }

    pub fn has_level_tracked_branching_clashed_descriptors(&self) -> bool {
        self.level_tracked_branching_clashes.is_some()
    }
    pub fn take_next_level_tracked_branching_clashed_descriptor(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> ClashDescId {
        self.take_from_bucket(Bucket::LevelBranching, calc_alg_context)
    }
    pub fn get_level_tracked_branching_clashed_descriptors(&self) -> ClashDescId {
        self.level_tracked_branching_clashes
    }

    pub fn has_pervious_level_tracked_clashed_descriptors(&self) -> bool {
        self.prev_levels_tracked_clashes.is_some()
    }
    pub fn take_next_pervious_level_tracked_clashed_descriptor(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> ClashDescId {
        self.take_from_bucket(Bucket::PreviousLevel, calc_alg_context)
    }
    pub fn get_pervious_level_tracked_clashed_descriptors(&self) -> ClashDescId {
        self.prev_levels_tracked_clashes
    }

    pub fn has_pervious_level_tracked_non_deterministic_clashed_descriptors(&self) -> bool {
        self.prev_levels_tracked_non_det_clashes.is_some()
    }
    pub fn take_next_pervious_level_tracked_non_deterministic_clashed_descriptor(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> ClashDescId {
        self.take_from_bucket(Bucket::PreviousLevelNonDet, calc_alg_context)
    }
    pub fn get_pervious_level_tracked_non_deterministic_clashed_descriptors(&self) -> ClashDescId {
        self.prev_levels_tracked_non_det_clashes
    }

    pub fn has_pervious_level_tracked_non_deterministic_branching_clashed_descriptors(
        &self,
    ) -> bool {
        self.prev_levels_tracked_non_det_branching_clashes.is_some()
    }
    pub fn take_next_pervious_level_tracked_non_deterministic_branching_clashed_descriptor(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> ClashDescId {
        self.take_from_bucket(Bucket::PreviousLevelNonDetBranching, calc_alg_context)
    }
    pub fn get_pervious_level_tracked_non_deterministic_branching_clashed_descriptors(
        &self,
    ) -> ClashDescId {
        self.prev_levels_tracked_non_det_branching_clashes
    }

    /// Port of `CTrackedClashedDependencyLine::hasMoreTrackedClashedList`.
    pub fn has_more_tracked_clashed_list(&self) -> bool {
        self.level_tracked_clashes.is_some()
            || self.level_tracked_branching_clashes.is_some()
            || self.prev_levels_tracked_clashes.is_some()
            || self.prev_levels_tracked_non_det_clashes.is_some()
            || self.prev_levels_tracked_non_det_branching_clashes.is_some()
            || self.independent_tracked_clashes.is_some()
    }

    /// Port of `CTrackedClashedDependencyLine::takeNextTrackedClashedList`.
    pub fn take_next_tracked_clashed_list(&mut self) -> ClashDescId {
        if self.level_tracked_clashes.is_some() {
            let clashes = self.level_tracked_clashes;
            self.level_tracked_clashes = ClashDescId::NONE;
            clashes
        } else if self.level_tracked_branching_clashes.is_some() {
            let clashes = self.level_tracked_branching_clashes;
            self.level_tracked_branching_clashes = ClashDescId::NONE;
            clashes
        } else if self.prev_levels_tracked_clashes.is_some() {
            let clashes = self.prev_levels_tracked_clashes;
            self.prev_levels_tracked_clashes = ClashDescId::NONE;
            clashes
        } else if self.prev_levels_tracked_non_det_clashes.is_some() {
            let clashes = self.prev_levels_tracked_non_det_clashes;
            self.prev_levels_tracked_non_det_clashes = ClashDescId::NONE;
            clashes
        } else if self.prev_levels_tracked_non_det_branching_clashes.is_some() {
            let clashes = self.prev_levels_tracked_non_det_branching_clashes;
            self.prev_levels_tracked_non_det_branching_clashes = ClashDescId::NONE;
            clashes
        } else if self.independent_tracked_clashes.is_some() {
            let clashes = self.independent_tracked_clashes;
            self.independent_tracked_clashes = ClashDescId::NONE;
            clashes
        } else {
            ClashDescId::NONE
        }
    }

    /// Port of `CTrackedClashedDependencyLine::takeNextFreeTrackedClashedDescriptor`.
    pub fn take_next_free_tracked_clashed_descriptor(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> ClashDescId {
        self.take_from_bucket(Bucket::Free, calc_alg_context)
    }

    /// Port of `CTrackedClashedDependencyLine::addFreeTrackedClashedDescriptor`.
    pub fn add_free_tracked_clashed_descriptor(
        &mut self,
        clash_des: ClashDescId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> &mut Self {
        if clash_des.is_some() {
            self.free_tracked_clashed_descriptors = self.prepend(
                clash_des,
                self.free_tracked_clashed_descriptors,
                calc_alg_context,
            );
        }
        self
    }

    pub fn get_tracked_clashed_descriptor_set(&self) -> &HashSet<TrackedClashedDescriptorHasher> {
        &self.clashed_set
    }
    /// Port helper for direct uses of `getTrackedClashedDescriptorSet()->contains/insert`.
    pub fn insert_tracked_clashed_descriptor_hasher(
        &mut self,
        tracked_clashed_des: ClashDescId,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> bool {
        let des_hasher = TrackedClashedDescriptorHasher::new(tracked_clashed_des, calc_alg_context);
        if self.clashed_set.contains(&des_hasher) {
            false
        } else {
            self.clashed_set.insert(des_hasher);
            true
        }
    }
    pub fn get_branching_level(&self) -> Cint64 {
        self.branching_level
    }
    pub fn get_individual_node_level(&self) -> Cint64 {
        self.individual_track_level
    }
    pub fn is_exact_individual_tracking(&self) -> bool {
        self.exact_individual_tracking
    }
    pub fn has_only_independent_tracked_clashed_descriptors_remaining(&self) -> bool {
        self.independent_tracked_clashes.is_some()
            && self.level_tracked_clashes.is_none()
            && self.level_tracked_branching_clashes.is_none()
            && self.prev_levels_tracked_clashes.is_none()
            && self.prev_levels_tracked_non_det_clashes.is_none()
            && self.prev_levels_tracked_non_det_branching_clashes.is_none()
    }
    pub fn has_only_current_individual_node_level_clashes_descriptors(&self) -> bool {
        self.prev_levels_tracked_clashes.is_none()
            && self.prev_levels_tracked_non_det_clashes.is_none()
            && self.prev_levels_tracked_non_det_branching_clashes.is_none()
    }
    pub fn set_involved_individual_tracking_set(
        &mut self,
        indi_tracking_set: Option<HashSet<Cint64>>,
    ) -> &mut Self {
        self.involved_individual_set = indi_tracking_set;
        self
    }
    pub fn get_involved_individual_tracking_set(&self) -> Option<&HashSet<Cint64>> {
        self.involved_individual_set.as_ref()
    }

    fn prepend(
        &self,
        clash_des: ClashDescId,
        head: ClashDescId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> ClashDescId {
        calc_alg_context
            .process_context_mut()
            .clash_desc_mut(clash_des)
            .set_next(head);
        clash_des
    }

    fn take_from_bucket(
        &mut self,
        bucket: Bucket,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> ClashDescId {
        let head = match bucket {
            Bucket::Independent => &mut self.independent_tracked_clashes,
            Bucket::Level => &mut self.level_tracked_clashes,
            Bucket::LevelBranching => &mut self.level_tracked_branching_clashes,
            Bucket::PreviousLevel => &mut self.prev_levels_tracked_clashes,
            Bucket::PreviousLevelNonDet => &mut self.prev_levels_tracked_non_det_clashes,
            Bucket::PreviousLevelNonDetBranching => {
                &mut self.prev_levels_tracked_non_det_branching_clashes
            }
            Bucket::Free => &mut self.free_tracked_clashed_descriptors,
        };
        let clashed_des_tmp = *head;
        if head.is_some() {
            *head = calc_alg_context
                .process_context()
                .clash_desc(*head)
                .get_next_descriptor();
            calc_alg_context
                .process_context_mut()
                .clash_desc_mut(clashed_des_tmp)
                .set_next(ClashDescId::NONE);
        }
        clashed_des_tmp
    }
}

enum Bucket {
    Independent,
    Level,
    LevelBranching,
    PreviousLevel,
    PreviousLevelNonDet,
    PreviousLevelNonDetBranching,
    Free,
}

impl super::algorithm::CompletionTaskHandleAlgorithm {
    // =======================================================================
    // Clash-descriptor construction from a node's label set (cpp 4395–4405).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::createClashedIndividualNodeDescriptor`.
    /// cpp 4395–4405.
    ///
    /// Walks the node's adding-sorted concept-descriptor chain and prepends one
    /// clashed-concept descriptor per concept onto `prev_clashes`, returning the new
    /// chain head.
    pub fn create_clashed_individual_node_descriptor(
        &mut self,
        prev_clashes: ClashDescId,
        process_indi: &mut NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> ClashDescId {
        // CClashedDependencyDescriptor* clashDes = prevClashes;
        // CReapplyConceptLabelSet* conSet = processIndi->getReapplyConceptLabelSet(false);
        // CConceptDescriptor* conDesIt = conSet->getAddingSortedConceptDescriptionLinker();
        // while (conDesIt) {
        //   CConceptDescriptor* conDes = conDesIt;
        //   clashDes = createClashedConceptDescriptor(clashDes,processIndi,conDes,conDes->getDependencyTrackPoint(),ctx);
        //   conDesIt = conDesIt->getNext();
        // }
        // return clashDes;
        let mut clash_des = prev_clashes;
        let con_set: LabelSetId = calc_alg_context
            .process_context_mut()
            .node_mut(*process_indi)
            .get_reapply_concept_label_set(false);
        let mut con_des_it = if con_set.is_some() {
            calc_alg_context
                .process_context()
                .label_set(con_set)
                .get_adding_sorted_concept_description_linker()
        } else {
            Id::NONE
        };
        while con_des_it.is_some() {
            let con_des = con_des_it;
            let prev_dep_track_point = calc_alg_context
                .process_context()
                .con_desc(con_des)
                .get_dependency_track_point();
            clash_des = self.create_clashed_concept_descriptor(
                clash_des,
                process_indi,
                con_des,
                prev_dep_track_point,
                calc_alg_context,
            );
            con_des_it = calc_alg_context
                .process_context()
                .con_desc(con_des_it)
                .get_next_concept_descriptor();
        }
        clash_des
    }

    // =======================================================================
    // Debug tracked-clash descriptor strings (cpp 6569–6718).
    // Both are instrumentation over the opaque `CTrackedClashedDescriptor` chain.
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::generateDebugTrackedClashedDescriptorSummaryString`.
    /// cpp 6569–6585.
    ///
    /// KONCLUDE-PORT-NOTE[api]: debug-only string builder over the not-yet-ported
    /// opaque `CTrackedClashedDescriptor` chain (`Cint64`).
    pub fn generate_debug_tracked_clashed_descriptor_summary_string(
        &mut self,
        tracked_clash_descriptors: ClashDescId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> String {
        // PORT-PENDING: faithful transcription of cpp 6569–6585. Outline:
        //   clashString = "";
        //   for it = trackedClashDescriptors; it; it = it->getNextDescriptor():
        //     conDes = it->getConceptDescriptor();
        //     conceptString = conDes ? CConceptTextFormater::getConceptString(conDes->getConcept(), conDes->isNegated()) : "null";
        //     if !clashString.isEmpty(): clashString += ", ";
        //     clashString += conceptString;
        //   return clashString;
        //
        // Held PORT-PENDING: the opaque `CTrackedClashedDescriptor` linked-list
        // (`getNextDescriptor` / `getConceptDescriptor`) and the
        // `CConceptTextFormater` debug formatter are not yet ported (W3-DEFER[api]).
        let _ = (tracked_clash_descriptors, calc_alg_context);
        String::new()
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::generateDebugTrackedClashedDescriptorString`.
    /// cpp 6588–6718.
    ///
    /// KONCLUDE-PORT-NOTE[api]: debug-only multi-line string builder over the opaque
    /// `CTrackedClashedDescriptor` chain; the body is a large dependency-type → label
    /// switch.
    pub fn generate_debug_tracked_clashed_descriptor_string(
        &mut self,
        tracked_clash_descriptors: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> String {
        // PORT-PENDING: faithful transcription of cpp 6588–6718. Outline:
        //   clashListString = "";
        //   for it = trackedClashDescriptors; it; it = it->getNextDescriptor():
        //     conDes = it->getConceptDescriptor();
        //     conceptString = conDes ? getConceptString(conDes->getConcept(), conDes->isNegated()) : "null";
        //     depTrackPoint = it->getDependencyTrackPoint();
        //     dependencyString = "null";
        //     if depTrackPoint:
        //       depNode = depTrackPoint->getDependencyNode();
        //       depTypeString = switch(depNode->getDependencyType()) {  // DependencyNode::DNT* -> label
        //         DNTINDEPENDENTBASE->"INDEPENDENT", DNTALLDEPENDENCY->"ALL", DNTSOMEDEPENDENCY->"SOME",
        //         DNTANDDEPENDENCY->"AND", DNTORDEPENDENCY->"OR", DNTATLEASTDEPENDENCY->"ATLEAST",
        //         DNTAUTOMATCHOOSEDEPENDENCY->"AUTOMATCHOOSE", DNTAUTOMATTRANSACTIONDEPENDENCY->"AUTOMATTRANSACTION",
        //         DNTSELFDEPENDENCY->"SELF", DNTVALUEDEPENDENCY->"VALUE", DNTNEGVALUEDEPENDENCY->"NEGVALUE",
        //         DNTDISTINCTDEPENDENCY->"DISTINCT", DNTMERGEDCONCEPT->"MERGEDCONCEPT", DNTMERGEDLINK->"MERGEDLINK",
        //         DNTMERGEDEPENDENCY->"MERGE", DNTATMOSTDEPENDENCY->"ATMOST", DNTQUALIFYDEPENDENCY->"QUALIFY",
        //         DNTFUNCTIONALDEPENDENCY->"FUNCTIONAL", DNTNOMINALDEPENDENCY->"NOMINAL",
        //         DNTIMPLICATIONDEPENDENCY->"IMPLICATION", DNTEXPANDEDDEPENDENCY->"EXPANDED",
        //         DNTDATATYPETRIGGERDEPENDENCY->"DATATYPETRIGGER" };
        //       depNodeConDes = depNode->getConceptDescriptor();
        //       conceptDepNodeString = depNodeConDes ? getConceptString(depNodeConDes->getConcept(), depNodeConDes->isNegated()) : "null";
        //       depInfoString = "";
        //       if depNode->isNonDeterministiDependencyNode():
        //         nonDetDepNode = (CNonDeterministicDependencyNode*)depNode;
        //         depInfoString += " NonDetDep, <openedDependencyTrackingPointsCount / branchTrackPoints.count>";
        //       depInfoString += " + ...(getAdditionalDependencyCount)";
        //       dependencyString = "{depTypeString}-Dependency: {conceptDepNodeString}{depInfoString}";
        //     clashString = "\t[ID:appropriatedIndividualID / L:appropriatedIndividualLevel | B:branchingLevelTag]: {conceptString}  -->  dependencyString\r\n";
        //     clashListString += clashString;
        //   clashListString.replace("\r\n","<br>");
        //   return clashListString;
        //
        // Held PORT-PENDING: the opaque `CTrackedClashedDescriptor` chain, the
        // `CDependencyNode`/`CNonDeterministicDependencyNode` debug accessors, and the
        // `CConceptTextFormater` formatter (W3-DEFER[api]).
        let _ = (tracked_clash_descriptors, calc_alg_context);
        String::new()
    }

    // =======================================================================
    // Tracked-clash free-list pop (cpp 6952–6959).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getFreeTrackedClashedDescriptor`.
    /// cpp 6952–6959.
    pub fn get_free_tracked_clashed_descriptor(
        &mut self,
        tracking_line: &mut TrackedClashedDependencyLine,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> ClashDescId {
        // Faithful transcription of cpp 6952–6959:
        //   des = trackingLine->takeNextFreeTrackedClashedDescriptor();
        //   if !des:
        //     tmpMemMan = calcAlgContext->getUsedTemporaryMemoryAllocationManager();
        //     des = CObjectAllocator<CTrackedClashedDescriptor>::allocateAndConstruct(tmpMemMan);
        //   return des;
        let des = tracking_line.take_next_free_tracked_clashed_descriptor(calc_alg_context);
        if des.is_some() {
            return des;
        }
        calc_alg_context
            .process_context_mut()
            .alloc_clash_desc(super::super::process::descriptor::ClashDescriptor::new())
    }

    // =======================================================================
    // Relevance marking over a tracked-clash chain (cpp 7352–7357).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::markRelevanceForTrackedClashedDescriptors`.
    /// cpp 7352–7357.
    ///
    /// Marks dependency relevance for the track point of every tracked-clash
    /// descriptor in the chain.
    pub fn mark_relevance_for_tracked_clashed_descriptors(
        &mut self,
        descriptors: ClashDescId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let mut des_it = descriptors;
        while des_it.is_some() {
            let dep_track_point = calc_alg_context
                .process_context()
                .clash_desc(des_it)
                .get_dependency_track_point();
            self.mark_dependency_relevance(dep_track_point, calc_alg_context);
            des_it = calc_alg_context
                .process_context()
                .clash_desc(des_it)
                .get_next_descriptor();
        }
    }

    // =======================================================================
    // Unsat-caching signature collection (cpp 7545–7552).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addIndiNodeSignatureOfUnsatisfiableClashedDescriptors`.
    /// cpp 7545–7552.
    ///
    /// Inserts the concept-signature value of the (corrected nominal) individual
    /// addressed by the tracked-clash descriptor into `mUnsatCachingSignatureSet`.
    pub fn add_indi_node_signature_of_unsatisfiable_clashed_descriptors(
        &mut self,
        tracked_clashed_des: ClashDescId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let indi_id = calc_alg_context
            .process_context()
            .clash_desc(tracked_clashed_des)
            .get_appropriated_individual_id();
        let indi = self.get_corrected_nominal_individual_node(indi_id, calc_alg_context);
        let con_set = calc_alg_context
            .process_context_mut()
            .node_mut(indi)
            .get_reapply_concept_label_set(false);
        let con_sig = calc_alg_context
            .process_context()
            .label_set(con_set)
            .get_concept_signature_value();
        self.unsat_caching_signature_set.insert(con_sig);
        true
    }

    // =======================================================================
    // Tracked-clash sort predicate + insertion sort (cpp 7554–7583).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::isClashedDescriptorSortedBefore`.
    /// cpp 7554–7556.
    ///
    /// True iff `before`'s concept tag does not exceed `after`'s (or `after` is the
    /// chain end).
    pub fn is_clashed_descriptor_sorted_before(
        &mut self,
        tracked_clashed_des_before: ClashDescId,
        tracked_clashed_des_after: ClashDescId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        if tracked_clashed_des_after.is_none() {
            return true;
        }
        let before_con_des = calc_alg_context
            .process_context()
            .clash_desc(tracked_clashed_des_before)
            .get_concept_descriptor();
        let after_con_des = calc_alg_context
            .process_context()
            .clash_desc(tracked_clashed_des_after)
            .get_concept_descriptor();
        let before_tag = calc_alg_context
            .process_context()
            .con_desc(before_con_des)
            .get_concept_tag(calc_alg_context.ontology_arenas());
        let after_tag = calc_alg_context
            .process_context()
            .con_desc(after_con_des)
            .get_concept_tag(calc_alg_context.ontology_arenas());
        before_tag <= after_tag
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getSortedClashedDescriptors`.
    /// cpp 7559–7583.
    ///
    /// Insertion-sorts the tracked-clash chain by concept tag (via
    /// `isClashedDescriptorSortedBefore`), returning the new sorted head.
    pub fn get_sorted_clashed_descriptors(
        &mut self,
        mut tracked_clashed_des: ClashDescId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> ClashDescId {
        if tracked_clashed_des.is_none() {
            return ClashDescId::NONE;
        }

        let mut sorted_tracked_clashed_des = tracked_clashed_des;
        tracked_clashed_des = calc_alg_context
            .process_context()
            .clash_desc(tracked_clashed_des)
            .get_next_descriptor();
        calc_alg_context
            .process_context_mut()
            .clash_desc_mut(sorted_tracked_clashed_des)
            .set_next(ClashDescId::NONE);

        while tracked_clashed_des.is_some() {
            let tmp_tracked_clashed_des = tracked_clashed_des;
            tracked_clashed_des = calc_alg_context
                .process_context()
                .clash_desc(tracked_clashed_des)
                .get_next_descriptor();
            calc_alg_context
                .process_context_mut()
                .clash_desc_mut(tmp_tracked_clashed_des)
                .set_next(ClashDescId::NONE);

            if self.is_clashed_descriptor_sorted_before(
                tmp_tracked_clashed_des,
                sorted_tracked_clashed_des,
                calc_alg_context,
            ) {
                calc_alg_context
                    .process_context_mut()
                    .clash_desc_mut(tmp_tracked_clashed_des)
                    .set_next(sorted_tracked_clashed_des);
                sorted_tracked_clashed_des = tmp_tracked_clashed_des;
            } else {
                let mut insert_pos_it = sorted_tracked_clashed_des;
                while insert_pos_it.is_some() {
                    let next_sorted_pos_des = calc_alg_context
                        .process_context()
                        .clash_desc(insert_pos_it)
                        .get_next_descriptor();
                    if self.is_clashed_descriptor_sorted_before(
                        tmp_tracked_clashed_des,
                        next_sorted_pos_des,
                        calc_alg_context,
                    ) {
                        calc_alg_context
                            .process_context_mut()
                            .clash_desc_mut(tmp_tracked_clashed_des)
                            .set_next(next_sorted_pos_des);
                        calc_alg_context
                            .process_context_mut()
                            .clash_desc_mut(insert_pos_it)
                            .set_next(tmp_tracked_clashed_des);
                        break;
                    }
                    insert_pos_it = next_sorted_pos_des;
                }
            }
        }
        sorted_tracked_clashed_des
    }

    // =======================================================================
    // Unsat-cache write (cpp 7586–7592).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::writeUnsatisfiableClashedDescriptors`.
    /// cpp 7586–7592.
    ///
    /// Forwards the tracked-clash chain to the unsatisfiable-cache handler when one
    /// is installed; returns false otherwise.
    pub fn write_unsatisfiable_clashed_descriptors(
        &mut self,
        tracked_clashed_des: ClashDescId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        if let Some(mut handler_state) = calc_alg_context.take_used_unsatisfiable_cache_handler() {
            let written = handler_state
                .handler
                .write_unsatisfiable_clashed_descriptors(
                    tracked_clashed_des,
                    calc_alg_context,
                    &mut handler_state.cache_context,
                );
            calc_alg_context.restore_used_unsatisfiable_cache_handler(handler_state);
            written
        } else {
            false
        }
    }

    // =======================================================================
    // Branch-filtered tracked-clash collection (cpp 7595–7652).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getCollectedFilteredClashedDescriptorsFromBranch`.
    /// cpp 7595–7652.
    ///
    /// Collects (de-duplicated) the tracked-clash descriptors of a non-deterministic
    /// branch: walks every branch track point, turning each non-self-pointing clash
    /// into a tracked-clash descriptor (one per dependency), records the involved
    /// individuals on the tracking line, then appends the deterministic backtracking
    /// of the self-pointing clash.
    ///
    /// KONCLUDE-PORT-NOTE[api]: `CNonDeterministicDependencyNode*` → `DependencyId`;
    /// the tracking line, the `CTrackedClashedDescriptor` chain, the
    /// `CTrackedClashedDescriptorHasher` set, branch track-point clash lists, and
    /// deterministic replay helper are all live substrate.
    pub fn get_collected_filtered_clashed_descriptors_from_branch(
        &mut self,
        non_det_clashed_pointing_des: ClashDescId,
        non_det_branch_dep_node: DependencyId,
        tracking_line: &mut TrackedClashedDependencyLine,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
        tmp_mem_man: Cint64,
    ) -> ClashDescId {
        let mut test_clashed_set: HashSet<TrackedClashedDescriptorHasher> = HashSet::new();
        let mut track_point_it = calc_alg_context
            .process_context()
            .dep_node(non_det_branch_dep_node)
            .branch_track_points();
        let mut new_tracked_clashed_descriptor_list = ClashDescId::NONE;
        let mut non_det_pointing_first_tracked_clashed_descriptor = non_det_clashed_pointing_des;

        while track_point_it.is_some() {
            let mut clashed_dep_descriptors_it = calc_alg_context
                .process_context()
                .track_point(track_point_it)
                .get_clashes();
            while clashed_dep_descriptors_it.is_some() {
                let clashed_dep_descriptor = clashed_dep_descriptors_it;
                let dep_track_point = calc_alg_context
                    .process_context()
                    .clash_desc(clashed_dep_descriptor)
                    .get_dependency_track_point();
                let pointing_dep_node = if dep_track_point.is_some() {
                    calc_alg_context
                        .process_context()
                        .track_point(dep_track_point)
                        .dependency_node()
                } else {
                    DependencyId::NONE
                };

                if pointing_dep_node != non_det_branch_dep_node {
                    let new_tracked_clash_des = self.create_tracked_clashes_descriptor(
                        clashed_dep_descriptor,
                        calc_alg_context,
                        tmp_mem_man,
                        false,
                    );
                    let hasher = TrackedClashedDescriptorHasher::new(
                        new_tracked_clash_des,
                        calc_alg_context,
                    );
                    if !test_clashed_set.contains(&hasher) {
                        test_clashed_set.insert(hasher);
                        calc_alg_context
                            .process_context_mut()
                            .clash_desc_mut(new_tracked_clash_des)
                            .set_next(new_tracked_clashed_descriptor_list);
                        new_tracked_clashed_descriptor_list = new_tracked_clash_des;
                    }
                } else if non_det_pointing_first_tracked_clashed_descriptor.is_none() {
                    non_det_pointing_first_tracked_clashed_descriptor = self
                        .create_tracked_clashes_descriptor(
                            clashed_dep_descriptor,
                            calc_alg_context,
                            tmp_mem_man,
                            false,
                        );
                }

                clashed_dep_descriptors_it = calc_alg_context
                    .process_context()
                    .clash_desc(clashed_dep_descriptors_it)
                    .get_next();
            }

            let involved_ids: Vec<Cint64> = calc_alg_context
                .process_context()
                .track_point(track_point_it)
                .get_involved_individual_ids_linker()
                .to_vec();
            for indi_id in involved_ids {
                tracking_line.add_involved_individual_id(indi_id);
            }

            track_point_it = calc_alg_context
                .process_context()
                .track_point(track_point_it)
                .next;
        }

        assert!(
            non_det_pointing_first_tracked_clashed_descriptor.is_some(),
            "track point for non-deterministic dependency not found"
        );

        let mut non_det_backtracked_clashed_des = self
            .get_backtracked_deterministic_clashed_descriptors(
                non_det_pointing_first_tracked_clashed_descriptor,
                tracking_line,
                None,
                calc_alg_context,
            );
        while non_det_backtracked_clashed_des.is_some() {
            let non_det_backtracked_clashed_des_it = non_det_backtracked_clashed_des;
            non_det_backtracked_clashed_des = calc_alg_context
                .process_context()
                .clash_desc(non_det_backtracked_clashed_des_it)
                .get_next_descriptor();
            calc_alg_context
                .process_context_mut()
                .clash_desc_mut(non_det_backtracked_clashed_des_it)
                .set_next(ClashDescId::NONE);

            let hasher = TrackedClashedDescriptorHasher::new(
                non_det_backtracked_clashed_des_it,
                calc_alg_context,
            );
            if !test_clashed_set.contains(&hasher) {
                test_clashed_set.insert(hasher);
                calc_alg_context
                    .process_context_mut()
                    .clash_desc_mut(non_det_backtracked_clashed_des_it)
                    .set_next(new_tracked_clashed_descriptor_list);
                new_tracked_clashed_descriptor_list = non_det_backtracked_clashed_des_it;
            }
        }

        new_tracked_clashed_descriptor_list
    }

    // =======================================================================
    // Tracked-clash descriptor builders (cpp 7921–7973).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::createTrackedClashesDescriptors`.
    /// cpp 7921–7935.
    ///
    /// Builds the tracked-clash chain for an entire `CClashedDependencyDescriptor`
    /// list (one tracked-clash descriptor per clash, head-prepended).
    ///
    /// KONCLUDE-PORT-NOTE[overload]: the C++ trailing `copyIndependentConceptDescriptors`
    /// has a header default; callers that pass three args (e.g. the branch collector)
    /// supply the default — the Rust port keeps it explicit.
    pub fn create_tracked_clashes_descriptors(
        &mut self,
        clashes: ClashDescId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
        tmp_mem_man: Cint64,
        copy_independent_concept_descriptors: bool,
    ) -> ClashDescId {
        // PORT-PENDING: faithful transcription of cpp 7921–7935. Outline:
        //   if !tmpMemMan: tmpMemMan = calcAlgContext->getUsedTemporaryMemoryAllocationManager();
        //   trackingClashes = nullptr;
        //   for nextClash = clashes; nextClash; nextClash = nextClash->getNext():
        //     newTrackingClash = createTrackedClashesDescriptor(nextClash, ctx, tmpMemMan, copyIndependentConceptDescriptors);
        //     trackingClashes = newTrackingClash->append(trackingClashes);
        //   return trackingClashes;
        //
        let _ = tmp_mem_man;
        let mut tracking_clashes = ClashDescId::NONE;
        let mut next_clash = clashes;
        while next_clash.is_some() {
            let next_next_clash = calc_alg_context
                .process_context()
                .clash_desc(next_clash)
                .get_next();
            let new_tracking_clash = self.create_tracked_clashes_descriptor(
                next_clash,
                calc_alg_context,
                tmp_mem_man,
                copy_independent_concept_descriptors,
            );
            if tracking_clashes.is_some() {
                calc_alg_context
                    .process_context_mut()
                    .clash_desc_mut(new_tracking_clash)
                    .set_next(tracking_clashes);
            }
            tracking_clashes = new_tracking_clash;
            next_clash = next_next_clash;
        }
        tracking_clashes
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::createTrackedClashesDescriptor`.
    /// cpp 7939–7973.
    ///
    /// Builds one tracked-clash descriptor from a single `CClashedDependencyDescriptor`,
    /// dispatching on its runtime subclass (already-tracked / clashed-concept /
    /// clashed-datatype-value-space-exclusion / generic-by-dependency).
    ///
    /// KONCLUDE-PORT-NOTE[api]: the C++ `dynamic_cast` over the
    /// `CClashedDependencyDescriptor` hierarchy cannot be reproduced — `ClashDescriptor`
    /// is currently a single struct (its per-subclass payload + the
    /// `CTrackedClashedDescriptor` subtype are deferred to the clash tagged-enum unit),
    /// so the four-way dispatch is held PORT-PENDING.
    pub fn create_tracked_clashes_descriptor(
        &mut self,
        clash_des: ClashDescId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
        tmp_mem_man: Cint64,
        copy_independent_concept_descriptors: bool,
    ) -> ClashDescId {
        let _ = tmp_mem_man;
        let (kind, dep_track_point) = {
            let clash = calc_alg_context.process_context().clash_desc(clash_des);
            (clash.kind, clash.get_dependency_track_point())
        };

        let mut new_tracking_clash = super::super::process::descriptor::ClashDescriptor::new();
        match kind {
            super::super::process::descriptor::ClashDescriptorKind::Tracked { .. } => {
                let source = calc_alg_context.process_context().clash_desc(clash_des);
                new_tracking_clash.init_tracked_clashed_descriptor_copy(source);
            }
            super::super::process::descriptor::ClashDescriptorKind::Concept {
                concept_descriptor,
                individual_node,
            } => {
                self.init_tracked_clash_from_parts(
                    &mut new_tracking_clash,
                    individual_node,
                    concept_descriptor,
                    VarBindingPathId::NONE,
                    dep_track_point,
                    calc_alg_context,
                );
            }
            super::super::process::descriptor::ClashDescriptorKind::Dependency
            | super::super::process::descriptor::ClashDescriptorKind::IndividualLink { .. }
            | super::super::process::descriptor::ClashDescriptorKind::IndividualDistinct {
                ..
            }
            | super::super::process::descriptor::ClashDescriptorKind::NegationDisjointLink {
                ..
            } => {
                let individual_node = if dep_track_point.is_some() {
                    self.get_coressponding_individual_node_from_dependency(
                        dep_track_point,
                        calc_alg_context,
                    )
                } else {
                    NodeId::NONE
                };
                self.init_tracked_clash_from_parts(
                    &mut new_tracking_clash,
                    individual_node,
                    ConDescId::NONE,
                    VarBindingPathId::NONE,
                    dep_track_point,
                    calc_alg_context,
                );
            }
        }

        let new_tracking_clash = calc_alg_context
            .process_context_mut()
            .alloc_clash_desc(new_tracking_clash);
        if copy_independent_concept_descriptors
            && calc_alg_context
                .process_context()
                .clash_desc(new_tracking_clash)
                .is_pointing_to_independent_dependency_node()
        {
            let con_des = calc_alg_context
                .process_context()
                .clash_desc(new_tracking_clash)
                .get_concept_descriptor();
            if con_des.is_some() {
                let (concept, negated, dep_track_point) = {
                    let source = calc_alg_context.process_context().con_desc(con_des);
                    (
                        source.get_concept(),
                        source.is_negated(),
                        source.get_dependency_track_point(),
                    )
                };
                let mut con_des_copy = super::super::process::descriptor::ConceptDescriptor::new();
                con_des_copy.concept = concept;
                con_des_copy.negated = negated;
                con_des_copy.dep_track_point = dep_track_point;
                let con_des_copy = calc_alg_context
                    .process_context_mut()
                    .alloc_con_desc(con_des_copy);
                calc_alg_context
                    .process_context_mut()
                    .clash_desc_mut(new_tracking_clash)
                    .set_concept_descriptor(con_des_copy);
            }
        }
        new_tracking_clash
    }

    fn init_tracked_clash_from_parts(
        &mut self,
        new_tracking_clash: &mut super::super::process::descriptor::ClashDescriptor,
        individual_node: NodeId,
        concept_descriptor: ConDescId,
        var_bind_path: VarBindingPathId,
        dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let mut individual_node_id = INVALID;
        let mut individual_node_level = INVALID;
        let mut nominal_individual = false;
        let mut error = false;
        if individual_node.is_some() {
            let node = calc_alg_context.process_context().node(individual_node);
            individual_node_id = node.individual_node_id();
            individual_node_level = node.individual_nominal_level_or_ancestor_depth();
            nominal_individual = node.is_nominal_individual_node();
        } else {
            error = true;
        }

        let mut deterministic = false;
        let mut independent = false;
        let mut processing_tag = INVALID;
        let mut branching_level_tag = INVALID;
        if dep_track_point.is_some() {
            let track_point = calc_alg_context
                .process_context()
                .track_point(dep_track_point);
            branching_level_tag = track_point.get_branching_tag();
            let dep_node = track_point.dependency_node();
            if dep_node.is_some() {
                let dep_node = calc_alg_context.process_context().dep_node(dep_node);
                processing_tag = dep_node.base().process_tag;
                deterministic = dep_node.is_deterministic();
                independent = dep_node.is_independent_base_dependency_type();
            } else {
                error = true;
            }
            if branching_level_tag <= -1 {
                error = true;
            }
        } else {
            error = true;
        }

        new_tracking_clash.init_tracked_clashed_descriptor(
            individual_node,
            individual_node_id,
            individual_node_level,
            nominal_individual,
            concept_descriptor,
            var_bind_path,
            dep_track_point,
            deterministic,
            independent,
            processing_tag,
            branching_level_tag,
            error,
        );
    }

    // =======================================================================
    // Clash-descriptor factory wrappers (cpp 16717–16735).
    //
    // Each is the identical Konclude idiom:
    //   CClashedDependencyDescriptor* clashDes =
    //       calcAlgContext->getClashDescriptorFactory()->createClashed*Descriptor(prevClashes, ..., ctx);
    //   return clashDes;
    // The concept/link/distinct/negation-disjoint descriptor wrappers are now
    // live over the folded `ClashDescriptor` arena.
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::createClashedConceptDescriptor`.
    /// cpp 16717–16720.
    pub fn create_clashed_concept_descriptor(
        &mut self,
        prev_clashes: ClashDescId,
        process_indi: &mut NodeId,
        con_des: ConDescId,
        prev_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> ClashDescId {
        let mut clash_descriptor = super::super::process::descriptor::ClashDescriptor::new();
        clash_descriptor.init_clashed_concept_descriptor(
            con_des,
            prev_dep_track_point,
            *process_indi,
        );
        if prev_clashes.is_some() {
            clash_descriptor.set_next(prev_clashes);
        }
        let clash_des = calc_alg_context
            .process_context_mut()
            .alloc_clash_desc(clash_descriptor);
        clash_des
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::createClashedIndividualLinkDescriptor`.
    /// cpp 16722–16725.
    pub fn create_clashed_individual_link_descriptor(
        &mut self,
        prev_clashes: ClashDescId,
        link: EdgeId,
        prev_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> ClashDescId {
        let mut clash_descriptor = super::super::process::descriptor::ClashDescriptor::new();
        clash_descriptor.init_clashed_link_descriptor(link, prev_dep_track_point);
        if prev_clashes.is_some() {
            clash_descriptor.set_next(prev_clashes);
        }
        let clash_des = calc_alg_context
            .process_context_mut()
            .alloc_clash_desc(clash_descriptor);
        clash_des
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::createClashedIndividualDistinctDescriptor`.
    /// cpp 16727–16730.
    pub fn create_clashed_individual_distinct_descriptor(
        &mut self,
        prev_clashes: ClashDescId,
        distinct: DistinctEdgeId,
        prev_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> ClashDescId {
        let mut clash_descriptor = super::super::process::descriptor::ClashDescriptor::new();
        clash_descriptor.init_clashed_distinct_descriptor(distinct, prev_dep_track_point);
        if prev_clashes.is_some() {
            clash_descriptor.set_next(prev_clashes);
        }
        let clash_des = calc_alg_context
            .process_context_mut()
            .alloc_clash_desc(clash_descriptor);
        clash_des
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::createClashedNegationDisjointDescriptor`.
    /// cpp 16732–16735.
    pub fn create_clashed_negation_disjoint_descriptor(
        &mut self,
        prev_clashes: ClashDescId,
        disjoint_neg_link: DisjointEdgeId,
        prev_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> ClashDescId {
        let mut clash_descriptor = super::super::process::descriptor::ClashDescriptor::new();
        clash_descriptor.init_clashed_negation_disjoint_link_descriptor(
            disjoint_neg_link,
            prev_dep_track_point,
        );
        if prev_clashes.is_some() {
            clash_descriptor.set_next(prev_clashes);
        }
        let clash_des = calc_alg_context
            .process_context_mut()
            .alloc_clash_desc(clash_descriptor);
        clash_des
    }

    // =======================================================================
    // Label-concept clash tests (cpp 17323–17391 and 20867–20932).
    //
    // Mirrors the u16/u34 label-set comparison ports: the count/threshold branch
    // selection (and, for the node version, the label-set fetch + count-swap) is
    // ported against concrete accessors; the per-concept lockstep walks iterate
    // `CReapplyConceptLabelSetIterator`, an unported LS-1 stub, so they stay
    // `W6-DEFER[api]` with the faithful logic in-comment.
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::isLabelConceptClashSet`
    /// (label-set / label-set form). cpp 17323–17391.
    ///
    /// KONCLUDE-PORT-NOTE[overload]: C++ overloads `isLabelConceptClashSet`; the two
    /// arities are disambiguated as `_label_sets` (this one) and `_nodes`.
    ///
    /// Detects whether `sub_concept_set` carries a concept that `super_concept_set`
    /// contains with the opposite negation (a clash → returns true). `sub_set_flag`,
    /// when supplied, reports whether `sub_concept_set` is a subset of
    /// `super_concept_set` (nominal concepts ignored when `ignore_nominals_for_subset_checking`).
    pub fn is_label_concept_clash_set_label_sets(
        &mut self,
        sub_concept_set: LabelSetId,
        super_concept_set: LabelSetId,
        sub_set_flag: Option<&mut bool>,
        ignore_nominals_for_subset_checking: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // STATINC(LABELCONCEPTSUBSETTESTCOUNT, calcAlgContext);
        let sub_con_set_count = calc_alg_context
            .process_context()
            .label_set(sub_concept_set)
            .get_concept_count();
        let super_con_set_count = calc_alg_context
            .process_context()
            .label_set(super_concept_set)
            .get_concept_count();
        let threshold_factor = self.map_comparison_direct_lookup_factor;
        // if (subSetFlag) *subSetFlag = true;
        let mut sub_set_flag = sub_set_flag;
        if let Some(flag) = sub_set_flag.as_deref_mut() {
            *flag = true;
        }
        if sub_con_set_count * threshold_factor < super_con_set_count {
            let mut sub_con_set_it = calc_alg_context
                .process_context()
                .label_set_concept_label_set_iterator(sub_concept_set, true, false, false);
            while sub_con_set_it.has_value() {
                let sub_con_des = sub_con_set_it.get_concept_descriptor();
                let sub_concept = calc_alg_context
                    .process_context()
                    .con_desc(sub_con_des)
                    .get_concept();
                let mut contained_negation = false;
                if self.label_set_contains_concept_get_negated_resolved(
                    super_concept_set,
                    sub_concept,
                    Some(&mut contained_negation),
                    calc_alg_context,
                ) {
                    if contained_negation
                        != calc_alg_context
                            .process_context()
                            .con_desc(sub_con_des)
                            .is_negated()
                    {
                        return true;
                    }
                } else if !ignore_nominals_for_subset_checking
                    || calc_alg_context
                        .ontology_arenas()
                        .concept(sub_concept)
                        .get_operator_code()
                        != CCNOMINAL
                {
                    if let Some(flag) = sub_set_flag.as_deref_mut() {
                        *flag = false;
                    }
                }
                sub_con_set_it.move_next(calc_alg_context.process_context());
            }
        } else {
            let mut sub_con_set_it = calc_alg_context
                .process_context()
                .label_set_concept_label_set_iterator(sub_concept_set, true, false, false);
            let mut super_con_set_it = calc_alg_context
                .process_context()
                .label_set_concept_label_set_iterator(super_concept_set, true, false, false);
            let mut super_con_des = super_con_set_it.get_concept_descriptor();
            let mut super_con_tag = if super_con_set_it.has_value() {
                super_con_set_it.get_data_tag(
                    calc_alg_context.process_context(),
                    calc_alg_context.ontology_arenas(),
                )
            } else {
                Cint64::MAX
            };
            if super_con_set_it.has_value() {
                super_con_set_it.move_next(calc_alg_context.process_context());
            }
            while sub_con_set_it.has_value() {
                let sub_con_des = sub_con_set_it.get_concept_descriptor();
                let sub_con_tag = sub_con_set_it.get_data_tag(
                    calc_alg_context.process_context(),
                    calc_alg_context.ontology_arenas(),
                );

                let mut concept_in_super_con_set = true;
                while super_con_tag < sub_con_tag {
                    if !super_con_set_it.has_value() {
                        if let Some(flag) = sub_set_flag.as_deref_mut() {
                            *flag = false;
                        }
                        return false;
                    }
                    super_con_des = super_con_set_it.get_concept_descriptor();
                    super_con_tag = super_con_set_it.get_data_tag(
                        calc_alg_context.process_context(),
                        calc_alg_context.ontology_arenas(),
                    );
                    super_con_set_it.move_next(calc_alg_context.process_context());
                }
                if sub_con_tag != super_con_tag {
                    concept_in_super_con_set = false;
                } else if calc_alg_context
                    .process_context()
                    .con_desc(sub_con_des)
                    .is_negated()
                    != calc_alg_context
                        .process_context()
                        .con_desc(super_con_des)
                        .is_negated()
                {
                    return true;
                }

                if !concept_in_super_con_set {
                    let sub_concept = calc_alg_context
                        .process_context()
                        .con_desc(sub_con_des)
                        .get_concept();
                    if !ignore_nominals_for_subset_checking
                        || calc_alg_context
                            .ontology_arenas()
                            .concept(sub_concept)
                            .get_operator_code()
                            != CCNOMINAL
                    {
                        if let Some(flag) = sub_set_flag.as_deref_mut() {
                            *flag = false;
                        }
                    }
                }

                sub_con_set_it.move_next(calc_alg_context.process_context());
            }
        }
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::isLabelConceptClashSet`
    /// (node / node form, building clash descriptors). cpp 20867–20932.
    ///
    /// KONCLUDE-PORT-NOTE[overload]: the `_nodes` arity of the overloaded
    /// `isLabelConceptClashSet` (see `_label_sets`).
    ///
    /// Detects a clashing concept pair between the two individuals' concept label
    /// sets and, on the first clash, prepends both sides' clashed-concept descriptors
    /// onto `clash_descriptors`. The smaller set is taken as `sub` (the lookup side);
    /// the per-concept iterator walks are deferred (LS-1 stub).
    pub fn is_label_concept_clash_set_nodes(
        &mut self,
        sub_set_indi: NodeId,
        super_set_indi: NodeId,
        clash_descriptors: &mut ClashDescId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // STATINC(INDINODESMERGEABLECONCEPTSETTESTCOUNT, calcAlgContext);
        // KONCLUDE-PORT-NOTE[ownership]: the C++ value params `subSetIndi`/`superSetIndi`
        // are reassigned by the count-swap and then passed by `CIndividualProcessNode*&`
        // to `createClashedConceptDescriptor`; modelled as local `mut` bindings + `&mut`.
        let mut sub_set_indi = sub_set_indi;
        let mut super_set_indi = super_set_indi;

        let mut sub_concept_set = calc_alg_context
            .process_context_mut()
            .node_mut(sub_set_indi)
            .get_reapply_concept_label_set(false);
        let mut super_concept_set = calc_alg_context
            .process_context_mut()
            .node_mut(super_set_indi)
            .get_reapply_concept_label_set(false);

        // if (superConceptSet->getConceptCount() < subConceptSet->getConceptCount()) { swap sets + indis }
        let super_count = calc_alg_context
            .process_context()
            .label_set(super_concept_set)
            .get_concept_count();
        let sub_count = calc_alg_context
            .process_context()
            .label_set(sub_concept_set)
            .get_concept_count();
        if super_count < sub_count {
            std::mem::swap(&mut sub_concept_set, &mut super_concept_set);
            std::mem::swap(&mut sub_set_indi, &mut super_set_indi);
        }

        let sub_con_set_count = calc_alg_context
            .process_context()
            .label_set(sub_concept_set)
            .get_concept_count();
        let super_con_set_count = calc_alg_context
            .process_context()
            .label_set(super_concept_set)
            .get_concept_count();
        let threshold_factor = self.map_comparison_direct_lookup_factor;
        if sub_con_set_count * threshold_factor < super_con_set_count {
            // W6-DEFER[api]: direct-lookup branch (`CReapplyConceptLabelSetIterator` +
            // `getConceptDescriptor(concept, out conDes, out depTrackPoint)`, unported
            // LS-1 stub). Faithful logic:
            //   subConSetIt = subConceptSet->getConceptLabelSetIterator(true,false,false);
            //   while subConSetIt.hasValue():
            //     subConDes = subConSetIt.getConceptDescriptor(); subDepTrackPoint = subConSetIt.getDependencyTrackPoint();
            //     if superConceptSet->getConceptDescriptor(subConDes->getConcept(), superConDes, superDepTrackPoint):
            //       if superConDes->getNegation() != subConDes->getNegation():
            //         clashDescriptors = createClashedConceptDescriptor(clashDescriptors, &subSetIndi, subConDes, subDepTrackPoint, ctx);
            //         clashDescriptors = createClashedConceptDescriptor(clashDescriptors, &superSetIndi, superConDes, superDepTrackPoint, ctx);
            //     subConSetIt.moveNext();
        } else {
            // W6-DEFER[api]: tag-merge branch over both sorted iterators. Faithful logic:
            //   conSet1It = subConceptSet->getConceptLabelSetIterator(true,false,false);
            //   conSet2It = superConceptSet->getConceptLabelSetIterator(true,false,false);
            //   conDes2 = conSet2It.getConceptDescriptor(); depTrackPoint2 = conSet2It.getDependencyTrackPoint();
            //   conTag2 = conDes2->getConceptTag(); conSet2It.moveNext();
            //   while conSet1It.hasValue():
            //     conDes1 = conSet1It.getConceptDescriptor(); depTrackPoint1 = conSet1It.getDependencyTrackPoint(); conTag1 = conDes1->getConceptTag();
            //     while conTag2 < conTag1:
            //       if !conSet2It.hasValue(): return false;
            //       conDes2 = conSet2It.getConceptDescriptor(); depTrackPoint2 = conSet2It.getDependencyTrackPoint(); conTag2 = conDes2->getConceptTag(); conSet2It.moveNext();
            //     if conTag1 == conTag2 && conDes1->isNegated() != conDes2->isNegated():
            //       clashDescriptors = createClashedConceptDescriptor(clashDescriptors, &subSetIndi, conDes1, depTrackPoint1, ctx);
            //       clashDescriptors = createClashedConceptDescriptor(clashDescriptors, &superSetIndi, conDes2, depTrackPoint2, ctx);
            //       return true;   // CLASH (early)
            //     conSet1It.moveNext();
            // (`createClashedConceptDescriptor` is this unit; live once LS-1 iterator lands.)
        }
        let _ = (
            clash_descriptors,
            sub_set_indi,
            super_set_indi,
            calc_alg_context,
        );
        false
    }
}
