//! `model::concept_process` — concept process/reference-linking data used by
//! saturation-backed completion lookups.
//!
//! Ports the small part of Konclude's `Reasoner/Ontology/` concept process data
//! and saturation reference-linking classes that connects a `CConcept` to the
//! `CIndividualSaturationProcessNode` produced by the saturation pre-pass.

#![allow(dead_code)]

use super::substrate::{Cint64, Id, NegLink, INVALID};
use super::{ConceptId, RoleId};
use crate::konclude_ht::process::SatNodeId;

/// `CConceptProcessData*` → `ConceptProcessDataId`.
pub type ConceptProcessDataId = Id<ConceptProcessData>;
/// `CUnsatisfiableCachingTags*` → `UnsatisfiableCachingTagsId`.
pub type UnsatisfiableCachingTagsId = Id<UnsatisfiableCachingTags>;
/// `CConceptSaturationReferenceLinkingData*` → `ConceptSaturationReferenceLinkingDataId`.
pub type ConceptSaturationReferenceLinkingDataId = Id<ConceptSaturationReferenceLinkingData>;
/// `CSaturationConceptReferenceLinking*` → `SaturationConceptReferenceLinkingId`.
pub type SaturationConceptReferenceLinkingId = Id<SaturationConceptReferenceLinking>;
/// `CReplacementData*` → `ReplacementDataId`.
pub type ReplacementDataId = Id<ReplacementData>;

/// Port of Konclude `CReplacementData`.
#[derive(Clone, Debug)]
pub struct ReplacementData {
    pub implication_replacement_concept: ConceptId,
    pub common_disjunct_concepts: Vec<NegLink<ConceptId>>,
}

impl Default for ReplacementData {
    fn default() -> Self {
        Self {
            implication_replacement_concept: Id::NONE,
            common_disjunct_concepts: Vec::new(),
        }
    }
}

impl ReplacementData {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn init_replacement_data(&mut self, previous: Option<&Self>) -> &mut Self {
        if let Some(previous) = previous {
            self.implication_replacement_concept = previous.implication_replacement_concept;
            self.common_disjunct_concepts = previous.common_disjunct_concepts.clone();
        } else {
            self.implication_replacement_concept = Id::NONE;
            self.common_disjunct_concepts.clear();
        }
        self
    }
}

/// Port of `CCachingTags`.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct CachingTags {
    /// `CCachingTags::mLastCachingTag`.
    pub last_caching_tag: Cint64,
    /// `CCachingTags::mMaxCachedTag`.
    pub max_cached_tag: Cint64,
    /// `CCachingTags::mMinCachedTag`.
    pub min_cached_tag: Cint64,
}

impl Default for CachingTags {
    fn default() -> Self {
        Self {
            last_caching_tag: 0,
            max_cached_tag: Cint64::MIN,
            min_cached_tag: Cint64::MAX,
        }
    }
}

impl CachingTags {
    /// Port of `CCachingTags::CCachingTags`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `getLastCachingTag`.
    pub fn get_last_caching_tag(&self) -> Cint64 {
        self.last_caching_tag
    }

    /// Port of `getMaxCachedTag`.
    pub fn get_max_cached_tag(&self) -> Cint64 {
        self.max_cached_tag
    }

    /// Port of `getMinCachedTag`.
    pub fn get_min_cached_tag(&self) -> Cint64 {
        self.min_cached_tag
    }

    /// Port of `setLastCachingTag`.
    pub fn set_last_caching_tag(&mut self, tag: Cint64) -> &mut Self {
        self.last_caching_tag = tag;
        self
    }

    /// Port of `setMaxCachedTag`.
    pub fn set_max_cached_tag(&mut self, tag: Cint64) -> &mut Self {
        self.max_cached_tag = tag;
        self
    }

    /// Port of `setMinCachedTag`.
    pub fn set_min_cached_tag(&mut self, tag: Cint64) -> &mut Self {
        self.min_cached_tag = tag;
        self
    }

    /// Port of `setMaxCachedTagCandidate`.
    pub fn set_max_cached_tag_candidate(&mut self, tag: Cint64) -> bool {
        if tag > self.max_cached_tag {
            self.max_cached_tag = tag;
            true
        } else {
            false
        }
    }

    /// Port of `setMinCachedTagCandidate`.
    pub fn set_min_cached_tag_candidate(&mut self, tag: Cint64) -> bool {
        if tag < self.min_cached_tag {
            self.min_cached_tag = tag;
            true
        } else {
            false
        }
    }
}

/// Port of `CUnsatisfiableCachingTags`.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct UnsatisfiableCachingTags {
    /// `CCachingTags` base subobject.
    pub base: CachingTags,
    /// `CUnsatisfiableCachingTags::mMinUnsatCachedSize`.
    pub min_unsat_cached_size: Cint64,
}

impl Default for UnsatisfiableCachingTags {
    fn default() -> Self {
        Self {
            base: CachingTags::new(),
            min_unsat_cached_size: Cint64::MAX,
        }
    }
}

impl UnsatisfiableCachingTags {
    /// Port of `CUnsatisfiableCachingTags::CUnsatisfiableCachingTags`.
    pub fn new() -> Self {
        Self::default()
    }

    pub fn get_last_caching_tag(&self) -> Cint64 {
        self.base.get_last_caching_tag()
    }

    pub fn get_max_cached_tag(&self) -> Cint64 {
        self.base.get_max_cached_tag()
    }

    pub fn get_min_cached_tag(&self) -> Cint64 {
        self.base.get_min_cached_tag()
    }

    pub fn set_last_caching_tag(&mut self, tag: Cint64) -> &mut Self {
        self.base.set_last_caching_tag(tag);
        self
    }

    pub fn set_max_cached_tag(&mut self, tag: Cint64) -> &mut Self {
        self.base.set_max_cached_tag(tag);
        self
    }

    pub fn set_min_cached_tag(&mut self, tag: Cint64) -> &mut Self {
        self.base.set_min_cached_tag(tag);
        self
    }

    pub fn set_max_cached_tag_candidate(&mut self, tag: Cint64) -> bool {
        self.base.set_max_cached_tag_candidate(tag)
    }

    pub fn set_min_cached_tag_candidate(&mut self, tag: Cint64) -> bool {
        self.base.set_min_cached_tag_candidate(tag)
    }

    /// Port of `getMinUnsatisfiableCachedSize`.
    pub fn get_min_unsatisfiable_cached_size(&self) -> Cint64 {
        self.min_unsat_cached_size
    }

    /// Port of `setMinUnsatisfiableCachedSize`.
    pub fn set_min_unsatisfiable_cached_size(&mut self, size: Cint64) -> &mut Self {
        self.min_unsat_cached_size = size;
        self
    }

    /// Port of `setMinUnsatisfiableCachedSizeCandidate`.
    pub fn set_min_unsatisfiable_cached_size_candidate(&mut self, size: Cint64) -> bool {
        if size < self.min_unsat_cached_size {
            self.min_unsat_cached_size = size;
            true
        } else {
            false
        }
    }

    /// Port of `updateCachingTags`.
    pub fn update_caching_tags(
        &mut self,
        cached_tag_candidate: Cint64,
        caching_number_tag: Cint64,
        size_candidate: Cint64,
    ) -> bool {
        let mut changed = false;
        changed |= self.set_min_unsatisfiable_cached_size_candidate(size_candidate);
        changed |= self.set_max_cached_tag_candidate(cached_tag_candidate);
        changed |= self.set_min_cached_tag_candidate(cached_tag_candidate);
        self.set_last_caching_tag(caching_number_tag);
        changed
    }

    /// Port of `candidateTags`.
    pub fn candidate_tags(
        &self,
        min_max_cached_tag: &mut Cint64,
        max_min_cached_tag: &mut Cint64,
        min_unsat_cached_size: &mut Cint64,
        required_last_caching_tag: Cint64,
    ) -> bool {
        if self.base.last_caching_tag >= required_last_caching_tag {
            *min_max_cached_tag = (*min_max_cached_tag).min(self.base.max_cached_tag);
            *max_min_cached_tag = (*max_min_cached_tag).max(self.base.min_cached_tag);
            *min_unsat_cached_size = (*min_unsat_cached_size).min(self.min_unsat_cached_size);
            true
        } else {
            false
        }
    }

    /// Port of `hasCandidateTags`.
    pub fn has_candidate_tags(
        &self,
        min_max_cached_tag: Cint64,
        max_min_cached_tag: Cint64,
        required_last_caching_tag: Cint64,
    ) -> bool {
        self.base.last_caching_tag >= required_last_caching_tag
            && (min_max_cached_tag == self.base.max_cached_tag
                || max_min_cached_tag == self.base.min_cached_tag)
    }

    /// Port of `candidateMinUnsatisfiableSize`.
    pub fn candidate_min_unsatisfiable_size(
        &self,
        min_unsat_cached_size: &mut Cint64,
        cached_tag: Cint64,
    ) -> bool {
        if self.base.min_cached_tag == cached_tag && self.base.max_cached_tag == cached_tag {
            *min_unsat_cached_size = (*min_unsat_cached_size).min(self.min_unsat_cached_size);
            true
        } else {
            false
        }
    }
}

/// Port of `CConceptProcessData`.
///
/// KONCLUDE-PORT-NOTE[ownership]: this ports the fields needed by the completion
/// and saturation reference-linking call chain. Other pointers on the C++ class
/// stay opaque `Cint64` handles until their owning subsystems are ported.
pub struct ConceptProcessData {
    /// `CConceptProcessData::mConceptRoleBranchTrigger`.
    pub concept_role_branch_trigger: Cint64,
    /// `CConceptProcessData::mReplacementData`.
    pub replacement_data: ReplacementDataId,
    /// `CConceptProcessData::mUnsatCachingTags[2]`.
    pub unsat_caching_tags: [Cint64; 2],
    /// `CConceptProcessData::mRefLinking`.
    pub concept_reference_linking: ConceptSaturationReferenceLinkingDataId,
    /// `CConceptProcessData::mInvalidatedRefLinking`.
    pub invalidated_reference_linking: bool,
    /// `CConceptProcessData::mPropagationIntoCreationDirection`.
    pub propagation_into_creation_direction: bool,
    /// `CConceptProcessData::mInferRelevantFlag`.
    pub infer_relevant_flag: bool,
    /// `CConceptProcessData::mCoreConceptFlags[2]`.
    pub core_concept_flags: [bool; 2],
    /// `CConceptProcessData::mBranchingStatistics`.
    pub branching_statistics: Cint64,
}

impl Default for ConceptProcessData {
    fn default() -> Self {
        ConceptProcessData {
            concept_role_branch_trigger: INVALID,
            replacement_data: Id::NONE,
            unsat_caching_tags: [INVALID, INVALID],
            concept_reference_linking: ConceptSaturationReferenceLinkingDataId::NONE,
            invalidated_reference_linking: false,
            propagation_into_creation_direction: false,
            infer_relevant_flag: false,
            core_concept_flags: [false, false],
            branching_statistics: INVALID,
        }
    }
}

impl ConceptProcessData {
    /// Port of `CConceptProcessData::CConceptProcessData`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `initConceptProcessExtensionData`.
    pub fn init_concept_process_extension_data(
        &mut self,
        concept_role_branch_trigger: Cint64,
        replacement_data: ReplacementDataId,
    ) -> &mut Self {
        self.concept_role_branch_trigger = concept_role_branch_trigger;
        self.replacement_data = replacement_data;
        self
    }

    /// Port of `getReplacementData`.
    pub fn get_replacement_data(&self) -> ReplacementDataId {
        self.replacement_data
    }

    /// Port of `setReplacementData`.
    pub fn set_replacement_data(&mut self, replacement_data: ReplacementDataId) -> &mut Self {
        self.replacement_data = replacement_data;
        self
    }

    /// Port of `getConceptReferenceLinking`.
    pub fn get_concept_reference_linking(&self) -> ConceptSaturationReferenceLinkingDataId {
        self.concept_reference_linking
    }

    /// Port of `setConceptReferenceLinking`.
    pub fn set_concept_reference_linking(
        &mut self,
        ref_linking: ConceptSaturationReferenceLinkingDataId,
    ) -> &mut Self {
        self.concept_reference_linking = ref_linking;
        self
    }

    /// Port of `isInvalidatedReferenceLinking`.
    pub fn is_invalidated_reference_linking(&self) -> bool {
        self.invalidated_reference_linking
    }

    /// Port of `setInvalidatedReferenceLinking`.
    pub fn set_invalidated_reference_linking(
        &mut self,
        invalidated_reference_linking: bool,
    ) -> &mut Self {
        self.invalidated_reference_linking = invalidated_reference_linking;
        self
    }

    /// Port of `getUnsatisfiableCachingTags`.
    pub fn get_unsatisfiable_caching_tags(
        &self,
        concept_negation: bool,
    ) -> UnsatisfiableCachingTagsId {
        Id::new(self.unsat_caching_tags[concept_negation as usize])
    }

    /// Port of `hasUnsatisfiableCachingTags`.
    pub fn has_unsatisfiable_caching_tags(&self, concept_negation: bool) -> bool {
        self.get_unsatisfiable_caching_tags(concept_negation)
            .is_some()
    }

    /// Port of `setUnsatisfiableCachingTags`.
    pub fn set_unsatisfiable_caching_tags(
        &mut self,
        concept_negation: bool,
        tags: UnsatisfiableCachingTagsId,
    ) -> &mut Self {
        self.unsat_caching_tags[concept_negation as usize] = tags.raw;
        self
    }

    /// Port of `isCoreBlockingConcept`.
    pub fn is_core_blocking_concept(&self, negated: bool) -> bool {
        self.core_concept_flags[negated as usize]
    }

    /// Port of `setCoreBlockingConcept`.
    pub fn set_core_blocking_concept(
        &mut self,
        negated: bool,
        core_blocking_concept: bool,
    ) -> &mut Self {
        self.core_concept_flags[negated as usize] = core_blocking_concept;
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn caching_tags_defaults_match_konclude() {
        let tags = UnsatisfiableCachingTags::new();
        assert_eq!(tags.get_last_caching_tag(), 0);
        assert_eq!(tags.get_min_cached_tag(), Cint64::MAX);
        assert_eq!(tags.get_max_cached_tag(), Cint64::MIN);
        assert_eq!(tags.get_min_unsatisfiable_cached_size(), Cint64::MAX);
    }

    #[test]
    fn unsat_caching_tags_update_matches_konclude() {
        let mut tags = UnsatisfiableCachingTags::new();
        assert!(tags.update_caching_tags(7, 3, 2));
        assert_eq!(tags.get_min_cached_tag(), 7);
        assert_eq!(tags.get_max_cached_tag(), 7);
        assert_eq!(tags.get_last_caching_tag(), 3);
        assert_eq!(tags.get_min_unsatisfiable_cached_size(), 2);

        assert!(!tags.update_caching_tags(7, 4, 5));
        assert_eq!(tags.get_min_cached_tag(), 7);
        assert_eq!(tags.get_max_cached_tag(), 7);
        assert_eq!(tags.get_last_caching_tag(), 4);
        assert_eq!(tags.get_min_unsatisfiable_cached_size(), 2);
    }

    #[test]
    fn candidate_tags_respects_required_last_caching_tag() {
        let mut tags = UnsatisfiableCachingTags::new();
        tags.update_caching_tags(7, 3, 2);

        let mut min_max_cached_tag = 100;
        let mut max_min_cached_tag = 0;
        let mut min_unsat_cached_size = 100;
        assert!(!tags.candidate_tags(
            &mut min_max_cached_tag,
            &mut max_min_cached_tag,
            &mut min_unsat_cached_size,
            4
        ));
        assert_eq!(min_max_cached_tag, 100);
        assert_eq!(max_min_cached_tag, 0);
        assert_eq!(min_unsat_cached_size, 100);

        assert!(tags.candidate_tags(
            &mut min_max_cached_tag,
            &mut max_min_cached_tag,
            &mut min_unsat_cached_size,
            3
        ));
        assert_eq!(min_max_cached_tag, 7);
        assert_eq!(max_min_cached_tag, 7);
        assert_eq!(min_unsat_cached_size, 2);
        assert!(tags.has_candidate_tags(7, 0, 3));
        assert!(tags.has_candidate_tags(100, 7, 3));
        assert!(!tags.has_candidate_tags(100, 0, 3));

        let mut candidate_size = 100;
        assert!(tags.candidate_min_unsatisfiable_size(&mut candidate_size, 7));
        assert_eq!(candidate_size, 2);
        assert!(!tags.candidate_min_unsatisfiable_size(&mut candidate_size, 8));
    }

    #[test]
    fn concept_process_data_unsat_tag_slots_are_polarity_specific() {
        let mut data = ConceptProcessData::new();
        let pos = UnsatisfiableCachingTagsId::new(3);
        let neg = UnsatisfiableCachingTagsId::new(5);

        assert!(!data.has_unsatisfiable_caching_tags(false));
        assert!(!data.has_unsatisfiable_caching_tags(true));

        data.set_unsatisfiable_caching_tags(false, pos);
        assert_eq!(data.get_unsatisfiable_caching_tags(false), pos);
        assert_eq!(
            data.get_unsatisfiable_caching_tags(true),
            UnsatisfiableCachingTagsId::NONE
        );
        assert!(data.has_unsatisfiable_caching_tags(false));
        assert!(!data.has_unsatisfiable_caching_tags(true));

        data.set_unsatisfiable_caching_tags(true, neg);
        assert_eq!(data.get_unsatisfiable_caching_tags(false), pos);
        assert_eq!(data.get_unsatisfiable_caching_tags(true), neg);
        assert!(data.has_unsatisfiable_caching_tags(true));
    }

    #[test]
    fn concept_process_data_core_blocking_flags_are_polarity_specific() {
        let mut data = ConceptProcessData::new();
        assert!(!data.is_core_blocking_concept(false));
        assert!(!data.is_core_blocking_concept(true));

        data.set_core_blocking_concept(false, true);
        assert!(data.is_core_blocking_concept(false));
        assert!(!data.is_core_blocking_concept(true));

        data.set_core_blocking_concept(true, true);
        data.set_core_blocking_concept(false, false);
        assert!(!data.is_core_blocking_concept(false));
        assert!(data.is_core_blocking_concept(true));
    }
}

/// Port of `CConceptSaturationReferenceLinkingData`.
pub struct ConceptSaturationReferenceLinkingData {
    /// `CConceptSaturationReferenceLinkingData::mPositiveSatConRefLinking`.
    pub positive_sat_con_ref_linking: SaturationConceptReferenceLinkingId,
    /// `CConceptSaturationReferenceLinkingData::mNegativeSatConRefLinking`.
    pub negative_sat_con_ref_linking: SaturationConceptReferenceLinkingId,
    /// `CConceptSaturationReferenceLinkingData::mExistentialSuccessorSatConRefLinking`.
    pub existential_successor_sat_con_ref_linking: SaturationConceptReferenceLinkingId,
    /// `CConceptSatisfiableReferenceLinkingData::mClassRefLinkData`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: C++ stores this as a
    /// `CClassificationConceptReferenceLinking*`. The model layer keeps the
    /// payload opaque so classifier-specific ids do not leak back into ontology
    /// reference-linking data.
    pub classifier_reference_linking_data: Cint64,
}

impl Default for ConceptSaturationReferenceLinkingData {
    fn default() -> Self {
        ConceptSaturationReferenceLinkingData {
            positive_sat_con_ref_linking: SaturationConceptReferenceLinkingId::NONE,
            negative_sat_con_ref_linking: SaturationConceptReferenceLinkingId::NONE,
            existential_successor_sat_con_ref_linking: SaturationConceptReferenceLinkingId::NONE,
            classifier_reference_linking_data: INVALID,
        }
    }
}

impl ConceptSaturationReferenceLinkingData {
    /// Port of `CConceptSaturationReferenceLinkingData::CConceptSaturationReferenceLinkingData`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `getPositiveConceptSaturationReferenceLinkingData`.
    pub fn get_positive_concept_saturation_reference_linking_data(
        &self,
    ) -> SaturationConceptReferenceLinkingId {
        self.positive_sat_con_ref_linking
    }

    /// Port of `setPositiveSaturationReferenceLinkingData`.
    pub fn set_positive_saturation_reference_linking_data(
        &mut self,
        sat_con_ref_linking: SaturationConceptReferenceLinkingId,
    ) -> &mut Self {
        self.positive_sat_con_ref_linking = sat_con_ref_linking;
        self
    }

    /// Port of `getNegativeConceptSaturationReferenceLinkingData`.
    pub fn get_negative_concept_saturation_reference_linking_data(
        &self,
    ) -> SaturationConceptReferenceLinkingId {
        self.negative_sat_con_ref_linking
    }

    /// Port of `setNegativeSaturationReferenceLinkingData`.
    pub fn set_negative_saturation_reference_linking_data(
        &mut self,
        sat_con_ref_linking: SaturationConceptReferenceLinkingId,
    ) -> &mut Self {
        self.negative_sat_con_ref_linking = sat_con_ref_linking;
        self
    }

    /// Port of `setSaturationReferenceLinkingData`.
    pub fn set_saturation_reference_linking_data(
        &mut self,
        sat_con_ref_linking: SaturationConceptReferenceLinkingId,
        negated: bool,
    ) -> &mut Self {
        if !negated {
            self.positive_sat_con_ref_linking = sat_con_ref_linking;
        } else {
            self.negative_sat_con_ref_linking = sat_con_ref_linking;
        }
        self
    }

    /// Port of `getConceptSaturationReferenceLinkingData`.
    pub fn get_concept_saturation_reference_linking_data(
        &self,
        negated: bool,
    ) -> SaturationConceptReferenceLinkingId {
        if !negated {
            self.positive_sat_con_ref_linking
        } else {
            self.negative_sat_con_ref_linking
        }
    }

    /// Port of `getExistentialSuccessorConceptSaturationReferenceLinkingData`.
    pub fn get_existential_successor_concept_saturation_reference_linking_data(
        &self,
    ) -> SaturationConceptReferenceLinkingId {
        self.existential_successor_sat_con_ref_linking
    }

    /// Port of `setExistentialSuccessorConceptSaturationReferenceLinkingData`.
    pub fn set_existential_successor_concept_saturation_reference_linking_data(
        &mut self,
        sat_con_ref_linking: SaturationConceptReferenceLinkingId,
    ) -> &mut Self {
        self.existential_successor_sat_con_ref_linking = sat_con_ref_linking;
        self
    }

    /// Port of `CConceptSatisfiableReferenceLinkingData::getClassifierReferenceLinkingData`.
    pub fn get_classifier_reference_linking_data(&self) -> Cint64 {
        self.classifier_reference_linking_data
    }

    /// Port of `CConceptSatisfiableReferenceLinkingData::setClassifierReferenceLinkingData`.
    pub fn set_classifier_reference_linking_data(
        &mut self,
        class_ref_link_data: Cint64,
    ) -> &mut Self {
        self.classifier_reference_linking_data = class_ref_link_data;
        self
    }
}

/// Port of `CSaturationConceptDataItem::SATURATIONITEMREFERENCESPECIALMODE`
/// (`Reasoner/Consistiser/CSaturationConceptDataItem.h` line 91).
pub const SATURATION_NONE_MODE: Cint64 = 0;
/// `SATURATIONCOPYMODE`.
pub const SATURATION_COPY_MODE: Cint64 = 1;
/// `SATURATIONSUBSTITUTEMODE`.
pub const SATURATION_SUBSTITUTE_MODE: Cint64 = 2;

/// Port of `CSaturationConceptReferenceLinking` FLATTENED with its only concrete
/// subclass `CSaturationConceptDataItem` (Consistiser). Konclude always allocates
/// the derived item (`CTotallyPrecomputationThread::createConceptSaturationProcessingJob`)
/// and downcasts at the use sites (`initializeInitializationConcepts` cpp 5475-5476);
/// the port stores the item fields directly on the linking so no downcast seam is
/// needed.
pub struct SaturationConceptReferenceLinking {
    /// `CSaturationConceptReferenceLinking::mPotentiallyExistInitConcept`.
    pub potentially_exist_init_concept: bool,
    /// `CSaturationConceptReferenceLinking::mDataRangeConcept`.
    pub data_range_concept: bool,
    /// `CSaturationConceptReferenceLinking::mIndiProcessNodeForConcept`.
    pub individual_process_node_for_concept: SatNodeId,
    /// `CSaturationConceptDataItem::mSaturationConcept` — the init concept.
    pub saturation_concept: ConceptId,
    /// `CSaturationConceptDataItem::mSaturationNegation`.
    pub saturation_negation: bool,
    /// `CSaturationConceptDataItem::mSaturationRoleRanges` (`CRole*`; NONE = no
    /// role-successor ranges item).
    pub saturation_role_ranges: RoleId,
    /// `CSaturationConceptDataItem::mSpecialItemReference` — the reference ITEM
    /// whose node substitution/copy starts from (id of another linking).
    pub special_item_reference: SaturationConceptReferenceLinkingId,
    /// `CSaturationConceptDataItem::mSpecialReferenceMode`
    /// (`SATURATION_{NONE,COPY,SUBSTITUTE}_MODE`).
    pub special_reference_mode: Cint64,
}

impl Default for SaturationConceptReferenceLinking {
    fn default() -> Self {
        SaturationConceptReferenceLinking {
            potentially_exist_init_concept: false,
            data_range_concept: false,
            individual_process_node_for_concept: SatNodeId::NONE,
            saturation_concept: ConceptId::NONE,
            saturation_negation: false,
            saturation_role_ranges: RoleId::NONE,
            special_item_reference: SaturationConceptReferenceLinkingId::NONE,
            special_reference_mode: SATURATION_NONE_MODE,
        }
    }
}

impl SaturationConceptReferenceLinking {
    /// Port of `CSaturationConceptReferenceLinking::CSaturationConceptReferenceLinking`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `isPotentiallyExistInitializationConcept`.
    pub fn is_potentially_exist_initialization_concept(&self) -> bool {
        self.potentially_exist_init_concept
    }

    /// Port of `setPotentiallyExistInitializationConcept`.
    pub fn set_potentially_exist_initialization_concept(
        &mut self,
        init_concept: bool,
    ) -> &mut Self {
        self.potentially_exist_init_concept = init_concept;
        self
    }

    /// Port of `isDataRangeConcept`.
    pub fn is_data_range_concept(&self) -> bool {
        self.data_range_concept
    }

    /// Port of `setDataRangeConcept`.
    pub fn set_data_range_concept(&mut self, data_range_concept: bool) -> &mut Self {
        self.data_range_concept = data_range_concept;
        self
    }

    /// Port of `getIndividualProcessNodeForConcept`.
    pub fn get_individual_process_node_for_concept(&self) -> SatNodeId {
        self.individual_process_node_for_concept
    }

    /// Port of `setIndividualProcessNodeForConcept`.
    pub fn set_individual_process_node_for_concept(&mut self, indi_node: SatNodeId) -> &mut Self {
        self.individual_process_node_for_concept = indi_node;
        self
    }

    // --- CSaturationConceptDataItem accessors (flattened subclass; see the
    // struct doc) ---

    /// Port of `CSaturationConceptDataItem::initConceptSaturationTestingItem`.
    pub fn init_concept_saturation_testing_item(
        &mut self,
        concept: ConceptId,
        negation: bool,
        role_ranges: RoleId,
    ) -> &mut Self {
        self.saturation_concept = concept;
        self.saturation_negation = negation;
        self.saturation_role_ranges = role_ranges;
        self.special_item_reference = SaturationConceptReferenceLinkingId::NONE;
        self.special_reference_mode = SATURATION_NONE_MODE;
        self
    }

    /// Port of `CSaturationConceptDataItem::getSaturationConcept`.
    pub fn get_saturation_concept(&self) -> ConceptId {
        self.saturation_concept
    }

    /// Port of `CSaturationConceptDataItem::getSaturationNegation`.
    pub fn get_saturation_negation(&self) -> bool {
        self.saturation_negation
    }

    /// Port of `CSaturationConceptDataItem::getSaturationRoleRanges`.
    pub fn get_saturation_role_ranges(&self) -> RoleId {
        self.saturation_role_ranges
    }

    /// Port of `CSaturationConceptDataItem::getSpecialItemReference`.
    pub fn get_special_item_reference(&self) -> SaturationConceptReferenceLinkingId {
        self.special_item_reference
    }

    /// Port of `CSaturationConceptDataItem::setSpecialItemReference`.
    pub fn set_special_item_reference(
        &mut self,
        item: SaturationConceptReferenceLinkingId,
    ) -> &mut Self {
        self.special_item_reference = item;
        self
    }

    /// Port of `CSaturationConceptDataItem::getSpecialReferenceMode`.
    pub fn get_special_reference_mode(&self) -> Cint64 {
        self.special_reference_mode
    }

    /// Port of `CSaturationConceptDataItem::setSpecialItemReferenceMode`.
    pub fn set_special_item_reference_mode(&mut self, mode: Cint64) -> &mut Self {
        self.special_reference_mode = mode;
        self
    }
}
