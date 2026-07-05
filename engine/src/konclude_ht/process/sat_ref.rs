//! `process::sat_ref` — minimal saturation concept reference data.
//!
//! Konclude stores `CSaturationConceptDataItem` through the
//! `CExtendedConceptReferenceLinkingData*` field on
//! `CIndividualSaturationProcessNode`. The base class is empty; the concrete
//! item carries the saturation concept tested by
//! `CSaturationNodeExpansionCacheHandler::tryNodeSatisfiableCaching`.

#![allow(dead_code)]

use super::super::model::substrate::{Id, INVALID};
use super::super::model::{Cint64, ConceptId, RoleId};

/// `CExtendedConceptReferenceLinkingData*` / `CSaturationConceptDataItem*`.
pub type ExtendedConceptReferenceLinkingDataId = Id<ExtendedConceptReferenceLinkingData>;

/// Port of the data needed from `CSaturationConceptDataItem`.
pub struct ExtendedConceptReferenceLinkingData {
    /// `CSaturationConceptDataItem::mConceptSat`.
    pub saturation_concept: ConceptId,
    /// `CSaturationConceptDataItem::mNegation`.
    pub saturation_negation: bool,
    /// `CSaturationConceptDataItem::mRoleRanges`.
    pub saturation_role_ranges: RoleId,
    /// `CSaturationConceptDataItem::mConRefLinking`.
    ///
    /// The concrete concept-reference-linking object is still outside this Rust
    /// slice, so this remains an opaque handle.
    pub concept_reference_linking: Cint64,
}

impl Default for ExtendedConceptReferenceLinkingData {
    fn default() -> Self {
        Self {
            saturation_concept: ConceptId::NONE,
            saturation_negation: false,
            saturation_role_ranges: RoleId::NONE,
            concept_reference_linking: INVALID,
        }
    }
}

impl ExtendedConceptReferenceLinkingData {
    /// Port of `CSaturationConceptDataItem::CSaturationConceptDataItem`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `initConceptSaturationTestingItem`.
    pub fn init_concept_saturation_testing_item(
        &mut self,
        sat_test_concept: ConceptId,
        negated: bool,
        role: RoleId,
    ) -> &mut Self {
        self.saturation_concept = sat_test_concept;
        self.saturation_negation = negated;
        self.saturation_role_ranges = role;
        self.concept_reference_linking = INVALID;
        self
    }

    /// Port of `getSaturationConcept`.
    pub fn get_saturation_concept(&self) -> ConceptId {
        self.saturation_concept
    }

    /// Port of `getSaturationRoleRanges`.
    pub fn get_saturation_role_ranges(&self) -> RoleId {
        self.saturation_role_ranges
    }

    /// Port of `getSaturationNegation`.
    pub fn get_saturation_negation(&self) -> bool {
        self.saturation_negation
    }

    /// Port of `getConceptReferenceLinking`.
    pub fn get_concept_reference_linking(&self) -> Cint64 {
        self.concept_reference_linking
    }

    /// Port of `setConceptReferenceLinking`.
    pub fn set_concept_reference_linking(&mut self, ref_linking: Cint64) -> &mut Self {
        self.concept_reference_linking = ref_linking;
        self
    }
}
