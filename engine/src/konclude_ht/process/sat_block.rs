//! `process::sat_block` — port of `CIndividualNodeSaturationBlockingData`.
//!
//! This tiny process satellite connects a completion-graph individual to the
//! saturation node whose completed label can be used for saturation expansion
//! cache writes.

#![allow(dead_code)]

use super::super::model::substrate::{Cint64, Id};
use super::{ConDescId, SatNodeId};

/// Port of `CIndividualNodeSaturationBlockingData`.
pub struct IndividualNodeSaturationBlockingData {
    /// `cint64 mSaturationBlockedConceptCount`.
    pub saturation_blocked_concept_count: Cint64,
    /// `CConceptDescriptor* mLastConfConDes`.
    pub last_confirmed_concept_descriptor: ConDescId,
    /// `CIndividualSaturationProcessNode* mSaturationNode`.
    pub saturation_node: SatNodeId,
}

impl Default for IndividualNodeSaturationBlockingData {
    fn default() -> Self {
        Self {
            saturation_blocked_concept_count: 0,
            last_confirmed_concept_descriptor: Id::NONE,
            saturation_node: Id::NONE,
        }
    }
}

impl IndividualNodeSaturationBlockingData {
    /// Port of `CIndividualNodeSaturationBlockingData::CIndividualNodeSaturationBlockingData`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `initSaturationBlockingData`.
    pub fn init_saturation_blocking_data(
        &mut self,
        cached_concept_count: Cint64,
        last_confirmed_concept_descriptor: ConDescId,
        saturation_node: SatNodeId,
    ) -> &mut Self {
        self.saturation_blocked_concept_count = cached_concept_count;
        self.last_confirmed_concept_descriptor = last_confirmed_concept_descriptor;
        self.saturation_node = saturation_node;
        self
    }

    /// Port of `setSaturationBlockedConceptCount`.
    pub fn set_saturation_blocked_concept_count(&mut self, cached_count: Cint64) -> &mut Self {
        self.saturation_blocked_concept_count = cached_count;
        self
    }

    /// Port of `getSaturationBlockedConceptCount`.
    pub fn get_saturation_blocked_concept_count(&self) -> Cint64 {
        self.saturation_blocked_concept_count
    }

    /// Port of `getLastConfirmedConceptDescriptior`.
    pub fn get_last_confirmed_concept_descriptior(&self) -> ConDescId {
        self.last_confirmed_concept_descriptor
    }

    /// Port of `getSaturationIndividualNode`.
    pub fn get_saturation_individual_node(&self) -> SatNodeId {
        self.saturation_node
    }
}
