//! `process::referred_tracking` — referred-individual dependence tracking.
//!
//! Port of Konclude
//! `Source/Reasoner/Kernel/Process/CReferredIndividualTracking{Data,Vector}.{h,cpp}`.
//! The vector is installed by the algorithm's individual-dependence tracking
//! path and records whether each tracked nominal individual was referred, and
//! whether the reference was extended.

#![allow(dead_code)]

use std::collections::HashSet;

use super::super::model::substrate::{Cint64, Id};

/// Port of `CReferredIndividualTrackingData`.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct ReferredIndividualTrackingData {
    /// `bool mReferred`.
    referred: bool,
    /// `bool mExtended`.
    extended: bool,
}

impl ReferredIndividualTrackingData {
    /// Port of `isReferred`.
    pub fn is_referred(&self) -> bool {
        self.referred
    }

    /// Port of `isExtended`.
    pub fn is_extended(&self) -> bool {
        self.extended
    }

    /// Port of `setReferred`.
    pub fn set_referred(&mut self) -> &mut Self {
        self.referred = true;
        self
    }

    /// Port of `setExtended`.
    pub fn set_extended(&mut self) -> &mut Self {
        self.extended = true;
        self
    }
}

/// Port of `CReferredIndividualTrackingVector`.
#[derive(Debug, Default, Clone)]
pub struct ReferredIndividualTrackingVector {
    /// `CReferredIndividualTrackingData* mIndiTrackVector`.
    indi_track_vector: Vec<ReferredIndividualTrackingData>,
    /// `cint64 mIndiTrackCount`.
    indi_track_count: Cint64,
    /// `cint64 mIndiTrackOffset`.
    indi_track_offset: Cint64,
}

pub type ReferredIndividualTrackingVectorId = Id<ReferredIndividualTrackingVector>;

impl ReferredIndividualTrackingVector {
    /// Port of the default constructor.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `initReferredIndividualTrackingVector(cint64 indiCount, cint64 indiOffset)`.
    pub fn init_referred_individual_tracking_vector(
        &mut self,
        indi_count: Cint64,
        indi_offset: Cint64,
    ) -> &mut Self {
        self.indi_track_count = indi_count.max(0);
        self.indi_track_offset = indi_offset;
        self.indi_track_vector =
            vec![ReferredIndividualTrackingData::default(); self.indi_track_count as usize];
        self
    }

    /// Port of `initReferredIndividualTrackingVector(CReferredIndividualTrackingVector*)`.
    pub fn init_referred_individual_tracking_vector_from(
        &mut self,
        indi_track_vec: &ReferredIndividualTrackingVector,
    ) -> &mut Self {
        self.indi_track_count = indi_track_vec.indi_track_count;
        self.indi_track_offset = indi_track_vec.indi_track_offset;
        self.indi_track_vector = indi_track_vec.indi_track_vector.clone();
        self
    }

    /// Port of `getReferredIndividualTrackingData`.
    pub fn get_referred_individual_tracking_data(
        &self,
        indi_id: Cint64,
    ) -> Option<&ReferredIndividualTrackingData> {
        let corrected_indi_id = indi_id + self.indi_track_offset;
        if corrected_indi_id >= 0 && corrected_indi_id < self.indi_track_count {
            self.indi_track_vector.get(corrected_indi_id as usize)
        } else {
            None
        }
    }

    /// Mutable variant of `getReferredIndividualTrackingData` for setter ports.
    pub fn get_referred_individual_tracking_data_mut(
        &mut self,
        indi_id: Cint64,
    ) -> Option<&mut ReferredIndividualTrackingData> {
        let corrected_indi_id = indi_id + self.indi_track_offset;
        if corrected_indi_id >= 0 && corrected_indi_id < self.indi_track_count {
            self.indi_track_vector.get_mut(corrected_indi_id as usize)
        } else {
            None
        }
    }

    /// Port of `setIndividualReferred`.
    pub fn set_individual_referred(&mut self, indi_id: Cint64) -> &mut Self {
        let lookup_id = indi_id + self.indi_track_offset;
        if let Some(ind_track_data) = self.get_referred_individual_tracking_data_mut(lookup_id) {
            if !ind_track_data.is_referred() {
                ind_track_data.set_referred();
            }
        }
        self
    }

    /// Port of `setIndividualReferredAndExtended`.
    pub fn set_individual_referred_and_extended(&mut self, indi_id: Cint64) -> &mut Self {
        let lookup_id = indi_id + self.indi_track_offset;
        if let Some(ind_track_data) = self.get_referred_individual_tracking_data_mut(lookup_id) {
            if !ind_track_data.is_extended() || !ind_track_data.is_referred() {
                ind_track_data.set_referred().set_extended();
            }
        }
        self
    }

    /// Port of `mergeGatheredTrackedIndividualDependences` for the concrete vector case.
    pub fn merge_gathered_tracked_individual_dependences(
        &mut self,
        indi_dep_tracking: &ReferredIndividualTrackingVector,
    ) -> bool {
        let merge_count = indi_dep_tracking
            .indi_track_count
            .min(self.indi_track_count);
        for i in 0..merge_count as usize {
            let merge_indi_track_data = indi_dep_tracking.indi_track_vector[i];
            let indi_track_data = &mut self.indi_track_vector[i];
            if !indi_track_data.is_extended() && merge_indi_track_data.is_extended() {
                indi_track_data.set_extended();
            }
            if !indi_track_data.is_referred() && merge_indi_track_data.is_referred() {
                indi_track_data.set_referred();
            }
        }
        true
    }

    /// Port of `areIndividualsAffected(QSet<cint64>*, QSet<cint64>*)`.
    pub fn are_individuals_affected(
        &self,
        indirectly_changed_individual_set: &HashSet<Cint64>,
        changed_compatible_set: &HashSet<Cint64>,
    ) -> bool {
        for indi_id in indirectly_changed_individual_set.iter().copied() {
            let corrected = indi_id + self.indi_track_offset;
            if corrected >= 0 && corrected < self.indi_track_count {
                if let Some(indi_track_data) = self.indi_track_vector.get(corrected as usize) {
                    if indi_track_data.is_extended() {
                        return true;
                    }
                    if indi_track_data.is_referred() && !changed_compatible_set.contains(&corrected)
                    {
                        return true;
                    }
                }
            }
        }
        false
    }

    /// Port of `getCopiedIndividualDependencyTracking`.
    pub fn get_copied_individual_dependency_tracking(&self) -> ReferredIndividualTrackingVector {
        let mut copy = ReferredIndividualTrackingVector::new();
        copy.init_referred_individual_tracking_vector_from(self);
        copy
    }

    /// Port of `getDependenceSize`.
    pub fn get_dependence_size(&self) -> Cint64 {
        self.indi_track_vector
            .iter()
            .filter(|data| data.is_referred())
            .count() as Cint64
    }

    pub fn get_individual_track_count(&self) -> Cint64 {
        self.indi_track_count
    }

    pub fn get_individual_track_offset(&self) -> Cint64 {
        self.indi_track_offset
    }
}
