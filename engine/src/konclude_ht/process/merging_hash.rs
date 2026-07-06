//! `process::merging_hash` — the per-node individual-merging hash that the merge
//! / nominal-expansion path (`completion/u17.rs` `getIndividualMergingHash`)
//! reaches into.
//!
//! Port of `Source/Reasoner/Kernel/Process/CIndividualMergingHash.{h,cpp}` +
//! `CIndividualMergingHashData.{h,cpp}`.
//!
//! KONCLUDE-PORT-NOTE[ownership]: `CIndividualMergingHash : public
//! CPROCESSHASH<cint64, CIndividualMergingHashData>` (a Qt hash subclass) becomes
//! a wrapper struct owning a `HashMap<Cint64, IndividualMergingHashData>`; the
//! `CXLinker<cint64>* mMergedIndividualLinker` intrusive chain becomes an owned
//! head-front `Vec<Cint64>` (PORT.md §6). `CIndividualMergingHashData :
//! CDependencyTracker` folds the dependency-track-point base in as a field, and
//! holds a `CCondensedReapplyQueue` by value.

#![allow(dead_code)]

use std::collections::HashMap;

use super::super::model::substrate::{Cint64, Id};
use super::condensed_reapply::CondensedReapplyQueue;
use super::TrackPointId;

/// `CIndividualMergingHash*` → `IndividualMergingHashId` (re-aliased from
/// `process::stubs` onto this real struct, the W2.7 pattern).
pub type IndividualMergingHashId = Id<IndividualMergingHash>;

// ===========================================================================
// CIndividualMergingHashData
// ===========================================================================

/// Port of `CIndividualMergingHashData` (`: public CDependencyTracker`) — the
/// per-individual value of the merging hash.
#[derive(Clone)]
pub struct IndividualMergingHashData {
    // --- base CDependencyTracker ---
    /// `CDependencyTrackPoint* mDependencyTrackPoint`.
    pub dependency_track_point: TrackPointId,
    // --- own fields ---
    /// `CCondensedReapplyQueue mReapplyQueue` (held by value).
    pub reapply_queue: CondensedReapplyQueue,
    /// `bool mMergedIndi`.
    pub merged_indi: bool,
}

impl Default for IndividualMergingHashData {
    /// Port of `CIndividualMergingHashData::CIndividualMergingHashData()`
    /// (`mMergedIndi = false;`).
    fn default() -> Self {
        IndividualMergingHashData {
            dependency_track_point: Id::NONE,
            reapply_queue: CondensedReapplyQueue::new(),
            merged_indi: false,
        }
    }
}

impl IndividualMergingHashData {
    /// Port of the default ctor.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `initIndividualMergingHashData(CIndividualMergingHashData* indiMergingHashData)`.
    pub fn init_individual_merging_hash_data(
        &mut self,
        indi_merging_hash_data: Option<&IndividualMergingHashData>,
    ) -> &mut Self {
        if let Some(prev) = indi_merging_hash_data {
            self.dependency_track_point = prev.dependency_track_point;
            let prev_queue = prev.reapply_queue;
            self.reapply_queue.init_reapply_queue(Some(&prev_queue));
            self.merged_indi = prev.merged_indi;
        } else {
            self.dependency_track_point = Id::NONE;
            self.reapply_queue.init_reapply_queue(None);
            self.merged_indi = false;
        }
        self
    }

    /// Port of `getReapplyQueue` (`return &mReapplyQueue;`).
    pub fn get_reapply_queue(&self) -> &CondensedReapplyQueue {
        &self.reapply_queue
    }
    /// Mutable access to the value-held reapply queue.
    pub fn get_reapply_queue_mut(&mut self) -> &mut CondensedReapplyQueue {
        &mut self.reapply_queue
    }

    /// Port of `isMergedWithIndividual` (`return mMergedIndi;`).
    pub fn is_merged_with_individual(&self) -> bool {
        self.merged_indi
    }
    /// Port of `setMergedWithIndividual(bool merged)`.
    pub fn set_merged_with_individual(&mut self, merged: bool) -> &mut Self {
        self.merged_indi = merged;
        self
    }

    /// Port of `CDependencyTracker::getDependencyTrackPoint`.
    pub fn get_dependency_track_point(&self) -> TrackPointId {
        self.dependency_track_point
    }
    /// Port of `CDependencyTracker::setDependencyTrackPoint`.
    pub fn set_dependency_track_point(&mut self, track_point: TrackPointId) -> &mut Self {
        self.dependency_track_point = track_point;
        self
    }
}

// ===========================================================================
// CIndividualMergingHash
// ===========================================================================

/// Port of `CIndividualMergingHash` (`: public CPROCESSHASH<cint64,
/// CIndividualMergingHashData>`).
#[derive(Clone)]
pub struct IndividualMergingHash {
    /// The Qt-hash base content (`cint64` individual id → merging data).
    indi_merging_hash: HashMap<Cint64, IndividualMergingHashData>,
    /// `CXLinker<cint64>* mMergedIndividualLinker` → owned head-front `Vec`.
    merged_individual_linker: Vec<Cint64>,
    /// `cint64 mMergedIndividualCount`.
    merged_individual_count: Cint64,
}

impl Default for IndividualMergingHash {
    fn default() -> Self {
        IndividualMergingHash {
            indi_merging_hash: HashMap::new(),
            merged_individual_linker: Vec::new(),
            merged_individual_count: 0,
        }
    }
}

impl IndividualMergingHash {
    /// Port of `CIndividualMergingHash::CIndividualMergingHash(CProcessContext*)`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `initIndividualMergingHash(CIndividualMergingHash* indiMergingHash)`.
    /// KONCLUDE-PORT-NOTE[ownership]: the C++ `*this = *indiMergingHash` (implicitly
    /// shared Qt-hash copy) becomes a clone; the linker/count are copied as in the
    /// original (the `*this = …` already copies them, then they are reassigned —
    /// the reassignment is faithful, the prior assign is a no-op clone).
    pub fn init_individual_merging_hash(
        &mut self,
        indi_merging_hash: Option<&IndividualMergingHash>,
    ) -> &mut Self {
        if let Some(prev) = indi_merging_hash {
            self.indi_merging_hash = prev.indi_merging_hash.clone();
            self.merged_individual_linker = prev.merged_individual_linker.clone();
            self.merged_individual_count = prev.merged_individual_count;
        } else {
            self.indi_merging_hash.clear();
            self.merged_individual_linker.clear();
            self.merged_individual_count = 0;
        }
        self
    }

    /// Port of `getMergedIndividualLinker` (the chain in head→tail order).
    pub fn get_merged_individual_linker(&self) -> &[Cint64] {
        &self.merged_individual_linker
    }

    /// Port of `addMergedIndividualLinker(CXLinker<cint64>* linker)`.
    /// KONCLUDE-PORT-NOTE[ownership]: `mMergedIndividualCount += linker->getCount();
    /// mMergedIndividualLinker = linker->append(mMergedIndividualLinker);` —
    /// head-front splice: the incoming chain becomes the head, the existing chain
    /// its tail (`[linker…, old…]`).
    pub fn add_merged_individual_linker(&mut self, linker: Vec<Cint64>) -> &mut Self {
        self.merged_individual_count += linker.len() as Cint64;
        let mut new_chain = linker;
        new_chain.extend(self.merged_individual_linker.iter().copied());
        self.merged_individual_linker = new_chain;
        self
    }

    /// Port of `getMergedIndividualCount`.
    pub fn get_merged_individual_count(&self) -> Cint64 {
        self.merged_individual_count
    }

    /// Port of `hasMergedIndividual(cint64 individualId)`
    /// (`return value(individualId).isMergedWithIndividual();`).
    /// KONCLUDE-PORT-NOTE[api]: Qt `value(key)` returns a default-constructed value
    /// when the key is absent (`mMergedIndi == false`), so a missing key reports
    /// `false` — reproduced via `map_or(false, …)`.
    pub fn has_merged_individual(&self, individual_id: Cint64) -> bool {
        self.indi_merging_hash
            .get(&individual_id)
            .map_or(false, |d| d.is_merged_with_individual())
    }

    // --- Qt-hash base surface used by the merge path ---

    /// Qt `operator[]` (`mSuccNegDisEdgeHash[indi]`) — insert-default-then-borrow.
    pub fn entry_mut(&mut self, individual_id: Cint64) -> &mut IndividualMergingHashData {
        self.indi_merging_hash.entry(individual_id).or_default()
    }
    /// Qt `value(key)` read borrow (`None` == default value).
    pub fn get(&self, individual_id: Cint64) -> Option<&IndividualMergingHashData> {
        self.indi_merging_hash.get(&individual_id)
    }
    /// Qt `contains(key)`.
    pub fn contains(&self, individual_id: Cint64) -> bool {
        self.indi_merging_hash.contains_key(&individual_id)
    }

    /// Read-only snapshot of the Qt-hash base iterator.
    pub fn iter(&self) -> impl Iterator<Item = (&Cint64, &IndividualMergingHashData)> {
        self.indi_merging_hash.iter()
    }
}
