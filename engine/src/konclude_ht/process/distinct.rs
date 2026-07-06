//! `process::distinct` — port unit **W2.7** (the fill wave): the distinct-edge /
//! connection-successor / disjoint-role process satellites that W2 left as
//! fieldless markers in `process::stubs` (`DistinctHash`, `ConnectionSuccessorSet`,
//! `DisjointSuccessorRoleHash`).
//!
//! Sources (`Source/Reasoner/Kernel/Process/`):
//!   * `CDistinctHash.{h,cpp}`                     → [`DistinctHash`]
//!   * `CDistinctIterator.{h,cpp}`                 → [`DistinctIterator`]
//!   * `CConnectionSuccessorSet.{h,cpp}`           → [`ConnectionSuccessorSet`]
//!   * `CConnectionSuccessorSetIterator.{h,cpp}`   → [`ConnectionSuccessorSetIterator`]
//!   * `CConnectionSuccessorCorrectionHash.{h,cpp}`→ [`ConnectionSuccessorCorrectionHash`]
//!   * `CDisjointSuccessorRoleHash.{h,cpp}`        → [`DisjointSuccessorRoleHash`]
//!   * `CDisjointSuccessorRoleIterator.{h,cpp}`    → [`DisjointSuccessorRoleIterator`]
//!
//! The two edge payload classes these satellites carry — `CDistinctEdge` and
//! `CNegationDisjointEdge` — are already ported in `process::edge`
//! (`edge::DistinctEdge` / `edge::DisjointEdge`); this unit references them by id
//! and resolves them against their existing `ProcessContext` arenas
//! (`distinct_edges` / `disjoint_edges`), so no edge re-port is needed here.
//!
//! ## Container model (the `CPROCESSHASH` / `CPROCESSSET` replacement)
//!
//! `CPROCESSHASH` is `CQtManagedRestrictedModificationHash` (a QHash with a
//! per-test allocator) and `CPROCESSSET` the QSet twin. Per the global `[ownership]`
//! / `[memory-pool]` decision (`substrate.rs`), the pooled, context-allocated
//! containers become **owned** `std::collections::HashMap` / `HashSet`; the
//! `CContext*` ctor argument (the allocator handle) is dropped — the arena owns
//! storage, the map owns its entries.
//!
//! ## Copy-on-write previous-set sharing (behaviour-load-bearing, rs1 precedent)
//!
//! `CConnectionSuccessorSet::mPrevConnSet` and
//! `CDisjointSuccessorRoleHash::CDisjointSuccessorRoleData::mUseNegDisSet` are raw
//! pointers that *alias* a parent node's set (the COW partner), localised on the
//! first mutation. The owned representation cannot alias, so — exactly as
//! `process::rs1` does for `CReapplyRoleSuccessorHash` — the alias is reproduced as
//! an **eager deep clone** at `init…` time, and the "is the active set locally
//! owned" bit is kept explicit (`prev_conn_set: Option<…>` non-null ⇄ the COW
//! partner is present; `DisjointSuccessorRoleData::located` ⇄ `mLocNegDisSet`).
//! The size thresholds that drive the split (**`<= 100`**, **`* 10`**) are
//! preserved verbatim; observable content (`conn_set ∪ prev_conn_set`) is
//! invariant, only the physical aliasing differs.

#![allow(dead_code)]

use std::collections::{HashMap, HashSet};

use super::super::model::substrate::{Arena, Cint64, Id};
use super::super::model::RoleId;
use super::edge::{DisjointEdge, DistinctEdge};
use super::{DisjointEdgeId, DistinctEdgeId, TrackPointId};

/// `CINT64_MIN`, Konclude's "no ancestor connection id" sentinel for
/// `CConnectionSuccessorSet::mAncConnID` (distinct from any valid id, which is
/// `>= 0`). Not the same as `substrate::INVALID` (`-1`): Konclude really uses the
/// minimum, so a `-1` id would not collide with it.
const ANC_CONN_NONE: Cint64 = Cint64::MIN;

// --- W2.7 process-layer id aliases (the real targets of the W2 stub markers) ---
/// `CDistinctHash*`                      → `DistinctHashId`.
pub type DistinctHashId = Id<DistinctHash>;
/// `CConnectionSuccessorSet*`            → `ConnectionSuccessorSetId`.
pub type ConnectionSuccessorSetId = Id<ConnectionSuccessorSet>;
/// `CConnectionSuccessorCorrectionHash*` → `ConnectionSuccessorCorrectionHashId`.
pub type ConnectionSuccessorCorrectionHashId = Id<ConnectionSuccessorCorrectionHash>;
/// `CDisjointSuccessorRoleHash*`         → `DisjointSuccessorRoleHashId`.
pub type DisjointSuccessorRoleHashId = Id<DisjointSuccessorRoleHash>;

// ===========================================================================
// CDistinctHash + CDistinctIterator
// ===========================================================================

/// Port of `CDistinctHash` (`: public CPROCESSHASH<cint64, CDistinctEdge*>`).
///
/// A per-node map `distinct-individual-id → distinct-edge`, recording the
/// `owl:differentFrom` partners of the node and the `CDistinctEdge` that justifies
/// each. The C++ class *is* the hash (inheritance); the port holds it by value.
///
/// KONCLUDE-PORT-NOTE[ownership]: `CDistinctEdge*` value → `DistinctEdgeId` into
/// the `ProcessContext::distinct_edges` arena; `Id::NONE` == `nullptr`.
#[derive(Default, Clone)]
pub struct DistinctHash {
    /// The underlying `CPROCESSHASH<cint64, CDistinctEdge*>`.
    hash: HashMap<Cint64, DistinctEdgeId>,
}

impl DistinctHash {
    /// Port of `CDistinctHash::CDistinctHash(CContext*)` (allocator handle dropped).
    pub fn new() -> Self {
        DistinctHash {
            hash: HashMap::new(),
        }
    }

    /// Port of `CDistinctHash::initDistinctHash`.
    ///
    /// `*this = *prevHash` (the QHash implicitly-shared assignment) → an eager
    /// clone; `clear()` otherwise.
    pub fn init_distinct_hash(&mut self, prev_hash: Option<&DistinctHash>) -> &mut Self {
        if let Some(prev_hash) = prev_hash {
            self.hash = prev_hash.hash.clone();
        } else {
            self.hash.clear();
        }
        self
    }

    /// Port of `CDistinctHash::getIndividualDistinctEdge` (`value(indiID, nullptr)`).
    pub fn get_individual_distinct_edge(&self, indi_id: Cint64) -> DistinctEdgeId {
        self.hash
            .get(&indi_id)
            .copied()
            .unwrap_or(DistinctEdgeId::NONE)
    }

    /// Port of `CDistinctHash::isIndividualDistinct` (`contains(indiID)`).
    pub fn is_individual_distinct(&self, indi_id: Cint64) -> bool {
        self.hash.contains_key(&indi_id)
    }

    /// Port of `CDistinctHash::insertDistinctIndividual` (C++ default
    /// `disEdge = nullptr` → pass `DistinctEdgeId::NONE`).
    pub fn insert_distinct_individual(
        &mut self,
        indi_id: Cint64,
        dis_edge: DistinctEdgeId,
    ) -> &mut Self {
        self.hash.insert(indi_id, dis_edge);
        self
    }

    /// Port of `CDistinctHash::removeDistinctIndividual` (`remove(indiID)`).
    pub fn remove_distinct_individual(&mut self, indi_id: Cint64) -> &mut Self {
        self.hash.remove(&indi_id);
        self
    }

    /// Port of `CDistinctHash::getDistinctCount` (`count()`).
    pub fn get_distinct_count(&self) -> Cint64 {
        self.hash.len() as Cint64
    }

    /// Port of `CDistinctHash::getDistinctIterator`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: the C++ iterator holds live `begin()/end()`
    /// hash iterators; the port snapshots the `(key, value)` pairs into an owned
    /// `Vec` so the iterator is self-contained (QHash iteration order is itself
    /// unspecified, so the snapshot is content-faithful).
    pub fn get_distinct_iterator(&self) -> DistinctIterator {
        DistinctIterator::from_entries(self.hash.iter().map(|(k, v)| (*k, *v)).collect())
    }
}

/// Port of `CDistinctIterator`.
///
/// Iterates the `(distinct-individual-id, distinct-edge)` entries of a
/// `CDistinctHash`. The dependency-track-point overload resolves the edge id
/// against the distinct-edge arena (the C++ `value()->getDependencyTrackPoint()`).
pub struct DistinctIterator {
    /// Snapshot of `CPROCESSHASH<cint64,CDistinctEdge*>` `[begin,end)` as
    /// `(mBeginIt.key(), mBeginIt.value())` pairs.
    entries: Vec<(Cint64, DistinctEdgeId)>,
    /// Cursor (`mBeginIt` advance == `++pos`).
    pos: usize,
}

impl DistinctIterator {
    /// Port of `CDistinctIterator::CDistinctIterator()` (empty).
    pub fn new() -> Self {
        DistinctIterator {
            entries: Vec::new(),
            pos: 0,
        }
    }

    /// Port of `CDistinctIterator::CDistinctIterator(beginIt, endIt)`.
    pub fn from_entries(entries: Vec<(Cint64, DistinctEdgeId)>) -> Self {
        DistinctIterator { entries, pos: 0 }
    }

    /// Port of `CDistinctIterator::hasNext` (`mBeginIt != mEndIt`).
    pub fn has_next(&self) -> bool {
        self.pos != self.entries.len()
    }

    /// Port of `CDistinctIterator::nextDistinctIndividualID(bool moveNext)`.
    pub fn next_distinct_individual_id(&mut self, move_next: bool) -> Cint64 {
        let mut indi = 0;
        if self.pos != self.entries.len() {
            indi = self.entries[self.pos].0;
            if move_next {
                self.pos += 1;
            }
        }
        indi
    }

    /// Port of `CDistinctIterator::nextDistinctIndividualID(CDependencyTrackPoint*&, bool)`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: the C++ out-parameter
    /// `CDependencyTrackPoint*& depTrackPoint` is returned as the second tuple
    /// element. `mBeginIt.value()->getDependencyTrackPoint()` becomes a deref of
    /// the `DistinctEdgeId` against the `distinct_edges` arena (already a
    /// `ProcessContext` field), exactly as `rs1` threads `&Arena<…>`.
    pub fn next_distinct_individual_id_dep(
        &mut self,
        distinct_edges: &Arena<DistinctEdge>,
        move_next: bool,
    ) -> (Cint64, TrackPointId) {
        let mut indi = 0;
        let mut dep_track_point = TrackPointId::NONE;
        if self.pos != self.entries.len() {
            let (key, edge) = self.entries[self.pos];
            indi = key;
            dep_track_point = distinct_edges.get(edge).get_dependency_track_point();
            if move_next {
                self.pos += 1;
            }
        }
        (indi, dep_track_point)
    }

    /// Port of `CDistinctIterator::next(bool moveNext)` (returns the edge value).
    pub fn next(&mut self, move_next: bool) -> DistinctEdgeId {
        let mut dis_edge = DistinctEdgeId::NONE;
        if self.pos != self.entries.len() {
            dis_edge = self.entries[self.pos].1;
            if move_next {
                self.pos += 1;
            }
        }
        dis_edge
    }
}

impl Default for DistinctIterator {
    fn default() -> Self {
        Self::new()
    }
}

// ===========================================================================
// CConnectionSuccessorSet + CConnectionSuccessorSetIterator
// ===========================================================================

/// Port of `CConnectionSuccessorSet`.
///
/// The set of successor-node ids a node is connected to, with a three-tier
/// representation that grows lazily:
///   * `anc_conn_id` — a single connection id (the common one-successor case),
///     `ANC_CONN_NONE` when unused;
///   * `conn_set` — the full owned set, allocated once a second id arrives;
///   * `prev_conn_set` — the copy-on-write partner inherited from the parent node.
///
/// KONCLUDE-PORT-NOTE[ownership]/[memory-pool]: `mContext` (the allocator handle)
/// is dropped; `CPROCESSSET<cint64>* mConnSet` / `mPrevConnSet` become owned
/// `Option<HashSet<cint64>>`. `mPrevConnSet` aliasing a parent's `mConnSet` is
/// reproduced by the eager deep clone in `init_connection_successor_set`
/// (rs1 precedent); see the module header.
#[derive(Default, Clone)]
pub struct ConnectionSuccessorSet {
    /// `CPROCESSSET<cint64>* mConnSet`.
    conn_set: Option<HashSet<Cint64>>,
    /// `CPROCESSSET<cint64>* mPrevConnSet` (the COW partner; owned clone here).
    prev_conn_set: Option<HashSet<Cint64>>,
    /// `cint64 mAncConnID`.
    anc_conn_id: Cint64,
}

impl ConnectionSuccessorSet {
    /// Port of `CConnectionSuccessorSet::CConnectionSuccessorSet(CProcessContext*)`.
    pub fn new() -> Self {
        ConnectionSuccessorSet {
            conn_set: None,
            prev_conn_set: None,
            anc_conn_id: ANC_CONN_NONE,
        }
    }

    /// Port of `CConnectionSuccessorSet::initConnectionSuccessorSet`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: `mPrevConnSet = connSuccSet->mConnSet` /
    /// `= connSuccSet->mPrevConnSet` are raw alias assignments in C++; with the
    /// owned `Option<HashSet>` model they are eager deep clones (rs1 precedent).
    /// The `<= 100` / `> 100` / `* 10` thresholds are preserved verbatim.
    pub fn init_connection_successor_set(
        &mut self,
        conn_succ_set: Option<&ConnectionSuccessorSet>,
    ) -> &mut Self {
        if let Some(conn_succ_set) = conn_succ_set {
            self.anc_conn_id = conn_succ_set.anc_conn_id;
            if let Some(other_conn_set) = conn_succ_set.conn_set.as_ref() {
                // if (!mConnSet) allocate; else mConnSet->clear()
                match self.conn_set.as_mut() {
                    None => self.conn_set = Some(HashSet::new()),
                    Some(s) => s.clear(),
                }

                if conn_succ_set.prev_conn_set.is_none() && other_conn_set.len() <= 100 {
                    // *mConnSet = *connSuccSet->mConnSet;  mPrevConnSet = nullptr
                    *self.conn_set.as_mut().unwrap() = other_conn_set.clone();
                    self.prev_conn_set = None;
                } else if conn_succ_set.prev_conn_set.is_none() && other_conn_set.len() > 100 {
                    // mPrevConnSet = connSuccSet->mConnSet  (alias → deep clone)
                    self.prev_conn_set = Some(other_conn_set.clone());
                } else {
                    let other_prev = conn_succ_set.prev_conn_set.as_ref().unwrap();
                    if other_conn_set.len() * 10 > other_prev.len() {
                        // *mConnSet = *connSuccSet->mPrevConnSet; then fold in mConnSet
                        *self.conn_set.as_mut().unwrap() = other_prev.clone();
                        for indi_id in other_conn_set.iter() {
                            self.conn_set.as_mut().unwrap().insert(*indi_id);
                        }
                        self.prev_conn_set = None;
                    } else {
                        // *mConnSet = *connSuccSet->mConnSet; mPrevConnSet = connSuccSet->mPrevConnSet
                        *self.conn_set.as_mut().unwrap() = other_conn_set.clone();
                        self.prev_conn_set = Some(other_prev.clone());
                    }
                }
            }
        } else {
            self.anc_conn_id = ANC_CONN_NONE;
            if let Some(s) = self.conn_set.as_mut() {
                s.clear();
            }
            self.prev_conn_set = None;
        }
        self
    }

    /// Port of `CConnectionSuccessorSet::hasConnectionSuccessor`.
    pub fn has_connection_successor(&self, indi_id: Cint64) -> bool {
        if let Some(prev) = self.prev_conn_set.as_ref() {
            if prev.contains(&indi_id) {
                return true;
            }
        }
        if let Some(conn) = self.conn_set.as_ref() {
            return conn.contains(&indi_id);
        }
        self.anc_conn_id == indi_id
    }

    /// Port of `CConnectionSuccessorSet::insertConnectionSuccessor`.
    pub fn insert_connection_successor(&mut self, indi_id: Cint64) -> &mut Self {
        if self.anc_conn_id != indi_id {
            if self.anc_conn_id != ANC_CONN_NONE {
                if self.conn_set.is_none() {
                    let mut new_set = HashSet::new();
                    new_set.insert(self.anc_conn_id);
                    self.conn_set = Some(new_set);
                }
                // if (!mPrevConnSet || !mPrevConnSet->contains(indiID)) mConnSet->insert(indiID)
                let in_prev = self
                    .prev_conn_set
                    .as_ref()
                    .map_or(false, |p| p.contains(&indi_id));
                if !in_prev {
                    self.conn_set.as_mut().unwrap().insert(indi_id);
                }
            } else {
                self.anc_conn_id = indi_id;
            }
        }
        self
    }

    /// Port of `CConnectionSuccessorSet::removeConnection`.
    pub fn remove_connection(&mut self, indi_id: Cint64) -> &mut Self {
        // if mPrevConnSet contains indiID: fold all of mPrevConnSet into mConnSet, drop mPrevConnSet
        let prev_contains = self
            .prev_conn_set
            .as_ref()
            .map_or(false, |p| p.contains(&indi_id));
        if prev_contains {
            let prev_owned = self.prev_conn_set.take().unwrap();
            let conn = self.conn_set.as_mut().unwrap();
            for id in prev_owned.iter() {
                conn.insert(*id);
            }
        }
        if let Some(conn) = self.conn_set.as_mut() {
            conn.remove(&indi_id);
        } else if self.anc_conn_id == indi_id {
            self.anc_conn_id = ANC_CONN_NONE;
        }
        self
    }

    /// Port of `CConnectionSuccessorSet::getConnectionSuccessorIterator`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: the C++ iterator wraps live set `begin/end`;
    /// the port snapshots the relevant set(s) into owned `Vec`s (content-faithful,
    /// QSet order being unspecified).
    pub fn get_connection_successor_iterator(&self) -> ConnectionSuccessorSetIterator {
        if let Some(prev) = self.prev_conn_set.as_ref() {
            // CConnectionSuccessorSetIterator(mConnSet, mPrevConnSet)
            let v1 = self
                .conn_set
                .as_ref()
                .map_or_else(Vec::new, |s| s.iter().copied().collect());
            let v2 = prev.iter().copied().collect();
            ConnectionSuccessorSetIterator::from_two(v1, v2)
        } else if let Some(conn) = self.conn_set.as_ref() {
            // CConnectionSuccessorSetIterator(mConnSet)
            ConnectionSuccessorSetIterator::from_one(conn.iter().copied().collect())
        } else {
            // CConnectionSuccessorSetIterator(mAncConnID)
            ConnectionSuccessorSetIterator::from_single(self.anc_conn_id)
        }
    }

    /// Port of `CConnectionSuccessorSet::getConnectionSuccessorCount`.
    pub fn get_connection_successor_count(&self) -> Cint64 {
        match self.conn_set.as_ref() {
            None => {
                if self.anc_conn_id != ANC_CONN_NONE {
                    1
                } else {
                    0
                }
            }
            Some(conn) => {
                if let Some(prev) = self.prev_conn_set.as_ref() {
                    conn.len() as Cint64 + prev.len() as Cint64
                } else {
                    conn.len() as Cint64
                }
            }
        }
    }
}

/// Port of `CConnectionSuccessorSetIterator`.
///
/// Walks the single-id / one-set / two-set forms of a `CConnectionSuccessorSet`.
pub struct ConnectionSuccessorSetIterator {
    /// Snapshot of `[mBeginIt1, mEndIt1)`.
    it1: Vec<Cint64>,
    pos1: usize,
    /// Snapshot of `[mBeginIt2, mEndIt2)`.
    it2: Vec<Cint64>,
    pos2: usize,
    /// `bool mIterator1`.
    iterator1: bool,
    /// `bool mIterator2`.
    iterator2: bool,
    /// `cint64 mConnID`.
    conn_id: Cint64,
}

impl ConnectionSuccessorSetIterator {
    /// Port of `CConnectionSuccessorSetIterator(cint64 connID = CINT64_MIN)`.
    pub fn from_single(conn_id: Cint64) -> Self {
        ConnectionSuccessorSetIterator {
            it1: Vec::new(),
            pos1: 0,
            it2: Vec::new(),
            pos2: 0,
            iterator1: false,
            iterator2: false,
            conn_id,
        }
    }

    /// Port of `CConnectionSuccessorSetIterator(beginIt, endIt)` (single set).
    pub fn from_one(it1: Vec<Cint64>) -> Self {
        ConnectionSuccessorSetIterator {
            it1,
            pos1: 0,
            it2: Vec::new(),
            pos2: 0,
            iterator1: true,
            iterator2: false,
            conn_id: ANC_CONN_NONE,
        }
    }

    /// Port of `CConnectionSuccessorSetIterator(beginIt1, endIt1, beginIt2, endIt2)`.
    pub fn from_two(it1: Vec<Cint64>, it2: Vec<Cint64>) -> Self {
        ConnectionSuccessorSetIterator {
            it1,
            pos1: 0,
            it2,
            pos2: 0,
            iterator1: true,
            iterator2: true,
            conn_id: ANC_CONN_NONE,
        }
    }

    /// Port of `CConnectionSuccessorSetIterator::hasNext`.
    ///
    /// `mConnID != CINT64_MIN || mIterator1 && it1-nonempty || mIterator2 && it2-nonempty`
    /// (C++ `&&` binds tighter than `||`).
    pub fn has_next(&self) -> bool {
        self.conn_id != ANC_CONN_NONE
            || self.iterator1 && self.pos1 != self.it1.len()
            || self.iterator2 && self.pos2 != self.it2.len()
    }

    /// Port of `CConnectionSuccessorSetIterator::nextSuccessorConnectionID(bool moveNext)`.
    pub fn next_successor_connection_id(&mut self, move_next: bool) -> Cint64 {
        let mut indi_id = 0;
        if self.conn_id != ANC_CONN_NONE {
            indi_id = self.conn_id;
            if move_next {
                self.conn_id = ANC_CONN_NONE;
            }
        }
        if self.iterator1 && self.pos1 != self.it1.len() {
            indi_id = self.it1[self.pos1];
            if move_next {
                self.pos1 += 1;
            }
        } else if self.iterator2 && self.pos2 != self.it2.len() {
            indi_id = self.it2[self.pos2];
            if move_next {
                self.pos2 += 1;
            }
        }
        indi_id
    }

    /// Port of `CConnectionSuccessorSetIterator::next(bool moveNext)`.
    pub fn next(&mut self, move_next: bool) -> Cint64 {
        self.next_successor_connection_id(move_next)
    }
}

// ===========================================================================
// CConnectionSuccessorCorrectionHash
// ===========================================================================

/// Port of `CConnectionSuccessorCorrectionHash`
/// (`: public CPROCESSHASH<cint64, cint64>`).
///
/// Maps a successor id to its corrected (post-merge) id; the identity entry is
/// inserted when a connection is first recorded, then overwritten by a correction.
///
/// KONCLUDE-PORT-NOTE[ownership]/[memory-pool]: `mContext` dropped; the inherited
/// `CPROCESSHASH<cint64,cint64>` becomes an owned `HashMap<cint64,cint64>`.
#[derive(Default, Clone)]
pub struct ConnectionSuccessorCorrectionHash {
    hash: HashMap<Cint64, Cint64>,
}

impl ConnectionSuccessorCorrectionHash {
    /// Port of `CConnectionSuccessorCorrectionHash::CConnectionSuccessorCorrectionHash`.
    pub fn new() -> Self {
        ConnectionSuccessorCorrectionHash {
            hash: HashMap::new(),
        }
    }

    /// Port of `CConnectionSuccessorCorrectionHash::initConnectionSuccessorCorrectionHash`.
    pub fn init_connection_successor_correction_hash(
        &mut self,
        conn_succ_corr_hash: Option<&ConnectionSuccessorCorrectionHash>,
    ) -> &mut Self {
        if let Some(conn_succ_corr_hash) = conn_succ_corr_hash {
            // CPROCESSHASH<cint64,cint64>::operator =(*connSuccCorrHash)
            self.hash = conn_succ_corr_hash.hash.clone();
        } else {
            self.hash.clear();
        }
        self
    }

    /// Port of `CConnectionSuccessorCorrectionHash::insertConnectionSuccessor`
    /// (`insert(indiID, indiID)`).
    pub fn insert_connection_successor(&mut self, indi_id: Cint64) -> &mut Self {
        self.hash.insert(indi_id, indi_id);
        self
    }

    /// Port of `CConnectionSuccessorCorrectionHash::correctSuccessorConnection`
    /// (`insert(indiID, correctedID)`).
    pub fn correct_successor_connection(
        &mut self,
        indi_id: Cint64,
        corrected_id: Cint64,
    ) -> &mut Self {
        self.hash.insert(indi_id, corrected_id);
        self
    }
}

// ===========================================================================
// CDisjointSuccessorRoleHash (+ inner CDisjointSuccessorRoleData)
//   + CDisjointSuccessorRoleIterator
// ===========================================================================

/// Port of `CDisjointSuccessorRoleHash::CDisjointSuccessorRoleData` (the nested
/// per-successor value).
///
/// Holds the successor's `role → negated-disjoint-edge` index. In C++ the data
/// keeps two raw pointers — `mLocNegDisSet` (the locally-owned hash) and
/// `mUseNegDisSet` (the *active* hash, which aliases either `mLocNegDisSet` or a
/// parent's set). The copy ctor shares the parent's `mUseNegDisSet` and nulls
/// `mLocNegDisSet` so the next write re-localises.
///
/// KONCLUDE-PORT-NOTE[ownership]: the owned model keeps the single *active* map
/// (`use_neg_dis_set`) plus a `located` flag standing in for `mLocNegDisSet != null`
/// (rs1's `located_link_set` precedent). The copy ctor (`Clone`) eager-clones the
/// active map and resets `located = false`; the located=true re-allocation in
/// `get_neg_dis_role_hash_located` reproduces the C++ "fresh empty set replaces the
/// aliased view" behaviour verbatim.
pub struct DisjointSuccessorRoleData {
    /// `CPROCESSHASH<CRole*,CNegationDisjointEdge*>* mUseNegDisSet` (the active map).
    pub use_neg_dis_set: Option<HashMap<RoleId, DisjointEdgeId>>,
    /// `mLocNegDisSet != nullptr` — is `use_neg_dis_set` locally owned?
    pub located: bool,
}

impl Default for DisjointSuccessorRoleData {
    /// Port of `CDisjointSuccessorRoleData::CDisjointSuccessorRoleData()`
    /// (`mUseNegDisSet = nullptr; mLocNegDisSet = nullptr`).
    fn default() -> Self {
        DisjointSuccessorRoleData {
            use_neg_dis_set: None,
            located: false,
        }
    }
}

impl Clone for DisjointSuccessorRoleData {
    /// Port of `CDisjointSuccessorRoleData(const CDisjointSuccessorRoleData&)`
    /// (`mUseNegDisSet = other.mUseNegDisSet; mLocNegDisSet = nullptr`).
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: the C++ aliases `mUseNegDisSet`; the owned
    /// model deep-clones it. `mLocNegDisSet = nullptr` → `located = false` (the COW
    /// trigger — load-bearing, preserved verbatim).
    fn clone(&self) -> Self {
        DisjointSuccessorRoleData {
            use_neg_dis_set: self.use_neg_dis_set.clone(),
            located: false,
        }
    }
}

/// Port of `CDisjointSuccessorRoleHash`.
///
/// A per-node map `successor-id → (role → negated-disjoint-edge)`, recording for
/// each connected successor the disjoint-role edges in force.
///
/// KONCLUDE-PORT-NOTE[ownership]/[memory-pool]: `mContext` dropped; the outer
/// `CPROCESSHASH<cint64, CDisjointSuccessorRoleData>` becomes an owned
/// `HashMap<cint64, DisjointSuccessorRoleData>`.
#[derive(Default, Clone)]
pub struct DisjointSuccessorRoleHash {
    /// `CPROCESSHASH<cint64, CDisjointSuccessorRoleData> mSuccNegDisEdgeHash`.
    succ_neg_dis_edge_hash: HashMap<Cint64, DisjointSuccessorRoleData>,
}

impl DisjointSuccessorRoleHash {
    /// Port of `CDisjointSuccessorRoleHash::CDisjointSuccessorRoleHash(CProcessContext*)`.
    pub fn new() -> Self {
        DisjointSuccessorRoleHash {
            succ_neg_dis_edge_hash: HashMap::new(),
        }
    }

    /// Port of `CDisjointSuccessorRoleHash::initDisjointSuccessorRoleHash`.
    ///
    /// `mSuccNegDisEdgeHash = prev->mSuccNegDisEdgeHash` (QHash implicitly-shared
    /// assignment) → an eager clone; each value goes through the ported copy ctor
    /// (`Clone for DisjointSuccessorRoleData`, resetting `located`).
    pub fn init_disjoint_successor_role_hash(
        &mut self,
        prev_disj_role_hash: Option<&DisjointSuccessorRoleHash>,
    ) -> &mut Self {
        if let Some(prev_disj_role_hash) = prev_disj_role_hash {
            self.succ_neg_dis_edge_hash = prev_disj_role_hash.succ_neg_dis_edge_hash.clone();
        } else {
            self.succ_neg_dis_edge_hash.clear();
        }
        self
    }

    /// Port of `CDisjointSuccessorRoleHash::getNegDisRoleHash(successor, located=false)`.
    ///
    /// KONCLUDE-PORT-NOTE[overload]: Rust cannot return either `&` or `&mut` from
    /// one signature, so the C++ `getNegDisRoleHash(successor, located)` is split
    /// into `…_unlocated` (read, no insert; `tryGetValuePointer`) and `…_located`
    /// (mutate, inserts default; `operator[]`). This is the `located == false` arm.
    fn get_neg_dis_role_hash_unlocated(
        &self,
        successor: Cint64,
    ) -> Option<&HashMap<RoleId, DisjointEdgeId>> {
        // CDisjointSuccessorRoleData* data; if (tryGetValuePointer(successor,data)) return data->mUseNegDisSet;
        if let Some(data) = self.succ_neg_dis_edge_hash.get(&successor) {
            return data.use_neg_dis_set.as_ref();
        }
        None
    }

    /// Port of `CDisjointSuccessorRoleHash::getNegDisRoleHash(successor, located=true)`.
    ///
    /// `operator[]` inserts a default `CDisjointSuccessorRoleData` if absent; if
    /// `!mLocNegDisSet` a fresh empty hash is allocated and assigned to BOTH
    /// `mLocNegDisSet` and `mUseNegDisSet` (discarding any aliased view — faithful).
    fn get_neg_dis_role_hash_located(
        &mut self,
        successor: Cint64,
    ) -> &mut HashMap<RoleId, DisjointEdgeId> {
        let data = self.succ_neg_dis_edge_hash.entry(successor).or_default();
        if !data.located {
            // newNegDisSet = allocate; mLocNegDisSet = newNegDisSet; mUseNegDisSet = newNegDisSet;
            data.use_neg_dis_set = Some(HashMap::new());
            data.located = true;
        }
        data.use_neg_dis_set.as_mut().unwrap()
    }

    /// Port of `CDisjointSuccessorRoleHash::insertDisjointSuccessorRoleLink`.
    ///
    /// `getNegDisRoleHash(succIndi,true)->insert(link->getLinkRole(), link)`. The
    /// `CNegationDisjointEdge::getLinkRole()` deref resolves the `DisjointEdgeId`
    /// against the `disjoint_edges` arena (a `ProcessContext` field), as `rs1`
    /// threads `&Arena<…>`.
    pub fn insert_disjoint_successor_role_link(
        &mut self,
        disjoint_edges: &Arena<DisjointEdge>,
        succ_indi: Cint64,
        link: DisjointEdgeId,
    ) -> &mut Self {
        let role = disjoint_edges.get(link).get_link_role();
        self.get_neg_dis_role_hash_located(succ_indi)
            .insert(role, link);
        self
    }

    /// Port of `CDisjointSuccessorRoleHash::hasDisjointSuccessorRoleLink`.
    pub fn has_disjoint_successor_role_link(&self, succ_indi: Cint64, role: RoleId) -> bool {
        if let Some(data_hash) = self.get_neg_dis_role_hash_unlocated(succ_indi) {
            return data_hash.contains_key(&role);
        }
        false
    }

    /// Port of `CDisjointSuccessorRoleHash::getDisjointSuccessorRoleLink`
    /// (`value(role, nullptr)`).
    pub fn get_disjoint_successor_role_link(
        &self,
        succ_indi: Cint64,
        role: RoleId,
    ) -> DisjointEdgeId {
        let mut link = DisjointEdgeId::NONE;
        if let Some(data_hash) = self.get_neg_dis_role_hash_unlocated(succ_indi) {
            link = data_hash
                .get(&role)
                .copied()
                .unwrap_or(DisjointEdgeId::NONE);
        }
        link
    }

    /// Port of `CDisjointSuccessorRoleHash::removeDisjointSuccessorRoleLinks`
    /// (`mSuccNegDisEdgeHash.remove(succIndi)`).
    pub fn remove_disjoint_successor_role_links(&mut self, succ_indi: Cint64) -> &mut Self {
        self.succ_neg_dis_edge_hash.remove(&succ_indi);
        self
    }

    /// Port of `CDisjointSuccessorRoleHash::getDisjointRoleIterator`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: the C++ iterator wraps the inner hash's live
    /// `begin/end`; the port snapshots the edge values into an owned `Vec` (the
    /// iterator only ever exposes `next()->edge`, not the role key).
    pub fn get_disjoint_role_iterator(&self, succ_indi: Cint64) -> DisjointSuccessorRoleIterator {
        if let Some(data_hash) = self.get_neg_dis_role_hash_unlocated(succ_indi) {
            return DisjointSuccessorRoleIterator::from_links(
                succ_indi,
                data_hash.values().copied().collect(),
            );
        }
        DisjointSuccessorRoleIterator::new()
    }
}

/// Port of `CDisjointSuccessorRoleIterator`.
///
/// Iterates the negated-disjoint edges held for one successor.
pub struct DisjointSuccessorRoleIterator {
    /// `cint64 mSuccIndi`.
    succ_indi: Cint64,
    /// Snapshot of the inner hash values (`mBeginIt.value()` over `[begin,end)`).
    links: Vec<DisjointEdgeId>,
    /// Cursor.
    pos: usize,
}

impl DisjointSuccessorRoleIterator {
    /// Port of `CDisjointSuccessorRoleIterator::CDisjointSuccessorRoleIterator()`
    /// (`mSuccIndi = 0`).
    pub fn new() -> Self {
        DisjointSuccessorRoleIterator {
            succ_indi: 0,
            links: Vec::new(),
            pos: 0,
        }
    }

    /// Port of `CDisjointSuccessorRoleIterator(succIndi, beginIt, endIt)`.
    pub fn from_links(succ_indi: Cint64, links: Vec<DisjointEdgeId>) -> Self {
        DisjointSuccessorRoleIterator {
            succ_indi,
            links,
            pos: 0,
        }
    }

    /// The successor id this iterator was built for (`mSuccIndi`).
    pub fn get_successor_individual_id(&self) -> Cint64 {
        self.succ_indi
    }

    /// Port of `CDisjointSuccessorRoleIterator::hasNext`.
    pub fn has_next(&self) -> bool {
        self.pos != self.links.len()
    }

    /// Port of `CDisjointSuccessorRoleIterator::next(bool moveNext)`.
    pub fn next(&mut self, move_next: bool) -> DisjointEdgeId {
        let mut link = DisjointEdgeId::NONE;
        if self.pos != self.links.len() {
            link = self.links[self.pos];
            if move_next {
                self.pos += 1;
            }
        }
        link
    }
}

impl Default for DisjointSuccessorRoleIterator {
    fn default() -> Self {
        Self::new()
    }
}

// ===========================================================================
// W2.7-ARENA-ADDITIONS
// ===========================================================================
//
// To un-defer the W2/W3 sites that hold these satellites (node.rs's
// `conn_succ_set`/`use_conn_succ_set`/`prev_conn_succ_set: ConnSuccSetId`,
// `distinct_hash`/`use_`/`prev_: DistinctHashId`,
// `disjoint_succ_role_hash`/`use_`/`prev_: DisjointSuccRoleHashId`; the pn6 lazy
// getters `getDistinctHash` / `getConnectionSuccessorSet` /
// `getDisjointSuccessorRoleHash`; and the u12/u13/u14 merge bodies), the per-test
// `ProcessContext` (`process/context.rs`) must gain ONE arena per satellite kind
// plus the standard `arena_accessors!` trio, mirroring the existing satellite
// arenas (`label_sets` / `role_succ_hashes` / `restriction_specs`):
//
//   // --- the W2.7 distinct / connection / disjoint-role satellites ---
//   distinct_hashes:        Arena<distinct::DistinctHash>,
//   conn_succ_sets:         Arena<distinct::ConnectionSuccessorSet>,
//   conn_succ_corr_hashes:  Arena<distinct::ConnectionSuccessorCorrectionHash>,
//   disjoint_succ_role_hashes: Arena<distinct::DisjointSuccessorRoleHash>,
//
//   arena_accessors!(distinct_hashes, distinct::DistinctHash, DistinctHashId,
//       distinct_hash, distinct_hash_mut, alloc_distinct_hash);
//   arena_accessors!(conn_succ_sets, distinct::ConnectionSuccessorSet, ConnectionSuccessorSetId,
//       conn_succ_set, conn_succ_set_mut, alloc_conn_succ_set);
//   arena_accessors!(conn_succ_corr_hashes, distinct::ConnectionSuccessorCorrectionHash,
//       ConnectionSuccessorCorrectionHashId,
//       conn_succ_corr_hash, conn_succ_corr_hash_mut, alloc_conn_succ_corr_hash);
//   arena_accessors!(disjoint_succ_role_hashes, distinct::DisjointSuccessorRoleHash,
//       DisjointSuccessorRoleHashId,
//       disjoint_succ_role_hash, disjoint_succ_role_hash_mut, alloc_disjoint_succ_role_hash);
//
// (plus `Arena::new()` for each in `ProcessContext::new()`, and a `pub mod distinct;`
// in `process/mod.rs`). The three iterators and the inner `DisjointSuccessorRoleData`
// are NOT arena-owned — iterators are returned by value (snapshots), and the data is
// an inline value in the `DisjointSuccessorRoleHash` map.
//
// RECONCILE (process/mod.rs): the W2 stub ids `DistinctHashId` / `ConnSuccSetId` /
// `DisjointSuccRoleHashId` (currently `Id<stubs::{DistinctHash,ConnectionSuccessorSet,
// DisjointSuccessorRoleHash}>`) must RE-ALIAS to the real structs here
// (`Id<distinct::DistinctHash>`, …), and those three markers be removed from
// `process/stubs.rs` — the standard "stub relocates to its own module" reconcile.
// The local `*Id` aliases at the top of this file are the canonical targets; the
// `ConnSuccSetId` short name in `mod.rs` should map to `ConnectionSuccessorSetId`,
// and `DisjointSuccRoleHashId` to `DisjointSuccessorRoleHashId`.
//
// No `W2.7-DEFER[api]` deferrals were required in the method bodies: the only
// cross-arena derefs (`CDistinctEdge::getDependencyTrackPoint`,
// `CNegationDisjointEdge::getLinkRole`) resolve against the `distinct_edges` /
// `disjoint_edges` arenas that ALREADY exist on `ProcessContext`, threaded as
// `&Arena<…>` params (the rs1 precedent); the COW parent-set aliases are handled by
// eager deep clone (also rs1), not by a cross-node id lookup.
