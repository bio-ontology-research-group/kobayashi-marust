//! `process::succ_role_hash` — the node's successor-role hash backend + its two
//! iterators, so the PN-3 relocation iterators iterate for real.
//!
//! Port of `Source/Reasoner/Kernel/Process/CSuccessorRoleHash.{h,cpp}` +
//! `CSuccessorRoleIterator.{h,cpp}` + `CSuccessorIterator.{h,cpp}`.
//!
//! KONCLUDE-PORT-NOTE[ownership]: the C++ `CPROCESSHASH<cint64, CIndividualLinkEdge*>`
//! is a Qt `QMultiHash` (multiple link edges per successor individual id). The port
//! models it as a `HashMap<cint64, Vec<EdgeId>>` (one bucket per id, head-front like
//! `insertMulti`'s newest-first). The shared `mPrevSuccessorLinkHash` COW partner
//! (a raw pointer to a previous test's hash) becomes an owned `Option<…>` clone (the
//! `[memory-pool]` zero-copy share is left for later); the size-threshold COW logic
//! of `initSuccessorRoleHash` is reproduced faithfully over those clones.
//!
//! KONCLUDE-PORT-NOTE[ownership]: the C++ iterators hold live `QMultiHash::iterator`
//! cursors. To avoid a self-referential borrow of the arena-held hash, the getters
//! snapshot the relevant buckets into owned `Vec`s (the iterators only ever expose
//! `next()->edge` / `nextIndividualID()`), exactly as the sibling `DistinctIterator`
//! / `SignatureIterator` ports do.

#![allow(dead_code)]

use std::collections::HashMap;

use super::super::model::substrate::Cint64;
use super::EdgeId;

/// `CSuccessorRoleHash*` → `SuccessorRoleHashId` (re-aliased from `process::stubs`
/// `SuccRoleHashId` onto this real struct, the W2.7 pattern).
pub type SuccessorRoleHashId = super::super::model::substrate::Id<SuccessorRoleHash>;

// ===========================================================================
// CSuccessorRoleHash
// ===========================================================================

/// Port of `CSuccessorRoleHash`.
pub struct SuccessorRoleHash {
    /// `CPROCESSHASH<cint64, CIndividualLinkEdge*>* mSuccessorLinkHash`.
    successor_link_hash: HashMap<Cint64, Vec<EdgeId>>,
    /// `CPROCESSHASH<cint64, CIndividualLinkEdge*>* mPrevSuccessorLinkHash`
    /// (shared COW partner; owned clone in the port).
    prev_successor_link_hash: Option<HashMap<Cint64, Vec<EdgeId>>>,
    /// `bool mPrevValidatingRequired`.
    prev_validating_required: bool,
}

impl Default for SuccessorRoleHash {
    fn default() -> Self {
        SuccessorRoleHash {
            successor_link_hash: HashMap::new(),
            prev_successor_link_hash: None,
            prev_validating_required: false,
        }
    }
}

impl SuccessorRoleHash {
    /// Port of `CSuccessorRoleHash::CSuccessorRoleHash(CProcessContext*)`
    /// (`mSuccessorLinkHash = new …; mPrevSuccessorLinkHash = nullptr;
    /// mPrevValidatingRequired = false;`).
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `initSuccessorRoleHash(CSuccessorRoleHash* prevRoleSuccHash)`.
    /// The size-threshold COW (share if `size <= 100`, else keep prev; combine if
    /// `size*10 > prev.size`) is reproduced over owned clones.
    pub fn init_successor_role_hash(&mut self, prev_role_succ_hash: Option<&SuccessorRoleHash>) -> &mut Self {
        if let Some(prev) = prev_role_succ_hash {
            if prev.prev_successor_link_hash.is_none() && prev.successor_link_hash.len() <= 100 {
                self.successor_link_hash = prev.successor_link_hash.clone();
                self.prev_successor_link_hash = None;
                self.prev_validating_required = false;
            } else if prev.prev_successor_link_hash.is_none() && prev.successor_link_hash.len() > 100 {
                self.successor_link_hash.clear();
                self.prev_successor_link_hash = Some(prev.successor_link_hash.clone());
                self.prev_validating_required = false;
            } else {
                let prev_prev = prev.prev_successor_link_hash.as_ref().unwrap();
                if prev.successor_link_hash.len() * 10 > prev_prev.len() {
                    self.successor_link_hash = prev.successor_link_hash.clone();
                    for (neighbour_id, links) in prev_prev.iter() {
                        if !self.prev_validating_required || !prev.successor_link_hash.contains_key(neighbour_id) {
                            for link in links.iter() {
                                self.successor_link_hash
                                    .entry(*neighbour_id)
                                    .or_default()
                                    .push(*link);
                            }
                        }
                    }
                    self.prev_successor_link_hash = None;
                    self.prev_validating_required = false;
                } else {
                    self.successor_link_hash = prev.successor_link_hash.clone();
                    self.prev_successor_link_hash = Some(prev_prev.clone());
                    self.prev_validating_required = false;
                }
            }
        } else {
            self.prev_validating_required = false;
            self.successor_link_hash.clear();
            self.prev_successor_link_hash = None;
        }
        self
    }

    /// Port of `insertSuccessorRoleLink(cint64 indi, CIndividualLinkEdge* link)`.
    /// KONCLUDE-PORT-NOTE[ownership]: when `indi` is only present in the shared prev
    /// hash, the C++ promotes (copies) its prev links into the local hash before the
    /// new insert, setting `mPrevValidatingRequired`.
    pub fn insert_successor_role_link(&mut self, indi: Cint64, link: EdgeId) -> &mut Self {
        if let Some(prev) = &self.prev_successor_link_hash {
            if prev.contains_key(&indi) && !self.successor_link_hash.contains_key(&indi) {
                let promoted: Vec<EdgeId> = prev.get(&indi).cloned().unwrap_or_default();
                self.successor_link_hash
                    .entry(indi)
                    .or_default()
                    .extend(promoted);
                self.prev_validating_required = true;
            }
        }
        self.successor_link_hash.entry(indi).or_default().push(link);
        self
    }

    /// Port of `getSuccessorRoleIterator(cint64 indi)`.
    pub fn get_successor_role_iterator(&self, indi: Cint64) -> SuccessorRoleIterator {
        if self.prev_successor_link_hash.is_none() || self.successor_link_hash.contains_key(&indi) {
            SuccessorRoleIterator::new(
                indi,
                self.successor_link_hash.get(&indi).cloned().unwrap_or_default(),
            )
        } else if self
            .prev_successor_link_hash
            .as_ref()
            .map_or(false, |p| p.contains_key(&indi))
        {
            SuccessorRoleIterator::new(
                indi,
                self.prev_successor_link_hash
                    .as_ref()
                    .unwrap()
                    .get(&indi)
                    .cloned()
                    .unwrap_or_default(),
            )
        } else {
            SuccessorRoleIterator::new(indi, Vec::new())
        }
    }

    /// Port of `hasSuccessorIndividualNode(cint64 indi)`.
    pub fn has_successor_individual_node(&self, indi: Cint64) -> bool {
        if self.successor_link_hash.contains_key(&indi) {
            return true;
        }
        if self
            .prev_successor_link_hash
            .as_ref()
            .map_or(false, |p| p.contains_key(&indi))
        {
            return true;
        }
        false
    }

    /// Port of `removeSuccessor(cint64 indi)`.
    /// When a shared-prev hash is present, the C++ first promotes every prev bucket
    /// not already local into the local hash (subject to the validating flag), drops
    /// the prev pointer, then removes `indi`.
    pub fn remove_successor(&mut self, indi: Cint64) -> &mut Self {
        if self
            .prev_successor_link_hash
            .as_ref()
            .map_or(false, |p| p.contains_key(&indi))
        {
            let prev = self.prev_successor_link_hash.take().unwrap();
            for (indi_id, links) in prev.iter() {
                if !self.prev_validating_required || !self.successor_link_hash.contains_key(indi_id) {
                    self.successor_link_hash
                        .entry(*indi_id)
                        .or_default()
                        .extend(links.iter().copied());
                }
            }
        }
        self.successor_link_hash.remove(&indi);
        self
    }

    /// Port of `getSuccessorIterator()`.
    /// KONCLUDE-PORT-NOTE[ownership]: the C++ `iterate` advances the cursor past
    /// repeated keys (`mLastSucc == beginIt.key()`), so the iterator yields one entry
    /// per DISTINCT successor individual (its first link). The snapshot reproduces
    /// that by taking one `(indi, links[0])` pair per bucket. When `mPrevValidatingRequired`
    /// the prev buckets already present locally are filtered out (`it2ValHash`).
    pub fn get_successor_iterator(&self) -> SuccessorIterator {
        let mut entries: Vec<(Cint64, EdgeId)> = Vec::new();
        for (indi, links) in self.successor_link_hash.iter() {
            if let Some(first) = links.first() {
                entries.push((*indi, *first));
            }
        }
        if let Some(prev) = &self.prev_successor_link_hash {
            for (indi, links) in prev.iter() {
                if self.prev_validating_required && self.successor_link_hash.contains_key(indi) {
                    continue;
                }
                if let Some(first) = links.first() {
                    entries.push((*indi, *first));
                }
            }
        }
        SuccessorIterator::from_entries(entries)
    }
}

// ===========================================================================
// CSuccessorRoleIterator
// ===========================================================================

/// Port of `CSuccessorRoleIterator` — the role-link edges held for one successor
/// individual.
pub struct SuccessorRoleIterator {
    /// `cint64 mIndi`.
    indi: Cint64,
    /// Snapshot of the successor's bucket (`find(indi)..end` while `key == indi`).
    links: Vec<EdgeId>,
    /// Cursor.
    pos: usize,
}

impl SuccessorRoleIterator {
    /// Port of `CSuccessorRoleIterator()` (the empty iterator,
    /// `mIterator1 = mIterator2 = false`).
    pub fn empty() -> Self {
        SuccessorRoleIterator {
            indi: 0,
            links: Vec::new(),
            pos: 0,
        }
    }

    /// Port of the `(indi, beginIt, endIt)` ctor.
    pub fn new(indi: Cint64, links: Vec<EdgeId>) -> Self {
        SuccessorRoleIterator { indi, links, pos: 0 }
    }

    /// The successor individual id (`mIndi`).
    pub fn individual_id(&self) -> Cint64 {
        self.indi
    }

    /// Port of `hasNext`.
    pub fn has_next(&self) -> bool {
        self.pos != self.links.len()
    }

    /// Port of `next(bool moveNext)` → `CIndividualLinkEdge*` (empty → NONE).
    pub fn next(&mut self, move_next: bool) -> EdgeId {
        let mut link = EdgeId::NONE;
        if self.pos != self.links.len() {
            link = self.links[self.pos];
            if move_next {
                self.pos += 1;
            }
        }
        link
    }
}

impl Default for SuccessorRoleIterator {
    fn default() -> Self {
        Self::empty()
    }
}

// ===========================================================================
// CSuccessorIterator
// ===========================================================================

/// Port of `CSuccessorIterator` — walks one (link, successor individual id) pair
/// per distinct successor of the node.
pub struct SuccessorIterator {
    /// Pre-deduplicated `(indi, first link)` entries (see `get_successor_iterator`).
    entries: Vec<(Cint64, EdgeId)>,
    /// Cursor.
    pos: usize,
}

impl SuccessorIterator {
    /// Port of `CSuccessorIterator()` (empty).
    pub fn empty() -> Self {
        SuccessorIterator {
            entries: Vec::new(),
            pos: 0,
        }
    }

    /// Build from the pre-deduplicated entry list.
    pub fn from_entries(entries: Vec<(Cint64, EdgeId)>) -> Self {
        SuccessorIterator { entries, pos: 0 }
    }

    /// Port of `hasNext`.
    pub fn has_next(&self) -> bool {
        self.pos != self.entries.len()
    }

    /// Port of `nextLink(bool moveNext)` → `CIndividualLinkEdge*` (empty → NONE).
    pub fn next_link(&mut self, move_next: bool) -> EdgeId {
        let mut link = EdgeId::NONE;
        if self.pos != self.entries.len() {
            link = self.entries[self.pos].1;
            if move_next {
                self.pos += 1;
            }
        }
        link
    }

    /// Port of `nextIndividualID(bool moveNext)` → `cint64` (empty → 0).
    pub fn next_individual_id(&mut self, move_next: bool) -> Cint64 {
        let mut indi_id: Cint64 = 0;
        if self.pos != self.entries.len() {
            indi_id = self.entries[self.pos].0;
            if move_next {
                self.pos += 1;
            }
        }
        indi_id
    }
}

impl Default for SuccessorIterator {
    fn default() -> Self {
        Self::empty()
    }
}
