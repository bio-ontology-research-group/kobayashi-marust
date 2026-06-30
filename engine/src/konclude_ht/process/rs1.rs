//! `process::rs1` — port unit **RS-1**: the method bodies of
//! `CReapplyRoleSuccessorHash` (a node's role→successor-edge index).
//!
//! Source: `Source/Reasoner/Kernel/Process/CReapplyRoleSuccessorHash.cpp`
//! (+ `CReapplyRoleSuccessorData.h` for the value type's copy constructor).
//! The struct definitions live in `process::satellites` (SD-4); this file holds
//! only the ported method bodies, exactly mirroring the C++ control flow.
//!
//! ## The 3-way successor representation + copy-on-write (behaviour-load-bearing)
//!
//! Each per-role value (`CReapplyRoleSuccessorData`) holds the successor edges in
//! up to three coexisting representations:
//!
//!   * `link_linker` (`CIndividualLinkEdge* mLinkLinker`) — the *always present*
//!     intrusive edge chain, head-of-list, walked via `edge.next` in the edge arena;
//!   * `link_set` (`mLinkSet`) — an optional localised `coupled-id → edge` hash,
//!     built lazily once a role has enough successors;
//!   * `prev_link_set` (`mPrevLinkSet`) — an optional *shared, un-copied* previous
//!     hash, the copy-on-write partner kept until an entry it holds is touched.
//!
//! `located_link_set` (`mLocatedLinkSet`) records whether `link_set` is locally
//! owned vs shared from a parent. In Konclude `mLinkSet`/`mPrevLinkSet` are raw
//! pointers that may *alias* a parent node's sets (the `CPROCESSHASH` value copy in
//! `initRoleSuccessorHash` is implicitly-shared, and `CReapplyRoleSuccessorData`'s
//! copy constructor copies the pointers but resets `mLocatedLinkSet = false`). The
//! port (per `substrate.rs`'s global `[ownership]` decision) replaces those raw
//! pointers with **owned** `Option<HashMap<…>>`; the alias-then-localise COW is
//! reproduced by an *eager deep clone* in `init_role_successor_hash` (driven by the
//! ported copy ctor `Clone for ReapplyRoleSuccessorData`, which clones the maps but
//! resets `located_link_set = false`). The observable content
//! (`link_set ∪ prev_link_set`, with `link_set` taking precedence) is invariant, so
//! the split is byte-faithful while the physical aliasing differs. The size
//! thresholds that decide the split — **`<= 100`**, **`* 10`** in
//! `ensure_role_successor_data_localated`, and the **`link_count >= 5`**
//! locate-on-read trigger in `get_role_successor_to_individual_link` — are preserved
//! verbatim. The coupled id is the integer **sum** of the two endpoint individual
//! ids (`get_coupled_individual_id`, already in `satellites.rs`).

#![allow(dead_code)]

use std::collections::HashMap;

use super::super::model::substrate::{Arena, Cint64, INVALID};
use super::super::model::RoleId;
use super::edge::IndividualLinkEdge;
use super::satellites::{ReapplyQueue, ReapplyRoleSuccessorData, ReapplyRoleSuccessorHash};
use super::EdgeId;

// ===========================================================================
// W2-DEFER[api]: not-yet-ported iterator/queue-iterator return types.
// CRoleSuccessorLinkIterator / CRoleSuccessorIterator / CReapplyQueueIterator
// each have their own `Process/` unit (`CRoleSuccessorLinkIterator.{h,cpp}`,
// `CRoleSuccessorIterator.h`, `CReapplyQueue.h`). They wrap raw `CPROCESSHASH`
// iterators + the intrusive `CIndividualLinkEdge*` chain, neither of which has a
// stable ported form yet. Placeholder zero-size structs so the RS-1 method
// signatures below stay shaped like the original; they relocate when those units
// land.
// ===========================================================================

/// W2-DEFER[api]: Port of `CRoleSuccessorLinkIterator` (placeholder).
#[derive(Default)]
pub struct RoleSuccessorLinkIterator;

/// W2-DEFER[api]: Port of `CRoleSuccessorIterator` (placeholder).
#[derive(Default)]
pub struct RoleSuccessorIterator;

/// W2-DEFER[api]: Port of `CReapplyQueueIterator` (placeholder).
#[derive(Default)]
pub struct ReapplyQueueIterator;

// ===========================================================================
// CReapplyRoleSuccessorData copy constructor (the COW heart of the value type).
// ===========================================================================

/// Port of `CReapplyRoleSuccessorData(const CReapplyRoleSuccessorData&)`
/// (`CReapplyRoleSuccessorData.h` 71–77).
///
/// KONCLUDE-PORT-NOTE[ownership]: the C++ copy ctor *aliases* the link-set raw
/// pointers (`mLinkSet = roleSuccData.mLinkSet`, `mPrevLinkSet = …`) but resets
/// `mLocatedLinkSet = false` so the next mutation re-localises. With the owned
/// `Option<HashMap>` representation we cannot alias, so we deep-clone the maps;
/// the `located_link_set = false` reset is preserved verbatim (it is the COW
/// trigger). `link_linker` is the shared chain head (an `EdgeId` into the shared
/// edge arena, not cloned — exactly mirroring the aliased `mLinkLinker`).
impl Clone for ReapplyRoleSuccessorData {
    fn clone(&self) -> Self {
        ReapplyRoleSuccessorData {
            // mLinkSet = roleSuccData.mLinkSet  (aliased in C++ → deep clone here)
            link_set: self.link_set.clone(),
            // mPrevLinkSet = roleSuccData.mPrevLinkSet
            prev_link_set: self.prev_link_set.clone(),
            // mLinkLinker = roleSuccData.mLinkLinker  (shared chain head; id, not cloned)
            link_linker: self.link_linker,
            // mLocatedLinkSet = false  (the reset — load-bearing)
            located_link_set: false,
            // mLinkCount = roleSuccData.mLinkCount
            link_count: self.link_count,
            // mReapplyQueue(roleSuccData.mReapplyQueue)
            // W2-DEFER[api]: CReapplyQueue is a stateless placeholder; the real
            // port copies the queue here.
            reapply_queue: ReapplyQueue,
        }
    }
}

impl ReapplyRoleSuccessorHash {
    /// Port of `CReapplyRoleSuccessorHash::initRoleSuccessorHash`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: `mRoleSuccessorDataHash = prev->mRoleSuccessorDataHash`
    /// is a `CPROCESSHASH` implicitly-shared (lazy COW) assignment; the port makes
    /// it an eager deep clone, which invokes the ported copy ctor
    /// (`Clone for ReapplyRoleSuccessorData`, resetting `located_link_set`) for
    /// every entry — the same per-entry effect a `CPROCESSHASH` detach has on the
    /// first mutation. Observable content is identical.
    pub fn init_role_successor_hash(
        &mut self,
        prev_role_succ_hash: Option<&ReapplyRoleSuccessorHash>,
    ) -> &mut Self {
        if let Some(prev_role_succ_hash) = prev_role_succ_hash {
            self.role_successor_data_hash = prev_role_succ_hash.role_successor_data_hash.clone();
            self.link_count = prev_role_succ_hash.link_count;
        } else {
            self.role_successor_data_hash.clear();
            self.link_count = 0;
        }
        self
    }

    /// Port of `CReapplyRoleSuccessorHash::insertRoleSuccessorLink`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: `CRole* role` → `RoleId`,
    /// `CIndividualLinkEdge* link` → `EdgeId` (+ the `&mut` edge arena to dereference
    /// `link->append(...)`). `mRoleSuccessorDataHash[role]` (insert-if-absent
    /// `operator[]`) → `entry(role).or_default()`. The optional
    /// `CReapplyQueueIterator*` out-param becomes an `Option<&mut …>`.
    pub fn insert_role_successor_link(
        &mut self,
        edges: &mut Arena<IndividualLinkEdge>,
        role: RoleId,
        link: EdgeId,
        reapply_queue_iterator: Option<&mut ReapplyQueueIterator>,
    ) -> Cint64 {
        let context = self.context;
        let role_succ_data = self.role_successor_data_hash.entry(role).or_default();
        if role_succ_data.link_set.is_some() {
            let coup_id = Self::get_coupled_individual_id_link(edges, link);
            Self::ensure_role_successor_data_localated(context, role_succ_data);
            Self::eliminate_role_successor_previous_share_data(role_succ_data, coup_id);
            role_succ_data.link_set.as_mut().unwrap().insert(coup_id, link);
        }
        // mLinkLinker = link->append(mLinkLinker)  (CLinker::append = link to tail
        // of `link`'s chain, then the old head appended after it → prepend `link`).
        let old_head = role_succ_data.link_linker;
        let mut last = link;
        while edges.get(last).get_next().is_some() {
            last = edges.get(last).get_next();
        }
        edges.get_mut(last).set_next(old_head);
        role_succ_data.link_linker = link;
        role_succ_data.link_count += 1;
        self.link_count += 1;
        let ret = role_succ_data.link_count;
        if let Some(_reapply_queue_iterator) = reapply_queue_iterator {
            // W2-DEFER[api]: CReapplyQueue::getIterator not yet ported.
            // *reapply_queue_iterator = role_succ_data.reapply_queue.get_iterator(true);
        }
        ret
    }

    /// Port of `CReapplyRoleSuccessorHash::ensureRoleSuccessorDataLocalated`.
    ///
    /// Localises `link_set` from the (possibly shared) referred sets, splitting
    /// between `link_set` and `prev_link_set` per the **`<= 100`** / **`* 10`**
    /// size thresholds. KONCLUDE-PORT-NOTE[ownership]: the C++ allocates a fresh
    /// `CPROCESSHASH` (`mContext` only feeds the pool allocator); the port uses an
    /// owned `HashMap`, and the C++ `init`/aliasing of the referred sets becomes a
    /// move of the owned referred maps (content-identical, since after the eager
    /// clone in `init_role_successor_hash` the referred maps are this data's own).
    pub fn ensure_role_successor_data_localated(
        _context: Cint64,
        role_succ_data: &mut ReapplyRoleSuccessorData,
    ) {
        if !role_succ_data.located_link_set {
            let referred_link_set = role_succ_data.link_set.take();
            let referred_prev_link_set = role_succ_data.prev_link_set.take();

            // newLinkSet allocated empty; mLinkSet = newLinkSet; mPrevLinkSet = nullptr.
            role_succ_data.link_set = Some(HashMap::new());
            role_succ_data.prev_link_set = None;
            role_succ_data.located_link_set = true;

            // referredLinkSet is dereferenced unconditionally in C++ (the caller only
            // enters when mLinkSet was non-null), so it is `Some` here.
            let referred_link_set =
                referred_link_set.expect("ensure: mLinkSet non-null (caller invariant)");

            match referred_prev_link_set {
                // !referredPrevLinkSet && referredLinkSet->size() <= 100
                None if referred_link_set.len() <= 100 => {
                    // newLinkSet->init(referredLinkSet)
                    role_succ_data.link_set = Some(referred_link_set);
                }
                // !referredPrevLinkSet && referredLinkSet->size() > 100
                None => {
                    // roleSuccData.mPrevLinkSet = referredLinkSet  (newLinkSet stays empty)
                    role_succ_data.prev_link_set = Some(referred_link_set);
                }
                // both referred sets present
                Some(referred_prev_link_set) => {
                    if referred_link_set.len() * 10 > referred_prev_link_set.len() {
                        // newLinkSet->init(referredPrevLinkSet); then re-insert referredLinkSet
                        let mut new_link_set = referred_prev_link_set;
                        for (neighbour_id, link) in referred_link_set.iter() {
                            new_link_set.insert(*neighbour_id, *link);
                        }
                        role_succ_data.link_set = Some(new_link_set);
                        // mPrevLinkSet remains nullptr (set above).
                    } else {
                        // newLinkSet->init(referredLinkSet); mPrevLinkSet = referredPrevLinkSet
                        role_succ_data.link_set = Some(referred_link_set);
                        role_succ_data.prev_link_set = Some(referred_prev_link_set);
                    }
                }
            }
        }
    }

    /// Port of `CReapplyRoleSuccessorHash::eliminateRoleSuccessorPreviousShareData`.
    ///
    /// If `prev_link_set` holds `coup_id`, fold all of `prev_link_set` into
    /// `link_set` and drop `prev_link_set` (so a subsequent write to `coup_id`
    /// cannot be shadowed by the shared previous set).
    pub fn eliminate_role_successor_previous_share_data(
        role_succ_data: &mut ReapplyRoleSuccessorData,
        coup_id: Cint64,
    ) {
        let contains = role_succ_data
            .prev_link_set
            .as_ref()
            .map_or(false, |prev| prev.contains_key(&coup_id));
        if contains {
            let prev = role_succ_data.prev_link_set.take().unwrap();
            let link_set = role_succ_data.link_set.as_mut().unwrap();
            for (neighbour_id, link) in prev.iter() {
                link_set.insert(*neighbour_id, *link);
            }
            // roleSuccData.mPrevLinkSet = nullptr  (already taken above).
        }
    }

    /// Port of `CReapplyRoleSuccessorHash::removeRoleSuccessorLink(CRole*, CIndividualLinkEdge*)`.
    ///
    /// KONCLUDE-PORT-NOTE[overload]: the `(role, link)` overload. Faithful to C++,
    /// the linker-replacement `else` branch rebuilds `link_set` from the chain
    /// *excluding* `link` but does **not** unlink `link` from `link_linker`.
    pub fn remove_role_successor_link_by_link(
        &mut self,
        edges: &Arena<IndividualLinkEdge>,
        role: RoleId,
        link: EdgeId,
    ) -> &mut Self {
        let context = self.context;
        let role_succ_data = self.role_successor_data_hash.entry(role).or_default();
        if role_succ_data.link_set.is_some() {
            let coup_id = Self::get_coupled_individual_id_link(edges, link);
            Self::ensure_role_successor_data_localated(context, role_succ_data);
            Self::eliminate_role_successor_previous_share_data(role_succ_data, coup_id);
            role_succ_data.link_set.as_mut().unwrap().remove(&coup_id);
        } else if role_succ_data.link_linker.is_some() {
            // replace by set
            let mut new_link_set: HashMap<Cint64, EdgeId> = HashMap::new();
            role_succ_data.located_link_set = true;
            let mut link_it = role_succ_data.link_linker;
            while link_it.is_some() {
                if link_it != link {
                    let coup = Self::get_coupled_individual_id_link(edges, link_it);
                    new_link_set.insert(coup, link_it);
                }
                link_it = edges.get(link_it).get_next();
            }
            role_succ_data.link_set = Some(new_link_set);
        }
        role_succ_data.link_count -= 1;
        self.link_count -= 1;
        self
    }

    /// Port of `CReapplyRoleSuccessorHash::removeRoleSuccessorLink(CRole*, cint64, cint64)`.
    ///
    /// KONCLUDE-PORT-NOTE[overload]: the `(role, sourceIndiID, destinationIndiID)`
    /// overload — locates the link by its coupled id (`source + destination`).
    pub fn remove_role_successor_link_by_ids(
        &mut self,
        edges: &Arena<IndividualLinkEdge>,
        role: RoleId,
        source_indi_id: Cint64,
        destination_indi_id: Cint64,
    ) -> &mut Self {
        let context = self.context;
        let searched_coupled_id = self.get_coupled_individual_id(source_indi_id, destination_indi_id);
        let role_succ_data = self.role_successor_data_hash.entry(role).or_default();
        if role_succ_data.link_set.is_some() {
            Self::ensure_role_successor_data_localated(context, role_succ_data);
            Self::eliminate_role_successor_previous_share_data(role_succ_data, searched_coupled_id);
            role_succ_data.link_set.as_mut().unwrap().remove(&searched_coupled_id);
        } else if role_succ_data.link_linker.is_some() {
            // replace by set
            let mut new_link_set: HashMap<Cint64, EdgeId> = HashMap::new();
            role_succ_data.located_link_set = true;
            let mut link_it = role_succ_data.link_linker;
            while link_it.is_some() {
                let coupled_id = Self::get_coupled_individual_id_link(edges, link_it);
                if coupled_id != searched_coupled_id {
                    new_link_set.insert(coupled_id, link_it);
                }
                link_it = edges.get(link_it).get_next();
            }
            role_succ_data.link_set = Some(new_link_set);
        }
        role_succ_data.link_count -= 1;
        self.link_count -= 1;
        self
    }

    /// Port of `CReapplyRoleSuccessorHash::getRoleSuccessorToIndividualLink`.
    ///
    /// Returns the successor edge with coupled id `source + destination`, or
    /// `EdgeId::NONE` (`nullptr`). The **`link_count >= 5`** locate-on-read trigger:
    /// when `locateable` and `link_set` is absent and the chain is long enough, the
    /// chain is materialised into a fresh `link_set` (a mutation through a "getter",
    /// faithfully reproduced via `get_mut`).
    pub fn get_role_successor_to_individual_link(
        &mut self,
        edges: &Arena<IndividualLinkEdge>,
        role: RoleId,
        source_indi_id: Cint64,
        destination_indi_id: Cint64,
        locateable: bool,
    ) -> EdgeId {
        let searched_coupled_id = self.get_coupled_individual_id(source_indi_id, destination_indi_id);
        if let Some(role_succ_data) = self.role_successor_data_hash.get_mut(&role) {
            if role_succ_data.link_linker.is_some() {
                if locateable && role_succ_data.link_set.is_none() && role_succ_data.link_count >= 5 {
                    let mut new_link_set: HashMap<Cint64, EdgeId> = HashMap::new();
                    let mut link_it = role_succ_data.link_linker;
                    let mut searched_link = EdgeId::NONE;
                    while link_it.is_some() {
                        let coupled_id = Self::get_coupled_individual_id_link(edges, link_it);
                        new_link_set.insert(coupled_id, link_it);
                        if coupled_id == searched_coupled_id {
                            searched_link = link_it;
                        }
                        link_it = edges.get(link_it).get_next();
                    }
                    role_succ_data.link_set = Some(new_link_set);
                    role_succ_data.located_link_set = true;
                    return searched_link;
                } else if role_succ_data.link_set.is_none() {
                    let mut link_it = role_succ_data.link_linker;
                    while link_it.is_some() {
                        let coupled_id = Self::get_coupled_individual_id_link(edges, link_it);
                        if coupled_id == searched_coupled_id {
                            return link_it;
                        }
                        link_it = edges.get(link_it).get_next();
                    }
                } else {
                    let mut link = role_succ_data
                        .link_set
                        .as_ref()
                        .unwrap()
                        .get(&searched_coupled_id)
                        .copied()
                        .unwrap_or(EdgeId::NONE);
                    if link.is_none() {
                        if let Some(prev_link_set) = role_succ_data.prev_link_set.as_ref() {
                            link = prev_link_set
                                .get(&searched_coupled_id)
                                .copied()
                                .unwrap_or(EdgeId::NONE);
                        }
                    }
                    return link;
                }
            }
        }
        EdgeId::NONE
    }

    /// Port of `CReapplyRoleSuccessorHash::hasRoleSuccessorToIndividual`.
    pub fn has_role_successor_to_individual(
        &mut self,
        edges: &Arena<IndividualLinkEdge>,
        role: RoleId,
        source_indi_id: Cint64,
        destination_indi_id: Cint64,
        locateable: bool,
    ) -> bool {
        let searched_link = self.get_role_successor_to_individual_link(
            edges,
            role,
            source_indi_id,
            destination_indi_id,
            locateable,
        );
        searched_link.is_some()
    }

    /// Port of `CReapplyRoleSuccessorHash::hasRoleSuccessor`.
    pub fn has_role_successor(&self, role: RoleId) -> bool {
        if let Some(role_succ_data) = self.role_successor_data_hash.get(&role) {
            if role_succ_data.prev_link_set.is_some() {
                !role_succ_data.link_set.as_ref().unwrap().is_empty()
                    || !role_succ_data.prev_link_set.as_ref().unwrap().is_empty()
            } else if role_succ_data.link_set.is_some() {
                !role_succ_data.link_set.as_ref().unwrap().is_empty()
            } else {
                role_succ_data.link_linker.is_some()
            }
        } else {
            false
        }
    }

    /// Port of `CReapplyRoleSuccessorHash::getRoleSuccessorCount`.
    pub fn get_role_successor_count(&self, role: RoleId) -> Cint64 {
        if let Some(role_succ_data) = self.role_successor_data_hash.get(&role) {
            role_succ_data.link_count
        } else {
            0
        }
    }

    /// Port of `CReapplyRoleSuccessorHash::getRoleReapplyQueue`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: returns a borrow of the in-data
    /// `CReapplyQueue` (`CReapplyQueue*` → `Option<&mut ReapplyQueue>`).
    pub fn get_role_reapply_queue(&mut self, role: RoleId, create: bool) -> Option<&mut ReapplyQueue> {
        if create {
            let role_succ_data = self.role_successor_data_hash.entry(role).or_default();
            Some(&mut role_succ_data.reapply_queue)
        } else {
            self.role_successor_data_hash
                .get_mut(&role)
                .map(|role_succ_data| &mut role_succ_data.reapply_queue)
        }
    }

    /// Port of `CReapplyRoleSuccessorHash::containsRoleReapplyQueue`.
    pub fn contains_role_reapply_queue(&self, role: RoleId) -> bool {
        if let Some(_role_succ_data) = self.role_successor_data_hash.get(&role) {
            // W2-DEFER[api]: CReapplyQueue::isEmpty not yet ported.
            // return !_role_succ_data.reapply_queue.is_empty();
            return false;
        }
        false
    }

    /// Port of `CReapplyRoleSuccessorHash::getRoleReapplyIterator`.
    ///
    /// W2-DEFER[api]: needs `CReapplyQueue::getIterator` + `CReapplyQueueIterator`.
    /// The faithful body is
    /// `tryGetValuePointer(role) ? roleSuccData->mReapplyQueue.getIterator(clearDynamicReapplyQueue)
    ///  : CReapplyQueueIterator(nullptr, nullptr)`.
    pub fn get_role_reapply_iterator(
        &mut self,
        _role: RoleId,
        _clear_dynamic_reapply_queue: bool,
    ) -> ReapplyQueueIterator {
        // W2-DEFER[api]
        ReapplyQueueIterator
    }

    /// Port of `CReapplyRoleSuccessorHash::getRoleSuccessorLinkIterator(CRole*)`.
    ///
    /// W2-DEFER[api]: needs `CRoleSuccessorLinkIterator`. Faithful body selects one
    /// of three iterator constructions on the per-role data: `(linkSet, prevLinkSet)`
    /// when `prev_link_set` is present, `(linkSet)` when only `link_set` is present,
    /// else `(link_linker)` over the intrusive chain; `nullptr` when the role is absent.
    pub fn get_role_successor_link_iterator(&self, _role: RoleId) -> RoleSuccessorLinkIterator {
        // W2-DEFER[api]
        RoleSuccessorLinkIterator
    }

    /// Port of `CReapplyRoleSuccessorHash::getRoleSuccessorLinkIterator(CRole*, cint64* linkCount)`.
    ///
    /// W2-DEFER[api]: as above; additionally writes `*linkCount = roleSuccData->mLinkCount`.
    pub fn get_role_successor_link_iterator_count(
        &self,
        role: RoleId,
        link_count: Option<&mut Cint64>,
    ) -> RoleSuccessorLinkIterator {
        if let Some(role_succ_data) = self.role_successor_data_hash.get(&role) {
            if let Some(link_count) = link_count {
                *link_count = role_succ_data.link_count;
            }
        }
        // W2-DEFER[api]: iterator construction over the selected representation.
        RoleSuccessorLinkIterator
    }

    /// Port of `CReapplyRoleSuccessorHash::getRoleSuccessorLinkIterator(CRole*, cint64*, CIndividualLinkEdge*&)`.
    ///
    /// W2-DEFER[api]: as above; additionally writes `lastLink = roleSuccData->mLinkLinker`.
    pub fn get_role_successor_link_iterator_count_last(
        &self,
        role: RoleId,
        link_count: Option<&mut Cint64>,
        last_link: &mut EdgeId,
    ) -> RoleSuccessorLinkIterator {
        if let Some(role_succ_data) = self.role_successor_data_hash.get(&role) {
            *last_link = role_succ_data.link_linker;
            if let Some(link_count) = link_count {
                *link_count = role_succ_data.link_count;
            }
        }
        // W2-DEFER[api]: iterator construction over the selected representation.
        RoleSuccessorLinkIterator
    }

    /// Port of `CReapplyRoleSuccessorHash::getRoleSuccessorHistoryLinkIterator(CRole*, CIndividualLinkEdge* lastLink)`.
    ///
    /// W2-DEFER[api]: needs `CRoleSuccessorLinkIterator`. Faithful body is
    /// `CRoleSuccessorLinkIterator(roleSuccData->mLinkLinker, lastLink)` (the chain
    /// from the head up to `lastLink`), `nullptr` when the role is absent.
    pub fn get_role_successor_history_link_iterator(
        &self,
        _role: RoleId,
        _last_link: EdgeId,
    ) -> RoleSuccessorLinkIterator {
        // W2-DEFER[api]
        RoleSuccessorLinkIterator
    }

    /// Port of `CReapplyRoleSuccessorHash::getRoleSuccessorHistoryLinkIterator(CRole*, CIndividualLinkEdge*, cint64*)`.
    ///
    /// W2-DEFER[api]: as above; additionally writes `*linkCount = roleSuccData->mLinkCount`.
    pub fn get_role_successor_history_link_iterator_count(
        &self,
        role: RoleId,
        _last_link: EdgeId,
        link_count: Option<&mut Cint64>,
    ) -> RoleSuccessorLinkIterator {
        if let Some(role_succ_data) = self.role_successor_data_hash.get(&role) {
            if let Some(link_count) = link_count {
                *link_count = role_succ_data.link_count;
            }
        }
        // W2-DEFER[api]: iterator construction over the chain.
        RoleSuccessorLinkIterator
    }

    /// Port of `CReapplyRoleSuccessorHash::getRoleIterator`.
    ///
    /// W2-DEFER[api]: needs `CRoleSuccessorIterator` over
    /// `mRoleSuccessorDataHash.begin()/end()`.
    pub fn get_role_iterator(&self) -> RoleSuccessorIterator {
        // W2-DEFER[api]
        RoleSuccessorIterator
    }

    /// Port of `CReapplyRoleSuccessorHash::getCoupledIndividualID(CIndividualLinkEdge*)`.
    ///
    /// W2-DEFER[api]: dispatches to `CNodeEdge::getCoupledIndividualID`, which sums
    /// the edge's `source`/`destination` node ids (`mSourceIndividual->getIndividualNodeID()
    /// + mDestinationIndividual->getIndividualNodeID()`) — that dereference needs the
    /// node arena, which `edge.rs` defers. Associated (no-`self`) so callers can use
    /// it while holding a `&mut` into `role_successor_data_hash`.
    fn get_coupled_individual_id_link(_edges: &Arena<IndividualLinkEdge>, _link: EdgeId) -> Cint64 {
        // W2-DEFER[api]: `_edges.get(_link).get_coupled_individual_id(nodes)` once the
        // CNodeEdge id accessors land (need the node arena).
        INVALID
    }
}
