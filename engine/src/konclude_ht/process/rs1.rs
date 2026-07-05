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

use super::super::model::substrate::{Arena, Cint64};
use super::super::model::RoleId;
use super::context::ProcessContext;
use super::edge::IndividualLinkEdge;
use super::node::IndividualProcessNode;
use super::reapply_sat::{ReapplyConceptDescriptor, ReapplyConceptDescriptorId};
use super::satellites::{ReapplyQueue, ReapplyRoleSuccessorData, ReapplyRoleSuccessorHash};
use super::{ConDescId, EdgeId};

// ===========================================================================
// CRoleSuccessorLinkIterator / CRoleSuccessorIterator / CReapplyQueueIterator
// ===========================================================================

/// Port of `CRoleSuccessorLinkIterator`.
///
/// KONCLUDE-PORT-NOTE[ownership]: C++ holds live `CPROCESSHASH` iterators or an
/// intrusive `CIndividualLinkEdge*` chain cursor. The port snapshots the selected
/// hash ranges or edge chain into `EdgeId`s so the iterator can be returned by
/// value without borrowing the process arenas.
#[derive(Clone, Default)]
pub struct RoleSuccessorLinkIterator {
    links: Vec<EdgeId>,
    pos: usize,
}

impl RoleSuccessorLinkIterator {
    /// Port of `CRoleSuccessorLinkIterator()`.
    pub fn empty() -> Self {
        Self::default()
    }

    fn from_links(links: Vec<EdgeId>) -> Self {
        RoleSuccessorLinkIterator { links, pos: 0 }
    }

    fn from_chain(edges: &Arena<IndividualLinkEdge>, head: EdgeId, last_link: EdgeId) -> Self {
        let mut links = Vec::new();
        let mut link_it = head;
        while link_it.is_some() && link_it != last_link {
            links.push(link_it);
            link_it = edges.get(link_it).get_next();
        }
        RoleSuccessorLinkIterator::from_links(links)
    }

    fn from_data(edges: &Arena<IndividualLinkEdge>, data: &ReapplyRoleSuccessorData) -> Self {
        if let Some(prev_link_set) = data.prev_link_set.as_ref() {
            let mut links = Vec::new();
            if let Some(link_set) = data.link_set.as_ref() {
                links.extend(link_set.values().copied());
            }
            links.extend(prev_link_set.values().copied());
            RoleSuccessorLinkIterator::from_links(links)
        } else if let Some(link_set) = data.link_set.as_ref() {
            RoleSuccessorLinkIterator::from_links(link_set.values().copied().collect())
        } else {
            RoleSuccessorLinkIterator::from_chain(edges, data.link_linker, EdgeId::NONE)
        }
    }

    /// Port of `hasNext`.
    pub fn has_next(&self) -> bool {
        self.pos != self.links.len()
    }

    /// Port of `next(bool moveNext)`.
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

/// Port of `CRoleSuccessorIterator`.
///
/// C++ skips roles whose `mLinkCount <= 0` at construction and after every
/// advance. The snapshot applies the same filter.
#[derive(Clone, Default)]
pub struct RoleSuccessorIterator {
    roles: Vec<RoleId>,
    pos: usize,
}

impl RoleSuccessorIterator {
    /// Port of `CRoleSuccessorIterator()`.
    pub fn empty() -> Self {
        Self::default()
    }

    fn from_roles(roles: Vec<RoleId>) -> Self {
        RoleSuccessorIterator { roles, pos: 0 }
    }

    /// Port of `hasNext`.
    pub fn has_next(&self) -> bool {
        self.pos != self.roles.len()
    }

    /// Port of `next(bool moveNext)`.
    pub fn next(&mut self, move_next: bool) -> RoleId {
        let mut role = RoleId::NONE;
        if self.pos != self.roles.len() {
            role = self.roles[self.pos];
            if move_next {
                self.pos += 1;
            }
        }
        role
    }
}

/// Port of `CReapplyQueueIterator`.
///
/// Walks dynamic descriptors first, then static descriptors, matching
/// `CReapplyQueueIterator::next`.
#[derive(Copy, Clone)]
pub struct ReapplyQueueIterator {
    static_reapply_des_linker: ReapplyConceptDescriptorId,
    dynamic_reapply_des_linker: ReapplyConceptDescriptorId,
}

impl Default for ReapplyQueueIterator {
    fn default() -> Self {
        ReapplyQueueIterator {
            static_reapply_des_linker: ReapplyConceptDescriptorId::NONE,
            dynamic_reapply_des_linker: ReapplyConceptDescriptorId::NONE,
        }
    }
}

impl ReapplyQueueIterator {
    /// Port of `CReapplyQueueIterator()`.
    pub fn empty() -> Self {
        Self::default()
    }

    /// Port of `CReapplyQueueIterator(staticReapplyDesLinker, dynamicReapplyDesLinker)`.
    pub fn new(
        static_reapply_des_linker: ReapplyConceptDescriptorId,
        dynamic_reapply_des_linker: ReapplyConceptDescriptorId,
    ) -> Self {
        ReapplyQueueIterator {
            static_reapply_des_linker,
            dynamic_reapply_des_linker,
        }
    }

    /// Port of `next(bool moveNext)`.
    pub fn next(&mut self, ctx: &ProcessContext, move_next: bool) -> ReapplyConceptDescriptorId {
        let mut next_des = ReapplyConceptDescriptorId::NONE;
        if self.dynamic_reapply_des_linker.is_some() {
            next_des = self.dynamic_reapply_des_linker;
            if move_next {
                self.dynamic_reapply_des_linker = ctx
                    .reapply_con_desc(self.dynamic_reapply_des_linker)
                    .get_next();
            }
        } else if self.static_reapply_des_linker.is_some() {
            next_des = self.static_reapply_des_linker;
            if move_next {
                self.static_reapply_des_linker = ctx
                    .reapply_con_desc(self.static_reapply_des_linker)
                    .get_next();
            }
        }
        next_des
    }

    /// Port of `hasNext`.
    pub fn has_next(&self) -> bool {
        self.dynamic_reapply_des_linker.is_some() || self.static_reapply_des_linker.is_some()
    }
}

impl ReapplyQueue {
    /// Port of `initReapplyQueue(CReapplyQueue*)`.
    pub fn init_reapply_queue(&mut self, prev_reapply_queue: Option<&ReapplyQueue>) -> &mut Self {
        if let Some(prev) = prev_reapply_queue {
            self.static_reapply_des_linker = prev.static_reapply_des_linker;
            self.dynamic_reapply_des_linker = prev.dynamic_reapply_des_linker;
        } else {
            self.static_reapply_des_linker = ReapplyConceptDescriptorId::NONE;
            self.dynamic_reapply_des_linker = ReapplyConceptDescriptorId::NONE;
        }
        self
    }

    /// Port of `isEmpty`.
    pub fn is_empty(&self) -> bool {
        self.static_reapply_des_linker.is_none() && self.dynamic_reapply_des_linker.is_none()
    }

    /// Port of `hasConceptDescriptor`.
    pub fn has_concept_descriptor(
        &self,
        ctx: &ProcessContext,
        concept_descriptor: ConDescId,
    ) -> bool {
        let mut des_linker = self.static_reapply_des_linker;
        while des_linker.is_some() {
            let d = ctx.reapply_con_desc(des_linker);
            if d.has_concept_descriptor(concept_descriptor) {
                return true;
            }
            des_linker = d.get_next();
        }
        des_linker = self.dynamic_reapply_des_linker;
        while des_linker.is_some() {
            let d = ctx.reapply_con_desc(des_linker);
            if d.has_concept_descriptor(concept_descriptor) {
                return true;
            }
            des_linker = d.get_next();
        }
        false
    }

    /// Port of `addReapplyConceptDescriptor`.
    pub fn add_reapply_concept_descriptor(
        &mut self,
        ctx: &mut ProcessContext,
        con_pro_des: ReapplyConceptDescriptorId,
    ) -> &mut Self {
        if con_pro_des.is_some() {
            if ctx.reapply_con_desc(con_pro_des).is_static_descriptor() {
                self.static_reapply_des_linker = ReapplyConceptDescriptor::append(
                    ctx,
                    con_pro_des,
                    self.static_reapply_des_linker,
                );
            } else {
                self.dynamic_reapply_des_linker = ReapplyConceptDescriptor::append(
                    ctx,
                    con_pro_des,
                    self.dynamic_reapply_des_linker,
                );
            }
        }
        self
    }

    /// Port of `getIterator(bool clearDynamicReapplyQueue)`.
    pub fn get_iterator(&mut self, clear_dynamic_reapply_queue: bool) -> ReapplyQueueIterator {
        let it = ReapplyQueueIterator::new(
            self.static_reapply_des_linker,
            self.dynamic_reapply_des_linker,
        );
        if clear_dynamic_reapply_queue {
            self.dynamic_reapply_des_linker = ReapplyConceptDescriptorId::NONE;
        }
        it
    }
}

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
            reapply_queue: self.reapply_queue,
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
        nodes: &Arena<IndividualProcessNode>,
        edges: &mut Arena<IndividualLinkEdge>,
        role: RoleId,
        link: EdgeId,
        reapply_queue_iterator: Option<&mut ReapplyQueueIterator>,
    ) -> Cint64 {
        let context = self.context;
        let role_succ_data = self.role_successor_data_hash.entry(role).or_default();
        if role_succ_data.link_set.is_some() {
            let coup_id = Self::get_coupled_individual_id_link(nodes, edges, link);
            Self::ensure_role_successor_data_localated(context, role_succ_data);
            Self::eliminate_role_successor_previous_share_data(role_succ_data, coup_id);
            role_succ_data
                .link_set
                .as_mut()
                .unwrap()
                .insert(coup_id, link);
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
        if let Some(reapply_queue_iterator) = reapply_queue_iterator {
            *reapply_queue_iterator = role_succ_data.reapply_queue.get_iterator(true);
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
        nodes: &Arena<IndividualProcessNode>,
        edges: &Arena<IndividualLinkEdge>,
        role: RoleId,
        link: EdgeId,
    ) -> &mut Self {
        let context = self.context;
        let role_succ_data = self.role_successor_data_hash.entry(role).or_default();
        if role_succ_data.link_set.is_some() {
            let coup_id = Self::get_coupled_individual_id_link(nodes, edges, link);
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
                    let coup = Self::get_coupled_individual_id_link(nodes, edges, link_it);
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
        nodes: &Arena<IndividualProcessNode>,
        edges: &Arena<IndividualLinkEdge>,
        role: RoleId,
        source_indi_id: Cint64,
        destination_indi_id: Cint64,
    ) -> &mut Self {
        let context = self.context;
        let searched_coupled_id =
            self.get_coupled_individual_id(source_indi_id, destination_indi_id);
        let role_succ_data = self.role_successor_data_hash.entry(role).or_default();
        if role_succ_data.link_set.is_some() {
            Self::ensure_role_successor_data_localated(context, role_succ_data);
            Self::eliminate_role_successor_previous_share_data(role_succ_data, searched_coupled_id);
            role_succ_data
                .link_set
                .as_mut()
                .unwrap()
                .remove(&searched_coupled_id);
        } else if role_succ_data.link_linker.is_some() {
            // replace by set
            let mut new_link_set: HashMap<Cint64, EdgeId> = HashMap::new();
            role_succ_data.located_link_set = true;
            let mut link_it = role_succ_data.link_linker;
            while link_it.is_some() {
                let coupled_id = Self::get_coupled_individual_id_link(nodes, edges, link_it);
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
        nodes: &Arena<IndividualProcessNode>,
        edges: &Arena<IndividualLinkEdge>,
        role: RoleId,
        source_indi_id: Cint64,
        destination_indi_id: Cint64,
        locateable: bool,
    ) -> EdgeId {
        let searched_coupled_id =
            self.get_coupled_individual_id(source_indi_id, destination_indi_id);
        if let Some(role_succ_data) = self.role_successor_data_hash.get_mut(&role) {
            if role_succ_data.link_linker.is_some() {
                if locateable && role_succ_data.link_set.is_none() && role_succ_data.link_count >= 5
                {
                    let mut new_link_set: HashMap<Cint64, EdgeId> = HashMap::new();
                    let mut link_it = role_succ_data.link_linker;
                    let mut searched_link = EdgeId::NONE;
                    while link_it.is_some() {
                        let coupled_id =
                            Self::get_coupled_individual_id_link(nodes, edges, link_it);
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
                        let coupled_id =
                            Self::get_coupled_individual_id_link(nodes, edges, link_it);
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
        nodes: &Arena<IndividualProcessNode>,
        edges: &Arena<IndividualLinkEdge>,
        role: RoleId,
        source_indi_id: Cint64,
        destination_indi_id: Cint64,
        locateable: bool,
    ) -> bool {
        let searched_link = self.get_role_successor_to_individual_link(
            nodes,
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
    pub fn get_role_reapply_queue(
        &mut self,
        role: RoleId,
        create: bool,
    ) -> Option<&mut ReapplyQueue> {
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
        if let Some(role_succ_data) = self.role_successor_data_hash.get(&role) {
            return !role_succ_data.reapply_queue.is_empty();
        }
        false
    }

    /// Port of `CReapplyRoleSuccessorHash::getRoleReapplyIterator`.
    ///
    pub fn get_role_reapply_iterator(
        &mut self,
        role: RoleId,
        clear_dynamic_reapply_queue: bool,
    ) -> ReapplyQueueIterator {
        if let Some(role_succ_data) = self.role_successor_data_hash.get_mut(&role) {
            return role_succ_data
                .reapply_queue
                .get_iterator(clear_dynamic_reapply_queue);
        }
        ReapplyQueueIterator::new(
            ReapplyConceptDescriptorId::NONE,
            ReapplyConceptDescriptorId::NONE,
        )
    }

    /// Port of `CReapplyRoleSuccessorHash::getRoleSuccessorLinkIterator(CRole*)`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: the C++ iterator can follow
    /// `mLinkLinker->getNext()` directly. The Rust snapshot needs the edge arena
    /// to resolve that chain, hence the additional `edges` parameter.
    pub fn get_role_successor_link_iterator(
        &self,
        edges: &Arena<IndividualLinkEdge>,
        role: RoleId,
    ) -> RoleSuccessorLinkIterator {
        if let Some(role_succ_data) = self.role_successor_data_hash.get(&role) {
            return RoleSuccessorLinkIterator::from_data(edges, role_succ_data);
        }
        RoleSuccessorLinkIterator::empty()
    }

    /// Port of `CReapplyRoleSuccessorHash::getRoleSuccessorLinkIterator(CRole*, cint64* linkCount)`.
    pub fn get_role_successor_link_iterator_count(
        &self,
        edges: &Arena<IndividualLinkEdge>,
        role: RoleId,
        link_count: Option<&mut Cint64>,
    ) -> RoleSuccessorLinkIterator {
        if let Some(role_succ_data) = self.role_successor_data_hash.get(&role) {
            if let Some(link_count) = link_count {
                *link_count = role_succ_data.link_count;
            }
            return RoleSuccessorLinkIterator::from_data(edges, role_succ_data);
        }
        RoleSuccessorLinkIterator::empty()
    }

    /// Port of `CReapplyRoleSuccessorHash::getRoleSuccessorLinkIterator(CRole*, cint64*, CIndividualLinkEdge*&)`.
    pub fn get_role_successor_link_iterator_count_last(
        &self,
        edges: &Arena<IndividualLinkEdge>,
        role: RoleId,
        link_count: Option<&mut Cint64>,
        last_link: &mut EdgeId,
    ) -> RoleSuccessorLinkIterator {
        if let Some(role_succ_data) = self.role_successor_data_hash.get(&role) {
            *last_link = role_succ_data.link_linker;
            if let Some(link_count) = link_count {
                *link_count = role_succ_data.link_count;
            }
            return RoleSuccessorLinkIterator::from_data(edges, role_succ_data);
        }
        RoleSuccessorLinkIterator::empty()
    }

    /// Port of `CReapplyRoleSuccessorHash::getRoleSuccessorHistoryLinkIterator(CRole*, CIndividualLinkEdge* lastLink)`.
    ///
    pub fn get_role_successor_history_link_iterator(
        &self,
        edges: &Arena<IndividualLinkEdge>,
        role: RoleId,
        last_link: EdgeId,
    ) -> RoleSuccessorLinkIterator {
        if let Some(role_succ_data) = self.role_successor_data_hash.get(&role) {
            return RoleSuccessorLinkIterator::from_chain(
                edges,
                role_succ_data.link_linker,
                last_link,
            );
        }
        RoleSuccessorLinkIterator::empty()
    }

    /// Port of `CReapplyRoleSuccessorHash::getRoleSuccessorHistoryLinkIterator(CRole*, CIndividualLinkEdge*, cint64*)`.
    pub fn get_role_successor_history_link_iterator_count(
        &self,
        edges: &Arena<IndividualLinkEdge>,
        role: RoleId,
        last_link: EdgeId,
        link_count: Option<&mut Cint64>,
    ) -> RoleSuccessorLinkIterator {
        if let Some(role_succ_data) = self.role_successor_data_hash.get(&role) {
            if let Some(link_count) = link_count {
                *link_count = role_succ_data.link_count;
            }
            return RoleSuccessorLinkIterator::from_chain(
                edges,
                role_succ_data.link_linker,
                last_link,
            );
        }
        RoleSuccessorLinkIterator::empty()
    }

    /// Port of `CReapplyRoleSuccessorHash::getRoleIterator`.
    pub fn get_role_iterator(&self) -> RoleSuccessorIterator {
        RoleSuccessorIterator::from_roles(
            self.role_successor_data_hash
                .iter()
                .filter_map(|(role, data)| {
                    if data.link_count > 0 {
                        Some(*role)
                    } else {
                        None
                    }
                })
                .collect(),
        )
    }

    /// Port of `CReapplyRoleSuccessorHash::getCoupledIndividualID(CIndividualLinkEdge*)`.
    ///
    fn get_coupled_individual_id_link(
        nodes: &Arena<IndividualProcessNode>,
        edges: &Arena<IndividualLinkEdge>,
        link: EdgeId,
    ) -> Cint64 {
        let edge = edges.get(link);
        nodes.get(edge.get_source_individual()).individual_node_id()
            + nodes
                .get(edge.get_destination_individual())
                .individual_node_id()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::konclude_ht::model::substrate::Id;
    use crate::konclude_ht::process::stubs::ProcessContextId;

    #[test]
    fn rs1_role_successor_iterator_overloads_write_count_and_last_link() {
        let mut nodes = Arena::new();
        let mut src = IndividualProcessNode::new(ProcessContextId::NONE);
        src.set_individual_node_id(10);
        let src = nodes.push(src);
        let mut dst = IndividualProcessNode::new(ProcessContextId::NONE);
        dst.set_individual_node_id(20);
        let dst = nodes.push(dst);

        let role = RoleId::new(3);
        let mut edges = Arena::new();
        let mut first = IndividualLinkEdge::new();
        first.init_individual_link_edge(src, src, dst, role, Id::NONE);
        let first = edges.push(first);
        let mut second = IndividualLinkEdge::new();
        second.init_individual_link_edge(src, src, dst, role, Id::NONE);
        let second = edges.push(second);

        let mut hash = ReapplyRoleSuccessorHash::new(0);
        hash.insert_role_successor_link(&nodes, &mut edges, role, first, None);
        hash.insert_role_successor_link(&nodes, &mut edges, role, second, None);

        let mut count = 0;
        let mut it = hash.get_role_successor_link_iterator_count(&edges, role, Some(&mut count));
        assert_eq!(count, 2);
        assert_eq!(it.next(true), second);
        assert_eq!(it.next(true), first);
        assert_eq!(it.next(true), EdgeId::NONE);

        let mut count = 0;
        let mut last_link = EdgeId::NONE;
        let mut it = hash.get_role_successor_link_iterator_count_last(
            &edges,
            role,
            Some(&mut count),
            &mut last_link,
        );
        assert_eq!(count, 2);
        assert_eq!(last_link, second);
        assert_eq!(it.next(true), second);

        let mut count = 0;
        let mut history = hash.get_role_successor_history_link_iterator_count(
            &edges,
            role,
            first,
            Some(&mut count),
        );
        assert_eq!(count, 2);
        assert_eq!(history.next(true), second);
        assert_eq!(history.next(true), EdgeId::NONE);
    }
}
