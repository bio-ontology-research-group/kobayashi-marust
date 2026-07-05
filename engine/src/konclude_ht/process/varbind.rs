//! `process::varbind` (port unit W2.7) — the variable-binding-path "process
//! satellite" subsystem of the completion graph.
//!
//! Ports the Konclude `Source/Reasoner/Kernel/Process/` classes that model the
//! propagation of variable bindings along the completion graph (the data behind
//! the `applyVARBIND*Rule` answering-propagation rules and the join machinery in
//! `completion/u11.rs` / `u33.rs`). In the W2 wave these were stubbed as fieldless
//! markers in `process::stubs` (`ConceptVariableBindingPathSetHash`,
//! `VariableBindingPathMergingHash`, `RepresentativeVariableBindingPath*`, …); this
//! unit fills them for real so the deferred `u11`/`u33` bodies can later un-defer.
//!
//! Classes ported here (one Rust struct per C++ class, `/// Port of …`):
//!   * `CVariableBinding`                       — a (variable ↦ individual) binding
//!   * `CVariableBindingDescriptor`             — sorted linker over bindings
//!   * `CVariableBindingPath`                   — a propagation path (id + binding chain)
//!   * `CVariableBindingPathDescriptor`         — linker over paths (+ dep-tracker)
//!   * `CVariableBindingPathMapData`            — the per-path map value
//!   * `CVariableBindingPathMap`                — propID → path-map-data
//!   * `CVariableBindingPathSet`               — a concept's set of paths
//!   * `CVariableBindingPathJoiningData`        — a pending left/right join record
//!   * `CVariableBindingPathJoiningHashData`    — its loc/use hash slot
//!   * `CVariableBindingPathJoiningHasher`      — the structural-equivalence key
//!   * `CVariableBindingPathJoiningHash`        — the joining hash
//!   * `CVariableBindingTriggerLinker`          — a queued join trigger
//!   * `CVariableBindingTriggerData`            — the per-(var,indi) trigger slot
//!   * `CVariableBindingTriggerHash`            — the trigger hash
//!   * `CVariableBindingPathMergingHashData`    — the merged-path cache value
//!   * `CVariableBindingPathMergingHash`        — the merged-path cache
//!   * `CRepresentativeVariableBindingPathMapData` — representative-map value
//!   * `CRepresentativeVariableBindingPathMap`  — propID → representative-map-data
//!
//! ## Memory model (the global `[ownership]` decision, `model/substrate.rs`)
//!
//! Every `CXxx*` becomes a typed arena `Id<T>` (`Id::NONE` == `nullptr`); the
//! per-test pool objects (`CVariableBinding`, the two descriptor kinds, the path,
//! the path set, the joining data, the trigger linker) get an `Arena<T>` field on
//! `ProcessContext` (listed in `// W2.7-ARENA-ADDITIONS` at the foot of this file —
//! the reconcile wires them in `process/context.rs`).
//!
//! KONCLUDE-PORT-NOTE[ownership]: the intrusive `CLinkerBase`/`CSortedLinkerBase`
//! chains are kept as the C++ has them — an in-node `next: Id<Self>` plus a `data`
//! field — rather than collapsed to an owner-`Vec`, because here the linker node IS
//! the satellite object and is referenced (and chain-walked) from several places
//! (`CVariableBindingPath`, the join data, the path set, the trigger data). The
//! per-node trivial accessors (`getData`/`setData`/`getNext`/`setNext`/the flag
//! get/sets) are ported as `&self`/`&mut self` methods; the chain-walking /
//! allocating operations (`append`, `getCount`, `insertSortedNextSorted`, the hash
//! computers, the key-equivalence walks) are ported as **associated functions that
//! take `ctx: &(mut) ProcessContext` + the relevant `Id`s** — the same
//! `ctx.<arena>(id)` deref idiom the W3.5 accessor convention prescribes — so a
//! receiver borrowed out of `ctx` never aliases a second `ctx` borrow.
//!
//! KONCLUDE-PORT-NOTE[pointer-alias]: where Konclude hashes raw pointers
//! (`(cint64)variableBinding`) or orders `CVariable*` with `<`/`<=`, the port uses
//! the corresponding arena `Id::raw` (a stable per-test integer that orders/identifies
//! the same objects). Behaviour matches: same objects hash/compare equal.

#![allow(
    dead_code,
    unused_variables,
    unused_mut,
    clippy::collapsible_if,
    clippy::collapsible_else_if,
    clippy::needless_return,
    clippy::type_complexity
)]

use std::collections::HashMap;

use super::super::model::substrate::{Cint64, Id, INVALID};
use super::super::model::VariableId;
use super::context::ProcessContext;
use super::representative::RepresentativeVariableBindingPathSetDataId;
use super::{ConDescId, NodeId, TrackPointId};

// ===========================================================================
// Process-layer id aliases for the W2.7 satellites (the `Id<T>` per ported class).
// ===========================================================================
/// `CVariableBinding*`                  → `VarBindingId`.
pub type VarBindingId = Id<VariableBinding>;
/// `CVariableBindingDescriptor*`        → `VarBindingDescriptorId`.
pub type VarBindingDescriptorId = Id<VariableBindingDescriptor>;
/// `CVariableBindingPath*`              → `VarBindingPathId`.
pub type VarBindingPathId = Id<VariableBindingPath>;
/// `CVariableBindingPathDescriptor*`    → `VarBindingPathDescriptorId`.
pub type VarBindingPathDescriptorId = Id<VariableBindingPathDescriptor>;
/// `CVariableBindingPathSet*`           → `VarBindingPathSetId`.
pub type VarBindingPathSetId = Id<VariableBindingPathSet>;
/// `CVariableBindingPathJoiningData*`   → `VarBindingPathJoiningDataId`.
pub type VarBindingPathJoiningDataId = Id<VariableBindingPathJoiningData>;
/// `CVariableBindingPathJoiningHash*`   -> `VariableBindingPathJoiningHashId`.
pub type VariableBindingPathJoiningHashId = Id<VariableBindingPathJoiningHash>;
/// `CVariableBindingPathMergingHash*`   -> `VariableBindingPathMergingHashId`.
pub type VariableBindingPathMergingHashId = Id<VariableBindingPathMergingHash>;
/// `CVariableBindingTriggerLinker*`     → `VarBindingTriggerLinkerId`.
pub type VarBindingTriggerLinkerId = Id<VariableBindingTriggerLinker>;
/// `CVariableBindingTriggerHash*`       -> `VariableBindingTriggerHashId`.
pub type VariableBindingTriggerHashId = Id<VariableBindingTriggerHash>;

// ===========================================================================
// CVariableBinding
// (`CVariableBinding.{h,cpp}`, `: public CDependencyTracker`)
// ===========================================================================

/// Port of `CVariableBinding`.
///
/// KONCLUDE-PORT-NOTE[ownership]: the `CDependencyTracker` base is folded in as the
/// `dep_track_point` field (exactly as `process/node.rs` folds it). `CVariable*` →
/// `VariableId`, `CIndividualProcessNode*` → `NodeId`.
pub struct VariableBinding {
    /// `CDependencyTracker::mDependencyTrackPoint`.
    pub dep_track_point: TrackPointId,
    /// `CVariable* mVariable`.
    pub variable: VariableId,
    /// `CIndividualProcessNode* mIndiNode`.
    pub indi_node: NodeId,
}

impl Default for VariableBinding {
    fn default() -> Self {
        VariableBinding {
            dep_track_point: Id::NONE,
            variable: Id::NONE,
            indi_node: Id::NONE,
        }
    }
}

impl VariableBinding {
    /// Port of `CVariableBinding::CVariableBinding`.
    pub fn new() -> Self {
        VariableBinding::default()
    }

    /// Port of `CVariableBinding::initVariableBinding`.
    pub fn init_variable_binding(
        &mut self,
        dependency_track_point: TrackPointId,
        indi: NodeId,
        variable: VariableId,
    ) -> &mut Self {
        // initDependencyTracker(dependencyTrackPoint)
        self.dep_track_point = dependency_track_point;
        self.variable = variable;
        self.indi_node = indi;
        self
    }

    /// Port of `getBindedVariable`.
    pub fn get_binded_variable(&self) -> VariableId {
        self.variable
    }
    /// Port of `setBindedVariable`.
    pub fn set_binded_variable(&mut self, variable: VariableId) -> &mut Self {
        self.variable = variable;
        self
    }

    /// Port of `getBindedIndividual`.
    pub fn get_binded_individual(&self) -> NodeId {
        self.indi_node
    }
    /// Port of `setBindedIndividual`.
    pub fn set_binded_individual(&mut self, indi: NodeId) -> &mut Self {
        self.indi_node = indi;
        self
    }

    /// Port of `CDependencyTracker::getDependencyTrackPoint`.
    pub fn get_dependency_track_point(&self) -> TrackPointId {
        self.dep_track_point
    }
    /// Port of `CDependencyTracker::setDependencyTrackPoint`.
    pub fn set_dependency_track_point(&mut self, dtp: TrackPointId) -> &mut Self {
        self.dep_track_point = dtp;
        self
    }

    /// Port of `CVariableBinding::operator<=(const CVariableBinding&)`
    /// (and the `*&` overload — identical body).
    ///
    /// KONCLUDE-PORT-NOTE[pointer-alias]: `getBindedVariable() <= other.getBindedVariable()`
    /// orders `CVariable*` pointers; the port orders the `VariableId.raw`.
    pub fn le_binding(&self, other: &VariableBinding) -> bool {
        self.variable.raw <= other.variable.raw
    }
}

// ===========================================================================
// CVariableBindingDescriptor
// (`CVariableBindingDescriptor.{h,cpp}`,
//  `: public CSortedLinkerBase<CVariableBinding*,CVariableBindingDescriptor>`)
// ===========================================================================

/// Port of `CVariableBindingDescriptor`.
///
/// KONCLUDE-PORT-NOTE[ownership]: the `CSortedLinkerBase<CVariableBinding*,Self>`
/// base contributes the `data` (the binding) + `next` (the sorted chain link).
pub struct VariableBindingDescriptor {
    /// `CSortedLinkerBase::data` (`CVariableBinding*`).
    pub data: VarBindingId,
    /// `CSortedLinkerBase::next`.
    pub next: VarBindingDescriptorId,
}

impl Default for VariableBindingDescriptor {
    fn default() -> Self {
        VariableBindingDescriptor {
            data: Id::NONE,
            next: Id::NONE,
        }
    }
}

impl VariableBindingDescriptor {
    /// Port of `CVariableBindingDescriptor::CVariableBindingDescriptor` (`data = nullptr`).
    pub fn new() -> Self {
        VariableBindingDescriptor::default()
    }

    /// Port of `getVariableBinding` (`return data`).
    pub fn get_variable_binding(&self) -> VarBindingId {
        self.data
    }

    /// Port of `initVariableBindingDescriptor` (`setData(propBinding)`).
    pub fn init_variable_binding_descriptor(&mut self, prop_binding: VarBindingId) -> &mut Self {
        self.data = prop_binding;
        self
    }

    /// Port of `CSortedLinkerBase::getData`.
    pub fn get_data(&self) -> VarBindingId {
        self.data
    }
    /// Port of `CSortedLinkerBase::setData`.
    pub fn set_data(&mut self, data: VarBindingId) -> &mut Self {
        self.data = data;
        self
    }
    /// Port of `CSortedLinkerBase::getNext`.
    pub fn get_next(&self) -> VarBindingDescriptorId {
        self.next
    }
    /// Port of `CSortedLinkerBase::setNext`.
    pub fn set_next(&mut self, next: VarBindingDescriptorId) -> &mut Self {
        self.next = next;
        self
    }
    /// Port of `CLinkerBase::hasNext`.
    pub fn has_next(&self) -> bool {
        self.next.is_some()
    }

    /// Port of `CLinkerBase<…>::getCount` (walk the chain from `head`).
    pub fn get_count(ctx: &ProcessContext, head: VarBindingDescriptorId) -> Cint64 {
        let mut linker_count: Cint64 = 0;
        let mut item_linker = head;
        while item_linker.is_some() {
            linker_count += 1;
            item_linker = ctx.var_binding_des(item_linker).get_next();
        }
        linker_count
    }

    /// Port of `CLinkerBase<…>::append` (tail-splice; returns the head `this`).
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: walks `this`'s chain to its last link and sets
    /// that link's `next` to `appending_list`, returning `this` (the unchanged head).
    pub fn append(
        ctx: &mut ProcessContext,
        this: VarBindingDescriptorId,
        appending_list: VarBindingDescriptorId,
    ) -> VarBindingDescriptorId {
        // getLastListLink(): walk to the tail.
        let mut last = this;
        while ctx.var_binding_des(last).has_next() {
            last = ctx.var_binding_des(last).get_next();
        }
        ctx.var_binding_des_mut(last).set_next(appending_list);
        this
    }

    /// Port of `CSortedLinker<T*>::insertSortedNextSorted` (`CSortedLinker.hpp`).
    /// Inserts the (already-sorted) `next_link` chain into `this` (sorted by the
    /// binding `operator<=`), returning the new head (`firstLinker`).
    pub fn insert_sorted_next_sorted(
        ctx: &mut ProcessContext,
        this: VarBindingDescriptorId,
        mut next_link: VarBindingDescriptorId,
    ) -> VarBindingDescriptorId {
        // items from nextLink are already sorted!
        let mut first_linker = this;

        while next_link.is_some() {
            let n_ins = next_link;

            if ctx.var_binding_des(next_link).has_next() {
                next_link = ctx.var_binding_des(next_link).get_next();
            } else {
                next_link = Id::NONE;
            }
            ctx.var_binding_des_mut(n_ins).set_next(Id::NONE);

            let mut inserted = false;
            let data_ins = ctx.var_binding_des(n_ins).get_data();

            let mut list = first_linker;
            let mut last_list: VarBindingDescriptorId = Id::NONE;
            while list.is_some() {
                let data_list = ctx.var_binding_des(list).get_data();
                // *dataIns <= *dataList
                if Self::binding_le(ctx, data_ins, data_list) {
                    if last_list.is_none() {
                        // firstLinker = nIns->insertNext(firstLinker)
                        first_linker = Self::insert_next(ctx, n_ins, first_linker);
                        list = ctx.var_binding_des(first_linker).get_next();
                        last_list = first_linker;
                    } else {
                        // lastList->insertNext(nIns)
                        Self::insert_next(ctx, last_list, n_ins);
                        last_list = ctx.var_binding_des(last_list).get_next();
                        // list is already on the correct position
                    }
                    inserted = true;
                    break;
                }
                last_list = list;
                list = ctx.var_binding_des(list).get_next();
            }
            if !inserted {
                // lastList->insertNext(nIns)
                Self::insert_next(ctx, last_list, n_ins);
            }
        }
        first_linker
    }

    /// Port of `CLinkerBase::insertNext` (splice `next_link` chain in after `this`).
    fn insert_next(
        ctx: &mut ProcessContext,
        this: VarBindingDescriptorId,
        next_link: VarBindingDescriptorId,
    ) -> VarBindingDescriptorId {
        if next_link.is_some() {
            let tmp_next = ctx.var_binding_des(this).get_next();
            ctx.var_binding_des_mut(this).set_next(next_link);
            if tmp_next.is_some() {
                Self::append(ctx, next_link, tmp_next);
            }
        }
        this
    }

    /// `*dataIns <= *dataList` — `CVariableBinding::operator<=` over two binding ids.
    fn binding_le(ctx: &ProcessContext, ins: VarBindingId, list: VarBindingId) -> bool {
        let ins_var = ctx.var_binding(ins).get_binded_variable();
        let list_var = ctx.var_binding(list).get_binded_variable();
        ins_var.raw <= list_var.raw
    }
}

// ===========================================================================
// CVariableBindingPath
// (`CVariableBindingPath.{h,cpp}`)
// ===========================================================================

/// Port of `CVariableBindingPath`.
pub struct VariableBindingPath {
    /// `cint64 mPropID`.
    pub prop_id: Cint64,
    /// `CVariableBindingDescriptor* mVarBindDesLinker`.
    pub var_bind_des_linker: VarBindingDescriptorId,
}

impl Default for VariableBindingPath {
    fn default() -> Self {
        VariableBindingPath {
            prop_id: 0,
            var_bind_des_linker: Id::NONE,
        }
    }
}

impl VariableBindingPath {
    /// Port of `CVariableBindingPath::CVariableBindingPath`.
    pub fn new() -> Self {
        VariableBindingPath::default()
    }

    /// Port of `getPropagationID`.
    pub fn get_propagation_id(&self) -> Cint64 {
        self.prop_id
    }
    /// Port of `setPropagationID`.
    pub fn set_propagation_id(&mut self, prop_id: Cint64) -> &mut Self {
        self.prop_id = prop_id;
        self
    }

    /// Port of `initVariableBindingPath`.
    pub fn init_variable_binding_path(
        &mut self,
        prop_id: Cint64,
        var_bind_des_linker: VarBindingDescriptorId,
    ) -> &mut Self {
        self.prop_id = prop_id;
        self.var_bind_des_linker = var_bind_des_linker;
        self
    }

    /// Port of `getVariableBindingDescriptorLinker`.
    pub fn get_variable_binding_descriptor_linker(&self) -> VarBindingDescriptorId {
        self.var_bind_des_linker
    }

    /// Port of `getVariableBindingCount`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: `mVarBindDesLinker->getCount()` walks the
    /// descriptor arena, so this is an associated fn taking `ctx` + the path id.
    pub fn get_variable_binding_count(ctx: &ProcessContext, this: VarBindingPathId) -> Cint64 {
        let linker = ctx.vbpath(this).var_bind_des_linker;
        if linker.is_none() {
            0
        } else {
            VariableBindingDescriptor::get_count(ctx, linker)
        }
    }

    /// Port of `addVariableBindingDescriptorLinker`.
    pub fn add_variable_binding_descriptor_linker(
        ctx: &mut ProcessContext,
        this: VarBindingPathId,
        var_bind_des_linker: VarBindingDescriptorId,
    ) {
        let cur = ctx.vbpath(this).var_bind_des_linker;
        let new_head = if cur.is_some() {
            VariableBindingDescriptor::insert_sorted_next_sorted(ctx, cur, var_bind_des_linker)
        } else {
            var_bind_des_linker
        };
        ctx.vbpath_mut(this).var_bind_des_linker = new_head;
    }
}

// ===========================================================================
// CVariableBindingPathMapData
// (`CVariableBindingPathMapData.{h,cpp}`)
// ===========================================================================

/// Port of `CVariableBindingPathMapData`.
#[derive(Copy, Clone)]
pub struct VariableBindingPathMapData {
    /// `CVariableBindingPathDescriptor* mPropBindDes`.
    pub prop_bind_des: VarBindingPathDescriptorId,
}

impl Default for VariableBindingPathMapData {
    fn default() -> Self {
        VariableBindingPathMapData {
            prop_bind_des: Id::NONE,
        }
    }
}

impl VariableBindingPathMapData {
    /// Port of `CVariableBindingPathMapData::CVariableBindingPathMapData(propBindDes = nullptr)`.
    pub fn new(prop_bind_des: VarBindingPathDescriptorId) -> Self {
        VariableBindingPathMapData { prop_bind_des }
    }

    /// Port of `getVariableBindingPathDescriptor`.
    pub fn get_variable_binding_path_descriptor(&self) -> VarBindingPathDescriptorId {
        self.prop_bind_des
    }
    /// Port of `hasVariableBindingPathDescriptor`.
    pub fn has_variable_binding_path_descriptor(&self) -> bool {
        self.prop_bind_des.is_some()
    }
    /// Port of `setVariableBindingPathDescriptor`.
    pub fn set_variable_binding_path_descriptor(
        &mut self,
        des: VarBindingPathDescriptorId,
    ) -> &mut Self {
        self.prop_bind_des = des;
        self
    }
}

// ===========================================================================
// CVariableBindingPathDescriptor
// (`CVariableBindingPathDescriptor.{h,cpp}`,
//  `: public CLinkerBase<CVariableBindingPath*,Self>, public CDependencyTracker`)
// ===========================================================================

/// Port of `CVariableBindingPathDescriptor`.
///
/// KONCLUDE-PORT-NOTE[ownership]: the `CLinkerBase<CVariableBindingPath*,Self>` base
/// gives `data` (the path) + `next`; the `CDependencyTracker` base gives
/// `dep_track_point`.
pub struct VariableBindingPathDescriptor {
    /// `CLinkerBase::data` (`CVariableBindingPath*`).
    pub data: VarBindingPathId,
    /// `CLinkerBase::next`.
    pub next: VarBindingPathDescriptorId,
    /// `CDependencyTracker::mDependencyTrackPoint`.
    pub dep_track_point: TrackPointId,
}

impl Default for VariableBindingPathDescriptor {
    fn default() -> Self {
        VariableBindingPathDescriptor {
            data: Id::NONE,
            next: Id::NONE,
            dep_track_point: Id::NONE,
        }
    }
}

impl VariableBindingPathDescriptor {
    /// Port of `CVariableBindingPathDescriptor::CVariableBindingPathDescriptor` (`data = nullptr`).
    pub fn new() -> Self {
        VariableBindingPathDescriptor::default()
    }

    /// Port of `getVariableBindingPath` (`return getData()`).
    pub fn get_variable_binding_path(&self) -> VarBindingPathId {
        self.data
    }

    /// Port of `initVariableBindingPathDescriptor`.
    pub fn init_variable_binding_path_descriptor(
        &mut self,
        var_bind_path: VarBindingPathId,
        dependency_track_point: TrackPointId,
    ) -> &mut Self {
        // initDependencyTracker(dependencyTrackPoint)
        self.dep_track_point = dependency_track_point;
        // setData(varBindPath)
        self.data = var_bind_path;
        self
    }

    /// Port of `CLinkerBase::getData`.
    pub fn get_data(&self) -> VarBindingPathId {
        self.data
    }
    /// Port of `CLinkerBase::setData`.
    pub fn set_data(&mut self, data: VarBindingPathId) -> &mut Self {
        self.data = data;
        self
    }
    /// Port of `CLinkerBase::getNext`.
    pub fn get_next(&self) -> VarBindingPathDescriptorId {
        self.next
    }
    /// Port of `CLinkerBase::setNext`.
    pub fn set_next(&mut self, next: VarBindingPathDescriptorId) -> &mut Self {
        self.next = next;
        self
    }
    /// Port of `CLinkerBase::hasNext`.
    pub fn has_next(&self) -> bool {
        self.next.is_some()
    }

    /// Port of `CDependencyTracker::getDependencyTrackPoint`.
    pub fn get_dependency_track_point(&self) -> TrackPointId {
        self.dep_track_point
    }
    /// Port of `CDependencyTracker::setDependencyTrackPoint`.
    pub fn set_dependency_track_point(&mut self, dtp: TrackPointId) -> &mut Self {
        self.dep_track_point = dtp;
        self
    }

    /// Port of `CLinkerBase<…>::append` (tail-splice; returns the head `this`).
    pub fn append(
        ctx: &mut ProcessContext,
        this: VarBindingPathDescriptorId,
        appending_list: VarBindingPathDescriptorId,
    ) -> VarBindingPathDescriptorId {
        let mut last = this;
        while ctx.vbpath_des(last).has_next() {
            last = ctx.vbpath_des(last).get_next();
        }
        ctx.vbpath_des_mut(last).set_next(appending_list);
        this
    }
}

// ===========================================================================
// CVariableBindingPathMap
// (`CVariableBindingPathMap.{h,cpp}`, `: public CPROCESSMAP<cint64,…MapData>`)
// ===========================================================================

/// Port of `CVariableBindingPathMap`.
///
/// KONCLUDE-PORT-NOTE[ownership]: the `CPROCESSMAP<cint64,CVariableBindingPathMapData>`
/// base becomes the `map` field (`cint64` propID key → map-data value). Held BY
/// VALUE by `CVariableBindingPathSet`, so it is not an arena element. `mProcessContext`
/// stays an opaque `Cint64` (as in `process/satellites.rs`).
#[derive(Clone)]
pub struct VariableBindingPathMap {
    /// `CProcessContext* mProcessContext` (opaque handle).
    pub process_context: Cint64,
    /// the `CPROCESSMAP<cint64,…MapData>` base storage.
    pub map: HashMap<Cint64, VariableBindingPathMapData>,
}

impl VariableBindingPathMap {
    /// Port of `CVariableBindingPathMap::CVariableBindingPathMap(CProcessContext*)`.
    pub fn new(process_context: Cint64) -> Self {
        VariableBindingPathMap {
            process_context,
            map: HashMap::new(),
        }
    }

    /// Port of `initVariableBindingPathMap` (operator= from prev, else clear).
    pub fn init_variable_binding_path_map(
        &mut self,
        prev_map: Option<&VariableBindingPathMap>,
    ) -> &mut Self {
        if let Some(prev) = prev_map {
            self.map = prev.map.clone();
        } else {
            self.map.clear();
        }
        self
    }

    /// Port of `CPROCESSMAP::contains`.
    pub fn contains(&self, key: Cint64) -> bool {
        self.map.contains_key(&key)
    }

    /// Port of `CPROCESSMAP::count`.
    pub fn count(&self) -> Cint64 {
        self.map.len() as Cint64
    }

    /// Port of `CPROCESSMAP::value` (returns a copy; default-constructed when absent).
    pub fn value(&self, key: Cint64) -> VariableBindingPathMapData {
        self.map.get(&key).copied().unwrap_or_default()
    }

    /// Port of `CPROCESSMAP::operator[]` (insert-default-then-borrow).
    pub fn entry_mut(&mut self, key: Cint64) -> &mut VariableBindingPathMapData {
        self.map.entry(key).or_default()
    }
}

// ===========================================================================
// CVariableBindingPathSet
// (`CVariableBindingPathSet.{h,cpp}`)
// ===========================================================================

/// Port of `CVariableBindingPathSet`.
///
/// KONCLUDE-PORT-NOTE[ownership]: `mVarBindPathMap` is held BY VALUE; the pointer
/// members become ids; `mProcessContext` stays opaque `Cint64`.
pub struct VariableBindingPathSet {
    /// `CProcessContext* mProcessContext` (opaque).
    pub process_context: Cint64,
    /// `CVariableBindingPathMap mVarBindPathMap` (by value).
    pub var_bind_path_map: VariableBindingPathMap,
    /// `CConceptDescriptor* mConceptDescriptor`.
    pub concept_descriptor: ConDescId,
    /// `CVariableBindingPathDescriptor* mVarBindPathDesLinker`.
    pub var_bind_path_des_linker: VarBindingPathDescriptorId,
}

impl VariableBindingPathSet {
    /// Port of `CVariableBindingPathSet::CVariableBindingPathSet(CProcessContext*)`.
    pub fn new(process_context: Cint64) -> Self {
        VariableBindingPathSet {
            process_context,
            var_bind_path_map: VariableBindingPathMap::new(process_context),
            concept_descriptor: Id::NONE,
            var_bind_path_des_linker: Id::NONE,
        }
    }

    /// Port of `initVariableBindingPathSet`.
    pub fn init_variable_binding_path_set(
        &mut self,
        prev_set: Option<&VariableBindingPathSet>,
    ) -> &mut Self {
        if let Some(prev) = prev_set {
            self.var_bind_path_map
                .init_variable_binding_path_map(Some(&prev.var_bind_path_map));
            self.concept_descriptor = prev.concept_descriptor;
            self.var_bind_path_des_linker = prev.var_bind_path_des_linker;
        } else {
            self.var_bind_path_map.init_variable_binding_path_map(None);
            self.concept_descriptor = Id::NONE;
            self.var_bind_path_des_linker = Id::NONE;
        }
        self
    }

    /// Port of `getVariableBindingPathMap`.
    pub fn get_variable_binding_path_map(&self) -> &VariableBindingPathMap {
        &self.var_bind_path_map
    }
    /// Mutable companion (`getVariableBindingPathMap` used as an lvalue).
    pub fn get_variable_binding_path_map_mut(&mut self) -> &mut VariableBindingPathMap {
        &mut self.var_bind_path_map
    }

    /// Port of `containsVariableBindingPath(CVariableBindingPath*)`.
    pub fn contains_variable_binding_path_for_path(
        &self,
        ctx: &ProcessContext,
        variable_binding_path: VarBindingPathId,
    ) -> bool {
        self.var_bind_path_map
            .contains(ctx.vbpath(variable_binding_path).get_propagation_id())
    }

    /// Port of `containsVariableBindingPath(cint64 bindingID)`.
    pub fn contains_variable_binding_path_for_id(&self, binding_id: Cint64) -> bool {
        self.var_bind_path_map.contains(binding_id)
    }

    /// Port of `getVariableBindingPathDescriptor`.
    pub fn get_variable_binding_path_descriptor(
        &self,
        ctx: &ProcessContext,
        variable_binding_path: VarBindingPathId,
    ) -> VarBindingPathDescriptorId {
        self.var_bind_path_map
            .value(ctx.vbpath(variable_binding_path).get_propagation_id())
            .get_variable_binding_path_descriptor()
    }

    /// Port of `addVariableBindingPath`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: split into ordered sub-borrows — `append`
    /// touches only the path-descriptor arena while the map mutation touches only the
    /// set; the two never overlap, mirroring the single C++ statement sequence.
    pub fn add_variable_binding_path(
        ctx: &mut ProcessContext,
        this: VarBindingPathSetId,
        var_bind_path_des: VarBindingPathDescriptorId,
    ) {
        // varBindPathDes->getVariableBindingPath()->getPropagationID()
        let path = ctx
            .vbpath_des(var_bind_path_des)
            .get_variable_binding_path();
        let prop_id = ctx.vbpath(path).get_propagation_id();

        // CVariableBindingPathMapData& data = mVarBindPathMap[propID];
        let has_des = ctx
            .vbpath_set(this)
            .var_bind_path_map
            .value(prop_id)
            .has_variable_binding_path_descriptor();
        // operator[] inserts a default if absent (so the key now exists, des == NONE).
        ctx.vbpath_set_mut(this)
            .var_bind_path_map
            .entry_mut(prop_id);

        if !has_des {
            // data.setVariableBindingPathDescriptor(varBindPathDes)
            ctx.vbpath_set_mut(this)
                .var_bind_path_map
                .entry_mut(prop_id)
                .set_variable_binding_path_descriptor(var_bind_path_des);
            // mVarBindPathDesLinker = varBindPathDes->append(mVarBindPathDesLinker)
            let old_head = ctx.vbpath_set(this).var_bind_path_des_linker;
            let new_head = VariableBindingPathDescriptor::append(ctx, var_bind_path_des, old_head);
            ctx.vbpath_set_mut(this).var_bind_path_des_linker = new_head;
        }
    }

    /// Port of `copyVariableBindingPaths` (`mVarBindPathMap = *varBindPathMap`).
    pub fn copy_variable_binding_paths(
        &mut self,
        var_bind_path_map: Option<&VariableBindingPathMap>,
    ) -> &mut Self {
        if let Some(m) = var_bind_path_map {
            self.var_bind_path_map = m.clone();
        }
        self
    }

    /// Port of `getConceptDescriptor`.
    pub fn get_concept_descriptor(&self) -> ConDescId {
        self.concept_descriptor
    }
    /// Port of `setConceptDescriptor`.
    pub fn set_concept_descriptor(&mut self, con_des: ConDescId) -> &mut Self {
        self.concept_descriptor = con_des;
        self
    }

    /// Port of `addVariableBindingPathDescriptorLinker`
    /// (`mVarBindPathDesLinker = varBindPathDesLinker->append(mVarBindPathDesLinker)`).
    pub fn add_variable_binding_path_descriptor_linker(
        ctx: &mut ProcessContext,
        this: VarBindingPathSetId,
        var_bind_path_des_linker: VarBindingPathDescriptorId,
    ) {
        let old_head = ctx.vbpath_set(this).var_bind_path_des_linker;
        let new_head =
            VariableBindingPathDescriptor::append(ctx, var_bind_path_des_linker, old_head);
        ctx.vbpath_set_mut(this).var_bind_path_des_linker = new_head;
    }

    /// Port of `getVariableBindingPathDescriptorLinker`.
    pub fn get_variable_binding_path_descriptor_linker(&self) -> VarBindingPathDescriptorId {
        self.var_bind_path_des_linker
    }
}

// ===========================================================================
// CVariableBindingPathJoiningData
// (`CVariableBindingPathJoiningData.{h,cpp}`)
// ===========================================================================

/// Port of `CVariableBindingPathJoiningData`.
pub struct VariableBindingPathJoiningData {
    /// `mutable cint64 mCalculatedHashValue`.
    pub calculated_hash_value: Cint64,
    /// `mutable bool mHashValueCalculated`.
    pub hash_value_calculated: bool,
    /// `CVariableBindingDescriptor* mKeyVarBindDesLinker`.
    pub key_var_bind_des_linker: VarBindingDescriptorId,
    /// `CVariableBindingPathDescriptor* mLeftVarBindPathDesLinker`.
    pub left_var_bind_path_des_linker: VarBindingPathDescriptorId,
    /// `CVariableBindingPathDescriptor* mRightVarBindPathDesLinker`.
    pub right_var_bind_path_des_linker: VarBindingPathDescriptorId,
    /// `bool mAllKeyTriggersAvailable`.
    pub all_key_triggers_available: bool,
    /// `CVariableBindingDescriptor* mNextKeyTriggerLinker`.
    pub next_key_trigger_linker: VarBindingDescriptorId,
}

impl Default for VariableBindingPathJoiningData {
    fn default() -> Self {
        VariableBindingPathJoiningData {
            calculated_hash_value: 0,
            hash_value_calculated: false,
            key_var_bind_des_linker: Id::NONE,
            left_var_bind_path_des_linker: Id::NONE,
            right_var_bind_path_des_linker: Id::NONE,
            all_key_triggers_available: false,
            next_key_trigger_linker: Id::NONE,
        }
    }
}

impl VariableBindingPathJoiningData {
    /// Port of `CVariableBindingPathJoiningData::CVariableBindingPathJoiningData`.
    pub fn new() -> Self {
        VariableBindingPathJoiningData::default()
    }

    /// Port of `initVariableBindingPathJoiningData(CVariableBindingPathJoiningData* prevJoinData)`.
    pub fn init_from_prev(
        ctx: &mut ProcessContext,
        this: VarBindingPathJoiningDataId,
        prev: VarBindingPathJoiningDataId,
    ) {
        if prev.is_some() {
            let p = ctx.vbpath_join_data(prev);
            let (kv, lv, rv, hc, chv, akt, nkt) = (
                p.key_var_bind_des_linker,
                p.left_var_bind_path_des_linker,
                p.right_var_bind_path_des_linker,
                p.hash_value_calculated,
                p.calculated_hash_value,
                p.all_key_triggers_available,
                p.next_key_trigger_linker,
            );
            let d = ctx.vbpath_join_data_mut(this);
            d.key_var_bind_des_linker = kv;
            d.left_var_bind_path_des_linker = lv;
            d.right_var_bind_path_des_linker = rv;
            d.hash_value_calculated = hc;
            d.calculated_hash_value = chv;
            d.all_key_triggers_available = akt;
            d.next_key_trigger_linker = nkt;
        } else {
            let d = ctx.vbpath_join_data_mut(this);
            d.key_var_bind_des_linker = Id::NONE;
            d.left_var_bind_path_des_linker = Id::NONE;
            d.right_var_bind_path_des_linker = Id::NONE;
            d.hash_value_calculated = false;
            d.calculated_hash_value = 0;
            d.all_key_triggers_available = false;
            d.next_key_trigger_linker = Id::NONE;
        }
    }

    /// Port of `initVariableBindingPathJoiningData(keyVarBindDesLinker, leftVarBindPathDesLinker, rightVarBindPathDesLinker)`.
    pub fn init_variable_binding_path_joining_data(
        &mut self,
        key_var_bind_des_linker: VarBindingDescriptorId,
        left_var_bind_path_des_linker: VarBindingPathDescriptorId,
        right_var_bind_path_des_linker: VarBindingPathDescriptorId,
    ) -> &mut Self {
        self.key_var_bind_des_linker = key_var_bind_des_linker;
        self.left_var_bind_path_des_linker = left_var_bind_path_des_linker;
        self.right_var_bind_path_des_linker = right_var_bind_path_des_linker;
        self.hash_value_calculated = false;
        self.calculated_hash_value = 0;
        self.all_key_triggers_available = false;
        self.next_key_trigger_linker = Id::NONE;
        self
    }

    /// Port of `getKeyVariableBindingDescriptorLinker`.
    pub fn get_key_variable_binding_descriptor_linker(&self) -> VarBindingDescriptorId {
        self.key_var_bind_des_linker
    }
    /// Port of `getLeftVariableBindingPathDescriptorLinker`.
    pub fn get_left_variable_binding_path_descriptor_linker(&self) -> VarBindingPathDescriptorId {
        self.left_var_bind_path_des_linker
    }
    /// Port of `getRightVariableBindingPathDescriptorLinker`.
    pub fn get_right_variable_binding_path_descriptor_linker(&self) -> VarBindingPathDescriptorId {
        self.right_var_bind_path_des_linker
    }

    /// Port of `getNextKeyTriggerLinker(bool moveNext = false)`.
    pub fn get_next_key_trigger_linker(
        ctx: &mut ProcessContext,
        this: VarBindingPathJoiningDataId,
        move_next: bool,
    ) -> VarBindingDescriptorId {
        let next_des_linker = ctx.vbpath_join_data(this).next_key_trigger_linker;
        if move_next {
            let advanced = ctx.var_binding_des(next_des_linker).get_next();
            ctx.vbpath_join_data_mut(this).next_key_trigger_linker = advanced;
        }
        next_des_linker
    }

    /// Port of `setKeyVariableBindingDescriptorLinker`.
    pub fn set_key_variable_binding_descriptor_linker(
        &mut self,
        v: VarBindingDescriptorId,
    ) -> &mut Self {
        self.key_var_bind_des_linker = v;
        self
    }
    /// Port of `setLeftVariableBindingPathDescriptorLinker`.
    pub fn set_left_variable_binding_path_descriptor_linker(
        &mut self,
        v: VarBindingPathDescriptorId,
    ) -> &mut Self {
        self.left_var_bind_path_des_linker = v;
        self
    }
    /// Port of `setRightVariableBindingPathDescriptorLinker`.
    pub fn set_right_variable_binding_path_descriptor_linker(
        &mut self,
        v: VarBindingPathDescriptorId,
    ) -> &mut Self {
        self.right_var_bind_path_des_linker = v;
        self
    }
    /// Port of `setNextKeyTriggerLinker`.
    pub fn set_next_key_trigger_linker(
        &mut self,
        next_key_trigger: VarBindingDescriptorId,
    ) -> &mut Self {
        self.next_key_trigger_linker = next_key_trigger;
        self
    }

    /// Port of `addKeyVariableBindingDescriptorLinker`
    /// (`mKeyVarBindDesLinker = keyVarBindDesLinker->append(mKeyVarBindDesLinker)`).
    pub fn add_key_variable_binding_descriptor_linker(
        ctx: &mut ProcessContext,
        this: VarBindingPathJoiningDataId,
        key_var_bind_des_linker: VarBindingDescriptorId,
    ) {
        let old = ctx.vbpath_join_data(this).key_var_bind_des_linker;
        let new_head = VariableBindingDescriptor::append(ctx, key_var_bind_des_linker, old);
        ctx.vbpath_join_data_mut(this).key_var_bind_des_linker = new_head;
    }
    /// Port of `addLeftVariableBindingPathDescriptorLinker`.
    pub fn add_left_variable_binding_path_descriptor_linker(
        ctx: &mut ProcessContext,
        this: VarBindingPathJoiningDataId,
        left_var_bind_path_des_linker: VarBindingPathDescriptorId,
    ) {
        let old = ctx.vbpath_join_data(this).left_var_bind_path_des_linker;
        let new_head =
            VariableBindingPathDescriptor::append(ctx, left_var_bind_path_des_linker, old);
        ctx.vbpath_join_data_mut(this).left_var_bind_path_des_linker = new_head;
    }
    /// Port of `addRightVariableBindingPathDescriptorLinker`.
    pub fn add_right_variable_binding_path_descriptor_linker(
        ctx: &mut ProcessContext,
        this: VarBindingPathJoiningDataId,
        right_var_bind_path_des_linker: VarBindingPathDescriptorId,
    ) {
        let old = ctx.vbpath_join_data(this).right_var_bind_path_des_linker;
        let new_head =
            VariableBindingPathDescriptor::append(ctx, right_var_bind_path_des_linker, old);
        ctx.vbpath_join_data_mut(this)
            .right_var_bind_path_des_linker = new_head;
    }

    /// Port of `allKeyTriggersAvailable`.
    pub fn all_key_triggers_available(&self) -> bool {
        self.all_key_triggers_available
    }
    /// Port of `setAllKeyTriggersAvailable`.
    pub fn set_all_key_triggers_available(&mut self, all_available: bool) -> &mut Self {
        self.all_key_triggers_available = all_available;
        self
    }

    /// `getCalculatedHashValue`'s pure inner walk: hash the key descriptor chain.
    /// (Factored out so `getCalculatedHashValue` and the `Hasher` ctor share it.)
    ///
    /// KONCLUDE-PORT-NOTE[pointer-alias]: `(cint64)variableBinding` becomes the
    /// binding `Id::raw`.
    fn compute_key_hash(ctx: &ProcessContext, key_head: VarBindingDescriptorId) -> Cint64 {
        let mut hash: Cint64 = 0;
        let mut multiplier: Cint64 = 13;
        let mut linker_it = key_head;
        while linker_it.is_some() {
            let variable_binding = ctx.var_binding_des(linker_it).get_variable_binding();
            hash = hash.wrapping_add(multiplier.wrapping_mul(variable_binding.raw));
            multiplier = multiplier * 2 + 1;
            linker_it = ctx.var_binding_des(linker_it).get_next();
        }
        hash
    }

    /// Port of `getCalculatedHashValue` (`const`, mutable cache).
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: the C++ `const` method caches into `mutable`
    /// fields; the port takes `&mut ctx` + the data id and writes the cache via the
    /// arena (the value cached is identical).
    pub fn get_calculated_hash_value(
        ctx: &mut ProcessContext,
        this: VarBindingPathJoiningDataId,
    ) -> Cint64 {
        if !ctx.vbpath_join_data(this).hash_value_calculated {
            let key_head = ctx.vbpath_join_data(this).key_var_bind_des_linker;
            let hash = Self::compute_key_hash(ctx, key_head);
            let d = ctx.vbpath_join_data_mut(this);
            d.hash_value_calculated = true;
            d.calculated_hash_value = hash;
        }
        ctx.vbpath_join_data(this).calculated_hash_value
    }

    /// Port of `isKeyEquivalentTo(const CVariableBindingPathJoiningData& data)`.
    pub fn is_key_equivalent_to_data(
        ctx: &mut ProcessContext,
        this: VarBindingPathJoiningDataId,
        data: VarBindingPathJoiningDataId,
    ) -> bool {
        if Self::get_calculated_hash_value(ctx, this) != Self::get_calculated_hash_value(ctx, data)
        {
            return false;
        }
        let mut linker_it1 = ctx.vbpath_join_data(this).key_var_bind_des_linker;
        let mut linker_it2 = ctx.vbpath_join_data(data).key_var_bind_des_linker;
        while linker_it1.is_some() && linker_it2.is_some() {
            if ctx.var_binding_des(linker_it1).get_variable_binding()
                != ctx.var_binding_des(linker_it2).get_variable_binding()
            {
                return false;
            }
            linker_it1 = ctx.var_binding_des(linker_it1).get_next();
            linker_it2 = ctx.var_binding_des(linker_it2).get_next();
        }
        if linker_it1.is_some() || linker_it2.is_some() {
            return false;
        }
        true
    }

    /// Port of `isKeyEquivalentTo(CVariableBindingPath* varBindPath)`.
    ///
    /// KONCLUDE-PORT-NOTE[pointer-alias]: the `getBindedVariable() <` ordering test
    /// becomes the `VariableId.raw` ordering.
    pub fn is_key_equivalent_to_path(
        ctx: &ProcessContext,
        this: VarBindingPathJoiningDataId,
        var_bind_path: VarBindingPathId,
    ) -> bool {
        let mut linker_it1 = ctx.vbpath_join_data(this).key_var_bind_des_linker;
        let mut linker_it2 = ctx
            .vbpath(var_bind_path)
            .get_variable_binding_descriptor_linker();
        while linker_it2.is_some() && linker_it1.is_some() {
            let bind2 = ctx.var_binding_des(linker_it2).get_variable_binding();
            let bind1 = ctx.var_binding_des(linker_it1).get_variable_binding();
            let var2 = ctx.var_binding(bind2).get_binded_variable();
            let var1 = ctx.var_binding(bind1).get_binded_variable();
            if var2.raw < var1.raw {
                linker_it2 = ctx.var_binding_des(linker_it2).get_next();
            } else {
                if bind1 != bind2 {
                    return false;
                }
                linker_it1 = ctx.var_binding_des(linker_it1).get_next();
                linker_it2 = ctx.var_binding_des(linker_it2).get_next();
            }
        }
        if linker_it1.is_some() {
            return false;
        }
        true
    }
}

// ===========================================================================
// CVariableBindingPathJoiningHashData
// (`CVariableBindingPathJoiningHashData.{h,cpp}`)
// ===========================================================================

/// Port of `CVariableBindingPathJoiningHashData`.
pub struct VariableBindingPathJoiningHashData {
    /// `CVariableBindingPathJoiningData* mLocVarBindPathJoiningData`.
    pub loc_var_bind_path_joining_data: VarBindingPathJoiningDataId,
    /// `CVariableBindingPathJoiningData* mUseVarBindPathJoiningData`.
    pub use_var_bind_path_joining_data: VarBindingPathJoiningDataId,
}

impl VariableBindingPathJoiningHashData {
    /// Port of `CVariableBindingPathJoiningHashData::CVariableBindingPathJoiningHashData()`.
    pub fn new() -> Self {
        VariableBindingPathJoiningHashData {
            loc_var_bind_path_joining_data: Id::NONE,
            use_var_bind_path_joining_data: Id::NONE,
        }
    }
}

impl Default for VariableBindingPathJoiningHashData {
    fn default() -> Self {
        VariableBindingPathJoiningHashData::new()
    }
}

impl Clone for VariableBindingPathJoiningHashData {
    /// Port of the copy ctor: `mLoc = nullptr; mUse = data.mUse`.
    fn clone(&self) -> Self {
        VariableBindingPathJoiningHashData {
            loc_var_bind_path_joining_data: Id::NONE,
            use_var_bind_path_joining_data: self.use_var_bind_path_joining_data,
        }
    }
}

// ===========================================================================
// CVariableBindingPathJoiningHasher
// (`CVariableBindingPathJoiningHasher.{h,cpp}`)
// ===========================================================================

/// Port of `CVariableBindingPathJoiningHasher`.
///
/// KONCLUDE-PORT-NOTE[api]: `mKeyVars` is a `CSortedLinker<CVariable*>*` — a
/// terminology-side (TBox/RBox) variable list reached via `concept->getVariableLinker()`,
/// not part of this satellite subsystem. W2.7-DEFER[api]: kept opaque `Cint64`; the
/// key-vars-side advance in `calculate_hash_value` is deferred until that linker is
/// ported.
pub struct VariableBindingPathJoiningHasher {
    /// `CVariableBindingPathJoiningData* mJoiningData`.
    pub joining_data: VarBindingPathJoiningDataId,
    /// `CVariableBindingPath* mVarBindPath`.
    pub var_bind_path: VarBindingPathId,
    /// `CSortedLinker<CVariable*>* mKeyVars`.
    pub key_vars: Vec<VariableId>,
    /// `cint64 mHashValue`.
    pub hash_value: Cint64,
}

impl VariableBindingPathJoiningHasher {
    /// Port of `CVariableBindingPathJoiningHasher(CVariableBindingPathJoiningData* data)`.
    pub fn new_from_joining_data(
        ctx: &mut ProcessContext,
        data: VarBindingPathJoiningDataId,
    ) -> Self {
        let hash_value = VariableBindingPathJoiningData::get_calculated_hash_value(ctx, data);
        VariableBindingPathJoiningHasher {
            var_bind_path: Id::NONE,
            key_vars: Vec::new(),
            joining_data: data,
            hash_value,
        }
    }

    /// Port of `CVariableBindingPathJoiningHasher(CVariableBindingPath* varBindPath, CSortedLinker<CVariable*>* keyVars)`.
    pub fn new_from_path(
        ctx: &ProcessContext,
        var_bind_path: VarBindingPathId,
        key_vars: &[VariableId],
    ) -> Self {
        let hash_value = Self::calculate_hash_value(ctx, var_bind_path, key_vars);
        VariableBindingPathJoiningHasher {
            joining_data: Id::NONE,
            var_bind_path,
            key_vars: key_vars.to_vec(),
            hash_value,
        }
    }

    /// Port of `calculateHashValue`.
    ///
    fn calculate_hash_value(
        ctx: &ProcessContext,
        var_bind_path: VarBindingPathId,
        key_vars: &[VariableId],
    ) -> Cint64 {
        let mut hash_value: Cint64 = 0;
        let mut key_vars_it: usize = 0;
        let mut multiplier: Cint64 = 13;
        let mut linker_it = ctx
            .vbpath(var_bind_path)
            .get_variable_binding_descriptor_linker();
        // for (...; keyVarsIt && linkerIt; linkerIt = linkerIt->getNext())
        while key_vars_it < key_vars.len() && linker_it.is_some() {
            let variable_binding = ctx.var_binding_des(linker_it).get_variable_binding();
            let variable = ctx.var_binding(variable_binding).get_binded_variable();
            let key_variable: VariableId = key_vars[key_vars_it];
            if variable == key_variable {
                hash_value = hash_value.wrapping_add(multiplier.wrapping_mul(variable_binding.raw));
                multiplier = multiplier * 2 + 1;
                key_vars_it += 1;
            }
            linker_it = ctx.var_binding_des(linker_it).get_next();
        }
        hash_value
    }

    /// Port of `getHashValue`.
    pub fn get_hash_value(&self) -> Cint64 {
        self.hash_value
    }

    /// Port of `operator==`.
    pub fn equals(
        &self,
        ctx: &mut ProcessContext,
        hasher: &VariableBindingPathJoiningHasher,
    ) -> bool {
        if self.joining_data.is_some() && hasher.joining_data.is_some() {
            VariableBindingPathJoiningData::is_key_equivalent_to_data(
                ctx,
                self.joining_data,
                hasher.joining_data,
            )
        } else if self.joining_data.is_some() && hasher.var_bind_path.is_some() {
            VariableBindingPathJoiningData::is_key_equivalent_to_path(
                ctx,
                self.joining_data,
                hasher.var_bind_path,
            )
        } else if self.var_bind_path.is_some() && hasher.joining_data.is_some() {
            VariableBindingPathJoiningData::is_key_equivalent_to_path(
                ctx,
                hasher.joining_data,
                self.var_bind_path,
            )
        } else {
            false
        }
    }
}

/// Port of the free `inline uint qHash(const CVariableBindingPathJoiningHasher&)`.
pub fn q_hash_joining(hasher: &VariableBindingPathJoiningHasher) -> u32 {
    let key: i64 = hasher.get_hash_value();
    if std::mem::size_of::<u64>() > std::mem::size_of::<u32>() {
        ((key >> (8 * std::mem::size_of::<u32>() as i64 - 1)) ^ key) as u32
    } else {
        key as u32
    }
}

// ===========================================================================
// CVariableBindingPathJoiningHash
// (`CVariableBindingPathJoiningHash.{h,cpp}`,
//  `: public CPROCESSHASH<CVariableBindingPathJoiningHasher,…HashData>`)
// ===========================================================================

/// Port of `CVariableBindingPathJoiningHash`.
///
/// KONCLUDE-PORT-NOTE[api]: the base `CPROCESSHASH<Hasher,HashData>` keys by the
/// hasher's `qHash` (= `getHashValue`) bucket with `operator==` (the
/// `isKeyEquivalentTo` arena-chain walk) for in-bucket disambiguation. Rust's `Eq`
/// cannot take `&ctx`, so this is keyed here by the hash **value** (`Cint64`);
/// W2.7-DEFER[api]: hash-value collisions are not yet disambiguated by
/// `isKeyEquivalentTo` (the `equals`/`q_hash_joining` ports above are the building
/// blocks for the reconcile that adds a proper bucketed key). The loc/use localize
/// flow IS ported faithfully.
pub struct VariableBindingPathJoiningHash {
    /// `CProcessContext* mContext` (opaque).
    pub context: Cint64,
    /// the `CPROCESSHASH` base storage, bucketed by `getHashValue()`.
    pub map: HashMap<Cint64, Vec<VariableBindingPathJoiningHashData>>,
}

impl VariableBindingPathJoiningHash {
    /// Port of `CVariableBindingPathJoiningHash::CVariableBindingPathJoiningHash(CProcessContext*)`.
    pub fn new(context: Cint64) -> Self {
        VariableBindingPathJoiningHash {
            context,
            map: HashMap::new(),
        }
    }

    /// Port of `getVariableBindingPathJoiningData(hasher, localize)`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: the C++ `localize` parameter is never read in the
    /// body (it always localizes a shared `mUse` when the key is contained); the port
    /// keeps the unused parameter for signature fidelity.
    pub fn get_variable_binding_path_joining_data(
        &mut self,
        ctx: &mut ProcessContext,
        hasher: &VariableBindingPathJoiningHasher,
        localize: bool,
    ) -> VarBindingPathJoiningDataId {
        let key = hasher.get_hash_value();
        // CVariableBindingPathJoiningHashData data = value(hasher);
        let mut var_bind_path_joining_data = self
            .map
            .get(&key)
            .and_then(|bucket| {
                bucket
                    .iter()
                    .find(|d| {
                        d.use_var_bind_path_joining_data.is_some()
                            && VariableBindingPathJoiningHasher::new_from_joining_data(
                                ctx,
                                d.use_var_bind_path_joining_data,
                            )
                            .equals(ctx, hasher)
                    })
                    .map(|d| d.use_var_bind_path_joining_data)
            })
            .unwrap_or(Id::NONE);
        let bucket_index = self.map.get(&key).and_then(|bucket| {
            bucket.iter().position(|d| {
                d.use_var_bind_path_joining_data.is_some()
                    && VariableBindingPathJoiningHasher::new_from_joining_data(
                        ctx,
                        d.use_var_bind_path_joining_data,
                    )
                    .equals(ctx, hasher)
            })
        });
        if let Some(bucket_index) = bucket_index {
            let (loc, use_) = {
                let d = &self.map.get(&key).unwrap()[bucket_index];
                (
                    d.loc_var_bind_path_joining_data,
                    d.use_var_bind_path_joining_data,
                )
            };
            if loc.is_none() && use_.is_some() {
                // allocateAndConstruct + initVariableBindingPathJoiningData(use)
                let new_data = ctx.alloc_vbpath_join_data(VariableBindingPathJoiningData::new());
                VariableBindingPathJoiningData::init_from_prev(ctx, new_data, use_);
                let d = &mut self.map.get_mut(&key).unwrap()[bucket_index];
                d.loc_var_bind_path_joining_data = new_data;
                d.use_var_bind_path_joining_data = new_data;
            }
            var_bind_path_joining_data =
                self.map.get(&key).unwrap()[bucket_index].use_var_bind_path_joining_data;
        }
        var_bind_path_joining_data
    }

    /// Port of `insertVariableBindingPathJoiningData(hasher, joinData)`.
    pub fn insert_variable_binding_path_joining_data(
        &mut self,
        hasher: &VariableBindingPathJoiningHasher,
        join_data: VarBindingPathJoiningDataId,
    ) -> &mut Self {
        let key = hasher.get_hash_value();
        let bucket = self.map.entry(key).or_default();
        let idx = bucket
            .iter()
            .position(|d| d.use_var_bind_path_joining_data == join_data)
            .unwrap_or_else(|| {
                bucket.push(VariableBindingPathJoiningHashData::new());
                bucket.len() - 1
            });
        let d = &mut bucket[idx];
        d.use_var_bind_path_joining_data = join_data;
        d.loc_var_bind_path_joining_data = join_data;
        self
    }
}

// ===========================================================================
// CVariableBindingTriggerLinker
// (`CVariableBindingTriggerLinker.{h,cpp}`,
//  `: public CLinkerBase<CVariableBindingPathDescriptor*,Self>`)
// ===========================================================================

/// Port of `CVariableBindingTriggerLinker`.
pub struct VariableBindingTriggerLinker {
    /// `CLinkerBase::data` (`CVariableBindingPathDescriptor*`).
    pub data: VarBindingPathDescriptorId,
    /// `CLinkerBase::next`.
    pub next: VarBindingTriggerLinkerId,
    /// `CVariableBindingDescriptor* mNextTriggerVariableBinding`.
    pub next_trigger_variable_binding: VarBindingDescriptorId,
    /// `bool mLeftTriggered`.
    pub left_triggered: bool,
}

impl Default for VariableBindingTriggerLinker {
    fn default() -> Self {
        VariableBindingTriggerLinker {
            data: Id::NONE,
            next: Id::NONE,
            next_trigger_variable_binding: Id::NONE,
            left_triggered: false,
        }
    }
}

impl VariableBindingTriggerLinker {
    /// Port of `CVariableBindingTriggerLinker::CVariableBindingTriggerLinker(varBindPath = nullptr)`.
    pub fn new(var_bind_path_des: VarBindingPathDescriptorId) -> Self {
        VariableBindingTriggerLinker {
            data: var_bind_path_des,
            ..Default::default()
        }
    }

    /// Port of `initTriggerLinker`.
    pub fn init_trigger_linker(
        &mut self,
        var_bind_path_des: VarBindingPathDescriptorId,
        var_bind_des: VarBindingDescriptorId,
        left_triggered: bool,
    ) -> &mut Self {
        // initLinker(varBindPathDes): data = varBindPathDes; next = nullptr
        self.data = var_bind_path_des;
        self.next = Id::NONE;
        self.next_trigger_variable_binding = var_bind_des;
        self.left_triggered = left_triggered;
        self
    }

    /// Port of `getVariableBindingPathDescriptor` (`return getData()`).
    pub fn get_variable_binding_path_descriptor(&self) -> VarBindingPathDescriptorId {
        self.data
    }
    /// Port of `setVariableBindingPathDescriptor`.
    pub fn set_variable_binding_path_descriptor(
        &mut self,
        v: VarBindingPathDescriptorId,
    ) -> &mut Self {
        self.data = v;
        self
    }

    /// Port of `getNextTriggerVariableBindingDescriptor`.
    pub fn get_next_trigger_variable_binding_descriptor(&self) -> VarBindingDescriptorId {
        self.next_trigger_variable_binding
    }
    /// Port of `setNextTriggerVariableBindingDescriptor`.
    pub fn set_next_trigger_variable_binding_descriptor(
        &mut self,
        v: VarBindingDescriptorId,
    ) -> &mut Self {
        self.next_trigger_variable_binding = v;
        self
    }

    /// Port of `isLeftTriggered`.
    pub fn is_left_triggered(&self) -> bool {
        self.left_triggered
    }
    /// Port of `setLeftTriggered`.
    pub fn set_left_triggered(&mut self, left_triggered: bool) -> &mut Self {
        self.left_triggered = left_triggered;
        self
    }

    /// Port of `CLinkerBase::getNext`.
    pub fn get_next(&self) -> VarBindingTriggerLinkerId {
        self.next
    }
    /// Port of `CLinkerBase::setNext`.
    pub fn set_next(&mut self, next: VarBindingTriggerLinkerId) -> &mut Self {
        self.next = next;
        self
    }
    /// Port of `CLinkerBase::hasNext`.
    pub fn has_next(&self) -> bool {
        self.next.is_some()
    }

    /// Port of `CLinkerBase<…>::append` (tail-splice; returns the head `this`).
    pub fn append(
        ctx: &mut ProcessContext,
        this: VarBindingTriggerLinkerId,
        appending_list: VarBindingTriggerLinkerId,
    ) -> VarBindingTriggerLinkerId {
        let mut last = this;
        while ctx.vbtrigger_linker(last).has_next() {
            last = ctx.vbtrigger_linker(last).get_next();
        }
        ctx.vbtrigger_linker_mut(last).set_next(appending_list);
        this
    }
}

// ===========================================================================
// CVariableBindingTriggerData
// (`CVariableBindingTriggerData.{h,cpp}`)
// ===========================================================================

/// Port of `CVariableBindingTriggerData`.
#[derive(Clone)]
pub struct VariableBindingTriggerData {
    /// `bool mTriggered`.
    pub triggered: bool,
    /// `CVariableBindingTriggerLinker* mVarBindTriggerLinker`.
    pub var_bind_trigger_linker: VarBindingTriggerLinkerId,
}

impl VariableBindingTriggerData {
    /// Port of `CVariableBindingTriggerData::CVariableBindingTriggerData()`.
    pub fn new() -> Self {
        VariableBindingTriggerData {
            triggered: false,
            var_bind_trigger_linker: Id::NONE,
        }
    }

    /// Port of `isTriggered`.
    pub fn is_triggered(&self) -> bool {
        self.triggered
    }
    /// Port of `getVariableBindingTriggerLinker`.
    pub fn get_variable_binding_trigger_linker(&self) -> VarBindingTriggerLinkerId {
        self.var_bind_trigger_linker
    }
    /// Port of `setTriggered`.
    pub fn set_triggered(&mut self, triggered: bool) -> &mut Self {
        self.triggered = triggered;
        self
    }
    /// Port of `setVariableBindingTriggerLinker`.
    pub fn set_variable_binding_trigger_linker(
        &mut self,
        v: VarBindingTriggerLinkerId,
    ) -> &mut Self {
        self.var_bind_trigger_linker = v;
        self
    }
    /// Port of `clearVariableBindingTriggerLinker`.
    pub fn clear_variable_binding_trigger_linker(&mut self) -> &mut Self {
        self.var_bind_trigger_linker = Id::NONE;
        self
    }

    /// Port of `addVariableBindingTriggerLinker`
    /// (`mVarBindTriggerLinker = varBindTriggerLinker->append(mVarBindTriggerLinker)`).
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: this trigger-data lives by value inside the
    /// trigger hash, so `&mut self` (the data) and `&mut ctx` (the linker arena) are
    /// distinct borrows.
    pub fn add_variable_binding_trigger_linker(
        &mut self,
        ctx: &mut ProcessContext,
        var_bind_trigger_linker: VarBindingTriggerLinkerId,
    ) -> &mut Self {
        let new_head = VariableBindingTriggerLinker::append(
            ctx,
            var_bind_trigger_linker,
            self.var_bind_trigger_linker,
        );
        self.var_bind_trigger_linker = new_head;
        self
    }
}

impl Default for VariableBindingTriggerData {
    fn default() -> Self {
        VariableBindingTriggerData::new()
    }
}

// ===========================================================================
// CVariableBindingTriggerHash
// (`CVariableBindingTriggerHash.{h,cpp}`,
//  `: public CPROCESSHASH<TVariableIndividualPair,CVariableBindingTriggerData>`)
// ===========================================================================

/// `typedef QPair<CVariable*,cint64> TVariableIndividualPair`.
/// KONCLUDE-PORT-NOTE[ownership]: `CVariable*` → `VariableId`; the `cint64` is the
/// individual node id. `(VariableId, Cint64)` is `Hash + Eq`, so it is a real
/// `HashMap` key (no deferral needed).
pub type TVariableIndividualPair = (VariableId, Cint64);

/// Port of `CVariableBindingTriggerHash`.
#[derive(Clone)]
pub struct VariableBindingTriggerHash {
    /// `CProcessContext* mContext` (opaque).
    pub context: Cint64,
    /// the `CPROCESSHASH<TVariableIndividualPair,…>` base storage.
    pub map: HashMap<TVariableIndividualPair, VariableBindingTriggerData>,
}

impl VariableBindingTriggerHash {
    /// Port of `CVariableBindingTriggerHash::CVariableBindingTriggerHash(CProcessContext*)`.
    pub fn new(context: Cint64) -> Self {
        VariableBindingTriggerHash {
            context,
            map: HashMap::new(),
        }
    }

    /// Port of `initVariableBindingTriggerHash` (operator= from prev, else clear).
    pub fn init_variable_binding_trigger_hash(
        &mut self,
        prev_hash: Option<&VariableBindingTriggerHash>,
    ) -> &mut Self {
        if let Some(prev) = prev_hash {
            self.map = prev.map.clone();
        } else {
            self.map.clear();
        }
        self
    }

    /// Port of `getTriggerData(CVariable*, CIndividualProcessNode*)`
    /// (`operator[](TVariableIndividualPair(variable, indiNode->getIndividualNodeID()))`).
    pub fn get_trigger_data(
        &mut self,
        ctx: &ProcessContext,
        variable: VariableId,
        indi_node: NodeId,
    ) -> &mut VariableBindingTriggerData {
        let indi_id = ctx.node(indi_node).individual_node_id();
        self.map
            .entry((variable, indi_id))
            .or_insert_with(VariableBindingTriggerData::new)
    }

    /// Port of `setTriggeredReturnTriggerLinker`.
    pub fn set_triggered_return_trigger_linker(
        &mut self,
        ctx: &ProcessContext,
        variable: VariableId,
        indi_node: NodeId,
    ) -> VarBindingTriggerLinkerId {
        let trigger_data = self.get_trigger_data(ctx, variable, indi_node);
        let trigger_linker = trigger_data.get_variable_binding_trigger_linker();
        trigger_data.set_triggered(true);
        trigger_data.clear_variable_binding_trigger_linker();
        trigger_linker
    }

    /// Port of `tryInsertVariableBindingTrigger`.
    pub fn try_insert_variable_binding_trigger(
        &mut self,
        ctx: &mut ProcessContext,
        variable: VariableId,
        indi_node: NodeId,
        var_bind_path_des: VarBindingPathDescriptorId,
        var_bind_des: VarBindingDescriptorId,
        left_triggered: bool,
    ) -> bool {
        let indi_id = ctx.node(indi_node).individual_node_id();
        let key = (variable, indi_id);
        // CVariableBindingTriggerData& triggerData = getTriggerData(variable, indiNode);
        if self
            .map
            .entry(key)
            .or_insert_with(VariableBindingTriggerData::new)
            .is_triggered()
        {
            return false;
        }
        // taskMemMan = mContext->getUsedMemoryAllocationManager();
        // triggerLinker = allocateAndConstruct<CVariableBindingTriggerLinker>(taskMemMan);
        let trigger_linker =
            ctx.alloc_vbtrigger_linker(VariableBindingTriggerLinker::new(Id::NONE));
        ctx.vbtrigger_linker_mut(trigger_linker)
            .init_trigger_linker(var_bind_path_des, var_bind_des, left_triggered);
        self.map
            .get_mut(&key)
            .unwrap()
            .add_variable_binding_trigger_linker(ctx, trigger_linker);
        true
    }
}

// ===========================================================================
// CVariableBindingPathMergingHashData
// (`CVariableBindingPathMergingHashData.{h,cpp}`)
// ===========================================================================

/// Port of `CVariableBindingPathMergingHashData`.
#[derive(Copy, Clone)]
pub struct VariableBindingPathMergingHashData {
    /// `CVariableBindingPath* mVariableBindingPath`.
    pub variable_binding_path: VarBindingPathId,
}

impl VariableBindingPathMergingHashData {
    /// Port of `CVariableBindingPathMergingHashData::CVariableBindingPathMergingHashData()`.
    pub fn new() -> Self {
        VariableBindingPathMergingHashData {
            variable_binding_path: Id::NONE,
        }
    }
    /// Port of `getVariableBindingPath`.
    pub fn get_variable_binding_path(&self) -> VarBindingPathId {
        self.variable_binding_path
    }
    /// Port of `setVariableBindingPath`.
    pub fn set_variable_binding_path(
        &mut self,
        variable_binding_path: VarBindingPathId,
    ) -> &mut Self {
        self.variable_binding_path = variable_binding_path;
        self
    }
}

impl Default for VariableBindingPathMergingHashData {
    fn default() -> Self {
        VariableBindingPathMergingHashData::new()
    }
}

// ===========================================================================
// CVariableBindingPathMergingHash
// (`CVariableBindingPathMergingHash.{h,cpp}`,
//  `: public CPROCESSHASH<TPathIDPair,CVariableBindingPathMergingHashData>`)
// ===========================================================================

/// `typedef QPair<cint64,cint64> TPathIDPair`.
pub type TPathIDPair = (Cint64, Cint64);

/// Port of `CVariableBindingPathMergingHash`.
pub struct VariableBindingPathMergingHash {
    /// `CProcessContext* mProcessContext` (opaque).
    pub process_context: Cint64,
    /// the `CPROCESSHASH<TPathIDPair,…>` base storage.
    pub map: HashMap<TPathIDPair, VariableBindingPathMergingHashData>,
}

impl VariableBindingPathMergingHash {
    /// Port of `CVariableBindingPathMergingHash::CVariableBindingPathMergingHash(CProcessContext*)`.
    pub fn new(process_context: Cint64) -> Self {
        VariableBindingPathMergingHash {
            process_context,
            map: HashMap::new(),
        }
    }

    /// Port of `initVariableBindingPathMergingHash` (operator= from prev, else clear).
    pub fn init_variable_binding_path_merging_hash(
        &mut self,
        prev_hash: Option<&VariableBindingPathMergingHash>,
    ) -> &mut Self {
        if let Some(prev) = prev_hash {
            self.map = prev.map.clone();
        } else {
            self.map.clear();
        }
        self
    }

    /// Port of `getMergedVariableBindingPathData(varBindPath1, varBindPath2)`
    /// (`TPathIDPair(qMin(p1,p2), qMax(p1,p2))` → `operator[]`).
    pub fn get_merged_variable_binding_path_data(
        &mut self,
        ctx: &ProcessContext,
        var_bind_path1: VarBindingPathId,
        var_bind_path2: VarBindingPathId,
    ) -> &mut VariableBindingPathMergingHashData {
        let p1 = ctx.vbpath(var_bind_path1).get_propagation_id();
        let p2 = ctx.vbpath(var_bind_path2).get_propagation_id();
        let path_id_pair: TPathIDPair = (p1.min(p2), p1.max(p2));
        self.map.entry(path_id_pair).or_default()
    }
}

// ===========================================================================
// CRepresentativeVariableBindingPathMapData
// (`CRepresentativeVariableBindingPathMapData.{h,cpp}`)
// ===========================================================================

/// Port of `CRepresentativeVariableBindingPathMapData`.
///
/// KONCLUDE-PORT-NOTE[api]: `CRepresentativeVariableBindingPathSetData*` is now ported
/// (`process::representative`, W3.5r); the former W2.7-DEFER opaque `Cint64` marker
/// `resolve_rep_var_bind_path_set_data` is re-aliased onto the real
/// [`RepresentativeVariableBindingPathSetDataId`]. The cached `getRepresentativeID()`
/// (`mResolveRepvarBindPathSetDataID`, a genuine `cint64`) still stays `INVALID` here:
/// reading it needs `ctx` (the rep id lives in the SetData arena element), which the
/// by-value ctor cannot reach — the caller supplies it via `set_resolve_…` when it has
/// `ctx`, so the read-the-id-in-the-ctor side remains W3.5r-DEFER[api].
#[derive(Debug, Copy, Clone)]
pub struct RepresentativeVariableBindingPathMapData {
    /// `CVariableBindingPath* mVarBindPath`.
    pub var_bind_path: VarBindingPathId,
    /// `CVariableBindingPath* mResolveVarBindPath`.
    pub resolve_var_bind_path: VarBindingPathId,
    /// `CRepresentativeVariableBindingPathSetData* mResolveRepVarBindPathSetData`.
    pub resolve_rep_var_bind_path_set_data: RepresentativeVariableBindingPathSetDataId,
    /// `cint64 mResolveRepvarBindPathSetDataID`.
    pub resolve_rep_var_bind_path_set_data_id: Cint64,
}

impl Default for RepresentativeVariableBindingPathMapData {
    fn default() -> Self {
        RepresentativeVariableBindingPathMapData {
            var_bind_path: Id::NONE,
            resolve_var_bind_path: Id::NONE,
            resolve_rep_var_bind_path_set_data: Id::NONE,
            resolve_rep_var_bind_path_set_data_id: INVALID,
        }
    }
}

impl RepresentativeVariableBindingPathMapData {
    /// Port of `CRepresentativeVariableBindingPathMapData(varBindPath = nullptr, resRevRepVarBindPath = nullptr)`.
    ///
    /// (This is the 2-arg ctor: `mResolveVarBindPath = varBindPath`.)
    pub fn new(
        var_bind_path: VarBindingPathId,
        res_rev_rep_var_bind_path: RepresentativeVariableBindingPathSetDataId,
    ) -> Self {
        RepresentativeVariableBindingPathMapData {
            var_bind_path,
            resolve_var_bind_path: var_bind_path,
            resolve_rep_var_bind_path_set_data: res_rev_rep_var_bind_path,
            // mResolveRepvarBindPathSetDataID = mResolveRepVarBindPathSetData->getRepresentativeID();
            // W3.5r-DEFER[api]: getRepresentativeID() needs ctx → INVALID until set by caller.
            resolve_rep_var_bind_path_set_data_id: INVALID,
        }
    }

    /// Port of the 3-arg ctor `(varBindPath, resolveVarBindPath, resRevRepVarBindPath)`.
    pub fn new_with_resolve(
        var_bind_path: VarBindingPathId,
        resolve_var_bind_path: VarBindingPathId,
        res_rev_rep_var_bind_path: RepresentativeVariableBindingPathSetDataId,
    ) -> Self {
        RepresentativeVariableBindingPathMapData {
            var_bind_path,
            resolve_var_bind_path,
            resolve_rep_var_bind_path_set_data: res_rev_rep_var_bind_path,
            // W3.5r-DEFER[api]: getRepresentativeID() needs ctx → INVALID until set by caller.
            resolve_rep_var_bind_path_set_data_id: INVALID,
        }
    }

    /// Port of `getVariableBindingPath`.
    pub fn get_variable_binding_path(&self) -> VarBindingPathId {
        self.var_bind_path
    }
    /// Port of `hasVariableBindingPath`.
    pub fn has_variable_binding_path(&self) -> bool {
        self.var_bind_path.is_some()
    }
    /// Port of `setVariableBindingPath`.
    pub fn set_variable_binding_path(&mut self, var_bind_path: VarBindingPathId) -> &mut Self {
        self.var_bind_path = var_bind_path;
        self
    }

    /// Port of `getResolveVariableBindingPath`.
    pub fn get_resolve_variable_binding_path(&self) -> VarBindingPathId {
        self.resolve_var_bind_path
    }
    /// Port of `hasResolveVariableBindingPath`.
    pub fn has_resolve_variable_binding_path(&self) -> bool {
        self.resolve_var_bind_path.is_some()
    }
    /// Port of `setResolveVariableBindingPath`.
    pub fn set_resolve_variable_binding_path(
        &mut self,
        var_bind_path: VarBindingPathId,
    ) -> &mut Self {
        self.resolve_var_bind_path = var_bind_path;
        self
    }

    /// Port of `getResolveRepresentativeVariableBindingPathSetData`.
    pub fn get_resolve_representative_variable_binding_path_set_data(
        &self,
    ) -> RepresentativeVariableBindingPathSetDataId {
        self.resolve_rep_var_bind_path_set_data
    }
    /// Port of `hasResolveRepresentativeVariableBindingPathSetData`.
    pub fn has_resolve_representative_variable_binding_path_set_data(&self) -> bool {
        self.resolve_rep_var_bind_path_set_data.is_some()
    }
    /// Port of `setResolveRepresentativeVariableBindingPathSetData`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: also re-reads `getRepresentativeID()` — that read needs
    /// `ctx` (the rep id lives in the SetData arena element), so the `_id` cache stays as
    /// the caller sets it (W3.5r-DEFER[api]).
    pub fn set_resolve_representative_variable_binding_path_set_data(
        &mut self,
        res_rev_rep_var_bind_path: RepresentativeVariableBindingPathSetDataId,
    ) -> &mut Self {
        self.resolve_rep_var_bind_path_set_data = res_rev_rep_var_bind_path;
        // self.resolve_rep_var_bind_path_set_data_id =
        //     ctx.rep_var_bind_path_set_data(res_rev_rep_var_bind_path).get_representative_id();
        // W3.5r-DEFER[api]: needs ctx (by-value method has none).
        self
    }

    /// Port of `getResolveRepresentativeVariableBindingPathSetDataID`.
    pub fn get_resolve_representative_variable_binding_path_set_data_id(&self) -> Cint64 {
        self.resolve_rep_var_bind_path_set_data_id
    }
}

// ===========================================================================
// CRepresentativeVariableBindingPathMap
// (`CRepresentativeVariableBindingPathMap.{h,cpp}`,
//  `: public CPROCESSMAP<cint64,CRepresentativeVariableBindingPathMapData>`)
// ===========================================================================

/// Port of `CRepresentativeVariableBindingPathMap`.
#[derive(Debug, Clone)]
pub struct RepresentativeVariableBindingPathMap {
    /// `CProcessContext* mProcessContext` (opaque).
    pub process_context: Cint64,
    /// the `CPROCESSMAP<cint64,…MapData>` base storage.
    pub map: HashMap<Cint64, RepresentativeVariableBindingPathMapData>,
}

impl RepresentativeVariableBindingPathMap {
    /// Port of `CRepresentativeVariableBindingPathMap::CRepresentativeVariableBindingPathMap(CProcessContext*)`.
    pub fn new(process_context: Cint64) -> Self {
        RepresentativeVariableBindingPathMap {
            process_context,
            map: HashMap::new(),
        }
    }

    /// Port of `initVariableBindingPathMap` (operator= from prev, else clear).
    pub fn init_variable_binding_path_map(
        &mut self,
        prev_map: Option<&RepresentativeVariableBindingPathMap>,
    ) -> &mut Self {
        if let Some(prev) = prev_map {
            self.map = prev.map.clone();
        } else {
            self.map.clear();
        }
        self
    }

    /// Port of `CPROCESSMAP::count`.
    pub fn count(&self) -> Cint64 {
        self.map.len() as Cint64
    }
    /// Port of `CPROCESSMAP::contains`.
    pub fn contains(&self, key: Cint64) -> bool {
        self.map.contains_key(&key)
    }
    /// Port of `CPROCESSMAP::value` (copy; default when absent).
    pub fn value(&self, key: Cint64) -> RepresentativeVariableBindingPathMapData {
        self.map.get(&key).copied().unwrap_or_default()
    }
    /// Port of `CPROCESSMAP::insert`.
    pub fn insert(&mut self, key: Cint64, data: RepresentativeVariableBindingPathMapData) {
        self.map.insert(key, data);
    }
    /// Port of `CPROCESSMAP::operator[]`.
    pub fn entry_mut(&mut self, key: Cint64) -> &mut RepresentativeVariableBindingPathMapData {
        self.map.entry(key).or_default()
    }
}

// ===========================================================================
// W2.7-ARENA-ADDITIONS
// ===========================================================================
//
// The reconcile must add the following to `process/context.rs` (the `ProcessContext`
// per-test arena container) so the `ctx.<arena>(id)` derefs in the methods above
// resolve. Each line is one `Arena<T>` field + its `get / get_mut / alloc` accessor
// trio (the `arena_accessors!(field, Type, IdAlias, get, get_mut, alloc)` macro,
// exactly as the existing 16 arenas are declared). All seven object kinds are
// bump-allocated per test in Konclude (`allocateAndConstruct<…>(taskMemMan)`), so
// each gets its own arena; the hashes/maps (`VariableBindingPathMap`,
// `VariableBindingPath{Joining,Merging}Hash`, `VariableBindingTriggerHash`,
// `RepresentativeVariableBindingPathMap`) are held BY VALUE by their owners and need
// NO arena.
//
//   // field name                    | element type                      | id alias                       | get / get_mut / alloc
//   var_bindings:        Arena<VariableBinding>                 | VarBindingId                  | var_binding / var_binding_mut / alloc_var_binding
//   var_binding_descs:   Arena<VariableBindingDescriptor>       | VarBindingDescriptorId        | var_binding_des / var_binding_des_mut / alloc_var_binding_des
//   var_binding_paths:   Arena<VariableBindingPath>             | VarBindingPathId              | vbpath / vbpath_mut / alloc_vbpath
//   var_binding_path_descs: Arena<VariableBindingPathDescriptor>| VarBindingPathDescriptorId    | vbpath_des / vbpath_des_mut / alloc_vbpath_des
//   var_binding_path_sets: Arena<VariableBindingPathSet>        | VarBindingPathSetId           | vbpath_set / vbpath_set_mut / alloc_vbpath_set
//   var_binding_path_join_datas: Arena<VariableBindingPathJoiningData> | VarBindingPathJoiningDataId | vbpath_join_data / vbpath_join_data_mut / alloc_vbpath_join_data
//   var_binding_trigger_linkers: Arena<VariableBindingTriggerLinker>  | VarBindingTriggerLinkerId  | vbtrigger_linker / vbtrigger_linker_mut / alloc_vbtrigger_linker
//
// As concrete `arena_accessors!` invocations (to paste into `impl ProcessContext`):
//
//   arena_accessors!(var_bindings, VariableBinding, VarBindingId,
//       var_binding, var_binding_mut, alloc_var_binding);
//   arena_accessors!(var_binding_descs, VariableBindingDescriptor, VarBindingDescriptorId,
//       var_binding_des, var_binding_des_mut, alloc_var_binding_des);
//   arena_accessors!(var_binding_paths, VariableBindingPath, VarBindingPathId,
//       vbpath, vbpath_mut, alloc_vbpath);
//   arena_accessors!(var_binding_path_descs, VariableBindingPathDescriptor, VarBindingPathDescriptorId,
//       vbpath_des, vbpath_des_mut, alloc_vbpath_des);
//   arena_accessors!(var_binding_path_sets, VariableBindingPathSet, VarBindingPathSetId,
//       vbpath_set, vbpath_set_mut, alloc_vbpath_set);
//   arena_accessors!(var_binding_path_join_datas, VariableBindingPathJoiningData, VarBindingPathJoiningDataId,
//       vbpath_join_data, vbpath_join_data_mut, alloc_vbpath_join_data);
//   arena_accessors!(var_binding_trigger_linkers, VariableBindingTriggerLinker, VarBindingTriggerLinkerId,
//       vbtrigger_linker, vbtrigger_linker_mut, alloc_vbtrigger_linker);
//
// Imports the reconcile adds to `context.rs`:
//   use super::varbind::{
//       VariableBinding, VariableBindingDescriptor, VariableBindingPath,
//       VariableBindingPathDescriptor, VariableBindingPathSet,
//       VariableBindingPathJoiningData, VariableBindingTriggerLinker,
//       VarBindingId, VarBindingDescriptorId, VarBindingPathId,
//       VarBindingPathDescriptorId, VarBindingPathSetId,
//       VarBindingPathJoiningDataId, VarBindingTriggerLinkerId,
//   };
// and `pub mod varbind;` in `process/mod.rs`.
//
// NOTE for the reconcile: `ctx.node(indi).individual_node_id()` (used by the trigger
// hash) already resolves against the existing `nodes` arena — no addition needed there.
