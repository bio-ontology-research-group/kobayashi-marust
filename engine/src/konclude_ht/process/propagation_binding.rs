//! `process::propagation_binding` (port unit **W3c**) — the propagation-binding
//! subsystem the `binding_hash` keystone (W3b) deferred.
//!
//! Ports the Konclude `Source/Reasoner/Kernel/Process/` propagation-binding classes
//! that model the bindings propagated along the completion graph for the nominal /
//! variable answering rules (the data behind `CConceptPropagationBindingSetHash` and
//! the deferred bodies in `completion/{u06,u07,u11,u33,u34}.rs`). In the W3b wave the
//! set + descriptor were fieldless placeholder markers in `process::binding_hash`
//! (`PropagationBindingSet`, `PropagationBindingDescriptor`); this unit fills them
//! for real so the `getPropagationBindingSet` localise-alloc and the `u07`/`u11`/`u33`
//! bodies can un-defer.
//!
//! Classes ported here (one Rust struct per C++ class, `/// Port of …`):
//!   * `CPropagationBinding`                          — a (variable ↦ individual, concept) binding
//!   * `CPropagationBindingDescriptor`                — linker over bindings (+ dep-tracker)
//!   * `CPropagationBindingReapplyConceptDescriptor`  — reapply linker (indi/binding/concept)
//!   * `CPropagationBindingMapData`                   — the per-binding map value (des + reapply-des)
//!   * `CPropagationBindingMap`                       — propID → map-data
//!   * `CPropagationBindingSet`                        — a concept's set of propagation bindings
//!
//! ## Memory model (the global `[ownership]` decision, `model/substrate.rs`)
//!
//! Every `CXxx*` becomes a typed arena `Id<T>` (`Id::NONE` == `nullptr`); the per-test
//! pool objects (`CPropagationBinding`, the two descriptor kinds, the set) get an
//! `Arena<T>` field on `ProcessContext` (listed in `// W3c-ARENA-ADDITIONS` at the foot
//! of this file — the reconcile wires them in `process/context.rs`). The
//! `CPropagationBindingMap` (a `CPROCESSMAP<cint64,…MapData>`) is held BY VALUE by the
//! set and needs no arena (the `CVariableBindingPathMap` precedent in `varbind.rs`).
//!
//! KONCLUDE-PORT-NOTE[ownership]: the intrusive `CLinkerBase`/`CDependencyTracker`
//! bases are folded in as `next` + `data` + `dep_track_point` fields (exactly as
//! `varbind.rs` folds `CVariableBindingPathDescriptor`). The chain-walking / allocating
//! operations (`append`, `addPropagationBinding`) are ported as **associated functions
//! over `ctx: &mut ProcessContext` + `Id`s** so a receiver borrowed out of `ctx` never
//! aliases a second `ctx` borrow (the W3.5 accessor convention).
//!
//! ## W3c-DEFER[api] — the three set sub-objects (own units)
//!
//! `CPropagationBindingSet` lazily allocates three further satellites that are their
//! own (not-yet-ported) subsystems: `CPropagationBindingReapplyConceptHash` (a
//! `CPROCESSHASH<TIndividualConceptPair,…>` with its iterator), and the two transition
//! extensions `CPropagationVariableBindingTransitionExtension` /
//! `CPropagationRepresentativeTransitionExtension`. These are kept as zero-size
//! placeholder markers + `Id<T>` aliases (no arena), exactly as W3b kept this very set
//! as a marker; the set holds their ids and the lazy `get…(create)` getters preserve
//! the control flow but `W3c-DEFER` the allocation (return the stored id, `Id::NONE`
//! until those subsystems land). The reapply-hash *insertion* in
//! `addPropagationBindingReapplyConceptDescriptor` is likewise deferred, while the
//! real `CPropagationBindingMapData` side of the same statement is ported faithfully.

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
use super::{ConDescId, NodeId, TrackPointId};

// ===========================================================================
// Process-layer id aliases for the W3c propagation-binding classes.
// ===========================================================================
/// `CPropagationBinding*`                         → `PropagationBindingId`.
pub type PropagationBindingId = Id<PropagationBinding>;
/// `CPropagationBindingDescriptor*`               → `PropagationBindingDescriptorId`.
pub type PropagationBindingDescriptorId = Id<PropagationBindingDescriptor>;
/// `CPropagationBindingReapplyConceptDescriptor*`  → `PropagationBindingReapplyConceptDescriptorId`.
pub type PropagationBindingReapplyConceptDescriptorId =
    Id<PropagationBindingReapplyConceptDescriptor>;
/// `CPropagationBindingSet*`                       → `PropagationBindingSetId`.
pub type PropagationBindingSetId = Id<PropagationBindingSet>;

// --- W3c-DEFER[api]: the three set sub-objects (own units, kept as markers) ---

/// W3c-DEFER placeholder for `CPropagationBindingReapplyConceptHash` (own unit).
#[derive(Debug, Default)]
pub struct PropagationBindingReapplyConceptHash;
/// `CPropagationBindingReapplyConceptHash*` → `PropagationBindingReapplyConceptHashId`.
pub type PropagationBindingReapplyConceptHashId = Id<PropagationBindingReapplyConceptHash>;

/// W3c-DEFER placeholder for `CPropagationVariableBindingTransitionExtension` (own unit).
#[derive(Debug, Default)]
pub struct PropagationVariableBindingTransitionExtension;
/// `CPropagationVariableBindingTransitionExtension*` → `…Id`.
pub type PropagationVariableBindingTransitionExtensionId =
    Id<PropagationVariableBindingTransitionExtension>;

/// W3c-DEFER placeholder for `CPropagationRepresentativeTransitionExtension` (own unit).
#[derive(Debug, Default)]
pub struct PropagationRepresentativeTransitionExtension;
/// `CPropagationRepresentativeTransitionExtension*` → `…Id`.
pub type PropagationRepresentativeTransitionExtensionId =
    Id<PropagationRepresentativeTransitionExtension>;

// ===========================================================================
// CPropagationBinding
// (`CPropagationBinding.{h,cpp}`, `: public CDependencyTracker`)
// ===========================================================================

/// Port of `CPropagationBinding`.
///
/// KONCLUDE-PORT-NOTE[ownership]: the `CDependencyTracker` base is folded in as the
/// `dep_track_point` field. `CVariable*` → `VariableId`, `CIndividualProcessNode*` →
/// `NodeId`, `CConceptDescriptor*` → `ConDescId`.
pub struct PropagationBinding {
    /// `CDependencyTracker::mDependencyTrackPoint`.
    pub dep_track_point: TrackPointId,
    /// `cint64 mPropID`.
    pub prop_id: Cint64,
    /// `CVariable* mVariable`.
    pub variable: VariableId,
    /// `CIndividualProcessNode* mIndiNode`.
    pub indi_node: NodeId,
    /// `CConceptDescriptor* mConDes`.
    pub con_des: ConDescId,
}

impl Default for PropagationBinding {
    fn default() -> Self {
        PropagationBinding {
            dep_track_point: Id::NONE,
            prop_id: INVALID,
            variable: Id::NONE,
            indi_node: Id::NONE,
            con_des: Id::NONE,
        }
    }
}

impl PropagationBinding {
    /// Port of `CPropagationBinding::CPropagationBinding`.
    pub fn new() -> Self {
        PropagationBinding::default()
    }

    /// Port of `CPropagationBinding::initPropagationBinding`.
    pub fn init_propagation_binding(
        &mut self,
        prop_id: Cint64,
        dependency_track_point: TrackPointId,
        indi: NodeId,
        con_des: ConDescId,
        variable: VariableId,
    ) -> &mut Self {
        // initDependencyTracker(dependencyTrackPoint)
        self.dep_track_point = dependency_track_point;
        self.variable = variable;
        self.indi_node = indi;
        self.prop_id = prop_id;
        self.con_des = con_des;
        self
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

    /// Port of `getBindedConceptDescriptor`.
    pub fn get_binded_concept_descriptor(&self) -> ConDescId {
        self.con_des
    }
    /// Port of `setBindedConceptDescriptor`.
    pub fn set_binded_concept_descriptor(&mut self, con_des: ConDescId) -> &mut Self {
        self.con_des = con_des;
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
}

// ===========================================================================
// CPropagationBindingDescriptor
// (`CPropagationBindingDescriptor.{h,cpp}`,
//  `: public CLinkerBase<CPropagationBindingDescriptor*,…>, public CDependencyTracker`)
// ===========================================================================

/// Port of `CPropagationBindingDescriptor`.
///
/// KONCLUDE-PORT-NOTE[ownership]: the `CLinkerBase<CPropagationBindingDescriptor*,Self>`
/// base is a list-of-self linker (`mData == this`); it is folded to `data` (the
/// self-pointer, set by the allocator when needed) + `next`. The `CDependencyTracker`
/// base gives `dep_track_point`. The payload `CPropagationBinding*` is `mPropBinding`.
pub struct PropagationBindingDescriptor {
    /// `CLinkerBase::data` (the self-pointer `CPropagationBindingDescriptor*`).
    pub data: PropagationBindingDescriptorId,
    /// `CLinkerBase::next`.
    pub next: PropagationBindingDescriptorId,
    /// `CDependencyTracker::mDependencyTrackPoint`.
    pub dep_track_point: TrackPointId,
    /// `CPropagationBinding* mPropBinding`.
    pub prop_binding: PropagationBindingId,
}

impl Default for PropagationBindingDescriptor {
    fn default() -> Self {
        PropagationBindingDescriptor {
            data: Id::NONE,
            next: Id::NONE,
            dep_track_point: Id::NONE,
            prop_binding: Id::NONE,
        }
    }
}

impl PropagationBindingDescriptor {
    /// Port of `CPropagationBindingDescriptor::CPropagationBindingDescriptor`
    /// (`CLinkerBase(this)`).
    pub fn new() -> Self {
        PropagationBindingDescriptor::default()
    }

    /// Port of `initPropagationBindingDescriptor`.
    pub fn init_propagation_binding_descriptor(
        &mut self,
        prop_binding: PropagationBindingId,
        dependency_track_point: TrackPointId,
    ) -> &mut Self {
        // initDependencyTracker(dependencyTrackPoint)
        self.dep_track_point = dependency_track_point;
        self.prop_binding = prop_binding;
        self
    }

    /// Port of `getPropagationBinding`.
    pub fn get_propagation_binding(&self) -> PropagationBindingId {
        self.prop_binding
    }

    /// Port of `CLinkerBase::getData` (the self-pointer).
    pub fn get_data(&self) -> PropagationBindingDescriptorId {
        self.data
    }
    /// Port of `CLinkerBase::setData`.
    pub fn set_data(&mut self, data: PropagationBindingDescriptorId) -> &mut Self {
        self.data = data;
        self
    }
    /// Port of `CLinkerBase::getNext`.
    pub fn get_next(&self) -> PropagationBindingDescriptorId {
        self.next
    }
    /// Port of `CLinkerBase::setNext`.
    pub fn set_next(&mut self, next: PropagationBindingDescriptorId) -> &mut Self {
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
        this: PropagationBindingDescriptorId,
        appending_list: PropagationBindingDescriptorId,
    ) -> PropagationBindingDescriptorId {
        let mut last = this;
        while ctx.prop_binding_des(last).has_next() {
            last = ctx.prop_binding_des(last).get_next();
        }
        ctx.prop_binding_des_mut(last).set_next(appending_list);
        this
    }
}

// ===========================================================================
// CPropagationBindingReapplyConceptDescriptor
// (`CPropagationBindingReapplyConceptDescriptor.{h,cpp}`,
//  `: public CDependencyTracker, public CLinkerBase<…*,…>`)
// ===========================================================================

/// Port of `CPropagationBindingReapplyConceptDescriptor`.
///
/// KONCLUDE-PORT-NOTE[ownership]: list-of-self `CLinkerBase` (`next`) + folded
/// `CDependencyTracker` (`dep_track_point`); the payload pointers become ids.
pub struct PropagationBindingReapplyConceptDescriptor {
    /// `CLinkerBase::next`.
    pub next: PropagationBindingReapplyConceptDescriptorId,
    /// `CDependencyTracker::mDependencyTrackPoint`.
    pub dep_track_point: TrackPointId,
    /// `CConceptDescriptor* mConceptDes`.
    pub concept_des: ConDescId,
    /// `CIndividualProcessNode* mIndiNode`.
    pub indi_node: NodeId,
    /// `CPropagationBinding* mPropBinding`.
    pub prop_binding: PropagationBindingId,
}

impl Default for PropagationBindingReapplyConceptDescriptor {
    fn default() -> Self {
        PropagationBindingReapplyConceptDescriptor {
            next: Id::NONE,
            dep_track_point: Id::NONE,
            concept_des: Id::NONE,
            indi_node: Id::NONE,
            prop_binding: Id::NONE,
        }
    }
}

impl PropagationBindingReapplyConceptDescriptor {
    /// Port of the constructor (`CLinkerBase(this)`).
    pub fn new() -> Self {
        PropagationBindingReapplyConceptDescriptor::default()
    }

    /// Port of `initReapllyDescriptor`.
    pub fn init_reapply_descriptor(
        &mut self,
        indi_node: NodeId,
        prop_binding: PropagationBindingId,
        concept_descriptor: ConDescId,
        dep_track_point: TrackPointId,
    ) -> &mut Self {
        // initDependencyTracker(depTrackPoint)
        self.dep_track_point = dep_track_point;
        self.indi_node = indi_node;
        self.prop_binding = prop_binding;
        self.concept_des = concept_descriptor;
        self
    }

    /// Port of `getConceptDescriptor`.
    pub fn get_concept_descriptor(&self) -> ConDescId {
        self.concept_des
    }
    /// Port of `getReapllyIndividualNode`.
    pub fn get_reapply_individual_node(&self) -> NodeId {
        self.indi_node
    }
    /// Port of `getPropagationBinding`.
    pub fn get_propagation_binding(&self) -> PropagationBindingId {
        self.prop_binding
    }

    /// Port of `CLinkerBase::getNext`.
    pub fn get_next(&self) -> PropagationBindingReapplyConceptDescriptorId {
        self.next
    }
    /// Port of `CLinkerBase::setNext`.
    pub fn set_next(&mut self, next: PropagationBindingReapplyConceptDescriptorId) -> &mut Self {
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
        this: PropagationBindingReapplyConceptDescriptorId,
        appending_list: PropagationBindingReapplyConceptDescriptorId,
    ) -> PropagationBindingReapplyConceptDescriptorId {
        let mut last = this;
        while ctx.prop_binding_reapply_con_des(last).has_next() {
            last = ctx.prop_binding_reapply_con_des(last).get_next();
        }
        ctx.prop_binding_reapply_con_des_mut(last).set_next(appending_list);
        this
    }
}

// ===========================================================================
// CPropagationBindingMapData
// (`CPropagationBindingMapData.{h,cpp}`)
// ===========================================================================

/// Port of `CPropagationBindingMapData` (the per-propID map value).
#[derive(Debug, Clone, Copy)]
pub struct PropagationBindingMapData {
    /// `CPropagationBindingReapplyConceptDescriptor* mReapplyConDes`.
    pub reapply_con_des: PropagationBindingReapplyConceptDescriptorId,
    /// `CPropagationBindingDescriptor* mPropBindDes`.
    pub prop_bind_des: PropagationBindingDescriptorId,
}

impl Default for PropagationBindingMapData {
    fn default() -> Self {
        PropagationBindingMapData::new(Id::NONE)
    }
}

impl PropagationBindingMapData {
    /// Port of `CPropagationBindingMapData::CPropagationBindingMapData(CPropagationBindingDescriptor*)`.
    pub fn new(prop_bind_des: PropagationBindingDescriptorId) -> Self {
        PropagationBindingMapData { reapply_con_des: Id::NONE, prop_bind_des }
    }

    /// Port of `getPropagationBindingDescriptor`.
    pub fn get_propagation_binding_descriptor(&self) -> PropagationBindingDescriptorId {
        self.prop_bind_des
    }
    /// Port of `hasPropagationBindingDescriptor`.
    pub fn has_propagation_binding_descriptor(&self) -> bool {
        self.prop_bind_des.is_some()
    }
    /// Port of `setPropagationBindingDescriptor`.
    pub fn set_propagation_binding_descriptor(
        &mut self,
        des: PropagationBindingDescriptorId,
    ) -> &mut Self {
        self.prop_bind_des = des;
        self
    }

    /// Port of `getReapplyConceptDescriptor`.
    pub fn get_reapply_concept_descriptor(&self) -> PropagationBindingReapplyConceptDescriptorId {
        self.reapply_con_des
    }
    /// Port of `hasReapplyConceptDescriptor`.
    pub fn has_reapply_concept_descriptor(&self) -> bool {
        self.reapply_con_des.is_some()
    }
    /// Port of `setReapplyConceptDescriptor`.
    pub fn set_reapply_concept_descriptor(
        &mut self,
        reapply_con_des: PropagationBindingReapplyConceptDescriptorId,
    ) -> &mut Self {
        self.reapply_con_des = reapply_con_des;
        self
    }
    /// Port of `clearReapplyConceptDescriptor`.
    pub fn clear_reapply_concept_descriptor(&mut self) -> &mut Self {
        self.reapply_con_des = Id::NONE;
        self
    }
}

// ===========================================================================
// CPropagationBindingMap
// (`CPropagationBindingMap.{h,cpp}`, `: public CPROCESSMAP<cint64,…MapData>`)
// ===========================================================================

/// Port of `CPropagationBindingMap`.
///
/// KONCLUDE-PORT-NOTE[ownership]: the `CPROCESSMAP<cint64,CPropagationBindingMapData>`
/// base becomes the `map` field (propID key → map-data value). Held BY VALUE by
/// `CPropagationBindingSet`, so it is not an arena element; `mProcessContext` stays an
/// opaque `Cint64` (the `CVariableBindingPathMap` precedent).
#[derive(Clone)]
pub struct PropagationBindingMap {
    /// `CProcessContext* mProcessContext` (opaque handle).
    pub process_context: Cint64,
    /// the `CPROCESSMAP<cint64,…MapData>` base storage.
    pub map: HashMap<Cint64, PropagationBindingMapData>,
}

impl PropagationBindingMap {
    /// Port of `CPropagationBindingMap::CPropagationBindingMap(CProcessContext*)`.
    pub fn new(process_context: Cint64) -> Self {
        PropagationBindingMap { process_context, map: HashMap::new() }
    }

    /// Port of `initPropagationBindingMap` (operator= from prev, else clear).
    pub fn init_propagation_binding_map(&mut self, prev_map: Option<&PropagationBindingMap>) -> &mut Self {
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

    /// Port of `CPROCESSMAP::value` (returns a copy; default-constructed when absent).
    pub fn value(&self, key: Cint64) -> PropagationBindingMapData {
        self.map.get(&key).copied().unwrap_or_default()
    }

    /// Port of `CPROCESSMAP::operator[]` (insert-default-then-borrow).
    pub fn entry_mut(&mut self, key: Cint64) -> &mut PropagationBindingMapData {
        self.map.entry(key).or_default()
    }
}

// ===========================================================================
// CPropagationBindingSet
// (`CPropagationBindingSet.{h,cpp}`)
// ===========================================================================

/// Port of `CPropagationBindingSet`.
///
/// KONCLUDE-PORT-NOTE[ownership]: `mPropMap` is held BY VALUE; the pointer members
/// become ids; `mProcessContext` stays opaque `Cint64`. The three lazily-allocated
/// sub-objects (reapply hash + the two transition extensions) are W3c-DEFER markers.
pub struct PropagationBindingSet {
    /// `CProcessContext* mProcessContext` (opaque).
    pub process_context: Cint64,
    /// `CPropagationBindingMap mPropMap` (by value).
    pub prop_map: PropagationBindingMap,
    /// `bool mPropagateAllFlag`.
    pub propagate_all_flag: bool,
    /// `CConceptDescriptor* mConceptDescriptor`.
    pub concept_descriptor: ConDescId,
    /// `CPropagationBindingDescriptor* mPropBindDesLinker`.
    pub prop_bind_des_linker: PropagationBindingDescriptorId,
    /// `CPropagationBindingDescriptor* mSpecialNewPropBindDes`.
    pub special_new_prop_bind_des: PropagationBindingDescriptorId,
    /// `CPropagationBindingReapplyConceptHash* mReapplyHash` (W3c-DEFER marker id).
    pub reapply_hash: PropagationBindingReapplyConceptHashId,
    /// `CPropagationVariableBindingTransitionExtension* mPropVarBindTransExtension` (W3c-DEFER).
    pub prop_var_bind_trans_extension: PropagationVariableBindingTransitionExtensionId,
    /// `CPropagationRepresentativeTransitionExtension* mPropRepTransExtension` (W3c-DEFER).
    pub prop_rep_trans_extension: PropagationRepresentativeTransitionExtensionId,
}

impl PropagationBindingSet {
    /// Port of `CPropagationBindingSet::CPropagationBindingSet(CProcessContext*)`
    /// (`: mProcessContext(processContext), mPropMap(processContext)`).
    pub fn new(process_context: Cint64) -> Self {
        PropagationBindingSet {
            process_context,
            prop_map: PropagationBindingMap::new(process_context),
            propagate_all_flag: false,
            concept_descriptor: Id::NONE,
            prop_bind_des_linker: Id::NONE,
            special_new_prop_bind_des: Id::NONE,
            reapply_hash: Id::NONE,
            prop_var_bind_trans_extension: Id::NONE,
            prop_rep_trans_extension: Id::NONE,
        }
    }

    /// Port of `initPropagationBindingSet`.
    ///
    /// W3c-DEFER[api]: the conditional re-creation of `mReapplyHash` /
    /// `mPropVarBindTransExtension` / `mPropRepTransExtension` from `prevSet` is deferred
    /// (those sub-objects are unported markers); the by-value map + scalar fields are
    /// copied faithfully. The markers stay `Id::NONE` (matching `prevSet`'s common
    /// no-extension case).
    pub fn init_propagation_binding_set(&mut self, prev_set: Option<&PropagationBindingSet>) -> &mut Self {
        if let Some(prev) = prev_set {
            self.prop_map.init_propagation_binding_map(Some(&prev.prop_map));
            self.concept_descriptor = prev.concept_descriptor;
            self.special_new_prop_bind_des = prev.special_new_prop_bind_des;
            self.prop_bind_des_linker = prev.prop_bind_des_linker;
            // W3c-DEFER[api]: prev.mReapplyHash / mPropVarBindTransExtension /
            // mPropRepTransExtension re-creation (unported sub-objects).
            self.reapply_hash = Id::NONE;
            self.prop_var_bind_trans_extension = Id::NONE;
            self.prop_rep_trans_extension = Id::NONE;
            self.propagate_all_flag = prev.propagate_all_flag;
        } else {
            self.prop_map.init_propagation_binding_map(None);
            self.concept_descriptor = Id::NONE;
            self.special_new_prop_bind_des = Id::NONE;
            self.prop_bind_des_linker = Id::NONE;
            self.reapply_hash = Id::NONE;
            self.prop_var_bind_trans_extension = Id::NONE;
            self.prop_rep_trans_extension = Id::NONE;
            self.propagate_all_flag = false;
        }
        self
    }

    /// Port of `getPropagationBindingMap`.
    pub fn get_propagation_binding_map(&self) -> &PropagationBindingMap {
        &self.prop_map
    }
    /// Mutable companion.
    pub fn get_propagation_binding_map_mut(&mut self) -> &mut PropagationBindingMap {
        &mut self.prop_map
    }

    /// Port of `containsPropagationBinding(CPropagationBinding*)`.
    pub fn contains_propagation_binding_for_binding(
        &self,
        ctx: &ProcessContext,
        propagation_binding: PropagationBindingId,
    ) -> bool {
        let id = ctx.prop_binding(propagation_binding).get_propagation_id();
        self.prop_map.contains(id) && self.prop_map.value(id).has_propagation_binding_descriptor()
    }

    /// Port of `containsPropagationBinding(cint64 bindingID)`.
    pub fn contains_propagation_binding_for_id(&self, binding_id: Cint64) -> bool {
        self.prop_map.contains(binding_id)
            && self.prop_map.value(binding_id).has_propagation_binding_descriptor()
    }

    /// Port of `getPropagationBindingDescriptor`.
    pub fn get_propagation_binding_descriptor(
        &self,
        ctx: &ProcessContext,
        propagation_binding: PropagationBindingId,
    ) -> PropagationBindingDescriptorId {
        self.prop_map
            .value(ctx.prop_binding(propagation_binding).get_propagation_id())
            .get_propagation_binding_descriptor()
    }

    /// Port of `getNewSepcialPropagationBindingDescriptor` (C++ spelling kept).
    pub fn get_new_special_propagation_binding_descriptor(&self) -> PropagationBindingDescriptorId {
        self.special_new_prop_bind_des
    }

    /// Port of `addPropagationBinding`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: split into ordered sub-borrows — the descriptor
    /// reads + `append` touch only the descriptor arena while the map mutation touches
    /// only the set; the two never overlap (the `varbind::add_variable_binding_path`
    /// precedent).
    pub fn add_propagation_binding(
        ctx: &mut ProcessContext,
        this: PropagationBindingSetId,
        prop_bind_des: PropagationBindingDescriptorId,
        new_special: bool,
    ) {
        // CPropagationBindingMapData& data = mPropMap[propBindDes->getPropagationBinding()->getPropagationID()];
        let binding = ctx.prop_binding_des(prop_bind_des).get_propagation_binding();
        let prop_id = ctx.prop_binding(binding).get_propagation_id();
        // data.setPropagationBindingDescriptor(propBindDes)
        ctx.prop_binding_set_mut(this)
            .prop_map
            .entry_mut(prop_id)
            .set_propagation_binding_descriptor(prop_bind_des);
        // mPropBindDesLinker = propBindDes->append(mPropBindDesLinker)
        let old_head = ctx.prop_binding_set(this).prop_bind_des_linker;
        let new_head = PropagationBindingDescriptor::append(ctx, prop_bind_des, old_head);
        ctx.prop_binding_set_mut(this).prop_bind_des_linker = new_head;
        if new_special {
            ctx.prop_binding_set_mut(this).special_new_prop_bind_des = prop_bind_des;
        }
    }

    /// Port of `addPropagationBindingReturnReapplyLinker`.
    ///
    /// Same as `addPropagationBinding` but returns the map-data's reapply-concept linker.
    pub fn add_propagation_binding_return_reapply_linker(
        ctx: &mut ProcessContext,
        this: PropagationBindingSetId,
        prop_bind_des: PropagationBindingDescriptorId,
        new_special: bool,
    ) -> PropagationBindingReapplyConceptDescriptorId {
        let binding = ctx.prop_binding_des(prop_bind_des).get_propagation_binding();
        let prop_id = ctx.prop_binding(binding).get_propagation_id();
        ctx.prop_binding_set_mut(this)
            .prop_map
            .entry_mut(prop_id)
            .set_propagation_binding_descriptor(prop_bind_des);
        let old_head = ctx.prop_binding_set(this).prop_bind_des_linker;
        let new_head = PropagationBindingDescriptor::append(ctx, prop_bind_des, old_head);
        ctx.prop_binding_set_mut(this).prop_bind_des_linker = new_head;
        if new_special {
            ctx.prop_binding_set_mut(this).special_new_prop_bind_des = prop_bind_des;
        }
        // return data.getReapplyConceptDescriptor()
        ctx.prop_binding_set(this)
            .prop_map
            .value(prop_id)
            .get_reapply_concept_descriptor()
    }

    /// Port of `copyPropagationBindings` (`mPropMap = *propBindMap`).
    pub fn copy_propagation_bindings(&mut self, prop_bind_map: Option<&PropagationBindingMap>) -> &mut Self {
        if let Some(m) = prop_bind_map {
            self.prop_map = m.clone();
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

    /// Port of `addPropagationBindingDescriptorLinker`
    /// (`mPropBindDesLinker = propBindDesLinker->append(mPropBindDesLinker)`).
    pub fn add_propagation_binding_descriptor_linker(
        ctx: &mut ProcessContext,
        this: PropagationBindingSetId,
        prop_bind_des_linker: PropagationBindingDescriptorId,
    ) {
        let old_head = ctx.prop_binding_set(this).prop_bind_des_linker;
        let new_head = PropagationBindingDescriptor::append(ctx, prop_bind_des_linker, old_head);
        ctx.prop_binding_set_mut(this).prop_bind_des_linker = new_head;
    }

    /// Port of `getPropagationBindingDescriptorLinker`.
    pub fn get_propagation_binding_descriptor_linker(&self) -> PropagationBindingDescriptorId {
        self.prop_bind_des_linker
    }

    /// Port of `getPropagationBindingReapplyConceptHash(bool create)`.
    ///
    /// W3c-DEFER[api]: `CPropagationBindingReapplyConceptHash` is an unported own unit;
    /// the allocate-on-create is deferred (the stored marker id is returned, `Id::NONE`
    /// until the reapply-hash subsystem lands). Control flow is preserved.
    pub fn get_propagation_binding_reapply_concept_hash(
        &self,
        create: bool,
    ) -> PropagationBindingReapplyConceptHashId {
        // if (create && !mReapplyHash) { mReapplyHash = allocate…(); }  // W3c-DEFER
        self.reapply_hash
    }

    /// Port of `addPropagationBindingReapplyConceptDescriptor`.
    ///
    /// W3c-DEFER[api]: the reapply-hash insertion (`getPropagationBindingReapplyConceptHash(true)
    /// ->addPropagationBindingReapplyConceptDescriptor(…)`) is deferred (unported hash);
    /// the `CPropagationBindingMapData` side (append into `data.mReapplyConDes`) is ported
    /// faithfully.
    pub fn add_propagation_binding_reapply_concept_descriptor(
        ctx: &mut ProcessContext,
        this: PropagationBindingSetId,
        prop_bind_reapply_con_des: PropagationBindingReapplyConceptDescriptorId,
    ) {
        // W3c-DEFER[api]: hash insertion keyed on (reapplyIndividualNode, concept).
        // CPropagationBindingMapData& data = mPropMap[reapplyConDes->getPropagationBinding()->getPropagationID()];
        let binding = ctx
            .prop_binding_reapply_con_des(prop_bind_reapply_con_des)
            .get_propagation_binding();
        let prop_id = ctx.prop_binding(binding).get_propagation_id();
        // data.setReapplyConceptDescriptor(reapplyConDes->append(data.getReapplyConceptDescriptor()))
        let old_head = ctx.prop_binding_set(this).prop_map.value(prop_id).get_reapply_concept_descriptor();
        let new_head = PropagationBindingReapplyConceptDescriptor::append(
            ctx,
            prop_bind_reapply_con_des,
            old_head,
        );
        ctx.prop_binding_set_mut(this)
            .prop_map
            .entry_mut(prop_id)
            .set_reapply_concept_descriptor(new_head);
    }

    /// Port of `getPropagationVariableBindingTransitionExtension(bool create)`.
    ///
    /// W3c-DEFER[api]: unported own unit — allocate-on-create deferred.
    pub fn get_propagation_variable_binding_transition_extension(
        &self,
        create: bool,
    ) -> PropagationVariableBindingTransitionExtensionId {
        self.prop_var_bind_trans_extension
    }

    /// Port of `getPropagationRepresentativeTransitionExtension(bool create)`.
    ///
    /// W3c-DEFER[api]: unported own unit — allocate-on-create deferred.
    pub fn get_propagation_representative_transition_extension(
        &self,
        create: bool,
    ) -> PropagationRepresentativeTransitionExtensionId {
        self.prop_rep_trans_extension
    }

    /// Port of `hasPropagateAllFlag`.
    pub fn has_propagate_all_flag(&self) -> bool {
        self.propagate_all_flag
    }
    /// Port of `getPropagateAllFlag`.
    pub fn get_propagate_all_flag(&self) -> bool {
        self.propagate_all_flag
    }
    /// Port of `setPropagateAllFlag`.
    pub fn set_propagate_all_flag(&mut self, prop_all_flag: bool) -> &mut Self {
        self.propagate_all_flag = prop_all_flag;
        self
    }
    /// Port of `adoptPropagateAllFlag`.
    pub fn adopt_propagate_all_flag(&mut self, other: &PropagationBindingSet) -> bool {
        if other.propagate_all_flag && !self.propagate_all_flag {
            self.propagate_all_flag = true;
            return true;
        }
        false
    }
}

// ===========================================================================
// W3c-ARENA-ADDITIONS
// ===========================================================================
//
// The reconcile adds the following to `process/context.rs` (the `ProcessContext`
// per-test arena container) so the `ctx.<arena>(id)` derefs in the methods above
// resolve. Each line is one `Arena<T>` field + its `arena_accessors!` trio. The four
// per-test pool objects each get their own arena; `CPropagationBindingMap` /
// `…MapData` are held BY VALUE and need NO arena. The three W3c-DEFER markers
// (reapply hash + the two transition extensions) have NO arena yet (allocation
// deferred to their own units).
//
//   prop_bindings:               Arena<PropagationBinding>                        | PropagationBindingId                          | prop_binding / prop_binding_mut / alloc_prop_binding
//   prop_binding_descs:          Arena<PropagationBindingDescriptor>              | PropagationBindingDescriptorId                | prop_binding_des / prop_binding_des_mut / alloc_prop_binding_des
//   prop_binding_reapply_con_descs: Arena<PropagationBindingReapplyConceptDescriptor> | PropagationBindingReapplyConceptDescriptorId | prop_binding_reapply_con_des / prop_binding_reapply_con_des_mut / alloc_prop_binding_reapply_con_des
//   prop_binding_sets:           Arena<PropagationBindingSet>                     | PropagationBindingSetId                       | prop_binding_set / prop_binding_set_mut / alloc_prop_binding_set
//
// Imports the reconcile adds to `context.rs`:
//   use super::propagation_binding::{
//       PropagationBinding, PropagationBindingDescriptor,
//       PropagationBindingReapplyConceptDescriptor, PropagationBindingSet,
//       PropagationBindingId, PropagationBindingDescriptorId,
//       PropagationBindingReapplyConceptDescriptorId, PropagationBindingSetId,
//   };
// and `pub mod propagation_binding;` in `process/mod.rs`.
