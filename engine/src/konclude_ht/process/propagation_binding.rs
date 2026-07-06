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
//! ## Set sub-objects
//!
//! `CPropagationBindingSet` lazily allocates three further satellites that are their
//! own subsystems. `CPropagationBindingReapplyConceptHash` (a
//! `CPROCESSHASH<TIndividualConceptPair,…>` with its iterator) and the two
//! transition extensions `CPropagationVariableBindingTransitionExtension` and
//! `CPropagationRepresentativeTransitionExtension` are now arena-backed and lazily
//! allocated like Konclude.

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
use super::super::model::{ConceptId, VariableId};
use super::context::ProcessContext;
use super::representative::{RepresentativePropagationDescriptorId, RepresentativePropagationMap};
use super::varbind::{
    TVariableIndividualPair, VarBindingPathDescriptorId, VarBindingTriggerLinkerId,
    VariableBindingPathJoiningHash, VariableBindingPathJoiningHashId, VariableBindingTriggerHash,
    VariableBindingTriggerHashId,
};
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

/// `TIndividualConceptPair` → `(individual node id, concept)`.
pub type TIndividualConceptPair = (Cint64, ConceptId);

/// Port of `CPropagationBindingReapplyConceptHashData`.
#[derive(Debug, Clone, Copy)]
pub struct PropagationBindingReapplyConceptHashData {
    /// `CPropagationBindingReapplyConceptDescriptor* mPropBindReapplyConDes`.
    pub prop_bind_reapply_con_des: PropagationBindingReapplyConceptDescriptorId,
}

impl Default for PropagationBindingReapplyConceptHashData {
    fn default() -> Self {
        PropagationBindingReapplyConceptHashData::new(Id::NONE)
    }
}

impl PropagationBindingReapplyConceptHashData {
    /// Port of `CPropagationBindingReapplyConceptHashData::CPropagationBindingReapplyConceptHashData`.
    pub fn new(prop_bind_reapply_con_des: PropagationBindingReapplyConceptDescriptorId) -> Self {
        PropagationBindingReapplyConceptHashData {
            prop_bind_reapply_con_des,
        }
    }

    /// Port of `getPropagationBindingReapplyConceptDescriptor`.
    pub fn get_propagation_binding_reapply_concept_descriptor(
        &self,
    ) -> PropagationBindingReapplyConceptDescriptorId {
        self.prop_bind_reapply_con_des
    }

    /// Port of `setPropagationBindingReapplyConceptDescriptor`.
    pub fn set_propagation_binding_reapply_concept_descriptor(
        &mut self,
        des: PropagationBindingReapplyConceptDescriptorId,
    ) -> &mut Self {
        self.prop_bind_reapply_con_des = des;
        self
    }

    /// Port of `clearPropagationBindingReapplyConceptDescriptor`.
    pub fn clear_propagation_binding_reapply_concept_descriptor(&mut self) -> &mut Self {
        self.prop_bind_reapply_con_des = Id::NONE;
        self
    }
}

/// Port of `CPropagationBindingReapplyConceptHash`.
#[derive(Debug, Clone)]
pub struct PropagationBindingReapplyConceptHash {
    /// `CProcessContext* mProcessContext` (opaque).
    pub process_context: Cint64,
    /// `CPROCESSHASH<TIndividualConceptPair,CPropagationBindingReapplyConceptHashData>`.
    pub map: HashMap<TIndividualConceptPair, PropagationBindingReapplyConceptHashData>,
}
/// `CPropagationBindingReapplyConceptHash*` → `PropagationBindingReapplyConceptHashId`.
pub type PropagationBindingReapplyConceptHashId = Id<PropagationBindingReapplyConceptHash>;

impl PropagationBindingReapplyConceptHash {
    /// Port of `CPropagationBindingReapplyConceptHash(CProcessContext*)`.
    pub fn new(process_context: Cint64) -> Self {
        PropagationBindingReapplyConceptHash {
            process_context,
            map: HashMap::new(),
        }
    }

    /// Port of `initPropagationBindingReapplyConceptHash`.
    pub fn init_propagation_binding_reapply_concept_hash(
        &mut self,
        prev_hash: Option<&PropagationBindingReapplyConceptHash>,
    ) -> &mut Self {
        if let Some(prev) = prev_hash {
            self.map = prev.map.clone();
        } else {
            self.map.clear();
        }
        self
    }

    /// Port of `addPropagationBindingReapplyConceptDescriptor(CIndividualProcessNode*, CConcept*, ...)`.
    pub fn add_propagation_binding_reapply_concept_descriptor_for_individual(
        ctx: &mut ProcessContext,
        this: PropagationBindingReapplyConceptHashId,
        indi: NodeId,
        concept: ConceptId,
        reapply_con_des: PropagationBindingReapplyConceptDescriptorId,
    ) {
        let indi_id = ctx.node(indi).individual_node_id();
        Self::add_propagation_binding_reapply_concept_descriptor(
            ctx,
            this,
            (indi_id, concept),
            reapply_con_des,
        );
    }

    /// Port of `addPropagationBindingReapplyConceptDescriptor(const TIndividualConceptPair&, ...)`.
    pub fn add_propagation_binding_reapply_concept_descriptor(
        ctx: &mut ProcessContext,
        this: PropagationBindingReapplyConceptHashId,
        indi_con_pair: TIndividualConceptPair,
        reapply_con_des: PropagationBindingReapplyConceptDescriptorId,
    ) {
        let old_head = ctx
            .prop_binding_reapply_con_hash(this)
            .map
            .get(&indi_con_pair)
            .map(|data| data.get_propagation_binding_reapply_concept_descriptor())
            .unwrap_or(Id::NONE);
        let new_head =
            PropagationBindingReapplyConceptDescriptor::append(ctx, reapply_con_des, old_head);
        ctx.prop_binding_reapply_con_hash_mut(this)
            .map
            .entry(indi_con_pair)
            .or_default()
            .set_propagation_binding_reapply_concept_descriptor(new_head);
    }

    /// Port of `takePropagationBindingReapplyConceptDescriptor`.
    pub fn take_propagation_binding_reapply_concept_descriptor(
        &mut self,
        indi_con_pair: TIndividualConceptPair,
    ) -> PropagationBindingReapplyConceptDescriptorId {
        let data = self.map.entry(indi_con_pair).or_default();
        let reapply_con_des = data.get_propagation_binding_reapply_concept_descriptor();
        data.clear_propagation_binding_reapply_concept_descriptor();
        reapply_con_des
    }

    /// Port of `hasPropagationBindingReapplyConceptDescriptor`.
    pub fn has_propagation_binding_reapply_concept_descriptor(
        &self,
        indi_con_pair: TIndividualConceptPair,
    ) -> bool {
        self.map
            .get(&indi_con_pair)
            .copied()
            .unwrap_or_default()
            .get_propagation_binding_reapply_concept_descriptor()
            .is_some()
    }

    /// Port of `getPropagationBindingReapplyConceptDescriptorIterator`.
    pub fn get_propagation_binding_reapply_concept_descriptor_iterator(
        &mut self,
    ) -> PropagationBindingReapplyConceptIterator<'_> {
        PropagationBindingReapplyConceptIterator::new(&mut self.map)
    }
}

impl Default for PropagationBindingReapplyConceptHash {
    fn default() -> Self {
        Self::new(INVALID)
    }
}

/// Port of `CPropagationBindingReapplyConceptIterator`.
#[derive(Debug)]
pub struct PropagationBindingReapplyConceptIterator<'a> {
    /// Live hash being iterated. C++ stores mutable `CPROCESSHASH::iterator`s.
    pub map: &'a mut HashMap<TIndividualConceptPair, PropagationBindingReapplyConceptHashData>,
    /// Stable key sequence for the iterator cursor.
    pub keys: Vec<TIndividualConceptPair>,
    /// Cursor.
    pub pos: usize,
}

impl<'a> PropagationBindingReapplyConceptIterator<'a> {
    /// Port of `CPropagationBindingReapplyConceptIterator(begin,end)`.
    pub fn new(
        map: &'a mut HashMap<TIndividualConceptPair, PropagationBindingReapplyConceptHashData>,
    ) -> Self {
        let keys = map.keys().copied().collect();
        PropagationBindingReapplyConceptIterator { map, keys, pos: 0 }
    }

    /// Port of `nextReapplyDescriptor`.
    pub fn next_reapply_descriptor(
        &mut self,
        move_next: bool,
    ) -> PropagationBindingReapplyConceptDescriptorId {
        let mut reapply_con_des = Id::NONE;
        if self.pos != self.keys.len() {
            reapply_con_des = self
                .map
                .get(&self.keys[self.pos])
                .map(|data| data.get_propagation_binding_reapply_concept_descriptor())
                .unwrap_or(Id::NONE);
            if move_next && self.pos != self.keys.len() {
                self.pos += 1;
            }
        }
        reapply_con_des
    }

    /// Port of `clearReapplyDescriptor`.
    pub fn clear_reapply_descriptor(&mut self) -> &mut Self {
        if self.pos != self.keys.len() {
            if let Some(data) = self.map.get_mut(&self.keys[self.pos]) {
                data.clear_propagation_binding_reapply_concept_descriptor();
            }
        }
        self
    }

    /// Port of `moveNext`.
    pub fn move_next(&mut self) -> bool {
        if self.pos != self.keys.len() {
            self.pos += 1;
            return true;
        }
        false
    }
}

/// Port of `CPropagationVariableBindingTransitionExtension`.
///
/// KONCLUDE-PORT-NOTE[ownership]: the C++ object is allocated from
/// `CProcessContext` and owns/localizes two process hashes. The port stores ids
/// for those hashes in the same `ProcessContext` arena root.
#[derive(Debug, Clone)]
pub struct PropagationVariableBindingTransitionExtension {
    /// `CProcessContext* mProcessContext` (opaque).
    pub process_context: Cint64,
    /// `CPropagationBindingDescriptor* mLastAnalysedPropBindDes`.
    pub last_analysed_prop_bind_des: PropagationBindingDescriptorId,
    /// `bool mLastAnalysedPropagateAllFlag`.
    pub last_analysed_propagate_all_flag: bool,
    /// `bool mProcessingCompleted`.
    pub processing_completed: bool,
    /// `CVariableBindingTriggerHash* mLocVarBindTriggerHash`.
    pub loc_var_bind_trigger_hash: VariableBindingTriggerHashId,
    /// `CVariableBindingTriggerHash* mUseVarBindTriggerHash`.
    pub use_var_bind_trigger_hash: VariableBindingTriggerHashId,
    /// `TVariableIndividualPair mTriggeredVarIndPair`.
    pub triggered_var_ind_pair: TVariableIndividualPair,
    /// `CVariableBindingPathJoiningHash* mUseVarBindPathJoiningHash`.
    pub use_var_bind_path_joining_hash: VariableBindingPathJoiningHashId,
    /// `CVariableBindingPathJoiningHash* mLocVarBindPathJoiningHash`.
    pub loc_var_bind_path_joining_hash: VariableBindingPathJoiningHashId,
    /// `CVariableBindingPathDescriptor* mLeftLastVarBindPathJoiningDes`.
    pub left_last_var_bind_path_joining_des: VarBindingPathDescriptorId,
    /// `CVariableBindingPathDescriptor* mRightLastVarBindPathJoiningDes`.
    pub right_last_var_bind_path_joining_des: VarBindingPathDescriptorId,
}
/// `CPropagationVariableBindingTransitionExtension*` → `…Id`.
pub type PropagationVariableBindingTransitionExtensionId =
    Id<PropagationVariableBindingTransitionExtension>;

impl PropagationVariableBindingTransitionExtension {
    /// Port of `CPropagationVariableBindingTransitionExtension(CProcessContext*)`.
    pub fn new(process_context: Cint64) -> Self {
        let mut ext = PropagationVariableBindingTransitionExtension {
            process_context,
            last_analysed_prop_bind_des: Id::NONE,
            last_analysed_propagate_all_flag: false,
            processing_completed: false,
            loc_var_bind_trigger_hash: Id::NONE,
            use_var_bind_trigger_hash: Id::NONE,
            triggered_var_ind_pair: (Id::NONE, 0),
            use_var_bind_path_joining_hash: Id::NONE,
            loc_var_bind_path_joining_hash: Id::NONE,
            left_last_var_bind_path_joining_des: Id::NONE,
            right_last_var_bind_path_joining_des: Id::NONE,
        };
        ext.init_propagation_variable_binding_transition_extension(None);
        ext
    }

    /// Port of `initPropagationVariableBindingTransitionExtension`.
    pub fn init_propagation_variable_binding_transition_extension(
        &mut self,
        prev: Option<&PropagationVariableBindingTransitionExtension>,
    ) -> &mut Self {
        if let Some(prev) = prev {
            self.last_analysed_prop_bind_des = prev.last_analysed_prop_bind_des;
            self.loc_var_bind_trigger_hash = Id::NONE;
            self.use_var_bind_trigger_hash = prev.use_var_bind_trigger_hash;
            self.loc_var_bind_path_joining_hash = Id::NONE;
            self.use_var_bind_path_joining_hash = prev.use_var_bind_path_joining_hash;
            self.triggered_var_ind_pair = prev.triggered_var_ind_pair;
            self.left_last_var_bind_path_joining_des = prev.left_last_var_bind_path_joining_des;
            self.right_last_var_bind_path_joining_des = prev.right_last_var_bind_path_joining_des;
            self.last_analysed_propagate_all_flag = prev.last_analysed_propagate_all_flag;
            self.processing_completed = prev.processing_completed;
        } else {
            self.last_analysed_prop_bind_des = Id::NONE;
            self.use_var_bind_trigger_hash = Id::NONE;
            self.loc_var_bind_trigger_hash = Id::NONE;
            self.use_var_bind_path_joining_hash = Id::NONE;
            self.loc_var_bind_path_joining_hash = Id::NONE;
            self.triggered_var_ind_pair = (Id::NONE, 0);
            self.left_last_var_bind_path_joining_des = Id::NONE;
            self.right_last_var_bind_path_joining_des = Id::NONE;
            self.last_analysed_propagate_all_flag = false;
            self.processing_completed = false;
        }
        self
    }

    /// Port of `getLastAnalysedPropagateAllFlag`.
    pub fn get_last_analysed_propagate_all_flag(&self) -> bool {
        self.last_analysed_propagate_all_flag
    }

    /// Port of `setLastAnalysedPropagateAllFlag`.
    pub fn set_last_analysed_propagate_all_flag(&mut self, propagate_all_flag: bool) -> &mut Self {
        self.last_analysed_propagate_all_flag = propagate_all_flag;
        self
    }

    /// Port of `getLastAnalysedPropagationBindingDescriptor`.
    pub fn get_last_analysed_propagation_binding_descriptor(
        &self,
    ) -> PropagationBindingDescriptorId {
        self.last_analysed_prop_bind_des
    }

    /// Port of `setLastAnalysedPropagationBindingDescriptor`.
    pub fn set_last_analysed_propagation_binding_descriptor(
        &mut self,
        last_anal_prop_bind_des: PropagationBindingDescriptorId,
    ) -> &mut Self {
        self.last_analysed_prop_bind_des = last_anal_prop_bind_des;
        self
    }

    /// Port of `getVariableBindingTriggerHash`.
    pub fn get_variable_binding_trigger_hash(
        ctx: &mut ProcessContext,
        this: PropagationVariableBindingTransitionExtensionId,
        localize: bool,
    ) -> VariableBindingTriggerHashId {
        let loc = ctx.prop_var_bind_trans_ext(this).loc_var_bind_trigger_hash;
        if localize && loc.is_none() {
            let use_hash = ctx.prop_var_bind_trans_ext(this).use_var_bind_trigger_hash;
            let new_hash = ctx.alloc_vbtrigger_hash(VariableBindingTriggerHash::new(INVALID));
            if use_hash.is_some() {
                let prev = ctx.vbtrigger_hash(use_hash).clone();
                ctx.vbtrigger_hash_mut(new_hash)
                    .init_variable_binding_trigger_hash(Some(&prev));
            }
            let ext = ctx.prop_var_bind_trans_ext_mut(this);
            ext.loc_var_bind_trigger_hash = new_hash;
            ext.use_var_bind_trigger_hash = new_hash;
        }
        ctx.prop_var_bind_trans_ext(this).use_var_bind_trigger_hash
    }

    /// Port of `getVariableBindingPathJoiningHash`.
    pub fn get_variable_binding_path_joining_hash(
        ctx: &mut ProcessContext,
        this: PropagationVariableBindingTransitionExtensionId,
        localize: bool,
    ) -> VariableBindingPathJoiningHashId {
        let loc = ctx
            .prop_var_bind_trans_ext(this)
            .loc_var_bind_path_joining_hash;
        if localize && loc.is_none() {
            let use_hash = ctx
                .prop_var_bind_trans_ext(this)
                .use_var_bind_path_joining_hash;
            let new_hash = ctx.alloc_vbpath_join_hash(VariableBindingPathJoiningHash::new(INVALID));
            if use_hash.is_some() {
                let prev_map = ctx.vbpath_join_hash(use_hash).map.clone();
                ctx.vbpath_join_hash_mut(new_hash).map = prev_map;
            }
            let ext = ctx.prop_var_bind_trans_ext_mut(this);
            ext.loc_var_bind_path_joining_hash = new_hash;
            ext.use_var_bind_path_joining_hash = new_hash;
        }
        ctx.prop_var_bind_trans_ext(this)
            .use_var_bind_path_joining_hash
    }

    /// Port of `getLeftLastVariableBindingPathJoiningDescriptor`.
    pub fn get_left_last_variable_binding_path_joining_descriptor(
        &self,
    ) -> VarBindingPathDescriptorId {
        self.left_last_var_bind_path_joining_des
    }

    /// Port of `getRightLastVariableBindingPathJoiningDescriptor`.
    pub fn get_right_last_variable_binding_path_joining_descriptor(
        &self,
    ) -> VarBindingPathDescriptorId {
        self.right_last_var_bind_path_joining_des
    }

    /// Port of `setLeftLastVariableBindingPathJoiningDescriptor`.
    pub fn set_left_last_variable_binding_path_joining_descriptor(
        &mut self,
        var_bind_path_des: VarBindingPathDescriptorId,
    ) -> &mut Self {
        self.left_last_var_bind_path_joining_des = var_bind_path_des;
        self
    }

    /// Port of `setRightLastVariableBindingPathJoiningDescriptor`.
    pub fn set_right_last_variable_binding_path_joining_descriptor(
        &mut self,
        var_bind_path_des: VarBindingPathDescriptorId,
    ) -> &mut Self {
        self.right_last_var_bind_path_joining_des = var_bind_path_des;
        self
    }

    /// Port of `addAnalysedPropagationBindingDescriptorReturnMatched`.
    pub fn add_analysed_propagation_binding_descriptor_return_matched(
        ctx: &mut ProcessContext,
        this: PropagationVariableBindingTransitionExtensionId,
        prop_bind_des: PropagationBindingDescriptorId,
        mut reapply_trigger_linker: Option<&mut VarBindingTriggerLinkerId>,
    ) -> bool {
        let prop_binding = ctx
            .prop_binding_des(prop_bind_des)
            .get_propagation_binding();
        let variable = ctx.prop_binding(prop_binding).get_binded_variable();
        let indi_node = ctx.prop_binding(prop_binding).get_binded_individual();
        let indi_id = ctx.node(indi_node).individual_node_id();
        let var_indi_pair = (variable, indi_id);

        if ctx.prop_var_bind_trans_ext(this).triggered_var_ind_pair == var_indi_pair {
            return true;
        }
        let trigger_hash = ctx.prop_var_bind_trans_ext(this).use_var_bind_trigger_hash;
        if trigger_hash.is_some() {
            let trigger_linker = {
                let mut hash = std::mem::replace(
                    ctx.vbtrigger_hash_mut(trigger_hash),
                    VariableBindingTriggerHash::new(INVALID),
                );
                let linker = hash.set_triggered_return_trigger_linker(ctx, variable, indi_node);
                *ctx.vbtrigger_hash_mut(trigger_hash) = hash;
                linker
            };
            if trigger_linker.is_some() {
                if let Some(out) = reapply_trigger_linker.as_deref_mut() {
                    *out = trigger_linker;
                }
                return true;
            }
        }
        false
    }

    /// Port of `setTriggeredVariableIndividualPair(const TVariableIndividualPair&)`.
    pub fn set_triggered_variable_individual_pair_value(
        &mut self,
        triggered_var_ind_pair: TVariableIndividualPair,
    ) -> &mut Self {
        self.triggered_var_ind_pair = triggered_var_ind_pair;
        self
    }

    /// Port of `setTriggeredVariableIndividualPair(CVariable*, CIndividualProcessNode*)`.
    pub fn set_triggered_variable_individual_pair(
        &mut self,
        ctx: &ProcessContext,
        variable: VariableId,
        indi_node: NodeId,
    ) -> &mut Self {
        self.triggered_var_ind_pair = (variable, ctx.node(indi_node).individual_node_id());
        self
    }

    /// Port of `getTriggeredVariableIndividualPair`.
    pub fn get_triggered_variable_individual_pair(&self) -> TVariableIndividualPair {
        self.triggered_var_ind_pair
    }

    /// Port of `isProcessingCompleted`.
    pub fn is_processing_completed(&self) -> bool {
        self.processing_completed
    }

    /// Port of `setProcessingCompleted`.
    pub fn set_processing_completed(&mut self, completed: bool) -> &mut Self {
        self.processing_completed = completed;
        self
    }
}

/// Port of `CPropagationRepresentativeTransitionExtension`.
#[derive(Debug, Clone)]
pub struct PropagationRepresentativeTransitionExtension {
    /// `CProcessContext* mProcessContext` (opaque).
    pub process_context: Cint64,
    /// `bool mLastAnalysedPropagateAllFlag`.
    pub last_analysed_propagate_all_flag: bool,
    /// `CPropagationBindingDescriptor* mLastAnalysedPropBindDes`.
    pub last_analysed_prop_bind_des: PropagationBindingDescriptorId,
    /// `CRepresentativePropagationDescriptor* mLeftLastRepPropDes`.
    pub left_last_rep_prop_des: RepresentativePropagationDescriptorId,
    /// `CRepresentativePropagationDescriptor* mRightLastRepPropDes`.
    pub right_last_rep_prop_des: RepresentativePropagationDescriptorId,
    /// `CRepresentativePropagationMap mLeftRepPropMap`.
    pub left_rep_prop_map: RepresentativePropagationMap,
    /// `CRepresentativePropagationMap mRightRepPropMap`.
    pub right_rep_prop_map: RepresentativePropagationMap,
}
/// `CPropagationRepresentativeTransitionExtension*` → `…Id`.
pub type PropagationRepresentativeTransitionExtensionId =
    Id<PropagationRepresentativeTransitionExtension>;

impl PropagationRepresentativeTransitionExtension {
    /// Port of `CPropagationRepresentativeTransitionExtension(CProcessContext*)`.
    pub fn new(process_context: Cint64) -> Self {
        let mut ext = PropagationRepresentativeTransitionExtension {
            process_context,
            last_analysed_propagate_all_flag: false,
            last_analysed_prop_bind_des: Id::NONE,
            left_last_rep_prop_des: Id::NONE,
            right_last_rep_prop_des: Id::NONE,
            left_rep_prop_map: RepresentativePropagationMap::new(process_context),
            right_rep_prop_map: RepresentativePropagationMap::new(process_context),
        };
        ext.init_propagation_representative_transition_extension(None);
        ext
    }

    /// Port of `initPropagationRepresentativeTransitionExtension`.
    pub fn init_propagation_representative_transition_extension(
        &mut self,
        prev: Option<&PropagationRepresentativeTransitionExtension>,
    ) -> &mut Self {
        if let Some(prev) = prev {
            self.last_analysed_prop_bind_des = prev.last_analysed_prop_bind_des;
            self.last_analysed_propagate_all_flag = prev.last_analysed_propagate_all_flag;
            self.left_last_rep_prop_des = prev.left_last_rep_prop_des;
            self.right_last_rep_prop_des = prev.right_last_rep_prop_des;
            self.left_rep_prop_map
                .init_representative_propagation_map(Some(&prev.left_rep_prop_map));
            self.right_rep_prop_map
                .init_representative_propagation_map(Some(&prev.right_rep_prop_map));
        } else {
            self.last_analysed_prop_bind_des = Id::NONE;
            self.last_analysed_propagate_all_flag = false;
            self.left_last_rep_prop_des = Id::NONE;
            self.right_last_rep_prop_des = Id::NONE;
            self.left_rep_prop_map
                .init_representative_propagation_map(None);
            self.right_rep_prop_map
                .init_representative_propagation_map(None);
        }
        self
    }

    /// Port of `getLastAnalysedPropagateAllFlag`.
    pub fn get_last_analysed_propagate_all_flag(&self) -> bool {
        self.last_analysed_propagate_all_flag
    }

    /// Port of `setLastAnalysedPropagateAllFlag`.
    pub fn set_last_analysed_propagate_all_flag(&mut self, flag: bool) -> &mut Self {
        self.last_analysed_propagate_all_flag = flag;
        self
    }

    /// Port of `getLastAnalysedPropagationBindingDescriptor`.
    pub fn get_last_analysed_propagation_binding_descriptor(
        &self,
    ) -> PropagationBindingDescriptorId {
        self.last_analysed_prop_bind_des
    }

    /// Port of `setLastAnalysedPropagationBindingDescriptor`.
    pub fn set_last_analysed_propagation_binding_descriptor(
        &mut self,
        des: PropagationBindingDescriptorId,
    ) -> &mut Self {
        self.last_analysed_prop_bind_des = des;
        self
    }

    /// Port of `getLeftLastRepresentativeJoiningDescriptor`.
    pub fn get_left_last_representative_joining_descriptor(
        &self,
    ) -> RepresentativePropagationDescriptorId {
        self.left_last_rep_prop_des
    }

    /// Port of `getRightLastRepresentativeJoiningDescriptor`.
    pub fn get_right_last_representative_joining_descriptor(
        &self,
    ) -> RepresentativePropagationDescriptorId {
        self.right_last_rep_prop_des
    }

    /// Port of `setLeftLastRepresentativeJoiningDescriptor`.
    pub fn set_left_last_representative_joining_descriptor(
        &mut self,
        des: RepresentativePropagationDescriptorId,
    ) -> &mut Self {
        self.left_last_rep_prop_des = des;
        self
    }

    /// Port of `setRightLastRepresentativeJoiningDescriptor`.
    pub fn set_right_last_representative_joining_descriptor(
        &mut self,
        des: RepresentativePropagationDescriptorId,
    ) -> &mut Self {
        self.right_last_rep_prop_des = des;
        self
    }

    /// Port of `getLeftRepresentativePropagationMap`.
    pub fn get_left_representative_propagation_map(&self) -> &RepresentativePropagationMap {
        &self.left_rep_prop_map
    }

    /// Mutable companion for `getLeftRepresentativePropagationMap`.
    pub fn get_left_representative_propagation_map_mut(
        &mut self,
    ) -> &mut RepresentativePropagationMap {
        &mut self.left_rep_prop_map
    }

    /// Port of `getRightRepresentativePropagationMap`.
    pub fn get_right_representative_propagation_map(&self) -> &RepresentativePropagationMap {
        &self.right_rep_prop_map
    }

    /// Mutable companion for `getRightRepresentativePropagationMap`.
    pub fn get_right_representative_propagation_map_mut(
        &mut self,
    ) -> &mut RepresentativePropagationMap {
        &mut self.right_rep_prop_map
    }
}

// ===========================================================================
// CPropagationBinding
// (`CPropagationBinding.{h,cpp}`, `: public CDependencyTracker`)
// ===========================================================================

/// Port of `CPropagationBinding`.
///
/// KONCLUDE-PORT-NOTE[ownership]: the `CDependencyTracker` base is folded in as the
/// `dep_track_point` field. `CVariable*` → `VariableId`, `CIndividualProcessNode*` →
/// `NodeId`, `CConceptDescriptor*` → `ConDescId`.
#[derive(Clone)]
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
#[derive(Clone)]
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
#[derive(Clone)]
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
        ctx.prop_binding_reapply_con_des_mut(last)
            .set_next(appending_list);
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
        PropagationBindingMapData {
            reapply_con_des: Id::NONE,
            prop_bind_des,
        }
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
        PropagationBindingMap {
            process_context,
            map: HashMap::new(),
        }
    }

    /// Port of `initPropagationBindingMap` (operator= from prev, else clear).
    pub fn init_propagation_binding_map(
        &mut self,
        prev_map: Option<&PropagationBindingMap>,
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
/// become ids; `mProcessContext` stays opaque `Cint64`.
#[derive(Clone)]
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
    /// `CPropagationBindingReapplyConceptHash* mReapplyHash`.
    pub reapply_hash: PropagationBindingReapplyConceptHashId,
    /// `CPropagationVariableBindingTransitionExtension* mPropVarBindTransExtension`.
    pub prop_var_bind_trans_extension: PropagationVariableBindingTransitionExtensionId,
    /// `CPropagationRepresentativeTransitionExtension* mPropRepTransExtension`.
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
    /// KONCLUDE-PORT-NOTE[ownership]: `mReapplyHash` and the transition extensions
    /// require arena allocation, so their copy/localize branches are handled by
    /// `init_propagation_binding_set_in_context`.
    pub fn init_propagation_binding_set(
        &mut self,
        prev_set: Option<&PropagationBindingSet>,
    ) -> &mut Self {
        if let Some(prev) = prev_set {
            self.prop_map
                .init_propagation_binding_map(Some(&prev.prop_map));
            self.concept_descriptor = prev.concept_descriptor;
            self.special_new_prop_bind_des = prev.special_new_prop_bind_des;
            self.prop_bind_des_linker = prev.prop_bind_des_linker;
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

    /// Context-threaded companion for `initPropagationBindingSet` that can
    /// faithfully localize the transition-extension subobject.
    pub fn init_propagation_binding_set_in_context(
        ctx: &mut ProcessContext,
        this: PropagationBindingSetId,
        prev_set: Option<&PropagationBindingSet>,
    ) {
        {
            let set = ctx.prop_binding_set_mut(this);
            set.init_propagation_binding_set(prev_set);
        }
        if let Some(prev) = prev_set {
            if prev.reapply_hash.is_some() {
                let new_hash = Self::get_propagation_binding_reapply_concept_hash(ctx, this, true);
                let prev_hash = ctx.prop_binding_reapply_con_hash(prev.reapply_hash).clone();
                ctx.prop_binding_reapply_con_hash_mut(new_hash)
                    .init_propagation_binding_reapply_concept_hash(Some(&prev_hash));
            }
            if prev.prop_var_bind_trans_extension.is_some() {
                let new_ext =
                    Self::get_propagation_variable_binding_transition_extension(ctx, this, true);
                let prev_ext = ctx
                    .prop_var_bind_trans_ext(prev.prop_var_bind_trans_extension)
                    .clone();
                ctx.prop_var_bind_trans_ext_mut(new_ext)
                    .init_propagation_variable_binding_transition_extension(Some(&prev_ext));
            }
            if prev.prop_rep_trans_extension.is_some() {
                let new_ext =
                    Self::get_propagation_representative_transition_extension(ctx, this, true);
                let prev_ext = ctx
                    .prop_rep_trans_ext(prev.prop_rep_trans_extension)
                    .clone();
                ctx.prop_rep_trans_ext_mut(new_ext)
                    .init_propagation_representative_transition_extension(Some(&prev_ext));
            }
        }
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
            && self
                .prop_map
                .value(binding_id)
                .has_propagation_binding_descriptor()
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
        let binding = ctx
            .prop_binding_des(prop_bind_des)
            .get_propagation_binding();
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
        let binding = ctx
            .prop_binding_des(prop_bind_des)
            .get_propagation_binding();
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
    pub fn copy_propagation_bindings(
        &mut self,
        prop_bind_map: Option<&PropagationBindingMap>,
    ) -> &mut Self {
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
    pub fn get_propagation_binding_reapply_concept_hash(
        ctx: &mut ProcessContext,
        this: PropagationBindingSetId,
        create: bool,
    ) -> PropagationBindingReapplyConceptHashId {
        let hash = ctx.prop_binding_set(this).reapply_hash;
        if hash.is_none() && create {
            let new_hash = ctx.alloc_prop_binding_reapply_con_hash(
                PropagationBindingReapplyConceptHash::new(INVALID),
            );
            ctx.prop_binding_reapply_con_hash_mut(new_hash)
                .init_propagation_binding_reapply_concept_hash(None);
            ctx.prop_binding_set_mut(this).reapply_hash = new_hash;
            return new_hash;
        }
        hash
    }

    /// Port of `addPropagationBindingReapplyConceptDescriptor`.
    pub fn add_propagation_binding_reapply_concept_descriptor(
        ctx: &mut ProcessContext,
        this: PropagationBindingSetId,
        prop_bind_reapply_con_des: PropagationBindingReapplyConceptDescriptorId,
    ) {
        let hash = Self::get_propagation_binding_reapply_concept_hash(ctx, this, true);
        let reapply_indi = ctx
            .prop_binding_reapply_con_des(prop_bind_reapply_con_des)
            .get_reapply_individual_node();
        let concept_des = ctx
            .prop_binding_reapply_con_des(prop_bind_reapply_con_des)
            .get_concept_descriptor();
        let concept = ctx.con_desc(concept_des).get_concept();
        PropagationBindingReapplyConceptHash::add_propagation_binding_reapply_concept_descriptor_for_individual(
            ctx,
            hash,
            reapply_indi,
            concept,
            prop_bind_reapply_con_des,
        );

        // CPropagationBindingMapData& data = mPropMap[reapplyConDes->getPropagationBinding()->getPropagationID()];
        let binding = ctx
            .prop_binding_reapply_con_des(prop_bind_reapply_con_des)
            .get_propagation_binding();
        let prop_id = ctx.prop_binding(binding).get_propagation_id();
        // data.setReapplyConceptDescriptor(reapplyConDes->append(data.getReapplyConceptDescriptor()))
        let old_head = ctx
            .prop_binding_set(this)
            .prop_map
            .value(prop_id)
            .get_reapply_concept_descriptor();
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
    pub fn get_propagation_variable_binding_transition_extension(
        ctx: &mut ProcessContext,
        this: PropagationBindingSetId,
        create: bool,
    ) -> PropagationVariableBindingTransitionExtensionId {
        let ext = ctx.prop_binding_set(this).prop_var_bind_trans_extension;
        if ext.is_none() && create {
            let new_ext = ctx.alloc_prop_var_bind_trans_ext(
                PropagationVariableBindingTransitionExtension::new(INVALID),
            );
            ctx.prop_var_bind_trans_ext_mut(new_ext)
                .init_propagation_variable_binding_transition_extension(None);
            ctx.prop_binding_set_mut(this).prop_var_bind_trans_extension = new_ext;
            return new_ext;
        }
        ext
    }

    /// Port of `getPropagationRepresentativeTransitionExtension(bool create)`.
    pub fn get_propagation_representative_transition_extension(
        ctx: &mut ProcessContext,
        this: PropagationBindingSetId,
        create: bool,
    ) -> PropagationRepresentativeTransitionExtensionId {
        let ext = ctx.prop_binding_set(this).prop_rep_trans_extension;
        if ext.is_none() && create {
            let new_ext = ctx.alloc_prop_rep_trans_ext(
                PropagationRepresentativeTransitionExtension::new(INVALID),
            );
            ctx.prop_rep_trans_ext_mut(new_ext)
                .init_propagation_representative_transition_extension(None);
            ctx.prop_binding_set_mut(this).prop_rep_trans_extension = new_ext;
            return new_ext;
        }
        ext
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
// resolve. Each line is one `Arena<T>` field + its `arena_accessors!` trio. The
// per-test pool objects each get their own arena; `CPropagationBindingMap` /
// `…MapData` and `CPropagationBindingReapplyConceptHashData` are held BY VALUE
// and need NO arena.
//
//   prop_bindings:               Arena<PropagationBinding>                        | PropagationBindingId                          | prop_binding / prop_binding_mut / alloc_prop_binding
//   prop_binding_descs:          Arena<PropagationBindingDescriptor>              | PropagationBindingDescriptorId                | prop_binding_des / prop_binding_des_mut / alloc_prop_binding_des
//   prop_binding_reapply_con_descs: Arena<PropagationBindingReapplyConceptDescriptor> | PropagationBindingReapplyConceptDescriptorId | prop_binding_reapply_con_des / prop_binding_reapply_con_des_mut / alloc_prop_binding_reapply_con_des
//   prop_binding_reapply_con_hashes: Arena<PropagationBindingReapplyConceptHash> | PropagationBindingReapplyConceptHashId        | prop_binding_reapply_con_hash / prop_binding_reapply_con_hash_mut / alloc_prop_binding_reapply_con_hash
//   prop_binding_sets:           Arena<PropagationBindingSet>                     | PropagationBindingSetId                       | prop_binding_set / prop_binding_set_mut / alloc_prop_binding_set
//
// Imports the reconcile adds to `context.rs`:
//   use super::propagation_binding::{
//       PropagationBinding, PropagationBindingDescriptor,
//       PropagationBindingReapplyConceptDescriptor,
//       PropagationBindingReapplyConceptHash, PropagationBindingSet,
//       PropagationBindingId, PropagationBindingDescriptorId,
//       PropagationBindingReapplyConceptDescriptorId,
//       PropagationBindingReapplyConceptHashId, PropagationBindingSetId,
//   };
// and `pub mod propagation_binding;` in `process/mod.rs`.

#[cfg(test)]
mod tests {
    use super::super::descriptor::ConceptDescriptor;
    use super::super::node::IndividualProcessNode;
    use super::super::representative::{
        RepresentativePropagationDescriptor, RepresentativePropagationMapData,
    };
    use super::*;

    fn alloc_concept_descriptor(ctx: &mut ProcessContext, concept: ConceptId) -> ConDescId {
        let mut descriptor = ConceptDescriptor::new();
        descriptor.concept = concept;
        ctx.alloc_con_desc(descriptor)
    }

    fn alloc_reapply_descriptor(
        ctx: &mut ProcessContext,
        node: NodeId,
        binding: PropagationBindingId,
        concept_descriptor: ConDescId,
    ) -> PropagationBindingReapplyConceptDescriptorId {
        let mut descriptor = PropagationBindingReapplyConceptDescriptor::new();
        descriptor.init_reapply_descriptor(node, binding, concept_descriptor, TrackPointId::NONE);
        ctx.alloc_prop_binding_reapply_con_des(descriptor)
    }

    #[test]
    fn propagation_binding_reapply_hash_add_take_and_iterate() {
        let mut ctx = ProcessContext::new();
        let concept = ConceptId::new(17);
        let pair = (41, concept);
        let hash = ctx.alloc_prop_binding_reapply_con_hash(
            PropagationBindingReapplyConceptHash::new(INVALID),
        );
        let first = ctx
            .alloc_prop_binding_reapply_con_des(PropagationBindingReapplyConceptDescriptor::new());
        let second = ctx
            .alloc_prop_binding_reapply_con_des(PropagationBindingReapplyConceptDescriptor::new());
        let third = ctx
            .alloc_prop_binding_reapply_con_des(PropagationBindingReapplyConceptDescriptor::new());

        PropagationBindingReapplyConceptHash::add_propagation_binding_reapply_concept_descriptor(
            &mut ctx, hash, pair, first,
        );
        assert!(ctx
            .prop_binding_reapply_con_hash(hash)
            .has_propagation_binding_reapply_concept_descriptor(pair));

        PropagationBindingReapplyConceptHash::add_propagation_binding_reapply_concept_descriptor(
            &mut ctx, hash, pair, second,
        );
        assert_eq!(ctx.prop_binding_reapply_con_des(second).get_next(), first);
        assert_eq!(
            ctx.prop_binding_reapply_con_hash_mut(hash)
                .take_propagation_binding_reapply_concept_descriptor(pair),
            second
        );
        assert!(
            !ctx.prop_binding_reapply_con_hash(hash)
                .has_propagation_binding_reapply_concept_descriptor(pair),
            "Konclude takePropagationBindingReapplyConceptDescriptor clears the stored hash entry"
        );

        PropagationBindingReapplyConceptHash::add_propagation_binding_reapply_concept_descriptor(
            &mut ctx, hash, pair, second,
        );
        assert!(
            ctx.prop_binding_reapply_con_hash(hash)
                .has_propagation_binding_reapply_concept_descriptor(pair),
            "re-added descriptor should be visible to the live iterator"
        );

        let mut iterator = ctx
            .prop_binding_reapply_con_hash_mut(hash)
            .get_propagation_binding_reapply_concept_descriptor_iterator();
        assert_eq!(iterator.next_reapply_descriptor(false), second);
        iterator.clear_reapply_descriptor();
        assert_eq!(
            iterator.next_reapply_descriptor(false),
            PropagationBindingReapplyConceptDescriptorId::NONE
        );
        assert_eq!(
            iterator.next_reapply_descriptor(true),
            PropagationBindingReapplyConceptDescriptorId::NONE
        );
        assert_eq!(
            iterator.next_reapply_descriptor(true),
            PropagationBindingReapplyConceptDescriptorId::NONE
        );
        drop(iterator);
        assert!(
            !ctx.prop_binding_reapply_con_hash(hash)
                .has_propagation_binding_reapply_concept_descriptor(pair),
            "iterator clearReapplyDescriptor mutates the live hash value"
        );
    }

    #[test]
    fn propagation_binding_set_reapply_descriptor_updates_hash_and_map() {
        let mut ctx = ProcessContext::new();
        let concept = ConceptId::new(23);
        let node = ctx.alloc_node(IndividualProcessNode::default());
        ctx.node_mut(node).set_individual_node_id(501);
        let concept_descriptor = alloc_concept_descriptor(&mut ctx, concept);
        let mut binding = PropagationBinding::new();
        binding.init_propagation_binding(
            77,
            TrackPointId::NONE,
            node,
            concept_descriptor,
            VariableId::NONE,
        );
        let binding = ctx.alloc_prop_binding(binding);
        let set = ctx.alloc_prop_binding_set(PropagationBindingSet::new(INVALID));
        let first = alloc_reapply_descriptor(&mut ctx, node, binding, concept_descriptor);
        let second = alloc_reapply_descriptor(&mut ctx, node, binding, concept_descriptor);
        let third = alloc_reapply_descriptor(&mut ctx, node, binding, concept_descriptor);

        assert!(ctx.prop_binding_set(set).reapply_hash.is_none());
        PropagationBindingSet::add_propagation_binding_reapply_concept_descriptor(
            &mut ctx, set, first,
        );
        let hash = ctx.prop_binding_set(set).reapply_hash;
        assert!(hash.is_some());
        assert_eq!(
            ctx.prop_binding_set(set)
                .prop_map
                .value(77)
                .get_reapply_concept_descriptor(),
            first
        );
        assert!(ctx
            .prop_binding_reapply_con_hash(hash)
            .has_propagation_binding_reapply_concept_descriptor((501, concept)));

        PropagationBindingSet::add_propagation_binding_reapply_concept_descriptor(
            &mut ctx, set, second,
        );
        assert_eq!(ctx.prop_binding_reapply_con_des(second).get_next(), first);
        assert_eq!(
            ctx.prop_binding_set(set)
                .prop_map
                .value(77)
                .get_reapply_concept_descriptor(),
            second
        );
        assert_eq!(
            ctx.prop_binding_reapply_con_hash_mut(hash)
                .take_propagation_binding_reapply_concept_descriptor((501, concept)),
            second
        );
        assert!(!ctx
            .prop_binding_reapply_con_hash(hash)
            .has_propagation_binding_reapply_concept_descriptor((501, concept)));
        PropagationBindingReapplyConceptHash::add_propagation_binding_reapply_concept_descriptor(
            &mut ctx,
            hash,
            (501, concept),
            third,
        );

        let snapshot = {
            let source = ctx.prop_binding_set(set);
            let mut snapshot = PropagationBindingSet::new(INVALID);
            snapshot.init_propagation_binding_set(Some(source));
            snapshot.reapply_hash = source.reapply_hash;
            snapshot
        };
        let copied_set = ctx.alloc_prop_binding_set(PropagationBindingSet::new(INVALID));
        PropagationBindingSet::init_propagation_binding_set_in_context(
            &mut ctx,
            copied_set,
            Some(&snapshot),
        );
        let copied_hash = ctx.prop_binding_set(copied_set).reapply_hash;
        assert!(copied_hash.is_some());
        assert_ne!(copied_hash, hash);
        assert_eq!(
            ctx.prop_binding_reapply_con_hash_mut(copied_hash)
                .take_propagation_binding_reapply_concept_descriptor((501, concept)),
            third
        );
    }

    #[test]
    fn representative_transition_extension_copies_cursors_and_maps() {
        let mut ctx = ProcessContext::new();
        let source_set = ctx.alloc_prop_binding_set(PropagationBindingSet::new(INVALID));
        let source_ext = PropagationBindingSet::get_propagation_representative_transition_extension(
            &mut ctx, source_set, true,
        );
        let bind_des = ctx.alloc_prop_binding_des(PropagationBindingDescriptor::new());
        let left_des = ctx.alloc_rep_prop_des(RepresentativePropagationDescriptor::new());
        let right_des = ctx.alloc_rep_prop_des(RepresentativePropagationDescriptor::new());

        {
            let ext = ctx.prop_rep_trans_ext_mut(source_ext);
            ext.set_last_analysed_propagate_all_flag(true)
                .set_last_analysed_propagation_binding_descriptor(bind_des)
                .set_left_last_representative_joining_descriptor(left_des)
                .set_right_last_representative_joining_descriptor(right_des);
            ext.get_left_representative_propagation_map_mut()
                .map
                .insert(10, RepresentativePropagationMapData::new(left_des));
            ext.get_right_representative_propagation_map_mut()
                .map
                .insert(20, RepresentativePropagationMapData::new(right_des));
        }

        let source_snapshot = {
            let source = ctx.prop_binding_set(source_set);
            let mut snapshot = PropagationBindingSet::new(INVALID);
            snapshot.init_propagation_binding_set(Some(source));
            snapshot.prop_rep_trans_extension = source.prop_rep_trans_extension;
            snapshot
        };
        let target_set = ctx.alloc_prop_binding_set(PropagationBindingSet::new(INVALID));
        PropagationBindingSet::init_propagation_binding_set_in_context(
            &mut ctx,
            target_set,
            Some(&source_snapshot),
        );

        let target_ext = ctx.prop_binding_set(target_set).prop_rep_trans_extension;
        assert!(target_ext.is_some());
        let copied = ctx.prop_rep_trans_ext(target_ext);
        assert!(copied.get_last_analysed_propagate_all_flag());
        assert_eq!(
            copied.get_last_analysed_propagation_binding_descriptor(),
            bind_des
        );
        assert_eq!(
            copied.get_left_last_representative_joining_descriptor(),
            left_des
        );
        assert_eq!(
            copied.get_right_last_representative_joining_descriptor(),
            right_des
        );
        assert_eq!(
            copied
                .get_left_representative_propagation_map()
                .value(10)
                .get_representative_propagation_descriptor(),
            left_des
        );
        assert_eq!(
            copied
                .get_right_representative_propagation_map()
                .value(20)
                .get_representative_propagation_descriptor(),
            right_des
        );

        let fresh_set = ctx.alloc_prop_binding_set(PropagationBindingSet::new(INVALID));
        let fresh_ext = PropagationBindingSet::get_propagation_representative_transition_extension(
            &mut ctx, fresh_set, true,
        );
        assert!(fresh_ext.is_some());
        let fresh = ctx.prop_rep_trans_ext(fresh_ext);
        assert!(!fresh.get_last_analysed_propagate_all_flag());
        assert!(fresh
            .get_last_analysed_propagation_binding_descriptor()
            .is_none());
        assert_eq!(fresh.get_left_representative_propagation_map().count(), 0);
        assert_eq!(fresh.get_right_representative_propagation_map().count(), 0);
    }
}
