//! `process::representative` (port unit **W3.5r**) — the representative
//! variable-binding-path-set subsystem that the `u17`/`u33` representative-binding
//! bodies defer over.
//!
//! This is the *representative* side of the binding machinery, distinct from the
//! W2.7 variable-binding-path arenas (`process::varbind`) and the W3c
//! propagation-binding subsystem (`process::propagation_binding`). Konclude folds
//! incomparable variable-binding paths into a shared *representative* (a
//! `CRepresentativeVariableBindingPathSetData`, identified by a `getRepresentativeID()`)
//! and propagates the representative once along the completion graph instead of every
//! member path. These are the classes the representative-propagation rules
//! (`updateRepresentativePropagationSet`, `requiresRepresentativePropagation`,
//! `createCommonJoiningAll`, …) in `completion/{u05,u06,u17,u33}.rs` walk; until now
//! they were unported (kept opaque `Cint64` in those bodies and in
//! `varbind::RepresentativeVariableBindingPathMapData`).
//!
//! Classes ported here (one Rust struct per C++ class, `/// Port of …`):
//!   * `CRepresentativeVariableBindingPathSetDataSignature` — the rolling key signature
//!   * `CRepresentativeVariableBindingPathSetData`          — the representative itself
//!   * `CRepresentativeVariableBindingPathSetMigrateData`   — its localised migrate payload
//!   * `CRepresentativeContainingMapData`                   — contained-representative map value
//!   * `CRepresentativeContainingMap`                       — repID → contained-representative
//!   * `CRepresentativePropagationMapData`                  — propagation-map value (descriptor)
//!   * `CRepresentativePropagationMap`                      — repID → propagation-map-data
//!   * `CRepresentativePropagationDescriptor`               — linker over representatives (+ dep)
//!   * `CRepresentativePropagationSet`                      — a concept's incoming/outgoing reps
//!   * `CRepresentativeVariableBindingPathSetHash{Data}`    — signature-keyed rep-set hash
//!
//! `CRepresentativeVariableBindingPathMap{,Data}` are NOT re-ported here — they already
//! landed faithfully in `process::varbind` (W2.7); the migrate-data holds that map by
//! value. This unit re-aliases the W2.7-DEFER opaque `Cint64` marker that stood in for
//! `CRepresentativeVariableBindingPathSetData*` (`varbind::RepresentativeVariableBindingPathMapData
//! ::resolve_rep_var_bind_path_set_data`) onto the real
//! [`RepresentativeVariableBindingPathSetDataId`].
//!
//! ## Memory model (the global `[ownership]` decision, `model/substrate.rs`)
//!
//! Every `CXxx*` becomes a typed arena `Id<T>` (`Id::NONE` == `nullptr`). The four
//! per-test pool objects (the set data, its migrate data, the propagation descriptor,
//! the propagation set) each get an `Arena<T>` field on `ProcessContext` (listed in the
//! `// W3.5r-ARENA-ADDITIONS` block at the foot of this file). The four `CPROCESSMAP`s
//! / the signature are held BY VALUE by their owners and need NO arena (the
//! `varbind::RepresentativeVariableBindingPathMap` precedent). The intrusive
//! `CLinkerBase` / `CDependencyTracker` bases are folded to `data`/`next`/
//! `dep_track_point` fields; chain-walking + allocating operations are ported as
//! **associated functions over `ctx: &mut ProcessContext` + `Id`s** (the W3.5 accessor
//! convention) so a receiver borrowed out of `ctx` never aliases a second `ctx` borrow.
//!
//! ## Representative JOIN substrate
//!
//! `CRepresentativeVariableBindingPathSetData` lazily allocates a
//! `CRepresentativeVariableBindingPathSetJoiningHash`, now ported as the
//! per-representative path-set `CPROCESSHASH<CConcept*,…>` joining-data cache.
//! The global representative joining hash and common-key/all-data maps are in
//! this module too; the still-missing public JOIN pieces are the global
//! variable-binding-path joining-key hash/data/hasher and the completion rule.

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
use super::varbind::{
    RepresentativeVariableBindingPathMap, VarBindingDescriptorId, VarBindingPathId,
    VariableBindingDescriptor,
};
use super::{ConDescId, TrackPointId};

// ===========================================================================
// Process-layer id aliases for the W3.5r representative classes.
// ===========================================================================
/// `CRepresentativeVariableBindingPathSetData*`        → `RepresentativeVariableBindingPathSetDataId`.
pub type RepresentativeVariableBindingPathSetDataId = Id<RepresentativeVariableBindingPathSetData>;
/// `CRepresentativeVariableBindingPathSetMigrateData*` → `RepresentativeVariableBindingPathSetMigrateDataId`.
pub type RepresentativeVariableBindingPathSetMigrateDataId =
    Id<RepresentativeVariableBindingPathSetMigrateData>;
/// `CRepresentativePropagationDescriptor*`             → `RepresentativePropagationDescriptorId`.
pub type RepresentativePropagationDescriptorId = Id<RepresentativePropagationDescriptor>;
/// `CRepresentativePropagationSet*`                    → `RepresentativePropagationSetId`.
pub type RepresentativePropagationSetId = Id<RepresentativePropagationSet>;
/// `CConceptRepresentativePropagationSetHash*`         → `ConceptRepresentativePropagationSetHashId`.
pub type ConceptRepresentativePropagationSetHashId = Id<ConceptRepresentativePropagationSetHash>;
/// `CRepresentativeVariableBindingPathSetHash*`        → `RepresentativeVariableBindingPathSetHashId`.
pub type RepresentativeVariableBindingPathSetHashId = Id<RepresentativeVariableBindingPathSetHash>;
/// `CRepresentativeVariableBindingPathHash*`           → `RepresentativeVariableBindingPathHashId`.
pub type RepresentativeVariableBindingPathHashId = Id<RepresentativeVariableBindingPathHash>;

/// `CRepresentativeJoiningData*`                      → `RepresentativeJoiningDataId`.
pub type RepresentativeJoiningDataId = Id<RepresentativeJoiningData>;
/// `CRepresentativeJoiningHash*`                      → `RepresentativeJoiningHashId`.
pub type RepresentativeJoiningHashId = Id<RepresentativeJoiningHash>;
/// `CRepresentativeVariableBindingPathJoiningKeyData*` → `RepresentativeVariableBindingPathJoiningKeyDataId`.
pub type RepresentativeVariableBindingPathJoiningKeyDataId =
    Id<RepresentativeVariableBindingPathJoiningKeyData>;
/// `CRepresentativeVariableBindingPathJoiningKeyHash*` → `RepresentativeVariableBindingPathJoiningKeyHashId`.
pub type RepresentativeVariableBindingPathJoiningKeyHashId =
    Id<RepresentativeVariableBindingPathJoiningKeyHash>;
/// `CRepresentativeVariableBindingPathSetJoiningData*` → `RepresentativeVariableBindingPathSetJoiningDataId`.
pub type RepresentativeVariableBindingPathSetJoiningDataId =
    Id<RepresentativeVariableBindingPathSetJoiningData>;
/// `CRepresentativeVariableBindingPathSetJoiningHash*` → `RepresentativeVariableBindingPathSetJoiningHashId`.
pub type RepresentativeVariableBindingPathSetJoiningHashId =
    Id<RepresentativeVariableBindingPathSetJoiningHash>;

// ===========================================================================
// Representative joining key/common-key support maps
// (`CRepresentativeVariableBindingPathSetJoiningKey*`,
//  `CRepresentativeJoiningCommonKey*`,
//  `CRepresentativeJoiningAllDataExtension`)
// ===========================================================================

/// Port of `CRepresentativeVariableBindingPathSetJoiningKeyDataMap`.
///
/// KONCLUDE-PORT-NOTE[ownership]: C++ subclasses `CPROCESSMAP<cint64,
/// CVariableBindingPath*>`; this port stores the map by value with
/// `VarBindingPathId` values. It remains ctx-free for the same reason as
/// `RepresentativeVariableBindingPathMap`.
#[derive(Debug, Clone)]
pub struct RepresentativeVariableBindingPathSetJoiningKeyDataMap {
    /// `CProcessContext* mProcessContext` (opaque).
    pub process_context: Cint64,
    /// `CPROCESSMAP<cint64,CVariableBindingPath*>` base storage.
    pub map: HashMap<Cint64, VarBindingPathId>,
}

impl RepresentativeVariableBindingPathSetJoiningKeyDataMap {
    /// Port of `CRepresentativeVariableBindingPathSetJoiningKeyDataMap(CProcessContext*)`.
    pub fn new(process_context: Cint64) -> Self {
        Self {
            process_context,
            map: HashMap::new(),
        }
    }

    /// Port of `initVariableBindingPathSetJoiningKeyDataMap`.
    pub fn init_variable_binding_path_set_joining_key_data_map(
        &mut self,
        prev_map: Option<&RepresentativeVariableBindingPathSetJoiningKeyDataMap>,
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

    /// Port of `CPROCESSMAP::insert`.
    pub fn insert(&mut self, key: Cint64, path: VarBindingPathId) {
        self.map.insert(key, path);
    }

    /// Port of `CPROCESSMAP::value`.
    pub fn value(&self, key: Cint64) -> VarBindingPathId {
        self.map.get(&key).copied().unwrap_or(Id::NONE)
    }
}

/// Port of `CRepresentativeVariableBindingPathSetJoiningKeyMapData`.
#[derive(Debug, Clone)]
pub struct RepresentativeVariableBindingPathSetJoiningKeyMapData {
    /// `CRepresentativeVariableBindingPathSetJoiningKeyDataMap*`.
    pub rep_var_bind_path_set_joining_key_data_map:
        Option<RepresentativeVariableBindingPathSetJoiningKeyDataMap>,
}

impl Default for RepresentativeVariableBindingPathSetJoiningKeyMapData {
    fn default() -> Self {
        Self::new(None)
    }
}

impl RepresentativeVariableBindingPathSetJoiningKeyMapData {
    /// Port of `CRepresentativeVariableBindingPathSetJoiningKeyMapData(...)`.
    pub fn new(
        rep_var_bind_path_set_joining_key_data_map: Option<
            RepresentativeVariableBindingPathSetJoiningKeyDataMap,
        >,
    ) -> Self {
        Self {
            rep_var_bind_path_set_joining_key_data_map,
        }
    }

    /// Port of `getRepresentativeVariableBindingPathSetJoiningKeyDataMap`.
    pub fn get_representative_variable_binding_path_set_joining_key_data_map(
        &self,
    ) -> Option<&RepresentativeVariableBindingPathSetJoiningKeyDataMap> {
        self.rep_var_bind_path_set_joining_key_data_map.as_ref()
    }

    /// Mutable companion for the map pointer.
    pub fn get_representative_variable_binding_path_set_joining_key_data_map_mut(
        &mut self,
    ) -> Option<&mut RepresentativeVariableBindingPathSetJoiningKeyDataMap> {
        self.rep_var_bind_path_set_joining_key_data_map.as_mut()
    }

    /// Port of `hasRepresentativeVariableBindingPathSetJoiningKeyDataMap`.
    pub fn has_representative_variable_binding_path_set_joining_key_data_map(&self) -> bool {
        self.rep_var_bind_path_set_joining_key_data_map.is_some()
    }

    /// Port of `setRepresentativeVariableBindingPathSetJoiningKeyDataMap`.
    pub fn set_representative_variable_binding_path_set_joining_key_data_map(
        &mut self,
        rep_var_bind_path_set_joining_key_data_map: RepresentativeVariableBindingPathSetJoiningKeyDataMap,
    ) -> &mut Self {
        self.rep_var_bind_path_set_joining_key_data_map =
            Some(rep_var_bind_path_set_joining_key_data_map);
        self
    }
}

/// Port of `CRepresentativeVariableBindingPathSetJoiningKeyMap`.
#[derive(Debug, Clone)]
pub struct RepresentativeVariableBindingPathSetJoiningKeyMap {
    /// `CProcessContext* mProcessContext` (opaque).
    pub process_context: Cint64,
    /// `CPROCESSMAP<cint64,CRepresentativeVariableBindingPathSetJoiningKeyMapData>`.
    pub map: HashMap<Cint64, RepresentativeVariableBindingPathSetJoiningKeyMapData>,
}

impl RepresentativeVariableBindingPathSetJoiningKeyMap {
    /// Port of `CRepresentativeVariableBindingPathSetJoiningKeyMap(CProcessContext*)`.
    pub fn new(process_context: Cint64) -> Self {
        Self {
            process_context,
            map: HashMap::new(),
        }
    }

    /// Port of `initRepresentativeVariableBindingPathSetJoiningKeyMap`.
    pub fn init_representative_variable_binding_path_set_joining_key_map(
        &mut self,
        prev_map: Option<&RepresentativeVariableBindingPathSetJoiningKeyMap>,
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

    /// Port of `CPROCESSMAP::value`.
    pub fn value(&self, key: Cint64) -> RepresentativeVariableBindingPathSetJoiningKeyMapData {
        self.map.get(&key).cloned().unwrap_or_default()
    }

    /// Port of `getJoiningKeyDataMap(joiningKey, create)`.
    pub fn get_joining_key_data_map(
        &mut self,
        joining_key: Cint64,
        create: bool,
    ) -> Option<&mut RepresentativeVariableBindingPathSetJoiningKeyDataMap> {
        if create {
            let process_context = self.process_context;
            let data = self.map.entry(joining_key).or_default();
            if !data.has_representative_variable_binding_path_set_joining_key_data_map() {
                let mut data_map =
                    RepresentativeVariableBindingPathSetJoiningKeyDataMap::new(process_context);
                data_map.init_variable_binding_path_set_joining_key_data_map(None);
                data.set_representative_variable_binding_path_set_joining_key_data_map(data_map);
            }
            data.get_representative_variable_binding_path_set_joining_key_data_map_mut()
        } else {
            self.map.get_mut(&joining_key).and_then(|data| {
                data.get_representative_variable_binding_path_set_joining_key_data_map_mut()
            })
        }
    }

    /// Read-only counterpart for the C++ `create=false` branch.
    pub fn get_joining_key_data_map_existing(
        &self,
        joining_key: Cint64,
    ) -> Option<&RepresentativeVariableBindingPathSetJoiningKeyDataMap> {
        self.map.get(&joining_key).and_then(|data| {
            data.get_representative_variable_binding_path_set_joining_key_data_map()
        })
    }
}

/// Port of `CRepresentativeJoiningCommonKeyData`.
#[derive(Debug, Clone)]
pub struct RepresentativeJoiningCommonKeyData {
    /// `CRepresentativeVariableBindingPathSetJoiningKeyDataMap* mLeftJoiningDataMap`.
    pub left_joining_data_map: RepresentativeVariableBindingPathSetJoiningKeyDataMap,
    /// `CRepresentativeVariableBindingPathSetJoiningKeyDataMap* mRightJoiningDataMap`.
    pub right_joining_data_map: RepresentativeVariableBindingPathSetJoiningKeyDataMap,
}

impl RepresentativeJoiningCommonKeyData {
    /// Port of `CRepresentativeJoiningCommonKeyData(left,right)`.
    pub fn new(
        left_joining_data_map: RepresentativeVariableBindingPathSetJoiningKeyDataMap,
        right_joining_data_map: RepresentativeVariableBindingPathSetJoiningKeyDataMap,
    ) -> Self {
        Self {
            left_joining_data_map,
            right_joining_data_map,
        }
    }

    /// Port of `getLeftCount`.
    pub fn get_left_count(&self) -> Cint64 {
        self.left_joining_data_map.count()
    }

    /// Port of `getRightCount`.
    pub fn get_right_count(&self) -> Cint64 {
        self.right_joining_data_map.count()
    }

    /// Port of `getLeftJoiningDataMap`.
    pub fn get_left_joining_data_map(
        &self,
    ) -> &RepresentativeVariableBindingPathSetJoiningKeyDataMap {
        &self.left_joining_data_map
    }

    /// Port of `getRightJoiningDataMap`.
    pub fn get_right_joining_data_map(
        &self,
    ) -> &RepresentativeVariableBindingPathSetJoiningKeyDataMap {
        &self.right_joining_data_map
    }
}

/// Port of `CRepresentativeJoiningCommonKeyMap`.
#[derive(Debug, Clone)]
pub struct RepresentativeJoiningCommonKeyMap {
    /// `CProcessContext* mProcessContext` (opaque).
    pub process_context: Cint64,
    /// `CPROCESSMAP<cint64,CRepresentativeJoiningCommonKeyData>`.
    pub map: HashMap<Cint64, RepresentativeJoiningCommonKeyData>,
}

impl RepresentativeJoiningCommonKeyMap {
    /// Port of `CRepresentativeJoiningCommonKeyMap(CProcessContext*)`.
    pub fn new(process_context: Cint64) -> Self {
        Self {
            process_context,
            map: HashMap::new(),
        }
    }

    /// Port of `initRepresentativeJoiningCommonKeyMap`.
    pub fn init_representative_joining_common_key_map(
        &mut self,
        prev_map: Option<&RepresentativeJoiningCommonKeyMap>,
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

    /// Port of `CPROCESSMAP::insert`.
    pub fn insert(&mut self, key: Cint64, data: RepresentativeJoiningCommonKeyData) {
        self.map.insert(key, data);
    }

    /// Port of `CPROCESSMAP::value`.
    pub fn value(&self, key: Cint64) -> Option<&RepresentativeJoiningCommonKeyData> {
        self.map.get(&key)
    }
}

/// Port of `CRepresentativeJoiningAllDataExtension`.
#[derive(Debug, Clone)]
pub struct RepresentativeJoiningAllDataExtension {
    /// `CProcessContext* mProcessContext` (opaque).
    pub process_context: Cint64,
    /// `CRepresentativeVariableBindingPathSetData* mRepVarBindPathSetData`.
    pub rep_var_bind_path_set_data: RepresentativeVariableBindingPathSetDataId,
    /// `CRepresentativeVariableBindingPathMap* mLeftResolveMap`.
    pub left_resolve_map: Option<RepresentativeVariableBindingPathMap>,
    /// `CRepresentativeVariableBindingPathMap* mRightResolveMap`.
    pub right_resolve_map: Option<RepresentativeVariableBindingPathMap>,
}

impl RepresentativeJoiningAllDataExtension {
    /// Port of `CRepresentativeJoiningAllDataExtension(CProcessContext*)`.
    pub fn new(process_context: Cint64) -> Self {
        Self {
            process_context,
            rep_var_bind_path_set_data: Id::NONE,
            left_resolve_map: None,
            right_resolve_map: None,
        }
    }

    /// Port of `getRepresentativeVariableBindingPathSetData`.
    pub fn get_representative_variable_binding_path_set_data(
        &self,
    ) -> RepresentativeVariableBindingPathSetDataId {
        self.rep_var_bind_path_set_data
    }

    /// Port of `setRepresentativeVariableBindingPathSetData`.
    pub fn set_representative_variable_binding_path_set_data(
        &mut self,
        rep_var_bind_path_set_data: RepresentativeVariableBindingPathSetDataId,
    ) -> &mut Self {
        self.rep_var_bind_path_set_data = rep_var_bind_path_set_data;
        self
    }

    /// Port of `getResolveVariableBindingPathMap(leftMap, create)`.
    pub fn get_resolve_variable_binding_path_map(
        &mut self,
        left_map: bool,
        create: bool,
    ) -> Option<&mut RepresentativeVariableBindingPathMap> {
        if left_map {
            self.get_left_resolve_variable_binding_path_map(create)
        } else {
            self.get_right_resolve_variable_binding_path_map(create)
        }
    }

    /// Port of `getLeftResolveVariableBindingPathMap`.
    pub fn get_left_resolve_variable_binding_path_map(
        &mut self,
        create: bool,
    ) -> Option<&mut RepresentativeVariableBindingPathMap> {
        if create && self.left_resolve_map.is_none() {
            let mut map = RepresentativeVariableBindingPathMap::new(self.process_context);
            map.init_variable_binding_path_map(None);
            self.left_resolve_map = Some(map);
        }
        self.left_resolve_map.as_mut()
    }

    /// Port of `getRightResolveVariableBindingPathMap`.
    pub fn get_right_resolve_variable_binding_path_map(
        &mut self,
        create: bool,
    ) -> Option<&mut RepresentativeVariableBindingPathMap> {
        if create && self.right_resolve_map.is_none() {
            let mut map = RepresentativeVariableBindingPathMap::new(self.process_context);
            map.init_variable_binding_path_map(None);
            self.right_resolve_map = Some(map);
        }
        self.right_resolve_map.as_mut()
    }
}

/// Port of `CRepresentativeVariableBindingPathSetJoiningData`.
#[derive(Debug, Clone)]
pub struct RepresentativeVariableBindingPathSetJoiningData {
    /// `CProcessContext* mProcessContext` (opaque).
    pub process_context: Cint64,
    /// `CRepresentativeVariableBindingPathSetJoiningKeyMap mJoiningKeyMap`.
    pub joining_key_map: RepresentativeVariableBindingPathSetJoiningKeyMap,
}

impl RepresentativeVariableBindingPathSetJoiningData {
    /// Port of `CRepresentativeVariableBindingPathSetJoiningData(CProcessContext*)`.
    pub fn new(process_context: Cint64) -> Self {
        Self {
            process_context,
            joining_key_map: RepresentativeVariableBindingPathSetJoiningKeyMap::new(
                process_context,
            ),
        }
    }

    /// Port of `initRepresentativeVariableBindingPathSetJoiningData`.
    pub fn init_representative_variable_binding_path_set_joining_data(
        &mut self,
        data: Option<&RepresentativeVariableBindingPathSetJoiningData>,
    ) -> &mut Self {
        if let Some(data) = data {
            self.joining_key_map = data.joining_key_map.clone();
        } else {
            self.joining_key_map
                .init_representative_variable_binding_path_set_joining_key_map(None);
        }
        self
    }

    /// Port of `getJoiningKeyMap`.
    pub fn get_joining_key_map(&self) -> &RepresentativeVariableBindingPathSetJoiningKeyMap {
        &self.joining_key_map
    }

    /// Mutable companion for `getJoiningKeyMap`.
    pub fn get_joining_key_map_mut(
        &mut self,
    ) -> &mut RepresentativeVariableBindingPathSetJoiningKeyMap {
        &mut self.joining_key_map
    }
}

/// Port of `CRepresentativeVariableBindingPathSetJoiningHashData`.
#[derive(Debug, Clone, Copy)]
pub struct RepresentativeVariableBindingPathSetJoiningHashData {
    /// `CRepresentativeVariableBindingPathSetJoiningData* mUseJoiningData`.
    pub use_joining_data: RepresentativeVariableBindingPathSetJoiningDataId,
    /// `CRepresentativeVariableBindingPathSetJoiningData* mLocJoiningData`.
    pub loc_joining_data: RepresentativeVariableBindingPathSetJoiningDataId,
}

impl RepresentativeVariableBindingPathSetJoiningHashData {
    /// Port of the default constructor.
    pub fn new() -> Self {
        Self {
            use_joining_data: Id::NONE,
            loc_joining_data: Id::NONE,
        }
    }

    /// Port of the copy constructor: local pointer is nulled, use pointer is shared.
    pub fn copy_from(data: &RepresentativeVariableBindingPathSetJoiningHashData) -> Self {
        Self {
            use_joining_data: data.use_joining_data,
            loc_joining_data: Id::NONE,
        }
    }
}

impl Default for RepresentativeVariableBindingPathSetJoiningHashData {
    fn default() -> Self {
        Self::new()
    }
}

/// Port of `CRepresentativeVariableBindingPathSetJoiningHash`.
#[derive(Debug, Clone)]
pub struct RepresentativeVariableBindingPathSetJoiningHash {
    /// `CProcessContext* mProcessContext` (opaque).
    pub process_context: Cint64,
    /// `CPROCESSHASH<CConcept*,CRepresentativeVariableBindingPathSetJoiningHashData>`.
    pub map: HashMap<ConceptId, RepresentativeVariableBindingPathSetJoiningHashData>,
}

impl RepresentativeVariableBindingPathSetJoiningHash {
    /// Port of `CRepresentativeVariableBindingPathSetJoiningHash(CProcessContext*)`.
    pub fn new(process_context: Cint64) -> Self {
        Self {
            process_context,
            map: HashMap::new(),
        }
    }

    /// Port of `initRepresentativeVariableBindingPathSetJoiningHash`.
    pub fn init_representative_variable_binding_path_set_joining_hash(
        &mut self,
        prev_hash: Option<&RepresentativeVariableBindingPathSetJoiningHash>,
    ) -> &mut Self {
        if let Some(prev_hash) = prev_hash {
            self.map = prev_hash
                .map
                .iter()
                .map(|(key, data)| {
                    (
                        *key,
                        RepresentativeVariableBindingPathSetJoiningHashData::copy_from(data),
                    )
                })
                .collect();
        } else {
            self.map.clear();
        }
        self
    }

    /// Port of `getRepresentativeVariableBindingPathSetJoiningData`.
    pub fn get_representative_variable_binding_path_set_joining_data(
        ctx: &mut ProcessContext,
        this: RepresentativeVariableBindingPathSetJoiningHashId,
        join_concept: ConceptId,
        create: bool,
    ) -> RepresentativeVariableBindingPathSetJoiningDataId {
        if create {
            let existing = ctx
                .rep_var_bind_path_set_joining_hash_mut(this)
                .map
                .entry(join_concept)
                .or_insert_with(RepresentativeVariableBindingPathSetJoiningHashData::new)
                .use_joining_data;
            if existing.is_some() {
                existing
            } else {
                let process_context = ctx.rep_var_bind_path_set_joining_hash(this).process_context;
                let rep_data = ctx.alloc_rep_var_bind_path_set_joining_data(
                    RepresentativeVariableBindingPathSetJoiningData::new(process_context),
                );
                ctx.rep_var_bind_path_set_joining_data_mut(rep_data)
                    .init_representative_variable_binding_path_set_joining_data(None);
                let data = ctx
                    .rep_var_bind_path_set_joining_hash_mut(this)
                    .map
                    .entry(join_concept)
                    .or_insert_with(RepresentativeVariableBindingPathSetJoiningHashData::new);
                data.use_joining_data = rep_data;
                rep_data
            }
        } else {
            ctx.rep_var_bind_path_set_joining_hash(this)
                .map
                .get(&join_concept)
                .copied()
                .unwrap_or_default()
                .use_joining_data
        }
    }
}

/// Port of `CRepresentativeJoiningData`.
#[derive(Debug, Clone)]
pub struct RepresentativeJoiningData {
    /// `CProcessContext* mProcessContext` (opaque).
    pub process_context: Cint64,
    /// `CRepresentativeJoiningCommonKeyMap mJoiningCommonKeyMap`.
    pub joining_common_key_map: RepresentativeJoiningCommonKeyMap,
    /// `CRepresentativeJoiningAllDataExtension* mJoiningAllExtension`.
    pub joining_all_extension: Option<RepresentativeJoiningAllDataExtension>,
}

impl RepresentativeJoiningData {
    /// Port of `CRepresentativeJoiningData(CProcessContext*)`.
    pub fn new(process_context: Cint64) -> Self {
        Self {
            process_context,
            joining_common_key_map: RepresentativeJoiningCommonKeyMap::new(process_context),
            joining_all_extension: None,
        }
    }

    /// Port of `getRepresentativeJoiningCommonKeyMap`.
    pub fn get_representative_joining_common_key_map(&self) -> &RepresentativeJoiningCommonKeyMap {
        &self.joining_common_key_map
    }

    /// Mutable companion for `getRepresentativeJoiningCommonKeyMap`.
    pub fn get_representative_joining_common_key_map_mut(
        &mut self,
    ) -> &mut RepresentativeJoiningCommonKeyMap {
        &mut self.joining_common_key_map
    }

    /// Port of `getJoiningAllExtension`.
    pub fn get_joining_all_extension(
        &mut self,
        create: bool,
    ) -> Option<&mut RepresentativeJoiningAllDataExtension> {
        if create && self.joining_all_extension.is_none() {
            self.joining_all_extension = Some(RepresentativeJoiningAllDataExtension::new(
                self.process_context,
            ));
        }
        self.joining_all_extension.as_mut()
    }
}

/// Port of `CRepresentativeJoiningHashData`.
#[derive(Debug, Clone, Copy)]
pub struct RepresentativeJoiningHashData {
    /// `CRepresentativeJoiningData* mVarBindPathJoiningData`.
    pub var_bind_path_joining_data: RepresentativeJoiningDataId,
}

impl RepresentativeJoiningHashData {
    /// Port of the default constructor.
    pub fn new() -> Self {
        Self {
            var_bind_path_joining_data: Id::NONE,
        }
    }
}

impl Default for RepresentativeJoiningHashData {
    fn default() -> Self {
        Self::new()
    }
}

/// Port of `CRepresentativeJoiningHash`.
#[derive(Debug, Clone)]
pub struct RepresentativeJoiningHash {
    /// `CProcessContext* mContext` (opaque).
    pub process_context: Cint64,
    /// `CPROCESSHASH<TRepIDPair,CRepresentativeJoiningHashData>`.
    pub map: HashMap<(Cint64, Cint64), RepresentativeJoiningHashData>,
}

impl RepresentativeJoiningHash {
    /// Port of `CRepresentativeJoiningHash(CProcessContext*)`.
    pub fn new(process_context: Cint64) -> Self {
        Self {
            process_context,
            map: HashMap::new(),
        }
    }

    /// Port of `initRepresentativeJoiningHash`.
    pub fn init_representative_joining_hash(
        &mut self,
        prev_hash: Option<&RepresentativeJoiningHash>,
    ) -> &mut Self {
        if let Some(prev_hash) = prev_hash {
            self.map = prev_hash.map.clone();
        } else {
            self.map.clear();
        }
        self
    }

    /// Port of `getRepresentativeJoiningData`.
    pub fn get_representative_joining_data(
        ctx: &mut ProcessContext,
        this: RepresentativeJoiningHashId,
        left_rep_data: RepresentativeVariableBindingPathSetDataId,
        right_rep_data: RepresentativeVariableBindingPathSetDataId,
        create: bool,
    ) -> RepresentativeJoiningDataId {
        let left_id = ctx
            .rep_var_bind_path_set_data(left_rep_data)
            .get_representative_id();
        let right_id = ctx
            .rep_var_bind_path_set_data(right_rep_data)
            .get_representative_id();
        let key = (left_id, right_id);
        if create {
            let existing = ctx
                .rep_joining_hash_mut(this)
                .map
                .entry(key)
                .or_insert_with(RepresentativeJoiningHashData::new)
                .var_bind_path_joining_data;
            if existing.is_some() {
                existing
            } else {
                let process_context = ctx.rep_joining_hash(this).process_context;
                let joining_data =
                    ctx.alloc_rep_joining_data(RepresentativeJoiningData::new(process_context));
                ctx.rep_joining_hash_mut(this)
                    .map
                    .entry(key)
                    .or_insert_with(RepresentativeJoiningHashData::new)
                    .var_bind_path_joining_data = joining_data;
                joining_data
            }
        } else {
            ctx.rep_joining_hash(this)
                .map
                .get(&key)
                .copied()
                .unwrap_or_default()
                .var_bind_path_joining_data
        }
    }
}

/// Port of `CRepresentativeVariableBindingPathJoiningKeyData`.
#[derive(Debug, Clone, Copy)]
pub struct RepresentativeVariableBindingPathJoiningKeyData {
    /// `mutable cint64 mCalculatedHashValue`.
    pub calculated_hash_value: Cint64,
    /// `mutable bool mHashValueCalculated`.
    pub hash_value_calculated: bool,
    /// `CVariableBindingDescriptor* mKeyVarBindDesLinker`.
    pub key_var_bind_des_linker: VarBindingDescriptorId,
    /// `cint64 mJoiningKey`.
    pub joining_key: Cint64,
}

impl RepresentativeVariableBindingPathJoiningKeyData {
    /// Port of `CRepresentativeVariableBindingPathJoiningKeyData()`.
    pub fn new() -> Self {
        Self {
            calculated_hash_value: 0,
            hash_value_calculated: false,
            key_var_bind_des_linker: Id::NONE,
            joining_key: 0,
        }
    }

    /// Port of `initVariableBindingPathJoiningData(prevJoinData)`.
    pub fn init_variable_binding_path_joining_data_from_prev(
        &mut self,
        prev_join_data: Option<&RepresentativeVariableBindingPathJoiningKeyData>,
    ) -> &mut Self {
        if let Some(prev) = prev_join_data {
            self.key_var_bind_des_linker = prev.key_var_bind_des_linker;
            self.hash_value_calculated = prev.hash_value_calculated;
            self.calculated_hash_value = prev.calculated_hash_value;
            self.joining_key = prev.joining_key;
        } else {
            self.key_var_bind_des_linker = Id::NONE;
            self.hash_value_calculated = false;
            self.calculated_hash_value = 0;
            self.joining_key = 0;
        }
        self
    }

    /// Port of `initVariableBindingPathJoiningData(keyVarBindDesLinker, joiningKey)`.
    pub fn init_variable_binding_path_joining_data(
        ctx: &mut ProcessContext,
        this: RepresentativeVariableBindingPathJoiningKeyDataId,
        key_var_bind_des_linker: VarBindingDescriptorId,
        joining_key: Cint64,
    ) {
        {
            let data = ctx.rep_var_bind_path_joining_key_data_mut(this);
            data.joining_key = joining_key;
            data.key_var_bind_des_linker = key_var_bind_des_linker;
            data.hash_value_calculated = false;
        }
        let calculated = Self::get_calculated_hash_value(ctx, this);
        ctx.rep_var_bind_path_joining_key_data_mut(this)
            .calculated_hash_value = calculated;
    }

    /// Port of `getKeyVariableBindingDescriptorLinker`.
    pub fn get_key_variable_binding_descriptor_linker(&self) -> VarBindingDescriptorId {
        self.key_var_bind_des_linker
    }

    /// Port of `getJoiningKey`.
    pub fn get_joining_key(&self) -> Cint64 {
        self.joining_key
    }

    fn compute_key_hash(ctx: &ProcessContext, key_head: VarBindingDescriptorId) -> Cint64 {
        let mut hash_value: Cint64 = 0;
        let mut multiplier: Cint64 = 13;
        let mut linker_it = key_head;
        while linker_it.is_some() {
            let variable_binding = ctx.var_binding_des(linker_it).get_variable_binding();
            hash_value = hash_value.wrapping_add(multiplier.wrapping_mul(variable_binding.raw));
            multiplier = multiplier * 2 + 1;
            linker_it = ctx.var_binding_des(linker_it).get_next();
        }
        hash_value
    }

    /// Port of `getCalculatedHashValue`.
    pub fn get_calculated_hash_value(
        ctx: &mut ProcessContext,
        this: RepresentativeVariableBindingPathJoiningKeyDataId,
    ) -> Cint64 {
        if !ctx
            .rep_var_bind_path_joining_key_data(this)
            .hash_value_calculated
        {
            let key_head = ctx
                .rep_var_bind_path_joining_key_data(this)
                .key_var_bind_des_linker;
            let hash_value = Self::compute_key_hash(ctx, key_head);
            let data = ctx.rep_var_bind_path_joining_key_data_mut(this);
            data.hash_value_calculated = true;
            data.calculated_hash_value = hash_value;
        }
        ctx.rep_var_bind_path_joining_key_data(this)
            .calculated_hash_value
    }

    /// Port of `isKeyEquivalentTo(const CRepresentativeVariableBindingPathJoiningKeyData&)`.
    pub fn is_key_equivalent_to_data(
        ctx: &ProcessContext,
        this: RepresentativeVariableBindingPathJoiningKeyDataId,
        data: RepresentativeVariableBindingPathJoiningKeyDataId,
    ) -> bool {
        ctx.rep_var_bind_path_joining_key_data(this).joining_key
            == ctx.rep_var_bind_path_joining_key_data(data).joining_key
    }

    /// Port of `isKeyEquivalentTo(CVariableBindingPath*)`.
    pub fn is_key_equivalent_to_path(
        ctx: &ProcessContext,
        this: RepresentativeVariableBindingPathJoiningKeyDataId,
        var_bind_path: VarBindingPathId,
    ) -> bool {
        let mut linker_it1 = ctx
            .rep_var_bind_path_joining_key_data(this)
            .key_var_bind_des_linker;
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

impl Default for RepresentativeVariableBindingPathJoiningKeyData {
    fn default() -> Self {
        Self::new()
    }
}

/// Port of `CRepresentativeVariableBindingPathJoiningKeyHasher`.
#[derive(Debug, Clone)]
pub struct RepresentativeVariableBindingPathJoiningKeyHasher {
    /// `CRepresentativeVariableBindingPathJoiningKeyData* mJoiningData`.
    pub joining_data: RepresentativeVariableBindingPathJoiningKeyDataId,
    /// `CVariableBindingPath* mVarBindPath`.
    pub var_bind_path: VarBindingPathId,
    /// `CSortedLinker<CVariable*>* mKeyVars`.
    pub key_vars: Vec<VariableId>,
    /// `cint64 mHashValue`.
    pub hash_value: Cint64,
}

impl RepresentativeVariableBindingPathJoiningKeyHasher {
    /// Port of `CRepresentativeVariableBindingPathJoiningKeyHasher(CRepresentativeVariableBindingPathJoiningKeyData*)`.
    pub fn new_from_joining_data(
        ctx: &mut ProcessContext,
        data: RepresentativeVariableBindingPathJoiningKeyDataId,
    ) -> Self {
        let hash_value =
            RepresentativeVariableBindingPathJoiningKeyData::get_calculated_hash_value(ctx, data);
        Self {
            var_bind_path: Id::NONE,
            key_vars: Vec::new(),
            joining_data: data,
            hash_value,
        }
    }

    /// Port of `CRepresentativeVariableBindingPathJoiningKeyHasher(CVariableBindingPath*, CSortedLinker<CVariable*>*)`.
    pub fn new_from_path(
        ctx: &ProcessContext,
        var_bind_path: VarBindingPathId,
        key_vars: &[VariableId],
    ) -> Self {
        let hash_value = Self::calculate_hash_value(ctx, var_bind_path, key_vars);
        Self {
            joining_data: Id::NONE,
            var_bind_path,
            key_vars: key_vars.to_vec(),
            hash_value,
        }
    }

    /// Port of `calculateHashValue`.
    pub fn calculate_hash_value(
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
        while key_vars_it < key_vars.len() && linker_it.is_some() {
            let variable_binding = ctx.var_binding_des(linker_it).get_variable_binding();
            let variable = ctx.var_binding(variable_binding).get_binded_variable();
            let key_variable = key_vars[key_vars_it];
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
        ctx: &ProcessContext,
        hasher: &RepresentativeVariableBindingPathJoiningKeyHasher,
    ) -> bool {
        if self.joining_data.is_some() && hasher.joining_data.is_some() {
            RepresentativeVariableBindingPathJoiningKeyData::is_key_equivalent_to_data(
                ctx,
                self.joining_data,
                hasher.joining_data,
            )
        } else if self.joining_data.is_some() && hasher.var_bind_path.is_some() {
            RepresentativeVariableBindingPathJoiningKeyData::is_key_equivalent_to_path(
                ctx,
                self.joining_data,
                hasher.var_bind_path,
            )
        } else if self.var_bind_path.is_some() && hasher.joining_data.is_some() {
            RepresentativeVariableBindingPathJoiningKeyData::is_key_equivalent_to_path(
                ctx,
                hasher.joining_data,
                self.var_bind_path,
            )
        } else {
            false
        }
    }
}

/// Port of the free `qHash(const CRepresentativeVariableBindingPathJoiningKeyHasher&)`.
pub fn q_hash_representative_joining_key(
    hasher: &RepresentativeVariableBindingPathJoiningKeyHasher,
) -> u32 {
    let key: i64 = hasher.get_hash_value();
    if std::mem::size_of::<u64>() > std::mem::size_of::<u32>() {
        ((key >> (8 * std::mem::size_of::<u32>() as i64 - 1)) ^ key) as u32
    } else {
        key as u32
    }
}

/// Port of `CRepresentativeVariableBindingPathJoiningKeyHashData`.
#[derive(Debug, Clone, Copy)]
pub struct RepresentativeVariableBindingPathJoiningKeyHashData {
    /// `CRepresentativeVariableBindingPathJoiningKeyData* mVarBindPathJoiningData`.
    pub var_bind_path_joining_data: RepresentativeVariableBindingPathJoiningKeyDataId,
}

impl RepresentativeVariableBindingPathJoiningKeyHashData {
    /// Port of the default constructor.
    pub fn new() -> Self {
        Self {
            var_bind_path_joining_data: Id::NONE,
        }
    }
}

impl Default for RepresentativeVariableBindingPathJoiningKeyHashData {
    fn default() -> Self {
        Self::new()
    }
}

/// Port of `CRepresentativeVariableBindingPathJoiningKeyHash`.
#[derive(Debug, Clone)]
pub struct RepresentativeVariableBindingPathJoiningKeyHash {
    /// `CProcessContext* mContext` (opaque).
    pub process_context: Cint64,
    /// `cint64 mNextRepVarBindPathJoiningKeyTag`.
    pub next_rep_var_bind_path_joining_key_tag: Cint64,
    /// `CPROCESSHASH<CRepresentativeVariableBindingPathJoiningKeyHasher,...>`.
    pub map: HashMap<Cint64, Vec<RepresentativeVariableBindingPathJoiningKeyHashData>>,
}

impl RepresentativeVariableBindingPathJoiningKeyHash {
    /// Port of `CRepresentativeVariableBindingPathJoiningKeyHash(CProcessContext*)`.
    pub fn new(process_context: Cint64) -> Self {
        Self {
            process_context,
            next_rep_var_bind_path_joining_key_tag: 1,
            map: HashMap::new(),
        }
    }

    /// Port of `initRepresentativeVariableBindingPathJoiningKeyHash`.
    pub fn init_representative_variable_binding_path_joining_key_hash(
        &mut self,
        prev_hash: Option<&RepresentativeVariableBindingPathJoiningKeyHash>,
    ) -> &mut Self {
        if let Some(prev_hash) = prev_hash {
            self.map = prev_hash.map.clone();
            self.next_rep_var_bind_path_joining_key_tag =
                prev_hash.next_rep_var_bind_path_joining_key_tag;
        } else {
            self.map.clear();
            self.next_rep_var_bind_path_joining_key_tag = 1;
        }
        self
    }

    /// Port of `createVariableBindingHashKeyDescriptor`.
    pub fn create_variable_binding_hash_key_descriptor(
        ctx: &mut ProcessContext,
        var_bind_path: VarBindingPathId,
        key_vars: &[VariableId],
    ) -> VarBindingDescriptorId {
        let mut key_var_bind_des_linker: VarBindingDescriptorId = Id::NONE;
        let mut last_key_var_bind_des_linker: VarBindingDescriptorId = Id::NONE;
        let mut var_linker_it: usize = 0;
        let mut var_bind_des_it = ctx
            .vbpath(var_bind_path)
            .get_variable_binding_descriptor_linker();
        while var_linker_it < key_vars.len() && var_bind_des_it.is_some() {
            let var_bind = ctx.var_binding_des(var_bind_des_it).get_variable_binding();
            if ctx.var_binding(var_bind).get_binded_variable() == key_vars[var_linker_it] {
                let next_key_var_bind_des_linker =
                    ctx.alloc_var_binding_des(VariableBindingDescriptor::new());
                ctx.var_binding_des_mut(next_key_var_bind_des_linker)
                    .init_variable_binding_descriptor(var_bind);
                if last_key_var_bind_des_linker.is_some() {
                    ctx.var_binding_des_mut(last_key_var_bind_des_linker)
                        .set_next(next_key_var_bind_des_linker);
                    last_key_var_bind_des_linker = next_key_var_bind_des_linker;
                } else {
                    key_var_bind_des_linker = next_key_var_bind_des_linker;
                    last_key_var_bind_des_linker = next_key_var_bind_des_linker;
                }
                var_linker_it += 1;
                var_bind_des_it = ctx.var_binding_des(var_bind_des_it).get_next();
            } else {
                var_bind_des_it = ctx.var_binding_des(var_bind_des_it).get_next();
            }
        }
        key_var_bind_des_linker
    }

    fn find_bucket_index(
        ctx: &ProcessContext,
        bucket: &[RepresentativeVariableBindingPathJoiningKeyHashData],
        hasher: &RepresentativeVariableBindingPathJoiningKeyHasher,
    ) -> Option<usize> {
        bucket.iter().position(|data| {
            data.var_bind_path_joining_data.is_some()
                && RepresentativeVariableBindingPathJoiningKeyHasher {
                    joining_data: data.var_bind_path_joining_data,
                    var_bind_path: Id::NONE,
                    key_vars: Vec::new(),
                    hash_value: hasher.hash_value,
                }
                .equals(ctx, hasher)
        })
    }

    /// Port of `getRepresentativeVariableBindingPathJoiningKeyData`.
    pub fn get_representative_variable_binding_path_joining_key_data(
        ctx: &mut ProcessContext,
        this: RepresentativeVariableBindingPathJoiningKeyHashId,
        var_bind_path: VarBindingPathId,
        key_vars: &[VariableId],
        create: bool,
    ) -> RepresentativeVariableBindingPathJoiningKeyDataId {
        let hasher = RepresentativeVariableBindingPathJoiningKeyHasher::new_from_path(
            ctx,
            var_bind_path,
            key_vars,
        );
        let key = hasher.get_hash_value();
        let existing = {
            let hash = ctx.rep_var_bind_path_joining_key_hash(this);
            hash.map
                .get(&key)
                .and_then(|bucket| {
                    Self::find_bucket_index(ctx, bucket, &hasher).map(|idx| bucket[idx])
                })
                .map(|data| data.var_bind_path_joining_data)
                .unwrap_or(Id::NONE)
        };
        if existing.is_some() || !create {
            return existing;
        }

        let joining_key = {
            let hash = ctx.rep_var_bind_path_joining_key_hash(this);
            hash.next_rep_var_bind_path_joining_key_tag
        };
        ctx.rep_var_bind_path_joining_key_hash_mut(this)
            .next_rep_var_bind_path_joining_key_tag += 1;
        let key_var_bind_des_linker =
            Self::create_variable_binding_hash_key_descriptor(ctx, var_bind_path, key_vars);
        let var_bind_path_joining_data = ctx.alloc_rep_var_bind_path_joining_key_data(
            RepresentativeVariableBindingPathJoiningKeyData::new(),
        );
        RepresentativeVariableBindingPathJoiningKeyData::init_variable_binding_path_joining_data(
            ctx,
            var_bind_path_joining_data,
            key_var_bind_des_linker,
            joining_key,
        );
        let stored_hasher =
            RepresentativeVariableBindingPathJoiningKeyHasher::new_from_joining_data(
                ctx,
                var_bind_path_joining_data,
            );
        let stored_key = stored_hasher.get_hash_value();
        ctx.rep_var_bind_path_joining_key_hash_mut(this)
            .map
            .entry(stored_key)
            .or_default()
            .push(RepresentativeVariableBindingPathJoiningKeyHashData {
                var_bind_path_joining_data: var_bind_path_joining_data,
            });
        var_bind_path_joining_data
    }

    /// Port of `getRepresentativeVariableBindingPathJoiningKey`.
    pub fn get_representative_variable_binding_path_joining_key(
        ctx: &mut ProcessContext,
        this: RepresentativeVariableBindingPathJoiningKeyHashId,
        var_bind_path: VarBindingPathId,
        key_vars: &[VariableId],
        create: bool,
    ) -> Cint64 {
        let data = Self::get_representative_variable_binding_path_joining_key_data(
            ctx,
            this,
            var_bind_path,
            key_vars,
            create,
        );
        if data.is_some() {
            ctx.rep_var_bind_path_joining_key_data(data)
                .get_joining_key()
        } else {
            0
        }
    }
}

// ===========================================================================
// CRepresentativeVariableBindingPathSetDataSignature
// (`CRepresentativeVariableBindingPathSetDataSignature.{h,cpp}`)
// ===========================================================================

/// Port of `CRepresentativeVariableBindingPathSetDataSignature`.
///
/// The rolling commutative key signature (sum + product fold) used to key
/// representative sets cheaply; held BY VALUE by both the set data (`mSigKey`) and the
/// propagation set (`mIncomingRepPropSignature`). `Copy` so it can be lifted out of an
/// arena element without a `Clone`.
#[derive(Debug, Clone, Copy)]
pub struct RepresentativeVariableBindingPathSetDataSignature {
    /// `cint64 mIncomingRepPropKey1` (the running sum fold).
    pub incoming_rep_prop_key1: Cint64,
    /// `cint64 mIncomingRepPropKey2` (the running product fold).
    pub incoming_rep_prop_key2: Cint64,
    /// `cint64 mIncomingRepPropKey` (the combined signature value).
    pub incoming_rep_prop_key: Cint64,
}

impl Default for RepresentativeVariableBindingPathSetDataSignature {
    fn default() -> Self {
        Self::new()
    }
}

impl RepresentativeVariableBindingPathSetDataSignature {
    /// Port of `CRepresentativeVariableBindingPathSetDataSignature::…Signature()`.
    ///
    /// The C++ ctor leaves the members uninitialised; we initialise to the
    /// `initSignature(nullptr)` resting state (the only state a fresh signature is ever
    /// read in) so the port has no UB analogue.
    pub fn new() -> Self {
        RepresentativeVariableBindingPathSetDataSignature {
            incoming_rep_prop_key1: 13,
            incoming_rep_prop_key2: 13,
            incoming_rep_prop_key: 0,
        }
    }

    /// Port of `initSignature` (copy from prev, else the `13/13/0` reset).
    pub fn init_signature(
        &mut self,
        prev_signature: Option<&RepresentativeVariableBindingPathSetDataSignature>,
    ) -> &mut Self {
        if let Some(prev) = prev_signature {
            self.incoming_rep_prop_key1 = prev.incoming_rep_prop_key1;
            self.incoming_rep_prop_key2 = prev.incoming_rep_prop_key2;
            self.incoming_rep_prop_key = prev.incoming_rep_prop_key;
        } else {
            self.incoming_rep_prop_key1 = 13;
            self.incoming_rep_prop_key2 = 13;
            self.incoming_rep_prop_key = 0;
        }
        self
    }

    /// Port of `addKey` (`key1 += k; key2 *= k; key = key1 + key2*17`).
    ///
    /// `wrapping_*` matches C++ `cint64` two's-complement overflow semantics (the fold
    /// is a hash, not an arithmetic count).
    pub fn add_key(&mut self, key: Cint64) -> &mut Self {
        self.incoming_rep_prop_key1 = self.incoming_rep_prop_key1.wrapping_add(key);
        self.incoming_rep_prop_key2 = self.incoming_rep_prop_key2.wrapping_mul(key);
        self.incoming_rep_prop_key = self
            .incoming_rep_prop_key1
            .wrapping_add(self.incoming_rep_prop_key2.wrapping_mul(17));
        self
    }

    /// Port of `getSignatureValue`.
    pub fn get_signature_value(&self) -> Cint64 {
        self.incoming_rep_prop_key
    }
}

// ===========================================================================
// CRepresentativeContainingMapData
// (`CRepresentativeContainingMapData.{h,cpp}`)
// ===========================================================================

/// Port of `CRepresentativeContainingMapData`.
///
/// The per-repID value of the containing map: a contained representative + whether it
/// is explicitly contained.
#[derive(Debug, Clone, Copy)]
pub struct RepresentativeContainingMapData {
    /// `CRepresentativeVariableBindingPathSetData* mContainedRep`.
    pub contained_rep: RepresentativeVariableBindingPathSetDataId,
    /// `bool mExplicitelyContained`.
    pub explicitely_contained: bool,
}

impl Default for RepresentativeContainingMapData {
    fn default() -> Self {
        RepresentativeContainingMapData::new(Id::NONE, false)
    }
}

impl RepresentativeContainingMapData {
    /// Port of `CRepresentativeContainingMapData(containedRep = nullptr, explContained = false)`.
    pub fn new(
        contained_rep: RepresentativeVariableBindingPathSetDataId,
        expl_contained: bool,
    ) -> Self {
        RepresentativeContainingMapData {
            contained_rep,
            explicitely_contained: expl_contained,
        }
    }

    /// Port of `getRepresentativeVariableBindingPathSetData`.
    pub fn get_representative_variable_binding_path_set_data(
        &self,
    ) -> RepresentativeVariableBindingPathSetDataId {
        self.contained_rep
    }
    /// Port of `hasRepresentativeVariableBindingPathSetData`.
    pub fn has_representative_variable_binding_path_set_data(&self) -> bool {
        self.contained_rep.is_some()
    }
    /// Port of `setRepresentativeVariableBindingPathSetData`.
    pub fn set_representative_variable_binding_path_set_data(
        &mut self,
        contained_rep: RepresentativeVariableBindingPathSetDataId,
    ) -> &mut Self {
        self.contained_rep = contained_rep;
        self
    }

    /// Port of `isExplicitelyContained`.
    pub fn is_explicitely_contained(&self) -> bool {
        self.explicitely_contained
    }
    /// Port of `setExplicitelyContained`.
    pub fn set_explicitely_contained(&mut self, expl_contained: bool) -> &mut Self {
        self.explicitely_contained = expl_contained;
        self
    }
}

// ===========================================================================
// CRepresentativeContainingMap
// (`CRepresentativeContainingMap.{h,cpp}`,
//  `: public CPROCESSMAP<cint64,CRepresentativeContainingMapData>`)
// ===========================================================================

/// Port of `CRepresentativeContainingMap`.
///
/// KONCLUDE-PORT-NOTE[ownership]: held BY VALUE by the migrate data, so it is not an
/// arena element; `mProcessContext` stays an opaque `Cint64` (the
/// `varbind::RepresentativeVariableBindingPathMap` precedent).
#[derive(Clone)]
pub struct RepresentativeContainingMap {
    /// `CProcessContext* mProcessContext` (opaque handle).
    pub process_context: Cint64,
    /// the `CPROCESSMAP<cint64,…MapData>` base storage (key = repID).
    pub map: HashMap<Cint64, RepresentativeContainingMapData>,
}

impl RepresentativeContainingMap {
    /// Port of `CRepresentativeContainingMap::CRepresentativeContainingMap(CProcessContext*)`.
    pub fn new(process_context: Cint64) -> Self {
        RepresentativeContainingMap {
            process_context,
            map: HashMap::new(),
        }
    }

    /// Port of `initRepresentativeContainingMap` (operator= from prev, else clear).
    pub fn init_representative_containing_map(
        &mut self,
        prev_map: Option<&RepresentativeContainingMap>,
    ) -> &mut Self {
        if let Some(prev) = prev_map {
            self.map = prev.map.clone();
        } else {
            self.map.clear();
        }
        self
    }

    /// Port of `insertContainedRepresentative(CRepresentativeVariableBindingPathSetData*, bool)`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: the C++ derives the key from
    /// `repData->getRepresentativeID()`; since the map is held BY VALUE (not in an
    /// arena) the caller reads `rep_id = ctx.rep_var_bind_path_set_data(rep_data)
    /// .get_representative_id()` first and passes it in, so this stays ctx-free (the
    /// receiver and `rep_data` would otherwise be two arena borrows).
    pub fn insert_contained_representative(
        &mut self,
        rep_id: Cint64,
        rep_data: RepresentativeVariableBindingPathSetDataId,
        explicitely_contained: bool,
    ) -> &mut Self {
        self.map.insert(
            rep_id,
            RepresentativeContainingMapData::new(rep_data, explicitely_contained),
        );
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
    pub fn value(&self, key: Cint64) -> RepresentativeContainingMapData {
        self.map.get(&key).copied().unwrap_or_default()
    }
    /// Port of `CPROCESSMAP::operator[]`.
    pub fn entry_mut(&mut self, key: Cint64) -> &mut RepresentativeContainingMapData {
        self.map.entry(key).or_default()
    }
}

// ===========================================================================
// CConceptRepresentativePropagationSetHash{Data}
// (`CConceptRepresentativePropagationSetHash{Data}.{h,cpp}`,
//  `: public CPROCESSHASH<cint64,CConceptRepresentativePropagationSetHashData>`)
// ===========================================================================

/// Port of `CConceptRepresentativePropagationSetHashData`.
#[derive(Debug, Clone, Copy)]
pub struct ConceptRepresentativePropagationSetHashData {
    /// `CRepresentativePropagationSet* mLocRepPropSet`.
    pub loc_rep_prop_set: RepresentativePropagationSetId,
    /// `CRepresentativePropagationSet* mUseRepPropSet`.
    pub use_rep_prop_set: RepresentativePropagationSetId,
}

impl ConceptRepresentativePropagationSetHashData {
    /// Port of the default constructor.
    pub fn new() -> Self {
        ConceptRepresentativePropagationSetHashData {
            loc_rep_prop_set: Id::NONE,
            use_rep_prop_set: Id::NONE,
        }
    }

    /// Port of the copy constructor: local pointer is nulled, use pointer is shared.
    pub fn copy_from(data: &ConceptRepresentativePropagationSetHashData) -> Self {
        ConceptRepresentativePropagationSetHashData {
            loc_rep_prop_set: Id::NONE,
            use_rep_prop_set: data.use_rep_prop_set,
        }
    }
}

impl Default for ConceptRepresentativePropagationSetHashData {
    fn default() -> Self {
        Self::new()
    }
}

/// Port of `CConceptRepresentativePropagationSetHash`.
pub struct ConceptRepresentativePropagationSetHash {
    /// `CProcessContext* mProcessContext` (opaque).
    pub process_context: Cint64,
    /// `CPROCESSHASH<cint64,CConceptRepresentativePropagationSetHashData>` storage.
    pub map: HashMap<Cint64, ConceptRepresentativePropagationSetHashData>,
}

impl ConceptRepresentativePropagationSetHash {
    /// Port of `CConceptRepresentativePropagationSetHash(CProcessContext*)`.
    pub fn new(process_context: Cint64) -> Self {
        ConceptRepresentativePropagationSetHash {
            process_context,
            map: HashMap::new(),
        }
    }

    /// Port of `initConceptRepresentativePropagationSetHash`.
    pub fn init_concept_representative_propagation_set_hash(
        &mut self,
        prev_hash: Option<&ConceptRepresentativePropagationSetHash>,
    ) -> &mut Self {
        if let Some(prev_hash) = prev_hash {
            self.map = prev_hash
                .map
                .iter()
                .map(|(key, data)| {
                    (
                        *key,
                        ConceptRepresentativePropagationSetHashData::copy_from(data),
                    )
                })
                .collect();
        } else {
            self.map.clear();
        }
        self
    }

    /// Port of `getRepresentativePropagationSet(CConcept* concept, bool localize)`.
    pub fn get_representative_propagation_set(
        ctx: &mut ProcessContext,
        this: ConceptRepresentativePropagationSetHashId,
        concept: ConceptId,
        localize: bool,
    ) -> RepresentativePropagationSetId {
        let con_tag = concept.raw;
        if localize {
            let (loc, use_) = {
                let hash = ctx.con_rep_prop_set_hash_mut(this);
                let data = hash
                    .map
                    .entry(con_tag)
                    .or_insert_with(ConceptRepresentativePropagationSetHashData::new);
                (data.loc_rep_prop_set, data.use_rep_prop_set)
            };
            if loc.is_none() {
                let new_set = ctx.alloc_rep_prop_set(RepresentativePropagationSet::new(INVALID));
                if use_.is_some() {
                    let taken = std::mem::replace(
                        ctx.rep_prop_set_mut(use_),
                        RepresentativePropagationSet::new(INVALID),
                    );
                    ctx.rep_prop_set_mut(new_set)
                        .init_representative_propagation_set(Some(&taken));
                    *ctx.rep_prop_set_mut(use_) = taken;
                } else {
                    ctx.rep_prop_set_mut(new_set)
                        .init_representative_propagation_set(None);
                }
                let data = ctx
                    .con_rep_prop_set_hash_mut(this)
                    .map
                    .get_mut(&con_tag)
                    .unwrap();
                data.use_rep_prop_set = new_set;
                data.loc_rep_prop_set = new_set;
                new_set
            } else {
                use_
            }
        } else {
            ctx.con_rep_prop_set_hash(this)
                .map
                .get(&con_tag)
                .map(|data| data.use_rep_prop_set)
                .unwrap_or(RepresentativePropagationSetId::NONE)
        }
    }
}

// ===========================================================================
// CRepresentativeVariableBindingPathSetHash{Data}
// (`CRepresentativeVariableBindingPathSetHash{Data}.{h,cpp}`,
//  `: public CPROCESSHASH<cint64,CRepresentativeVariableBindingPathSetHashData>`)
// ===========================================================================

/// Port of `CRepresentativeVariableBindingPathSetHashData`.
#[derive(Debug, Clone, Copy)]
pub struct RepresentativeVariableBindingPathSetHashData {
    /// `CRepresentativeVariableBindingPathSetData* mUseDataLinker`.
    pub use_data_linker: RepresentativeVariableBindingPathSetDataId,
    /// `CRepresentativeVariableBindingPathSetData* mLocDataLinker`.
    pub loc_data_linker: RepresentativeVariableBindingPathSetDataId,
}

impl RepresentativeVariableBindingPathSetHashData {
    /// Port of the default constructor.
    pub fn new() -> Self {
        RepresentativeVariableBindingPathSetHashData {
            use_data_linker: Id::NONE,
            loc_data_linker: Id::NONE,
        }
    }

    /// Port of the copy constructor: shared use chain copied, local chain reset.
    pub fn copy_from(data: &RepresentativeVariableBindingPathSetHashData) -> Self {
        RepresentativeVariableBindingPathSetHashData {
            use_data_linker: data.use_data_linker,
            loc_data_linker: Id::NONE,
        }
    }
}

impl Default for RepresentativeVariableBindingPathSetHashData {
    fn default() -> Self {
        Self::new()
    }
}

/// Port of `CRepresentativeVariableBindingPathSetHash`.
pub struct RepresentativeVariableBindingPathSetHash {
    /// `CProcessContext* mProcessContext` (opaque).
    pub process_context: Cint64,
    /// `CPROCESSHASH<cint64,CRepresentativeVariableBindingPathSetHashData>` storage.
    pub map: HashMap<Cint64, RepresentativeVariableBindingPathSetHashData>,
}

impl RepresentativeVariableBindingPathSetHash {
    /// Port of `CRepresentativeVariableBindingPathSetHash(CProcessContext*)`.
    pub fn new(process_context: Cint64) -> Self {
        RepresentativeVariableBindingPathSetHash {
            process_context,
            map: HashMap::new(),
        }
    }

    /// Port of `initRepresentativeVariableBindingPathSetHash`.
    pub fn init_representative_variable_binding_path_set_hash(
        &mut self,
        prev_hash: Option<&RepresentativeVariableBindingPathSetHash>,
    ) -> &mut Self {
        if let Some(prev_hash) = prev_hash {
            self.map = prev_hash
                .map
                .iter()
                .map(|(key, data)| {
                    (
                        *key,
                        RepresentativeVariableBindingPathSetHashData::copy_from(data),
                    )
                })
                .collect();
        } else {
            self.map.clear();
        }
        self
    }

    /// Port of `insertRepresentativeVariableBindingPathSetData`.
    pub fn insert_representative_variable_binding_path_set_data(
        ctx: &mut ProcessContext,
        this: RepresentativeVariableBindingPathSetHashId,
        rep_set_data: RepresentativeVariableBindingPathSetDataId,
    ) -> RepresentativeVariableBindingPathSetHashId {
        let key = ctx
            .rep_var_bind_path_set_data(rep_set_data)
            .get_representative_key();
        let old_head = {
            let hash = ctx.rep_var_bind_path_set_hash_mut(this);
            hash.map
                .entry(key)
                .or_insert_with(RepresentativeVariableBindingPathSetHashData::new)
                .use_data_linker
        };
        let new_head =
            RepresentativeVariableBindingPathSetData::append(ctx, rep_set_data, old_head);
        let data = ctx
            .rep_var_bind_path_set_hash_mut(this)
            .map
            .entry(key)
            .or_insert_with(RepresentativeVariableBindingPathSetHashData::new);
        data.loc_data_linker = new_head;
        data.use_data_linker = new_head;
        this
    }

    /// Port of `getRepresentativeVariableBindingPathSetData(repSetData, createOrLocalize)`.
    pub fn get_representative_variable_binding_path_set_data_for_data(
        ctx: &mut ProcessContext,
        this: RepresentativeVariableBindingPathSetHashId,
        rep_set_data: RepresentativeVariableBindingPathSetDataId,
        create_or_localize: bool,
    ) -> RepresentativeVariableBindingPathSetDataId {
        let (key, rep_id) = {
            let data = ctx.rep_var_bind_path_set_data(rep_set_data);
            (data.get_representative_key(), data.get_representative_id())
        };
        if create_or_localize {
            let use_head = {
                let hash = ctx.rep_var_bind_path_set_hash_mut(this);
                hash.map
                    .entry(key)
                    .or_insert_with(RepresentativeVariableBindingPathSetHashData::new)
                    .use_data_linker
            };
            let mut found = Id::NONE;
            let mut it = use_head;
            while it.is_some() && found.is_none() {
                if ctx.rep_var_bind_path_set_data(it).get_representative_id() == rep_id {
                    found = it;
                }
                it = ctx.rep_var_bind_path_set_data(it).get_next();
            }
            if found.is_some() {
                return Self::localize_data_linker_prefix(ctx, this, key, use_head, found);
            }

            Self::create_fresh_data_linker(ctx, this, key, use_head)
        } else {
            let use_head = ctx
                .rep_var_bind_path_set_hash(this)
                .map
                .get(&key)
                .map(|data| data.use_data_linker)
                .unwrap_or(Id::NONE);
            let mut it = use_head;
            while it.is_some() {
                if ctx.rep_var_bind_path_set_data(it).get_representative_id() == rep_id {
                    return it;
                }
                it = ctx.rep_var_bind_path_set_data(it).get_next();
            }
            Id::NONE
        }
    }

    /// Port of `getRepresentativeVariableBindingPathSetData(repPropSet, createOrLocalize)`.
    pub fn get_representative_variable_binding_path_set_data_for_propagation_set(
        ctx: &mut ProcessContext,
        this: RepresentativeVariableBindingPathSetHashId,
        rep_prop_set: RepresentativePropagationSetId,
        create_or_localize: bool,
    ) -> RepresentativeVariableBindingPathSetDataId {
        let key = ctx
            .rep_prop_set(rep_prop_set)
            .get_incoming_representative_propagation_signature_key();
        if create_or_localize {
            let use_head = {
                let hash = ctx.rep_var_bind_path_set_hash_mut(this);
                hash.map
                    .entry(key)
                    .or_insert_with(RepresentativeVariableBindingPathSetHashData::new)
                    .use_data_linker
            };
            let mut selected = Id::NONE;
            let mut found = Id::NONE;
            let mut it = use_head;
            while it.is_some() && found.is_none() {
                if !ctx.rep_var_bind_path_set_data(it).has_migrate_data() {
                    if selected.is_none() {
                        selected = it;
                    }
                } else {
                    let migrate_data =
                        RepresentativeVariableBindingPathSetData::get_migrate_data(ctx, it, false);
                    let identical = {
                        let rep_cont_map = ctx
                            .rep_var_bind_path_set_migrate_data(migrate_data)
                            .get_representative_containing_map();
                        let rep_prop_map = ctx
                            .rep_prop_set(rep_prop_set)
                            .get_representative_propagation_map();
                        Self::is_representative_propagation_map_identical_to_representative_containing_map(
                            rep_prop_map,
                            rep_cont_map,
                        )
                    };
                    if identical {
                        found = it;
                    }
                }
                it = ctx.rep_var_bind_path_set_data(it).get_next();
            }

            let inc_loc_data_linker = if found.is_some() { found } else { selected };
            if inc_loc_data_linker.is_some() {
                return Self::localize_data_linker_prefix(
                    ctx,
                    this,
                    key,
                    use_head,
                    inc_loc_data_linker,
                );
            }

            Self::create_fresh_data_linker(ctx, this, key, use_head)
        } else {
            let use_head = ctx
                .rep_var_bind_path_set_hash(this)
                .map
                .get(&key)
                .map(|data| data.use_data_linker)
                .unwrap_or(Id::NONE);
            let mut it = use_head;
            while it.is_some() {
                if ctx.rep_var_bind_path_set_data(it).has_migrate_data() {
                    let migrate_data =
                        RepresentativeVariableBindingPathSetData::get_migrate_data(ctx, it, false);
                    let identical = {
                        let rep_cont_map = ctx
                            .rep_var_bind_path_set_migrate_data(migrate_data)
                            .get_representative_containing_map();
                        let rep_prop_map = ctx
                            .rep_prop_set(rep_prop_set)
                            .get_representative_propagation_map();
                        Self::is_representative_propagation_map_identical_to_representative_containing_map(
                            rep_prop_map,
                            rep_cont_map,
                        )
                    };
                    if identical {
                        return it;
                    }
                }
                it = ctx.rep_var_bind_path_set_data(it).get_next();
            }
            Id::NONE
        }
    }

    /// Port of `isRepresentativePropagationMapIdenticalToRepresentativeContainingMap`.
    pub fn is_representative_propagation_map_identical_to_representative_containing_map(
        rep_prop_map: &RepresentativePropagationMap,
        rep_cont_map: &RepresentativeContainingMap,
    ) -> bool {
        if rep_prop_map.count() != rep_cont_map.count() {
            return false;
        }
        let mut prop_keys: Vec<Cint64> = rep_prop_map.map.keys().copied().collect();
        let mut cont_keys: Vec<Cint64> = rep_cont_map.map.keys().copied().collect();
        prop_keys.sort_unstable();
        cont_keys.sort_unstable();
        prop_keys == cont_keys
    }

    fn create_fresh_data_linker(
        ctx: &mut ProcessContext,
        this: RepresentativeVariableBindingPathSetHashId,
        key: Cint64,
        use_head: RepresentativeVariableBindingPathSetDataId,
    ) -> RepresentativeVariableBindingPathSetDataId {
        let localization_tag = ctx.used_process_tagger().get_current_localization_tag();
        let loc_linker = ctx.alloc_rep_var_bind_path_set_data(
            RepresentativeVariableBindingPathSetData::new(INVALID, localization_tag),
        );
        ctx.rep_var_bind_path_set_data_mut(loc_linker)
            .init_representative_variable_binding_path_data(None)
            .set_next(use_head);
        let data = ctx
            .rep_var_bind_path_set_hash_mut(this)
            .map
            .entry(key)
            .or_insert_with(RepresentativeVariableBindingPathSetHashData::new);
        data.loc_data_linker = loc_linker;
        data.use_data_linker = loc_linker;
        loc_linker
    }

    fn localize_data_linker_prefix(
        ctx: &mut ProcessContext,
        this: RepresentativeVariableBindingPathSetHashId,
        key: Cint64,
        use_head: RepresentativeVariableBindingPathSetDataId,
        inc_loc_data_linker: RepresentativeVariableBindingPathSetDataId,
    ) -> RepresentativeVariableBindingPathSetDataId {
        let next_inc_loc_data_linker = ctx
            .rep_var_bind_path_set_data(inc_loc_data_linker)
            .get_next();
        let localization_tag = ctx.used_process_tagger().get_current_localization_tag();
        let mut return_data_linker = Id::NONE;
        let mut new_loc_data_linker = Id::NONE;
        let mut last_new_loc_data_linker = Id::NONE;
        let mut data_linker_it = use_head;
        while data_linker_it != next_inc_loc_data_linker {
            let mut loc_linker = data_linker_it;
            if !ctx
                .rep_var_bind_path_set_data(data_linker_it)
                .is_localization_tag_up_to_date(localization_tag)
            {
                let copied = std::mem::replace(
                    ctx.rep_var_bind_path_set_data_mut(data_linker_it),
                    RepresentativeVariableBindingPathSetData::new(INVALID, localization_tag),
                );
                loc_linker = ctx.alloc_rep_var_bind_path_set_data(
                    RepresentativeVariableBindingPathSetData::new(INVALID, localization_tag),
                );
                ctx.rep_var_bind_path_set_data_mut(loc_linker)
                    .init_representative_variable_binding_path_data(Some(&copied));
                *ctx.rep_var_bind_path_set_data_mut(data_linker_it) = copied;
            }
            if data_linker_it == inc_loc_data_linker {
                return_data_linker = loc_linker;
            }
            if last_new_loc_data_linker.is_some() {
                ctx.rep_var_bind_path_set_data_mut(last_new_loc_data_linker)
                    .set_next(loc_linker);
                last_new_loc_data_linker = loc_linker;
            } else {
                last_new_loc_data_linker = loc_linker;
                new_loc_data_linker = loc_linker;
            }
            data_linker_it = ctx.rep_var_bind_path_set_data(data_linker_it).get_next();
        }

        let data = ctx
            .rep_var_bind_path_set_hash_mut(this)
            .map
            .entry(key)
            .or_insert_with(RepresentativeVariableBindingPathSetHashData::new);
        data.loc_data_linker = new_loc_data_linker;
        data.use_data_linker = new_loc_data_linker;
        return_data_linker
    }
}

// ===========================================================================
// CRepresentativeVariableBindingPathHash
// (`CRepresentativeVariableBindingPathHash.{h,cpp}`,
//  `: public CPROCESSHASH<cint64,CRepresentativeVariableBindingPathSetHashData>`)
// ===========================================================================

/// Port of `CRepresentativeVariableBindingPathHash`.
pub struct RepresentativeVariableBindingPathHash {
    /// `CProcessContext* mProcessContext` (opaque).
    pub process_context: Cint64,
    /// `CPROCESSHASH<cint64,CRepresentativeVariableBindingPathSetHashData>` storage.
    pub map: HashMap<Cint64, RepresentativeVariableBindingPathSetHashData>,
}

impl RepresentativeVariableBindingPathHash {
    /// Port of `CRepresentativeVariableBindingPathHash(CProcessContext*)`.
    pub fn new(process_context: Cint64) -> Self {
        Self {
            process_context,
            map: HashMap::new(),
        }
    }

    /// Port of `initRepresentativeVariableBindingPathHash`.
    pub fn init_representative_variable_binding_path_hash(
        &mut self,
        prev_hash: Option<&RepresentativeVariableBindingPathHash>,
    ) -> &mut Self {
        if let Some(prev_hash) = prev_hash {
            self.map = prev_hash
                .map
                .iter()
                .map(|(key, data)| {
                    (
                        *key,
                        RepresentativeVariableBindingPathSetHashData::copy_from(data),
                    )
                })
                .collect();
        } else {
            self.map.clear();
        }
        self
    }

    /// Port of `getRepresentativeVariableBindingPathSetData(CVariableBindingPath*, bool)`.
    pub fn get_representative_variable_binding_path_set_data(
        ctx: &mut ProcessContext,
        this: RepresentativeVariableBindingPathHashId,
        var_bind_path: VarBindingPathId,
        create_or_localize: bool,
    ) -> RepresentativeVariableBindingPathSetDataId {
        let key = ctx.vbpath(var_bind_path).get_propagation_id();
        if create_or_localize {
            let existing = {
                let hash = ctx.rep_var_bind_path_hash_mut(this);
                let data = hash
                    .map
                    .entry(key)
                    .or_insert_with(RepresentativeVariableBindingPathSetHashData::new);
                data.use_data_linker
            };
            let loc_existing = ctx
                .rep_var_bind_path_hash(this)
                .map
                .get(&key)
                .copied()
                .unwrap_or_default()
                .loc_data_linker;
            if loc_existing.is_some() {
                return existing;
            }

            let localization_tag = ctx.used_process_tagger().get_current_localization_tag();
            let rep_data = ctx.alloc_rep_var_bind_path_set_data(
                RepresentativeVariableBindingPathSetData::new(INVALID, localization_tag),
            );
            ctx.rep_var_bind_path_set_data_mut(rep_data)
                .init_representative_variable_binding_path_data(None);
            let data = ctx
                .rep_var_bind_path_hash_mut(this)
                .map
                .entry(key)
                .or_insert_with(RepresentativeVariableBindingPathSetHashData::new);
            data.loc_data_linker = rep_data;
            data.use_data_linker = rep_data;
            rep_data
        } else {
            ctx.rep_var_bind_path_hash(this)
                .map
                .get(&key)
                .copied()
                .unwrap_or_default()
                .use_data_linker
        }
    }
}

// ===========================================================================
// CRepresentativeVariableBindingPathSetMigrateData
// (`CRepresentativeVariableBindingPathSetMigrateData.{h,cpp}`)
// ===========================================================================

/// Port of `CRepresentativeVariableBindingPathSetMigrateData`.
///
/// The localised payload of a representative set: the resolve map (`varbind`'s already
/// ported `CRepresentativeVariableBindingPathMap`) + the containing map, both held BY
/// VALUE. Lazily created + copy-on-write localised by
/// [`RepresentativeVariableBindingPathSetData::get_migrate_data`].
#[derive(Clone)]
pub struct RepresentativeVariableBindingPathSetMigrateData {
    /// `CProcessContext* mProcessContext` (opaque).
    pub process_context: Cint64,
    /// `CRepresentativeContainingMap mRepContainingMap` (by value).
    pub rep_containing_map: RepresentativeContainingMap,
    /// `CRepresentativeVariableBindingPathMap mVarBindPathMap` (by value, `varbind`).
    pub var_bind_path_map: RepresentativeVariableBindingPathMap,
}

impl RepresentativeVariableBindingPathSetMigrateData {
    /// Port of `CRepresentativeVariableBindingPathSetMigrateData(CProcessContext*)`
    /// (`: mProcessContext(context), mVarBindPathMap(context), mRepContainingMap(context)`).
    pub fn new(process_context: Cint64) -> Self {
        RepresentativeVariableBindingPathSetMigrateData {
            process_context,
            rep_containing_map: RepresentativeContainingMap::new(process_context),
            var_bind_path_map: RepresentativeVariableBindingPathMap::new(process_context),
        }
    }

    /// Port of `initRepresentativeVariableBindingPathSetMigrateData`
    /// (operator= from prev's two maps, else clear both).
    pub fn init_representative_variable_binding_path_set_migrate_data(
        &mut self,
        data: Option<&RepresentativeVariableBindingPathSetMigrateData>,
    ) -> &mut Self {
        if let Some(d) = data {
            self.var_bind_path_map = d.var_bind_path_map.clone();
            self.rep_containing_map = d.rep_containing_map.clone();
        } else {
            self.var_bind_path_map.init_variable_binding_path_map(None);
            self.rep_containing_map
                .init_representative_containing_map(None);
        }
        self
    }

    /// Port of `getRepresentativeVariableBindingPathMap`.
    pub fn get_representative_variable_binding_path_map(
        &self,
    ) -> &RepresentativeVariableBindingPathMap {
        &self.var_bind_path_map
    }
    /// Mutable companion.
    pub fn get_representative_variable_binding_path_map_mut(
        &mut self,
    ) -> &mut RepresentativeVariableBindingPathMap {
        &mut self.var_bind_path_map
    }

    /// Port of `getRepresentativeContainingMap`.
    pub fn get_representative_containing_map(&self) -> &RepresentativeContainingMap {
        &self.rep_containing_map
    }
    /// Mutable companion.
    pub fn get_representative_containing_map_mut(&mut self) -> &mut RepresentativeContainingMap {
        &mut self.rep_containing_map
    }
}

// ===========================================================================
// CRepresentativeVariableBindingPathSetData
// (`CRepresentativeVariableBindingPathSetData.{h,cpp}`,
//  `: public CLinkerBase<cint64,Self>, public CLocalizationTag`)
// ===========================================================================

/// Port of `CRepresentativeVariableBindingPathSetData`.
///
/// KONCLUDE-PORT-NOTE[ownership]: the `CLinkerBase<cint64,Self>` base carries the
/// representative ID AS its `data` (`getRepresentativeID() == getData()`); it is folded
/// to `data: Cint64` (the rep id) + `next: …Id` (the list linker). The `CLocalizationTag`
/// base → `localization_tag: Cint64`. The two migrate-data pointers become arena ids; the
/// two joining-hash pointers are W3.5r-DEFER marker ids (the hash is an unported own
/// unit). `mSigKey` is held BY VALUE.
pub struct RepresentativeVariableBindingPathSetData {
    /// `CLinkerBase::data` (the representative ID — `getData()`/`setData()`).
    pub data: Cint64,
    /// `CLinkerBase::next` (the representative list linker).
    pub next: RepresentativeVariableBindingPathSetDataId,
    /// `CLocalizationTag::mLocalizationTag`.
    pub localization_tag: Cint64,
    /// `CProcessContext* mProcessContext` (opaque).
    pub process_context: Cint64,
    /// `bool mMigratable`.
    pub migratable: bool,
    /// `cint64 mUseCount`.
    pub use_count: Cint64,
    /// `cint64 mShareCount`.
    pub share_count: Cint64,
    /// `CRepresentativeVariableBindingPathSetDataSignature mSigKey` (by value).
    pub sig_key: RepresentativeVariableBindingPathSetDataSignature,
    /// `CRepresentativeVariableBindingPathSetMigrateData* mLocMigrateData`.
    pub loc_migrate_data: RepresentativeVariableBindingPathSetMigrateDataId,
    /// `CRepresentativeVariableBindingPathSetMigrateData* mUseMigrateData`.
    pub use_migrate_data: RepresentativeVariableBindingPathSetMigrateDataId,
    /// `CRepresentativeVariableBindingPathSetJoiningHash* mUseJoiningHash`.
    pub use_joining_hash: RepresentativeVariableBindingPathSetJoiningHashId,
    /// `CRepresentativeVariableBindingPathSetJoiningHash* mLocJoiningHash`.
    pub loc_joining_hash: RepresentativeVariableBindingPathSetJoiningHashId,
}

impl RepresentativeVariableBindingPathSetData {
    /// Port of `CRepresentativeVariableBindingPathSetData(CProcessContext*)`
    /// (`CLinkerBase(0)`, `CLocalizationTag(tagger->getCurrentLocalizationTag())`).
    ///
    /// The caller supplies the localization tag (the allocator has `ctx`):
    /// `ctx.used_process_tagger().get_current_localization_tag()`.
    pub fn new(process_context: Cint64, localization_tag: Cint64) -> Self {
        RepresentativeVariableBindingPathSetData {
            data: 0,
            next: Id::NONE,
            localization_tag,
            process_context,
            migratable: true,
            use_count: 0,
            share_count: 0,
            sig_key: RepresentativeVariableBindingPathSetDataSignature::new(),
            loc_migrate_data: Id::NONE,
            use_migrate_data: Id::NONE,
            use_joining_hash: Id::NONE,
            loc_joining_hash: Id::NONE,
        }
    }

    /// Port of `initRepresentativeVariableBindingPathData(data)`.
    ///
    /// With `data`: inherits `getData()` (the rep id), the counts, migratable, the shared
    /// `mUseMigrateData`/`mUseJoiningHash`, and the signature; nulls the `mLoc…`. Without:
    /// resets to a fresh representative (`data = 0`, migratable, counts 0, everything null).
    pub fn init_representative_variable_binding_path_data(
        &mut self,
        data: Option<&RepresentativeVariableBindingPathSetData>,
    ) -> &mut Self {
        if let Some(d) = data {
            self.data = d.data;
            self.migratable = d.migratable;
            self.use_count = d.use_count;
            self.share_count = d.share_count;
            self.use_migrate_data = d.use_migrate_data;
            self.sig_key.init_signature(Some(&d.sig_key));
            self.use_joining_hash = d.use_joining_hash;
            self.loc_migrate_data = Id::NONE;
            self.loc_joining_hash = Id::NONE;
        } else {
            self.data = 0;
            self.migratable = true;
            self.use_migrate_data = Id::NONE;
            self.loc_migrate_data = Id::NONE;
            self.use_joining_hash = Id::NONE;
            self.loc_joining_hash = Id::NONE;
            self.sig_key.init_signature(None);
            self.use_count = 0;
            self.share_count = 0;
        }
        self
    }

    /// Port of `getRepresentativeKey` (`mSigKey.getSignatureValue()`).
    pub fn get_representative_key(&self) -> Cint64 {
        self.sig_key.get_signature_value()
    }

    /// Port of `getRepresentativeID` (`getData()`).
    pub fn get_representative_id(&self) -> Cint64 {
        self.data
    }
    /// Port of `setRepresentativeID` (`setData(repID)`).
    pub fn set_representative_id(&mut self, rep_id: Cint64) -> &mut Self {
        self.data = rep_id;
        self
    }

    /// Port of `CLocalizationTag::isLocalizationTagUpToDate`.
    pub fn is_localization_tag_up_to_date(&self, localization_tag: Cint64) -> bool {
        self.localization_tag >= localization_tag
    }

    /// Port of `getUseCount`.
    pub fn get_use_count(&self) -> Cint64 {
        self.use_count
    }
    /// Port of `setUseCount`.
    pub fn set_use_count(&mut self, use_count: Cint64) -> &mut Self {
        self.use_count = use_count;
        self
    }
    /// Port of `incUseCount(incCount = 1)`.
    pub fn inc_use_count(&mut self, inc_count: Cint64) -> &mut Self {
        self.use_count += inc_count;
        self
    }

    /// Port of `getShareCount`.
    pub fn get_share_count(&self) -> Cint64 {
        self.share_count
    }
    /// Port of `setShareCount`.
    pub fn set_share_count(&mut self, share_count: Cint64) -> &mut Self {
        self.share_count = share_count;
        self
    }
    /// Port of `incShareCount(incCount = 1)`.
    pub fn inc_share_count(&mut self, inc_count: Cint64) -> &mut Self {
        self.share_count += inc_count;
        self
    }
    /// Port of `decShareCount(decCount = 1)`.
    pub fn dec_share_count(&mut self, dec_count: Cint64) -> &mut Self {
        self.share_count -= dec_count;
        self
    }

    /// Port of `isMigratable`.
    pub fn is_migratable(&self) -> bool {
        self.migratable
    }
    /// Port of `setMigratable`.
    pub fn set_migratable(&mut self, migratable: bool) -> &mut Self {
        self.migratable = migratable;
        self
    }

    /// Port of `hasMigrateData` (`mUseMigrateData != nullptr`).
    pub fn has_migrate_data(&self) -> bool {
        self.use_migrate_data.is_some()
    }

    /// Port of `addKeySignatureValue(keySignatureValue)` (`mSigKey.addKey(…)`).
    pub fn add_key_signature_value(&mut self, key_signature_value: Cint64) -> &mut Self {
        self.sig_key.add_key(key_signature_value);
        self
    }
    /// Port of `getKeySignature` (`&mSigKey`).
    pub fn get_key_signature(&self) -> &RepresentativeVariableBindingPathSetDataSignature {
        &self.sig_key
    }

    /// Port of `getJoiningHash(create)`.
    pub fn get_joining_hash(
        ctx: &mut ProcessContext,
        this: RepresentativeVariableBindingPathSetDataId,
        create: bool,
    ) -> RepresentativeVariableBindingPathSetJoiningHashId {
        let (loc, use_, process_context) = {
            let data = ctx.rep_var_bind_path_set_data(this);
            (
                data.loc_joining_hash,
                data.use_joining_hash,
                data.process_context,
            )
        };
        if create && loc.is_none() {
            let new_hash = ctx.alloc_rep_var_bind_path_set_joining_hash(
                RepresentativeVariableBindingPathSetJoiningHash::new(process_context),
            );
            if use_.is_some() {
                let taken = std::mem::replace(
                    ctx.rep_var_bind_path_set_joining_hash_mut(use_),
                    RepresentativeVariableBindingPathSetJoiningHash::new(process_context),
                );
                ctx.rep_var_bind_path_set_joining_hash_mut(new_hash)
                    .init_representative_variable_binding_path_set_joining_hash(Some(&taken));
                *ctx.rep_var_bind_path_set_joining_hash_mut(use_) = taken;
            } else {
                ctx.rep_var_bind_path_set_joining_hash_mut(new_hash)
                    .init_representative_variable_binding_path_set_joining_hash(None);
            }
            let data = ctx.rep_var_bind_path_set_data_mut(this);
            data.loc_joining_hash = new_hash;
            data.use_joining_hash = new_hash;
            new_hash
        } else {
            use_
        }
    }

    /// Port of `hasJoiningData(CConcept* joinConcept)`.
    pub fn has_joining_data(
        ctx: &ProcessContext,
        this: RepresentativeVariableBindingPathSetDataId,
        join_concept: ConceptId,
    ) -> bool {
        let joining_hash = ctx.rep_var_bind_path_set_data(this).use_joining_hash;
        if joining_hash.is_none() {
            return false;
        }
        ctx.rep_var_bind_path_set_joining_hash(joining_hash)
            .map
            .get(&join_concept)
            .copied()
            .unwrap_or_default()
            .use_joining_data
            .is_some()
    }

    /// Port of `getMigrateData(localizeOrCreate)`.
    ///
    /// The copy-on-write localise: when `localize_or_create` and there is no localised
    /// migrate data yet, allocate a fresh one, init-from the shared `mUseMigrateData`, and
    /// point `mLoc`/`mUse` at it. Uses the same lift-init-restore idiom as the
    /// `binding_hash::get_variable_binding_path_set` sibling (the new migrate data and its
    /// parent live in the same arena).
    pub fn get_migrate_data(
        ctx: &mut ProcessContext,
        this: RepresentativeVariableBindingPathSetDataId,
        localize_or_create: bool,
    ) -> RepresentativeVariableBindingPathSetMigrateDataId {
        let (loc, use_) = {
            let d = ctx.rep_var_bind_path_set_data(this);
            (d.loc_migrate_data, d.use_migrate_data)
        };
        if loc.is_none() && localize_or_create {
            let new_id = ctx.alloc_rep_var_bind_path_set_migrate_data(
                RepresentativeVariableBindingPathSetMigrateData::new(INVALID),
            );
            if use_.is_some() {
                let taken = std::mem::replace(
                    ctx.rep_var_bind_path_set_migrate_data_mut(use_),
                    RepresentativeVariableBindingPathSetMigrateData::new(INVALID),
                );
                ctx.rep_var_bind_path_set_migrate_data_mut(new_id)
                    .init_representative_variable_binding_path_set_migrate_data(Some(&taken));
                *ctx.rep_var_bind_path_set_migrate_data_mut(use_) = taken;
            } else {
                ctx.rep_var_bind_path_set_migrate_data_mut(new_id)
                    .init_representative_variable_binding_path_set_migrate_data(None);
            }
            let d = ctx.rep_var_bind_path_set_data_mut(this);
            d.loc_migrate_data = new_id;
            d.use_migrate_data = new_id;
            new_id
        } else {
            use_
        }
    }

    /// Port of `takeMigrateDataFrom(repData)`.
    ///
    /// Steals `repData`'s `mUseMigrateData` (nulling it on the source), copies the
    /// signature, and returns the taken migrate data.
    pub fn take_migrate_data_from(
        ctx: &mut ProcessContext,
        this: RepresentativeVariableBindingPathSetDataId,
        rep_data: RepresentativeVariableBindingPathSetDataId,
    ) -> RepresentativeVariableBindingPathSetMigrateDataId {
        let (rep_use, rep_sig) = {
            let d = ctx.rep_var_bind_path_set_data(rep_data);
            (d.use_migrate_data, d.sig_key)
        };
        {
            let t = ctx.rep_var_bind_path_set_data_mut(this);
            t.loc_migrate_data = rep_use;
            t.use_migrate_data = rep_use;
            t.sig_key.init_signature(Some(&rep_sig));
        }
        {
            let r = ctx.rep_var_bind_path_set_data_mut(rep_data);
            r.use_migrate_data = Id::NONE;
            r.loc_migrate_data = Id::NONE;
        }
        rep_use
    }

    /// Port of `copyMigrateDataFrom(repData)`.
    ///
    /// Allocates a fresh localised migrate data, init-copies it from `repData`'s
    /// `mUseMigrateData`, copies the signature, and points `mLoc`/`mUse` at it.
    pub fn copy_migrate_data_from(
        ctx: &mut ProcessContext,
        this: RepresentativeVariableBindingPathSetDataId,
        rep_data: RepresentativeVariableBindingPathSetDataId,
    ) -> RepresentativeVariableBindingPathSetMigrateDataId {
        let (rep_use, rep_sig) = {
            let d = ctx.rep_var_bind_path_set_data(rep_data);
            (d.use_migrate_data, d.sig_key)
        };
        let new_id = ctx.alloc_rep_var_bind_path_set_migrate_data(
            RepresentativeVariableBindingPathSetMigrateData::new(INVALID),
        );
        if rep_use.is_some() {
            let taken = std::mem::replace(
                ctx.rep_var_bind_path_set_migrate_data_mut(rep_use),
                RepresentativeVariableBindingPathSetMigrateData::new(INVALID),
            );
            ctx.rep_var_bind_path_set_migrate_data_mut(new_id)
                .init_representative_variable_binding_path_set_migrate_data(Some(&taken));
            *ctx.rep_var_bind_path_set_migrate_data_mut(rep_use) = taken;
        } else {
            ctx.rep_var_bind_path_set_migrate_data_mut(new_id)
                .init_representative_variable_binding_path_set_migrate_data(None);
        }
        {
            let t = ctx.rep_var_bind_path_set_data_mut(this);
            t.loc_migrate_data = new_id;
            t.use_migrate_data = new_id;
            t.sig_key.init_signature(Some(&rep_sig));
        }
        new_id
    }

    /// Port of `getRepresentatedVariableCount`
    /// (`mUseMigrateData ? …->getRepresentativeVariableBindingPathMap()->count() : 0`).
    pub fn get_representated_variable_count(
        ctx: &ProcessContext,
        this: RepresentativeVariableBindingPathSetDataId,
    ) -> Cint64 {
        let use_ = ctx.rep_var_bind_path_set_data(this).use_migrate_data;
        if use_.is_some() {
            ctx.rep_var_bind_path_set_migrate_data(use_)
                .get_representative_variable_binding_path_map()
                .count()
        } else {
            0
        }
    }

    /// Port of `CLinkerBase::getData` (the representative id).
    pub fn get_data(&self) -> Cint64 {
        self.data
    }
    /// Port of `CLinkerBase::setData`.
    pub fn set_data(&mut self, data: Cint64) -> &mut Self {
        self.data = data;
        self
    }
    /// Port of `CLinkerBase::getNext`.
    pub fn get_next(&self) -> RepresentativeVariableBindingPathSetDataId {
        self.next
    }
    /// Port of `CLinkerBase::setNext`.
    pub fn set_next(&mut self, next: RepresentativeVariableBindingPathSetDataId) -> &mut Self {
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
        this: RepresentativeVariableBindingPathSetDataId,
        appending_list: RepresentativeVariableBindingPathSetDataId,
    ) -> RepresentativeVariableBindingPathSetDataId {
        let mut last = this;
        while ctx.rep_var_bind_path_set_data(last).has_next() {
            last = ctx.rep_var_bind_path_set_data(last).get_next();
        }
        ctx.rep_var_bind_path_set_data_mut(last)
            .set_next(appending_list);
        this
    }
}

// ===========================================================================
// CRepresentativePropagationDescriptor
// (`CRepresentativePropagationDescriptor.{h,cpp}`,
//  `: public CLinkerBase<CRepresentativeVariableBindingPathSetData*,Self>,
//     public CDependencyTracker`)
// ===========================================================================

/// Port of `CRepresentativePropagationDescriptor`.
///
/// KONCLUDE-PORT-NOTE[ownership]: the `CLinkerBase<CRepresentativeVariableBindingPathSetData*,Self>`
/// base carries the *representative set data* AS its `data` (`getRepresentativeVariableBindingPathSetData()
/// == getData()`); folded to `data` (the SetData id) + `next` (the descriptor list linker).
/// `CDependencyTracker` → `dep_track_point`.
pub struct RepresentativePropagationDescriptor {
    /// `CLinkerBase::data` (the `CRepresentativeVariableBindingPathSetData*`).
    pub data: RepresentativeVariableBindingPathSetDataId,
    /// `CLinkerBase::next`.
    pub next: RepresentativePropagationDescriptorId,
    /// `CDependencyTracker::mDependencyTrackPoint`.
    pub dep_track_point: TrackPointId,
}

impl Default for RepresentativePropagationDescriptor {
    fn default() -> Self {
        RepresentativePropagationDescriptor {
            data: Id::NONE,
            next: Id::NONE,
            dep_track_point: Id::NONE,
        }
    }
}

impl RepresentativePropagationDescriptor {
    /// Port of `CRepresentativePropagationDescriptor::CRepresentativePropagationDescriptor`
    /// (`CLinkerBase(nullptr)`).
    pub fn new() -> Self {
        RepresentativePropagationDescriptor::default()
    }

    /// Port of `initRepresentativeDescriptor(repData, depTrackPoint)`.
    pub fn init_representative_descriptor(
        &mut self,
        rep_data: RepresentativeVariableBindingPathSetDataId,
        dep_track_point: TrackPointId,
    ) -> &mut Self {
        self.data = rep_data;
        self.dep_track_point = dep_track_point;
        self
    }

    /// Port of `getRepresentativeVariableBindingPathSetData` (`getData()`).
    pub fn get_representative_variable_binding_path_set_data(
        &self,
    ) -> RepresentativeVariableBindingPathSetDataId {
        self.data
    }
    /// Port of `setRepresentativeVariableBindingPathSetData` (`setData(repData)`).
    pub fn set_representative_variable_binding_path_set_data(
        &mut self,
        rep_data: RepresentativeVariableBindingPathSetDataId,
    ) -> &mut Self {
        self.data = rep_data;
        self
    }

    /// Port of `CLinkerBase::getData`.
    pub fn get_data(&self) -> RepresentativeVariableBindingPathSetDataId {
        self.data
    }
    /// Port of `CLinkerBase::setData`.
    pub fn set_data(&mut self, data: RepresentativeVariableBindingPathSetDataId) -> &mut Self {
        self.data = data;
        self
    }
    /// Port of `CLinkerBase::getNext`.
    pub fn get_next(&self) -> RepresentativePropagationDescriptorId {
        self.next
    }
    /// Port of `CLinkerBase::setNext`.
    pub fn set_next(&mut self, next: RepresentativePropagationDescriptorId) -> &mut Self {
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
        this: RepresentativePropagationDescriptorId,
        appending_list: RepresentativePropagationDescriptorId,
    ) -> RepresentativePropagationDescriptorId {
        let mut last = this;
        while ctx.rep_prop_des(last).has_next() {
            last = ctx.rep_prop_des(last).get_next();
        }
        ctx.rep_prop_des_mut(last).set_next(appending_list);
        this
    }
}

// ===========================================================================
// CRepresentativePropagationMapData
// (`CRepresentativePropagationMapData.{h,cpp}`)
// ===========================================================================

/// Port of `CRepresentativePropagationMapData` (the per-repID propagation-map value).
#[derive(Debug, Clone, Copy)]
pub struct RepresentativePropagationMapData {
    /// `CRepresentativePropagationDescriptor* mRepPropDes`.
    pub rep_prop_des: RepresentativePropagationDescriptorId,
}

impl Default for RepresentativePropagationMapData {
    fn default() -> Self {
        RepresentativePropagationMapData::new(Id::NONE)
    }
}

impl RepresentativePropagationMapData {
    /// Port of `CRepresentativePropagationMapData(repPropDes = nullptr)`.
    pub fn new(rep_prop_des: RepresentativePropagationDescriptorId) -> Self {
        RepresentativePropagationMapData { rep_prop_des }
    }

    /// Port of `getRepresentativePropagationDescriptor`.
    pub fn get_representative_propagation_descriptor(
        &self,
    ) -> RepresentativePropagationDescriptorId {
        self.rep_prop_des
    }
    /// Port of `hasRepresentativePropagationDescriptor`.
    pub fn has_representative_propagation_descriptor(&self) -> bool {
        self.rep_prop_des.is_some()
    }
    /// Port of `setRepresentativePropagationDescriptor`.
    pub fn set_representative_propagation_descriptor(
        &mut self,
        rep_prop_des: RepresentativePropagationDescriptorId,
    ) -> &mut Self {
        self.rep_prop_des = rep_prop_des;
        self
    }
}

// ===========================================================================
// CRepresentativePropagationMap
// (`CRepresentativePropagationMap.{h,cpp}`,
//  `: public CPROCESSMAP<cint64,CRepresentativePropagationMapData>`)
// ===========================================================================

/// Port of `CRepresentativePropagationMap`.
///
/// KONCLUDE-PORT-NOTE[ownership]: held BY VALUE by the propagation set; not an arena
/// element; `mProcessContext` opaque.
#[derive(Debug, Clone)]
pub struct RepresentativePropagationMap {
    /// `CProcessContext* mProcessContext` (opaque).
    pub process_context: Cint64,
    /// the `CPROCESSMAP<cint64,…MapData>` base storage (key = repID).
    pub map: HashMap<Cint64, RepresentativePropagationMapData>,
}

impl RepresentativePropagationMap {
    /// Port of `CRepresentativePropagationMap::CRepresentativePropagationMap(CProcessContext*)`.
    pub fn new(process_context: Cint64) -> Self {
        RepresentativePropagationMap {
            process_context,
            map: HashMap::new(),
        }
    }

    /// Port of `initRepresentativePropagationMap` (operator= from prev, else clear).
    pub fn init_representative_propagation_map(
        &mut self,
        prev_map: Option<&RepresentativePropagationMap>,
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
    /// Port of `CPROCESSMAP::value` (copy; default when absent).
    pub fn value(&self, key: Cint64) -> RepresentativePropagationMapData {
        self.map.get(&key).copied().unwrap_or_default()
    }
    /// Port of `CPROCESSMAP::operator[]`.
    pub fn entry_mut(&mut self, key: Cint64) -> &mut RepresentativePropagationMapData {
        self.map.entry(key).or_default()
    }
}

// ===========================================================================
// CRepresentativePropagationSet
// (`CRepresentativePropagationSet.{h,cpp}`)
// ===========================================================================

/// Port of `CRepresentativePropagationSet`.
///
/// A concept's incoming/outgoing representative propagations: the repID → descriptor
/// map (`mRepPropMap`, by value), the incoming/outgoing/last-processed descriptor
/// linkers, the rolling incoming signature (by value) and the concept descriptor.
pub struct RepresentativePropagationSet {
    /// `CProcessContext* mProcessContext` (opaque).
    pub process_context: Cint64,
    /// `CRepresentativePropagationMap mRepPropMap` (by value).
    pub rep_prop_map: RepresentativePropagationMap,
    /// `CConceptDescriptor* mConceptDescriptor`.
    pub concept_descriptor: ConDescId,
    /// `CRepresentativePropagationDescriptor* mIncomingRepPropDesLinker`.
    pub incoming_rep_prop_des_linker: RepresentativePropagationDescriptorId,
    /// `CRepresentativePropagationDescriptor* mOutgoingRepPropDesLinker`.
    pub outgoing_rep_prop_des_linker: RepresentativePropagationDescriptorId,
    /// `CRepresentativeVariableBindingPathSetDataSignature mIncomingRepPropSignature` (by value).
    pub incoming_rep_prop_signature: RepresentativeVariableBindingPathSetDataSignature,
    /// `CRepresentativePropagationDescriptor* mLastProcessedIncomingRepPropDesLinker`.
    pub last_processed_incoming_rep_prop_des_linker: RepresentativePropagationDescriptorId,
}

impl RepresentativePropagationSet {
    /// Port of `CRepresentativePropagationSet::CRepresentativePropagationSet(CProcessContext*)`
    /// (`: mProcessContext(processContext), mRepPropMap(processContext)`).
    pub fn new(process_context: Cint64) -> Self {
        RepresentativePropagationSet {
            process_context,
            rep_prop_map: RepresentativePropagationMap::new(process_context),
            concept_descriptor: Id::NONE,
            incoming_rep_prop_des_linker: Id::NONE,
            outgoing_rep_prop_des_linker: Id::NONE,
            incoming_rep_prop_signature: RepresentativeVariableBindingPathSetDataSignature::new(),
            last_processed_incoming_rep_prop_des_linker: Id::NONE,
        }
    }

    /// Port of `initRepresentativePropagationSet(prevSet)`.
    pub fn init_representative_propagation_set(
        &mut self,
        prev_set: Option<&RepresentativePropagationSet>,
    ) -> &mut Self {
        if let Some(prev) = prev_set {
            self.rep_prop_map
                .init_representative_propagation_map(Some(&prev.rep_prop_map));
            self.incoming_rep_prop_signature
                .init_signature(Some(&prev.incoming_rep_prop_signature));
            self.concept_descriptor = prev.concept_descriptor;
            self.incoming_rep_prop_des_linker = prev.incoming_rep_prop_des_linker;
            self.outgoing_rep_prop_des_linker = prev.outgoing_rep_prop_des_linker;
            self.last_processed_incoming_rep_prop_des_linker =
                prev.last_processed_incoming_rep_prop_des_linker;
        } else {
            self.rep_prop_map.init_representative_propagation_map(None);
            self.incoming_rep_prop_signature.init_signature(None);
            self.concept_descriptor = Id::NONE;
            self.incoming_rep_prop_des_linker = Id::NONE;
            self.outgoing_rep_prop_des_linker = Id::NONE;
            self.last_processed_incoming_rep_prop_des_linker = Id::NONE;
        }
        self
    }

    /// Port of `getRepresentativePropagationMap`.
    pub fn get_representative_propagation_map(&self) -> &RepresentativePropagationMap {
        &self.rep_prop_map
    }
    /// Mutable companion.
    pub fn get_representative_propagation_map_mut(&mut self) -> &mut RepresentativePropagationMap {
        &mut self.rep_prop_map
    }

    /// Port of `containsRepresentativePropagation(CRepresentativeVariableBindingPathSetData*)`.
    pub fn contains_representative_propagation_for_data(
        &self,
        ctx: &ProcessContext,
        rep_var_bind_path_set_data: RepresentativeVariableBindingPathSetDataId,
    ) -> bool {
        let rep_id = ctx
            .rep_var_bind_path_set_data(rep_var_bind_path_set_data)
            .get_representative_id();
        self.rep_prop_map.contains(rep_id)
    }

    /// Port of `containsRepresentativePropagation(cint64 repID)`.
    pub fn contains_representative_propagation_for_id(&self, rep_id: Cint64) -> bool {
        self.rep_prop_map.contains(rep_id)
    }

    /// Port of `getRepresentativePropagationDescriptor(CRepresentativeVariableBindingPathSetData*)`.
    pub fn get_representative_propagation_descriptor(
        &self,
        ctx: &ProcessContext,
        rep_var_bind_path_set_data: RepresentativeVariableBindingPathSetDataId,
    ) -> RepresentativePropagationDescriptorId {
        let rep_id = ctx
            .rep_var_bind_path_set_data(rep_var_bind_path_set_data)
            .get_representative_id();
        self.rep_prop_map
            .value(rep_id)
            .get_representative_propagation_descriptor()
    }

    /// Port of `addIncomingRepresentativePropagation(repPropDes)`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: split into ordered sub-borrows — the SetData reads
    /// (rep id / key / key signature) touch only the SetData arena, the descriptor reads +
    /// `append` only the descriptor arena, and the map / signature / linker mutations only
    /// the set; no two overlap (the `propagation_binding::add_propagation_binding`
    /// precedent). The signature is `Copy`, so `getKeySignature()` is taken by value.
    pub fn add_incoming_representative_propagation(
        ctx: &mut ProcessContext,
        this: RepresentativePropagationSetId,
        rep_prop_des: RepresentativePropagationDescriptorId,
    ) {
        let rep_data = ctx
            .rep_prop_des(rep_prop_des)
            .get_representative_variable_binding_path_set_data();
        let rep_id = ctx
            .rep_var_bind_path_set_data(rep_data)
            .get_representative_id();
        // CRepresentativePropagationMapData& data = mRepPropMap[repID];
        let has_des = ctx
            .rep_prop_set(this)
            .rep_prop_map
            .value(rep_id)
            .has_representative_propagation_descriptor();
        if !has_des {
            ctx.rep_prop_set_mut(this)
                .rep_prop_map
                .entry_mut(rep_id)
                .set_representative_propagation_descriptor(rep_prop_des);
            // signature: addKey(repKey) when a linker already exists, else init from key sig.
            if ctx
                .rep_prop_set(this)
                .incoming_rep_prop_des_linker
                .is_some()
            {
                let rep_key = ctx
                    .rep_var_bind_path_set_data(rep_data)
                    .get_representative_key();
                ctx.rep_prop_set_mut(this)
                    .incoming_rep_prop_signature
                    .add_key(rep_key);
            } else {
                let key_sig = *ctx.rep_var_bind_path_set_data(rep_data).get_key_signature();
                ctx.rep_prop_set_mut(this)
                    .incoming_rep_prop_signature
                    .init_signature(Some(&key_sig));
            }
            // mIncomingRepPropDesLinker = repPropDes->append(mIncomingRepPropDesLinker);
            let old_head = ctx.rep_prop_set(this).incoming_rep_prop_des_linker;
            let new_head = RepresentativePropagationDescriptor::append(ctx, rep_prop_des, old_head);
            ctx.rep_prop_set_mut(this).incoming_rep_prop_des_linker = new_head;
        }
    }

    /// Port of `copyRepresentativePropagations(repPropMap)` (`mRepPropMap = *repPropMap`).
    pub fn copy_representative_propagations(
        &mut self,
        rep_prop_map: Option<&RepresentativePropagationMap>,
    ) -> &mut Self {
        if let Some(m) = rep_prop_map {
            self.rep_prop_map = m.clone();
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

    /// Port of `addIncomingRepresentativePropagationDescriptorLinker(repPropDesLinker)`.
    ///
    /// Walks the appended linker chain adding each representative's key to the incoming
    /// signature, then splices the chain onto `mIncomingRepPropDesLinker`.
    pub fn add_incoming_representative_propagation_descriptor_linker(
        ctx: &mut ProcessContext,
        this: RepresentativePropagationSetId,
        rep_prop_des_linker: RepresentativePropagationDescriptorId,
    ) {
        let mut it = rep_prop_des_linker;
        while it.is_some() {
            let rep_data = ctx
                .rep_prop_des(it)
                .get_representative_variable_binding_path_set_data();
            let rep_key = ctx
                .rep_var_bind_path_set_data(rep_data)
                .get_representative_key();
            ctx.rep_prop_set_mut(this)
                .incoming_rep_prop_signature
                .add_key(rep_key);
            it = ctx.rep_prop_des(it).get_next();
        }
        let old_head = ctx.rep_prop_set(this).incoming_rep_prop_des_linker;
        let new_head =
            RepresentativePropagationDescriptor::append(ctx, rep_prop_des_linker, old_head);
        ctx.rep_prop_set_mut(this).incoming_rep_prop_des_linker = new_head;
    }

    /// Port of `getIncomingRepresentativePropagationDescriptorLinker`.
    pub fn get_incoming_representative_propagation_descriptor_linker(
        &self,
    ) -> RepresentativePropagationDescriptorId {
        self.incoming_rep_prop_des_linker
    }

    /// Port of `setOutgoingRepresentativePropagationDescriptorLinker`.
    pub fn set_outgoing_representative_propagation_descriptor_linker(
        &mut self,
        rep_prop_des_linker: RepresentativePropagationDescriptorId,
    ) -> &mut Self {
        self.outgoing_rep_prop_des_linker = rep_prop_des_linker;
        self
    }

    /// Port of `addOutgoingRepresentativePropagationDescriptorLinker`
    /// (`mOutgoingRepPropDesLinker = repPropDesLinker->append(mOutgoingRepPropDesLinker)`).
    pub fn add_outgoing_representative_propagation_descriptor_linker(
        ctx: &mut ProcessContext,
        this: RepresentativePropagationSetId,
        rep_prop_des_linker: RepresentativePropagationDescriptorId,
    ) {
        let old_head = ctx.rep_prop_set(this).outgoing_rep_prop_des_linker;
        let new_head =
            RepresentativePropagationDescriptor::append(ctx, rep_prop_des_linker, old_head);
        ctx.rep_prop_set_mut(this).outgoing_rep_prop_des_linker = new_head;
    }

    /// Port of `getOutgoingRepresentativePropagationDescriptorLinker`.
    pub fn get_outgoing_representative_propagation_descriptor_linker(
        &self,
    ) -> RepresentativePropagationDescriptorId {
        self.outgoing_rep_prop_des_linker
    }

    /// Port of `getIncomingRepresentativePropagationSignatureKey`.
    pub fn get_incoming_representative_propagation_signature_key(&self) -> Cint64 {
        self.incoming_rep_prop_signature.get_signature_value()
    }

    /// Port of `getLastProcessedIncomingRepresentativePropagationDescriptorLinker`.
    pub fn get_last_processed_incoming_representative_propagation_descriptor_linker(
        &self,
    ) -> RepresentativePropagationDescriptorId {
        self.last_processed_incoming_rep_prop_des_linker
    }

    /// Port of `setLastProcessedIncomingRepresentativePropagationDescriptorLinker`.
    pub fn set_last_processed_incoming_representative_propagation_descriptor_linker(
        &mut self,
        descriptor: RepresentativePropagationDescriptorId,
    ) -> &mut Self {
        self.last_processed_incoming_rep_prop_des_linker = descriptor;
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rep_data(
        ctx: &mut ProcessContext,
        rep_id: Cint64,
        key_component: Cint64,
    ) -> RepresentativeVariableBindingPathSetDataId {
        let tag = ctx.used_process_tagger().get_current_localization_tag();
        let id = ctx.alloc_rep_var_bind_path_set_data(
            RepresentativeVariableBindingPathSetData::new(INVALID, tag),
        );
        ctx.rep_var_bind_path_set_data_mut(id)
            .set_representative_id(rep_id)
            .add_key_signature_value(key_component);
        id
    }

    fn var_binding(
        ctx: &mut ProcessContext,
        variable: Cint64,
        individual: Cint64,
    ) -> super::super::varbind::VarBindingId {
        let id = ctx.alloc_var_binding(super::super::varbind::VariableBinding::new());
        ctx.var_binding_mut(id).init_variable_binding(
            TrackPointId::NONE,
            super::super::NodeId::new(individual),
            VariableId::new(variable),
        );
        id
    }

    fn var_binding_path_from_bindings(
        ctx: &mut ProcessContext,
        prop_id: Cint64,
        bindings: &[super::super::varbind::VarBindingId],
    ) -> VarBindingPathId {
        let mut head = VarBindingDescriptorId::NONE;
        let mut last = VarBindingDescriptorId::NONE;
        for binding in bindings {
            let des = ctx.alloc_var_binding_des(VariableBindingDescriptor::new());
            ctx.var_binding_des_mut(des)
                .init_variable_binding_descriptor(*binding);
            if last.is_some() {
                ctx.var_binding_des_mut(last).set_next(des);
            } else {
                head = des;
            }
            last = des;
        }
        let path = ctx.alloc_vbpath(super::super::varbind::VariableBindingPath::new());
        ctx.vbpath_mut(path)
            .init_variable_binding_path(prop_id, head);
        path
    }

    #[test]
    fn representative_path_set_hash_insert_and_data_lookup_follow_rep_id() {
        let mut ctx = ProcessContext::new();
        let hash = ctx.alloc_rep_var_bind_path_set_hash(
            RepresentativeVariableBindingPathSetHash::new(INVALID),
        );
        let first = rep_data(&mut ctx, 10, 7);
        let second = rep_data(&mut ctx, 20, 7);

        RepresentativeVariableBindingPathSetHash::insert_representative_variable_binding_path_set_data(
            &mut ctx, hash, first,
        );
        RepresentativeVariableBindingPathSetHash::insert_representative_variable_binding_path_set_data(
            &mut ctx, hash, second,
        );

        assert_eq!(
            RepresentativeVariableBindingPathSetHash::get_representative_variable_binding_path_set_data_for_data(
                &mut ctx, hash, first, false,
            ),
            first
        );
        assert_eq!(
            RepresentativeVariableBindingPathSetHash::get_representative_variable_binding_path_set_data_for_data(
                &mut ctx, hash, second, false,
            ),
            second
        );
    }

    #[test]
    fn representative_path_set_hash_init_copies_use_and_clears_local_linker() {
        let mut ctx = ProcessContext::new();
        let source_hash = ctx.alloc_rep_var_bind_path_set_hash(
            RepresentativeVariableBindingPathSetHash::new(INVALID),
        );
        let data = rep_data(&mut ctx, 10, 11);
        let key = ctx
            .rep_var_bind_path_set_data(data)
            .get_representative_key();
        RepresentativeVariableBindingPathSetHash::insert_representative_variable_binding_path_set_data(
            &mut ctx,
            source_hash,
            data,
        );

        let copied_hash = ctx.alloc_rep_var_bind_path_set_hash(
            RepresentativeVariableBindingPathSetHash::new(INVALID),
        );
        let source = std::mem::replace(
            ctx.rep_var_bind_path_set_hash_mut(source_hash),
            RepresentativeVariableBindingPathSetHash::new(INVALID),
        );
        ctx.rep_var_bind_path_set_hash_mut(copied_hash)
            .init_representative_variable_binding_path_set_hash(Some(&source));
        *ctx.rep_var_bind_path_set_hash_mut(source_hash) = source;

        let copied_bucket = ctx
            .rep_var_bind_path_set_hash(copied_hash)
            .map
            .get(&key)
            .copied()
            .unwrap();
        assert_eq!(copied_bucket.use_data_linker, data);
        assert!(copied_bucket.loc_data_linker.is_none());
    }

    #[test]
    fn representative_path_hash_uses_variable_binding_path_propagation_id() {
        let mut ctx = ProcessContext::new();
        let hash =
            ctx.alloc_rep_var_bind_path_hash(RepresentativeVariableBindingPathHash::new(INVALID));
        let path = ctx.alloc_vbpath(super::super::varbind::VariableBindingPath::new());
        ctx.vbpath_mut(path)
            .init_variable_binding_path(41, Id::NONE);

        assert!(
            RepresentativeVariableBindingPathHash::get_representative_variable_binding_path_set_data(
                &mut ctx, hash, path, false,
            )
            .is_none()
        );
        let data =
            RepresentativeVariableBindingPathHash::get_representative_variable_binding_path_set_data(
                &mut ctx, hash, path, true,
            );
        assert!(data.is_some());
        assert_eq!(
            RepresentativeVariableBindingPathHash::get_representative_variable_binding_path_set_data(
                &mut ctx, hash, path, false,
            ),
            data
        );
        assert_eq!(
            RepresentativeVariableBindingPathHash::get_representative_variable_binding_path_set_data(
                &mut ctx, hash, path, true,
            ),
            data
        );
        let bucket = ctx
            .rep_var_bind_path_hash(hash)
            .map
            .get(&41)
            .copied()
            .unwrap();
        assert_eq!(bucket.use_data_linker, data);
        assert_eq!(bucket.loc_data_linker, data);
    }

    #[test]
    fn representative_path_hash_init_copies_use_and_clears_local_linker() {
        let mut ctx = ProcessContext::new();
        let source_hash =
            ctx.alloc_rep_var_bind_path_hash(RepresentativeVariableBindingPathHash::new(INVALID));
        let path = ctx.alloc_vbpath(super::super::varbind::VariableBindingPath::new());
        ctx.vbpath_mut(path)
            .init_variable_binding_path(43, Id::NONE);
        let data =
            RepresentativeVariableBindingPathHash::get_representative_variable_binding_path_set_data(
                &mut ctx,
                source_hash,
                path,
                true,
            );

        let copied_hash =
            ctx.alloc_rep_var_bind_path_hash(RepresentativeVariableBindingPathHash::new(INVALID));
        let source = std::mem::replace(
            ctx.rep_var_bind_path_hash_mut(source_hash),
            RepresentativeVariableBindingPathHash::new(INVALID),
        );
        ctx.rep_var_bind_path_hash_mut(copied_hash)
            .init_representative_variable_binding_path_hash(Some(&source));
        *ctx.rep_var_bind_path_hash_mut(source_hash) = source;

        let copied_bucket = ctx
            .rep_var_bind_path_hash(copied_hash)
            .map
            .get(&43)
            .copied()
            .unwrap();
        assert_eq!(copied_bucket.use_data_linker, data);
        assert!(copied_bucket.loc_data_linker.is_none());
    }

    #[test]
    fn representative_path_set_hash_compares_ordered_key_sets_only() {
        let mut prop_map = RepresentativePropagationMap::new(INVALID);
        prop_map.entry_mut(3);
        prop_map.entry_mut(9);

        let mut cont_map = RepresentativeContainingMap::new(INVALID);
        cont_map.insert_contained_representative(9, Id::NONE, false);
        cont_map.insert_contained_representative(3, Id::NONE, false);
        assert!(RepresentativeVariableBindingPathSetHash::is_representative_propagation_map_identical_to_representative_containing_map(
            &prop_map,
            &cont_map,
        ));

        cont_map.insert_contained_representative(11, Id::NONE, false);
        assert!(!RepresentativeVariableBindingPathSetHash::is_representative_propagation_map_identical_to_representative_containing_map(
            &prop_map,
            &cont_map,
        ));
    }

    #[test]
    fn representative_path_set_hash_propagation_lookup_requires_matching_migrate_map() {
        let mut ctx = ProcessContext::new();
        let hash = ctx.alloc_rep_var_bind_path_set_hash(
            RepresentativeVariableBindingPathSetHash::new(INVALID),
        );
        let data = rep_data(&mut ctx, 10, 13);
        let sig = *ctx.rep_var_bind_path_set_data(data).get_key_signature();

        let migrate =
            RepresentativeVariableBindingPathSetData::get_migrate_data(&mut ctx, data, true);
        ctx.rep_var_bind_path_set_migrate_data_mut(migrate)
            .get_representative_containing_map_mut()
            .insert_contained_representative(10, data, false);
        RepresentativeVariableBindingPathSetHash::insert_representative_variable_binding_path_set_data(
            &mut ctx, hash, data,
        );

        let prop_set = ctx.alloc_rep_prop_set(RepresentativePropagationSet::new(INVALID));
        ctx.rep_prop_set_mut(prop_set)
            .incoming_rep_prop_signature
            .init_signature(Some(&sig));
        ctx.rep_prop_set_mut(prop_set).rep_prop_map.entry_mut(10);

        assert_eq!(
            RepresentativeVariableBindingPathSetHash::get_representative_variable_binding_path_set_data_for_propagation_set(
                &mut ctx, hash, prop_set, false,
            ),
            data
        );
    }

    #[test]
    fn representative_joining_key_map_lazily_creates_and_copies_data_maps() {
        let mut joining_key_map = RepresentativeVariableBindingPathSetJoiningKeyMap::new(17);
        assert!(joining_key_map
            .get_joining_key_data_map_existing(5)
            .is_none());

        {
            let data_map = joining_key_map
                .get_joining_key_data_map(5, true)
                .expect("created joining-key data map");
            assert_eq!(data_map.process_context, 17);
            data_map.insert(101, VarBindingPathId::new(3));
            data_map.insert(102, VarBindingPathId::new(4));
        }

        assert_eq!(joining_key_map.count(), 1);
        assert_eq!(
            joining_key_map
                .get_joining_key_data_map(5, false)
                .expect("existing joining-key data map")
                .value(101),
            VarBindingPathId::new(3)
        );
        assert!(joining_key_map.get_joining_key_data_map(6, false).is_none());

        let mut copied = RepresentativeVariableBindingPathSetJoiningKeyMap::new(19);
        copied
            .init_representative_variable_binding_path_set_joining_key_map(Some(&joining_key_map));
        assert_eq!(copied.count(), 1);
        assert_eq!(
            copied
                .get_joining_key_data_map_existing(5)
                .expect("copied joining-key data map")
                .count(),
            2
        );

        copied.init_representative_variable_binding_path_set_joining_key_map(None);
        assert_eq!(copied.count(), 0);
    }

    #[test]
    fn representative_common_key_data_reports_left_and_right_counts() {
        let mut left = RepresentativeVariableBindingPathSetJoiningKeyDataMap::new(0);
        left.insert(1, VarBindingPathId::new(11));
        left.insert(2, VarBindingPathId::new(12));
        let mut right = RepresentativeVariableBindingPathSetJoiningKeyDataMap::new(0);
        right.insert(3, VarBindingPathId::new(13));

        let common_data = RepresentativeJoiningCommonKeyData::new(left.clone(), right.clone());
        assert_eq!(common_data.get_left_count(), 2);
        assert_eq!(common_data.get_right_count(), 1);
        assert_eq!(
            common_data.get_left_joining_data_map().value(1),
            VarBindingPathId::new(11)
        );
        assert_eq!(
            common_data.get_right_joining_data_map().value(3),
            VarBindingPathId::new(13)
        );

        let mut common_map = RepresentativeJoiningCommonKeyMap::new(0);
        common_map.insert(77, common_data);
        assert_eq!(common_map.count(), 1);
        assert_eq!(common_map.value(77).unwrap().get_left_count(), 2);

        let mut copied = RepresentativeJoiningCommonKeyMap::new(0);
        copied.init_representative_joining_common_key_map(Some(&common_map));
        assert_eq!(copied.value(77).unwrap().get_right_count(), 1);
        copied.init_representative_joining_common_key_map(None);
        assert_eq!(copied.count(), 0);
    }

    #[test]
    fn representative_joining_all_data_extension_lazily_creates_resolve_maps() {
        let mut ext = RepresentativeJoiningAllDataExtension::new(23);
        assert!(ext
            .get_left_resolve_variable_binding_path_map(false)
            .is_none());
        assert!(ext
            .get_right_resolve_variable_binding_path_map(false)
            .is_none());

        let left = ext
            .get_resolve_variable_binding_path_map(true, true)
            .expect("left resolve map");
        assert_eq!(left.process_context, 23);
        left.insert(
            5,
            super::super::varbind::RepresentativeVariableBindingPathMapData::new(
                VarBindingPathId::new(5),
                RepresentativeVariableBindingPathSetDataId::NONE,
            ),
        );

        let right = ext
            .get_resolve_variable_binding_path_map(false, true)
            .expect("right resolve map");
        assert_eq!(right.process_context, 23);
        assert_eq!(right.count(), 0);

        let rep_data = RepresentativeVariableBindingPathSetDataId::new(8);
        ext.set_representative_variable_binding_path_set_data(rep_data);
        assert_eq!(
            ext.get_representative_variable_binding_path_set_data(),
            rep_data
        );
        assert_eq!(
            ext.get_left_resolve_variable_binding_path_map(false)
                .expect("existing left map")
                .count(),
            1
        );
    }

    #[test]
    fn representative_path_set_joining_hash_lazily_creates_joining_data() {
        let mut ctx = ProcessContext::new();
        let hash = ctx.alloc_rep_var_bind_path_set_joining_hash(
            RepresentativeVariableBindingPathSetJoiningHash::new(31),
        );
        let join_concept = ConceptId::new(17);

        assert_eq!(
            RepresentativeVariableBindingPathSetJoiningHash::get_representative_variable_binding_path_set_joining_data(
                &mut ctx,
                hash,
                join_concept,
                false,
            ),
            RepresentativeVariableBindingPathSetJoiningDataId::NONE
        );

        let joining_data =
            RepresentativeVariableBindingPathSetJoiningHash::get_representative_variable_binding_path_set_joining_data(
                &mut ctx,
                hash,
                join_concept,
                true,
            );
        assert!(joining_data.is_some());
        assert_eq!(
            ctx.rep_var_bind_path_set_joining_data(joining_data)
                .process_context,
            31
        );
        assert_eq!(
            RepresentativeVariableBindingPathSetJoiningHash::get_representative_variable_binding_path_set_joining_data(
                &mut ctx,
                hash,
                join_concept,
                false,
            ),
            joining_data
        );

        ctx.rep_var_bind_path_set_joining_data_mut(joining_data)
            .get_joining_key_map_mut()
            .get_joining_key_data_map(44, true)
            .expect("joining-key data map")
            .insert(7, VarBindingPathId::new(3));

        let copied_hash = ctx.alloc_rep_var_bind_path_set_joining_hash(
            RepresentativeVariableBindingPathSetJoiningHash::new(32),
        );
        let source = std::mem::replace(
            ctx.rep_var_bind_path_set_joining_hash_mut(hash),
            RepresentativeVariableBindingPathSetJoiningHash::new(31),
        );
        ctx.rep_var_bind_path_set_joining_hash_mut(copied_hash)
            .init_representative_variable_binding_path_set_joining_hash(Some(&source));
        *ctx.rep_var_bind_path_set_joining_hash_mut(hash) = source;

        let copied_bucket = ctx
            .rep_var_bind_path_set_joining_hash(copied_hash)
            .map
            .get(&join_concept)
            .copied()
            .unwrap();
        assert_eq!(copied_bucket.use_joining_data, joining_data);
        assert!(copied_bucket.loc_joining_data.is_none());
    }

    #[test]
    fn representative_path_set_data_lazily_creates_joining_hash() {
        let mut ctx = ProcessContext::new();
        let data = rep_data(&mut ctx, 30, 4);
        let join_concept = ConceptId::new(19);

        assert_eq!(
            RepresentativeVariableBindingPathSetData::get_joining_hash(&mut ctx, data, false),
            RepresentativeVariableBindingPathSetJoiningHashId::NONE
        );
        assert!(!RepresentativeVariableBindingPathSetData::has_joining_data(
            &ctx,
            data,
            join_concept
        ));

        let joining_hash =
            RepresentativeVariableBindingPathSetData::get_joining_hash(&mut ctx, data, true);
        assert!(joining_hash.is_some());
        assert_eq!(
            ctx.rep_var_bind_path_set_joining_hash(joining_hash)
                .process_context,
            INVALID
        );
        assert_eq!(
            RepresentativeVariableBindingPathSetData::get_joining_hash(&mut ctx, data, false),
            joining_hash
        );

        let joining_data =
            RepresentativeVariableBindingPathSetJoiningHash::get_representative_variable_binding_path_set_joining_data(
                &mut ctx,
                joining_hash,
                join_concept,
                true,
            );
        assert!(joining_data.is_some());
        assert!(RepresentativeVariableBindingPathSetData::has_joining_data(
            &ctx,
            data,
            join_concept
        ));
    }

    #[test]
    fn representative_joining_hash_uses_ordered_representative_pair() {
        let mut ctx = ProcessContext::new();
        let hash = ctx.alloc_rep_joining_hash(RepresentativeJoiningHash::new(41));
        let left = rep_data(&mut ctx, 10, 1);
        let right = rep_data(&mut ctx, 20, 2);

        assert_eq!(
            RepresentativeJoiningHash::get_representative_joining_data(
                &mut ctx, hash, left, right, false,
            ),
            RepresentativeJoiningDataId::NONE
        );

        let left_right = RepresentativeJoiningHash::get_representative_joining_data(
            &mut ctx, hash, left, right, true,
        );
        let right_left = RepresentativeJoiningHash::get_representative_joining_data(
            &mut ctx, hash, right, left, true,
        );
        assert!(left_right.is_some());
        assert!(right_left.is_some());
        assert_ne!(left_right, right_left);
        assert_eq!(
            RepresentativeJoiningHash::get_representative_joining_data(
                &mut ctx, hash, left, right, false,
            ),
            left_right
        );
        assert_eq!(
            RepresentativeJoiningHash::get_representative_joining_data(
                &mut ctx, hash, right, left, false,
            ),
            right_left
        );

        let common_map = ctx
            .rep_joining_data_mut(left_right)
            .get_representative_joining_common_key_map_mut();
        common_map.insert(
            5,
            RepresentativeJoiningCommonKeyData::new(
                RepresentativeVariableBindingPathSetJoiningKeyDataMap::new(41),
                RepresentativeVariableBindingPathSetJoiningKeyDataMap::new(41),
            ),
        );
        assert_eq!(
            ctx.rep_joining_data(left_right)
                .get_representative_joining_common_key_map()
                .count(),
            1
        );

        let extension = ctx
            .rep_joining_data_mut(left_right)
            .get_joining_all_extension(true)
            .expect("joining all extension");
        assert_eq!(extension.process_context, 41);
        assert!(ctx
            .rep_joining_data_mut(right_left)
            .get_joining_all_extension(false)
            .is_none());
    }

    #[test]
    fn representative_joining_key_hash_extracts_key_descriptors() {
        let mut ctx = ProcessContext::new();
        let b1 = var_binding(&mut ctx, 1, 101);
        let b2 = var_binding(&mut ctx, 2, 102);
        let b3 = var_binding(&mut ctx, 3, 103);
        let path = var_binding_path_from_bindings(&mut ctx, 7, &[b1, b2, b3]);

        let key_head =
            RepresentativeVariableBindingPathJoiningKeyHash::create_variable_binding_hash_key_descriptor(
                &mut ctx,
                path,
                &[VariableId::new(2), VariableId::new(3)],
            );
        assert_eq!(ctx.var_binding_des(key_head).get_variable_binding(), b2);
        let second = ctx.var_binding_des(key_head).get_next();
        assert_eq!(ctx.var_binding_des(second).get_variable_binding(), b3);
        assert!(ctx.var_binding_des(second).get_next().is_none());
    }

    #[test]
    fn representative_joining_key_hash_interns_by_selected_binding_identity() {
        let mut ctx = ProcessContext::new();
        let hash = ctx.alloc_rep_var_bind_path_joining_key_hash(
            RepresentativeVariableBindingPathJoiningKeyHash::new(51),
        );
        let b1 = var_binding(&mut ctx, 1, 101);
        let b2 = var_binding(&mut ctx, 2, 102);
        let b3 = var_binding(&mut ctx, 3, 103);
        let same_key_path = var_binding_path_from_bindings(&mut ctx, 11, &[b1, b2, b3]);
        let same_key_other_path = var_binding_path_from_bindings(&mut ctx, 12, &[b1, b2, b3]);
        let different_b2 = var_binding(&mut ctx, 2, 202);
        let different_key_path =
            var_binding_path_from_bindings(&mut ctx, 13, &[b1, different_b2, b3]);
        let key_vars = [VariableId::new(2), VariableId::new(3)];

        assert_eq!(
            RepresentativeVariableBindingPathJoiningKeyHash::get_representative_variable_binding_path_joining_key(
                &mut ctx,
                hash,
                same_key_path,
                &key_vars,
                false,
            ),
            0
        );
        let first_key =
            RepresentativeVariableBindingPathJoiningKeyHash::get_representative_variable_binding_path_joining_key(
                &mut ctx,
                hash,
                same_key_path,
                &key_vars,
                true,
            );
        let reused_key =
            RepresentativeVariableBindingPathJoiningKeyHash::get_representative_variable_binding_path_joining_key(
                &mut ctx,
                hash,
                same_key_other_path,
                &key_vars,
                true,
            );
        let second_key =
            RepresentativeVariableBindingPathJoiningKeyHash::get_representative_variable_binding_path_joining_key(
                &mut ctx,
                hash,
                different_key_path,
                &key_vars,
                true,
            );

        assert_eq!(first_key, 1);
        assert_eq!(reused_key, first_key);
        assert_eq!(second_key, 2);
        assert_eq!(
            ctx.rep_var_bind_path_joining_key_hash(hash)
                .next_rep_var_bind_path_joining_key_tag,
            3
        );

        let copied_hash = ctx.alloc_rep_var_bind_path_joining_key_hash(
            RepresentativeVariableBindingPathJoiningKeyHash::new(52),
        );
        let source = std::mem::replace(
            ctx.rep_var_bind_path_joining_key_hash_mut(hash),
            RepresentativeVariableBindingPathJoiningKeyHash::new(51),
        );
        ctx.rep_var_bind_path_joining_key_hash_mut(copied_hash)
            .init_representative_variable_binding_path_joining_key_hash(Some(&source));
        *ctx.rep_var_bind_path_joining_key_hash_mut(hash) = source;
        assert_eq!(
            ctx.rep_var_bind_path_joining_key_hash(copied_hash)
                .next_rep_var_bind_path_joining_key_tag,
            3
        );
        assert_eq!(
            RepresentativeVariableBindingPathJoiningKeyHash::get_representative_variable_binding_path_joining_key(
                &mut ctx,
                copied_hash,
                same_key_path,
                &key_vars,
                false,
            ),
            first_key
        );
    }
}

// ===========================================================================
// W3.5r-ARENA-ADDITIONS
// ===========================================================================
//
// The reconcile adds the following to `process/context.rs` (the `ProcessContext`
// per-test arena container) so the `ctx.<arena>(id)` derefs in the methods above
// resolve. Each line is one `Arena<T>` field + its `arena_accessors!` trio. The four
// per-test pool objects each get their own arena; the four `CPROCESSMAP`s + the
// signature are held BY VALUE and need NO arena. The W3.5r-DEFER joining-hash marker
// has NO arena yet (allocation deferred to its own unit).
//
//   rep_var_bind_path_set_datas:         Arena<RepresentativeVariableBindingPathSetData>        | RepresentativeVariableBindingPathSetDataId        | rep_var_bind_path_set_data / rep_var_bind_path_set_data_mut / alloc_rep_var_bind_path_set_data
//   rep_var_bind_path_set_migrate_datas: Arena<RepresentativeVariableBindingPathSetMigrateData> | RepresentativeVariableBindingPathSetMigrateDataId | rep_var_bind_path_set_migrate_data / rep_var_bind_path_set_migrate_data_mut / alloc_rep_var_bind_path_set_migrate_data
//   rep_prop_descs:                      Arena<RepresentativePropagationDescriptor>             | RepresentativePropagationDescriptorId             | rep_prop_des / rep_prop_des_mut / alloc_rep_prop_des
//   rep_prop_sets:                       Arena<RepresentativePropagationSet>                    | RepresentativePropagationSetId                    | rep_prop_set / rep_prop_set_mut / alloc_rep_prop_set
//
// Imports the reconcile adds to `context.rs`:
//   use super::representative::{
//       RepresentativeVariableBindingPathSetData, RepresentativeVariableBindingPathSetMigrateData,
//       RepresentativePropagationDescriptor, RepresentativePropagationSet,
//       RepresentativeVariableBindingPathSetDataId, RepresentativeVariableBindingPathSetMigrateDataId,
//       RepresentativePropagationDescriptorId, RepresentativePropagationSetId,
//   };
// and `pub mod representative;` in `process/mod.rs`.
