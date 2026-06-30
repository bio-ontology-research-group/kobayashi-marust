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
//! ## W3.5r-DEFER[api] — the per-set joining hash (own unit)
//!
//! `CRepresentativeVariableBindingPathSetData` lazily allocates a
//! `CRepresentativeVariableBindingPathSetJoiningHash` (its own not-yet-ported
//! `CPROCESSHASH<CConcept*,…>` subsystem). It is kept as a zero-size placeholder marker
//! + `Id<T>` alias (no arena), exactly as `propagation_binding` kept its three lazy
//! sub-objects. `getJoiningHash(create)` returns the stored id (`Id::NONE` until that
//! subsystem lands) and `hasJoiningData` returns `false` — the faithful null-hash case.

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
use super::context::ProcessContext;
use super::varbind::RepresentativeVariableBindingPathMap;
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

// --- W3.5r-DEFER[api]: the per-set joining hash (own unit, kept as a marker) ---

/// W3.5r-DEFER placeholder for `CRepresentativeVariableBindingPathSetJoiningHash` (own unit).
#[derive(Debug, Default)]
pub struct RepresentativeVariableBindingPathSetJoiningHash;
/// `CRepresentativeVariableBindingPathSetJoiningHash*` → `…Id`.
pub type RepresentativeVariableBindingPathSetJoiningHashId =
    Id<RepresentativeVariableBindingPathSetJoiningHash>;

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
        RepresentativeContainingMapData { contained_rep, explicitely_contained: expl_contained }
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
        RepresentativeContainingMap { process_context, map: HashMap::new() }
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
            self.rep_containing_map.init_representative_containing_map(None);
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
    /// `CRepresentativeVariableBindingPathSetJoiningHash* mUseJoiningHash` (W3.5r-DEFER marker).
    pub use_joining_hash: RepresentativeVariableBindingPathSetJoiningHashId,
    /// `CRepresentativeVariableBindingPathSetJoiningHash* mLocJoiningHash` (W3.5r-DEFER marker).
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
    ///
    /// W3.5r-DEFER[api]: `CRepresentativeVariableBindingPathSetJoiningHash` is an unported
    /// own unit; the allocate-on-create is deferred (the stored marker id is returned,
    /// `Id::NONE` until the joining-hash subsystem lands). Control flow is preserved.
    pub fn get_joining_hash(
        &self,
        create: bool,
    ) -> RepresentativeVariableBindingPathSetJoiningHashId {
        // if (create && !mLocJoiningHash) { mLocJoiningHash = allocate…(); }  // W3.5r-DEFER
        self.use_joining_hash
    }

    /// Port of `hasJoiningData(CConcept* joinConcept)`.
    ///
    /// W3.5r-DEFER[api]: with the joining hash unported it is always `Id::NONE`, so this
    /// is the faithful `mUseJoiningHash == nullptr` branch (`return false`).
    pub fn has_joining_data(&self, join_concept: Cint64) -> bool {
        if self.use_joining_hash.is_none() {
            return false;
        }
        // W3.5r-DEFER[api]: joiningHash->value(joinConcept).mUseJoiningData != nullptr.
        false
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
        ctx.rep_var_bind_path_set_data_mut(last).set_next(appending_list);
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
#[derive(Clone)]
pub struct RepresentativePropagationMap {
    /// `CProcessContext* mProcessContext` (opaque).
    pub process_context: Cint64,
    /// the `CPROCESSMAP<cint64,…MapData>` base storage (key = repID).
    pub map: HashMap<Cint64, RepresentativePropagationMapData>,
}

impl RepresentativePropagationMap {
    /// Port of `CRepresentativePropagationMap::CRepresentativePropagationMap(CProcessContext*)`.
    pub fn new(process_context: Cint64) -> Self {
        RepresentativePropagationMap { process_context, map: HashMap::new() }
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
            incoming_rep_prop_signature:
                RepresentativeVariableBindingPathSetDataSignature::new(),
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
        let rep_id = ctx.rep_var_bind_path_set_data(rep_data).get_representative_id();
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
            if ctx.rep_prop_set(this).incoming_rep_prop_des_linker.is_some() {
                let rep_key = ctx.rep_var_bind_path_set_data(rep_data).get_representative_key();
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
            let rep_key = ctx.rep_var_bind_path_set_data(rep_data).get_representative_key();
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
