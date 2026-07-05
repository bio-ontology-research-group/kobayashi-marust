//! `process::binding_hash` — port unit **W3b**: the two node-owned concept→binding
//! container hashes that W2 left as fieldless markers in `process::stubs`
//! (`ConceptVariableBindingPathSetHash`, `ConceptPropagationBindingSetHash`).
//!
//! Sources (`Source/Reasoner/Kernel/Process/`):
//!   * `CConceptVariableBindingPathSetHash.{h,cpp}`     → [`ConceptVariableBindingPathSetHash`]
//!   * `CConceptVariableBindingPathSetHashData.{h,cpp}` → [`ConceptVariableBindingPathSetHashData`]
//!   * `CConceptPropagationBindingSetHash.{h,cpp}`      → [`ConceptPropagationBindingSetHash`]
//!   * `CConceptPropagationBindingSetHashData.{h,cpp}`  → [`ConceptPropagationBindingSetHashData`]
//!
//! Each is a `CPROCESSHASH<cint64, …HashData>` (a concept-tag → binding-set hash)
//! that the node lazily allocates (`getConceptVariableBindingPathSetHash` /
//! `getConceptPropagationBindingSetHash`). Per the global `[ownership]` /
//! `[memory-pool]` decision (`substrate.rs`) the pooled `CPROCESSHASH` becomes an
//! owned `HashMap`, the hash itself is an arena element on `ProcessContext`
//! (`con_var_bind_path_set_hashes` / `con_prop_binding_set_hashes`), and the C++
//! `concept->getConceptTag()` key is taken as a `con_tag: Cint64` (the caller
//! reads `ctx.concept(c).get_concept_tag()` — the ontology arenas are not threaded
//! into these hash methods).
//!
//! ## Localize / COW value model (the `getXBindingSet` heart)
//!
//! `getVariableBindingPathSet` / `getPropagationBindingSet` localize a shared
//! binding-set when `localize` is set: `operator[](conTag)` default-constructs the
//! data, and if `mLoc…` is null a fresh binding set is allocated and
//! `init…BindingSet(mUse…)`-inherited from the parent, then `mUse = mLoc = new`.
//! `CVariableBindingPathSet` IS ported (`varbind::VariableBindingPathSet`), so the
//! variable-binding-path branch is faithful end-to-end; `CPropagationBindingSet`
//! is NOT yet ported, so the propagation-binding alloc is a `W3b-DEFER[api]` (the
//! control flow is preserved, only the unported-set allocation is stubbed).

#![allow(dead_code)]

use std::collections::HashMap;

use super::super::model::substrate::{Cint64, Id, INVALID};
use super::context::ProcessContext;
use super::varbind::{VarBindingPathDescriptorId, VarBindingPathSetId, VariableBindingPathSet};

// ===========================================================================
// id aliases (the real targets of the W2 stub markers) + the unported payloads
// ===========================================================================

/// `CConceptVariableBindingPathSetHash*` → `ConceptVariableBindingPathSetHashId`.
pub type ConceptVariableBindingPathSetHashId = Id<ConceptVariableBindingPathSetHash>;
/// `CConceptPropagationBindingSetHash*`    → `ConceptPropagationBindingSetHashId`.
pub type ConceptPropagationBindingSetHashId = Id<ConceptPropagationBindingSetHash>;

/// W3c landed the propagation-binding subsystem: the former W3b placeholder
/// `PropagationBindingSet` / `PropagationBindingDescriptor` markers are now the real
/// ported structs in `process::propagation_binding`. Re-exported here so the existing
/// `binding_hash::PropagationBinding{Set,Descriptor}{,Id}` paths keep resolving.
pub use super::propagation_binding::{
    PropagationBindingDescriptor, PropagationBindingDescriptorId, PropagationBindingSet,
    PropagationBindingSetId,
};

// ===========================================================================
// CConceptVariableBindingPathSetHash
// ===========================================================================

/// Port of `CConceptVariableBindingPathSetHashData`.
///
/// The per-concept-tag value of the hash: the localised + shared
/// `CVariableBindingPathSet*` pair.
#[derive(Debug, Clone, Copy)]
pub struct ConceptVariableBindingPathSetHashData {
    /// `CVariableBindingPathSet* mLocVariableBindingPathSet`.
    pub loc_variable_binding_path_set: VarBindingPathSetId,
    /// `CVariableBindingPathSet* mUseVariableBindingPathSet`.
    pub use_variable_binding_path_set: VarBindingPathSetId,
}

impl Default for ConceptVariableBindingPathSetHashData {
    fn default() -> Self {
        Self::new()
    }
}

impl ConceptVariableBindingPathSetHashData {
    /// Port of `CConceptVariableBindingPathSetHashData::CConceptVariableBindingPathSetHashData`
    /// (`mLoc… = mUse… = nullptr`).
    pub fn new() -> Self {
        ConceptVariableBindingPathSetHashData {
            loc_variable_binding_path_set: Id::NONE,
            use_variable_binding_path_set: Id::NONE,
        }
    }
}

/// Port of `CConceptVariableBindingPathSetHash`
/// (`: public CPROCESSHASH<cint64, CConceptVariableBindingPathSetHashData>`).
#[derive(Clone)]
pub struct ConceptVariableBindingPathSetHash {
    /// `CProcessContext* mProcessContext` (opaque; the real ctx is threaded).
    pub process_context: Cint64,
    /// the `CPROCESSHASH<cint64, …HashData>` base storage.
    pub map: HashMap<Cint64, ConceptVariableBindingPathSetHashData>,
    /// `CVariableBindingPathDescriptor* mLastVarBindDesLinker`.
    pub last_var_bind_des_linker: VarBindingPathDescriptorId,
}

impl Default for ConceptVariableBindingPathSetHash {
    fn default() -> Self {
        ConceptVariableBindingPathSetHash {
            process_context: INVALID,
            map: HashMap::new(),
            last_var_bind_des_linker: Id::NONE,
        }
    }
}

impl ConceptVariableBindingPathSetHash {
    /// Port of `CConceptVariableBindingPathSetHash::CConceptVariableBindingPathSetHash(CProcessContext*)`.
    pub fn new(process_context: Cint64) -> Self {
        ConceptVariableBindingPathSetHash {
            process_context,
            map: HashMap::new(),
            last_var_bind_des_linker: Id::NONE,
        }
    }

    /// Port of `initConceptVariableBindingPathSetHash`.
    ///
    /// `*this = *prevHash` (the QHash implicitly-shared assignment) → an eager
    /// clone; `clear()` otherwise.
    pub fn init_concept_variable_binding_path_set_hash(
        &mut self,
        prev_hash: Option<&ConceptVariableBindingPathSetHash>,
    ) -> &mut Self {
        if let Some(prev_hash) = prev_hash {
            self.map = prev_hash.map.clone();
            self.last_var_bind_des_linker = prev_hash.last_var_bind_des_linker;
        } else {
            self.last_var_bind_des_linker = Id::NONE;
            self.map.clear();
        }
        self
    }

    /// Port of `getLastVariableBindingDescriptionLinker`.
    pub fn get_last_variable_binding_description_linker(&self) -> VarBindingPathDescriptorId {
        self.last_var_bind_des_linker
    }

    /// Port of `setLastVariableBindingDescriptionLinker`.
    pub fn set_last_variable_binding_description_linker(
        &mut self,
        var_bind_des: VarBindingPathDescriptorId,
    ) -> &mut Self {
        self.last_var_bind_des_linker = var_bind_des;
        self
    }

    /// Port of `getVariableBindingPathSet(CConcept* concept, bool localize)`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: the hash is itself an arena element, so this
    /// is an associated function over `(ctx, this, …)` (the `add_variable_binding_path`
    /// precedent) — `this` and the freshly allocated `CVariableBindingPathSet` live
    /// in different arenas, so the borrows never overlap. The C++ `concept`
    /// argument is reduced to its `getConceptTag()` (`con_tag`).
    pub fn get_variable_binding_path_set(
        ctx: &mut ProcessContext,
        this: ConceptVariableBindingPathSetHashId,
        con_tag: Cint64,
        localize: bool,
    ) -> VarBindingPathSetId {
        if localize {
            // CConceptVariableBindingPathSetHashData& data = operator[](conTag);
            let (loc, use_) = {
                let hash = ctx.con_var_bind_path_set_hash_mut(this);
                let data = hash
                    .map
                    .entry(con_tag)
                    .or_insert_with(ConceptVariableBindingPathSetHashData::new);
                (
                    data.loc_variable_binding_path_set,
                    data.use_variable_binding_path_set,
                )
            };
            if loc.is_none() {
                // propBindSet = allocateAndConstruct(...); propBindSet->initVariableBindingPathSet(data.mUse…);
                let new_set = ctx.alloc_vbpath_set(VariableBindingPathSet::new(INVALID));
                if use_.is_some() {
                    // same-arena init-from-prev: lift `use_` out, init, restore (no Clone needed).
                    let taken = std::mem::replace(
                        ctx.vbpath_set_mut(use_),
                        VariableBindingPathSet::new(INVALID),
                    );
                    ctx.vbpath_set_mut(new_set)
                        .init_variable_binding_path_set(Some(&taken));
                    *ctx.vbpath_set_mut(use_) = taken;
                } else {
                    ctx.vbpath_set_mut(new_set)
                        .init_variable_binding_path_set(None);
                }
                // data.mUseVariableBindingPathSet = data.mLocVariableBindingPathSet = propBindSet;
                let data = ctx
                    .con_var_bind_path_set_hash_mut(this)
                    .map
                    .get_mut(&con_tag)
                    .unwrap();
                data.use_variable_binding_path_set = new_set;
                data.loc_variable_binding_path_set = new_set;
                new_set
            } else {
                use_
            }
        } else {
            // CConceptVariableBindingPathSetHashData data = value(conTag); return data.mUse…;
            ctx.con_var_bind_path_set_hash(this)
                .map
                .get(&con_tag)
                .map(|d| d.use_variable_binding_path_set)
                .unwrap_or(VarBindingPathSetId::NONE)
        }
    }
}

// ===========================================================================
// CConceptPropagationBindingSetHash
// ===========================================================================

/// Port of `CConceptPropagationBindingSetHashData`.
#[derive(Debug, Clone, Copy)]
pub struct ConceptPropagationBindingSetHashData {
    /// `CPropagationBindingSet* mLocPropBindingSet`.
    pub loc_prop_binding_set: PropagationBindingSetId,
    /// `CPropagationBindingSet* mUsePropBindingSet`.
    pub use_prop_binding_set: PropagationBindingSetId,
}

impl Default for ConceptPropagationBindingSetHashData {
    fn default() -> Self {
        Self::new()
    }
}

impl ConceptPropagationBindingSetHashData {
    /// Port of `CConceptPropagationBindingSetHashData::CConceptPropagationBindingSetHashData`.
    pub fn new() -> Self {
        ConceptPropagationBindingSetHashData {
            loc_prop_binding_set: Id::NONE,
            use_prop_binding_set: Id::NONE,
        }
    }
}

/// Port of `CConceptPropagationBindingSetHash`
/// (`: public CPROCESSHASH<cint64, CConceptPropagationBindingSetHashData>`).
#[derive(Clone)]
pub struct ConceptPropagationBindingSetHash {
    /// `CProcessContext* mProcessContext` (opaque).
    pub process_context: Cint64,
    /// the `CPROCESSHASH<cint64, …HashData>` base storage.
    pub map: HashMap<Cint64, ConceptPropagationBindingSetHashData>,
    /// `CPropagationBindingDescriptor* mLastPropagationBindingDescriptor`.
    pub last_propagation_binding_descriptor: PropagationBindingDescriptorId,
}

impl Default for ConceptPropagationBindingSetHash {
    fn default() -> Self {
        ConceptPropagationBindingSetHash {
            process_context: INVALID,
            map: HashMap::new(),
            last_propagation_binding_descriptor: Id::NONE,
        }
    }
}

impl ConceptPropagationBindingSetHash {
    /// Port of `CConceptPropagationBindingSetHash::CConceptPropagationBindingSetHash(CProcessContext*)`.
    pub fn new(process_context: Cint64) -> Self {
        ConceptPropagationBindingSetHash {
            process_context,
            map: HashMap::new(),
            last_propagation_binding_descriptor: Id::NONE,
        }
    }

    /// Port of `initConceptPropagationBindingSetHash`.
    pub fn init_concept_propagation_binding_set_hash(
        &mut self,
        prev_hash: Option<&ConceptPropagationBindingSetHash>,
    ) -> &mut Self {
        if let Some(prev_hash) = prev_hash {
            self.map = prev_hash.map.clone();
            self.last_propagation_binding_descriptor =
                prev_hash.last_propagation_binding_descriptor;
        } else {
            self.map.clear();
            self.last_propagation_binding_descriptor = Id::NONE;
        }
        self
    }

    /// Port of `getLastPropagationBindingDescriptor`.
    pub fn get_last_propagation_binding_descriptor(&self) -> PropagationBindingDescriptorId {
        self.last_propagation_binding_descriptor
    }

    /// Port of `setLastPropagationBindingDescriptor`.
    pub fn set_last_propagation_binding_descriptor(
        &mut self,
        prop_bind_des: PropagationBindingDescriptorId,
    ) -> &mut Self {
        self.last_propagation_binding_descriptor = prop_bind_des;
        self
    }

    /// Port of `getPropagationBindingSet(CConcept* concept, bool localize)`.
    ///
    /// W3b-DEFER[api]: the `localize` alloc branch constructs a `CPropagationBindingSet`,
    /// which is NOT yet ported (no arena). The control flow is preserved: the data
    /// is `operator[]`-localised exactly as in C++, but the allocate-and-init of the
    /// unported set is deferred — `mLoc`/`mUse` stay `Id::NONE` until the
    /// propagation-binding-set subsystem lands, so the localise branch returns the
    /// current (possibly null) `mUse`. The non-localise read is faithful.
    pub fn get_propagation_binding_set(
        ctx: &mut ProcessContext,
        this: ConceptPropagationBindingSetHashId,
        con_tag: Cint64,
        localize: bool,
    ) -> PropagationBindingSetId {
        if localize {
            let (loc, use_) = {
                let hash = ctx.con_prop_binding_set_hash_mut(this);
                let data = hash
                    .map
                    .entry(con_tag)
                    .or_insert_with(ConceptPropagationBindingSetHashData::new);
                (data.loc_prop_binding_set, data.use_prop_binding_set)
            };
            if loc.is_none() {
                // W3c (un-defer): propBindSet = allocateAndConstruct(...);
                // propBindSet->initPropagationBindingSet(data.mUsePropBindingSet);
                let new_set = ctx.alloc_prop_binding_set(PropagationBindingSet::new(INVALID));
                if use_.is_some() {
                    // same-arena init-from-prev: lift `use_` out, init, restore (no Clone needed).
                    let taken = std::mem::replace(
                        ctx.prop_binding_set_mut(use_),
                        PropagationBindingSet::new(INVALID),
                    );
                    PropagationBindingSet::init_propagation_binding_set_in_context(
                        ctx,
                        new_set,
                        Some(&taken),
                    );
                    *ctx.prop_binding_set_mut(use_) = taken;
                } else {
                    PropagationBindingSet::init_propagation_binding_set_in_context(
                        ctx, new_set, None,
                    );
                }
                // data.mUsePropBindingSet = data.mLocPropBindingSet = propBindSet;
                let data = ctx
                    .con_prop_binding_set_hash_mut(this)
                    .map
                    .get_mut(&con_tag)
                    .unwrap();
                data.use_prop_binding_set = new_set;
                data.loc_prop_binding_set = new_set;
                new_set
            } else {
                use_
            }
        } else {
            ctx.con_prop_binding_set_hash(this)
                .map
                .get(&con_tag)
                .map(|d| d.use_prop_binding_set)
                .unwrap_or(PropagationBindingSetId::NONE)
        }
    }
}
