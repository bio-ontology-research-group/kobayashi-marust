//! `cache::backend` — F1, the **backend representative-memory association cache**
//! family (Konclude `Source/Reasoner/Kernel/Cache/CBackendRepresentativeMemoryCache*`,
//! manifest `07-cache.md` §F1). This is the largest cache family (~18–19k C++
//! lines, ~half the subtree): the realisation/association store holding, per
//! individual, its label associations (deterministic / nondeterministic concept
//! sets, role-set neighbours, same-as mergings), cardinalities, and nominal
//! indirect connections, indexed per ontology + recomputation id.
//!
//! The completion engine reaches it only through the Algorithm-layer
//! `CIndividualNodeBackendCacheHandler` / `CBackendAssociationCacheHandler`
//! (markers in `completion::stubs`); this subtree provides the cache facade +
//! Reader + Writer + the WriteData payloads + the entry / context / flags / slot
//! storage those handlers drive.
//!
//! ## What this file is (struct-definition sub-wave only)
//!
//! STRUCT DEFINITIONS for the F1 **CORE** classes (the facade + Reader + Writer +
//! WriteData chain + contexts + caching-flags + utilities + slot-item), with
//! faithful fields and `new` / `Default` constructors. NO method bodies yet —
//! every real method body lands in the later `// W6-CACHE method-batch` (see
//! markers). The DEEP storage internals (ontology-data, individual-association
//! data, label / cardinality cache items, role-set-neighbour family, the ~13
//! temporary linker chains, the retrieval-coordination hash) live in the sibling
//! `cache/backend_data.rs`. The file is intentionally NOT wired into a `mod.rs`.
//!
//! ## License (per `PORT.md` §License note)
//!
//! Function-by-function translation of LGPLv3 Konclude source; the LGPL terms
//! attach to this ported module. Keep `konclude_ht/` self-contained and
//! LGPL-headed so the obligation stays scoped.
//!
//! ## Port conventions applied (PORT.md §44; manifest §Concurrency)
//!
//! * `CXxx*` pointer → typed arena `Id<T>` (`Id::NONE` == `nullptr`).
//! * intrusive `CLinkerBase` / `QList` / `QVector` chains → owned `Vec<Id>`,
//!   head-at-FRONT (the canonical CLinker convention, PORT.md §6).
//! * `QMutex` / `QSemaphore` / `QReadWriteLock` / `QAtomicInt` / `QAtomicPointer`
//!   → opaque `Cint64` `[threading]` — this whole subtree IS the shared-mutable
//!   surface; the Reader/Writer/Event split is the concurrency model. The first
//!   faithful port runs single-threaded (worker == writer, drains inline).
//! * pool / context allocators (`CMemoryPool*`, `CMemoryPoolContainer*`,
//!   `CNewAllocationMemoryPoolProvider*`, `CMemoryPoolContainerAllocationManager`)
//!   → opaque `Cint64` `[memory-pool]`.
//! * `CThread` base (Qt event-loop worker) → opaque `thread_base: Cint64`
//!   `[threading]`; `CContext` base carries no port-relevant data.
//! * **cross-family refs → opaque `Cint64`**: `CConcept` / `CRole` /
//!   `CIndividual` / `CConceptDescriptor` / `CConceptSaturationDescriptor` /
//!   `CDependencyTrackPoint` / `CDistinctHash` / `CIndividualMergingHash` /
//!   `CConfiguration` / `CWatchDog` / `CConcreteOntology` / `CCallbackData` are
//!   model/process/infra types referenced opaquely here.
//! * F0 shared types reuse the real ports: `CCacheValue` → `value::CacheValue`,
//!   `CCacheStatistics` → `value::CacheStatistics`, `CCacheEntryWriteData` →
//!   `value::CacheEntryWriteData`, `CBackendCache` → `base::BackendCache`.
//!
//! ## Record-families / enums formed here (manifest §Record-families)
//!
//! * `SlotItem<T>` — the cross-family generic open-addressing / reader-shared
//!   hash-slot (Backend / Signature / Reuse / OccurrenceUnsat-UpdateSlotItem
//!   collapse). Seeded here; the backend slot is `SlotItem<BackendSlotPayload>`.
//! * `CacheWriteData` — the F1 queued-write-payload union (the
//!   `*WriteData`/`*WriteTypesData` collapse, "one per facade").
//! * `BackendTempWriteRecord` — the ~13 `*Temporary*DataLinker` chains collapse;
//!   defined in `backend_data.rs` (it carries DEEP storage payloads).

#![allow(dead_code)]

use std::collections::HashMap;

use super::super::model::substrate::{Cint64, Id, INVALID};
use super::base::BackendCache;
use super::value::{
    CacheEntryWriteData, CacheStatistics, CacheValue, CacheValueIdentifier, CacheWriteDataType,
};

use super::backend_data::{
    BackendTempWriteRecordId, CardinalitySignatureResolveCacheItem, IndividualAssociationDataId,
    LabelCacheItemExtensionType, LabelCacheItemId, LabelCacheItemType,
    LabelSignatureResolveCacheItem, NominalIndividualIndirectConnectionDataId, OntologyDataId,
    RoleAssertionLinkerId,
};
use super::context::CacheContext;

// ===========================================================================
// F1 CORE arena id aliases (typed replacements for the `CXxx*` back-pointers).
// KONCLUDE-PORT-NOTE[ownership]: an `Arena<T>` for each lives in the eventual
// cache context; these alias the `Id<T>` that indexes it.
// ===========================================================================

/// `CBackendRepresentativeMemoryCache*`             → `BackendCacheId`.
pub type BackendCacheId = Id<BackendRepresentativeMemoryCache>;
/// `CBackendRepresentativeMemoryCacheReader*`       → `ReaderId`.
pub type ReaderId = Id<BackendRepresentativeMemoryCacheReader>;
/// `CBackendRepresentativeMemoryCacheWriter*`       → `WriterId`.
pub type WriterId = Id<BackendRepresentativeMemoryCacheWriter>;
/// `CBackendRepresentativeMemoryCacheLabelAssociationWriteData*` → `LabelAssociationWriteDataId`.
pub type LabelAssociationWriteDataId =
    Id<BackendRepresentativeMemoryCacheLabelAssociationWriteData>;
/// `CBackendRepresentativeMemoryCacheSlotItem*`     → `SlotItemId`.
pub type SlotItemId = Id<BackendRepresentativeMemoryCacheSlotItem>;
/// `CBackendRepresentativeMemoryCacheBaseContext*`  → `BaseContextId`.
pub type BaseContextId = Id<BackendRepresentativeMemoryCacheBaseContext>;
/// `CBackendRepresentativeMemoryCacheOntologyContext*` → `OntologyContextId`.
pub type OntologyContextId = Id<BackendRepresentativeMemoryCacheOntologyContext>;

// ===========================================================================
// CacheWriteData — the F1 queued-write-payload union (record-family collapse).
//
// KONCLUDE-PORT-NOTE[api]: the C++ F1 write-data classes form a 3-deep
// inheritance chain `CBackendRepresentativeMemoryCacheLabelAssociationWriteData :
// CBackendRepresentativeMemoryCacheWriteData : CBackendCacheWriteData :
// CCacheEntryWriteData`. Per manifest §Record-families ("~15 *WriteData →
// one CacheWriteData enum, or one per cache facade") the F1 leaves collapse to
// this tagged enum; the leaf payload structs are kept (they ARE the variant
// data) so the inheritance fields survive. The cross-family tag lives in
// `value::CacheWriteDataType` (`BackendAssociationWriteDataType = 3`).
// ===========================================================================

/// Port of the F1 `*WriteData` family as a tagged union (the queued write
/// payload the facade's `writeCachedData` consumes).
#[derive(Debug, Clone)]
pub enum CacheWriteData {
    /// `CBackendRepresentativeMemoryCacheWriteData` (the bare ontology-id payload).
    Representative(BackendRepresentativeMemoryCacheWriteData),
    /// `CBackendRepresentativeMemoryCacheLabelAssociationWriteData` (the concrete
    /// label/association write payload — the 7 temp-linker heads + recomputation id).
    LabelAssociation(BackendRepresentativeMemoryCacheLabelAssociationWriteData),
}

/// `CacheWriteData*` → `CacheWriteDataId`.
pub type CacheWriteDataId = Id<CacheWriteData>;

// ===========================================================================
// CBackendCacheWriteData : CCacheEntryWriteData   (F1 spine marker)
// ===========================================================================

/// Port of `CBackendCacheWriteData` (`: public CCacheEntryWriteData`).
/// No own fields; the base discriminant lives in `CacheEntryWriteData`.
#[derive(Debug, Default, Clone)]
pub struct BackendCacheWriteData {
    /// Inlined `CCacheEntryWriteData` base (F0, `value.rs`).
    pub base: CacheEntryWriteData,
}

impl BackendCacheWriteData {
    /// Port of `CBackendCacheWriteData::CBackendCacheWriteData`.
    pub fn new() -> Self {
        Self::default()
    }
    // Port of `CBackendCacheWriteData`: the C++ class declares ONLY the (empty)
    // constructor and a virtual destructor — there are no further method bodies.
}

// ===========================================================================
// CBackendRepresentativeMemoryCacheWriteData : CBackendCacheWriteData
// ===========================================================================

/// Port of `CBackendRepresentativeMemoryCacheWriteData`.
#[derive(Debug, Default, Clone)]
pub struct BackendRepresentativeMemoryCacheWriteData {
    /// Inlined `CBackendCacheWriteData` base.
    pub base: BackendCacheWriteData,
    /// `cint64 mOntologyIdentifier`.
    pub ontology_identifier: Cint64,
}

impl BackendRepresentativeMemoryCacheWriteData {
    /// Port of `CBackendRepresentativeMemoryCacheWriteData::CBackendRepresentativeMemoryCacheWriteData`
    /// (`mOntologyIdentifier = 0;`).
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `CBackendRepresentativeMemoryCacheWriteData::getOntologyIdentifier`.
    pub fn get_ontology_identifier(&self) -> Cint64 {
        self.ontology_identifier
    }

    /// Port of `CBackendRepresentativeMemoryCacheWriteData::setOntologyIdentifier`
    /// (C++ returns `this` → `&mut Self`).
    pub fn set_ontology_identifier(&mut self, identifier: Cint64) -> &mut Self {
        self.ontology_identifier = identifier;
        self
    }
}

// ===========================================================================
// CBackendRepresentativeMemoryCacheLabelAssociationWriteData
//   (: CBackendRepresentativeMemoryCacheWriteData)
// ===========================================================================

/// Port of `CBackendRepresentativeMemoryCacheLabelAssociationWriteData`.
///
/// The concrete write payload: it gathers the per-update temporary linker chains
/// (association / label / cardinality / association-use / nominal-indirect /
/// involved-individual / propagation-cut) the writer installs into the cache,
/// plus the recomputation id this batch was produced under.
///
/// KONCLUDE-PORT-NOTE[ownership]: each `CBackendRepresentativeMemoryCacheTemporary*
/// DataLinker*` head → the collapsed `BackendTempWriteRecord` chain
/// (`Vec<BackendTempWriteRecordId>`, head-front; the records discriminate which
/// chain they belong to).
#[derive(Debug, Default, Clone)]
pub struct BackendRepresentativeMemoryCacheLabelAssociationWriteData {
    /// Inlined `CBackendRepresentativeMemoryCacheWriteData` base.
    pub base: BackendRepresentativeMemoryCacheWriteData,

    /// `CBackendRepresentativeMemoryCacheTemporaryAssociationWriteDataLinker* mTempAssWriteDataLinker`.
    pub temp_ass_write_data_linker: Vec<BackendTempWriteRecordId>,
    /// `CBackendRepresentativeMemoryCacheTemporaryLabelWriteDataLinker* mTempLabelWriteDataLinker`.
    pub temp_label_write_data_linker: Vec<BackendTempWriteRecordId>,
    /// `CBackendRepresentativeMemoryCacheTemporaryCardinalityWriteDataLinker* mTempCardWriteDataLinker`.
    pub temp_card_write_data_linker: Vec<BackendTempWriteRecordId>,
    /// `CBackendRepresentativeMemoryCacheTemporaryAssociationUseDataLinker* mTempAssUseDataLinker`.
    pub temp_ass_use_data_linker: Vec<BackendTempWriteRecordId>,
    /// `CBackendRepresentativeMemoryCacheTemporaryNominalIndirectConnectionDataLinker* mTempNomIndirectConnDataLinker`.
    pub temp_nom_indirect_conn_data_linker: Vec<BackendTempWriteRecordId>,
    /// `CBackendRepresentativeMemoryCacheTemporaryInvolvedIndividualDataLinker* mInvolvedIndiDataLinker`.
    pub involved_indi_data_linker: Vec<BackendTempWriteRecordId>,
    /// `CBackendRepresentativeMemoryCacheTemporaryPropagationCutDataLinker* mPropCutDataLinker`.
    pub prop_cut_data_linker: Vec<BackendTempWriteRecordId>,

    /// `cint64 mRecompuationId`.
    pub recompuation_id: Cint64,
}

impl BackendRepresentativeMemoryCacheLabelAssociationWriteData {
    /// Port of `CBackendRepresentativeMemoryCacheLabelAssociationWriteData::CBackendRepresentativeMemoryCacheLabelAssociationWriteData`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `CBackendRepresentativeMemoryCacheLabelAssociationWriteData::initWriteData`.
    /// C++ returns `this` → `&mut Self`. The 7 `CBackendRepresentativeMemoryCacheTemporary*
    /// DataLinker*` chain heads → the collapsed `Vec<BackendTempWriteRecordId>` chains
    /// (head-front). `mType = BACKENDASSOCIATIONWRITEDATATYPE` writes the inherited
    /// `CCacheEntryWriteData` discriminant; `mOntologyIdentifier` the
    /// `CBackendRepresentativeMemoryCacheWriteData` base.
    pub fn init_write_data(
        &mut self,
        ontology_identifier: Cint64,
        temp_ass_write_data_linker: Vec<BackendTempWriteRecordId>,
        temp_nom_indirect_conn_data_linker: Vec<BackendTempWriteRecordId>,
        temp_ass_use_data_linker: Vec<BackendTempWriteRecordId>,
        temp_label_write_data_linker: Vec<BackendTempWriteRecordId>,
        temp_card_write_data_linker: Vec<BackendTempWriteRecordId>,
        involved_indi_data_linker: Vec<BackendTempWriteRecordId>,
        prop_cut_data_linker: Vec<BackendTempWriteRecordId>,
        rep_comp_id: Cint64,
    ) -> &mut Self {
        self.temp_ass_use_data_linker = temp_ass_use_data_linker;
        self.temp_ass_write_data_linker = temp_ass_write_data_linker;
        self.temp_label_write_data_linker = temp_label_write_data_linker;
        self.temp_card_write_data_linker = temp_card_write_data_linker;
        self.temp_nom_indirect_conn_data_linker = temp_nom_indirect_conn_data_linker;
        self.involved_indi_data_linker = involved_indi_data_linker;
        self.base.base.base.type_ = CacheWriteDataType::BackendAssociationWriteDataType;
        self.base.ontology_identifier = ontology_identifier;
        self.prop_cut_data_linker = prop_cut_data_linker;
        self.recompuation_id = rep_comp_id;
        self
    }

    /// Port of `getTemporaryAssociationWriteDataLinker` (the chain head → slice).
    pub fn get_temporary_association_write_data_linker(&self) -> &[BackendTempWriteRecordId] {
        &self.temp_ass_write_data_linker
    }

    /// Port of `getTemporaryLabelWriteDataLinker`.
    pub fn get_temporary_label_write_data_linker(&self) -> &[BackendTempWriteRecordId] {
        &self.temp_label_write_data_linker
    }

    /// Port of `getTemporaryCardinaltyWriteDataLinker` (C++ spelling preserved).
    pub fn get_temporary_cardinalty_write_data_linker(&self) -> &[BackendTempWriteRecordId] {
        &self.temp_card_write_data_linker
    }

    /// Port of `getTemporaryAssociationUseDataLinker`.
    pub fn get_temporary_association_use_data_linker(&self) -> &[BackendTempWriteRecordId] {
        &self.temp_ass_use_data_linker
    }

    /// Port of `getTemporaryNominalIndirectConnectionDataLinker`.
    pub fn get_temporary_nominal_indirect_connection_data_linker(
        &self,
    ) -> &[BackendTempWriteRecordId] {
        &self.temp_nom_indirect_conn_data_linker
    }

    /// Port of `getTemporaryInvolvedIndividualIdDataLinker`.
    pub fn get_temporary_involved_individual_id_data_linker(&self) -> &[BackendTempWriteRecordId] {
        &self.involved_indi_data_linker
    }

    /// Port of `getTemporaryPropagationCutDataLinker`.
    pub fn get_temporary_propagation_cut_data_linker(&self) -> &[BackendTempWriteRecordId] {
        &self.prop_cut_data_linker
    }

    /// Port of `getRecompuationId` (C++ spelling preserved).
    pub fn get_recompuation_id(&self) -> Cint64 {
        self.recompuation_id
    }
}

// ===========================================================================
// CBackendRepresentativeMemoryCacheContext : CContext   (abstract)
// CBackendRepresentativeMemoryCacheBaseContext  / *OntologyContext  (concrete)
// ===========================================================================

/// Port of `CBackendRepresentativeMemoryCacheContext` (`: public CContext`).
/// Abstract base (pure-virtual `getMemoryAllocationManager` /
/// `getMemoryPoolProvider`); no member variables.
#[derive(Debug, Default, Clone)]
pub struct BackendRepresentativeMemoryCacheContext;

impl BackendRepresentativeMemoryCacheContext {
    /// Port of `CBackendRepresentativeMemoryCacheContext::CBackendRepresentativeMemoryCacheContext`.
    pub fn new() -> Self {
        Self
    }
    // Port of `CBackendRepresentativeMemoryCacheContext`: abstract base — its only
    // declared methods (`getMemoryAllocationManager` / `getMemoryPoolProvider`) are
    // pure-virtual (`= 0`); the concrete bodies live on the Base/Ontology contexts.
}

/// Port of `CBackendRepresentativeMemoryCacheBaseContext`
/// (`: public CBackendRepresentativeMemoryCacheContext`).
///
/// The cache-wide allocation context (owns the new-allocation pool provider).
#[derive(Debug, Clone)]
pub struct BackendRepresentativeMemoryCacheBaseContext {
    /// Inlined `CBackendRepresentativeMemoryCacheContext` base.
    pub base: BackendRepresentativeMemoryCacheContext,
    /// `CMemoryPoolAllocationManager* mMemMan`.  [memory-pool] → opaque.
    pub mem_man: Cint64,
    /// `CNewAllocationMemoryPoolProvider* mMemoryPoolProvider`.  [memory-pool] → opaque.
    pub memory_pool_provider: Cint64,
    /// `cint64 mAddRelMemory`.
    pub add_rel_memory: Cint64,
}

impl Default for BackendRepresentativeMemoryCacheBaseContext {
    fn default() -> Self {
        BackendRepresentativeMemoryCacheBaseContext {
            base: BackendRepresentativeMemoryCacheContext::new(),
            mem_man: INVALID,
            memory_pool_provider: INVALID,
            add_rel_memory: 0,
        }
    }
}

impl BackendRepresentativeMemoryCacheBaseContext {
    /// Port of `CBackendRepresentativeMemoryCacheBaseContext::CBackendRepresentativeMemoryCacheBaseContext`.
    /// KONCLUDE-PORT-NOTE[memory-pool]: the C++ ctor news a `CNewAllocationMemoryPoolProvider`
    /// + a `CLimitedReserveMemoryPoolAllocationManager` over it; both are opaque handles
    /// in the port (`Default` leaves them `INVALID`), so this is the `mAddRelMemory = 0`
    /// remainder.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `CBackendRepresentativeMemoryCacheBaseContext::getMemoryPoolAllocationManager`.
    /// [memory-pool] opaque `mMemMan` handle.
    pub fn get_memory_pool_allocation_manager(&self) -> Cint64 {
        self.mem_man
    }

    /// Port of `CBackendRepresentativeMemoryCacheBaseContext::getMemoryAllocationManager`
    /// (`return mMemMan;`).
    pub fn get_memory_allocation_manager(&self) -> Cint64 {
        self.mem_man
    }

    /// Port of `CBackendRepresentativeMemoryCacheBaseContext::getMemoryPoolProvider`.
    pub fn get_memory_pool_provider(&self) -> Cint64 {
        self.memory_pool_provider
    }

    /// Port of `CBackendRepresentativeMemoryCacheBaseContext::getMemoryConsumption`
    /// (`return mAddRelMemory + mMemoryPoolProvider->getAllocatedReleaseDifferencePoolSize();`).
    /// KONCLUDE-PORT-NOTE[memory-pool]: the provider's allocated/released pool-size
    /// difference is read from the opaque pool provider; W6-DEFER until the pool
    /// provider is ported, so only the tracked `mAddRelMemory` term is returned.
    pub fn get_memory_consumption(&self) -> Cint64 {
        // W6-DEFER[memory-pool]: + memory_pool_provider.get_allocated_release_difference_pool_size().
        self.add_rel_memory
    }

    /// Port of `CBackendRepresentativeMemoryCacheBaseContext::releaseTemporaryMemoryPools`.
    /// C++ walks the `CMemoryPool*` chain adding each block's size to `mAddRelMemory`,
    /// then forwards the chain to `mMemMan->releaseTemporaryMemoryPools`.
    /// KONCLUDE-PORT-NOTE[memory-pool]: the `CMemoryPool*` chain + the pool manager are
    /// opaque handles; the size-accumulation walk + manager release are deferred.
    /// C++ returns `this` → `&mut Self`.
    pub fn release_temporary_memory_pools(&mut self, _memory_pools: Cint64) -> &mut Self {
        // W6-DEFER[memory-pool]: faithful body sums getMemoryBlockSize() over the pool
        // chain into self.add_rel_memory, then mem_man.release_temporary_memory_pools(pools).
        self
    }
}

/// Port of `CBackendRepresentativeMemoryCacheOntologyContext`
/// (`: public CBackendRepresentativeMemoryCacheContext`).
///
/// A per-ontology(-data) allocation context layered over the base context's
/// pool container.
#[derive(Debug, Clone)]
pub struct BackendRepresentativeMemoryCacheOntologyContext {
    /// Inlined `CBackendRepresentativeMemoryCacheContext` base.
    pub base: BackendRepresentativeMemoryCacheContext,
    /// `CBackendRepresentativeMemoryCacheBaseContext* mCacheContext`.
    pub cache_context: BaseContextId,
    /// `CMemoryPoolContainerAllocationManager* mMemMan`.  [memory-pool] → opaque.
    pub mem_man: Cint64,
    /// `CMemoryPoolProvider* mMemoryPoolProvider`.  [memory-pool] → opaque.
    pub memory_pool_provider: Cint64,
    /// `cint64 mAddRelMemory`.
    pub add_rel_memory: Cint64,
    /// `CMemoryPoolContainer mMemPoolContainer` (by value).  [memory-pool] → opaque.
    pub mem_pool_container: Cint64,
}

impl Default for BackendRepresentativeMemoryCacheOntologyContext {
    fn default() -> Self {
        BackendRepresentativeMemoryCacheOntologyContext {
            base: BackendRepresentativeMemoryCacheContext::new(),
            cache_context: BaseContextId::NONE,
            mem_man: INVALID,
            memory_pool_provider: INVALID,
            add_rel_memory: 0,
            mem_pool_container: INVALID,
        }
    }
}

impl BackendRepresentativeMemoryCacheOntologyContext {
    /// Port of `CBackendRepresentativeMemoryCacheOntologyContext::CBackendRepresentativeMemoryCacheOntologyContext`
    /// `(CBackendRepresentativeMemoryCacheBaseContext* cacheContext)`.
    pub fn new(cache_context: BaseContextId) -> Self {
        BackendRepresentativeMemoryCacheOntologyContext {
            cache_context,
            ..Default::default()
        }
    }

    /// Port of `CBackendRepresentativeMemoryCacheOntologyContext::getMemoryAllocationManager`
    /// (`return mMemMan;`). [memory-pool] opaque container-allocation-manager handle.
    pub fn get_memory_allocation_manager(&self) -> Cint64 {
        self.mem_man
    }

    /// Port of `CBackendRepresentativeMemoryCacheOntologyContext::getMemoryPoolProvider`.
    pub fn get_memory_pool_provider(&self) -> Cint64 {
        self.memory_pool_provider
    }

    /// Port of `CBackendRepresentativeMemoryCacheOntologyContext::getMemoryPoolContainer`
    /// (`return &mMemPoolContainer;`). [memory-pool] opaque by-value container handle.
    pub fn get_memory_pool_container(&self) -> Cint64 {
        self.mem_pool_container
    }
}

// ===========================================================================
// CBackendRepresentativeMemoryCachingFlags
// ===========================================================================

/// Port of `CBackendRepresentativeMemoryCachingFlags`.
///
/// A small status-flag bitset (completely-handled / -saturated / -propagated /
/// has-nondeterministic-elements) mixed into the individual-association data and
/// label cache items.
#[derive(Debug, Default, Clone, Copy)]
pub struct BackendRepresentativeMemoryCachingFlags {
    /// `cint64 mStatusFlags`.
    pub status_flags: Cint64,
}

impl BackendRepresentativeMemoryCachingFlags {
    /// `FLAG_COMPLETELY_HANDLED = 0x0001`.
    pub const FLAG_COMPLETELY_HANDLED: Cint64 = 0x0001;
    /// `FLAG_COMPLETELY_SATURATED = 0x0002`.
    pub const FLAG_COMPLETELY_SATURATED: Cint64 = 0x0002;
    /// `FLAG_COMPLETELY_PROPAGATED = 0x0004`.
    pub const FLAG_COMPLETELY_PROPAGATED: Cint64 = 0x0004;
    /// `FLAG_NONDETERMINISTIC_ELEMENTS = 0x0008`.
    pub const FLAG_NONDETERMINISTIC_ELEMENTS: Cint64 = 0x0008;

    /// Port of `CBackendRepresentativeMemoryCachingFlags::CBackendRepresentativeMemoryCachingFlags`
    /// (`mStatusFlags = 0;`).
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `initCachingStatusFlags(cint64 flags = 0)`. C++ returns `this` → `&mut Self`.
    pub fn init_caching_status_flags(&mut self, flags: Cint64) -> &mut Self {
        self.status_flags = flags;
        self
    }

    /// Port of `isCompletelyHandled` (`return hasStatusFlags(FLAG_COMPLETELY_HANDLED);`).
    pub fn is_completely_handled(&self) -> bool {
        self.has_status_flags(Self::FLAG_COMPLETELY_HANDLED)
    }

    /// Port of `setCompletelyHandled`. C++ returns `this` → `&mut Self`.
    pub fn set_completely_handled(&mut self, completely_handled: bool) -> &mut Self {
        if completely_handled {
            self.add_status_flags(Self::FLAG_COMPLETELY_HANDLED);
        } else {
            self.clear_status_flags(Self::FLAG_COMPLETELY_HANDLED);
        }
        self
    }

    /// Port of `isCompletelySaturated`.
    pub fn is_completely_saturated(&self) -> bool {
        self.has_status_flags(Self::FLAG_COMPLETELY_SATURATED)
    }

    /// Port of `setCompletelySaturated`. C++ returns `this` → `&mut Self`.
    pub fn set_completely_saturated(&mut self, completely_saturated: bool) -> &mut Self {
        if completely_saturated {
            self.add_status_flags(Self::FLAG_COMPLETELY_SATURATED);
        } else {
            self.clear_status_flags(Self::FLAG_COMPLETELY_SATURATED);
        }
        self
    }

    /// Port of `isCompletelyPropagated`.
    pub fn is_completely_propagated(&self) -> bool {
        self.has_status_flags(Self::FLAG_COMPLETELY_PROPAGATED)
    }

    /// Port of `setCompletelyPropagated`. C++ returns `this` → `&mut Self`.
    pub fn set_completely_propagated(&mut self, completely_propagated: bool) -> &mut Self {
        if completely_propagated {
            self.add_status_flags(Self::FLAG_COMPLETELY_PROPAGATED);
        } else {
            self.clear_status_flags(Self::FLAG_COMPLETELY_PROPAGATED);
        }
        self
    }

    /// Port of `hasNondeterministicElements`.
    pub fn has_nondeterministic_elements(&self) -> bool {
        self.has_status_flags(Self::FLAG_NONDETERMINISTIC_ELEMENTS)
    }

    /// Port of `setNondeterministicElements`. C++ returns `this` → `&mut Self`.
    pub fn set_nondeterministic_elements(&mut self, nondeterministic_elements: bool) -> &mut Self {
        if nondeterministic_elements {
            self.add_status_flags(Self::FLAG_NONDETERMINISTIC_ELEMENTS);
        } else {
            self.clear_status_flags(Self::FLAG_NONDETERMINISTIC_ELEMENTS);
        }
        self
    }

    /// Port of `hasStatusFlags` (`return (mStatusFlags & flags) == flags;`).
    pub fn has_status_flags(&self, flags: Cint64) -> bool {
        (self.status_flags & flags) == flags
    }

    /// Port of `hasStatusFlagsPartially` (`return (mStatusFlags & flags) != 0;`).
    pub fn has_status_flags_partially(&self, flags: Cint64) -> bool {
        (self.status_flags & flags) != 0
    }

    /// Port of `setStatusFlags` (`mStatusFlags = flags;`). C++ returns `this`.
    pub fn set_status_flags(&mut self, flags: Cint64) -> &mut Self {
        self.status_flags = flags;
        self
    }

    /// Port of `addStatusFlags` (`mStatusFlags |= flags;`). C++ returns `this`.
    pub fn add_status_flags(&mut self, flags: Cint64) -> &mut Self {
        self.status_flags |= flags;
        self
    }

    /// Port of `clearStatusFlags` (`mStatusFlags &= ~flags;`). C++ returns `this`.
    pub fn clear_status_flags(&mut self, flags: Cint64) -> &mut Self {
        self.status_flags &= !flags;
        self
    }

    /// Port of `getStatusFlags`.
    pub fn get_status_flags(&self) -> Cint64 {
        self.status_flags
    }
}

// ===========================================================================
// CBackendRepresentativeMemoryCacheUtilities  (static signature helpers)
// ===========================================================================

/// Port of `CBackendRepresentativeMemoryCacheUtilities`.
/// All methods are `static` signature/hashing helpers; no member variables.
#[derive(Debug, Default, Clone, Copy)]
pub struct BackendRepresentativeMemoryCacheUtilities;

/// Slice element for the `CIndividualMergingHash*` overloads used by the backend
/// reader. It carries exactly the fields those C++ overloads inspect.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IndividualMergingHashEntry {
    pub individual_id: Cint64,
    pub merged_with_individual: bool,
    pub dependency_branch_tag: Option<Cint64>,
}

impl IndividualMergingHashEntry {
    pub fn new(
        individual_id: Cint64,
        merged_with_individual: bool,
        dependency_branch_tag: Option<Cint64>,
    ) -> Self {
        Self {
            individual_id,
            merged_with_individual,
            dependency_branch_tag,
        }
    }

    fn is_deterministically_derived(&self, max_deterministic_branch_tag: Cint64) -> bool {
        self.dependency_branch_tag
            .is_some_and(|tag| tag <= max_deterministic_branch_tag)
    }
}

/// Slice element for the `CDistinctHash*` overloads. Konclude stores the
/// distinct individual as `-it.key()`, so the port keeps the original hash key.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DistinctHashEntry {
    pub hash_key: Cint64,
    pub dependency_branch_tag: Option<Cint64>,
}

impl DistinctHashEntry {
    pub fn new(hash_key: Cint64, dependency_branch_tag: Option<Cint64>) -> Self {
        Self {
            hash_key,
            dependency_branch_tag,
        }
    }

    pub fn distinct_individual_id(&self) -> Cint64 {
        -self.hash_key
    }

    fn is_deterministically_derived(&self, max_deterministic_branch_tag: Cint64) -> bool {
        self.dependency_branch_tag
            .is_some_and(|tag| tag <= max_deterministic_branch_tag)
    }
}

/// Slice element for `CConceptDescriptor*` and `CConceptSaturationDescriptor*`
/// overloads. It carries exactly the concept fields the backend cache reader
/// inspects.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ConceptDescriptorRecord {
    pub concept_id: Cint64,
    pub concept_tag: Cint64,
    pub negated: bool,
    pub dependency_branch_tag: Option<Cint64>,
    pub nominal: bool,
}

impl ConceptDescriptorRecord {
    pub fn new(
        concept_id: Cint64,
        concept_tag: Cint64,
        negated: bool,
        dependency_branch_tag: Option<Cint64>,
        nominal: bool,
    ) -> Self {
        Self {
            concept_id,
            concept_tag,
            negated,
            dependency_branch_tag,
            nominal,
        }
    }

    pub fn signed_tag(&self) -> Cint64 {
        if self.negated {
            -self.concept_tag
        } else {
            self.concept_tag
        }
    }

    fn is_deterministically_derived(&self, max_deterministic_branch_tag: Cint64) -> bool {
        self.dependency_branch_tag
            .is_some_and(|tag| tag <= max_deterministic_branch_tag)
    }
}

impl BackendRepresentativeMemoryCacheUtilities {
    /// Port of `CBackendRepresentativeMemoryCacheUtilities::CBackendRepresentativeMemoryCacheUtilities`.
    pub fn new() -> Self {
        Self
    }

    /// Port of `getConceptDescriptorSignature(CConceptSaturationDescriptor*, cint64 count, CConcept* exclusionConcept)`.
    /// Saturation descriptors use the same record; only concept id/tag/negation are read.
    pub fn get_concept_descriptor_signature_saturation(
        con_des_linker: &[ConceptDescriptorRecord],
        _count: Cint64,
        exclusion_concept: Cint64,
    ) -> Cint64 {
        let mut sig_value = 0;
        for con_des in con_des_linker {
            if con_des.negated || con_des.concept_id != exclusion_concept {
                let value = con_des.signed_tag() as u64;
                sig_value += ((value >> 31) ^ value) as u32 as Cint64;
            }
        }
        sig_value
    }

    /// Port of `getConceptDescriptorSignature(CConceptDescriptor*, cint64& count, bool deterministic,
    /// cint64 maxDeterministicBranchTag, bool excludePositiveNominalConcepts)`.
    /// Uses `ConceptDescriptorRecord` for the fields inspected by the C++ descriptor chain.
    pub fn get_concept_descriptor_signature(
        con_des_linker: &[ConceptDescriptorRecord],
        count: &mut Cint64,
        deterministic: bool,
        max_deterministic_branch_tag: Cint64,
        exclude_positive_nominal_concepts: bool,
    ) -> Cint64 {
        *count = 0;
        let mut sig_value = 0;
        for con_des in con_des_linker {
            let mut consider_concept =
                con_des.is_deterministically_derived(max_deterministic_branch_tag) == deterministic;
            if exclude_positive_nominal_concepts && con_des.nominal && !con_des.negated {
                consider_concept = false;
            }
            if consider_concept {
                let value = con_des.signed_tag() as u64;
                sig_value += ((value >> 31) ^ value) as u32 as Cint64;
                *count += 1;
            }
        }
        sig_value
    }

    /// Port of `getConceptDescriptorSignature(CConceptDescriptor*, cint64& count,
    /// function<bool(CConcept*, bool)> exclusionDetermineFunction)`.
    pub fn get_concept_descriptor_signature_with_exclusion(
        con_des_linker: &[ConceptDescriptorRecord],
        count: &mut Cint64,
        exclusion_determine_function: impl Fn(Cint64, bool) -> bool,
    ) -> Cint64 {
        *count = 0;
        let mut sig_value = 0;
        for con_des in con_des_linker {
            if exclusion_determine_function(con_des.concept_id, con_des.negated) {
                let value = con_des.signed_tag() as u64;
                sig_value += ((value >> 31) ^ value) as u32 as Cint64;
                *count += 1;
            }
        }
        sig_value
    }

    /// Port of `getConceptDescriptorSignature(CConceptDescriptor*, cint64& count,
    /// function<bool(CConcept*, bool)>, function<bool(CConcept*, bool, CDependencyTrackPoint*)>)`.
    pub fn get_concept_descriptor_signature_with_determinism(
        con_des_linker: &[ConceptDescriptorRecord],
        count: &mut Cint64,
        exclusion_determine_function: impl Fn(Cint64, bool) -> bool,
        deterministic_determine_function: impl Fn(Cint64, bool, Option<Cint64>) -> bool,
    ) -> Cint64 {
        *count = 0;
        let mut sig_value = 0;
        for con_des in con_des_linker {
            if exclusion_determine_function(con_des.concept_id, con_des.negated) {
                let _deterministic = deterministic_determine_function(
                    con_des.concept_id,
                    con_des.negated,
                    con_des.dependency_branch_tag,
                );
                let value = con_des.signed_tag() as u64;
                sig_value += ((value >> 31) ^ value) as u32 as Cint64;
                *count += 1;
            }
        }
        sig_value
    }

    /// Port of `getRoleInversedLinkerSignature(CSortedNegLinker<CRole*>*, bool inversed, cint64 count)`.
    /// The C++ sorted-neg linker is represented as `(role_tag, negated)` pairs.
    pub fn get_role_inversed_linker_signature(
        role_linker: &[(Cint64, bool)],
        inversed: bool,
        _count: Cint64,
    ) -> Cint64 {
        let mut sig_value = 0;
        for &(role, negated) in role_linker {
            let tag = if negated ^ inversed { -role } else { role };
            let value = tag as u64;
            sig_value += ((value >> 31) ^ value) as u32 as Cint64;
        }
        sig_value
    }

    /// Port of `getNeighbourRoleInstantiatedSetLinkerSignature(
    /// CBackendRepresentativeMemoryCacheTemporaryLabelReferenceDataLinker*, cint64 count)`.
    /// The C++ linker chain is represented by this port's head-front
    /// `Vec<BackendTempWriteRecordId>` convention.
    pub fn get_neighbour_role_instantiated_set_linker_signature(
        neighbour_role_set_linker: &[BackendTempWriteRecordId],
        _count: Cint64,
        cache_context: &mut CacheContext,
    ) -> Cint64 {
        let mut signature = 0;
        for &linker_id in neighbour_role_set_linker {
            if linker_id == BackendTempWriteRecordId::NONE {
                continue;
            }
            let linker = cache_context.backend_temp_write_record(linker_id);
            let tmp_label_write_data = linker.label_reference_get_referred_temporary_label_data();
            let label_cache_item = linker.label_reference_get_referred_label_data();
            let value = if tmp_label_write_data != BackendTempWriteRecordId::NONE {
                tmp_label_write_data.raw
            } else if label_cache_item != LabelCacheItemId::NONE {
                cache_context
                    .label_cache_item(label_cache_item)
                    .get_cache_entry_id()
            } else {
                0
            };
            let value = value as u64;
            signature += ((value >> 31) ^ value) as u32 as Cint64;
        }
        signature
    }

    /// Port of `getIndividualSetSignature(cint64 indiId, CIndividualMergingHash*, cint64& count,
    /// bool onlyDeterministic, cint64 maxDeterministicBranchTag)`.
    pub fn get_individual_set_signature_merging(
        indi_id: Cint64,
        indi_merging_hash: &[IndividualMergingHashEntry],
        count: &mut Cint64,
        only_deterministic: bool,
        max_deterministic_branch_tag: Cint64,
    ) -> Cint64 {
        *count = 0;
        let mut sig_value = 0;
        for entry in indi_merging_hash {
            let merged_indi_id = entry.individual_id;
            if merged_indi_id == indi_id || !entry.merged_with_individual {
                continue;
            }
            let consider_individual = entry
                .is_deterministically_derived(max_deterministic_branch_tag)
                || !only_deterministic;
            if consider_individual {
                let value = merged_indi_id as u64;
                sig_value += ((value >> 31) ^ value) as u32 as Cint64;
                *count += 1;
            }
        }
        if *count > 0 && indi_id >= 0 {
            let value = indi_id as u64;
            sig_value += ((value >> 31) ^ value) as u32 as Cint64;
            *count += 1;
        }
        sig_value
    }

    /// Port of `getIndividualSetSignature(CPROCESSSET<cint64>* individualSet, cint64& count)`.
    /// The C++ process set is represented as a slice because this overload only iterates ids.
    pub fn get_individual_set_signature_set(
        individual_set: &[Cint64],
        count: &mut Cint64,
    ) -> Cint64 {
        *count = 0;
        let mut sig_value = 0;
        for &indi_id in individual_set {
            let value = indi_id as u64;
            sig_value += ((value >> 31) ^ value) as u32 as Cint64;
            *count += 1;
        }
        sig_value
    }

    /// Port of `getIndividualSetSignature(cint64 indiId, CDistinctHash*, cint64& count,
    /// bool onlyDeterministic, cint64 maxDeterministicBranchTag)`.
    pub fn get_individual_set_signature_distinct(
        indi_id: Cint64,
        indi_distinct_hash: &[DistinctHashEntry],
        count: &mut Cint64,
        only_deterministic: bool,
        max_deterministic_branch_tag: Cint64,
    ) -> Cint64 {
        *count = 0;
        let mut sig_value = 0;
        for entry in indi_distinct_hash {
            let distinct_indi_id = entry.distinct_individual_id();
            if distinct_indi_id < 0 || distinct_indi_id == indi_id {
                continue;
            }
            let consider_individual = entry
                .is_deterministically_derived(max_deterministic_branch_tag)
                || !only_deterministic;
            if consider_individual {
                let value = distinct_indi_id as u64;
                sig_value += ((value >> 31) ^ value) as u32 as Cint64;
                *count += 1;
            }
        }
        if *count > 0 && indi_id >= 0 {
            let value = indi_id as u64;
            sig_value += ((value >> 31) ^ value) as u32 as Cint64;
            *count += 1;
        }
        sig_value
    }

    /// Port of `getSignatureExtensionByCacheValue(cint64 signature, CCacheValue& cacheValue)`
    /// (`signature += qHash((qint64)cacheValue.getTag()); return signature;`).
    /// KONCLUDE-PORT-NOTE[api]: `qHash(qint64)` reproduces Qt5's fold — the same leaf math
    /// `value::CacheValue::q_hash` uses (`((k >> 31) ^ k)` truncated to 32 bits); kept inline
    /// since that helper is private to `value`.
    pub fn get_signature_extension_by_cache_value(
        signature: Cint64,
        cache_value: &CacheValue,
    ) -> Cint64 {
        let tag = cache_value.get_tag() as u64;
        let h = ((tag >> 31) ^ tag) as u32 as Cint64;
        signature + h
    }
}

// ===========================================================================
// SlotItem<T>  — cross-family generic reader-shared hash-slot
//   (Backend / Signature / Reuse / OccurrenceUnsat-UpdateSlotItem collapse).
// ===========================================================================

/// Port of the `*SlotItem` record family as a generic versioned, reader-shared
/// storage slot (manifest §Record-families).
///
/// KONCLUDE-PORT-NOTE[ownership]: the C++ `CBackendRepresentativeMemoryCacheSlotItem`
/// is `: CMemoryPoolContainer, CLinkerBase<...>` — the slot chain is collapsed to
/// an owned `Vec<SlotItemId>` on the cache facade (head-front), so the `CLinkerBase`
/// next-pointer is dropped; the `CMemoryPoolContainer` base is the opaque
/// `mem_pool_container` handle.
/// KONCLUDE-PORT-NOTE[threading]: `QAtomicInt mReaderSharingCount` → opaque
/// `Cint64` (CAS reader-share count).
#[derive(Debug, Clone)]
pub struct SlotItem<T> {
    /// The slot's stored payload (per family). For F1 backend this is the
    /// `CCACHINGHASH<cint64, CBackendRepresentativeMemoryCacheOntologyData*>*`
    /// ontology-identifier → ontology-data map (`BackendSlotPayload`).
    pub payload: T,
    /// `QAtomicInt mReaderSharingCount`.  [threading] → opaque.
    pub reader_sharing_count: Cint64,
    /// `bool mReaderUsing`.
    pub reader_using: bool,
    /// `CMemoryPoolContainer` base.  [memory-pool] → opaque.
    pub mem_pool_container: Cint64,
}

impl<T: Default> Default for SlotItem<T> {
    fn default() -> Self {
        SlotItem {
            payload: T::default(),
            reader_sharing_count: 0,
            reader_using: false,
            mem_pool_container: INVALID,
        }
    }
}

impl<T: Default> SlotItem<T> {
    /// Port of `CBackendRepresentativeMemoryCacheSlotItem::CBackendRepresentativeMemoryCacheSlotItem`
    /// (`mReaderUsing = false; mOntologyIdentifierDataHash = nullptr;`).
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `incReader()`. KONCLUDE-PORT-NOTE[threading]: `QAtomicInt::ref()`
    /// (atomic ++, returns "new value != 0") → single-threaded `+= 1` then the
    /// non-zero test.
    pub fn inc_reader(&mut self) -> bool {
        self.reader_sharing_count += 1;
        if self.reader_sharing_count != 0 {
            self.reader_using = true;
        }
        true
    }

    /// Port of `incReader(cint64 incCount)`.
    pub fn inc_reader_count(&mut self, inc_count: Cint64) -> bool {
        for _ in 0..inc_count {
            self.inc_reader();
        }
        self.reader_using
    }

    /// Port of `decReader()`. KONCLUDE-PORT-NOTE[threading]: `QAtomicInt::deref()`
    /// (atomic --, returns "new value != 0"); `!deref()` ⇒ new value == 0.
    pub fn dec_reader(&mut self) -> bool {
        self.reader_sharing_count -= 1;
        if self.reader_sharing_count == 0 {
            self.reader_using = false;
        }
        self.reader_using
    }

    /// Port of `hasCacheReaders()` (`return mReaderUsing;`).
    pub fn has_cache_readers(&self) -> bool {
        self.reader_using
    }
}

// The payload-specific slot methods (the backend ontology-id → ontology-data hash).
impl SlotItem<BackendSlotPayload> {
    /// Port of `CBackendRepresentativeMemoryCacheSlotItem::getOntologyData(cint64 ontologyIdentifier)`.
    /// C++ guards on a null `mOntologyIdentifierDataHash`; in the port the payload IS the
    /// hash (always present), and `QHash::value(key)` of an absent key → `nullptr` ==
    /// `OntologyDataId::NONE`.
    pub fn get_ontology_data(&self, ontology_identifier: Cint64) -> OntologyDataId {
        self.payload
            .get(&ontology_identifier)
            .copied()
            .unwrap_or(OntologyDataId::NONE)
    }

    /// Port of `getOntologyIdentifierDataHash()` (`return mOntologyIdentifierDataHash;`).
    pub fn get_ontology_identifier_data_hash(&self) -> &BackendSlotPayload {
        &self.payload
    }

    /// Port of `setOntologyIdentifierDataHash(...)`. C++ stores the hash pointer; the
    /// port moves the owned map into the slot payload. KONCLUDE-PORT-NOTE[ownership]:
    /// C++ shares one hash by pointer across slots — the by-value move drops that
    /// sharing (faithful single-thread staging). C++ returns `this` → `&mut Self`.
    pub fn set_ontology_identifier_data_hash(
        &mut self,
        ont_id_data_hash: BackendSlotPayload,
    ) -> &mut Self {
        self.payload = ont_id_data_hash;
        self
    }
}

/// The F1 backend slot payload: `CCACHINGHASH<cint64, OntologyData*>` →
/// `HashMap<cint64, OntologyDataId>` (the per-ontology data map snapshot).
pub type BackendSlotPayload = HashMap<Cint64, OntologyDataId>;
/// `CBackendRepresentativeMemoryCacheSlotItem` → `SlotItem<BackendSlotPayload>`.
pub type BackendRepresentativeMemoryCacheSlotItem = SlotItem<BackendSlotPayload>;

// ===========================================================================
// CBackendRepresentativeMemoryCacheReader  (: CLinkerBase<...>)
// ===========================================================================

/// Port of `CBackendRepresentativeMemoryCacheReader`.
///
/// The per-thread read cursor over the F1 cache: it pins a slot (atomically
/// republished on update), resolves an ontology + recomputation id, and answers
/// the (very many) label/association/neighbour/cardinality lookup queries the
/// completion engine issues. Holds two empty signature-resolve cache items by
/// value as reusable lookup scratch.
///
/// KONCLUDE-PORT-NOTE[ownership]: the `CLinkerBase` next-pointer (the cache owns
/// its readers in `mReaderLinker`) is dropped.
#[derive(Debug, Clone)]
pub struct BackendRepresentativeMemoryCacheReader {
    /// `CBackendRepresentativeMemoryCacheSlotItem* mCurrentSlot`.
    pub current_slot: SlotItemId,
    /// `QAtomicPointer<CBackendRepresentativeMemoryCacheSlotItem> mUpdatedSlot`.
    /// Atomically published `SlotItemId`.
    pub updated_slot: SlotItemId,

    /// `CBackendRepresentativeMemoryLabelSignatureResolveCacheItem mEmptySigResCacheItem` (by value).
    pub empty_sig_res_cache_item: LabelSignatureResolveCacheItem,
    /// `CBackendRepresentativeMemoryCardinalitySignatureResolveCacheItem mEmptyCardSigResCacheItem` (by value).
    pub empty_card_sig_res_cache_item: CardinalitySignatureResolveCacheItem,

    /// `cint64 mOntologyIdentifier`.
    pub ontology_identifier: Cint64,
    /// `cint64 mRecomputationId`.
    pub recomputation_id: Cint64,
    /// `CBackendRepresentativeMemoryCacheOntologyData* mOntologyData`.
    pub ontology_data: OntologyDataId,
    /// `CBackendRepresentativeMemoryCacheOntologyData* mFixedOntologyData`.
    pub fixed_ontology_data: OntologyDataId,
}

impl Default for BackendRepresentativeMemoryCacheReader {
    fn default() -> Self {
        BackendRepresentativeMemoryCacheReader {
            current_slot: SlotItemId::NONE,
            updated_slot: SlotItemId::NONE,
            empty_sig_res_cache_item: LabelSignatureResolveCacheItem::default(),
            empty_card_sig_res_cache_item: CardinalitySignatureResolveCacheItem::default(),
            ontology_identifier: 0,
            recomputation_id: 0,
            ontology_data: OntologyDataId::NONE,
            fixed_ontology_data: OntologyDataId::NONE,
        }
    }
}

impl BackendRepresentativeMemoryCacheReader {
    /// Port of `CBackendRepresentativeMemoryCacheReader::CBackendRepresentativeMemoryCacheReader`
    /// (`mCurrentSlot = nullptr; mFixedOntologyData = nullptr; mOntologyData = nullptr;
    /// mRecomputationId = 0;`).
    pub fn new() -> Self {
        Self::default()
    }

    // -- slot / ontology-data pinning ------------------------------------------------
    //
    /// Port of `updateSlot(CBackendRepresentativeMemoryCacheSlotItem* updatedSlot)`.
    /// KONCLUDE-PORT-NOTE[threading]: `mUpdatedSlot.fetchAndStoreOrdered(updatedSlot)`
    /// becomes a single-threaded slot-id swap; the previously published slot loses
    /// this reader.
    pub fn update_slot(
        &mut self,
        updated_slot: SlotItemId,
        cache_context: &mut CacheContext,
    ) -> &mut Self {
        let prev_slot = self.updated_slot;
        self.updated_slot = updated_slot;
        if prev_slot.is_some() {
            cache_context.backend_slot_item_mut(prev_slot).dec_reader();
        }
        self
    }

    /// Port of `fixOntologyData(CBackendRepresentativeMemoryCacheOntologyData* ontologyData)`
    /// (`mFixedOntologyData = ontologyData; mOntologyData = ontologyData;`). C++ returns `this`.
    pub fn fix_ontology_data(&mut self, ontology_data: OntologyDataId) -> &mut Self {
        self.fixed_ontology_data = ontology_data;
        self.ontology_data = ontology_data;
        self
    }

    /// Port of `checkRecomputationIdUsage(cint64 recomputationId)`.
    /// KONCLUDE-PORT-NOTE[error]: Konclude throws
    /// `CCalculationErrorProcessingException::ECINVALIDRECOMPUATIONID` when the
    /// requested id is older than the ontology data permits. The Rust cache layer
    /// currently has no calculation-error type, so this keeps the same fail-fast
    /// guard as a panic.
    pub fn check_recomputation_id_usage(
        &mut self,
        recomputation_id: Cint64,
        cache_context: &mut CacheContext,
    ) -> &mut Self {
        self.recomputation_id = recomputation_id;
        if self.has_updated_slot_item() {
            self.switch_to_updated_slot_item_in_context(cache_context);
        }
        if self.ontology_data.is_none() && self.current_slot.is_some() {
            self.ontology_data = cache_context
                .backend_slot_item(self.current_slot)
                .get_ontology_data(self.ontology_identifier);
        }
        if self.ontology_data.is_some() {
            let min_valid = cache_context
                .ontology_data(self.ontology_data)
                .get_minimum_valid_recomputation_id();
            if recomputation_id < min_valid {
                panic!("invalid backend representative memory cache recomputation id");
            }
            let rec_ref = cache_context
                .ontology_data(self.ontology_data)
                .get_recomputation_reference_linker();
            if rec_ref.is_some() {
                cache_context
                    .ontology_data_recomp_ref_linker_mut(rec_ref)
                    .update_used_recomputation_id(recomputation_id);
            }
        }
        self
    }

    /// Port of `setWorkingOntology(cint64 ontologyIdentifier)`.
    /// C++ returns `this`.
    pub fn set_working_ontology_by_id(
        &mut self,
        ontology_identifier: Cint64,
        cache_context: &mut CacheContext,
    ) -> &mut Self {
        self.ontology_identifier = ontology_identifier;
        if self.has_updated_slot_item() {
            self.switch_to_updated_slot_item_in_context(cache_context);
        }
        self.ontology_data = OntologyDataId::NONE;
        if self.current_slot.is_some() {
            self.ontology_data = cache_context
                .backend_slot_item(self.current_slot)
                .get_ontology_data(self.ontology_identifier);
        }
        if self.fixed_ontology_data.is_some() {
            self.ontology_data = self.fixed_ontology_data;
        }
        self
    }

    /// Port of `setWorkingOntology(CConcreteOntology* ontology)`
    /// (`return setWorkingOntology(ontology->getOntologyID());`).
    /// KONCLUDE-PORT-NOTE[api]: `ontology` is a cross-subtree `CConcreteOntology*`
    /// (opaque); resolving `getOntologyID()` is deferred. C++ returns `this`. W6-DEFER[api].
    pub fn set_working_ontology(&mut self, _ontology: Cint64) -> &mut Self {
        // W6-DEFER[api]: self.set_working_ontology_by_id(ontology.get_ontology_id()).
        self
    }

    /// Port of `hasUpdatedSlotItem()` [protected]
    /// (`return mUpdatedSlot.fetchAndAddRelaxed(0) != nullptr;`).
    /// KONCLUDE-PORT-NOTE[threading]: relaxed atomic load → single-threaded id test.
    pub fn has_updated_slot_item(&self) -> bool {
        self.updated_slot.is_some()
    }

    /// Port of `switchToUpdatedSlotItem()` [protected]: atomically takes the published
    /// slot, swaps it for the current slot (decReader on the old), and refreshes
    /// `mOntologyData` from it.
    pub fn switch_to_updated_slot_item_in_context(
        &mut self,
        cache_context: &mut CacheContext,
    ) -> bool {
        let updated_slot = self.updated_slot;
        self.updated_slot = SlotItemId::NONE;
        if updated_slot.is_some() {
            let prev_slot = self.current_slot;
            self.current_slot = updated_slot;
            if prev_slot.is_some() {
                cache_context.backend_slot_item_mut(prev_slot).dec_reader();
            }
            self.refresh_ontology_data_from_current_slot(cache_context);
            return true;
        }
        false
    }

    fn refresh_ontology_data_from_current_slot(&mut self, cache_context: &mut CacheContext) {
        self.ontology_data = OntologyDataId::NONE;
        if self.current_slot.is_some() {
            self.ontology_data = cache_context
                .backend_slot_item(self.current_slot)
                .get_ontology_data(self.ontology_identifier);
        }
        if self.ontology_data.is_some() && self.recomputation_id != 0 {
            let rec_ref = cache_context
                .ontology_data(self.ontology_data)
                .get_recomputation_reference_linker();
            if rec_ref.is_some() {
                cache_context
                    .ontology_data_recomp_ref_linker_mut(rec_ref)
                    .update_used_recomputation_id(self.recomputation_id);
            }
        }
    }

    /// Port of `hasSameIndividualsMergings()` — derefs `mOntologyData->hasSameIndividualsMergings()`.
    pub fn has_same_individuals_mergings(&mut self, cache_context: &mut CacheContext) -> bool {
        if self.has_updated_slot_item() {
            self.switch_to_updated_slot_item_in_context(cache_context);
        }
        self.ontology_data != OntologyDataId::NONE
            && cache_context
                .ontology_data(self.ontology_data)
                .has_same_individuals_mergings()
    }

    // -- label-signature lookup ------------------------------------------------------

    /// Port of `hasCacheEntry(cint64 labelType, cint64 signature)` — tests the ontology
    /// data's per-type signature→label-item hash for `signature`.
    pub fn has_cache_entry(
        &mut self,
        label_type: Cint64,
        signature: Cint64,
        cache_context: &mut CacheContext,
    ) -> bool {
        if self.has_updated_slot_item() {
            self.switch_to_updated_slot_item_in_context(cache_context);
        }
        if self.ontology_data == OntologyDataId::NONE || label_type < 0 {
            return false;
        }
        cache_context
            .ontology_data(self.ontology_data)
            .sig_label_item_hash
            .get(label_type as usize)
            .is_some_and(|hash| hash.contains_key(&signature))
    }

    /// Port of `getLabelCacheEntry(cint64 labelType, cint64 signature)`.
    /// KONCLUDE-PORT-NOTE[api]: C++ returns a pointer to the hashed
    /// `CBackendRepresentativeMemoryLabelSignatureResolveCacheItem` (or to the reusable
    /// `mEmptySigResCacheItem` scratch when absent). The Rust port returns the resolve item
    /// by value.
    pub fn get_label_cache_entry(
        &mut self,
        label_type: Cint64,
        signature: Cint64,
        cache_context: &mut CacheContext,
    ) -> LabelSignatureResolveCacheItem {
        if self.has_updated_slot_item() {
            self.switch_to_updated_slot_item_in_context(cache_context);
        }
        if self.ontology_data != OntologyDataId::NONE && label_type >= 0 {
            if let Some(item) = cache_context
                .ontology_data(self.ontology_data)
                .sig_label_item_hash
                .get(label_type as usize)
                .and_then(|hash| hash.get(&signature))
            {
                return item.clone();
            }
        }
        self.empty_sig_res_cache_item.clone()
    }

    /// Port of `visitLabelCacheEntries(cint64 labelType, function<bool(...)> visitFunc)`.
    /// Iterates every signature bucket for `labelType` and stops when the visitor
    /// returns false.
    pub fn visit_label_cache_entries(
        &mut self,
        label_type: Cint64,
        mut visit_func: impl FnMut(LabelCacheItemId) -> bool,
        cache_context: &mut CacheContext,
    ) -> bool {
        if self.has_updated_slot_item() {
            self.switch_to_updated_slot_item_in_context(cache_context);
        }
        if self.ontology_data == OntologyDataId::NONE || label_type < 0 {
            return false;
        }
        let Some(hash) = cache_context
            .ontology_data(self.ontology_data)
            .sig_label_item_hash
            .get(label_type as usize)
        else {
            return false;
        };

        let mut visited = false;
        for sig_resolve_cache_item in hash.values() {
            for &item in sig_resolve_cache_item.get_label_items() {
                visited = true;
                if !visit_func(item) {
                    return visited;
                }
            }
        }
        visited
    }

    /// Port of `getLabelCacheEntryViaProvidedCacheValues(cint64 labelType, cint64 signature,
    /// cint64 count, function<bool(bool, cint64&, CCacheValue&)> provFunc)`.
    /// Matches provided cache-values against the facade-arena label items.
    pub fn get_label_cache_entry_via_provided_cache_values(
        &mut self,
        label_type: Cint64,
        signature: Cint64,
        count: Cint64,
        mut prov_func: impl FnMut(bool, &mut Cint64, &mut CacheValue) -> bool,
        cache_context: &mut CacheContext,
    ) -> LabelCacheItemId {
        let sig_res_entry = self.get_label_cache_entry(label_type, signature, cache_context);
        for &item_id in sig_res_entry.get_label_items() {
            let item = cache_context.label_cache_item(item_id);
            if item.get_cache_value_count() != count {
                continue;
            }

            let mut compatible = true;
            let mut tag = 0;
            let mut cache_value = CacheValue::new();
            let mut reset_providing = true;
            while compatible {
                if !prov_func(reset_providing, &mut tag, &mut cache_value) {
                    break;
                }
                reset_providing = false;
                let Some(&label_value_linker) = item.tag_value_hash.get(&tag) else {
                    compatible = false;
                    continue;
                };
                if cache_context
                    .label_value_linker(label_value_linker)
                    .get_cache_value()
                    != &cache_value
                {
                    compatible = false;
                }
            }
            if compatible {
                return item_id;
            }
        }
        LabelCacheItemId::NONE
    }

    /// Port of `getLabelCacheEntryViaRoleLinker(cint64 labelType, cint64 signature, cint64 count,
    /// CSortedNegLinker<CRole*>* roleLinker, bool inversed, CRole* assertedRole = nullptr)`.
    pub fn get_label_cache_entry_via_role_linker(
        &mut self,
        label_type: Cint64,
        signature: Cint64,
        count: Cint64,
        role_linker: &[(Cint64, bool)],
        inversed: bool,
        asserted_role: Cint64,
        cache_context: &mut CacheContext,
    ) -> LabelCacheItemId {
        let provided_values: Vec<CacheValue> = role_linker
            .iter()
            .copied()
            .map(|(role, negated)| {
                let role_inversion = negated ^ inversed;
                let assertion_link_base = role == asserted_role && role_inversion == inversed;
                self.get_cache_value_role_qualified(
                    role,
                    role_inversion,
                    assertion_link_base,
                    false,
                    false,
                )
            })
            .collect();
        let mut pos = 0usize;
        self.get_label_cache_entry_via_provided_cache_values(
            label_type,
            signature,
            count,
            |reset_providing, tag, cache_value| {
                if reset_providing {
                    pos = 0;
                }
                let Some(value) = provided_values.get(pos).copied() else {
                    return false;
                };
                *cache_value = value;
                *tag = cache_value.get_tag();
                pos += 1;
                true
            },
            cache_context,
        )
    }

    /// Port of `getLabelCacheEntryViaRoleAssertionLinker(cint64 labelType, cint64 signature,
    /// cint64 count, CBackendRepresentativeMemoryCacheRoleAssertionLinker* roleAssertionLinker)`.
    pub fn get_label_cache_entry_via_role_assertion_linker(
        &mut self,
        label_type: Cint64,
        signature: Cint64,
        count: Cint64,
        role_assertion_linker: &[RoleAssertionLinkerId],
        cache_context: &mut CacheContext,
    ) -> LabelCacheItemId {
        let provided_values: Vec<CacheValue> = role_assertion_linker
            .iter()
            .copied()
            .filter(|id| *id != RoleAssertionLinkerId::NONE)
            .map(|id| {
                let linker = cache_context.role_assertion_linker(id);
                self.get_cache_value_role_qualified(
                    linker.role,
                    linker.is_inversed(),
                    linker.is_abox_asserted(),
                    linker.is_nominal_connected(),
                    linker.is_nondeterministic(),
                )
            })
            .collect();
        let mut pos = 0usize;
        self.get_label_cache_entry_via_provided_cache_values(
            label_type,
            signature,
            count,
            |reset_providing, tag, cache_value| {
                if reset_providing {
                    pos = 0;
                }
                let Some(value) = provided_values.get(pos).copied() else {
                    return false;
                };
                *cache_value = value;
                *tag = cache_value.get_tag();
                pos += 1;
                true
            },
            cache_context,
        )
    }

    /// Port of `getNeighbourRoleInstantiatedSetCompinationLabelCacheEntry(cint64 signature,
    /// cint64 count, CBackendRepresentativeMemoryCacheTemporaryLabelReferenceDataLinker*)`.
    pub fn get_neighbour_role_instantiated_set_compination_label_cache_entry(
        &mut self,
        signature: Cint64,
        count: Cint64,
        neigbour_role_instantiated_set_tmp_label_linker: &[BackendTempWriteRecordId],
        cache_context: &mut CacheContext,
    ) -> LabelCacheItemId {
        let provided_values: Vec<CacheValue> = neigbour_role_instantiated_set_tmp_label_linker
            .iter()
            .copied()
            .map(|linker_id| self.get_cache_value_neighbour_label(linker_id, cache_context))
            .collect();
        let mut pos = 0usize;
        self.get_label_cache_entry_via_provided_cache_values(
            LabelCacheItemType::NeighbourInstantiatedRoleSetCombinationLabel as Cint64,
            signature,
            count,
            |reset_providing, tag, cache_value| {
                if reset_providing {
                    pos = 0;
                }
                let Some(value) = provided_values.get(pos).copied() else {
                    return false;
                };
                *cache_value = value;
                *tag = cache_value.get_tag();
                pos += 1;
                true
            },
            cache_context,
        )
    }

    /// Port of `getConceptSetLabelCacheEntry(cint64 labelType, cint64 signature, cint64 conCount,
    /// CConceptSaturationDescriptor* conDesLinker)`.
    pub fn get_concept_set_label_cache_entry_saturation(
        &mut self,
        label_type: Cint64,
        signature: Cint64,
        con_count: Cint64,
        con_des_linker: &[ConceptDescriptorRecord],
        cache_context: &mut CacheContext,
    ) -> LabelCacheItemId {
        let sig_res_entry = self.get_label_cache_entry(label_type, signature, cache_context);
        for &item_id in sig_res_entry.get_label_items() {
            let item = cache_context.label_cache_item(item_id);
            if item.get_cache_value_count() != con_count {
                continue;
            }
            let mut compatible = true;
            for con_des in con_des_linker {
                let tag = con_des.signed_tag();
                let Some(&label_value_linker) = item.tag_value_hash.get(&tag) else {
                    compatible = false;
                    break;
                };
                if cache_context
                    .label_value_linker(label_value_linker)
                    .get_cache_value()
                    != &self.get_cache_value_concept_descriptor(con_des, true)
                {
                    compatible = false;
                    break;
                }
            }
            if compatible {
                return item_id;
            }
        }
        LabelCacheItemId::NONE
    }

    /// Port of `getDeterministicConceptSetLabelCacheEntry(...)`
    /// (`return getConceptSetLabelCacheEntry(signature, conCount, conDesLinker, true, ...);`).
    pub fn get_deterministic_concept_set_label_cache_entry(
        &mut self,
        signature: Cint64,
        con_count: Cint64,
        con_des_linker: &[ConceptDescriptorRecord],
        max_deterministic_branch_tag: Cint64,
        exclude_positive_nominal_concepts: bool,
        cache_context: &mut CacheContext,
    ) -> LabelCacheItemId {
        self.get_concept_set_label_cache_entry_descriptor(
            signature,
            con_count,
            con_des_linker,
            true,
            max_deterministic_branch_tag,
            exclude_positive_nominal_concepts,
            cache_context,
        )
    }

    /// Port of `getNondeterministicConceptSetLabelCacheEntry(...)`
    /// (`return getConceptSetLabelCacheEntry(signature, conCount, conDesLinker, false, ...);`).
    pub fn get_nondeterministic_concept_set_label_cache_entry(
        &mut self,
        signature: Cint64,
        con_count: Cint64,
        con_des_linker: &[ConceptDescriptorRecord],
        max_deterministic_branch_tag: Cint64,
        exclude_positive_nominal_concepts: bool,
        cache_context: &mut CacheContext,
    ) -> LabelCacheItemId {
        self.get_concept_set_label_cache_entry_descriptor(
            signature,
            con_count,
            con_des_linker,
            false,
            max_deterministic_branch_tag,
            exclude_positive_nominal_concepts,
            cache_context,
        )
    }

    /// Port of `getConceptSetLabelCacheEntry(cint64 signature, cint64 conCount,
    /// CConceptDescriptor* conDesLinker, bool deterministic, cint64 maxDeterministicBranchTag,
    /// bool excludePositiveNominalConcepts)`.
    pub fn get_concept_set_label_cache_entry_descriptor(
        &mut self,
        signature: Cint64,
        con_count: Cint64,
        con_des_linker: &[ConceptDescriptorRecord],
        deterministic: bool,
        max_deterministic_branch_tag: Cint64,
        exclude_positive_nominal_concepts: bool,
        cache_context: &mut CacheContext,
    ) -> LabelCacheItemId {
        let label_type = if deterministic {
            LabelCacheItemType::DeterministicConceptSetLabel
        } else {
            LabelCacheItemType::NondeterministicConceptSetLabel
        } as Cint64;
        let sig_res_entry = self.get_label_cache_entry(label_type, signature, cache_context);
        for &item_id in sig_res_entry.get_label_items() {
            let item = cache_context.label_cache_item(item_id);
            if item.get_cache_value_count() != con_count {
                continue;
            }
            let mut compatible = true;
            for con_des in con_des_linker {
                let mut consider_concept = con_des
                    .is_deterministically_derived(max_deterministic_branch_tag)
                    == deterministic;
                if exclude_positive_nominal_concepts && con_des.nominal && !con_des.negated {
                    consider_concept = false;
                }
                if consider_concept {
                    let tag = con_des.signed_tag();
                    let Some(&label_value_linker) = item.tag_value_hash.get(&tag) else {
                        compatible = false;
                        break;
                    };
                    if cache_context
                        .label_value_linker(label_value_linker)
                        .get_cache_value()
                        != &self.get_cache_value_concept_descriptor(con_des, true)
                    {
                        compatible = false;
                        break;
                    }
                }
            }
            if compatible {
                return item_id;
            }
        }
        LabelCacheItemId::NONE
    }

    /// Port of `getConceptSetLabelCacheEntry(cint64 labelType, cint64 signature, cint64 conCount,
    /// CConceptDescriptor* conDesLinker, function<bool(CConcept*, bool)> exclusionDetermineFunction)`.
    pub fn get_concept_set_label_cache_entry_exclusion(
        &mut self,
        label_type: Cint64,
        signature: Cint64,
        con_count: Cint64,
        con_des_linker: &[ConceptDescriptorRecord],
        exclusion_determine_function: impl Fn(Cint64, bool) -> bool,
        cache_context: &mut CacheContext,
    ) -> LabelCacheItemId {
        let sig_res_entry = self.get_label_cache_entry(label_type, signature, cache_context);
        for &item_id in sig_res_entry.get_label_items() {
            let item = cache_context.label_cache_item(item_id);
            if item.get_cache_value_count() != con_count {
                continue;
            }
            let mut compatible = true;
            for con_des in con_des_linker {
                if exclusion_determine_function(con_des.concept_id, con_des.negated) {
                    let tag = con_des.signed_tag();
                    let Some(&label_value_linker) = item.tag_value_hash.get(&tag) else {
                        compatible = false;
                        break;
                    };
                    if cache_context
                        .label_value_linker(label_value_linker)
                        .get_cache_value()
                        != &self.get_cache_value_concept_descriptor(con_des, true)
                    {
                        compatible = false;
                        break;
                    }
                }
            }
            if compatible {
                return item_id;
            }
        }
        LabelCacheItemId::NONE
    }

    /// Port of `getFullConceptSetLabelCacheEntry(cint64 labelType, cint64 signature, cint64 conCount,
    /// CConceptDescriptor* conDesLinker, function<bool(CConcept*, bool)> exclusionDetermineFunction,
    /// function<bool(CConcept*, bool, CDependencyTrackPoint*)> nondeterministicDetermineFunction)`.
    pub fn get_full_concept_set_label_cache_entry(
        &mut self,
        label_type: Cint64,
        signature: Cint64,
        con_count: Cint64,
        con_des_linker: &[ConceptDescriptorRecord],
        exclusion_determine_function: impl Fn(Cint64, bool) -> bool,
        nondeterministic_determine_function: impl Fn(Cint64, bool, Option<Cint64>) -> bool,
        cache_context: &mut CacheContext,
    ) -> LabelCacheItemId {
        let sig_res_entry = self.get_label_cache_entry(label_type, signature, cache_context);
        for &item_id in sig_res_entry.get_label_items() {
            let item = cache_context.label_cache_item(item_id);
            if item.get_cache_value_count() != con_count {
                continue;
            }
            let mut compatible = true;
            for con_des in con_des_linker {
                if exclusion_determine_function(con_des.concept_id, con_des.negated) {
                    let deterministic_concept = nondeterministic_determine_function(
                        con_des.concept_id,
                        con_des.negated,
                        con_des.dependency_branch_tag,
                    );
                    let tag = con_des.signed_tag();
                    let Some(&label_value_linker) = item.tag_value_hash.get(&tag) else {
                        compatible = false;
                        break;
                    };
                    if cache_context
                        .label_value_linker(label_value_linker)
                        .get_cache_value()
                        != &self.get_cache_value_concept_descriptor(con_des, deterministic_concept)
                    {
                        compatible = false;
                        break;
                    }
                }
            }
            if compatible {
                return item_id;
            }
        }
        LabelCacheItemId::NONE
    }

    // -- individual association data -------------------------------------------------

    /// Port of `getIndividualAssociationData(CIndividual* individual)`
    /// (`return getIndividualAssociationData(individual->getIndividualID());`).
    /// KONCLUDE-PORT-NOTE[api]: `individual` is a cross-subtree `CIndividual*` (opaque);
    /// resolving `getIndividualID()` is deferred. W6-DEFER[api].
    pub fn get_individual_association_data_for_individual(
        &mut self,
        _individual: Cint64,
    ) -> IndividualAssociationDataId {
        // W6-DEFER[api]: self.get_individual_association_data(individual.get_individual_id()).
        IndividualAssociationDataId::NONE
    }

    /// Port of `getIndividualAssociationData(cint64 indiId)` — indexes the ontology data's
    /// individual-id → association-data vector (or the basic-precomputation vector).
    pub fn get_individual_association_data(
        &mut self,
        indi_id: Cint64,
        cache_context: &mut CacheContext,
    ) -> IndividualAssociationDataId {
        if self.has_updated_slot_item() {
            self.switch_to_updated_slot_item_in_context(cache_context);
        }
        if self.ontology_data == OntologyDataId::NONE || indi_id < 0 {
            return IndividualAssociationDataId::NONE;
        }

        let ontology_data = cache_context.ontology_data(self.ontology_data);
        let (vector_size, vector) = if ontology_data.is_basic_precomputation_mode() {
            (
                ontology_data.get_basic_precomputation_individual_id_assoiation_data_vector_size(),
                ontology_data.get_basic_precomputation_individual_id_assoiation_data_vector(),
            )
        } else {
            (
                ontology_data.get_individual_id_assoiation_data_vector_size(),
                ontology_data.get_individual_id_assoiation_data_vector(),
            )
        };

        if indi_id < vector_size {
            vector
                .get(indi_id as usize)
                .copied()
                .unwrap_or(IndividualAssociationDataId::NONE)
        } else {
            IndividualAssociationDataId::NONE
        }
    }

    /// Port of `getIndividualAssociatedCacheLabelItem(cint64 indiId, cint64 labelType)`.
    pub fn get_individual_associated_cache_label_item(
        &mut self,
        indi_id: Cint64,
        label_type: Cint64,
        cache_context: &mut CacheContext,
    ) -> LabelCacheItemId {
        let ass_data = self.get_individual_association_data(indi_id, cache_context);
        if ass_data == IndividualAssociationDataId::NONE {
            return LabelCacheItemId::NONE;
        }
        cache_context
            .individual_assoc_data(ass_data)
            .get_label_cache_entry(label_type)
    }

    /// Port of `getNominalIndirectConnectionData(cint64 indiId)` — looks up the ontology
    /// data's nominal-indirect-connection hash.
    pub fn get_nominal_indirect_connection_data(
        &mut self,
        indi_id: Cint64,
        cache_context: &mut CacheContext,
    ) -> NominalIndividualIndirectConnectionDataId {
        if self.has_updated_slot_item() {
            self.switch_to_updated_slot_item_in_context(cache_context);
        }
        if self.ontology_data == OntologyDataId::NONE {
            return NominalIndividualIndirectConnectionDataId::NONE;
        }
        cache_context
            .ontology_data(self.ontology_data)
            .nominal_indi_id_indirect_connection_data_hash
            .get(&indi_id)
            .copied()
            .unwrap_or(NominalIndividualIndirectConnectionDataId::NONE)
    }

    /// Port of `getIndividualSetLabelCacheEntry(cint64 labelType, cint64 signature, cint64 indiId,
    /// CDistinctHash* indiDistinctHash, cint64& count, bool onlyDeterministic, cint64 maxDeterministicBranchTag)`.
    pub fn get_individual_set_label_cache_entry_distinct(
        &mut self,
        label_type: Cint64,
        signature: Cint64,
        indi_id: Cint64,
        indi_distinct_hash: &[DistinctHashEntry],
        count: Cint64,
        only_deterministic: bool,
        max_deterministic_branch_tag: Cint64,
        cache_context: &mut CacheContext,
    ) -> LabelCacheItemId {
        let mut individual_ids = Vec::new();
        for entry in indi_distinct_hash {
            let distinct_indi_id = entry.distinct_individual_id();
            if distinct_indi_id < 0 || distinct_indi_id == indi_id {
                continue;
            }
            let consider_individual = entry
                .is_deterministically_derived(max_deterministic_branch_tag)
                || !only_deterministic;
            if consider_individual {
                individual_ids.push(distinct_indi_id);
            }
        }
        if !individual_ids.is_empty() && indi_id >= 0 {
            individual_ids.push(indi_id);
        }
        self.get_individual_set_label_cache_entry_set(
            label_type,
            signature,
            &individual_ids,
            count,
            cache_context,
        )
    }

    /// Port of the `CIndividualMergingHash*` overload of `getIndividualSetLabelCacheEntry`.
    pub fn get_individual_set_label_cache_entry_merging(
        &mut self,
        label_type: Cint64,
        signature: Cint64,
        indi_id: Cint64,
        indi_merging_hash: &[IndividualMergingHashEntry],
        count: Cint64,
        only_deterministic: bool,
        max_deterministic_branch_tag: Cint64,
        cache_context: &mut CacheContext,
    ) -> LabelCacheItemId {
        let mut individual_ids = Vec::new();
        for entry in indi_merging_hash {
            let merged_indi_id = entry.individual_id;
            if merged_indi_id == indi_id || !entry.merged_with_individual {
                continue;
            }
            let consider_individual = entry
                .is_deterministically_derived(max_deterministic_branch_tag)
                || !only_deterministic;
            if consider_individual {
                individual_ids.push(merged_indi_id);
            }
        }
        if !individual_ids.is_empty() && indi_id >= 0 {
            individual_ids.push(indi_id);
        }
        self.get_individual_set_label_cache_entry_set(
            label_type,
            signature,
            &individual_ids,
            count,
            cache_context,
        )
    }

    /// Port of the `CPROCESSSET<cint64>*` overload of `getIndividualSetLabelCacheEntry`.
    pub fn get_individual_set_label_cache_entry_set(
        &mut self,
        label_type: Cint64,
        signature: Cint64,
        individual_set: &[Cint64],
        count: Cint64,
        cache_context: &mut CacheContext,
    ) -> LabelCacheItemId {
        let sig_res_entry = self.get_label_cache_entry(label_type, signature, cache_context);
        for &item_id in sig_res_entry.get_label_items() {
            let item = cache_context.label_cache_item(item_id);
            if item.get_cache_value_count() != count {
                continue;
            }
            let mut compatible = true;
            for &indi_id in individual_set {
                let Some(&label_value_linker) = item.tag_value_hash.get(&indi_id) else {
                    compatible = false;
                    break;
                };
                if cache_context
                    .label_value_linker(label_value_linker)
                    .get_cache_value()
                    != &self.get_cache_value_individual(indi_id, false)
                {
                    compatible = false;
                    break;
                }
            }
            if compatible {
                return item_id;
            }
        }
        LabelCacheItemId::NONE
    }

    // -- cache-value construction / classification -----------------------------------

    /// Port of `getCacheValue(cint64 indiId, bool negation)` — builds an individual-id
    /// cache value (fully self-contained; no arena deref).
    pub fn get_cache_value_individual(&self, mut indi_id: Cint64, negation: bool) -> CacheValue {
        let mut cache_value_identifier = CacheValueIdentifier::CacheValueIndividualId;
        if negation {
            indi_id = -indi_id;
            cache_value_identifier = CacheValueIdentifier::CacheValueNegatedIndividualId;
        }
        let mut cache_value = CacheValue::new();
        cache_value.init_cache_value(indi_id, 0, cache_value_identifier);
        cache_value
    }

    /// Port of `getCacheValue(CConcept* concept, bool negation, bool deterministic = true)`.
    pub fn get_cache_value_concept(
        &self,
        concept: Cint64,
        negation: bool,
        deterministic: bool,
    ) -> CacheValue {
        let identifier = match (deterministic, negation) {
            (true, false) => CacheValueIdentifier::CacheValTagAndConcept,
            (true, true) => CacheValueIdentifier::CacheValTagAndNegatedConcept,
            (false, false) => CacheValueIdentifier::CacheValTagAndNondeterministicConcept,
            (false, true) => CacheValueIdentifier::CacheValTagAndNondeterministicNegatedConcept,
        };
        let tag = if negation { -concept } else { concept };
        CacheValue::new_value(tag, concept, identifier)
    }

    /// Port helper for `getCacheValue(CConcept* concept, ...)` when a descriptor
    /// keeps Konclude's concept identity separate from `concept->getConceptTag()`.
    pub fn get_cache_value_concept_descriptor(
        &self,
        descriptor: &ConceptDescriptorRecord,
        deterministic: bool,
    ) -> CacheValue {
        let identifier = match (deterministic, descriptor.negated) {
            (true, false) => CacheValueIdentifier::CacheValTagAndConcept,
            (true, true) => CacheValueIdentifier::CacheValTagAndNegatedConcept,
            (false, false) => CacheValueIdentifier::CacheValTagAndNondeterministicConcept,
            (false, true) => CacheValueIdentifier::CacheValTagAndNondeterministicNegatedConcept,
        };
        CacheValue::new_value(descriptor.signed_tag(), descriptor.concept_id, identifier)
    }

    /// Port of `getCacheValue(CRole* role)`.
    pub fn get_cache_value_role(&self, role: Cint64) -> CacheValue {
        CacheValue::new_value(role, role, CacheValueIdentifier::CacheValTagAndRole)
    }

    /// Port of `getCacheValue(CRole* role, bool inversed, bool assertionLinkBase = false,
    /// bool nominalConnected = false, bool nondeterministc = false)`.
    pub fn get_cache_value_role_qualified(
        &self,
        role: Cint64,
        inversed: bool,
        assertion_link_base: bool,
        nominal_connected: bool,
        nondeterministic: bool,
    ) -> CacheValue {
        let identifier = match (
            inversed,
            assertion_link_base,
            nominal_connected,
            nondeterministic,
        ) {
            (true, true, _, false) => CacheValueIdentifier::CacheValTagAndInversedAssertedRole,
            (true, true, _, true) => {
                CacheValueIdentifier::CacheValTagAndNondeterministicInversedAssertedRole
            }
            (true, false, true, false) => {
                CacheValueIdentifier::CacheValTagAndInversedNominalConnectedRole
            }
            (true, false, true, true) => {
                CacheValueIdentifier::CacheValTagAndNondeterministicInversedNominalConnectedRole
            }
            (true, false, false, false) => CacheValueIdentifier::CacheValTagAndInversedRole,
            (true, false, false, true) => {
                CacheValueIdentifier::CacheValTagAndNondeterministicInversedRole
            }
            (false, true, _, false) => CacheValueIdentifier::CacheValTagAndAssertedRole,
            (false, true, _, true) => {
                CacheValueIdentifier::CacheValTagAndNondeterministicAssertedRole
            }
            (false, false, true, false) => CacheValueIdentifier::CacheValTagAndNominalConnectedRole,
            (false, false, true, true) => {
                CacheValueIdentifier::CacheValTagAndNondeterministicNominalConnectedRole
            }
            (false, false, false, true) => CacheValueIdentifier::CacheValTagAndNondeterministicRole,
            (false, false, false, false) => CacheValueIdentifier::CacheValTagAndRole,
        };
        let tag = if inversed { -role } else { role };
        CacheValue::new_value(tag, role, identifier)
    }

    /// Port of `getCacheValue(CBackendRepresentativeMemoryCacheTemporaryLabelReferenceDataLinker*)`.
    /// Resolves the temporary label reference to an entry or temporary-entry cache value.
    pub fn get_cache_value_neighbour_label(
        &self,
        neigbour_role_instantiated_set_tmp_label_linker: BackendTempWriteRecordId,
        cache_context: &mut CacheContext,
    ) -> CacheValue {
        if neigbour_role_instantiated_set_tmp_label_linker == BackendTempWriteRecordId::NONE {
            return CacheValue::new();
        }
        let temp_record = cache_context
            .backend_temp_write_record(neigbour_role_instantiated_set_tmp_label_linker);
        let label_cache_item = temp_record.label_reference_get_referred_label_data();
        let tmp_label_write_data = temp_record.label_reference_get_referred_temporary_label_data();

        if tmp_label_write_data != BackendTempWriteRecordId::NONE {
            CacheValue::new_value(
                0,
                tmp_label_write_data.raw,
                CacheValueIdentifier::CacheValueTagAndTemporaryEntry,
            )
        } else if label_cache_item != LabelCacheItemId::NONE {
            let tag = cache_context
                .label_cache_item(label_cache_item)
                .get_cache_entry_id();
            CacheValue::new_value(
                tag,
                label_cache_item.raw,
                CacheValueIdentifier::CacheValueTagAndEntry,
            )
        } else {
            CacheValue::new()
        }
    }

    /// Port of `isCacheValueRoleInverse(const CCacheValue& cacheValue)` (pure identifier test).
    pub fn is_cache_value_role_inverse(&self, cache_value: &CacheValue) -> bool {
        let id = cache_value.get_cache_value_identifier();
        id == CacheValueIdentifier::CacheValTagAndInversedRole as Cint64
            || id == CacheValueIdentifier::CacheValTagAndInversedAssertedRole as Cint64
            || id == CacheValueIdentifier::CacheValTagAndInversedNominalConnectedRole as Cint64
            || id == CacheValueIdentifier::CacheValTagAndNondeterministicInversedRole as Cint64
            || id
                == CacheValueIdentifier::CacheValTagAndNondeterministicInversedAssertedRole
                    as Cint64
            || id
                == CacheValueIdentifier::CacheValTagAndNondeterministicInversedNominalConnectedRole
                    as Cint64
    }

    /// Port of `isCacheValueRoleNondeterministic(const CCacheValue& cacheValue)`.
    pub fn is_cache_value_role_nondeterministic(&self, cache_value: &CacheValue) -> bool {
        let id = cache_value.get_cache_value_identifier();
        id == CacheValueIdentifier::CacheValTagAndNondeterministicRole as Cint64
            || id == CacheValueIdentifier::CacheValTagAndNondeterministicInversedRole as Cint64
            || id == CacheValueIdentifier::CacheValTagAndNondeterministicAssertedRole as Cint64
            || id
                == CacheValueIdentifier::CacheValTagAndNondeterministicInversedAssertedRole
                    as Cint64
            || id
                == CacheValueIdentifier::CacheValTagAndNondeterministicNominalConnectedRole
                    as Cint64
            || id
                == CacheValueIdentifier::CacheValTagAndNondeterministicInversedNominalConnectedRole
                    as Cint64
    }

    /// Port of `isCacheValueRoleNominal(const CCacheValue& cacheValue)`.
    pub fn is_cache_value_role_nominal(&self, cache_value: &CacheValue) -> bool {
        let id = cache_value.get_cache_value_identifier();
        id == CacheValueIdentifier::CacheValTagAndNominalConnectedRole as Cint64
            || id == CacheValueIdentifier::CacheValTagAndInversedNominalConnectedRole as Cint64
            || id
                == CacheValueIdentifier::CacheValTagAndNondeterministicNominalConnectedRole
                    as Cint64
            || id
                == CacheValueIdentifier::CacheValTagAndNondeterministicInversedNominalConnectedRole
                    as Cint64
    }

    /// Port of `isCacheValueRoleAssertion(const CCacheValue& cacheValue)`.
    pub fn is_cache_value_role_assertion(&self, cache_value: &CacheValue) -> bool {
        let id = cache_value.get_cache_value_identifier();
        id == CacheValueIdentifier::CacheValTagAndAssertedRole as Cint64
            || id == CacheValueIdentifier::CacheValTagAndInversedAssertedRole as Cint64
            || id == CacheValueIdentifier::CacheValTagAndNondeterministicAssertedRole as Cint64
            || id
                == CacheValueIdentifier::CacheValTagAndNondeterministicInversedAssertedRole
                    as Cint64
    }

    fn is_cache_value_concept_negated(&self, cache_value: &CacheValue) -> bool {
        let id = cache_value.get_cache_value_identifier();
        id == CacheValueIdentifier::CacheValTagAndNegatedConcept as Cint64
            || id == CacheValueIdentifier::CacheValTagAndNondeterministicNegatedConcept as Cint64
    }

    // -- associated-label visit / has queries ----------------------------------------
    //
    // All of these walk facade-arena label cache items / value linkers / extension data
    // and pass cross-subtree CConcept*/CRole*/indi-id to the visit callbacks. They are
    // W6-DEFER[api] faithful stubs until the cache facade arena is wired.

    /// Port of `visitNominalIndirectlyConnectedIndividualIds(assData, nomConnData, visitFunc)`.
    pub fn visit_nominal_indirectly_connected_individual_ids(
        &mut self,
        _ass_data: IndividualAssociationDataId,
        nom_conn_data: NominalIndividualIndirectConnectionDataId,
        mut visit_func: impl FnMut(Cint64) -> bool,
        cache_context: &mut CacheContext,
    ) -> bool {
        if nom_conn_data.is_none() {
            return false;
        }
        let linker = cache_context
            .nominal_indirect_connection_data(nom_conn_data)
            .get_indirectly_connected_individual_id_linker();
        if linker.is_empty() {
            return false;
        }
        for indirectly_connected_indi_id in linker.iter().copied() {
            if !visit_func(indirectly_connected_indi_id) {
                break;
            }
        }
        true
    }

    /// Port of `visitIndividualIdsOfAssociatedIndividualSetLabel(assData, indiSetLabel, visitFunc)`.
    pub fn visit_individual_ids_of_associated_individual_set_label(
        &mut self,
        _ass_data: IndividualAssociationDataId,
        indi_set_label: LabelCacheItemId,
        mut visit_func: impl FnMut(Cint64) -> bool,
        cache_context: &mut CacheContext,
    ) -> bool {
        self.visit_label_item_individual_id_associations(
            indi_set_label,
            |indi_id, _same_individual_merged| visit_func(indi_id),
            true,
            true,
            true,
            cache_context,
        )
    }

    /// Port of `hasIndividualIdsInAssociatedIndividualSetLabel(assData, indiSetLabel, indiId)`.
    pub fn has_individual_ids_in_associated_individual_set_label(
        &mut self,
        _ass_data: IndividualAssociationDataId,
        indi_set_label: LabelCacheItemId,
        indi_id: Cint64,
        cache_context: &mut CacheContext,
    ) -> bool {
        let mut found = false;
        self.visit_label_item_individual_id_associations(
            indi_set_label,
            |visited_indi_id, _same_individual_merged| {
                found = visited_indi_id == indi_id;
                !found
            },
            true,
            true,
            true,
            cache_context,
        );
        found
    }

    /// Port of `visitConceptsOfAssociatedDeterministicConceptSetLabel(assData, visitFunc)`.
    pub fn visit_concepts_of_associated_deterministic_concept_set_label(
        &mut self,
        ass_data: IndividualAssociationDataId,
        visit_func: impl FnMut(Cint64, bool) -> bool,
        cache_context: &mut CacheContext,
    ) -> bool {
        if ass_data.is_none() {
            return false;
        }
        let label_item = cache_context
            .individual_assoc_data(ass_data)
            .get_deterministic_concept_set_label_cache_entry();
        self.visit_concepts_of_associated_concept_set_label(
            ass_data,
            label_item,
            visit_func,
            cache_context,
        )
    }

    /// Port of `hasConceptInAssociatedDeterministicConceptSetLabel(assData, concept, negation)`.
    pub fn has_concept_in_associated_deterministic_concept_set_label(
        &mut self,
        ass_data: IndividualAssociationDataId,
        concept: Cint64,
        negation: bool,
        cache_context: &mut CacheContext,
    ) -> bool {
        if ass_data.is_none() {
            return false;
        }
        let label_item = cache_context
            .individual_assoc_data(ass_data)
            .get_deterministic_concept_set_label_cache_entry();
        self.has_concept_in_associated_concept_set_label(
            ass_data,
            label_item,
            concept,
            negation,
            cache_context,
        )
    }

    /// Port of `visitConceptsOfAssociatedNonDeterministicConceptSetLabel(assData, visitFunc)`.
    pub fn visit_concepts_of_associated_non_deterministic_concept_set_label(
        &mut self,
        ass_data: IndividualAssociationDataId,
        visit_func: impl FnMut(Cint64, bool) -> bool,
        cache_context: &mut CacheContext,
    ) -> bool {
        if ass_data.is_none() {
            return false;
        }
        let label_item = cache_context
            .individual_assoc_data(ass_data)
            .get_label_cache_entry(LabelCacheItemType::NondeterministicConceptSetLabel as Cint64);
        self.visit_concepts_of_associated_concept_set_label(
            ass_data,
            label_item,
            visit_func,
            cache_context,
        )
    }

    /// Port of `hasConceptInAssociatedNonDeterministicConceptSetLabel(assData, concept, negation)`.
    pub fn has_concept_in_associated_non_deterministic_concept_set_label(
        &mut self,
        ass_data: IndividualAssociationDataId,
        concept: Cint64,
        negation: bool,
        cache_context: &mut CacheContext,
    ) -> bool {
        if ass_data.is_none() {
            return false;
        }
        let label_item = cache_context
            .individual_assoc_data(ass_data)
            .get_label_cache_entry(LabelCacheItemType::NondeterministicConceptSetLabel as Cint64);
        self.has_concept_in_associated_concept_set_label(
            ass_data,
            label_item,
            concept,
            negation,
            cache_context,
        )
    }

    /// Port of `visitConceptsOfAssociatedConceptSetLabel(assData, labelItem, visitFunc)`.
    pub fn visit_concepts_of_associated_concept_set_label(
        &mut self,
        _ass_data: IndividualAssociationDataId,
        label_item: LabelCacheItemId,
        mut visit_func: impl FnMut(Cint64, bool) -> bool,
        cache_context: &mut CacheContext,
    ) -> bool {
        if label_item.is_none() {
            return false;
        }
        let label = cache_context.label_cache_item(label_item);
        if label.get_cache_value_linker().is_empty() {
            return false;
        }
        for linker in label.get_cache_value_linker().iter().copied() {
            let cache_value = cache_context.label_value_linker(linker).get_cache_value();
            let concept = cache_value.get_identification();
            let negation = self.is_cache_value_concept_negated(cache_value);
            if !visit_func(concept, negation) {
                break;
            }
        }
        true
    }

    /// Port of `hasConceptInAssociatedConceptSetLabel(assData, labelItem, concept, negation)`.
    pub fn has_concept_in_associated_concept_set_label(
        &mut self,
        _ass_data: IndividualAssociationDataId,
        label_item: LabelCacheItemId,
        concept: Cint64,
        negation: bool,
        cache_context: &mut CacheContext,
    ) -> bool {
        if label_item.is_none() {
            return false;
        }
        let tag = if negation { -concept } else { concept };
        let label = cache_context.label_cache_item(label_item);
        if let Some(label_linker) = label.tag_value_hash.get(&tag).copied() {
            return *cache_context
                .label_value_linker(label_linker)
                .get_cache_value()
                == self.get_cache_value_concept(concept, negation, true);
        }
        false
    }

    /// Port of `visitConceptsOfFullConceptSetLabel(labelItem, visitFunc, visitDeterministicConcepts,
    /// visitNonDeterministicConcepts)`.
    pub fn visit_concepts_of_full_concept_set_label(
        &mut self,
        label_item: LabelCacheItemId,
        mut visit_func: impl FnMut(Cint64, bool, bool) -> bool,
        visit_deterministic_concepts: bool,
        visit_non_deterministic_concepts: bool,
        cache_context: &mut CacheContext,
    ) -> bool {
        if label_item.is_none() {
            return false;
        }
        let label = cache_context.label_cache_item(label_item);
        if label.get_cache_value_linker().is_empty() {
            return false;
        }
        for linker in label.get_cache_value_linker().iter().copied() {
            let cache_value = cache_context.label_value_linker(linker).get_cache_value();
            let value_id = cache_value.get_cache_value_identifier();
            let negation = value_id == CacheValueIdentifier::CacheValTagAndNegatedConcept as Cint64
                || value_id
                    == CacheValueIdentifier::CacheValTagAndNondeterministicNegatedConcept as Cint64;
            let deterministic = value_id == CacheValueIdentifier::CacheValTagAndConcept as Cint64
                || value_id == CacheValueIdentifier::CacheValTagAndNegatedConcept as Cint64;
            if (deterministic && visit_deterministic_concepts)
                || (!deterministic && visit_non_deterministic_concepts)
            {
                let concept = cache_value.get_identification();
                if !visit_func(concept, negation, deterministic) {
                    break;
                }
            }
        }
        true
    }

    /// Port of `visitConceptsOfAssociatedFullConceptSetLabel(assData, labelItem, visitFunc, ...)`
    /// (`return visitConceptsOfFullConceptSetLabel(labelItem, visitFunc, ...);`).
    pub fn visit_concepts_of_associated_full_concept_set_label(
        &mut self,
        _ass_data: IndividualAssociationDataId,
        label_item: LabelCacheItemId,
        visit_func: impl FnMut(Cint64, bool, bool) -> bool,
        visit_deterministic_concepts: bool,
        visit_non_deterministic_concepts: bool,
        cache_context: &mut CacheContext,
    ) -> bool {
        self.visit_concepts_of_full_concept_set_label(
            label_item,
            visit_func,
            visit_deterministic_concepts,
            visit_non_deterministic_concepts,
            cache_context,
        )
    }

    /// Port of `hasConceptInAssociatedFullConceptSetLabel(assData, labelItem, concept, negation)`.
    pub fn has_concept_in_associated_full_concept_set_label(
        &mut self,
        _ass_data: IndividualAssociationDataId,
        label_item: LabelCacheItemId,
        concept: Cint64,
        negation: bool,
        cache_context: &mut CacheContext,
    ) -> bool {
        if label_item.is_none() {
            return false;
        }
        let tag = if negation { -concept } else { concept };
        cache_context
            .label_cache_item(label_item)
            .tag_value_hash
            .contains_key(&tag)
    }

    /// Port of the determinism-qualified overload `hasConceptInAssociatedFullConceptSetLabel(
    /// assData, labelItem, concept, negation, deterministic)`.
    pub fn has_concept_in_associated_full_concept_set_label_with_determinism(
        &mut self,
        _ass_data: IndividualAssociationDataId,
        label_item: LabelCacheItemId,
        concept: Cint64,
        negation: bool,
        deterministic: bool,
        cache_context: &mut CacheContext,
    ) -> bool {
        if label_item.is_none() {
            return false;
        }
        let tag = if negation { -concept } else { concept };
        let label = cache_context.label_cache_item(label_item);
        if let Some(label_linker) = label.tag_value_hash.get(&tag).copied() {
            return *cache_context
                .label_value_linker(label_linker)
                .get_cache_value()
                == self.get_cache_value_concept(concept, negation, deterministic);
        }
        false
    }

    /// Port of `getConceptOccurrenceInAssociatedFullConceptSetLabel(assData, labelItem, concept,
    /// bool& negationFlag, bool& deterministicFlag)`. `negation_flag` /
    /// `deterministic_flag` are the C++ out-params.
    pub fn get_concept_occurrence_in_associated_full_concept_set_label(
        &mut self,
        _ass_data: IndividualAssociationDataId,
        label_item: LabelCacheItemId,
        concept: Cint64,
        negation_flag: &mut bool,
        deterministic_flag: &mut bool,
        cache_context: &mut CacheContext,
    ) -> bool {
        if label_item.is_none() {
            return false;
        }
        let label = cache_context.label_cache_item(label_item);
        let label_linker = if let Some(linker) = label.tag_value_hash.get(&concept).copied() {
            *negation_flag = false;
            linker
        } else if let Some(linker) = label.tag_value_hash.get(&(-concept)).copied() {
            *negation_flag = true;
            linker
        } else {
            return false;
        };

        let cache_value = cache_context
            .label_value_linker(label_linker)
            .get_cache_value();
        let value_id = cache_value.get_cache_value_identifier();
        *deterministic_flag = value_id == CacheValueIdentifier::CacheValTagAndConcept as Cint64
            || value_id == CacheValueIdentifier::CacheValTagAndNegatedConcept as Cint64;
        true
    }

    // -- neighbour role-set array queries --------------------------------------------

    /// Port of `visitNeighbourIndividualIdsForNeighbourArrayIdFromCursor(assData, arrayId,
    /// visitFunc, visitOnlyDeterministicNeighbours = true, cursor = 0)`.
    pub fn visit_neighbour_individual_ids_for_neighbour_array_id_from_cursor(
        &mut self,
        ass_data: IndividualAssociationDataId,
        array_id: Cint64,
        mut visit_func: impl FnMut(Cint64, LabelCacheItemId, bool, Cint64) -> bool,
        _visit_only_deterministic_neighbours: bool,
        cursor: Cint64,
        cache_context: &mut CacheContext,
    ) -> bool {
        if ass_data.is_none() {
            return false;
        }
        let ass = cache_context.individual_assoc_data(ass_data);
        let neighbour_array = ass.get_role_set_neighbour_array();
        let neighbour_comb_label_item = ass.get_label_cache_entry(
            LabelCacheItemType::NeighbourInstantiatedRoleSetCombinationLabel as Cint64,
        );
        if neighbour_comb_label_item.is_none() || neighbour_array.is_none() {
            return false;
        }
        let array = cache_context.individual_role_set_neighbour_array(neighbour_array);
        let index_data = array.get_index_data();
        if index_data.is_none() {
            return false;
        }
        let neighbour_label = cache_context
            .label_cache_item_ext_data(index_data)
            .get_neighbour_role_set_label(array_id);
        let neighbour_data = array.at(array_id);
        if neighbour_label.is_none() || neighbour_data.is_none() {
            return false;
        }
        let nondeterministic = cache_context
            .label_cache_item(neighbour_label)
            .flags
            .has_nondeterministic_elements();
        let mut wrapped_visit = |neighbour_indi_id: Cint64, next_cursor: Cint64| {
            visit_func(
                neighbour_indi_id,
                neighbour_label,
                nondeterministic,
                next_cursor,
            )
        };
        if !(_visit_only_deterministic_neighbours && nondeterministic) {
            cache_context
                .individual_role_set_neighbour_data(neighbour_data)
                .visit_neighbour_individual_ids_from_cursor(
                    &mut wrapped_visit,
                    cursor,
                    cache_context,
                );
        }
        true
    }

    /// Port of `visitNeighbourIndividualIdsForRole(assData, role, visitFunc,
    /// visitOnlyDeterministicNeighbours = true)`.
    pub fn visit_neighbour_individual_ids_for_role(
        &mut self,
        ass_data: IndividualAssociationDataId,
        role: Cint64,
        mut visit_func: impl FnMut(Cint64, LabelCacheItemId, bool) -> bool,
        visit_only_deterministic_neighbours: bool,
        cache_context: &mut CacheContext,
    ) -> bool {
        if ass_data.is_none() {
            return false;
        }
        let ass = cache_context.individual_assoc_data(ass_data);
        let neighbour_array = ass.get_role_set_neighbour_array();
        let neighbour_comb_label_item = ass.get_label_cache_entry(
            LabelCacheItemType::NeighbourInstantiatedRoleSetCombinationLabel as Cint64,
        );
        if neighbour_comb_label_item.is_none() || neighbour_array.is_none() {
            return false;
        }
        let extension_data = cache_context
            .label_cache_item(neighbour_comb_label_item)
            .get_extension_data(LabelCacheItemExtensionType::TagResolvingHash as Cint64);
        if extension_data.is_none() {
            return false;
        }
        let linker = cache_context
            .label_cache_item_ext_data(extension_data)
            .get_tag_label_resolving_data_linker(role);
        if linker.is_none() {
            return true;
        }
        let resolving_data = cache_context.tag_label_resolving_data_linker(linker);
        if visit_only_deterministic_neighbours && !resolving_data.is_deterministic() {
            return true;
        }
        let neighbour_data = cache_context
            .individual_role_set_neighbour_array(neighbour_array)
            .at(resolving_data.get_index());
        if neighbour_data.is_none() {
            return true;
        }
        let label_item = resolving_data.get_label_cache_item();
        let nondeterministic = !resolving_data.is_deterministic();
        let mut wrapped_visit =
            |neighbour_indi_id: Cint64| visit_func(neighbour_indi_id, label_item, nondeterministic);
        cache_context
            .individual_role_set_neighbour_data(neighbour_data)
            .visit_neighbour_individual_ids(&mut wrapped_visit, cache_context);
        true
    }

    /// Port of `visitNeighbourArrayIdsForRole(assData, role, visitFunc,
    /// visitOnlyDeterministicNeighbours = true)`.
    pub fn visit_neighbour_array_ids_for_role(
        &mut self,
        ass_data: IndividualAssociationDataId,
        role: Cint64,
        mut visit_func: impl FnMut(Cint64, LabelCacheItemId, bool) -> bool,
        visit_only_deterministic_neighbours: bool,
        cache_context: &mut CacheContext,
    ) -> bool {
        if ass_data.is_none() {
            return false;
        }
        let ass = cache_context.individual_assoc_data(ass_data);
        let neighbour_array = ass.get_role_set_neighbour_array();
        let neighbour_comb_label_item = ass.get_label_cache_entry(
            LabelCacheItemType::NeighbourInstantiatedRoleSetCombinationLabel as Cint64,
        );
        if neighbour_comb_label_item.is_none() || neighbour_array.is_none() {
            return false;
        }
        let extension_data = cache_context
            .label_cache_item(neighbour_comb_label_item)
            .get_extension_data(LabelCacheItemExtensionType::TagResolvingHash as Cint64);
        if extension_data.is_none() {
            return false;
        }
        let linker = cache_context
            .label_cache_item_ext_data(extension_data)
            .get_tag_label_resolving_data_linker(role);
        if linker.is_none() {
            return true;
        }
        let resolving_data = cache_context.tag_label_resolving_data_linker(linker);
        if !visit_only_deterministic_neighbours || resolving_data.is_deterministic() {
            return visit_func(
                resolving_data.get_index(),
                resolving_data.get_label_cache_item(),
                !resolving_data.is_deterministic(),
            );
        }
        true
    }

    /// Port of `getNeighbourCountForRole(assData, role)`.
    pub fn get_neighbour_count_for_role(
        &mut self,
        ass_data: IndividualAssociationDataId,
        role: Cint64,
        cache_context: &mut CacheContext,
    ) -> Cint64 {
        if ass_data.is_none() {
            return 0;
        }
        let ass = cache_context.individual_assoc_data(ass_data);
        let neighbour_array = ass.get_role_set_neighbour_array();
        let neighbour_comb_label_item = ass.get_label_cache_entry(
            LabelCacheItemType::NeighbourInstantiatedRoleSetCombinationLabel as Cint64,
        );
        if neighbour_comb_label_item.is_none() || neighbour_array.is_none() {
            return 0;
        }
        let extension_data = cache_context
            .label_cache_item(neighbour_comb_label_item)
            .get_extension_data(LabelCacheItemExtensionType::TagResolvingHash as Cint64);
        if extension_data.is_none() {
            return 0;
        }
        let linker = cache_context
            .label_cache_item_ext_data(extension_data)
            .get_tag_label_resolving_data_linker(role);
        if linker.is_none() {
            return 0;
        }
        let index = cache_context
            .tag_label_resolving_data_linker(linker)
            .get_index();
        let neighbour_data = cache_context
            .individual_role_set_neighbour_array(neighbour_array)
            .at(index);
        if neighbour_data.is_none() {
            return 0;
        }
        cache_context
            .individual_role_set_neighbour_data(neighbour_data)
            .get_individual_count()
    }

    /// Port of `getNeighbourCountForArrayPos(assData, pos)`.
    pub fn get_neighbour_count_for_array_pos(
        &mut self,
        ass_data: IndividualAssociationDataId,
        pos: Cint64,
        cache_context: &mut CacheContext,
    ) -> Cint64 {
        if ass_data.is_none() {
            return 0;
        }
        let ass = cache_context.individual_assoc_data(ass_data);
        let neighbour_array = ass.get_role_set_neighbour_array();
        let neighbour_comb_label_item = ass.get_label_cache_entry(
            LabelCacheItemType::NeighbourInstantiatedRoleSetCombinationLabel as Cint64,
        );
        if neighbour_comb_label_item.is_none() || neighbour_array.is_none() {
            return 0;
        }
        let neighbour_data = cache_context
            .individual_role_set_neighbour_array(neighbour_array)
            .at(pos);
        if neighbour_data.is_none() {
            return 0;
        }
        cache_context
            .individual_role_set_neighbour_data(neighbour_data)
            .get_individual_count()
    }

    // -- neighbour / combination role-set label queries ------------------------------

    /// Port of `visitRolesOfAssociatedNeigbourRoleSetLabel(assData, neighbourRoleSetLabel, visitFunc)`.
    pub fn visit_roles_of_associated_neigbour_role_set_label(
        &mut self,
        _ass_data: IndividualAssociationDataId,
        neighbour_role_set_label: LabelCacheItemId,
        mut visit_func: impl FnMut(Cint64, bool, bool, bool, bool) -> bool,
        cache_context: &mut CacheContext,
    ) -> bool {
        if neighbour_role_set_label.is_none() {
            return false;
        }
        let label = cache_context.label_cache_item(neighbour_role_set_label);
        if label.get_cache_value_linker().is_empty() {
            return false;
        }
        for linker in label.get_cache_value_linker().iter().copied() {
            let cache_value = cache_context.label_value_linker(linker).get_cache_value();
            let role = cache_value.get_identification();
            let inversed = self.is_cache_value_role_inverse(cache_value);
            let assertion_link_base = self.is_cache_value_role_assertion(cache_value);
            let nominal_link_base = self.is_cache_value_role_nominal(cache_value);
            let nondeterministic = self.is_cache_value_role_nondeterministic(cache_value);
            if !visit_func(
                role,
                inversed,
                assertion_link_base,
                nominal_link_base,
                nondeterministic,
            ) {
                break;
            }
        }
        true
    }

    /// Port of `hasRoleInAssociatedNeigbourRoleSetLabel(assData, label, role, inversed,
    /// assertionLinkBase, nominalLinkBase, nondeterministic)`.
    pub fn has_role_in_associated_neigbour_role_set_label_full(
        &mut self,
        _ass_data: IndividualAssociationDataId,
        neighbour_role_set_label: LabelCacheItemId,
        role: Cint64,
        inversed: bool,
        assertion_link_base: bool,
        nominal_link_base: bool,
        nondeterministic: bool,
        cache_context: &mut CacheContext,
    ) -> bool {
        if neighbour_role_set_label.is_none() {
            return false;
        }
        let tag = if inversed { -role } else { role };
        let label = cache_context.label_cache_item(neighbour_role_set_label);
        if let Some(label_linker) = label.tag_value_hash.get(&tag).copied() {
            return *cache_context
                .label_value_linker(label_linker)
                .get_cache_value()
                == self.get_cache_value_role_qualified(
                    role,
                    inversed,
                    assertion_link_base,
                    nominal_link_base,
                    nondeterministic,
                );
        }
        false
    }

    /// Port of the `(assData, label, role, inversed)` overload of
    /// `hasRoleInAssociatedNeigbourRoleSetLabel`.
    pub fn has_role_in_associated_neigbour_role_set_label(
        &mut self,
        _ass_data: IndividualAssociationDataId,
        neighbour_role_set_label: LabelCacheItemId,
        role: Cint64,
        inversed: bool,
        cache_context: &mut CacheContext,
    ) -> bool {
        if neighbour_role_set_label.is_none() {
            return false;
        }
        let tag = if inversed { -role } else { role };
        cache_context
            .label_cache_item(neighbour_role_set_label)
            .tag_value_hash
            .contains_key(&tag)
    }

    /// Port of the `(assData, label, role, inversed, nondeterministic)` overload of
    /// `hasRoleInAssociatedNeigbourRoleSetLabel`.
    pub fn has_role_in_associated_neigbour_role_set_label_with_nondeterminism(
        &mut self,
        _ass_data: IndividualAssociationDataId,
        neighbour_role_set_label: LabelCacheItemId,
        role: Cint64,
        inversed: bool,
        nondeterministic: bool,
        cache_context: &mut CacheContext,
    ) -> bool {
        if neighbour_role_set_label.is_none() {
            return false;
        }
        let tag = if inversed { -role } else { role };
        let label = cache_context.label_cache_item(neighbour_role_set_label);
        if let Some(label_linker) = label.tag_value_hash.get(&tag).copied() {
            let cache_value = cache_context
                .label_value_linker(label_linker)
                .get_cache_value();
            return self.is_cache_value_role_nondeterministic(cache_value) == nondeterministic;
        }
        false
    }

    /// Port of `hasRoleInAssociatedCombinedNeigbourRoleSetLabel(assData, label, role, inversed)`.
    pub fn has_role_in_associated_combined_neigbour_role_set_label(
        &mut self,
        _ass_data: IndividualAssociationDataId,
        neighbour_role_set_label: LabelCacheItemId,
        role: Cint64,
        inversed: bool,
        cache_context: &mut CacheContext,
    ) -> bool {
        if neighbour_role_set_label.is_none() {
            return false;
        }
        let tag = if inversed { -role } else { role };
        let label = cache_context.label_cache_item(neighbour_role_set_label);
        if let Some(label_linker) = label.tag_value_hash.get(&tag).copied() {
            return *cache_context
                .label_value_linker(label_linker)
                .get_cache_value()
                == self.get_cache_value_role_qualified(role, inversed, false, false, false);
        }
        false
    }

    /// Port of `visitLabelsOfAssociatedNeigbourRoleSetCombinationLabel(assData,
    /// neighbourRoleSetCompinationLabel, visitFunc)`.
    pub fn visit_labels_of_associated_neigbour_role_set_combination_label(
        &mut self,
        _ass_data: IndividualAssociationDataId,
        neighbour_role_set_compination_label: LabelCacheItemId,
        mut visit_func: impl FnMut(LabelCacheItemId) -> bool,
        cache_context: &mut CacheContext,
    ) -> bool {
        if neighbour_role_set_compination_label.is_none() {
            return false;
        }
        let label = cache_context.label_cache_item(neighbour_role_set_compination_label);
        if label.get_cache_value_linker().is_empty() {
            return false;
        }
        for linker in label.get_cache_value_linker().iter().copied() {
            let cache_value = cache_context.label_value_linker(linker).get_cache_value();
            let neighbour_role_set = LabelCacheItemId::new(cache_value.get_identification());
            if !visit_func(neighbour_role_set) {
                break;
            }
        }
        true
    }

    /// Port of `visitRolesOfAssociatedCompinationRoleSetLabel(assData, combinationRoleSetLabel, visitFunc)`.
    pub fn visit_roles_of_associated_compination_role_set_label(
        &mut self,
        _ass_data: IndividualAssociationDataId,
        combination_role_set_label: LabelCacheItemId,
        mut visit_func: impl FnMut(Cint64, bool) -> bool,
        cache_context: &mut CacheContext,
    ) -> bool {
        if combination_role_set_label.is_none() {
            return false;
        }
        let label = cache_context.label_cache_item(combination_role_set_label);
        if label.get_cache_value_linker().is_empty() {
            return false;
        }
        for linker in label.get_cache_value_linker().iter().copied() {
            let cache_value = cache_context.label_value_linker(linker).get_cache_value();
            let role = cache_value.get_identification();
            let inversed = cache_value.get_cache_value_identifier()
                == CacheValueIdentifier::CacheValTagAndInversedRole as Cint64;
            if !visit_func(role, inversed) {
                break;
            }
        }
        true
    }

    /// Port of `hasRoleInAssociatedCompinationRoleSetLabel(assData, compinationRoleSetLabel, role, inversed)`.
    pub fn has_role_in_associated_compination_role_set_label(
        &mut self,
        _ass_data: IndividualAssociationDataId,
        compination_role_set_label: LabelCacheItemId,
        role: Cint64,
        inversed: bool,
        cache_context: &mut CacheContext,
    ) -> bool {
        if compination_role_set_label.is_none() {
            return false;
        }
        let tag = if inversed { -role } else { role };
        cache_context
            .label_cache_item(compination_role_set_label)
            .tag_value_hash
            .contains_key(&tag)
    }

    /// Port of `visitRolesOfAssociatedCombinedNeigbourRoleSetLabel(assData, neighbourRoleSetLabel, visitFunc)`.
    pub fn visit_roles_of_associated_combined_neigbour_role_set_label(
        &mut self,
        _ass_data: IndividualAssociationDataId,
        neighbour_role_set_label: LabelCacheItemId,
        mut visit_func: impl FnMut(Cint64, bool) -> bool,
        cache_context: &mut CacheContext,
    ) -> bool {
        if neighbour_role_set_label.is_none() {
            return false;
        }
        let label = cache_context.label_cache_item(neighbour_role_set_label);
        if label.get_cache_value_linker().is_empty() {
            return false;
        }
        for linker in label.get_cache_value_linker().iter().copied() {
            let cache_value = cache_context.label_value_linker(linker).get_cache_value();
            let role = cache_value.get_identification();
            let inversed = self.is_cache_value_role_inverse(cache_value);
            if !visit_func(role, inversed) {
                break;
            }
        }
        true
    }

    /// Port of `hasRoleToNeigbourInAssociatedNeighbourRoleSetLabel(assData, neighbourIndiId, role, inversed)`.
    pub fn has_role_to_neigbour_in_associated_neighbour_role_set_label(
        &mut self,
        ass_data: IndividualAssociationDataId,
        neighbour_indi_id: Cint64,
        role: Cint64,
        inversed: bool,
        cache_context: &mut CacheContext,
    ) -> bool {
        if ass_data.is_none() {
            return false;
        }
        let neighbour_role_set_hash = cache_context
            .individual_assoc_data(ass_data)
            .get_neighbour_role_set_hash();
        if neighbour_role_set_hash.is_none() {
            return false;
        }
        let neighbour_role_set_label = cache_context
            .individual_neighbour_role_set_hash(neighbour_role_set_hash)
            .get_neighbour_role_set_label(neighbour_indi_id);
        if neighbour_role_set_label.is_none() {
            return false;
        }
        self.has_role_in_associated_neigbour_role_set_label(
            ass_data,
            neighbour_role_set_label,
            role,
            inversed,
            cache_context,
        )
    }

    /// Port of `visitRolesToNeigbourInAssociatedNeighbourRoleSetLabel(assData, neighbourIndiId, visitFunc)`.
    pub fn visit_roles_to_neigbour_in_associated_neighbour_role_set_label(
        &mut self,
        ass_data: IndividualAssociationDataId,
        neighbour_indi_id: Cint64,
        visit_func: impl FnMut(Cint64, bool, bool, bool, bool) -> bool,
        cache_context: &mut CacheContext,
    ) -> bool {
        if ass_data.is_none() {
            return false;
        }
        let neighbour_role_set_hash = cache_context
            .individual_assoc_data(ass_data)
            .get_neighbour_role_set_hash();
        if neighbour_role_set_hash.is_none() {
            return false;
        }
        let neighbour_role_set_label = cache_context
            .individual_neighbour_role_set_hash(neighbour_role_set_hash)
            .get_neighbour_role_set_label(neighbour_indi_id);
        if neighbour_role_set_label.is_none() {
            return false;
        }
        self.visit_roles_of_associated_neigbour_role_set_label(
            ass_data,
            neighbour_role_set_label,
            visit_func,
            cache_context,
        )
    }

    /// Port of `visitLabelItemIndividualIdAssociations(labelItem, visitFunc, ascending = true,
    /// visitBaseIndividual = true, visitSameMergedIndividuals = true)`.
    pub fn visit_label_item_individual_id_associations(
        &mut self,
        label_item: LabelCacheItemId,
        mut visit_func: impl FnMut(Cint64, bool) -> bool,
        ascending: bool,
        visit_base_individual: bool,
        visit_same_merged_individuals: bool,
        cache_context: &mut CacheContext,
    ) -> bool {
        if label_item.is_none() {
            return false;
        }
        let extension_data = cache_context
            .label_cache_item(label_item)
            .get_extension_data(LabelCacheItemExtensionType::IndividualAssociationMap as Cint64);
        if extension_data.is_none() {
            return false;
        }

        let mut visited = false;
        let mut it = cache_context
            .label_cache_item_ext_data(extension_data)
            .get_iterator(
                ascending,
                visit_base_individual,
                visit_same_merged_individuals,
            );
        while !it.at_end() {
            visited = true;
            let continue_visiting = visit_func(
                it.current_associated_individual_id(),
                it.current_associated_individual_same_merged(),
            );
            if !continue_visiting {
                break;
            }
            it.move_next();
        }
        visited
    }
}

#[cfg(test)]
mod tests {
    use super::super::backend_data::{
        BackendTempWriteRecord, IndividualAssociationData, IndividualNeighbourRoleSetHash,
        IndividualRoleSetNeighbourArray, IndividualRoleSetNeighbourData,
        IndividualRoleSetNeighbourDataId, IndividualRoleSetNeighbourIndividualIdLinker,
        LabelCacheItem, LabelCacheItemExtensionData, LabelCacheItemTagLabelResolvingDataLinker,
        LabelValueLinker, NominalIndividualIndirectConnectionData, OntologyData,
        OntologyDataRecomputationReferenceLinker, OntologyDataRecomputationReferenceLinkerId,
        RoleAssertionLinker, TempLabelReference,
    };
    use super::*;

    fn association_label_context() -> (CacheContext, LabelCacheItemId) {
        let mut ctx = CacheContext::new();
        let mut extension = LabelCacheItemExtensionData::IndividualAssociationMap {
            context: INVALID,
            base_indi_asso_map: Vec::new(),
            same_indi_merged_asso_map: Vec::new(),
        };
        extension
            .add_individual_id_association(1, false)
            .add_individual_id_association(3, false)
            .add_individual_id_association(5, false)
            .add_individual_id_association(3, true)
            .add_individual_id_association(4, true);
        let extension = ctx.alloc_label_cache_item_ext_data(extension);

        let mut label = LabelCacheItem::new(INVALID);
        label.set_extension_data(
            LabelCacheItemExtensionType::IndividualAssociationMap as Cint64,
            extension,
        );
        let label = ctx.alloc_label_cache_item(label);
        (ctx, label)
    }

    fn alloc_concept_label(
        ctx: &mut CacheContext,
        values: &[(Cint64, bool, bool)],
        label_type: LabelCacheItemType,
    ) -> LabelCacheItemId {
        let mut label = LabelCacheItem::new(INVALID);
        label.cache_item_type = label_type;
        let mut chain = Vec::new();
        for &(concept, negation, deterministic) in values.iter().rev() {
            let cache_value = BackendRepresentativeMemoryCacheReader::new()
                .get_cache_value_concept(concept, negation, deterministic);
            let mut linker = LabelValueLinker {
                cache_value: CacheValue::new(),
            };
            linker.init_label_value_linker(cache_value);
            let linker = ctx.alloc_label_value_linker(linker);
            label.tag_value_hash.insert(cache_value.get_tag(), linker);
            chain.insert(0, linker);
        }
        label.add_cache_value_linker(&chain);
        ctx.alloc_label_cache_item(label)
    }

    fn alloc_role_label(
        ctx: &mut CacheContext,
        values: &[(Cint64, bool, bool, bool, bool)],
        label_type: LabelCacheItemType,
    ) -> LabelCacheItemId {
        let mut label = LabelCacheItem::new(INVALID);
        label.cache_item_type = label_type;
        let mut chain = Vec::new();
        for &(role, inversed, assertion, nominal, nondeterministic) in values.iter().rev() {
            let cache_value = BackendRepresentativeMemoryCacheReader::new()
                .get_cache_value_role_qualified(
                    role,
                    inversed,
                    assertion,
                    nominal,
                    nondeterministic,
                );
            let mut linker = LabelValueLinker {
                cache_value: CacheValue::new(),
            };
            linker.init_label_value_linker(cache_value);
            let linker = ctx.alloc_label_value_linker(linker);
            label.tag_value_hash.insert(cache_value.get_tag(), linker);
            chain.insert(0, linker);
        }
        label.add_cache_value_linker(&chain);
        ctx.alloc_label_cache_item(label)
    }

    fn alloc_individual_set_label(
        ctx: &mut CacheContext,
        individual_ids: &[Cint64],
        label_type: LabelCacheItemType,
    ) -> LabelCacheItemId {
        let mut label = LabelCacheItem::new(INVALID);
        label.cache_item_type = label_type;
        let reader = BackendRepresentativeMemoryCacheReader::new();
        let mut chain = Vec::new();
        for &indi_id in individual_ids.iter().rev() {
            let cache_value = reader.get_cache_value_individual(indi_id, false);
            let mut linker = LabelValueLinker::new();
            linker.init_label_value_linker(cache_value);
            let linker = ctx.alloc_label_value_linker(linker);
            label.tag_value_hash.insert(cache_value.get_tag(), linker);
            chain.insert(0, linker);
        }
        label.add_cache_value_linker(&chain);
        ctx.alloc_label_cache_item(label)
    }

    fn alloc_concept_descriptor_label(
        ctx: &mut CacheContext,
        descriptors: &[ConceptDescriptorRecord],
        deterministic_flags: &[bool],
        label_type: LabelCacheItemType,
    ) -> LabelCacheItemId {
        let mut label = LabelCacheItem::new(INVALID);
        label.cache_item_type = label_type;
        let reader = BackendRepresentativeMemoryCacheReader::new();
        let mut chain = Vec::new();
        for (&descriptor, &deterministic) in descriptors.iter().zip(deterministic_flags).rev() {
            let cache_value = reader.get_cache_value_concept_descriptor(&descriptor, deterministic);
            let mut linker = LabelValueLinker::new();
            linker.init_label_value_linker(cache_value);
            let linker = ctx.alloc_label_value_linker(linker);
            label.tag_value_hash.insert(cache_value.get_tag(), linker);
            chain.insert(0, linker);
        }
        label.add_cache_value_linker(&chain);
        ctx.alloc_label_cache_item(label)
    }

    fn alloc_label_reference_combination(
        ctx: &mut CacheContext,
        labels: &[LabelCacheItemId],
    ) -> LabelCacheItemId {
        let mut label = LabelCacheItem::new(INVALID);
        label.cache_item_type = LabelCacheItemType::NeighbourInstantiatedRoleSetCombinationLabel;
        let mut chain = Vec::new();
        for label_id in labels.iter().copied().rev() {
            let cache_value = CacheValue::new_value(
                label_id.raw,
                label_id.raw,
                CacheValueIdentifier::CacheValueTagAndEntry,
            );
            let mut linker = LabelValueLinker {
                cache_value: CacheValue::new(),
            };
            linker.init_label_value_linker(cache_value);
            let linker = ctx.alloc_label_value_linker(linker);
            chain.insert(0, linker);
        }
        label.add_cache_value_linker(&chain);
        ctx.alloc_label_cache_item(label)
    }

    fn alloc_neighbour_data(
        ctx: &mut CacheContext,
        individual_ids: &[Cint64],
    ) -> IndividualRoleSetNeighbourDataId {
        let mut linkers = Vec::new();
        for indi_id in individual_ids.iter().copied() {
            let mut linker = IndividualRoleSetNeighbourIndividualIdLinker::new();
            linker.init_individual_id_linker(indi_id);
            linkers.push(ctx.alloc_individual_role_set_neighbour_id_linker(linker));
        }
        let mut data = IndividualRoleSetNeighbourData::new();
        data.set_individual_id_linker(&linkers, true);
        ctx.alloc_individual_role_set_neighbour_data(data)
    }

    fn reader_with_ontology_data(
        ctx: &mut CacheContext,
        ontology_data: OntologyData,
    ) -> BackendRepresentativeMemoryCacheReader {
        let ontology_data = ctx.alloc_ontology_data(ontology_data);
        let mut reader = BackendRepresentativeMemoryCacheReader::new();
        reader.fix_ontology_data(ontology_data);
        reader
    }

    fn alloc_recomputation_reference_linker(
        ctx: &mut CacheContext,
        update_id: Cint64,
    ) -> OntologyDataRecomputationReferenceLinkerId {
        let mut linker = OntologyDataRecomputationReferenceLinker::new();
        linker.init_recomputation_reference_linker(update_id);
        ctx.alloc_ontology_data_recomp_ref_linker(linker)
    }

    #[test]
    fn backend_cache_reader_slot_update_publishes_snapshot_to_readers() {
        let mut ctx = CacheContext::new();
        let mut ontology_data = OntologyData::new();
        ontology_data.set_next_update_minimum_valid_recomputation_id(17);
        let ontology_data = ctx.alloc_ontology_data(ontology_data);
        let mut cache = BackendRepresentativeMemoryCache::new(INVALID, "test", INVALID);
        cache
            .ontology_identifier_data_hash
            .insert(101, ontology_data);
        let first = cache.create_cache_reader(&mut ctx);
        let second = cache.create_cache_reader(&mut ctx);

        cache.create_reader_slot_update(ontology_data, &mut ctx);

        assert_eq!(cache.reader_slot_update_count, 1);
        assert_eq!(cache.slot_linker.len(), 1);
        let slot = cache.slot_linker[0];
        assert_eq!(cache.last_updated_slot_linker, slot);
        assert_eq!(
            ctx.ontology_data(ontology_data)
                .get_minimum_valid_recomputation_id(),
            17
        );
        assert!(ctx.ontology_data(ontology_data).is_slot_update_integrated());
        assert_eq!(ctx.ontology_data(ontology_data).get_usage_count(), 1);
        assert_eq!(
            ctx.backend_slot_item(slot).get_ontology_data(101),
            ontology_data
        );
        assert_eq!(ctx.backend_slot_item(slot).reader_sharing_count, 2);
        assert_eq!(ctx.backend_cache_reader(first).updated_slot, slot);
        assert_eq!(ctx.backend_cache_reader(second).updated_slot, slot);
    }

    #[test]
    fn backend_cache_reader_switches_updated_slot_and_refreshes_ontology_data() {
        let mut ctx = CacheContext::new();
        let old_ontology = ctx.alloc_ontology_data(OntologyData::new());
        let new_ontology = ctx.alloc_ontology_data(OntologyData::new());
        let mut old_slot = BackendRepresentativeMemoryCacheSlotItem::new();
        old_slot.set_ontology_identifier_data_hash(HashMap::from([(7, old_ontology)]));
        old_slot.inc_reader();
        let old_slot = ctx.alloc_backend_slot_item(old_slot);
        let mut new_slot = BackendRepresentativeMemoryCacheSlotItem::new();
        new_slot.set_ontology_identifier_data_hash(HashMap::from([(7, new_ontology)]));
        new_slot.inc_reader();
        let new_slot = ctx.alloc_backend_slot_item(new_slot);
        let mut reader = BackendRepresentativeMemoryCacheReader::new();
        reader.ontology_identifier = 7;
        reader.current_slot = old_slot;
        reader.ontology_data = old_ontology;
        reader.update_slot(new_slot, &mut ctx);

        assert!(reader.switch_to_updated_slot_item_in_context(&mut ctx));

        assert_eq!(reader.current_slot, new_slot);
        assert_eq!(reader.updated_slot, SlotItemId::NONE);
        assert_eq!(reader.ontology_data, new_ontology);
        assert!(!ctx.backend_slot_item(old_slot).has_cache_readers());
        assert!(ctx.backend_slot_item(new_slot).has_cache_readers());
    }

    #[test]
    fn backend_cache_reader_set_working_ontology_consumes_updated_slot() {
        let mut ctx = CacheContext::new();
        let old_ontology = ctx.alloc_ontology_data(OntologyData::new());
        let new_ontology = ctx.alloc_ontology_data(OntologyData::new());
        let fixed_ontology = ctx.alloc_ontology_data(OntologyData::new());
        let mut old_slot = BackendRepresentativeMemoryCacheSlotItem::new();
        old_slot.set_ontology_identifier_data_hash(HashMap::from([(7, old_ontology)]));
        old_slot.inc_reader();
        let old_slot = ctx.alloc_backend_slot_item(old_slot);
        let mut new_slot = BackendRepresentativeMemoryCacheSlotItem::new();
        new_slot.set_ontology_identifier_data_hash(HashMap::from([(9, new_ontology)]));
        new_slot.inc_reader();
        let new_slot = ctx.alloc_backend_slot_item(new_slot);
        let mut reader = BackendRepresentativeMemoryCacheReader::new();
        reader.current_slot = old_slot;
        reader.ontology_data = old_ontology;
        reader.update_slot(new_slot, &mut ctx);

        reader.set_working_ontology_by_id(9, &mut ctx);

        assert_eq!(reader.current_slot, new_slot);
        assert_eq!(reader.updated_slot, SlotItemId::NONE);
        assert_eq!(reader.ontology_identifier, 9);
        assert_eq!(reader.ontology_data, new_ontology);
        assert!(!ctx.backend_slot_item(old_slot).has_cache_readers());

        reader.fix_ontology_data(fixed_ontology);
        reader.set_working_ontology_by_id(9, &mut ctx);

        assert_eq!(reader.ontology_data, fixed_ontology);
    }

    #[test]
    fn backend_cache_reader_check_recomputation_usage_updates_reference() {
        let mut ctx = CacheContext::new();
        let rec_ref = alloc_recomputation_reference_linker(&mut ctx, 1);
        let mut ontology = OntologyData::new();
        ontology.set_minimum_valid_recomputation_id(3);
        ontology.set_recomputation_reference_linker(rec_ref, &mut ctx);
        let ontology = ctx.alloc_ontology_data(ontology);
        let mut slot = BackendRepresentativeMemoryCacheSlotItem::new();
        slot.set_ontology_identifier_data_hash(HashMap::from([(7, ontology)]));
        slot.inc_reader();
        let slot = ctx.alloc_backend_slot_item(slot);
        let mut reader = BackendRepresentativeMemoryCacheReader::new();
        reader.ontology_identifier = 7;
        reader.current_slot = slot;

        reader.check_recomputation_id_usage(5, &mut ctx);

        assert_eq!(reader.ontology_data, ontology);
        assert_eq!(
            ctx.ontology_data_recomp_ref_linker(rec_ref)
                .get_max_used_recomputation_id(),
            5
        );
    }

    #[test]
    #[should_panic(expected = "invalid backend representative memory cache recomputation id")]
    fn backend_cache_reader_check_recomputation_usage_rejects_stale_id() {
        let mut ctx = CacheContext::new();
        let mut ontology = OntologyData::new();
        ontology.set_minimum_valid_recomputation_id(3);
        let ontology = ctx.alloc_ontology_data(ontology);
        let mut slot = BackendRepresentativeMemoryCacheSlotItem::new();
        slot.set_ontology_identifier_data_hash(HashMap::from([(7, ontology)]));
        let slot = ctx.alloc_backend_slot_item(slot);
        let mut reader = BackendRepresentativeMemoryCacheReader::new();
        reader.ontology_identifier = 7;
        reader.current_slot = slot;

        reader.check_recomputation_id_usage(2, &mut ctx);
    }

    #[test]
    fn backend_cache_clean_unused_slots_decrements_ontology_usage_counts() {
        let mut ctx = CacheContext::new();
        let mut unused_ontology = OntologyData::new();
        unused_ontology.inc_usage_count(1);
        let unused_ontology = ctx.alloc_ontology_data(unused_ontology);
        let mut used_ontology = OntologyData::new();
        used_ontology.inc_usage_count(1);
        let used_ontology = ctx.alloc_ontology_data(used_ontology);
        let mut unused_slot = BackendRepresentativeMemoryCacheSlotItem::new();
        unused_slot.set_ontology_identifier_data_hash(HashMap::from([(1, unused_ontology)]));
        let unused_slot = ctx.alloc_backend_slot_item(unused_slot);
        let mut used_slot = BackendRepresentativeMemoryCacheSlotItem::new();
        used_slot.set_ontology_identifier_data_hash(HashMap::from([(2, used_ontology)]));
        used_slot.inc_reader();
        let used_slot = ctx.alloc_backend_slot_item(used_slot);
        let mut cache = BackendRepresentativeMemoryCache::new(INVALID, "test", INVALID);
        cache.slot_linker = vec![unused_slot, used_slot];

        cache.clean_unused_slots(&mut ctx);

        assert_eq!(cache.slot_linker, vec![used_slot]);
        assert_eq!(cache.reader_slot_released_count, 1);
        assert_eq!(cache.ontology_data_released_count, 1);
        assert_eq!(cache.ontology_data_released_while_slot_update_count, 1);
        assert_eq!(ctx.ontology_data(unused_ontology).get_usage_count(), 0);
        assert_eq!(ctx.ontology_data(used_ontology).get_usage_count(), 1);
    }

    fn neighbour_array_context() -> (
        CacheContext,
        IndividualAssociationDataId,
        LabelCacheItemId,
        LabelCacheItemId,
    ) {
        let mut ctx = CacheContext::new();
        let det_label = alloc_role_label(
            &mut ctx,
            &[(91, false, false, false, false)],
            LabelCacheItemType::NeighbourInstantiatedRoleSetLabel,
        );
        let nondet_label = alloc_role_label(
            &mut ctx,
            &[(91, true, false, false, true)],
            LabelCacheItemType::NeighbourInstantiatedRoleSetLabel,
        );
        ctx.label_cache_item_mut(nondet_label)
            .flags
            .set_nondeterministic_elements(true);

        let mut combination_label = LabelCacheItem::new(INVALID);
        combination_label.cache_item_type =
            LabelCacheItemType::NeighbourInstantiatedRoleSetCombinationLabel;
        let combination_label = ctx.alloc_label_cache_item(combination_label);

        let mut index_hash = HashMap::new();
        index_hash.insert(det_label, 0);
        index_hash.insert(nondet_label, 1);
        let index_data =
            ctx.alloc_label_cache_item_ext_data(LabelCacheItemExtensionData::NeighbourArrayIndex {
                context: INVALID,
                combined_neighbour_role_set_label: combination_label,
                array_size: 2,
                index_neighbour_role_set_label_array: vec![det_label, nondet_label],
                neighbour_role_set_label_index_hash: index_hash,
            });
        let mut array = IndividualRoleSetNeighbourArray::new();
        array.index_data = index_data;
        array.data_array = vec![
            alloc_neighbour_data(&mut ctx, &[1001, 1002]),
            alloc_neighbour_data(&mut ctx, &[2001, 2002]),
        ];
        let array = ctx.alloc_individual_role_set_neighbour_array(array);

        let mut det_resolving = LabelCacheItemTagLabelResolvingDataLinker::new();
        det_resolving.init_tag_label_resolving_data(det_label, 0, true);
        let det_resolving = ctx.alloc_tag_label_resolving_data_linker(det_resolving);
        let mut nondet_resolving = LabelCacheItemTagLabelResolvingDataLinker::new();
        nondet_resolving.init_tag_label_resolving_data(nondet_label, 1, false);
        let nondet_resolving = ctx.alloc_tag_label_resolving_data_linker(nondet_resolving);
        let mut resolving_hash = HashMap::new();
        resolving_hash.insert(91, det_resolving);
        resolving_hash.insert(-91, nondet_resolving);
        let resolving_ext =
            ctx.alloc_label_cache_item_ext_data(LabelCacheItemExtensionData::TagLabelResolving {
                context: INVALID,
                tag_label_resolving_data_linker_hash: resolving_hash,
            });
        ctx.label_cache_item_mut(combination_label)
            .set_extension_data(
                LabelCacheItemExtensionType::TagResolvingHash as Cint64,
                resolving_ext,
            );

        let mut ass_data = IndividualAssociationData::new();
        ass_data.set_role_set_neighbour_array(array);
        ass_data.set_label_cache_entry(
            LabelCacheItemType::NeighbourInstantiatedRoleSetCombinationLabel as Cint64,
            combination_label,
        );
        let ass_data = ctx.alloc_individual_assoc_data(ass_data);
        (ctx, ass_data, det_label, nondet_label)
    }

    fn concept_label_context() -> (
        CacheContext,
        IndividualAssociationDataId,
        LabelCacheItemId,
        LabelCacheItemId,
        LabelCacheItemId,
    ) {
        let mut ctx = CacheContext::new();
        let det_label = alloc_concept_label(
            &mut ctx,
            &[(11, false, true), (12, true, true)],
            LabelCacheItemType::DeterministicConceptSetLabel,
        );
        let nondet_label = alloc_concept_label(
            &mut ctx,
            &[(21, false, false), (22, true, false)],
            LabelCacheItemType::NondeterministicConceptSetLabel,
        );
        let full_label = alloc_concept_label(
            &mut ctx,
            &[
                (11, false, true),
                (12, true, true),
                (21, false, false),
                (22, true, false),
            ],
            LabelCacheItemType::FullConceptSetLabel,
        );
        let mut ass_data = IndividualAssociationData::new();
        ass_data.set_deterministic_concept_set_label_cache_entry(det_label);
        ass_data.set_label_cache_entry(
            LabelCacheItemType::NondeterministicConceptSetLabel as Cint64,
            nondet_label,
        );
        let ass_data = ctx.alloc_individual_assoc_data(ass_data);
        (ctx, ass_data, det_label, nondet_label, full_label)
    }

    #[test]
    fn reader_gets_individual_association_data_from_ontology_vector() {
        let mut ctx = CacheContext::new();
        let ass_data = ctx.alloc_individual_assoc_data(IndividualAssociationData::new());
        let mut ontology_data = OntologyData::new();
        ontology_data.set_individual_id_assoiation_data_vector(
            4,
            vec![
                IndividualAssociationDataId::NONE,
                IndividualAssociationDataId::NONE,
                ass_data,
                IndividualAssociationDataId::NONE,
            ],
        );
        let mut reader = reader_with_ontology_data(&mut ctx, ontology_data);

        assert_eq!(
            reader.get_individual_association_data(2, &mut ctx),
            ass_data
        );
        assert_eq!(
            reader.get_individual_association_data(4, &mut ctx),
            IndividualAssociationDataId::NONE
        );
        assert_eq!(
            reader.get_individual_association_data(-1, &mut ctx),
            IndividualAssociationDataId::NONE
        );
    }

    #[test]
    fn reader_gets_individual_association_data_from_basic_precomputation_vector() {
        let mut ctx = CacheContext::new();
        let direct_ass_data = ctx.alloc_individual_assoc_data(IndividualAssociationData::new());
        let basic_ass_data = ctx.alloc_individual_assoc_data(IndividualAssociationData::new());
        let mut ontology_data = OntologyData::new();
        ontology_data.set_individual_id_assoiation_data_vector(
            3,
            vec![
                IndividualAssociationDataId::NONE,
                direct_ass_data,
                IndividualAssociationDataId::NONE,
            ],
        );
        ontology_data.set_basic_precomputation_mode(true);
        ontology_data.set_basic_precomputation_individual_id_assoiation_data_vector(
            3,
            vec![
                IndividualAssociationDataId::NONE,
                basic_ass_data,
                IndividualAssociationDataId::NONE,
            ],
        );
        let mut reader = reader_with_ontology_data(&mut ctx, ontology_data);

        assert_eq!(
            reader.get_individual_association_data(1, &mut ctx),
            basic_ass_data
        );
    }

    #[test]
    fn reader_gets_individual_associated_cache_label_item() {
        let mut ctx = CacheContext::new();
        let label = ctx.alloc_label_cache_item(LabelCacheItem::new(INVALID));
        let mut ass_data = IndividualAssociationData::new();
        ass_data.set_label_cache_entry(LabelCacheItemType::FullConceptSetLabel as Cint64, label);
        let ass_data = ctx.alloc_individual_assoc_data(ass_data);
        let mut ontology_data = OntologyData::new();
        ontology_data.set_individual_id_assoiation_data_vector(
            2,
            vec![IndividualAssociationDataId::NONE, ass_data],
        );
        let mut reader = reader_with_ontology_data(&mut ctx, ontology_data);

        assert_eq!(
            reader.get_individual_associated_cache_label_item(
                1,
                LabelCacheItemType::FullConceptSetLabel as Cint64,
                &mut ctx,
            ),
            label
        );
        assert_eq!(
            reader.get_individual_associated_cache_label_item(
                1,
                LabelCacheItemType::DeterministicConceptSetLabel as Cint64,
                &mut ctx,
            ),
            LabelCacheItemId::NONE
        );
    }

    #[test]
    fn reader_gets_nominal_indirect_connection_data_from_ontology_hash() {
        let mut ctx = CacheContext::new();
        let nominal_data = ctx
            .alloc_nominal_indirect_connection_data(NominalIndividualIndirectConnectionData::new());
        let mut ontology_data = OntologyData::new();
        ontology_data
            .nominal_indi_id_indirect_connection_data_hash
            .insert(77, nominal_data);
        let mut reader = reader_with_ontology_data(&mut ctx, ontology_data);

        assert_eq!(
            reader.get_nominal_indirect_connection_data(77, &mut ctx),
            nominal_data
        );
        assert_eq!(
            reader.get_nominal_indirect_connection_data(78, &mut ctx),
            NominalIndividualIndirectConnectionDataId::NONE
        );
    }

    #[test]
    fn reader_checks_and_gets_label_signature_cache_entries() {
        let mut ctx = CacheContext::new();
        let label_a = ctx.alloc_label_cache_item(LabelCacheItem::new(INVALID));
        let label_b = ctx.alloc_label_cache_item(LabelCacheItem::new(INVALID));
        let mut resolve_item = LabelSignatureResolveCacheItem::new();
        resolve_item.append_label_item(&[label_a, label_b]);
        let mut ontology_data = OntologyData::new();
        ontology_data.sig_label_item_hash[LabelCacheItemType::FullConceptSetLabel as usize]
            .insert(12345, resolve_item.clone());
        let mut reader = reader_with_ontology_data(&mut ctx, ontology_data);

        assert!(reader.has_cache_entry(
            LabelCacheItemType::FullConceptSetLabel as Cint64,
            12345,
            &mut ctx,
        ));
        assert!(!reader.has_cache_entry(
            LabelCacheItemType::FullConceptSetLabel as Cint64,
            54321,
            &mut ctx,
        ));
        assert_eq!(
            reader
                .get_label_cache_entry(
                    LabelCacheItemType::FullConceptSetLabel as Cint64,
                    12345,
                    &mut ctx,
                )
                .get_label_items(),
            &[label_a, label_b]
        );
        assert_eq!(
            reader
                .get_label_cache_entry(
                    LabelCacheItemType::FullConceptSetLabel as Cint64,
                    54321,
                    &mut ctx,
                )
                .get_label_item_count(),
            0
        );
    }

    #[test]
    fn reader_checks_same_individual_mergings_flag() {
        let mut ctx = CacheContext::new();
        let mut ontology_data = OntologyData::new();
        ontology_data.set_same_individuals_mergings(true);
        let mut reader = reader_with_ontology_data(&mut ctx, ontology_data);

        assert!(reader.has_same_individuals_mergings(&mut ctx));
    }

    #[test]
    fn reader_visits_label_cache_entries_and_stops_on_false() {
        let mut ctx = CacheContext::new();
        let label_a = ctx.alloc_label_cache_item(LabelCacheItem::new(INVALID));
        let label_b = ctx.alloc_label_cache_item(LabelCacheItem::new(INVALID));
        let label_c = ctx.alloc_label_cache_item(LabelCacheItem::new(INVALID));
        let mut first_resolve_item = LabelSignatureResolveCacheItem::new();
        first_resolve_item.append_label_item(&[label_a, label_b]);
        let mut second_resolve_item = LabelSignatureResolveCacheItem::new();
        second_resolve_item.append_label_item(&[label_c]);
        let mut ontology_data = OntologyData::new();
        ontology_data.sig_label_item_hash[LabelCacheItemType::FullConceptSetLabel as usize]
            .insert(1, first_resolve_item);
        ontology_data.sig_label_item_hash[LabelCacheItemType::FullConceptSetLabel as usize]
            .insert(2, second_resolve_item);
        let mut reader = reader_with_ontology_data(&mut ctx, ontology_data);
        let mut visited = Vec::new();

        let any = reader.visit_label_cache_entries(
            LabelCacheItemType::FullConceptSetLabel as Cint64,
            |label| {
                visited.push(label);
                true
            },
            &mut ctx,
        );
        visited.sort_by_key(|label| label.raw);

        assert!(any);
        assert_eq!(visited, vec![label_a, label_b, label_c]);

        let mut stopped = Vec::new();
        let any = reader.visit_label_cache_entries(
            LabelCacheItemType::FullConceptSetLabel as Cint64,
            |label| {
                stopped.push(label);
                false
            },
            &mut ctx,
        );

        assert!(any);
        assert_eq!(stopped.len(), 1);
    }

    #[test]
    fn reader_gets_label_cache_entry_via_provided_cache_values() {
        let mut ctx = CacheContext::new();
        let distractor = alloc_concept_label(
            &mut ctx,
            &[(10, false, true), (12, false, true)],
            LabelCacheItemType::FullConceptSetLabel,
        );
        let matching = alloc_concept_label(
            &mut ctx,
            &[(10, false, true), (11, true, true)],
            LabelCacheItemType::FullConceptSetLabel,
        );
        let mut resolve_item = LabelSignatureResolveCacheItem::new();
        resolve_item.append_label_item(&[distractor, matching]);
        let mut ontology_data = OntologyData::new();
        ontology_data.sig_label_item_hash[LabelCacheItemType::FullConceptSetLabel as usize]
            .insert(909, resolve_item);
        let mut reader = reader_with_ontology_data(&mut ctx, ontology_data);
        let provided = [
            reader.get_cache_value_concept(10, false, true),
            reader.get_cache_value_concept(11, true, true),
        ];
        let mut pos = 0usize;
        let mut reset_count = 0;

        let found = reader.get_label_cache_entry_via_provided_cache_values(
            LabelCacheItemType::FullConceptSetLabel as Cint64,
            909,
            2,
            |reset, tag, cache_value| {
                if reset {
                    reset_count += 1;
                    pos = 0;
                }
                let Some(value) = provided.get(pos).copied() else {
                    return false;
                };
                *tag = value.get_tag();
                *cache_value = value;
                pos += 1;
                true
            },
            &mut ctx,
        );

        assert_eq!(found, matching);
        assert_eq!(reset_count, 2);
    }

    #[test]
    fn reader_get_label_cache_entry_via_provided_cache_values_returns_none_without_match() {
        let mut ctx = CacheContext::new();
        let label = alloc_concept_label(
            &mut ctx,
            &[(10, false, true), (11, true, true)],
            LabelCacheItemType::FullConceptSetLabel,
        );
        let mut resolve_item = LabelSignatureResolveCacheItem::new();
        resolve_item.append_label_item(&[label]);
        let mut ontology_data = OntologyData::new();
        ontology_data.sig_label_item_hash[LabelCacheItemType::FullConceptSetLabel as usize]
            .insert(910, resolve_item);
        let mut reader = reader_with_ontology_data(&mut ctx, ontology_data);
        let provided = [
            reader.get_cache_value_concept(10, false, true),
            reader.get_cache_value_concept(13, false, true),
        ];
        let mut pos = 0usize;

        let found = reader.get_label_cache_entry_via_provided_cache_values(
            LabelCacheItemType::FullConceptSetLabel as Cint64,
            910,
            2,
            |reset, tag, cache_value| {
                if reset {
                    pos = 0;
                }
                let Some(value) = provided.get(pos).copied() else {
                    return false;
                };
                *tag = value.get_tag();
                *cache_value = value;
                pos += 1;
                true
            },
            &mut ctx,
        );

        assert_eq!(found, LabelCacheItemId::NONE);
    }

    #[test]
    fn reader_gets_cache_value_for_resolved_neighbour_label_reference() {
        let mut ctx = CacheContext::new();
        let mut label = LabelCacheItem::new(INVALID);
        label.set_cache_entry_id(4242);
        let label = ctx.alloc_label_cache_item(label);
        let temp_ref = TempLabelReference::from_referred_label_data(label);
        let temp_ref = ctx
            .alloc_backend_temp_write_record(BackendTempWriteRecord::new_label_reference(temp_ref));
        let reader = BackendRepresentativeMemoryCacheReader::new();

        let cache_value = reader.get_cache_value_neighbour_label(temp_ref, &mut ctx);

        assert_eq!(cache_value.get_tag(), 4242);
        assert_eq!(cache_value.get_identification(), label.raw);
        assert_eq!(
            cache_value.get_cache_value_identifier(),
            CacheValueIdentifier::CacheValueTagAndEntry as Cint64
        );
    }

    #[test]
    fn reader_gets_cache_value_for_temporary_neighbour_label_reference() {
        let mut ctx = CacheContext::new();
        let tmp_label_write =
            ctx.alloc_backend_temp_write_record(BackendTempWriteRecord::new_label_write(
                123,
                LabelCacheItemType::NeighbourInstantiatedRoleSetLabel as Cint64,
            ));
        let temp_ref = TempLabelReference::from_referred_temporary_label_data(tmp_label_write);
        let temp_ref = ctx
            .alloc_backend_temp_write_record(BackendTempWriteRecord::new_label_reference(temp_ref));
        let reader = BackendRepresentativeMemoryCacheReader::new();

        let cache_value = reader.get_cache_value_neighbour_label(temp_ref, &mut ctx);

        assert_eq!(cache_value.get_tag(), 0);
        assert_eq!(cache_value.get_identification(), tmp_label_write.raw);
        assert_eq!(
            cache_value.get_cache_value_identifier(),
            CacheValueIdentifier::CacheValueTagAndTemporaryEntry as Cint64
        );
    }

    #[test]
    fn utilities_get_neighbour_role_instantiated_set_linker_signature() {
        let mut ctx = CacheContext::new();
        let mut label = LabelCacheItem::new(INVALID);
        label.set_cache_entry_id(5001);
        let label = ctx.alloc_label_cache_item(label);
        let resolved_ref =
            ctx.alloc_backend_temp_write_record(BackendTempWriteRecord::new_label_reference(
                TempLabelReference::from_referred_label_data(label),
            ));
        let temp_label_write =
            ctx.alloc_backend_temp_write_record(BackendTempWriteRecord::new_label_write(
                77,
                LabelCacheItemType::NeighbourInstantiatedRoleSetLabel as Cint64,
            ));
        let temp_ref =
            ctx.alloc_backend_temp_write_record(BackendTempWriteRecord::new_label_reference(
                TempLabelReference::from_referred_temporary_label_data(temp_label_write),
            ));
        let chain = vec![resolved_ref, temp_ref];
        let qhash = |value: Cint64| {
            let value = value as u64;
            ((value >> 31) ^ value) as u32 as Cint64
        };

        let signature =
            BackendRepresentativeMemoryCacheUtilities::get_neighbour_role_instantiated_set_linker_signature(
                &chain,
                chain.len() as Cint64,
                &mut ctx,
            );

        assert_eq!(signature, qhash(5001) + qhash(temp_label_write.raw));
    }

    #[test]
    fn reader_gets_neighbour_role_instantiated_set_combination_label_cache_entry() {
        let mut ctx = CacheContext::new();
        let mut role_label_a = LabelCacheItem::new(INVALID);
        role_label_a.set_cache_entry_id(6101);
        let role_label_a = ctx.alloc_label_cache_item(role_label_a);
        let mut role_label_b = LabelCacheItem::new(INVALID);
        role_label_b.set_cache_entry_id(6102);
        let role_label_b = ctx.alloc_label_cache_item(role_label_b);
        let ref_a =
            ctx.alloc_backend_temp_write_record(BackendTempWriteRecord::new_label_reference(
                TempLabelReference::from_referred_label_data(role_label_a),
            ));
        let ref_b =
            ctx.alloc_backend_temp_write_record(BackendTempWriteRecord::new_label_reference(
                TempLabelReference::from_referred_label_data(role_label_b),
            ));
        let chain = vec![ref_a, ref_b];

        let reader = BackendRepresentativeMemoryCacheReader::new();
        let values = [
            reader.get_cache_value_neighbour_label(ref_a, &mut ctx),
            reader.get_cache_value_neighbour_label(ref_b, &mut ctx),
        ];
        let mut combination_label = LabelCacheItem::new(INVALID);
        combination_label.cache_item_type =
            LabelCacheItemType::NeighbourInstantiatedRoleSetCombinationLabel;
        combination_label.set_cache_entry_id(7001);
        let mut value_chain = Vec::new();
        for value in values.iter().copied().rev() {
            let mut linker = LabelValueLinker::new();
            linker.init_label_value_linker(value);
            let linker = ctx.alloc_label_value_linker(linker);
            combination_label
                .tag_value_hash
                .insert(value.get_tag(), linker);
            value_chain.insert(0, linker);
        }
        combination_label.add_cache_value_linker(&value_chain);
        let combination_label = ctx.alloc_label_cache_item(combination_label);

        let signature =
            BackendRepresentativeMemoryCacheUtilities::get_neighbour_role_instantiated_set_linker_signature(
                &chain,
                chain.len() as Cint64,
                &mut ctx,
            );
        let mut resolve_item = LabelSignatureResolveCacheItem::new();
        resolve_item.append_label_item(&[combination_label]);
        let mut ontology_data = OntologyData::new();
        ontology_data.sig_label_item_hash
            [LabelCacheItemType::NeighbourInstantiatedRoleSetCombinationLabel as usize]
            .insert(signature, resolve_item);
        let mut reader = reader_with_ontology_data(&mut ctx, ontology_data);

        let found = reader.get_neighbour_role_instantiated_set_compination_label_cache_entry(
            signature,
            chain.len() as Cint64,
            &chain,
            &mut ctx,
        );

        assert_eq!(found, combination_label);
    }

    #[test]
    fn utilities_get_individual_set_signature_set_hashes_all_ids_and_counts() {
        let individual_set = vec![3, 5, -7];
        let mut count = 0;
        let qhash = |value: Cint64| {
            let value = value as u64;
            ((value >> 31) ^ value) as u32 as Cint64
        };

        let signature = BackendRepresentativeMemoryCacheUtilities::get_individual_set_signature_set(
            &individual_set,
            &mut count,
        );

        assert_eq!(count, 3);
        assert_eq!(signature, qhash(3) + qhash(5) + qhash(-7));
    }

    #[test]
    fn reader_gets_individual_set_label_cache_entry_set() {
        let mut ctx = CacheContext::new();
        let mut reader = BackendRepresentativeMemoryCacheReader::new();
        let individual_set = vec![31, 37];
        let mut count = 0;
        let signature = BackendRepresentativeMemoryCacheUtilities::get_individual_set_signature_set(
            &individual_set,
            &mut count,
        );

        let mut distractor = LabelCacheItem::new(INVALID);
        distractor.cache_item_type = LabelCacheItemType::DeterministicSameIndividualSetLabel;
        for value in [
            reader.get_cache_value_individual(31, false),
            reader.get_cache_value_individual(39, false),
        ] {
            let mut linker = LabelValueLinker::new();
            linker.init_label_value_linker(value);
            let linker = ctx.alloc_label_value_linker(linker);
            distractor.tag_value_hash.insert(value.get_tag(), linker);
            distractor.value_linker.push(linker);
            distractor.value_count += 1;
        }
        let distractor = ctx.alloc_label_cache_item(distractor);

        let mut matching = LabelCacheItem::new(INVALID);
        matching.cache_item_type = LabelCacheItemType::DeterministicSameIndividualSetLabel;
        for &indi_id in &individual_set {
            let value = reader.get_cache_value_individual(indi_id, false);
            let mut linker = LabelValueLinker::new();
            linker.init_label_value_linker(value);
            let linker = ctx.alloc_label_value_linker(linker);
            matching.tag_value_hash.insert(value.get_tag(), linker);
            matching.value_linker.push(linker);
            matching.value_count += 1;
        }
        let matching = ctx.alloc_label_cache_item(matching);

        let mut resolve_item = LabelSignatureResolveCacheItem::new();
        resolve_item.append_label_item(&[distractor, matching]);
        let mut ontology_data = OntologyData::new();
        ontology_data.sig_label_item_hash
            [LabelCacheItemType::DeterministicSameIndividualSetLabel as usize]
            .insert(signature, resolve_item);
        reader = reader_with_ontology_data(&mut ctx, ontology_data);

        let found = reader.get_individual_set_label_cache_entry_set(
            LabelCacheItemType::DeterministicSameIndividualSetLabel as Cint64,
            signature,
            &individual_set,
            count,
            &mut ctx,
        );
        let missing = reader.get_individual_set_label_cache_entry_set(
            LabelCacheItemType::DeterministicSameIndividualSetLabel as Cint64,
            signature,
            &[31, 41],
            count,
            &mut ctx,
        );

        assert_eq!(found, matching);
        assert_eq!(missing, LabelCacheItemId::NONE);
    }

    #[test]
    fn utilities_get_individual_set_signature_merging_filters_entries() {
        let entries = vec![
            IndividualMergingHashEntry::new(101, true, Some(3)),
            IndividualMergingHashEntry::new(102, true, None),
            IndividualMergingHashEntry::new(103, false, Some(1)),
            IndividualMergingHashEntry::new(100, true, Some(1)),
        ];
        let mut count = 0;
        let qhash = |value: Cint64| {
            let value = value as u64;
            ((value >> 31) ^ value) as u32 as Cint64
        };

        let signature =
            BackendRepresentativeMemoryCacheUtilities::get_individual_set_signature_merging(
                100, &entries, &mut count, true, 5,
            );

        assert_eq!(count, 2);
        assert_eq!(signature, qhash(101) + qhash(100));
    }

    #[test]
    fn utilities_get_individual_set_signature_distinct_uses_negated_hash_key() {
        let entries = vec![
            DistinctHashEntry::new(-201, Some(2)),
            DistinctHashEntry::new(-202, None),
            DistinctHashEntry::new(203, Some(1)),
            DistinctHashEntry::new(-200, Some(1)),
        ];
        let mut count = 0;
        let qhash = |value: Cint64| {
            let value = value as u64;
            ((value >> 31) ^ value) as u32 as Cint64
        };

        let signature =
            BackendRepresentativeMemoryCacheUtilities::get_individual_set_signature_distinct(
                200, &entries, &mut count, true, 5,
            );

        assert_eq!(count, 2);
        assert_eq!(signature, qhash(201) + qhash(200));
    }

    #[test]
    fn reader_gets_individual_set_label_cache_entry_merging() {
        let mut ctx = CacheContext::new();
        let entries = vec![
            IndividualMergingHashEntry::new(301, true, Some(2)),
            IndividualMergingHashEntry::new(302, true, None),
        ];
        let mut count = 0;
        let signature =
            BackendRepresentativeMemoryCacheUtilities::get_individual_set_signature_merging(
                300, &entries, &mut count, true, 5,
            );
        let matching = alloc_individual_set_label(
            &mut ctx,
            &[301, 300],
            LabelCacheItemType::DeterministicSameIndividualSetLabel,
        );
        let mut resolve_item = LabelSignatureResolveCacheItem::new();
        resolve_item.append_label_item(&[matching]);
        let mut ontology_data = OntologyData::new();
        ontology_data.sig_label_item_hash
            [LabelCacheItemType::DeterministicSameIndividualSetLabel as usize]
            .insert(signature, resolve_item);
        let mut reader = reader_with_ontology_data(&mut ctx, ontology_data);

        let found = reader.get_individual_set_label_cache_entry_merging(
            LabelCacheItemType::DeterministicSameIndividualSetLabel as Cint64,
            signature,
            300,
            &entries,
            count,
            true,
            5,
            &mut ctx,
        );

        assert_eq!(found, matching);
    }

    #[test]
    fn reader_gets_individual_set_label_cache_entry_distinct() {
        let mut ctx = CacheContext::new();
        let entries = vec![
            DistinctHashEntry::new(-401, Some(2)),
            DistinctHashEntry::new(-402, None),
        ];
        let mut count = 0;
        let signature =
            BackendRepresentativeMemoryCacheUtilities::get_individual_set_signature_distinct(
                400, &entries, &mut count, true, 5,
            );
        let matching = alloc_individual_set_label(
            &mut ctx,
            &[401, 400],
            LabelCacheItemType::DeterministicDiffrentIndividualSetLabel,
        );
        let mut resolve_item = LabelSignatureResolveCacheItem::new();
        resolve_item.append_label_item(&[matching]);
        let mut ontology_data = OntologyData::new();
        ontology_data.sig_label_item_hash
            [LabelCacheItemType::DeterministicDiffrentIndividualSetLabel as usize]
            .insert(signature, resolve_item);
        let mut reader = reader_with_ontology_data(&mut ctx, ontology_data);

        let found = reader.get_individual_set_label_cache_entry_distinct(
            LabelCacheItemType::DeterministicDiffrentIndividualSetLabel as Cint64,
            signature,
            400,
            &entries,
            count,
            true,
            5,
            &mut ctx,
        );

        assert_eq!(found, matching);
    }

    #[test]
    fn utilities_get_concept_descriptor_signature_saturation_excludes_positive_concept() {
        let descriptors = vec![
            ConceptDescriptorRecord::new(5001, 71, false, Some(1), false),
            ConceptDescriptorRecord::new(5002, 72, true, Some(1), false),
        ];
        let qhash = |value: Cint64| {
            let value = value as u64;
            ((value >> 31) ^ value) as u32 as Cint64
        };

        let signature =
            BackendRepresentativeMemoryCacheUtilities::get_concept_descriptor_signature_saturation(
                &descriptors,
                0,
                5001,
            );

        assert_eq!(signature, qhash(-72));
    }

    #[test]
    fn utilities_get_concept_descriptor_signature_splits_determinism_and_nominals() {
        let descriptors = vec![
            ConceptDescriptorRecord::new(5101, 81, false, Some(1), false),
            ConceptDescriptorRecord::new(5102, 82, true, None, false),
            ConceptDescriptorRecord::new(5103, 83, false, Some(1), true),
        ];
        let qhash = |value: Cint64| {
            let value = value as u64;
            ((value >> 31) ^ value) as u32 as Cint64
        };

        let mut deterministic_count = 0;
        let deterministic_signature =
            BackendRepresentativeMemoryCacheUtilities::get_concept_descriptor_signature(
                &descriptors,
                &mut deterministic_count,
                true,
                5,
                true,
            );
        let mut nondeterministic_count = 0;
        let nondeterministic_signature =
            BackendRepresentativeMemoryCacheUtilities::get_concept_descriptor_signature(
                &descriptors,
                &mut nondeterministic_count,
                false,
                5,
                true,
            );

        assert_eq!(deterministic_count, 1);
        assert_eq!(deterministic_signature, qhash(81));
        assert_eq!(nondeterministic_count, 1);
        assert_eq!(nondeterministic_signature, qhash(-82));
    }

    #[test]
    fn reader_gets_concept_set_label_cache_entry_saturation() {
        let mut ctx = CacheContext::new();
        let descriptors = vec![
            ConceptDescriptorRecord::new(5201, 91, false, Some(1), false),
            ConceptDescriptorRecord::new(5202, 92, true, Some(1), false),
        ];
        let signature =
            BackendRepresentativeMemoryCacheUtilities::get_concept_descriptor_signature_saturation(
                &descriptors,
                descriptors.len() as Cint64,
                INVALID,
            );
        let matching = alloc_concept_descriptor_label(
            &mut ctx,
            &descriptors,
            &[true, true],
            LabelCacheItemType::FullConceptSetLabel,
        );
        let mut resolve_item = LabelSignatureResolveCacheItem::new();
        resolve_item.append_label_item(&[matching]);
        let mut ontology_data = OntologyData::new();
        ontology_data.sig_label_item_hash[LabelCacheItemType::FullConceptSetLabel as usize]
            .insert(signature, resolve_item);
        let mut reader = reader_with_ontology_data(&mut ctx, ontology_data);

        let found = reader.get_concept_set_label_cache_entry_saturation(
            LabelCacheItemType::FullConceptSetLabel as Cint64,
            signature,
            descriptors.len() as Cint64,
            &descriptors,
            &mut ctx,
        );

        assert_eq!(found, matching);
    }

    #[test]
    fn reader_gets_deterministic_and_nondeterministic_concept_set_label_entries() {
        let mut ctx = CacheContext::new();
        let descriptors = vec![
            ConceptDescriptorRecord::new(5301, 101, false, Some(1), false),
            ConceptDescriptorRecord::new(5302, 102, true, None, false),
            ConceptDescriptorRecord::new(5303, 103, false, Some(1), true),
        ];
        let mut det_count = 0;
        let det_signature =
            BackendRepresentativeMemoryCacheUtilities::get_concept_descriptor_signature(
                &descriptors,
                &mut det_count,
                true,
                5,
                true,
            );
        let mut nondet_count = 0;
        let nondet_signature =
            BackendRepresentativeMemoryCacheUtilities::get_concept_descriptor_signature(
                &descriptors,
                &mut nondet_count,
                false,
                5,
                true,
            );
        let det_label = alloc_concept_descriptor_label(
            &mut ctx,
            &descriptors[0..1],
            &[true],
            LabelCacheItemType::DeterministicConceptSetLabel,
        );
        let nondet_label = alloc_concept_descriptor_label(
            &mut ctx,
            &descriptors[1..2],
            &[true],
            LabelCacheItemType::NondeterministicConceptSetLabel,
        );
        let mut det_resolve = LabelSignatureResolveCacheItem::new();
        det_resolve.append_label_item(&[det_label]);
        let mut nondet_resolve = LabelSignatureResolveCacheItem::new();
        nondet_resolve.append_label_item(&[nondet_label]);
        let mut ontology_data = OntologyData::new();
        ontology_data.sig_label_item_hash
            [LabelCacheItemType::DeterministicConceptSetLabel as usize]
            .insert(det_signature, det_resolve);
        ontology_data.sig_label_item_hash
            [LabelCacheItemType::NondeterministicConceptSetLabel as usize]
            .insert(nondet_signature, nondet_resolve);
        let mut reader = reader_with_ontology_data(&mut ctx, ontology_data);

        let det_found = reader.get_deterministic_concept_set_label_cache_entry(
            det_signature,
            det_count,
            &descriptors,
            5,
            true,
            &mut ctx,
        );
        let nondet_found = reader.get_nondeterministic_concept_set_label_cache_entry(
            nondet_signature,
            nondet_count,
            &descriptors,
            5,
            true,
            &mut ctx,
        );

        assert_eq!(det_found, det_label);
        assert_eq!(nondet_found, nondet_label);
    }

    #[test]
    fn reader_gets_concept_set_label_cache_entry_exclusion() {
        let mut ctx = CacheContext::new();
        let descriptors = vec![
            ConceptDescriptorRecord::new(5401, 111, false, Some(1), false),
            ConceptDescriptorRecord::new(5402, 112, true, Some(1), false),
        ];
        let mut count = 0;
        let signature =
            BackendRepresentativeMemoryCacheUtilities::get_concept_descriptor_signature_with_exclusion(
                &descriptors,
                &mut count,
                |concept, _negated| concept == 5402,
            );
        let matching = alloc_concept_descriptor_label(
            &mut ctx,
            &descriptors[1..2],
            &[true],
            LabelCacheItemType::FullConceptSetLabel,
        );
        let mut resolve_item = LabelSignatureResolveCacheItem::new();
        resolve_item.append_label_item(&[matching]);
        let mut ontology_data = OntologyData::new();
        ontology_data.sig_label_item_hash[LabelCacheItemType::FullConceptSetLabel as usize]
            .insert(signature, resolve_item);
        let mut reader = reader_with_ontology_data(&mut ctx, ontology_data);

        let found = reader.get_concept_set_label_cache_entry_exclusion(
            LabelCacheItemType::FullConceptSetLabel as Cint64,
            signature,
            count,
            &descriptors,
            |concept, _negated| concept == 5402,
            &mut ctx,
        );

        assert_eq!(found, matching);
    }

    #[test]
    fn reader_gets_full_concept_set_label_cache_entry_uses_determinism_callback() {
        let mut ctx = CacheContext::new();
        let descriptors = vec![
            ConceptDescriptorRecord::new(5501, 121, false, Some(1), false),
            ConceptDescriptorRecord::new(5502, 122, true, None, false),
        ];
        let mut count = 0;
        let signature =
            BackendRepresentativeMemoryCacheUtilities::get_concept_descriptor_signature_with_determinism(
                &descriptors,
                &mut count,
                |_concept, _negated| true,
                |_concept, _negated, dep_branch| dep_branch.is_some(),
            );
        let matching = alloc_concept_descriptor_label(
            &mut ctx,
            &descriptors,
            &[true, false],
            LabelCacheItemType::FullConceptSetLabel,
        );
        let mut resolve_item = LabelSignatureResolveCacheItem::new();
        resolve_item.append_label_item(&[matching]);
        let mut ontology_data = OntologyData::new();
        ontology_data.sig_label_item_hash[LabelCacheItemType::FullConceptSetLabel as usize]
            .insert(signature, resolve_item);
        let mut reader = reader_with_ontology_data(&mut ctx, ontology_data);

        let found = reader.get_full_concept_set_label_cache_entry(
            LabelCacheItemType::FullConceptSetLabel as Cint64,
            signature,
            count,
            &descriptors,
            |_concept, _negated| true,
            |_concept, _negated, dep_branch| dep_branch.is_some(),
            &mut ctx,
        );

        assert_eq!(found, matching);
    }

    #[test]
    fn role_assertion_linker_preserves_inversion_flag() {
        let mut linker = RoleAssertionLinker::new();
        linker.init_role_assertion_linker(44, true, false, true, false);

        assert_eq!(linker.role, 44);
        assert!(linker.is_inversed());
        assert!(linker.is_nominal_connected());
        assert!(!linker.is_abox_asserted());
        assert!(!linker.is_nondeterministic());
    }

    #[test]
    fn reader_gets_label_cache_entry_via_role_assertion_linker() {
        let mut ctx = CacheContext::new();
        let mut reader = BackendRepresentativeMemoryCacheReader::new();
        let mut assertion_a = RoleAssertionLinker::new();
        assertion_a.init_role_assertion_linker(51, false, true, false, false);
        let assertion_a = ctx.alloc_role_assertion_linker(assertion_a);
        let mut assertion_b = RoleAssertionLinker::new();
        assertion_b.init_role_assertion_linker(52, true, false, true, true);
        let assertion_b = ctx.alloc_role_assertion_linker(assertion_b);
        let chain = vec![assertion_a, assertion_b];

        let values = [
            reader.get_cache_value_role_qualified(51, false, true, false, false),
            reader.get_cache_value_role_qualified(52, true, false, true, true),
        ];
        let mut label = LabelCacheItem::new(INVALID);
        label.cache_item_type = LabelCacheItemType::NeighbourInstantiatedRoleSetLabel;
        for value in values.iter().copied() {
            let mut value_linker = LabelValueLinker::new();
            value_linker.init_label_value_linker(value);
            let value_linker = ctx.alloc_label_value_linker(value_linker);
            label.tag_value_hash.insert(value.get_tag(), value_linker);
            label.value_linker.push(value_linker);
            label.value_count += 1;
        }
        let label = ctx.alloc_label_cache_item(label);
        let mut resolve_item = LabelSignatureResolveCacheItem::new();
        resolve_item.append_label_item(&[label]);
        let mut ontology_data = OntologyData::new();
        ontology_data.sig_label_item_hash
            [LabelCacheItemType::NeighbourInstantiatedRoleSetLabel as usize]
            .insert(8181, resolve_item);
        reader = reader_with_ontology_data(&mut ctx, ontology_data);

        let found = reader.get_label_cache_entry_via_role_assertion_linker(
            LabelCacheItemType::NeighbourInstantiatedRoleSetLabel as Cint64,
            8181,
            chain.len() as Cint64,
            &chain,
            &mut ctx,
        );

        assert_eq!(found, label);
    }

    #[test]
    fn utilities_get_role_inversed_linker_signature_respects_global_inversion() {
        let role_linker = vec![(71, false), (72, true)];
        let qhash = |value: Cint64| {
            let value = value as u64;
            ((value >> 31) ^ value) as u32 as Cint64
        };

        let signature =
            BackendRepresentativeMemoryCacheUtilities::get_role_inversed_linker_signature(
                &role_linker,
                true,
                role_linker.len() as Cint64,
            );

        assert_eq!(signature, qhash(-71) + qhash(72));
    }

    #[test]
    fn reader_gets_label_cache_entry_via_role_linker() {
        let mut ctx = CacheContext::new();
        let mut reader = BackendRepresentativeMemoryCacheReader::new();
        let role_linker = vec![(81, false), (82, true)];
        let values = [
            reader.get_cache_value_role_qualified(81, false, true, false, false),
            reader.get_cache_value_role_qualified(82, true, false, false, false),
        ];
        let mut label = LabelCacheItem::new(INVALID);
        label.cache_item_type = LabelCacheItemType::NeighbourInstantiatedRoleSetLabel;
        for value in values.iter().copied() {
            let mut value_linker = LabelValueLinker::new();
            value_linker.init_label_value_linker(value);
            let value_linker = ctx.alloc_label_value_linker(value_linker);
            label.tag_value_hash.insert(value.get_tag(), value_linker);
            label.value_linker.push(value_linker);
            label.value_count += 1;
        }
        let label = ctx.alloc_label_cache_item(label);
        let mut resolve_item = LabelSignatureResolveCacheItem::new();
        resolve_item.append_label_item(&[label]);
        let mut ontology_data = OntologyData::new();
        ontology_data.sig_label_item_hash
            [LabelCacheItemType::NeighbourInstantiatedRoleSetLabel as usize]
            .insert(8282, resolve_item);
        reader = reader_with_ontology_data(&mut ctx, ontology_data);

        let found = reader.get_label_cache_entry_via_role_linker(
            LabelCacheItemType::NeighbourInstantiatedRoleSetLabel as Cint64,
            8282,
            role_linker.len() as Cint64,
            &role_linker,
            false,
            81,
            &mut ctx,
        );
        let missing = reader.get_label_cache_entry_via_role_linker(
            LabelCacheItemType::NeighbourInstantiatedRoleSetLabel as Cint64,
            8282,
            role_linker.len() as Cint64,
            &role_linker,
            true,
            81,
            &mut ctx,
        );

        assert_eq!(found, label);
        assert_eq!(missing, LabelCacheItemId::NONE);
    }

    #[test]
    fn reader_visits_label_item_individual_associations_in_iterator_order() {
        let (mut ctx, label) = association_label_context();
        let mut reader = BackendRepresentativeMemoryCacheReader::new();
        let mut visited = Vec::new();

        let any = reader.visit_label_item_individual_id_associations(
            label,
            |indi_id, same_merged| {
                visited.push((indi_id, same_merged));
                true
            },
            true,
            true,
            true,
            &mut ctx,
        );

        assert!(any);
        assert_eq!(
            visited,
            vec![(1, false), (3, true), (3, false), (4, true), (5, false)]
        );
    }

    #[test]
    fn reader_visit_label_item_individual_associations_respects_filters_and_stop() {
        let (mut ctx, label) = association_label_context();
        let mut reader = BackendRepresentativeMemoryCacheReader::new();
        let mut visited = Vec::new();

        let any = reader.visit_label_item_individual_id_associations(
            label,
            |indi_id, same_merged| {
                visited.push((indi_id, same_merged));
                visited.len() < 2
            },
            false,
            false,
            true,
            &mut ctx,
        );

        assert!(any);
        assert_eq!(visited, vec![(4, true), (3, true)]);
    }

    #[test]
    fn reader_visit_label_item_individual_associations_returns_false_without_extension() {
        let mut ctx = CacheContext::new();
        let label = ctx.alloc_label_cache_item(LabelCacheItem::new(INVALID));
        let mut reader = BackendRepresentativeMemoryCacheReader::new();
        let mut called = false;

        let any = reader.visit_label_item_individual_id_associations(
            label,
            |_indi_id, _same_merged| {
                called = true;
                true
            },
            true,
            true,
            true,
            &mut ctx,
        );

        assert!(!any);
        assert!(!called);
    }

    #[test]
    fn reader_visits_individual_ids_of_associated_individual_set_label() {
        let (mut ctx, label) = association_label_context();
        let mut reader = BackendRepresentativeMemoryCacheReader::new();
        let mut visited = Vec::new();

        let any = reader.visit_individual_ids_of_associated_individual_set_label(
            IndividualAssociationDataId::NONE,
            label,
            |indi_id| {
                visited.push(indi_id);
                true
            },
            &mut ctx,
        );

        assert!(any);
        assert_eq!(visited, vec![1, 3, 3, 4, 5]);
    }

    #[test]
    fn reader_visit_individual_ids_of_associated_individual_set_label_respects_stop() {
        let (mut ctx, label) = association_label_context();
        let mut reader = BackendRepresentativeMemoryCacheReader::new();
        let mut visited = Vec::new();

        let any = reader.visit_individual_ids_of_associated_individual_set_label(
            IndividualAssociationDataId::NONE,
            label,
            |indi_id| {
                visited.push(indi_id);
                visited.len() < 3
            },
            &mut ctx,
        );

        assert!(any);
        assert_eq!(visited, vec![1, 3, 3]);
    }

    #[test]
    fn reader_has_individual_ids_in_associated_individual_set_label_checks_all_associations() {
        let (mut ctx, label) = association_label_context();
        let mut reader = BackendRepresentativeMemoryCacheReader::new();

        assert!(
            reader.has_individual_ids_in_associated_individual_set_label(
                IndividualAssociationDataId::NONE,
                label,
                1,
                &mut ctx,
            )
        );
        assert!(
            reader.has_individual_ids_in_associated_individual_set_label(
                IndividualAssociationDataId::NONE,
                label,
                4,
                &mut ctx,
            )
        );
        assert!(
            !reader.has_individual_ids_in_associated_individual_set_label(
                IndividualAssociationDataId::NONE,
                label,
                9,
                &mut ctx,
            )
        );
    }

    #[test]
    fn reader_visits_nominal_indirectly_connected_individual_ids() {
        let mut ctx = CacheContext::new();
        let mut data = NominalIndividualIndirectConnectionData::new();
        data.set_indirectly_connected_individual_id_linker(vec![101, 102, 103]);
        let data = ctx.alloc_nominal_indirect_connection_data(data);
        let mut reader = BackendRepresentativeMemoryCacheReader::new();
        let mut visited = Vec::new();

        let any = reader.visit_nominal_indirectly_connected_individual_ids(
            IndividualAssociationDataId::NONE,
            data,
            |indi_id| {
                visited.push(indi_id);
                visited.len() < 2
            },
            &mut ctx,
        );

        assert!(any);
        assert_eq!(visited, vec![101, 102]);
    }

    #[test]
    fn reader_visit_nominal_indirectly_connected_individual_ids_returns_false_without_linker() {
        let mut ctx = CacheContext::new();
        let data = ctx
            .alloc_nominal_indirect_connection_data(NominalIndividualIndirectConnectionData::new());
        let mut reader = BackendRepresentativeMemoryCacheReader::new();
        let mut called = false;

        assert!(!reader.visit_nominal_indirectly_connected_individual_ids(
            IndividualAssociationDataId::NONE,
            data,
            |_indi_id| {
                called = true;
                true
            },
            &mut ctx,
        ));
        assert!(!called);
        assert!(!reader.visit_nominal_indirectly_connected_individual_ids(
            IndividualAssociationDataId::NONE,
            NominalIndividualIndirectConnectionDataId::NONE,
            |_indi_id| true,
            &mut ctx,
        ));
    }

    #[test]
    fn reader_visits_neighbour_individual_ids_for_array_id_from_cursor() {
        let (mut ctx, ass_data, det_label, _nondet_label) = neighbour_array_context();
        let mut reader = BackendRepresentativeMemoryCacheReader::new();
        let mut visited = Vec::new();
        let mut next_cursor = 0;

        assert!(
            reader.visit_neighbour_individual_ids_for_neighbour_array_id_from_cursor(
                ass_data,
                0,
                |neighbour_id, label, nondeterministic, cursor| {
                    visited.push((neighbour_id, label, nondeterministic));
                    next_cursor = cursor;
                    false
                },
                true,
                0,
                &mut ctx,
            )
        );
        assert_eq!(visited, vec![(1001, det_label, false)]);
        visited.clear();

        let cursor = next_cursor;
        assert!(
            reader.visit_neighbour_individual_ids_for_neighbour_array_id_from_cursor(
                ass_data,
                0,
                |neighbour_id, label, nondeterministic, cursor| {
                    visited.push((neighbour_id, label, nondeterministic));
                    next_cursor = cursor;
                    true
                },
                true,
                cursor,
                &mut ctx,
            )
        );
        assert_eq!(visited, vec![(1002, det_label, false)]);
        assert_eq!(next_cursor, 2);
    }

    #[test]
    fn reader_visits_neighbour_individual_ids_for_role_respects_determinism_filter() {
        let (mut ctx, ass_data, det_label, nondet_label) = neighbour_array_context();
        let mut reader = BackendRepresentativeMemoryCacheReader::new();
        let mut deterministic = Vec::new();
        let mut nondeterministic = Vec::new();

        assert!(reader.visit_neighbour_individual_ids_for_role(
            ass_data,
            91,
            |neighbour_id, label, nondet| {
                deterministic.push((neighbour_id, label, nondet));
                true
            },
            true,
            &mut ctx,
        ));
        assert!(reader.visit_neighbour_individual_ids_for_role(
            ass_data,
            -91,
            |neighbour_id, label, nondet| {
                nondeterministic.push((neighbour_id, label, nondet));
                true
            },
            false,
            &mut ctx,
        ));

        assert_eq!(
            deterministic,
            vec![(1001, det_label, false), (1002, det_label, false)]
        );
        assert_eq!(
            nondeterministic,
            vec![(2001, nondet_label, true), (2002, nondet_label, true)]
        );
    }

    #[test]
    fn reader_visits_neighbour_array_ids_for_role() {
        let (mut ctx, ass_data, det_label, nondet_label) = neighbour_array_context();
        let mut reader = BackendRepresentativeMemoryCacheReader::new();
        let mut deterministic = Vec::new();
        let mut nondeterministic = Vec::new();

        assert!(reader.visit_neighbour_array_ids_for_role(
            ass_data,
            91,
            |array_id, label, nondet| {
                deterministic.push((array_id, label, nondet));
                true
            },
            true,
            &mut ctx,
        ));
        assert!(reader.visit_neighbour_array_ids_for_role(
            ass_data,
            -91,
            |array_id, label, nondet| {
                nondeterministic.push((array_id, label, nondet));
                true
            },
            false,
            &mut ctx,
        ));

        assert_eq!(deterministic, vec![(0, det_label, false)]);
        assert_eq!(nondeterministic, vec![(1, nondet_label, true)]);
    }

    #[test]
    fn reader_visit_neighbour_array_id_from_cursor_respects_determinism_filter() {
        let (mut ctx, ass_data, _det_label, _nondet_label) = neighbour_array_context();
        let mut reader = BackendRepresentativeMemoryCacheReader::new();
        let mut visited = Vec::new();

        assert!(
            reader.visit_neighbour_individual_ids_for_neighbour_array_id_from_cursor(
                ass_data,
                1,
                |neighbour_id, label, nondeterministic, cursor| {
                    visited.push((neighbour_id, label, nondeterministic, cursor));
                    true
                },
                true,
                0,
                &mut ctx,
            )
        );

        assert!(visited.is_empty());
    }

    #[test]
    fn reader_counts_neighbours_by_role_and_array_position() {
        let (mut ctx, ass_data, _det_label, _nondet_label) = neighbour_array_context();
        let mut reader = BackendRepresentativeMemoryCacheReader::new();

        assert_eq!(
            reader.get_neighbour_count_for_array_pos(ass_data, 0, &mut ctx),
            2
        );
        assert_eq!(
            reader.get_neighbour_count_for_array_pos(ass_data, 1, &mut ctx),
            2
        );
        assert_eq!(
            reader.get_neighbour_count_for_array_pos(ass_data, 9, &mut ctx),
            0
        );
        assert_eq!(
            reader.get_neighbour_count_for_role(ass_data, 91, &mut ctx),
            2
        );
        assert_eq!(
            reader.get_neighbour_count_for_role(ass_data, -91, &mut ctx),
            2
        );
        assert_eq!(
            reader.get_neighbour_count_for_role(ass_data, 92, &mut ctx),
            0
        );
    }

    #[test]
    fn reader_visits_associated_deterministic_and_nondeterministic_concept_labels() {
        let (mut ctx, ass_data, _det_label, _nondet_label, _full_label) = concept_label_context();
        let mut reader = BackendRepresentativeMemoryCacheReader::new();
        let mut det_seen = Vec::new();
        let mut nondet_seen = Vec::new();

        let det_any = reader.visit_concepts_of_associated_deterministic_concept_set_label(
            ass_data,
            |concept, negation| {
                det_seen.push((concept, negation));
                true
            },
            &mut ctx,
        );
        let nondet_any = reader.visit_concepts_of_associated_non_deterministic_concept_set_label(
            ass_data,
            |concept, negation| {
                nondet_seen.push((concept, negation));
                true
            },
            &mut ctx,
        );

        assert!(det_any);
        assert!(nondet_any);
        assert_eq!(det_seen, vec![(11, false), (12, true)]);
        assert_eq!(nondet_seen, vec![(21, false), (22, true)]);
    }

    #[test]
    fn reader_has_associated_concept_labels_checks_cache_values() {
        let (mut ctx, ass_data, _det_label, _nondet_label, _full_label) = concept_label_context();
        let mut reader = BackendRepresentativeMemoryCacheReader::new();

        assert!(
            reader.has_concept_in_associated_deterministic_concept_set_label(
                ass_data, 11, false, &mut ctx,
            )
        );
        assert!(
            reader.has_concept_in_associated_deterministic_concept_set_label(
                ass_data, 12, true, &mut ctx,
            )
        );
        assert!(
            !reader.has_concept_in_associated_deterministic_concept_set_label(
                ass_data, 21, false, &mut ctx,
            )
        );
        assert!(
            !reader.has_concept_in_associated_non_deterministic_concept_set_label(
                ass_data, 21, false, &mut ctx,
            )
        );
    }

    #[test]
    fn reader_visits_full_concept_set_label_with_determinism_filters() {
        let (mut ctx, ass_data, _det_label, _nondet_label, full_label) = concept_label_context();
        let mut reader = BackendRepresentativeMemoryCacheReader::new();
        let mut deterministic = Vec::new();
        let mut nondeterministic = Vec::new();

        let det_any = reader.visit_concepts_of_associated_full_concept_set_label(
            ass_data,
            full_label,
            |concept, negation, det| {
                deterministic.push((concept, negation, det));
                true
            },
            true,
            false,
            &mut ctx,
        );
        let nondet_any = reader.visit_concepts_of_full_concept_set_label(
            full_label,
            |concept, negation, det| {
                nondeterministic.push((concept, negation, det));
                true
            },
            false,
            true,
            &mut ctx,
        );

        assert!(det_any);
        assert!(nondet_any);
        assert_eq!(deterministic, vec![(11, false, true), (12, true, true)]);
        assert_eq!(
            nondeterministic,
            vec![(21, false, false), (22, true, false)]
        );
    }

    #[test]
    fn reader_has_full_concept_set_label_respects_determinism_overload() {
        let (mut ctx, ass_data, _det_label, _nondet_label, full_label) = concept_label_context();
        let mut reader = BackendRepresentativeMemoryCacheReader::new();

        assert!(reader.has_concept_in_associated_full_concept_set_label(
            ass_data, full_label, 21, false, &mut ctx,
        ));
        assert!(reader.has_concept_in_associated_full_concept_set_label(
            ass_data, full_label, 22, true, &mut ctx,
        ));
        assert!(
            reader.has_concept_in_associated_full_concept_set_label_with_determinism(
                ass_data, full_label, 21, false, false, &mut ctx,
            )
        );
        assert!(
            !reader.has_concept_in_associated_full_concept_set_label_with_determinism(
                ass_data, full_label, 21, false, true, &mut ctx,
            )
        );
    }

    #[test]
    fn reader_gets_concept_occurrence_in_associated_full_concept_set_label() {
        let (mut ctx, ass_data, _det_label, _nondet_label, full_label) = concept_label_context();
        let mut reader = BackendRepresentativeMemoryCacheReader::new();
        let mut negated = true;
        let mut deterministic = false;

        assert!(
            reader.get_concept_occurrence_in_associated_full_concept_set_label(
                ass_data,
                full_label,
                11,
                &mut negated,
                &mut deterministic,
                &mut ctx,
            )
        );
        assert!(!negated);
        assert!(deterministic);

        assert!(
            reader.get_concept_occurrence_in_associated_full_concept_set_label(
                ass_data,
                full_label,
                22,
                &mut negated,
                &mut deterministic,
                &mut ctx,
            )
        );
        assert!(negated);
        assert!(!deterministic);

        negated = false;
        deterministic = true;
        assert!(
            !reader.get_concept_occurrence_in_associated_full_concept_set_label(
                ass_data,
                full_label,
                99,
                &mut negated,
                &mut deterministic,
                &mut ctx,
            )
        );
        assert!(!negated);
        assert!(deterministic);
    }

    #[test]
    fn reader_visits_roles_of_associated_neighbour_role_set_label() {
        let mut ctx = CacheContext::new();
        let label = alloc_role_label(
            &mut ctx,
            &[
                (31, false, false, false, false),
                (32, true, true, false, false),
                (33, true, false, true, true),
            ],
            LabelCacheItemType::NeighbourInstantiatedRoleSetLabel,
        );
        let mut reader = BackendRepresentativeMemoryCacheReader::new();
        let mut visited = Vec::new();

        let any = reader.visit_roles_of_associated_neigbour_role_set_label(
            IndividualAssociationDataId::NONE,
            label,
            |role, inversed, assertion, nominal, nondeterministic| {
                visited.push((role, inversed, assertion, nominal, nondeterministic));
                true
            },
            &mut ctx,
        );

        assert!(any);
        assert_eq!(
            visited,
            vec![
                (31, false, false, false, false),
                (32, true, true, false, false),
                (33, true, false, true, true)
            ]
        );
    }

    #[test]
    fn reader_has_roles_in_associated_neighbour_role_set_label_variants() {
        let mut ctx = CacheContext::new();
        let label = alloc_role_label(
            &mut ctx,
            &[
                (41, false, false, false, false),
                (42, true, true, false, false),
                (43, true, false, true, true),
            ],
            LabelCacheItemType::NeighbourInstantiatedRoleSetLabel,
        );
        let mut reader = BackendRepresentativeMemoryCacheReader::new();

        assert!(reader.has_role_in_associated_neigbour_role_set_label(
            IndividualAssociationDataId::NONE,
            label,
            42,
            true,
            &mut ctx,
        ));
        assert!(reader.has_role_in_associated_neigbour_role_set_label_full(
            IndividualAssociationDataId::NONE,
            label,
            42,
            true,
            true,
            false,
            false,
            &mut ctx,
        ));
        assert!(!reader.has_role_in_associated_neigbour_role_set_label_full(
            IndividualAssociationDataId::NONE,
            label,
            42,
            true,
            false,
            false,
            false,
            &mut ctx,
        ));
        assert!(
            reader.has_role_in_associated_neigbour_role_set_label_with_nondeterminism(
                IndividualAssociationDataId::NONE,
                label,
                43,
                true,
                true,
                &mut ctx,
            )
        );
        assert!(
            !reader.has_role_in_associated_neigbour_role_set_label_with_nondeterminism(
                IndividualAssociationDataId::NONE,
                label,
                43,
                true,
                false,
                &mut ctx,
            )
        );
    }

    #[test]
    fn reader_visits_label_references_of_neighbour_role_set_combination_label() {
        let mut ctx = CacheContext::new();
        let label_a = alloc_role_label(
            &mut ctx,
            &[(51, false, false, false, false)],
            LabelCacheItemType::NeighbourInstantiatedRoleSetLabel,
        );
        let label_b = alloc_role_label(
            &mut ctx,
            &[(52, true, false, false, false)],
            LabelCacheItemType::NeighbourInstantiatedRoleSetLabel,
        );
        let combination = alloc_label_reference_combination(&mut ctx, &[label_a, label_b]);
        let mut reader = BackendRepresentativeMemoryCacheReader::new();
        let mut visited = Vec::new();

        let any = reader.visit_labels_of_associated_neigbour_role_set_combination_label(
            IndividualAssociationDataId::NONE,
            combination,
            |label| {
                visited.push(label);
                true
            },
            &mut ctx,
        );

        assert!(any);
        assert_eq!(visited, vec![label_a, label_b]);
    }

    #[test]
    fn reader_visits_and_checks_combination_role_set_labels() {
        let mut ctx = CacheContext::new();
        let label = alloc_role_label(
            &mut ctx,
            &[
                (61, false, false, false, false),
                (62, true, false, false, false),
                (63, true, true, false, false),
                (64, true, false, false, true),
            ],
            LabelCacheItemType::NeighbourInstantiatedRoleSetLabel,
        );
        let mut reader = BackendRepresentativeMemoryCacheReader::new();
        let mut combination_roles = Vec::new();
        let mut combined_roles = Vec::new();

        assert!(reader.visit_roles_of_associated_compination_role_set_label(
            IndividualAssociationDataId::NONE,
            label,
            |role, inversed| {
                combination_roles.push((role, inversed));
                true
            },
            &mut ctx,
        ));
        assert!(
            reader.visit_roles_of_associated_combined_neigbour_role_set_label(
                IndividualAssociationDataId::NONE,
                label,
                |role, inversed| {
                    combined_roles.push((role, inversed));
                    true
                },
                &mut ctx,
            )
        );

        assert_eq!(
            combination_roles,
            vec![(61, false), (62, true), (63, false), (64, false)]
        );
        assert_eq!(
            combined_roles,
            vec![(61, false), (62, true), (63, true), (64, true)]
        );
        assert!(reader.has_role_in_associated_compination_role_set_label(
            IndividualAssociationDataId::NONE,
            label,
            63,
            true,
            &mut ctx,
        ));
        assert!(
            !reader.has_role_in_associated_combined_neigbour_role_set_label(
                IndividualAssociationDataId::NONE,
                label,
                63,
                true,
                &mut ctx,
            )
        );
        assert!(
            reader.has_role_in_associated_combined_neigbour_role_set_label(
                IndividualAssociationDataId::NONE,
                label,
                62,
                true,
                &mut ctx,
            )
        );
        assert!(
            reader.has_role_in_associated_neigbour_role_set_label_with_nondeterminism(
                IndividualAssociationDataId::NONE,
                label,
                64,
                true,
                true,
                &mut ctx,
            )
        );
    }

    #[test]
    fn reader_checks_role_to_neighbour_through_neighbour_role_set_hash() {
        let mut ctx = CacheContext::new();
        let label = alloc_role_label(
            &mut ctx,
            &[
                (71, false, false, false, false),
                (72, true, false, false, false),
            ],
            LabelCacheItemType::NeighbourInstantiatedRoleSetLabel,
        );
        let mut hash = IndividualNeighbourRoleSetHash::new();
        hash.set_neighbour_role_set_label(9001, label);
        let hash = ctx.alloc_individual_neighbour_role_set_hash(hash);
        let mut ass_data = IndividualAssociationData::new();
        ass_data.set_neighbour_role_set_hash(hash);
        let ass_data = ctx.alloc_individual_assoc_data(ass_data);
        let mut reader = BackendRepresentativeMemoryCacheReader::new();

        assert!(
            reader.has_role_to_neigbour_in_associated_neighbour_role_set_label(
                ass_data, 9001, 71, false, &mut ctx,
            )
        );
        assert!(
            reader.has_role_to_neigbour_in_associated_neighbour_role_set_label(
                ass_data, 9001, 72, true, &mut ctx,
            )
        );
        assert!(
            !reader.has_role_to_neigbour_in_associated_neighbour_role_set_label(
                ass_data, 9002, 71, false, &mut ctx,
            )
        );
    }

    #[test]
    fn reader_visits_roles_to_neighbour_through_neighbour_role_set_hash() {
        let mut ctx = CacheContext::new();
        let label = alloc_role_label(
            &mut ctx,
            &[
                (81, false, false, false, false),
                (82, true, true, false, true),
            ],
            LabelCacheItemType::NeighbourInstantiatedRoleSetLabel,
        );
        let mut hash = IndividualNeighbourRoleSetHash::new();
        hash.set_neighbour_role_set_label(9101, label);
        let hash = ctx.alloc_individual_neighbour_role_set_hash(hash);
        let mut ass_data = IndividualAssociationData::new();
        ass_data.set_neighbour_role_set_hash(hash);
        let ass_data = ctx.alloc_individual_assoc_data(ass_data);
        let mut reader = BackendRepresentativeMemoryCacheReader::new();
        let mut visited = Vec::new();

        assert!(
            reader.visit_roles_to_neigbour_in_associated_neighbour_role_set_label(
                ass_data,
                9101,
                |role, inversed, assertion, nominal, nondeterministic| {
                    visited.push((role, inversed, assertion, nominal, nondeterministic));
                    true
                },
                &mut ctx,
            )
        );
        assert_eq!(
            visited,
            vec![
                (81, false, false, false, false),
                (82, true, true, false, true)
            ]
        );
        assert!(
            !reader.visit_roles_to_neigbour_in_associated_neighbour_role_set_label(
                ass_data,
                9102,
                |_role, _inversed, _assertion, _nominal, _nondeterministic| true,
                &mut ctx,
            )
        );
    }
}

// ===========================================================================
// CBackendRepresentativeMemoryCacheWriter
// ===========================================================================

/// Port of `CBackendRepresentativeMemoryCacheWriter`.
///
/// The thin mutation facade: forwards a `CacheWriteData` payload (+ memory pool)
/// to the owning cache's `writeCachedData`. In the faithful single-threaded
/// staging (manifest §Concurrency) the worker IS the writer.
#[derive(Debug, Clone)]
pub struct BackendRepresentativeMemoryCacheWriter {
    /// `CBackendRepresentativeMemoryCache* mCache`.
    pub cache: BackendCacheId,
}

impl Default for BackendRepresentativeMemoryCacheWriter {
    fn default() -> Self {
        BackendRepresentativeMemoryCacheWriter {
            cache: BackendCacheId::NONE,
        }
    }
}

impl BackendRepresentativeMemoryCacheWriter {
    /// Port of `CBackendRepresentativeMemoryCacheWriter::CBackendRepresentativeMemoryCacheWriter`
    /// `(CBackendRepresentativeMemoryCache* cache)`.
    pub fn new(cache: BackendCacheId) -> Self {
        BackendRepresentativeMemoryCacheWriter { cache }
    }

    /// Port of `CBackendRepresentativeMemoryCacheWriter::writeCachedData`
    /// (`mCache->writeCachedData(writeData, memoryPools); return this;`).
    /// KONCLUDE-PORT-NOTE[api]: `mCache` is the facade `CBackendRepresentativeMemoryCache*`
    /// resolved against the cache facade arena (ported separately); the forward to the
    /// facade `writeCachedData` is deferred. `memoryPools` is an opaque `CMemoryPool*`
    /// chain [memory-pool]. C++ returns `this` → `&mut Self`. W6-DEFER[api].
    pub fn write_cached_data(
        &mut self,
        _write_data: CacheWriteDataId,
        _memory_pools: Cint64,
    ) -> &mut Self {
        // W6-DEFER[api]: cache_facade(self.cache).write_cached_data(write_data, memory_pools).
        self
    }

    /// Port of `CBackendRepresentativeMemoryCacheWriter::getCache` (`return mCache;`).
    pub fn get_cache(&self) -> BackendCacheId {
        self.cache
    }
}

// ===========================================================================
// Facade helper records (C++ nested classes inside CBackendRepresentativeMemoryCache).
// ===========================================================================

/// Port of `CBackendRepresentativeMemoryCache::CPropagationCutNeighbourArrayHandlingData`
/// (a nested helper grouping the readd / reduction / removal array-position sets).
#[derive(Debug, Default, Clone)]
pub struct PropagationCutNeighbourArrayHandlingData {
    /// `QSet<cint64> mReaddingArrayPosSet`.
    pub readding_array_pos_set: Vec<Cint64>,
    /// `QSet<cint64> mReductionArrayPosSet`.
    pub reduction_array_pos_set: Vec<Cint64>,
    /// `QSet<cint64> mRemovalArrayPosSet`.
    pub removal_array_pos_set: Vec<Cint64>,
}

/// Port of `CBackendRepresentativeMemoryCache::CDeterministicSameHandlingInstallationData`
/// (a nested helper grouping the possible-installation id sets).
#[derive(Debug, Default, Clone)]
pub struct DeterministicSameHandlingInstallationData {
    /// `QSet<cint64> mIdPossibleInstallationSet`.
    pub id_possible_installation_set: Vec<Cint64>,
    /// `QSet<cint64> mIdFirstPossibleInstallationSet`.
    pub id_first_possible_installation_set: Vec<Cint64>,
}

// ===========================================================================
// CBackendRepresentativeMemoryCache  (: CThread, CBackendCache) — the facade
// ===========================================================================

/// Port of `CBackendRepresentativeMemoryCache` (the F1 facade — 5.8k C++ lines).
///
/// The backend representative-memory cache and its own writer thread. It owns the
/// per-ontology data hashes, the slot ring + reader chain, the in-flight write
/// collection buffer, the deterministic-same-as / propagation-cut handling
/// scratch, the configuration flags, and an extensive statistics block.
///
/// KONCLUDE-PORT-NOTE[threading]: the `CThread` base (event loop + watchdog) is
/// infra → opaque `thread_base`. `QMutex` / `QSemaphore` / `QAtomicInt` /
/// `QReadWriteLock` members → opaque `Cint64` `[threading]`. The faithful first
/// port runs the cache single-threaded (worker == writer), preserving the class
/// boundary. The `KONCLUDE_CACHE_DEBUGGING_DATA_GENERATION`-gated debug-string
/// members are omitted (build-flag only).
#[derive(Debug, Clone)]
pub struct BackendRepresentativeMemoryCache {
    /// `CThread` base.  [threading] → opaque (Qt event-loop worker).
    pub thread_base: Cint64,
    /// `CBackendCache` base (F0, `base.rs`).
    pub backend_cache_base: BackendCache,

    /// `CConfiguration* mConfig`.  [api] cross-family → opaque.
    pub config: Cint64,
    /// `CConcreteOntology* mDebugOntology` (public).  [api] → opaque.
    pub debug_ontology: Cint64,

    /// `QHash<cint64, cint64> mIndiContextCountHash`.
    pub indi_context_count_hash: HashMap<Cint64, Cint64>,
    /// `cint64 mIndiContextDebuggingCount = 50`.
    pub indi_context_debugging_count: Cint64,

    /// `CCACHINGHASH<cint64, OntologyData*>* mOntologyIdentifierDataHash`.
    pub ontology_identifier_data_hash: HashMap<Cint64, OntologyDataId>,
    /// `QHash<cint64, OntologyData*> mFixedOntologyIdentifierDataHash`.
    pub fixed_ontology_identifier_data_hash: HashMap<Cint64, OntologyDataId>,
    /// `QReadWriteLock mFixedOntologyIdentifierDataHashLock`.  [threading] → opaque.
    pub fixed_ontology_identifier_data_hash_lock: Cint64,

    /// `CCACHINGHASH<cint64, CBackendRepresentativeMemoryLabelCacheItem*> mTmpIndiIndirectlyConnNomLabelItemHash`.
    pub tmp_indi_indirectly_conn_nom_label_item_hash:
        HashMap<Cint64, super::backend_data::LabelCacheItemId>,
    /// `cint64 mTmpIndiAssocPrevUpdateId`.
    pub tmp_indi_assoc_prev_update_id: Cint64,
    /// `CCACHINGSET<cint64> mPropagationCutIndiSet`.
    pub propagation_cut_indi_set: Vec<Cint64>,

    /// `cint64 mCheckingRemainingIncompletelyHandledCount`.
    pub checking_remaining_incompletely_handled_count: Cint64,
    /// `cint64 mEmptyWriteDataCount`.
    pub empty_write_data_count: Cint64,
    /// `cint64 mWriteDataCount`.
    pub write_data_count: Cint64,
    /// `cint64 mStartWriteCollectCount`.
    pub start_write_collect_count: Cint64,
    /// `cint64 mNextWriteCollectCount`.
    pub next_write_collect_count: Cint64,
    /// `cint64 mCollectCount`.
    pub collect_count: Cint64,
    /// `CMemoryPool* mCollectMemoryPools`.  [memory-pool] → opaque.
    pub collect_memory_pools: Cint64,
    /// `CBackendRepresentativeMemoryCacheWriteData* mCollectWriteData`.
    pub collect_write_data: CacheWriteDataId,

    /// `cint64 mNextIndiUpdateId`.
    pub next_indi_update_id: Cint64,
    /// `cint64 mNextNomConnUpdateId`.
    pub next_nom_conn_update_id: Cint64,
    /// `cint64 mUpdatedIndiCount = 0`.
    pub updated_indi_count: Cint64,
    /// `cint64 mAssociationUpdatedIndiCount = 0`.
    pub association_updated_indi_count: Cint64,
    /// `cint64 mUpdateIncompatibleIndiCount = 0`.
    pub update_incompatible_indi_count: Cint64,
    /// `cint64 mCheckedIndiCount = 0`.
    pub checked_indi_count: Cint64,
    /// `cint64 mCheckIncompatibleIndiCount = 0`.
    pub check_incompatible_indi_count: Cint64,
    /// `cint64 mReducedNeighbourArrayCount = 0`.
    pub reduced_neighbour_array_count: Cint64,

    /// `cint64 mCurrentUpdateHandlingRecomputationId = -1`.
    pub current_update_handling_recomputation_id: Cint64,

    /// `cint64 mReaderSlotUpdateCount`.
    pub reader_slot_update_count: Cint64,
    /// `cint64 mOntologyDataUpdateCount`.
    pub ontology_data_update_count: Cint64,
    /// `cint64 mOntologyDataReleasedCount`.
    pub ontology_data_released_count: Cint64,
    /// `cint64 mOntologyDataReleasedWhileNewCreationCount`.
    pub ontology_data_released_while_new_creation_count: Cint64,
    /// `cint64 mOntologyDataReleasedWhileSlotUpdateCount`.
    pub ontology_data_released_while_slot_update_count: Cint64,
    /// `cint64 mReaderSlotReleasedCount`.
    pub reader_slot_released_count: Cint64,

    /// `QSet<CIndividualReference> mIncompletelyAssociatedIndividualSet`.
    /// [api] CIndividualReference → opaque `Cint64` individual id.
    pub incompletely_associated_individual_set: Vec<Cint64>,
    /// `CCacheStatistics mCacheStat` (by value).
    pub cache_stat: CacheStatistics,

    /// `QHash<cint64, CPropagationCutNeighbourArrayHandlingData*>* mTmpPropCutIndiArrayNeighboursHandlingDataHash`.
    pub tmp_prop_cut_indi_array_neighbours_handling_data_hash:
        HashMap<Cint64, PropagationCutNeighbourArrayHandlingData>,
    /// `QSet<cint64> mTmpCompleteNeighbourSameIndiMergingSet`.
    pub tmp_complete_neighbour_same_indi_merging_set: Vec<Cint64>,
    /// `QHash<cint64,cint64> mTmpDetSameMergingCompletionReferenceHash`.
    pub tmp_det_same_merging_completion_reference_hash: HashMap<Cint64, Cint64>,

    /// `CBackendRepresentativeMemoryCacheSlotItem* mSlotLinker` (chain head → Vec head-front).
    pub slot_linker: Vec<SlotItemId>,
    /// `CBackendRepresentativeMemoryCacheSlotItem* mLastUpdatedSlotLinker`.
    pub last_updated_slot_linker: SlotItemId,
    /// `CBackendRepresentativeMemoryCacheReader* mReaderLinker` (chain head → Vec head-front).
    pub reader_linker: Vec<ReaderId>,

    /// `QMutex mReaderSyncMutex`.  [threading] → opaque.
    pub reader_sync_mutex: Cint64,
    /// `bool mLimitRemainingWritePending`.
    pub limit_remaining_write_pending: bool,
    /// `QSemaphore mRemainingWritePendingSemaphore`.  [threading] → opaque.
    pub remaining_write_pending_semaphore: Cint64,

    /// `CBackendRepresentativeMemoryCacheBaseContext mContext` (by value).
    pub context: BackendRepresentativeMemoryCacheBaseContext,

    /// `bool mConfLateIndividualLabelAssociationIndexing`.
    pub conf_late_individual_label_association_indexing: bool,
    /// `bool mConfWaitIndividualLabelAssociationIndexed`.
    pub conf_wait_individual_label_association_indexed: bool,
    /// `bool mConfDebugWriteRepresentativeCache`.
    pub conf_debug_write_representative_cache: bool,

    /// `bool mConfIncrementUpdateIdForDeterministicSameAsCompletion = true`.
    pub conf_increment_update_id_for_deterministic_same_as_completion: bool,
    /// `cint64 mConfMinRequiredDeterministicSameMergedHandledInstallationPossiblitiesForNeighbourCompletion = 1`.
    pub conf_min_required_deterministic_same_merged_handled_installation_possiblities_for_neighbour_completion:
        Cint64,
    /// `cint64 mConfUnchangedDeterministicSameMergeUpdatesForDeterministicSameNeighbourCompletion = 1`.
    pub conf_unchanged_deterministic_same_merge_updates_for_deterministic_same_neighbour_completion:
        Cint64,

    /// `bool mConfInstallingDeterministicSameHandlingLargeDifferenceReached`.
    pub conf_installing_deterministic_same_handling_large_difference_reached: bool,
    /// `cint64 mConfInstallingDeterministicSameHandlingLargeDifference`.
    pub conf_installing_deterministic_same_handling_large_difference: Cint64,

    /// `double mConfBasicPrecomputationModeActivationUpdateMergesRatio = 0.05`.
    pub conf_basic_precomputation_mode_activation_update_merges_ratio: f64,

    /// `QAtomicInt mPendingUpdateCount`.  [threading] → opaque.
    pub pending_update_count: Cint64,

    /// `cint64 mSlotUpdateWaitingIncreaseCount`.
    pub slot_update_waiting_increase_count: Cint64,
    /// `cint64 mSlotUpdateWaitingMaxCount`.
    pub slot_update_waiting_max_count: Cint64,

    /// `bool mConfDirectUpdateSynchronization`.
    pub conf_direct_update_synchronization: bool,
    /// `QMutex mDirectUpdateSyncMutex`.  [threading] → opaque.
    pub direct_update_sync_mutex: Cint64,

    /// `QHash<cint64, CDeterministicSameHandlingInstallationData> mDeterministicSameHandlingInstallationDataHash`.
    pub deterministic_same_handling_installation_data_hash:
        HashMap<Cint64, DeterministicSameHandlingInstallationData>,

    /// `bool mConfPropagationCutPropagatedConceptDirectInstallation = true`.
    pub conf_propagation_cut_propagated_concept_direct_installation: bool,

    /// `cint64 mConfMaxIncompletelyHandledIndividualsRetrievalCount = -1`.
    pub conf_max_incompletely_handled_individuals_retrieval_count: Cint64,
    /// `cint64 mConfMaxCacheDataUpdateWritingCount = -1`.
    pub conf_max_cache_data_update_writing_count: Cint64,

    /// `double mConfUpdateRejectingIncompatibleIndividualAssociationsRatio = 1.`.
    pub conf_update_rejecting_incompatible_individual_associations_ratio: f64,
    /// `double mConfUpdateRejectingIncompatiblePropagationCuttedIndividualLinkedNeighbourRatio = 1`.
    pub conf_update_rejecting_incompatible_propagation_cutted_individual_linked_neighbour_ratio:
        f64,
    /// `cint64 mConfUpdateRejectingIncompatiblePropagationCuttedIndividualLinkedNeighbourCount = -1`.
    pub conf_update_rejecting_incompatible_propagation_cutted_individual_linked_neighbour_count:
        Cint64,

    /// `bool mConfInterpretUnchangedLabelsAsCompatible = false`.
    pub conf_interpret_unchanged_labels_as_compatible: bool,

    /// `bool mStatCollectStatistics`.
    pub stat_collect_statistics: bool,

    /// `cint64 mStatAddingNeighbourLinksAssociationUpdateCount`.
    pub stat_adding_neighbour_links_association_update_count: Cint64,
    /// `cint64 mStatUpdatedOrRemovedNeighbourLinksAssociationUpdateCount`.
    pub stat_updated_or_removed_neighbour_links_association_update_count: Cint64,
    /// `cint64 mStatMaxSameAsMergedCount`.
    pub stat_max_same_as_merged_count: Cint64,
    /// `cint64 mStatMaxLabelValueCount`.
    pub stat_max_label_value_count: Cint64,
    /// `cint64 mStatMaxAssociationUpdateCount`.
    pub stat_max_association_update_count: Cint64,
    /// `cint64 mStatMaxNeighbourLinksCount`.
    pub stat_max_neighbour_links_count: Cint64,
    /// `cint64 mStatLabelCount`.
    pub stat_label_count: Cint64,

    /// `cint64 mStatLabelTypeCount[LABEL_CACHE_ITEM_TYPE_COUNT]` (16).
    pub stat_label_type_count: Vec<Cint64>,
    /// `cint64 mStatLabelTypeMaxValueCount[LABEL_CACHE_ITEM_TYPE_COUNT]` (16).
    pub stat_label_type_max_value_count: Vec<Cint64>,
    /// `cint64 mStatLabelTypeAllValueCount[LABEL_CACHE_ITEM_TYPE_COUNT]` (16).
    pub stat_label_type_all_value_count: Vec<Cint64>,

    /// `cint64 mStatDetSameRepresentativeMergingCount`.
    pub stat_det_same_representative_merging_count: Cint64,
    /// `cint64 mStatDetSameAssociationInstallCount`.
    pub stat_det_same_association_install_count: Cint64,
    /// `cint64 mStatDetSameAssociationFailedCount`.
    pub stat_det_same_association_failed_count: Cint64,
    /// `cint64 mStatDetSameAssociationDifferentUpdateIdFailedCount`.
    pub stat_det_same_association_different_update_id_failed_count: Cint64,
    /// `cint64 mStatDetSameAssociationDifferentDestIdFailedCount`.
    pub stat_det_same_association_different_dest_id_failed_count: Cint64,
    /// `cint64 mStatDetSameAssociationIncompleteHandledDestFailedCount`.
    pub stat_det_same_association_incomplete_handled_dest_failed_count: Cint64,
    /// `cint64 mStatDetSameAssociationRepMergedDestFailedCount`.
    pub stat_det_same_association_rep_merged_dest_failed_count: Cint64,

    /// `cint64 mStatCreatedNeighbourLinks`.
    pub stat_created_neighbour_links: Cint64,

    /// `cint64 mStatIncompatibleLabelNeighbourCompletionCount`.
    pub stat_incompatible_label_neighbour_completion_count: Cint64,
    /// `cint64 mStatChangedLabelNeighbourCompletionCount`.
    pub stat_changed_label_neighbour_completion_count: Cint64,
    /// `cint64 mStatNeighbourCompletionDetSameSuccededCount`.
    pub stat_neighbour_completion_det_same_succeded_count: Cint64,
    /// `cint64 mStatNeighbourCompletionDetSameUnchangedCount`.
    pub stat_neighbour_completion_det_same_unchanged_count: Cint64,
    /// `cint64 mStatNeighbourCompletionDetSameChangedCount`.
    pub stat_neighbour_completion_det_same_changed_count: Cint64,
    /// `cint64 mStatNeighbourCompletionDetSameIncompatibleCount`.
    pub stat_neighbour_completion_det_same_incompatible_count: Cint64,

    /// `cint64 mStatIndividualAssociationSeparateMemoryManagmentContextCreationCount = 0`.
    pub stat_individual_association_separate_memory_managment_context_creation_count: Cint64,
    /// `cint64 mStatIndividualAssociationSeparateMemoryManagmentContextReuseCount = 0`.
    pub stat_individual_association_separate_memory_managment_context_reuse_count: Cint64,
    /// `cint64 mStatIndividualAssociationSeparateMemoryManagmentSlotReferredCheckingCount = 0`.
    pub stat_individual_association_separate_memory_managment_slot_referred_checking_count: Cint64,
    /// `cint64 mStatIndividualAssociationSeparateMemoryManagmentUnreferredSlotCount = 0`.
    pub stat_individual_association_separate_memory_managment_unreferred_slot_count: Cint64,
    /// `cint64 mStatIndividualAssociationSeparateMemoryManagmentDeletionCount = 0`.
    pub stat_individual_association_separate_memory_managment_deletion_count: Cint64,
    /// `cint64 mStatIndividualAssociationSeparateMemoryManagmentSlotReferredCheckingQueuingCount = 0`.
    pub stat_individual_association_separate_memory_managment_slot_referred_checking_queuing_count:
        Cint64,
    /// `cint64 mStatIndividualAssociationWithoutSeparateMemoryManagmentCount = 0`.
    pub stat_individual_association_without_separate_memory_managment_count: Cint64,
    /// `cint64 mStatIndividualAssociationSeparateMemoryManagmentNeighbourLinkCopyingCount = 0`.
    pub stat_individual_association_separate_memory_managment_neighbour_link_copying_count: Cint64,
    /// `cint64 mStatReportedMaximumHandledRecomputationIdCount = 0`.
    pub stat_reported_maximum_handled_recomputation_id_count: Cint64,
    /// `cint64 mStatMemoryManagmentQueuedCheckingCount = 0`.
    pub stat_memory_managment_queued_checking_count: Cint64,
    /// `cint64 mStatMemoryManagmentScheduledReleasingCount = 0`.
    pub stat_memory_managment_scheduled_releasing_count: Cint64,

    /// `CBackendRepresentativeMemoryCacheOntologyData* mLastHandledOntologyContext = nullptr`.
    pub last_handled_ontology_context: OntologyDataId,
    /// `cint64 mLastMemoryContextDeletionMinValidRecompId = 0`.
    pub last_memory_context_deletion_min_valid_recomp_id: Cint64,
    /// `CBackendRepresentativeMemoryCacheTemporaryPropagationCutDataLinker* mLastHandledPropCutDataLinker = nullptr`.
    pub last_handled_prop_cut_data_linker: BackendTempWriteRecordId,

    /// `bool s1` / `s2` / `s3` (debug toggles).
    pub s1: bool,
    pub s2: bool,
    pub s3: bool,
    /// `cint64 mDebugIndiId = -1`.
    pub debug_indi_id: Cint64,
}

impl Default for BackendRepresentativeMemoryCache {
    fn default() -> Self {
        BackendRepresentativeMemoryCache {
            thread_base: INVALID,
            backend_cache_base: BackendCache::new(),
            config: INVALID,
            debug_ontology: INVALID,
            indi_context_count_hash: HashMap::new(),
            indi_context_debugging_count: 50,
            ontology_identifier_data_hash: HashMap::new(),
            fixed_ontology_identifier_data_hash: HashMap::new(),
            fixed_ontology_identifier_data_hash_lock: INVALID,
            tmp_indi_indirectly_conn_nom_label_item_hash: HashMap::new(),
            tmp_indi_assoc_prev_update_id: 0,
            propagation_cut_indi_set: Vec::new(),
            checking_remaining_incompletely_handled_count: 0,
            empty_write_data_count: 0,
            write_data_count: 0,
            start_write_collect_count: 0,
            next_write_collect_count: 0,
            collect_count: 0,
            collect_memory_pools: INVALID,
            collect_write_data: CacheWriteDataId::NONE,
            next_indi_update_id: 0,
            next_nom_conn_update_id: 0,
            updated_indi_count: 0,
            association_updated_indi_count: 0,
            update_incompatible_indi_count: 0,
            checked_indi_count: 0,
            check_incompatible_indi_count: 0,
            reduced_neighbour_array_count: 0,
            current_update_handling_recomputation_id: -1,
            reader_slot_update_count: 0,
            ontology_data_update_count: 0,
            ontology_data_released_count: 0,
            ontology_data_released_while_new_creation_count: 0,
            ontology_data_released_while_slot_update_count: 0,
            reader_slot_released_count: 0,
            incompletely_associated_individual_set: Vec::new(),
            cache_stat: CacheStatistics::new(),
            tmp_prop_cut_indi_array_neighbours_handling_data_hash: HashMap::new(),
            tmp_complete_neighbour_same_indi_merging_set: Vec::new(),
            tmp_det_same_merging_completion_reference_hash: HashMap::new(),
            slot_linker: Vec::new(),
            last_updated_slot_linker: SlotItemId::NONE,
            reader_linker: Vec::new(),
            reader_sync_mutex: INVALID,
            limit_remaining_write_pending: false,
            remaining_write_pending_semaphore: INVALID,
            context: BackendRepresentativeMemoryCacheBaseContext::new(),
            conf_late_individual_label_association_indexing: false,
            conf_wait_individual_label_association_indexed: false,
            conf_debug_write_representative_cache: false,
            conf_increment_update_id_for_deterministic_same_as_completion: true,
            conf_min_required_deterministic_same_merged_handled_installation_possiblities_for_neighbour_completion: 1,
            conf_unchanged_deterministic_same_merge_updates_for_deterministic_same_neighbour_completion: 1,
            conf_installing_deterministic_same_handling_large_difference_reached: false,
            conf_installing_deterministic_same_handling_large_difference: 0,
            conf_basic_precomputation_mode_activation_update_merges_ratio: 0.05,
            pending_update_count: 0,
            slot_update_waiting_increase_count: 0,
            slot_update_waiting_max_count: 0,
            conf_direct_update_synchronization: false,
            direct_update_sync_mutex: INVALID,
            deterministic_same_handling_installation_data_hash: HashMap::new(),
            conf_propagation_cut_propagated_concept_direct_installation: true,
            conf_max_incompletely_handled_individuals_retrieval_count: -1,
            conf_max_cache_data_update_writing_count: -1,
            conf_update_rejecting_incompatible_individual_associations_ratio: 1.0,
            conf_update_rejecting_incompatible_propagation_cutted_individual_linked_neighbour_ratio: 1.0,
            conf_update_rejecting_incompatible_propagation_cutted_individual_linked_neighbour_count: -1,
            conf_interpret_unchanged_labels_as_compatible: false,
            stat_collect_statistics: false,
            stat_adding_neighbour_links_association_update_count: 0,
            stat_updated_or_removed_neighbour_links_association_update_count: 0,
            stat_max_same_as_merged_count: 0,
            stat_max_label_value_count: 0,
            stat_max_association_update_count: 0,
            stat_max_neighbour_links_count: 0,
            stat_label_count: 0,
            stat_label_type_count: vec![0; 16],
            stat_label_type_max_value_count: vec![0; 16],
            stat_label_type_all_value_count: vec![0; 16],
            stat_det_same_representative_merging_count: 0,
            stat_det_same_association_install_count: 0,
            stat_det_same_association_failed_count: 0,
            stat_det_same_association_different_update_id_failed_count: 0,
            stat_det_same_association_different_dest_id_failed_count: 0,
            stat_det_same_association_incomplete_handled_dest_failed_count: 0,
            stat_det_same_association_rep_merged_dest_failed_count: 0,
            stat_created_neighbour_links: 0,
            stat_incompatible_label_neighbour_completion_count: 0,
            stat_changed_label_neighbour_completion_count: 0,
            stat_neighbour_completion_det_same_succeded_count: 0,
            stat_neighbour_completion_det_same_unchanged_count: 0,
            stat_neighbour_completion_det_same_changed_count: 0,
            stat_neighbour_completion_det_same_incompatible_count: 0,
            stat_individual_association_separate_memory_managment_context_creation_count: 0,
            stat_individual_association_separate_memory_managment_context_reuse_count: 0,
            stat_individual_association_separate_memory_managment_slot_referred_checking_count: 0,
            stat_individual_association_separate_memory_managment_unreferred_slot_count: 0,
            stat_individual_association_separate_memory_managment_deletion_count: 0,
            stat_individual_association_separate_memory_managment_slot_referred_checking_queuing_count: 0,
            stat_individual_association_without_separate_memory_managment_count: 0,
            stat_individual_association_separate_memory_managment_neighbour_link_copying_count: 0,
            stat_reported_maximum_handled_recomputation_id_count: 0,
            stat_memory_managment_queued_checking_count: 0,
            stat_memory_managment_scheduled_releasing_count: 0,
            last_handled_ontology_context: OntologyDataId::NONE,
            last_memory_context_deletion_min_valid_recomp_id: 0,
            last_handled_prop_cut_data_linker: BackendTempWriteRecordId::NONE,
            s1: false,
            s2: false,
            s3: false,
            debug_indi_id: -1,
        }
    }
}

impl BackendRepresentativeMemoryCache {
    /// Port of `CBackendRepresentativeMemoryCache::CBackendRepresentativeMemoryCache`
    /// `(CConfiguration* config, QString threadIdentifierName, CWatchDog* watchDogThread)`.
    ///
    /// KONCLUDE-PORT-NOTE[threading]: the `threadIdentifierName` / `CWatchDog*`
    /// args drive the `CThread` base (infra, not modelled); kept in the signature
    /// for fidelity. `_config` / `_watch_dog_thread` are opaque `Cint64` handles.
    pub fn new(config: Cint64, _thread_identifier_name: &str, _watch_dog_thread: Cint64) -> Self {
        BackendRepresentativeMemoryCache {
            config,
            ..Default::default()
        }
    }

    // W6-CACHE method-batch: createCacheReader / createOntologyFixedCacheReader /
    // createCacheWriter / writeCachedData / getCacheStatistics /
    // getIncompletlyAssociationCachedIndividuals / initializeIndividualsAssociationCaching /
    // reportMaximumHandledRecomputationId / writeStringifiedRepresentativeCacheToFile /
    // createReaderSlotUpdate / cleanUnusedSlots / deleteExpiredIndividualAssociationMemoryContexts /
    // queueIndividualAssociationMemoryContextDeletion / getMinimumSlotReferreringInstalledValidRecomputationId /
    // processCustomsEvents / checkAssociationComplete / installTemporary{Cardinalities,Labels} /
    // installAssociationUpdate{,s} / copyNeighbourIndividualIdLinkers /
    // createLocalizedIndividualAssociationData / getIndividualAssociationDataMemoryContext /
    // updateIndexedAssociationCount (×2) / installDeterministicSameAsAssociationUpdate{,s} /
    // checkRequiresDeterministicSameAsAssociationUpdateInstallation / completeSameAsNeighbours /
    // completeNeighboursForSameAsMerging / completeDeterministicSameAsMergingInformation /
    // udateDeterministicSameAssociations / installNominalIndirectConncetionUpdates /
    // checkAssociationUsage / get{AdditionMerged,Reduced,Extended}Label / addCreatedLabelStatistics /
    // setUpdatedIndividualAssociationData / mark*IndividualAssociation{In,}completelyHandled /
    // requiresIndividualAssociations / get*ExtensionData / prepareOntologyDataUpdate /
    // indexIndividualLabelAssociations / updateInvolvedIndividuals / integratePropagationCut /
    // updatePropagationCutIndividualIncompletelyHandled / storeIndividualIncompletelyMarked /
    // check/handleUpdateRejection / analyseDeterministicSameAsAssociationInstallation /
    // activate/checkBasicPrecompuationMode / isRoleNeighbourLinkLabelItemCompatibility /
    // isCacheValueRole{Inverse,Nondeterministic} / threadStarted/Stopped + debug strings.
}
