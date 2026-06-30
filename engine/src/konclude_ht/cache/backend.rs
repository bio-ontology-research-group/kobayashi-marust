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
    CacheStatistics, CacheEntryWriteData, CacheValue, CacheValueIdentifier, CacheWriteDataType,
};

use super::backend_data::{
    OntologyDataId, BackendTempWriteRecordId,
    LabelSignatureResolveCacheItem, CardinalitySignatureResolveCacheItem,
    LabelCacheItemId, IndividualAssociationDataId, NominalIndividualIndirectConnectionDataId,
    RoleAssertionLinkerId,
};

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
pub type LabelAssociationWriteDataId = Id<BackendRepresentativeMemoryCacheLabelAssociationWriteData>;
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
    pub fn new() -> Self { Self::default() }
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
    pub fn new() -> Self { Self::default() }

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
    pub fn new() -> Self { Self::default() }

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
    pub fn get_temporary_nominal_indirect_connection_data_linker(&self) -> &[BackendTempWriteRecordId] {
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
    pub fn new() -> Self { Self }
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
    pub fn new() -> Self { Self::default() }

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
        BackendRepresentativeMemoryCacheOntologyContext { cache_context, ..Default::default() }
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
    pub fn new() -> Self { Self::default() }

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

impl BackendRepresentativeMemoryCacheUtilities {
    /// Port of `CBackendRepresentativeMemoryCacheUtilities::CBackendRepresentativeMemoryCacheUtilities`.
    pub fn new() -> Self { Self }

    /// Port of `getConceptDescriptorSignature(CConceptSaturationDescriptor*, cint64 count, CConcept* exclusionConcept)`.
    /// KONCLUDE-PORT-NOTE[api]: `conDesLinker` is a process-layer `CConceptSaturationDescriptor*`
    /// chain and `exclusionConcept` a model-layer `CConcept*` — both cross-subtree opaque
    /// here, so the per-link `getConcept()/getConceptTag()/isNegated()` walk (accumulating
    /// `qHash(±tag)`) cannot be resolved. W6-DEFER[api].
    pub fn get_concept_descriptor_signature_saturation(
        _con_des_linker: Cint64, _count: Cint64, _exclusion_concept: Cint64,
    ) -> Cint64 {
        0
    }

    /// Port of `getConceptDescriptorSignature(CConceptDescriptor*, cint64& count, bool deterministic,
    /// cint64 maxDeterministicBranchTag, bool excludePositiveNominalConcepts)`.
    /// KONCLUDE-PORT-NOTE[api]: walks the cross-subtree `CConceptDescriptor*` chain
    /// (`getDependencyTrackPoint()->getBranchingTag()`, `getOperatorCode() == CCNOMINAL`)
    /// — opaque here. W6-DEFER[api]; `count` is the C++ out-param.
    pub fn get_concept_descriptor_signature(
        _con_des_linker: Cint64, count: &mut Cint64, _deterministic: bool,
        _max_deterministic_branch_tag: Cint64, _exclude_positive_nominal_concepts: bool,
    ) -> Cint64 {
        *count = 0;
        0
    }

    /// Port of `getConceptDescriptorSignature(CConceptDescriptor*, cint64& count,
    /// function<bool(CConcept*, bool)> exclusionDetermineFunction)`. W6-DEFER[api]
    /// (cross-subtree `CConceptDescriptor*` chain walk).
    pub fn get_concept_descriptor_signature_with_exclusion(
        _con_des_linker: Cint64, count: &mut Cint64,
        _exclusion_determine_function: impl Fn(Cint64, bool) -> bool,
    ) -> Cint64 {
        *count = 0;
        0
    }

    /// Port of `getConceptDescriptorSignature(CConceptDescriptor*, cint64& count,
    /// function<bool(CConcept*, bool)>, function<bool(CConcept*, bool, CDependencyTrackPoint*)>)`.
    /// W6-DEFER[api] (cross-subtree `CConceptDescriptor*` chain walk).
    pub fn get_concept_descriptor_signature_with_determinism(
        _con_des_linker: Cint64, count: &mut Cint64,
        _exclusion_determine_function: impl Fn(Cint64, bool) -> bool,
        _deterministic_determine_function: impl Fn(Cint64, bool, Cint64) -> bool,
    ) -> Cint64 {
        *count = 0;
        0
    }

    /// Port of `getRoleInversedLinkerSignature(CSortedNegLinker<CRole*>*, bool inversed, cint64 count)`.
    /// KONCLUDE-PORT-NOTE[api]: the role linker is a model-layer `CSortedNegLinker<CRole*>`
    /// chain (opaque); the per-link `getRoleTag()` ^ inversion `qHash(±tag)` accumulation is
    /// deferred. W6-DEFER[api].
    pub fn get_role_inversed_linker_signature(
        _role_linker: Cint64, _inversed: bool, _count: Cint64,
    ) -> Cint64 {
        0
    }

    /// Port of `getNeighbourRoleInstantiatedSetLinkerSignature(
    /// CBackendRepresentativeMemoryCacheTemporaryLabelReferenceDataLinker*, cint64 count)`.
    /// KONCLUDE-PORT-NOTE[api]: walks the temp label-reference chain
    /// (`getReferredLabelData()->getCacheEntryID()` / `getReferredTemporaryLabelData()`) — the
    /// referred label-cache-item / temp-write-record are facade-arena objects, opaque here.
    /// W6-DEFER[api].
    pub fn get_neighbour_role_instantiated_set_linker_signature(
        _neighbour_role_set_linker: Cint64, _count: Cint64,
    ) -> Cint64 {
        0
    }

    /// Port of `getIndividualSetSignature(cint64 indiId, CIndividualMergingHash*, cint64& count,
    /// bool onlyDeterministic, cint64 maxDeterministicBranchTag)`. W6-DEFER[api]
    /// (cross-subtree `CIndividualMergingHash` iteration).
    pub fn get_individual_set_signature_merging(
        _indi_id: Cint64, _indi_merging_hash: Cint64, count: &mut Cint64,
        _only_deterministic: bool, _max_deterministic_branch_tag: Cint64,
    ) -> Cint64 {
        *count = 0;
        0
    }

    /// Port of `getIndividualSetSignature(CPROCESSSET<cint64>* individualSet, cint64& count)`.
    /// W6-DEFER[api] (cross-subtree process-set iteration).
    pub fn get_individual_set_signature_set(
        _individual_set: Cint64, count: &mut Cint64,
    ) -> Cint64 {
        *count = 0;
        0
    }

    /// Port of `getIndividualSetSignature(cint64 indiId, CDistinctHash*, cint64& count,
    /// bool onlyDeterministic, cint64 maxDeterministicBranchTag)`. W6-DEFER[api]
    /// (cross-subtree `CDistinctHash` iteration).
    pub fn get_individual_set_signature_distinct(
        _indi_id: Cint64, _indi_distinct_hash: Cint64, count: &mut Cint64,
        _only_deterministic: bool, _max_deterministic_branch_tag: Cint64,
    ) -> Cint64 {
        *count = 0;
        0
    }

    /// Port of `getSignatureExtensionByCacheValue(cint64 signature, CCacheValue& cacheValue)`
    /// (`signature += qHash((qint64)cacheValue.getTag()); return signature;`).
    /// KONCLUDE-PORT-NOTE[api]: `qHash(qint64)` reproduces Qt5's fold — the same leaf math
    /// `value::CacheValue::q_hash` uses (`((k >> 31) ^ k)` truncated to 32 bits); kept inline
    /// since that helper is private to `value`.
    pub fn get_signature_extension_by_cache_value(signature: Cint64, cache_value: &CacheValue) -> Cint64 {
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
    pub fn new() -> Self { Self::default() }

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
    pub fn set_ontology_identifier_data_hash(&mut self, ont_id_data_hash: BackendSlotPayload) -> &mut Self {
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
    /// [threading] → opaque `Cint64` (atomically published `SlotItemId`).
    pub updated_slot: Cint64,

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
            updated_slot: INVALID,
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
    pub fn new() -> Self { Self::default() }

    // -- slot / ontology-data pinning ------------------------------------------------
    //
    // The slot ring + ontology-data blocks the reader pins live in the facade-owned
    // cache arena (the `CBackendRepresentativeMemoryCache` is ported separately, so
    // there is no arena yet to resolve `SlotItemId` / `OntologyDataId` into objects).
    // Every method that dereferences the current/updated slot or the ontology data is
    // a W6-DEFER[api] faithful stub; the field-only effects that need no arena are kept.

    /// Port of `updateSlot(CBackendRepresentativeMemoryCacheSlotItem* updatedSlot)`.
    /// KONCLUDE-PORT-NOTE[threading]: `mUpdatedSlot.fetchAndStoreOrdered(updatedSlot)`
    /// (atomic publish) then `prevSlot->decReader()`. The atomic + facade-arena
    /// `decReader` are deferred; C++ returns `this` → `&mut Self`. W6-DEFER[api].
    pub fn update_slot(&mut self, _updated_slot: SlotItemId) -> &mut Self {
        // W6-DEFER[api]: prev = atomic_swap(self.updated_slot, updated_slot);
        //                if prev != NONE { slot_mut(prev).dec_reader(); }
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
    /// KONCLUDE-PORT-NOTE[api]: sets `mRecomputationId` (kept), then switches the slot
    /// and validates `recomputationId` against the ontology data's minimum-valid
    /// recomputation id (throwing `CCalculationErrorProcessingException` on violation)
    /// + refreshes the recomputation-reference linker — all facade-arena work, deferred.
    /// C++ returns `this`. W6-DEFER[api].
    pub fn check_recomputation_id_usage(&mut self, recomputation_id: Cint64) -> &mut Self {
        self.recomputation_id = recomputation_id;
        // W6-DEFER[api]: if has_updated_slot_item { switch_to_updated_slot_item() };
        //   resolve mOntologyData from current slot; validate min-valid recomp id
        //   (throw ECINVALIDRECOMPUATIONID); recRefLinker.update_used_recomputation_id(..).
        self
    }

    /// Port of `setWorkingOntology(cint64 ontologyIdentifier)`.
    /// The identifier assignment is kept; the subsequent slot/ontology-data refresh
    /// (`mCurrentSlot->getOntologyData(...)`, honouring `mFixedOntologyData`) is deferred.
    /// C++ returns `this`. W6-DEFER[api].
    pub fn set_working_ontology_by_id(&mut self, ontology_identifier: Cint64) -> &mut Self {
        self.ontology_identifier = ontology_identifier;
        // W6-DEFER[api]: if has_updated_slot_item { switch_to_updated_slot_item() };
        //   self.ontology_data = current_slot.get_ontology_data(self.ontology_identifier);
        //   if self.fixed_ontology_data != NONE { self.ontology_data = self.fixed_ontology_data; }
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
    /// KONCLUDE-PORT-NOTE[threading]: the relaxed atomic load is deferred. W6-DEFER[api].
    pub fn has_updated_slot_item(&self) -> bool {
        // W6-DEFER[api]: atomic_load(self.updated_slot) != NONE.
        false
    }

    /// Port of `switchToUpdatedSlotItem()` [protected]: atomically takes the published
    /// slot, swaps it for the current slot (decReader on the old), and refreshes
    /// `mOntologyData` from it. KONCLUDE-PORT-NOTE[threading]+[api]: atomic swap +
    /// facade-arena slot/ontology-data resolution deferred. W6-DEFER[api].
    pub fn switch_to_updated_slot_item(&mut self) -> bool {
        // W6-DEFER[api]: updated = atomic_swap(self.updated_slot, NONE); if updated != NONE {
        //   prev = self.current_slot; self.current_slot = updated; slot_mut(prev).dec_reader();
        //   self.ontology_data = current_slot.get_ontology_data(self.ontology_identifier);
        //   recRefLinker.update_used_recomputation_id(self.recomputation_id); return true; } false
        false
    }

    /// Port of `hasSameIndividualsMergings()` — derefs `mOntologyData->hasSameIndividualsMergings()`.
    /// W6-DEFER[api] (facade-arena ontology-data deref).
    pub fn has_same_individuals_mergings(&mut self) -> bool {
        false
    }

    // -- label-signature lookup ------------------------------------------------------

    /// Port of `hasCacheEntry(cint64 labelType, cint64 signature)` — tests the ontology
    /// data's per-type signature→label-item hash for `signature`. W6-DEFER[api].
    pub fn has_cache_entry(&mut self, _label_type: Cint64, _signature: Cint64) -> bool {
        false
    }

    /// Port of `getLabelCacheEntry(cint64 labelType, cint64 signature)`.
    /// KONCLUDE-PORT-NOTE[api]: C++ returns a pointer to the hashed
    /// `CBackendRepresentativeMemoryLabelSignatureResolveCacheItem` (or to the reusable
    /// `mEmptySigResCacheItem` scratch when absent). The port returns a clone of the empty
    /// scratch until the facade arena hash is wired. W6-DEFER[api].
    pub fn get_label_cache_entry(&mut self, _label_type: Cint64, _signature: Cint64) -> LabelSignatureResolveCacheItem {
        self.empty_sig_res_cache_item.clone()
    }

    /// Port of `visitLabelCacheEntries(cint64 labelType, function<bool(...)> visitFunc)`.
    /// W6-DEFER[api] (iterates the facade-arena signature→label-item hash chains).
    pub fn visit_label_cache_entries(
        &mut self, _label_type: Cint64, _visit_func: impl FnMut(LabelCacheItemId) -> bool,
    ) -> bool {
        false
    }

    /// Port of `getLabelCacheEntryViaProvidedCacheValues(cint64 labelType, cint64 signature,
    /// cint64 count, function<bool(bool, cint64&, CCacheValue&)> provFunc)`.
    /// W6-DEFER[api] (matches provided cache-values against the facade-arena label items).
    pub fn get_label_cache_entry_via_provided_cache_values(
        &mut self, _label_type: Cint64, _signature: Cint64, _count: Cint64,
        _prov_func: impl FnMut(bool, &mut Cint64, &mut CacheValue) -> bool,
    ) -> LabelCacheItemId {
        LabelCacheItemId::NONE
    }

    /// Port of `getLabelCacheEntryViaRoleLinker(cint64 labelType, cint64 signature, cint64 count,
    /// CSortedNegLinker<CRole*>* roleLinker, bool inversed, CRole* assertedRole = nullptr)`.
    /// W6-DEFER[api] (`roleLinker`/`assertedRole` cross-subtree + facade-arena lookup).
    pub fn get_label_cache_entry_via_role_linker(
        &mut self, _label_type: Cint64, _signature: Cint64, _count: Cint64,
        _role_linker: Cint64, _inversed: bool, _asserted_role: Cint64,
    ) -> LabelCacheItemId {
        LabelCacheItemId::NONE
    }

    /// Port of `getLabelCacheEntryViaRoleAssertionLinker(cint64 labelType, cint64 signature,
    /// cint64 count, CBackendRepresentativeMemoryCacheRoleAssertionLinker* roleAssertionLinker)`.
    /// W6-DEFER[api].
    pub fn get_label_cache_entry_via_role_assertion_linker(
        &mut self, _label_type: Cint64, _signature: Cint64, _count: Cint64,
        _role_assertion_linker: RoleAssertionLinkerId,
    ) -> LabelCacheItemId {
        LabelCacheItemId::NONE
    }

    /// Port of `getNeighbourRoleInstantiatedSetCompinationLabelCacheEntry(cint64 signature,
    /// cint64 count, CBackendRepresentativeMemoryCacheTemporaryLabelReferenceDataLinker*)`.
    /// W6-DEFER[api].
    pub fn get_neighbour_role_instantiated_set_compination_label_cache_entry(
        &mut self, _signature: Cint64, _count: Cint64,
        _neigbour_role_instantiated_set_tmp_label_linker: BackendTempWriteRecordId,
    ) -> LabelCacheItemId {
        LabelCacheItemId::NONE
    }

    /// Port of `getConceptSetLabelCacheEntry(cint64 labelType, cint64 signature, cint64 conCount,
    /// CConceptSaturationDescriptor* conDesLinker)`. W6-DEFER[api].
    pub fn get_concept_set_label_cache_entry_saturation(
        &mut self, _label_type: Cint64, _signature: Cint64, _con_count: Cint64, _con_des_linker: Cint64,
    ) -> LabelCacheItemId {
        LabelCacheItemId::NONE
    }

    /// Port of `getDeterministicConceptSetLabelCacheEntry(...)`
    /// (`return getConceptSetLabelCacheEntry(signature, conCount, conDesLinker, true, ...);`).
    /// W6-DEFER[api] (forwards to the deferred deterministic-flagged variant).
    pub fn get_deterministic_concept_set_label_cache_entry(
        &mut self, signature: Cint64, con_count: Cint64, con_des_linker: Cint64,
        max_deterministic_branch_tag: Cint64, exclude_positive_nominal_concepts: bool,
    ) -> LabelCacheItemId {
        self.get_concept_set_label_cache_entry_descriptor(
            signature, con_count, con_des_linker, true,
            max_deterministic_branch_tag, exclude_positive_nominal_concepts,
        )
    }

    /// Port of `getNondeterministicConceptSetLabelCacheEntry(...)`
    /// (`return getConceptSetLabelCacheEntry(signature, conCount, conDesLinker, false, ...);`).
    pub fn get_nondeterministic_concept_set_label_cache_entry(
        &mut self, signature: Cint64, con_count: Cint64, con_des_linker: Cint64,
        max_deterministic_branch_tag: Cint64, exclude_positive_nominal_concepts: bool,
    ) -> LabelCacheItemId {
        self.get_concept_set_label_cache_entry_descriptor(
            signature, con_count, con_des_linker, false,
            max_deterministic_branch_tag, exclude_positive_nominal_concepts,
        )
    }

    /// Port of `getConceptSetLabelCacheEntry(cint64 signature, cint64 conCount,
    /// CConceptDescriptor* conDesLinker, bool deterministic, cint64 maxDeterministicBranchTag,
    /// bool excludePositiveNominalConcepts)`. W6-DEFER[api].
    pub fn get_concept_set_label_cache_entry_descriptor(
        &mut self, _signature: Cint64, _con_count: Cint64, _con_des_linker: Cint64,
        _deterministic: bool, _max_deterministic_branch_tag: Cint64, _exclude_positive_nominal_concepts: bool,
    ) -> LabelCacheItemId {
        LabelCacheItemId::NONE
    }

    /// Port of `getConceptSetLabelCacheEntry(cint64 labelType, cint64 signature, cint64 conCount,
    /// CConceptDescriptor* conDesLinker, function<bool(CConcept*, bool)> exclusionDetermineFunction)`.
    /// W6-DEFER[api].
    pub fn get_concept_set_label_cache_entry_exclusion(
        &mut self, _label_type: Cint64, _signature: Cint64, _con_count: Cint64, _con_des_linker: Cint64,
        _exclusion_determine_function: impl Fn(Cint64, bool) -> bool,
    ) -> LabelCacheItemId {
        LabelCacheItemId::NONE
    }

    /// Port of `getFullConceptSetLabelCacheEntry(cint64 labelType, cint64 signature, cint64 conCount,
    /// CConceptDescriptor* conDesLinker, function<bool(CConcept*, bool)> exclusionDetermineFunction,
    /// function<bool(CConcept*, bool, CDependencyTrackPoint*)> nondeterministicDetermineFunction)`.
    /// W6-DEFER[api].
    pub fn get_full_concept_set_label_cache_entry(
        &mut self, _label_type: Cint64, _signature: Cint64, _con_count: Cint64, _con_des_linker: Cint64,
        _exclusion_determine_function: impl Fn(Cint64, bool) -> bool,
        _nondeterministic_determine_function: impl Fn(Cint64, bool, Cint64) -> bool,
    ) -> LabelCacheItemId {
        LabelCacheItemId::NONE
    }

    // -- individual association data -------------------------------------------------

    /// Port of `getIndividualAssociationData(CIndividual* individual)`
    /// (`return getIndividualAssociationData(individual->getIndividualID());`).
    /// KONCLUDE-PORT-NOTE[api]: `individual` is a cross-subtree `CIndividual*` (opaque);
    /// resolving `getIndividualID()` is deferred. W6-DEFER[api].
    pub fn get_individual_association_data_for_individual(&mut self, _individual: Cint64) -> IndividualAssociationDataId {
        // W6-DEFER[api]: self.get_individual_association_data(individual.get_individual_id()).
        IndividualAssociationDataId::NONE
    }

    /// Port of `getIndividualAssociationData(cint64 indiId)` — indexes the ontology data's
    /// individual-id → association-data vector (or the basic-precomputation vector).
    /// W6-DEFER[api] (facade-arena ontology-data + vector deref).
    pub fn get_individual_association_data(&mut self, _indi_id: Cint64) -> IndividualAssociationDataId {
        IndividualAssociationDataId::NONE
    }

    /// Port of `getIndividualAssociatedCacheLabelItem(cint64 indiId, cint64 labelType)`.
    /// W6-DEFER[api] (resolves the association data, then `getLabelCacheEntry(labelType)`).
    pub fn get_individual_associated_cache_label_item(&mut self, _indi_id: Cint64, _label_type: Cint64) -> LabelCacheItemId {
        LabelCacheItemId::NONE
    }

    /// Port of `getNominalIndirectConnectionData(cint64 indiId)` — looks up the ontology
    /// data's nominal-indirect-connection hash. W6-DEFER[api].
    pub fn get_nominal_indirect_connection_data(&mut self, _indi_id: Cint64) -> NominalIndividualIndirectConnectionDataId {
        NominalIndividualIndirectConnectionDataId::NONE
    }

    /// Port of `getIndividualSetLabelCacheEntry(cint64 labelType, cint64 signature, cint64 indiId,
    /// CDistinctHash* indiDistinctHash, cint64& count, bool onlyDeterministic, cint64 maxDeterministicBranchTag)`.
    /// W6-DEFER[api] (`CDistinctHash` cross-subtree iteration + facade-arena label match).
    pub fn get_individual_set_label_cache_entry_distinct(
        &mut self, _label_type: Cint64, _signature: Cint64, _indi_id: Cint64, _indi_distinct_hash: Cint64,
        _count: Cint64, _only_deterministic: bool, _max_deterministic_branch_tag: Cint64,
    ) -> LabelCacheItemId {
        LabelCacheItemId::NONE
    }

    /// Port of the `CIndividualMergingHash*` overload of `getIndividualSetLabelCacheEntry`.
    /// W6-DEFER[api].
    pub fn get_individual_set_label_cache_entry_merging(
        &mut self, _label_type: Cint64, _signature: Cint64, _indi_id: Cint64, _indi_merging_hash: Cint64,
        _count: Cint64, _only_deterministic: bool, _max_deterministic_branch_tag: Cint64,
    ) -> LabelCacheItemId {
        LabelCacheItemId::NONE
    }

    /// Port of the `CPROCESSSET<cint64>*` overload of `getIndividualSetLabelCacheEntry`.
    /// W6-DEFER[api].
    pub fn get_individual_set_label_cache_entry_set(
        &mut self, _label_type: Cint64, _signature: Cint64, _individual_set: Cint64, _count: Cint64,
    ) -> LabelCacheItemId {
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
    /// KONCLUDE-PORT-NOTE[api]: needs the cross-subtree `concept->getConceptTag()` and the
    /// `(cint64)concept` identification; the cache-value-identifier selection logic is
    /// faithful but the value cannot be built without resolving `concept`. W6-DEFER[api].
    pub fn get_cache_value_concept(&self, _concept: Cint64, _negation: bool, _deterministic: bool) -> CacheValue {
        CacheValue::new()
    }

    /// Port of `getCacheValue(CRole* role)`. W6-DEFER[api] (`role->getRoleTag()` + `(cint64)role`).
    pub fn get_cache_value_role(&self, _role: Cint64) -> CacheValue {
        CacheValue::new()
    }

    /// Port of `getCacheValue(CRole* role, bool inversed, bool assertionLinkBase = false,
    /// bool nominalConnected = false, bool nondeterministc = false)`. W6-DEFER[api]
    /// (the identifier-selection tree is faithful, but `role` resolution is deferred).
    pub fn get_cache_value_role_qualified(
        &self, _role: Cint64, _inversed: bool, _assertion_link_base: bool,
        _nominal_connected: bool, _nondeterministic: bool,
    ) -> CacheValue {
        CacheValue::new()
    }

    /// Port of `getCacheValue(CBackendRepresentativeMemoryCacheTemporaryLabelReferenceDataLinker*)`.
    /// W6-DEFER[api] (derefs the referred label-cache-item / temp-write-record).
    pub fn get_cache_value_neighbour_label(&self, _neigbour_role_instantiated_set_tmp_label_linker: BackendTempWriteRecordId) -> CacheValue {
        CacheValue::new()
    }

    /// Port of `isCacheValueRoleInverse(const CCacheValue& cacheValue)` (pure identifier test).
    pub fn is_cache_value_role_inverse(&self, cache_value: &CacheValue) -> bool {
        let id = cache_value.get_cache_value_identifier();
        id == CacheValueIdentifier::CacheValTagAndInversedRole as Cint64
            || id == CacheValueIdentifier::CacheValTagAndInversedAssertedRole as Cint64
            || id == CacheValueIdentifier::CacheValTagAndInversedNominalConnectedRole as Cint64
            || id == CacheValueIdentifier::CacheValTagAndNondeterministicInversedRole as Cint64
            || id == CacheValueIdentifier::CacheValTagAndNondeterministicInversedAssertedRole as Cint64
            || id == CacheValueIdentifier::CacheValTagAndNondeterministicInversedNominalConnectedRole as Cint64
    }

    /// Port of `isCacheValueRoleNondeterministic(const CCacheValue& cacheValue)`.
    pub fn is_cache_value_role_nondeterministic(&self, cache_value: &CacheValue) -> bool {
        let id = cache_value.get_cache_value_identifier();
        id == CacheValueIdentifier::CacheValTagAndNondeterministicRole as Cint64
            || id == CacheValueIdentifier::CacheValTagAndNondeterministicInversedRole as Cint64
            || id == CacheValueIdentifier::CacheValTagAndNondeterministicAssertedRole as Cint64
            || id == CacheValueIdentifier::CacheValTagAndNondeterministicInversedAssertedRole as Cint64
            || id == CacheValueIdentifier::CacheValTagAndNondeterministicNominalConnectedRole as Cint64
            || id == CacheValueIdentifier::CacheValTagAndNondeterministicInversedNominalConnectedRole as Cint64
    }

    /// Port of `isCacheValueRoleNominal(const CCacheValue& cacheValue)`.
    pub fn is_cache_value_role_nominal(&self, cache_value: &CacheValue) -> bool {
        let id = cache_value.get_cache_value_identifier();
        id == CacheValueIdentifier::CacheValTagAndNominalConnectedRole as Cint64
            || id == CacheValueIdentifier::CacheValTagAndInversedNominalConnectedRole as Cint64
            || id == CacheValueIdentifier::CacheValTagAndNondeterministicNominalConnectedRole as Cint64
            || id == CacheValueIdentifier::CacheValTagAndNondeterministicInversedNominalConnectedRole as Cint64
    }

    /// Port of `isCacheValueRoleAssertion(const CCacheValue& cacheValue)`.
    pub fn is_cache_value_role_assertion(&self, cache_value: &CacheValue) -> bool {
        let id = cache_value.get_cache_value_identifier();
        id == CacheValueIdentifier::CacheValTagAndAssertedRole as Cint64
            || id == CacheValueIdentifier::CacheValTagAndInversedAssertedRole as Cint64
            || id == CacheValueIdentifier::CacheValTagAndNondeterministicAssertedRole as Cint64
            || id == CacheValueIdentifier::CacheValTagAndNondeterministicInversedAssertedRole as Cint64
    }

    // -- associated-label visit / has queries ----------------------------------------
    //
    // All of these walk facade-arena label cache items / value linkers / extension data
    // and pass cross-subtree CConcept*/CRole*/indi-id to the visit callbacks. They are
    // W6-DEFER[api] faithful stubs until the cache facade arena is wired.

    /// Port of `visitNominalIndirectlyConnectedIndividualIds(assData, nomConnData, visitFunc)`.
    /// W6-DEFER[api].
    pub fn visit_nominal_indirectly_connected_individual_ids(
        &mut self, _ass_data: IndividualAssociationDataId,
        _nom_conn_data: NominalIndividualIndirectConnectionDataId,
        _visit_func: impl FnMut(Cint64) -> bool,
    ) -> bool {
        false
    }

    /// Port of `visitIndividualIdsOfAssociatedIndividualSetLabel(assData, indiSetLabel, visitFunc)`.
    /// W6-DEFER[api].
    pub fn visit_individual_ids_of_associated_individual_set_label(
        &mut self, _ass_data: IndividualAssociationDataId, _indi_set_label: LabelCacheItemId,
        _visit_func: impl FnMut(Cint64) -> bool,
    ) -> bool {
        false
    }

    /// Port of `hasIndividualIdsInAssociatedIndividualSetLabel(assData, indiSetLabel, indiId)`.
    /// W6-DEFER[api].
    pub fn has_individual_ids_in_associated_individual_set_label(
        &mut self, _ass_data: IndividualAssociationDataId, _indi_set_label: LabelCacheItemId, _indi_id: Cint64,
    ) -> bool {
        false
    }

    /// Port of `visitConceptsOfAssociatedDeterministicConceptSetLabel(assData, visitFunc)`.
    /// W6-DEFER[api].
    pub fn visit_concepts_of_associated_deterministic_concept_set_label(
        &mut self, _ass_data: IndividualAssociationDataId, _visit_func: impl FnMut(Cint64, bool) -> bool,
    ) -> bool {
        false
    }

    /// Port of `hasConceptInAssociatedDeterministicConceptSetLabel(assData, concept, negation)`.
    /// W6-DEFER[api].
    pub fn has_concept_in_associated_deterministic_concept_set_label(
        &mut self, _ass_data: IndividualAssociationDataId, _concept: Cint64, _negation: bool,
    ) -> bool {
        false
    }

    /// Port of `visitConceptsOfAssociatedNonDeterministicConceptSetLabel(assData, visitFunc)`.
    /// W6-DEFER[api].
    pub fn visit_concepts_of_associated_non_deterministic_concept_set_label(
        &mut self, _ass_data: IndividualAssociationDataId, _visit_func: impl FnMut(Cint64, bool) -> bool,
    ) -> bool {
        false
    }

    /// Port of `hasConceptInAssociatedNonDeterministicConceptSetLabel(assData, concept, negation)`.
    /// W6-DEFER[api].
    pub fn has_concept_in_associated_non_deterministic_concept_set_label(
        &mut self, _ass_data: IndividualAssociationDataId, _concept: Cint64, _negation: bool,
    ) -> bool {
        false
    }

    /// Port of `visitConceptsOfAssociatedConceptSetLabel(assData, labelItem, visitFunc)`.
    /// W6-DEFER[api].
    pub fn visit_concepts_of_associated_concept_set_label(
        &mut self, _ass_data: IndividualAssociationDataId, _label_item: LabelCacheItemId,
        _visit_func: impl FnMut(Cint64, bool) -> bool,
    ) -> bool {
        false
    }

    /// Port of `hasConceptInAssociatedConceptSetLabel(assData, labelItem, concept, negation)`.
    /// W6-DEFER[api].
    pub fn has_concept_in_associated_concept_set_label(
        &mut self, _ass_data: IndividualAssociationDataId, _label_item: LabelCacheItemId,
        _concept: Cint64, _negation: bool,
    ) -> bool {
        false
    }

    /// Port of `visitConceptsOfFullConceptSetLabel(labelItem, visitFunc, visitDeterministicConcepts,
    /// visitNonDeterministicConcepts)`. W6-DEFER[api].
    pub fn visit_concepts_of_full_concept_set_label(
        &mut self, _label_item: LabelCacheItemId,
        _visit_func: impl FnMut(Cint64, bool, bool) -> bool,
        _visit_deterministic_concepts: bool, _visit_non_deterministic_concepts: bool,
    ) -> bool {
        false
    }

    /// Port of `visitConceptsOfAssociatedFullConceptSetLabel(assData, labelItem, visitFunc, ...)`
    /// (`return visitConceptsOfFullConceptSetLabel(labelItem, visitFunc, ...);`). W6-DEFER[api].
    pub fn visit_concepts_of_associated_full_concept_set_label(
        &mut self, _ass_data: IndividualAssociationDataId, label_item: LabelCacheItemId,
        visit_func: impl FnMut(Cint64, bool, bool) -> bool,
        visit_deterministic_concepts: bool, visit_non_deterministic_concepts: bool,
    ) -> bool {
        self.visit_concepts_of_full_concept_set_label(
            label_item, visit_func, visit_deterministic_concepts, visit_non_deterministic_concepts,
        )
    }

    /// Port of `hasConceptInAssociatedFullConceptSetLabel(assData, labelItem, concept, negation)`.
    /// W6-DEFER[api].
    pub fn has_concept_in_associated_full_concept_set_label(
        &mut self, _ass_data: IndividualAssociationDataId, _label_item: LabelCacheItemId,
        _concept: Cint64, _negation: bool,
    ) -> bool {
        false
    }

    /// Port of the determinism-qualified overload `hasConceptInAssociatedFullConceptSetLabel(
    /// assData, labelItem, concept, negation, deterministic)`. W6-DEFER[api].
    pub fn has_concept_in_associated_full_concept_set_label_with_determinism(
        &mut self, _ass_data: IndividualAssociationDataId, _label_item: LabelCacheItemId,
        _concept: Cint64, _negation: bool, _deterministic: bool,
    ) -> bool {
        false
    }

    /// Port of `getConceptOccurrenceInAssociatedFullConceptSetLabel(assData, labelItem, concept,
    /// bool& negationFlag, bool& deterministicFlag)`. W6-DEFER[api]; `negation_flag` /
    /// `deterministic_flag` are the C++ out-params.
    pub fn get_concept_occurrence_in_associated_full_concept_set_label(
        &mut self, _ass_data: IndividualAssociationDataId, _label_item: LabelCacheItemId,
        _concept: Cint64, _negation_flag: &mut bool, _deterministic_flag: &mut bool,
    ) -> bool {
        false
    }

    // -- neighbour role-set array queries --------------------------------------------

    /// Port of `visitNeighbourIndividualIdsForNeighbourArrayIdFromCursor(assData, arrayId,
    /// visitFunc, visitOnlyDeterministicNeighbours = true, cursor = 0)`. W6-DEFER[api].
    pub fn visit_neighbour_individual_ids_for_neighbour_array_id_from_cursor(
        &mut self, _ass_data: IndividualAssociationDataId, _array_id: Cint64,
        _visit_func: impl FnMut(Cint64, LabelCacheItemId, bool, Cint64) -> bool,
        _visit_only_deterministic_neighbours: bool, _cursor: Cint64,
    ) -> bool {
        false
    }

    /// Port of `visitNeighbourIndividualIdsForRole(assData, role, visitFunc,
    /// visitOnlyDeterministicNeighbours = true)`. W6-DEFER[api].
    pub fn visit_neighbour_individual_ids_for_role(
        &mut self, _ass_data: IndividualAssociationDataId, _role: Cint64,
        _visit_func: impl FnMut(Cint64, LabelCacheItemId, bool) -> bool,
        _visit_only_deterministic_neighbours: bool,
    ) -> bool {
        false
    }

    /// Port of `visitNeighbourArrayIdsForRole(assData, role, visitFunc,
    /// visitOnlyDeterministicNeighbours = true)`. W6-DEFER[api].
    pub fn visit_neighbour_array_ids_for_role(
        &mut self, _ass_data: IndividualAssociationDataId, _role: Cint64,
        _visit_func: impl FnMut(Cint64, LabelCacheItemId, bool) -> bool,
        _visit_only_deterministic_neighbours: bool,
    ) -> bool {
        false
    }

    /// Port of `getNeighbourCountForRole(assData, role)`. W6-DEFER[api].
    pub fn get_neighbour_count_for_role(&mut self, _ass_data: IndividualAssociationDataId, _role: Cint64) -> Cint64 {
        0
    }

    /// Port of `getNeighbourCountForArrayPos(assData, pos)`. W6-DEFER[api].
    pub fn get_neighbour_count_for_array_pos(&mut self, _ass_data: IndividualAssociationDataId, _pos: Cint64) -> Cint64 {
        0
    }

    // -- neighbour / combination role-set label queries ------------------------------

    /// Port of `visitRolesOfAssociatedNeigbourRoleSetLabel(assData, neighbourRoleSetLabel, visitFunc)`.
    /// W6-DEFER[api].
    pub fn visit_roles_of_associated_neigbour_role_set_label(
        &mut self, _ass_data: IndividualAssociationDataId, _neighbour_role_set_label: LabelCacheItemId,
        _visit_func: impl FnMut(Cint64, bool, bool, bool, bool) -> bool,
    ) -> bool {
        false
    }

    /// Port of `hasRoleInAssociatedNeigbourRoleSetLabel(assData, label, role, inversed,
    /// assertionLinkBase, nominalLinkBase, nondeterministic)`. W6-DEFER[api].
    pub fn has_role_in_associated_neigbour_role_set_label_full(
        &mut self, _ass_data: IndividualAssociationDataId, _neighbour_role_set_label: LabelCacheItemId,
        _role: Cint64, _inversed: bool, _assertion_link_base: bool, _nominal_link_base: bool, _nondeterministic: bool,
    ) -> bool {
        false
    }

    /// Port of the `(assData, label, role, inversed)` overload of
    /// `hasRoleInAssociatedNeigbourRoleSetLabel`. W6-DEFER[api].
    pub fn has_role_in_associated_neigbour_role_set_label(
        &mut self, _ass_data: IndividualAssociationDataId, _neighbour_role_set_label: LabelCacheItemId,
        _role: Cint64, _inversed: bool,
    ) -> bool {
        false
    }

    /// Port of the `(assData, label, role, inversed, nondeterministic)` overload of
    /// `hasRoleInAssociatedNeigbourRoleSetLabel`. W6-DEFER[api].
    pub fn has_role_in_associated_neigbour_role_set_label_with_nondeterminism(
        &mut self, _ass_data: IndividualAssociationDataId, _neighbour_role_set_label: LabelCacheItemId,
        _role: Cint64, _inversed: bool, _nondeterministic: bool,
    ) -> bool {
        false
    }

    /// Port of `hasRoleInAssociatedCombinedNeigbourRoleSetLabel(assData, label, role, inversed)`.
    /// W6-DEFER[api].
    pub fn has_role_in_associated_combined_neigbour_role_set_label(
        &mut self, _ass_data: IndividualAssociationDataId, _neighbour_role_set_label: LabelCacheItemId,
        _role: Cint64, _inversed: bool,
    ) -> bool {
        false
    }

    /// Port of `visitLabelsOfAssociatedNeigbourRoleSetCombinationLabel(assData,
    /// neighbourRoleSetCompinationLabel, visitFunc)`. W6-DEFER[api].
    pub fn visit_labels_of_associated_neigbour_role_set_combination_label(
        &mut self, _ass_data: IndividualAssociationDataId, _neighbour_role_set_compination_label: LabelCacheItemId,
        _visit_func: impl FnMut(LabelCacheItemId) -> bool,
    ) -> bool {
        false
    }

    /// Port of `visitRolesOfAssociatedCompinationRoleSetLabel(assData, combinationRoleSetLabel, visitFunc)`.
    /// W6-DEFER[api].
    pub fn visit_roles_of_associated_compination_role_set_label(
        &mut self, _ass_data: IndividualAssociationDataId, _combination_role_set_label: LabelCacheItemId,
        _visit_func: impl FnMut(Cint64, bool) -> bool,
    ) -> bool {
        false
    }

    /// Port of `hasRoleInAssociatedCompinationRoleSetLabel(assData, compinationRoleSetLabel, role, inversed)`.
    /// W6-DEFER[api].
    pub fn has_role_in_associated_compination_role_set_label(
        &mut self, _ass_data: IndividualAssociationDataId, _compination_role_set_label: LabelCacheItemId,
        _role: Cint64, _inversed: bool,
    ) -> bool {
        false
    }

    /// Port of `visitRolesOfAssociatedCombinedNeigbourRoleSetLabel(assData, neighbourRoleSetLabel, visitFunc)`.
    /// W6-DEFER[api].
    pub fn visit_roles_of_associated_combined_neigbour_role_set_label(
        &mut self, _ass_data: IndividualAssociationDataId, _neighbour_role_set_label: LabelCacheItemId,
        _visit_func: impl FnMut(Cint64, bool) -> bool,
    ) -> bool {
        false
    }

    /// Port of `hasRoleToNeigbourInAssociatedNeighbourRoleSetLabel(assData, neighbourIndiId, role, inversed)`.
    /// W6-DEFER[api].
    pub fn has_role_to_neigbour_in_associated_neighbour_role_set_label(
        &mut self, _ass_data: IndividualAssociationDataId, _neighbour_indi_id: Cint64, _role: Cint64, _inversed: bool,
    ) -> bool {
        false
    }

    /// Port of `visitRolesToNeigbourInAssociatedNeighbourRoleSetLabel(assData, neighbourIndiId, visitFunc)`.
    /// W6-DEFER[api].
    pub fn visit_roles_to_neigbour_in_associated_neighbour_role_set_label(
        &mut self, _ass_data: IndividualAssociationDataId, _neighbour_indi_id: Cint64,
        _visit_func: impl FnMut(Cint64, bool, bool, bool, bool) -> bool,
    ) -> bool {
        false
    }

    /// Port of `visitLabelItemIndividualIdAssociations(labelItem, visitFunc, ascending = true,
    /// visitBaseIndividual = true, visitSameMergedIndividuals = true)`. W6-DEFER[api]
    /// (the individual-association-map extension-data iterator).
    pub fn visit_label_item_individual_id_associations(
        &mut self, _label_item: LabelCacheItemId,
        _visit_func: impl FnMut(Cint64, bool) -> bool,
        _ascending: bool, _visit_base_individual: bool, _visit_same_merged_individuals: bool,
    ) -> bool {
        false
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
        BackendRepresentativeMemoryCacheWriter { cache: BackendCacheId::NONE }
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
    pub fn write_cached_data(&mut self, _write_data: CacheWriteDataId, _memory_pools: Cint64) -> &mut Self {
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
    pub tmp_indi_indirectly_conn_nom_label_item_hash: HashMap<Cint64, super::backend_data::LabelCacheItemId>,
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
    pub conf_min_required_deterministic_same_merged_handled_installation_possiblities_for_neighbour_completion: Cint64,
    /// `cint64 mConfUnchangedDeterministicSameMergeUpdatesForDeterministicSameNeighbourCompletion = 1`.
    pub conf_unchanged_deterministic_same_merge_updates_for_deterministic_same_neighbour_completion: Cint64,

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
    pub conf_update_rejecting_incompatible_propagation_cutted_individual_linked_neighbour_ratio: f64,
    /// `cint64 mConfUpdateRejectingIncompatiblePropagationCuttedIndividualLinkedNeighbourCount = -1`.
    pub conf_update_rejecting_incompatible_propagation_cutted_individual_linked_neighbour_count: Cint64,

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
    pub stat_individual_association_separate_memory_managment_slot_referred_checking_queuing_count: Cint64,
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
        BackendRepresentativeMemoryCache { config, ..Default::default() }
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
