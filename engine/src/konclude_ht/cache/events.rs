//! `cache::events` — F8 cache events (Konclude
//! `Source/Reasoner/Kernel/Cache/Events/`, ~1.8k lines, 11 event classes).
//!
//! Derivative work of Konclude (LGPLv3); see `konclude_ht/PORT.md §License note`.
//! Keep this directory self-contained and LGPL-scoped.
//!
//! ## What these are (the concurrency seam)
//! The caches (F0–F7) are the only structures shared across the hypertableau
//! worker threads. Mutation is NOT applied inline: a worker posts a `CWrite*Event`
//! message that a dedicated *writer* thread drains and applies, while workers read
//! through per-thread `*Reader` cursors. These 11 `CCustomEvent` subclasses ARE
//! those messages — the Reader / Writer / **Event** split is the threading model
//! (manifest/07-cache.md §Concurrency). So this file is the message payload set;
//! the writer that consumes them lives with each cache facade (F1–F7).
//!
//! ## Record-family → one tagged enum (mirrors the W2 `DependencyNode` collapse)
//! Konclude has one `CCustomEvent` subclass per cache write/coordination message,
//! each adding only its own payload fields over the shared `CCustomEvent` base.
//! Per manifest/07-cache.md the 11 collapse to ONE tagged enum `CacheEvent`, one
//! variant per event carrying that event's fields faithfully. The discriminant
//! replaces the per-class `static const QEvent::Type EVENTTYPE`; the codes are
//! reproduced as the `EVENT_*` consts below (from `Cache/CacheSettings.h`).
//!
//! KONCLUDE-PORT-NOTE[threading]: the shared `Concurrent::Events::CCustomEvent`
//! base carries `QEvent::Type type` (→ the enum discriminant + `EVENT_*` codes)
//! and an unused `void* obj` (`set/getObject`, defaulted to `0` by every cache
//! event ctor — folded out; re-add an `object: Cint64` field if a consumer needs
//! it). No separate base struct is emitted: the base IS the enum.
//!
//! KONCLUDE-PORT-NOTE[threading]: KM runs process-per-ontology, so the first
//! faithful port can drain this event channel single-threaded (the worker IS the
//! writer — apply each `CacheEvent` inline after producing it), deferring true
//! cross-thread Reader/Writer concurrency. The class boundary is preserved here so
//! real concurrency can be re-enabled later.

#![allow(dead_code)]

use super::super::model::substrate::{Cint64, Id};

// --- shared event-type codes (Port of `Cache/CacheSettings.h` `EVENT*` consts) ---
// Konclude declares these as `(QEvent::Type)200x`; kept as `Cint64` so the ported
// discriminant round-trips with the original `EVENTTYPE` statics.
pub const EVENT_WRITE_UNSATISFIABLE_CACHE_ENTRY: Cint64 = 2000;
pub const EVENT_WRITE_SATISFIABLE_CACHE_ENTRY: Cint64 = 2001;
pub const EVENT_WRITE_EXPAND_CACHED_ENTRY: Cint64 = 2002;
pub const EVENT_WRITE_SATISFIABLE_BRANCH_CACHED_ENTRY: Cint64 = 2003;
pub const EVENT_WRITE_CACHED_DATA_ENTRY: Cint64 = 2004;
pub const EVENT_WRITE_SATURATION_CACHE_DATA_ENTRY: Cint64 = 2005;
pub const EVENT_WRITE_COMPUTED_CONSEQUENCES_CACHE_DATA_ENTRY: Cint64 = 2006;
pub const EVENT_WRITE_BACKEND_ASSOCIATION_ENTRY: Cint64 = 2007;
pub const EVENT_RETRIEVE_INCOMPLETELY_ASSOCIATION_CACHED: Cint64 = 2008;
pub const EVENT_INITIALIZE_INDIVIDUALS_ASSOCIATIONS_CACHE: Cint64 = 2009;
pub const EVENT_REPORT_MAXIMUM_HANDLED_RECOMPUTATION_ID: Cint64 = 2010;

// --- W6-CACHE placeholder markers for not-yet-ported referenced types ---------
// KONCLUDE-PORT-NOTE[api]: F8 is the SECOND cache unit (after `cache/value.rs`);
// these payload types belong to caches not yet ported (F0–F7). Declared here as
// opaque marker structs (the `process/stubs.rs` precedent) so the event payloads
// stay typed and this file is self-contained; on the reconcile pass each is
// replaced by an import of the real ported type (`super::value::CacheValue`, the
// per-cache `*WriteData`, the F1 coordination hash) and the duplicate removed.

/// Placeholder — Port of `CCacheValue` (F0, `cache/value.rs`).
pub struct CacheValue;
/// Placeholder — Port of `CCACHINGLIST<CCacheValue>` (F0 pool container; `CacheSettings.h`).
pub struct CachingValueList;
/// Placeholder — Port of `CCACHINGHASH<cint64,cint64>` (F0 pool container; `CacheSettings.h`).
pub struct CachingDepHash;
/// Placeholder — Port of `CCacheEntryWriteData` (F0).
pub struct CacheEntryWriteData;
/// Placeholder — Port of `CSaturationNodeAssociatedExpansionCacheWriteData` (F5).
pub struct SaturationNodeAssociatedExpansionCacheWriteData;
/// Placeholder — Port of `CComputedConsequencesCacheWriteData` (F6).
pub struct ComputedConsequencesCacheWriteData;
/// Placeholder — Port of `CBackendRepresentativeMemoryCacheWriteData` (F1).
pub struct BackendRepresentativeMemoryCacheWriteData;
/// Placeholder — Port of `CBackendIndividualRetrievalComputationUpdateCoordinationHash` (F1).
pub struct BackendIndividualRetrievalComputationUpdateCoordinationHash;

/// `CCACHINGLIST<CCacheValue>*` → arena id of the pool-allocated value list.
pub type CachingValueListId = Id<CachingValueList>;
/// `CCACHINGHASH<cint64,cint64>*` → arena id of the pool-allocated dep hash.
pub type CachingDepHashId = Id<CachingDepHash>;
/// `CCacheEntryWriteData*` → arena id.
pub type CacheEntryWriteDataId = Id<CacheEntryWriteData>;
/// `CSaturationNodeAssociatedExpansionCacheWriteData*` → arena id.
pub type SaturationNodeAssociatedExpansionCacheWriteDataId =
    Id<SaturationNodeAssociatedExpansionCacheWriteData>;
/// `CComputedConsequencesCacheWriteData*` → arena id.
pub type ComputedConsequencesCacheWriteDataId = Id<ComputedConsequencesCacheWriteData>;
/// `CBackendRepresentativeMemoryCacheWriteData*` → arena id.
pub type BackendRepresentativeMemoryCacheWriteDataId =
    Id<BackendRepresentativeMemoryCacheWriteData>;
/// `CBackendIndividualRetrievalComputationUpdateCoordinationHash*` → arena id.
pub type BackendIndividualRetrievalCoordinationHashId =
    Id<BackendIndividualRetrievalComputationUpdateCoordinationHash>;

// -----------------------------------------------------------------------------

/// The 11 `Cache/Events/CWrite*Event` / coordination-event classes, collapsed to
/// one tagged enum (manifest/07-cache.md F8). One variant per event; field order
/// mirrors each header's member declaration order.
///
/// KONCLUDE-PORT-NOTE[ownership]: every `CXxx*` payload pointer becomes a typed
/// arena `Id`; the by-value `QList<CCacheValue>` payloads become owned `Vec`s
/// (events that own their list vs. events that borrow a pool-allocated one — the
/// distinction is faithful). `CMemoryPool*` and `CCallbackData*` are opaque
/// `Cint64` handles ([memory-pool] / [threading]); see `model/substrate.rs`.
pub enum CacheEvent {
    /// Port of `CWriteUnsatisfiableCacheEntryEvent`.
    /// (`EVENT_WRITE_UNSATISFIABLE_CACHE_ENTRY`)
    WriteUnsatisfiableCacheEntry {
        /// `cacheEntry` — owned `QList<CCacheValue>` by value.
        cache_entry: Vec<CacheValue>,
    },

    /// Port of `CWriteSatisfiableCacheEntryEvent`.
    /// (`EVENT_WRITE_SATISFIABLE_CACHE_ENTRY`)
    WriteSatisfiableCacheEntry {
        /// `cacheItemList` — owned `QList<CCacheValue>` by value.
        cache_item_list: Vec<CacheValue>,
        /// `cacheOutcomeList` — owned `QList<CCacheValue>` by value.
        cache_outcome_list: Vec<CacheValue>,
    },

    /// Port of `CWriteExpandCachedEvent`.
    /// (`EVENT_WRITE_EXPAND_CACHED_ENTRY`)
    WriteExpandCached {
        /// `mPrevSignature`.
        prev_signature: Cint64,
        /// `mNewSignature`.
        new_signature: Cint64,
        /// `mCacheValueList` — `CCACHINGLIST<CCacheValue>*` (pool-allocated).
        cache_value_list: CachingValueListId,
        /// `mDepHash` — `CCACHINGHASH<cint64,cint64>*` (pool-allocated).
        dep_hash: CachingDepHashId,
        /// `mMemoryPools` — `CMemoryPool*` ([memory-pool], opaque handle).
        memory_pools: Cint64,
    },

    /// Port of `CWriteSatisfiableBranchCachedEvent`.
    /// (`EVENT_WRITE_SATISFIABLE_BRANCH_CACHED_ENTRY`)
    WriteSatisfiableBranchCached {
        /// `mSignature`.
        signature: Cint64,
        /// `mCacheValueList` — `CCACHINGLIST<CCacheValue>*`.
        cache_value_list: CachingValueListId,
        /// `mBranchedValueList` — `CCACHINGLIST<CCacheValue>*`.
        branched_value_list: CachingValueListId,
        /// `mMemoryPools` — `CMemoryPool*` ([memory-pool]).
        memory_pools: Cint64,
    },

    /// Port of `CWriteCachedDataEvent`.
    /// (`EVENT_WRITE_CACHED_DATA_ENTRY`)
    WriteCachedData {
        /// `mWriteData` — `CCacheEntryWriteData*`.
        write_data: CacheEntryWriteDataId,
        /// `mMemoryPools` — `CMemoryPool*` ([memory-pool]).
        memory_pools: Cint64,
    },

    /// Port of `CWriteSaturationCacheDataEvent`.
    /// (`EVENT_WRITE_SATURATION_CACHE_DATA_ENTRY`)
    WriteSaturationCacheData {
        /// `mWriteData` — `CSaturationNodeAssociatedExpansionCacheWriteData*`.
        write_data: SaturationNodeAssociatedExpansionCacheWriteDataId,
        /// `mMemoryPools` — `CMemoryPool*` ([memory-pool]).
        memory_pools: Cint64,
    },

    /// Port of `CWriteComputedConcequencesCacheEntryEvent`.
    /// (`EVENT_WRITE_COMPUTED_CONSEQUENCES_CACHE_DATA_ENTRY`)
    WriteComputedConcequencesCacheEntry {
        /// `mWriteData` — `CComputedConsequencesCacheWriteData*`.
        write_data: ComputedConsequencesCacheWriteDataId,
        /// `mMemoryPools` — `CMemoryPool*` ([memory-pool]).
        memory_pools: Cint64,
    },

    /// Port of `CWriteBackendAssociationCachedEvent`.
    /// (`EVENT_WRITE_BACKEND_ASSOCIATION_ENTRY`)
    WriteBackendAssociationCached {
        /// `mWriteData` — `CBackendRepresentativeMemoryCacheWriteData*`.
        write_data: BackendRepresentativeMemoryCacheWriteDataId,
        /// `mMemoryPools` — `CMemoryPool*` ([memory-pool]).
        memory_pools: Cint64,
    },

    /// Port of `CRetrieveIncompletelyAssociationCachedEvent`.
    /// (`EVENT_RETRIEVE_INCOMPLETELY_ASSOCIATION_CACHED`)
    RetrieveIncompletelyAssociationCached {
        /// `mOntologyIdentifier`.
        ontology_identifier: Cint64,
        /// `mCallback` — `CCallbackData*` ([threading], opaque continuation handle).
        callback: Cint64,
        /// `mLastRetrievalHash` — `CBackendIndividualRetrievalComputationUpdateCoordinationHash*`.
        last_retrieval_hash: BackendIndividualRetrievalCoordinationHashId,
        /// `mNewRetrievalHash` — same type.
        new_retrieval_hash: BackendIndividualRetrievalCoordinationHashId,
        /// `mLimit`.
        limit: Cint64,
        /// `mAllIndividualsAdded`.
        all_individuals_added: bool,
        /// `mRefillRetrievalCoordHash`.
        refill_retrieval_coord_hash: bool,
    },

    /// Port of `CInitializeIndividualAssociationsCacheEvent`.
    /// (`EVENT_INITIALIZE_INDIVIDUALS_ASSOCIATIONS_CACHE`)
    InitializeIndividualAssociationsCache {
        /// `mOntologyIdentifier`.
        ontology_identifier: Cint64,
        /// `mIndividualCount`.
        individual_count: Cint64,
    },

    /// Port of `CReportMaximumHandledRecomputationIdsEvent`.
    /// (`EVENT_REPORT_MAXIMUM_HANDLED_RECOMPUTATION_ID`)
    ReportMaximumHandledRecomputationIds {
        /// `mOntologyIdentifier`.
        ontology_identifier: Cint64,
        /// `mMaximumHandledRecomputationId`.
        maximum_handled_recomputation_id: Cint64,
    },
}

impl CacheEvent {
    // ---- per-event constructors (Port of each `CWrite*Event(...)` ctor) -------
    // KONCLUDE-PORT-NOTE[threading]: each C++ ctor passes its `EVENT*` code up to
    // `CCustomEvent(type)` and defaults the inherited `void* obj` to 0; the type is
    // now the enum discriminant (recovered via `event_type()`) and `obj` is folded
    // out (file header [threading] note), so the ctors just build the variant. The
    // C++ ctor PARAMETER order is preserved even where it differs from the variant's
    // field order (e.g. `RetrieveIncompletelyAssociationCached`).

    /// Port of `CWriteUnsatisfiableCacheEntryEvent::CWriteUnsatisfiableCacheEntryEvent`.
    pub fn write_unsatisfiable_cache_entry(cache_entry: Vec<CacheValue>) -> Self {
        CacheEvent::WriteUnsatisfiableCacheEntry { cache_entry }
    }

    /// Port of `CWriteSatisfiableCacheEntryEvent::CWriteSatisfiableCacheEntryEvent`.
    pub fn write_satisfiable_cache_entry(
        item_list: Vec<CacheValue>,
        out_list: Vec<CacheValue>,
    ) -> Self {
        CacheEvent::WriteSatisfiableCacheEntry {
            cache_item_list: item_list,
            cache_outcome_list: out_list,
        }
    }

    /// Port of `CWriteExpandCachedEvent::CWriteExpandCachedEvent`.
    pub fn write_expand_cached(
        prev_signature: Cint64,
        new_signature: Cint64,
        cache_value_list: CachingValueListId,
        dep_hash: CachingDepHashId,
        memory_pools: Cint64,
    ) -> Self {
        CacheEvent::WriteExpandCached {
            prev_signature,
            new_signature,
            cache_value_list,
            dep_hash,
            memory_pools,
        }
    }

    /// Port of `CWriteSatisfiableBranchCachedEvent::CWriteSatisfiableBranchCachedEvent`.
    pub fn write_satisfiable_branch_cached(
        signature: Cint64,
        cache_value_list: CachingValueListId,
        branched_list: CachingValueListId,
        memory_pools: Cint64,
    ) -> Self {
        CacheEvent::WriteSatisfiableBranchCached {
            signature,
            cache_value_list,
            branched_value_list: branched_list,
            memory_pools,
        }
    }

    /// Port of `CWriteCachedDataEvent::CWriteCachedDataEvent`.
    pub fn write_cached_data(write_data: CacheEntryWriteDataId, memory_pools: Cint64) -> Self {
        CacheEvent::WriteCachedData { write_data, memory_pools }
    }

    /// Port of `CWriteSaturationCacheDataEvent::CWriteSaturationCacheDataEvent`.
    pub fn write_saturation_cache_data(
        write_data: SaturationNodeAssociatedExpansionCacheWriteDataId,
        memory_pools: Cint64,
    ) -> Self {
        CacheEvent::WriteSaturationCacheData { write_data, memory_pools }
    }

    /// Port of `CWriteComputedConcequencesCacheEntryEvent::CWriteComputedConcequencesCacheEntryEvent`.
    pub fn write_computed_concequences_cache_entry(
        write_data: ComputedConsequencesCacheWriteDataId,
        memory_pools: Cint64,
    ) -> Self {
        CacheEvent::WriteComputedConcequencesCacheEntry { write_data, memory_pools }
    }

    /// Port of `CWriteBackendAssociationCachedEvent::CWriteBackendAssociationCachedEvent`.
    pub fn write_backend_association_cached(
        write_data: BackendRepresentativeMemoryCacheWriteDataId,
        memory_pools: Cint64,
    ) -> Self {
        CacheEvent::WriteBackendAssociationCached { write_data, memory_pools }
    }

    /// Port of `CRetrieveIncompletelyAssociationCachedEvent::CRetrieveIncompletelyAssociationCachedEvent`.
    /// KONCLUDE-PORT-NOTE[threading]: `callbackData` is the `CCallbackData*`
    /// continuation handle, opaque `Cint64` here.
    #[allow(clippy::too_many_arguments)]
    pub fn retrieve_incompletely_association_cached(
        callback_data: Cint64,
        ontology_identifier: Cint64,
        last_retrieval_hash: BackendIndividualRetrievalCoordinationHashId,
        new_retrieval_hash: BackendIndividualRetrievalCoordinationHashId,
        all_individuals_added: bool,
        refill_retrieval_coord_hash: bool,
        limit: Cint64,
    ) -> Self {
        CacheEvent::RetrieveIncompletelyAssociationCached {
            ontology_identifier,
            callback: callback_data,
            last_retrieval_hash,
            new_retrieval_hash,
            limit,
            all_individuals_added,
            refill_retrieval_coord_hash,
        }
    }

    /// Port of `CInitializeIndividualAssociationsCacheEvent::CInitializeIndividualAssociationsCacheEvent`.
    pub fn initialize_individual_associations_cache(
        ontology_identifier: Cint64,
        individual_count: Cint64,
    ) -> Self {
        CacheEvent::InitializeIndividualAssociationsCache {
            ontology_identifier,
            individual_count,
        }
    }

    /// Port of `CReportMaximumHandledRecomputationIdsEvent::CReportMaximumHandledRecomputationIdsEvent`.
    pub fn report_maximum_handled_recomputation_ids(
        ontology_identifier: Cint64,
        maximum_handled_recomputation_id: Cint64,
    ) -> Self {
        CacheEvent::ReportMaximumHandledRecomputationIds {
            ontology_identifier,
            maximum_handled_recomputation_id,
        }
    }

    // ---- EVENTTYPE accessor --------------------------------------------------

    /// Port of the per-class `static const QEvent::Type EVENTTYPE` / the
    /// `CCustomEvent::type()` discriminant. Returns the `EVENT_*` code of the
    /// variant. KONCLUDE-PORT-NOTE[threading]: in C++ the dispatcher reads
    /// `event->type()` to pick the handler; here the writer-thread drain matches
    /// the enum variant, and this getter recovers the original code if needed.
    pub fn event_type(&self) -> Cint64 {
        match self {
            CacheEvent::WriteUnsatisfiableCacheEntry { .. } => {
                EVENT_WRITE_UNSATISFIABLE_CACHE_ENTRY
            }
            CacheEvent::WriteSatisfiableCacheEntry { .. } => EVENT_WRITE_SATISFIABLE_CACHE_ENTRY,
            CacheEvent::WriteExpandCached { .. } => EVENT_WRITE_EXPAND_CACHED_ENTRY,
            CacheEvent::WriteSatisfiableBranchCached { .. } => {
                EVENT_WRITE_SATISFIABLE_BRANCH_CACHED_ENTRY
            }
            CacheEvent::WriteCachedData { .. } => EVENT_WRITE_CACHED_DATA_ENTRY,
            CacheEvent::WriteSaturationCacheData { .. } => EVENT_WRITE_SATURATION_CACHE_DATA_ENTRY,
            CacheEvent::WriteComputedConcequencesCacheEntry { .. } => {
                EVENT_WRITE_COMPUTED_CONSEQUENCES_CACHE_DATA_ENTRY
            }
            CacheEvent::WriteBackendAssociationCached { .. } => EVENT_WRITE_BACKEND_ASSOCIATION_ENTRY,
            CacheEvent::RetrieveIncompletelyAssociationCached { .. } => {
                EVENT_RETRIEVE_INCOMPLETELY_ASSOCIATION_CACHED
            }
            CacheEvent::InitializeIndividualAssociationsCache { .. } => {
                EVENT_INITIALIZE_INDIVIDUALS_ASSOCIATIONS_CACHE
            }
            CacheEvent::ReportMaximumHandledRecomputationIds { .. } => {
                EVENT_REPORT_MAXIMUM_HANDLED_RECOMPUTATION_ID
            }
        }
    }

    // ---- per-event getters / setters -----------------------------------------
    // KONCLUDE-PORT-NOTE[api]: each C++ getter is declared on the ONE concrete
    // event class, so a caller that holds a `CWriteExpandCachedEvent*` knows the
    // getter applies. Collapsed into one enum, a getter is meaningful only for its
    // variant; ported as `Option<…>` (`None` == "wrong variant", unreachable in a
    // faithful caller that has already matched the variant). Where the SAME C++
    // getter name+return-type appears on several classes (`getMemoryPools`,
    // `getCacheValueList`) it is ported as ONE method matching all those variants;
    // where the name collides but the return TYPE differs (`getWriteData` on the 4
    // `*WriteData` events) Rust cannot overload, so each is given a per-family name.

    /// Port of `CWriteUnsatisfiableCacheEntryEvent::getCacheEntryList`.
    pub fn get_cache_entry_list(&self) -> Option<&Vec<CacheValue>> {
        match self {
            CacheEvent::WriteUnsatisfiableCacheEntry { cache_entry } => Some(cache_entry),
            _ => None,
        }
    }

    /// Port of `CWriteUnsatisfiableCacheEntryEvent::setCacheEntryList`.
    pub fn set_cache_entry_list(&mut self, list: Vec<CacheValue>) {
        if let CacheEvent::WriteUnsatisfiableCacheEntry { cache_entry } = self {
            *cache_entry = list;
        }
    }

    /// Port of `CWriteSatisfiableCacheEntryEvent::getCacheItemList`.
    pub fn get_cache_item_list(&self) -> Option<&Vec<CacheValue>> {
        match self {
            CacheEvent::WriteSatisfiableCacheEntry { cache_item_list, .. } => Some(cache_item_list),
            _ => None,
        }
    }

    /// Port of `CWriteSatisfiableCacheEntryEvent::setCacheItemList`.
    pub fn set_cache_item_list(&mut self, list: Vec<CacheValue>) {
        if let CacheEvent::WriteSatisfiableCacheEntry { cache_item_list, .. } = self {
            *cache_item_list = list;
        }
    }

    /// Port of `CWriteSatisfiableCacheEntryEvent::getCacheOutcomeList`.
    pub fn get_cache_outcome_list(&self) -> Option<&Vec<CacheValue>> {
        match self {
            CacheEvent::WriteSatisfiableCacheEntry { cache_outcome_list, .. } => {
                Some(cache_outcome_list)
            }
            _ => None,
        }
    }

    /// Port of `CWriteSatisfiableCacheEntryEvent::setCacheOutcomeList`.
    pub fn set_cache_outcome_list(&mut self, list: Vec<CacheValue>) {
        if let CacheEvent::WriteSatisfiableCacheEntry { cache_outcome_list, .. } = self {
            *cache_outcome_list = list;
        }
    }

    /// Port of `CWriteExpandCachedEvent::getPrevSignature`.
    pub fn get_prev_signature(&self) -> Option<Cint64> {
        match self {
            CacheEvent::WriteExpandCached { prev_signature, .. } => Some(*prev_signature),
            _ => None,
        }
    }

    /// Port of `CWriteExpandCachedEvent::getNewSignature`.
    pub fn get_new_signature(&self) -> Option<Cint64> {
        match self {
            CacheEvent::WriteExpandCached { new_signature, .. } => Some(*new_signature),
            _ => None,
        }
    }

    /// Port of `CWriteExpandCachedEvent::getDepHash`.
    pub fn get_dep_hash(&self) -> Option<CachingDepHashId> {
        match self {
            CacheEvent::WriteExpandCached { dep_hash, .. } => Some(*dep_hash),
            _ => None,
        }
    }

    /// Port of `CWriteSatisfiableBranchCachedEvent::getSignature`.
    pub fn get_signature(&self) -> Option<Cint64> {
        match self {
            CacheEvent::WriteSatisfiableBranchCached { signature, .. } => Some(*signature),
            _ => None,
        }
    }

    /// Port of `CWriteSatisfiableBranchCachedEvent::getBranchedValueList`.
    pub fn get_branched_value_list(&self) -> Option<CachingValueListId> {
        match self {
            CacheEvent::WriteSatisfiableBranchCached { branched_value_list, .. } => {
                Some(*branched_value_list)
            }
            _ => None,
        }
    }

    /// Port of `CWriteExpandCachedEvent::getCacheValueList` /
    /// `CWriteSatisfiableBranchCachedEvent::getCacheValueList` (same name+type on
    /// both classes → one method).
    pub fn get_cache_value_list(&self) -> Option<CachingValueListId> {
        match self {
            CacheEvent::WriteExpandCached { cache_value_list, .. }
            | CacheEvent::WriteSatisfiableBranchCached { cache_value_list, .. } => {
                Some(*cache_value_list)
            }
            _ => None,
        }
    }

    /// Port of `CWriteCachedDataEvent::getWriteData`.
    /// (per-family name; see the [api] note above on the `getWriteData` overloads.)
    pub fn get_cache_entry_write_data(&self) -> Option<CacheEntryWriteDataId> {
        match self {
            CacheEvent::WriteCachedData { write_data, .. } => Some(*write_data),
            _ => None,
        }
    }

    /// Port of `CWriteSaturationCacheDataEvent::getWriteData`.
    pub fn get_saturation_cache_write_data(
        &self,
    ) -> Option<SaturationNodeAssociatedExpansionCacheWriteDataId> {
        match self {
            CacheEvent::WriteSaturationCacheData { write_data, .. } => Some(*write_data),
            _ => None,
        }
    }

    /// Port of `CWriteComputedConcequencesCacheEntryEvent::getWriteData`.
    pub fn get_computed_consequences_write_data(
        &self,
    ) -> Option<ComputedConsequencesCacheWriteDataId> {
        match self {
            CacheEvent::WriteComputedConcequencesCacheEntry { write_data, .. } => Some(*write_data),
            _ => None,
        }
    }

    /// Port of `CWriteBackendAssociationCachedEvent::getWriteData`.
    pub fn get_backend_association_write_data(
        &self,
    ) -> Option<BackendRepresentativeMemoryCacheWriteDataId> {
        match self {
            CacheEvent::WriteBackendAssociationCached { write_data, .. } => Some(*write_data),
            _ => None,
        }
    }

    /// Port of `getMemoryPools` on every `CMemoryPool*`-carrying event (same
    /// name+type across all 6 → one method). KONCLUDE-PORT-NOTE[memory-pool]:
    /// `CMemoryPool*` is an opaque `Cint64` handle.
    pub fn get_memory_pools(&self) -> Option<Cint64> {
        match self {
            CacheEvent::WriteExpandCached { memory_pools, .. }
            | CacheEvent::WriteSatisfiableBranchCached { memory_pools, .. }
            | CacheEvent::WriteCachedData { memory_pools, .. }
            | CacheEvent::WriteSaturationCacheData { memory_pools, .. }
            | CacheEvent::WriteComputedConcequencesCacheEntry { memory_pools, .. }
            | CacheEvent::WriteBackendAssociationCached { memory_pools, .. } => Some(*memory_pools),
            _ => None,
        }
    }

    /// Port of `CRetrieveIncompletelyAssociationCachedEvent::getCallback`.
    /// KONCLUDE-PORT-NOTE[threading]: `CCallbackData*` opaque `Cint64`.
    pub fn get_callback(&self) -> Option<Cint64> {
        match self {
            CacheEvent::RetrieveIncompletelyAssociationCached { callback, .. } => Some(*callback),
            _ => None,
        }
    }

    /// Port of `CRetrieveIncompletelyAssociationCachedEvent::getLastIndividualsRetrievalCoordinationHash`.
    pub fn get_last_individuals_retrieval_coordination_hash(
        &self,
    ) -> Option<BackendIndividualRetrievalCoordinationHashId> {
        match self {
            CacheEvent::RetrieveIncompletelyAssociationCached { last_retrieval_hash, .. } => {
                Some(*last_retrieval_hash)
            }
            _ => None,
        }
    }

    /// Port of `CRetrieveIncompletelyAssociationCachedEvent::getNewIndividualsRetrievalCoordinationHash`.
    pub fn get_new_individuals_retrieval_coordination_hash(
        &self,
    ) -> Option<BackendIndividualRetrievalCoordinationHashId> {
        match self {
            CacheEvent::RetrieveIncompletelyAssociationCached { new_retrieval_hash, .. } => {
                Some(*new_retrieval_hash)
            }
            _ => None,
        }
    }

    /// Port of `CRetrieveIncompletelyAssociationCachedEvent::getRetrievalLimit`.
    pub fn get_retrieval_limit(&self) -> Option<Cint64> {
        match self {
            CacheEvent::RetrieveIncompletelyAssociationCached { limit, .. } => Some(*limit),
            _ => None,
        }
    }

    /// Port of `CRetrieveIncompletelyAssociationCachedEvent::hasAllIndividualsAdded`.
    pub fn has_all_individuals_added(&self) -> Option<bool> {
        match self {
            CacheEvent::RetrieveIncompletelyAssociationCached { all_individuals_added, .. } => {
                Some(*all_individuals_added)
            }
            _ => None,
        }
    }

    /// Port of `CRetrieveIncompletelyAssociationCachedEvent::hasRefillRetrievalCoordHashOrdered`.
    pub fn has_refill_retrieval_coord_hash_ordered(&self) -> Option<bool> {
        match self {
            CacheEvent::RetrieveIncompletelyAssociationCached {
                refill_retrieval_coord_hash,
                ..
            } => Some(*refill_retrieval_coord_hash),
            _ => None,
        }
    }

    /// Port of `CInitializeIndividualAssociationsCacheEvent::getIndividualCount`.
    pub fn get_individual_count(&self) -> Option<Cint64> {
        match self {
            CacheEvent::InitializeIndividualAssociationsCache { individual_count, .. } => {
                Some(*individual_count)
            }
            _ => None,
        }
    }

    /// Port of `CReportMaximumHandledRecomputationIdsEvent::getMaximumHandledRecomputationId`.
    pub fn get_maximum_handled_recomputation_id(&self) -> Option<Cint64> {
        match self {
            CacheEvent::ReportMaximumHandledRecomputationIds {
                maximum_handled_recomputation_id,
                ..
            } => Some(*maximum_handled_recomputation_id),
            _ => None,
        }
    }

    /// Port of `getOntologyIdentifier` — shared, by the same name+type, across
    /// `CRetrieveIncompletelyAssociationCachedEvent`,
    /// `CInitializeIndividualAssociationsCacheEvent`, and
    /// `CReportMaximumHandledRecomputationIdsEvent` → one method.
    pub fn get_ontology_identifier(&self) -> Option<Cint64> {
        match self {
            CacheEvent::RetrieveIncompletelyAssociationCached { ontology_identifier, .. }
            | CacheEvent::InitializeIndividualAssociationsCache { ontology_identifier, .. }
            | CacheEvent::ReportMaximumHandledRecomputationIds { ontology_identifier, .. } => {
                Some(*ontology_identifier)
            }
            _ => None,
        }
    }
}
