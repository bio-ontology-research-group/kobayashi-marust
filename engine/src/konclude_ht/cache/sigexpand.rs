//! `cache::sigexpand` — F2, the **signature-satisfiable expander cache**
//! (Konclude `Source/Reasoner/Kernel/Cache/CSignatureSatisfiableExpanderCache*`,
//! `CExpander*Linker`, plus the shared `CSatisfiableCache{,Reader,Writer}` bases).
//!
//! This cache stores satisfiable label *signatures* so the completion expander
//! can skip re-saturating a label set already known satisfiable, and tracks the
//! expander value-linker / branched-linker chains that justify each cached
//! signature. The algorithm reaches it only through the Algorithm-layer
//! `CSatisfiableExpanderCacheHandler` (stubbed in `completion::stubs`).
//!
//! W6-CACHE struct-skeleton unit (manifest/07-cache.md §F2 + the CORE-vs-DEEP
//! split): this file defines the struct/enum DATA MODEL only — every method body
//! is deferred to the W6-CACHE method-batch wave. `mod.rs` is intentionally NOT
//! wired and this file is not built yet.
//!
//! ## Port conventions applied (see `model/substrate.rs` + `PORT.md`)
//! - `CXxx*` pointer to a same-family pooled record (Entry / SlotItem /
//!   RedirectionItem / Reader / the two expander linkers / the write-data) →
//!   a typed arena `Id<T>` (`Id::NONE` == `nullptr`). [ownership]
//! - Back-pointer to the long-lived facade `CSignatureSatisfiableExpanderCache`
//!   (a `CThread`, not an arena record) → opaque `Cint64`. [ownership]
//! - `CCacheValue` (F0, `cache/value.rs`) is a CROSS-FAMILY value
//!   → the real shared `value::CacheValue` triple. [api]
//! - `CCACHINGHASH/LIST/SET<…>` = `CQtManagedRestrictedModification{Hash,List,Set}`
//!   pool-managed concurrent-modification containers → opaque `Cint64` (a
//!   pointer/handle into the per-cache pool); realized in F0 `cache/value.rs`
//!   later. [memory-pool]
//! - `QMutex` / `QAtomicInt` / `QAtomicPointer` / `CThread` base → opaque `Cint64`
//!   / a noted `Id`. [threading]
//! - `CMemoryPool*` / `CMemoryPoolAllocationManager*` / `CMemoryPoolProvider*` /
//!   `CConfiguration*` / `CCacheStatistics` (F0) → opaque `Cint64`. [memory-pool]/[api]
//! - The `*EntryWriteData` family (base + Expand + SatisfiableBranch) is the
//!   manifest-flagged record-family → ONE tagged enum
//!   (`SigExpanderEntryWriteDataKind`) inside a wrapper carrying the shared
//!   `CCacheEntryWriteData` base header (mirrors the W2 `DepKind` collapse).

#![allow(dead_code)]

use super::super::model::substrate::{Cint64, Id, INVALID};
use super::context::CacheContext;
use super::events::{
    CacheEvent, EVENT_WRITE_CACHED_DATA_ENTRY, EVENT_WRITE_EXPAND_CACHED_ENTRY,
    EVENT_WRITE_SATISFIABLE_BRANCH_CACHED_ENTRY,
};
use super::value::{CacheValue, CacheWriteDataType};
use std::collections::{HashMap, HashSet};

const DEFAULT_SIG_EXPANDER_INITIAL_MEMORY_LEVEL_FOR_REF_COUNT_INCREASE: Cint64 = 200 * 1024 * 1024;
const DEFAULT_SIG_EXPANDER_NEXT_MEMORY_LEVEL_INCREASE_FOR_REF_COUNT: Cint64 = 100 * 1024 * 1024;
const DEFAULT_SIG_EXPANDER_REQUIRED_SIGNATURE_REFERENCE_COUNT_INCREASE: Cint64 = 1;

// --- cross-family shared value (F0 `cache/value.rs`) ---
/// Port of `CCacheValue` (F0, `cache/value.rs`).
///
/// A by-value `CCACHINGLIST<CCacheValue>` → `Vec<CCacheValue>`; a *pointer* to a
/// pool-managed `CCACHING*` container becomes the typed list/set arena id below.
pub type CCacheValue = CacheValue;

// --- F2 same-family arena ids (would live in `cache/mod.rs` once wired) ---
/// `CSignatureSatisfiableExpanderCacheEntry*`        → `SigExpanderCacheEntryId`.
pub type SigExpanderCacheEntryId = Id<SignatureSatisfiableExpanderCacheEntry>;
/// `CSignatureSatisfiableExpanderCacheSlotItem*`     → `SigExpanderSlotItemId`.
pub type SigExpanderSlotItemId = Id<SignatureSatisfiableExpanderCacheSlotItem>;
/// `CSignatureSatisfiableExpanderCacheRedirectionItem*` → `SigExpanderRedirectionItemId`.
pub type SigExpanderRedirectionItemId = Id<SignatureSatisfiableExpanderCacheRedirectionItem>;
/// `CSignatureSatisfiableExpanderCacheReader*`       → `SigExpanderCacheReaderId`.
pub type SigExpanderCacheReaderId = Id<SignatureSatisfiableExpanderCacheReader>;
/// `CExpanderCacheValueLinker*`                      → `ExpanderCacheValueLinkerId`.
pub type ExpanderCacheValueLinkerId = Id<ExpanderCacheValueLinker>;
/// `CExpanderBranchedLinker*`                        → `ExpanderBranchedLinkerId`.
pub type ExpanderBranchedLinkerId = Id<ExpanderBranchedLinker>;
/// `CCACHINGLIST<CCacheValue>*`                      → `SigExpanderCacheValueListId`.
pub type SigExpanderCacheValueListId = Id<SignatureSatisfiableExpanderCacheValueList>;
/// `CCACHINGSET<CCacheValue>*`                       → `SigExpanderCacheValueSetId`.
pub type SigExpanderCacheValueSetId = Id<SignatureSatisfiableExpanderCacheValueSet>;
/// `CCACHINGHASH<cint64,cint64>*`                    → `SigExpanderDepHashId`.
pub type SigExpanderDepHashId = Id<SignatureSatisfiableExpanderDepHash>;
/// `CSignatureSatisfiableExpanderCacheEntryWriteData*` (the write-data enum) →
/// `SigExpanderEntryWriteDataId`.
pub type SigExpanderEntryWriteDataId = Id<SignatureSatisfiableExpanderCacheEntryWriteData>;
/// `CCACHINGHASH<CSignatureSatisfiableExpanderCacheHasher,...RedirectionItem*>`.
pub type SigExpanderHasherItemHash = Vec<(
    SignatureSatisfiableExpanderCacheHasher,
    SigExpanderRedirectionItemId,
)>;
/// `CCACHINGHASH<cint64,CExpanderCacheValueLinker*>`.
pub type SigExpanderTagHash = HashMap<Cint64, ExpanderCacheValueLinkerId>;

// ===========================================================================
// Shared satisfiable-cache bases (`CSatisfiableCache{,Reader,Writer}`).
// ===========================================================================

/// Port of `CSatisfiableCache` (base `CCache`).
///
/// Marker base shared by F2 (signature-satisfiable expander) and F5 (saturation)
/// caches; carries no data of its own.
#[derive(Debug, Default, Clone)]
pub struct SatisfiableCache;

impl SatisfiableCache {
    /// Port of `CSatisfiableCache::CSatisfiableCache`.
    pub fn new() -> Self {
        Self::default()
    }
    // No further methods: `CSatisfiableCache` is an empty marker base (virtual dtor only).
}

/// Port of `CSatisfiableCacheReader`.
///
/// Abstract reader base (pure-virtual `isSatisfiable` / `getSatisfiableOutcome`);
/// no data members. Ported as a marker the concrete `*Reader` conceptually
/// implements.
#[derive(Debug, Default, Clone)]
pub struct SatisfiableCacheReader;

impl SatisfiableCacheReader {
    /// Port of `CSatisfiableCacheReader::CSatisfiableCacheReader`.
    pub fn new() -> Self {
        Self::default()
    }
    // No concrete bodies: `isSatisfiable` / `getSatisfiableOutcome` are pure-virtual
    // (= 0) in C++; the concrete `SignatureSatisfiableExpanderCacheReader` provides them.
}

/// Port of `CSatisfiableCacheWriter`.
///
/// Abstract writer base (pure-virtual `setSatisfiable`); no data members.
#[derive(Debug, Default, Clone)]
pub struct SatisfiableCacheWriter;

impl SatisfiableCacheWriter {
    /// Port of `CSatisfiableCacheWriter::CSatisfiableCacheWriter`.
    pub fn new() -> Self {
        Self::default()
    }
    // No concrete bodies: `setSatisfiable` is pure-virtual (= 0) in C++.
}

// ===========================================================================
// Context (`CSignatureSatisfiableExpanderCacheContext`).
// ===========================================================================

/// Port of `CSignatureSatisfiableExpanderCacheContext` (base `CContext`).
///
/// The per-cache memory-pool scratch context. Held BY VALUE in the facade.
pub struct SignatureSatisfiableExpanderCacheContext {
    // KONCLUDE-PORT-NOTE[memory-pool]: `CMemoryPoolAllocationManager* mMemMan`.
    /// `CSignatureSatisfiableExpanderCacheContext::mMemMan`.
    pub mem_man: Cint64,
    // KONCLUDE-PORT-NOTE[memory-pool]: `CNewAllocationMemoryPoolProvider* mMemoryPoolProvider`.
    /// `CSignatureSatisfiableExpanderCacheContext::mMemoryPoolProvider`.
    pub memory_pool_provider: Cint64,
    /// `CSignatureSatisfiableExpanderCacheContext::mAddRelMemory`.
    pub add_rel_memory: Cint64,
}

impl Default for SignatureSatisfiableExpanderCacheContext {
    fn default() -> Self {
        SignatureSatisfiableExpanderCacheContext {
            mem_man: 0,
            memory_pool_provider: 0,
            add_rel_memory: 0,
        }
    }
}

impl SignatureSatisfiableExpanderCacheContext {
    /// Port of `CSignatureSatisfiableExpanderCacheContext::CSignatureSatisfiableExpanderCacheContext`.
    /// KONCLUDE-PORT-NOTE[memory-pool]: the C++ ctor news a `CNewAllocationMemoryPoolProvider`
    /// + `CLimitedReserveMemoryPoolAllocationManager`; both stay opaque `Cint64` handles here.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `getMemoryAllocationManager`.
    pub fn get_memory_allocation_manager(&self) -> Cint64 {
        self.mem_man
    }

    /// Port of `getMemoryPoolAllocationManager`.
    pub fn get_memory_pool_allocation_manager(&self) -> Cint64 {
        self.mem_man
    }

    /// Port of `getMemoryPoolProvider`.
    pub fn get_memory_pool_provider(&self) -> Cint64 {
        self.memory_pool_provider
    }

    /// Port of `getMemoryConsumption`.
    pub fn get_memory_consumption(&self) -> Cint64 {
        // KONCLUDE-PORT-NOTE[memory-pool]: C++ returns
        // `mAddRelMemory + mMemoryPoolProvider->getAllocatedReleaseDifferencePoolSize()`.
        // W6-DEFER[memory-pool]: the pool-provider difference query is on an opaque handle.
        self.add_rel_memory /* + mMemoryPoolProvider->getAllocatedReleaseDifferencePoolSize() */
    }

    /// Port of `releaseTemporaryMemoryPools`.
    pub fn release_temporary_memory_pools(&mut self, memory_pools: Cint64) -> &mut Self {
        // KONCLUDE-PORT-NOTE[memory-pool]: walk the CMemoryPool chain summing each block size
        // into mAddRelMemory, then hand the chain to the pool manager for release.
        let mut memory_pool_it = memory_pools;
        while memory_pool_it != 0 {
            // W6-DEFER[memory-pool]: mAddRelMemory += memoryPoolIt->getMemoryBlockSize();
            // W6-DEFER[memory-pool]: memoryPoolIt = memoryPoolIt->getNext();
            memory_pool_it = 0;
        }
        // W6-DEFER[memory-pool]: mMemMan->releaseTemporaryMemoryPools(memoryPools);
        let _ = memory_pools;
        self
    }
}

// ===========================================================================
// Expander value chains (`CExpanderCacheValueLinker`, `CExpanderBranchedLinker`).
// ===========================================================================

/// Port of `CExpanderCacheValueLinker` (base `CLinkerBase`).
///
/// A cached single cache value with its expander-dependency list; intrusively
/// chained.
pub struct ExpanderCacheValueLinker {
    // KONCLUDE-PORT-NOTE[ownership]: `CLinkerBase` intrusive self-chain → `next`.
    /// `CLinkerBase` next link (`getNext`/`setNext`).
    pub next: ExpanderCacheValueLinkerId,
    // KONCLUDE-PORT-NOTE[ownership]: back-pointer to the owning cache's context;
    // the port threads `&mut ctx` instead of storing it.
    /// `CExpanderCacheValueLinker::mContext`.
    pub context: Cint64,
    /// `CExpanderCacheValueLinker::mCacheValue` (`CCacheValue`, F0).
    pub cache_value: CCacheValue,
    // KONCLUDE-PORT-NOTE[ownership]: `CCACHINGLIST<CExpanderCacheValueLinker*> mDepList`
    // (owned by-value caching list) → owned `Vec` of same-family ids.
    /// `CExpanderCacheValueLinker::mDepList`.
    pub dep_list: Vec<ExpanderCacheValueLinkerId>,
}

impl Default for ExpanderCacheValueLinker {
    fn default() -> Self {
        ExpanderCacheValueLinker {
            next: ExpanderCacheValueLinkerId::NONE,
            context: 0,
            cache_value: CacheValue::new(),
            dep_list: Vec::new(),
        }
    }
}

impl ExpanderCacheValueLinker {
    /// Port of `CExpanderCacheValueLinker::CExpanderCacheValueLinker`.
    pub fn new() -> Self {
        Self::default()
    }

    /// `CLinkerBase::getNext`.
    pub fn get_next(&self) -> ExpanderCacheValueLinkerId {
        self.next
    }

    /// `CLinkerBase::setNext`.
    pub fn set_next(&mut self, next: ExpanderCacheValueLinkerId) -> &mut Self {
        self.next = next;
        self
    }

    /// `CLinkerBase::hasNext`.
    pub fn has_next(&self) -> bool {
        self.next.is_some()
    }

    /// Port of `addExpanderDependency`.
    pub fn add_expander_dependency(
        &mut self,
        dep_exp_cache_value: ExpanderCacheValueLinkerId,
    ) -> &mut Self {
        // `mDepList.append(...)` on a CCACHINGLIST (QList-like) = push to the back.
        self.dep_list.push(dep_exp_cache_value);
        self
    }

    /// Port of `getExpanderDependencyList`.
    pub fn get_expander_dependency_list(&self) -> &Vec<ExpanderCacheValueLinkerId> {
        &self.dep_list
    }

    /// Port of `getCacheValue` (returns `&mCacheValue`).
    pub fn get_cache_value(&self) -> CCacheValue {
        self.cache_value
    }

    /// Port of `setCacheValue`.
    pub fn set_cache_value(&mut self, cache_value: CCacheValue) -> &mut Self {
        self.cache_value = cache_value;
        self
    }
}

/// Port of `CExpanderBranchedLinker` (base `CLinkerBase`).
///
/// A branched (non-deterministic) cache-value group; intrusively chained.
pub struct ExpanderBranchedLinker {
    // KONCLUDE-PORT-NOTE[ownership]: `CLinkerBase` intrusive self-chain → `next`.
    /// `CLinkerBase` next link.
    pub next: ExpanderBranchedLinkerId,
    // KONCLUDE-PORT-NOTE[ownership]: back-pointer to the owning cache's context.
    /// `CExpanderBranchedLinker::mContext`.
    pub context: Cint64,
    // KONCLUDE-PORT-NOTE[ownership]: `CCACHINGLIST<CCacheValue> mNonDetCacheValues`
    // (owned by-value caching list of F0 cache values) → owned `Vec<CCacheValue>`.
    /// `CExpanderBranchedLinker::mNonDetCacheValues`.
    pub non_det_cache_values: Vec<CCacheValue>,
    /// `CExpanderBranchedLinker::mValuesCount`.
    pub values_count: Cint64,
}

impl Default for ExpanderBranchedLinker {
    fn default() -> Self {
        ExpanderBranchedLinker {
            next: ExpanderBranchedLinkerId::NONE,
            context: 0,
            non_det_cache_values: Vec::new(),
            values_count: 0,
        }
    }
}

impl ExpanderBranchedLinker {
    /// Port of `CExpanderBranchedLinker::CExpanderBranchedLinker`.
    pub fn new() -> Self {
        Self::default()
    }

    /// `CLinkerBase::getNext`.
    pub fn get_next(&self) -> ExpanderBranchedLinkerId {
        self.next
    }

    /// `CLinkerBase::setNext`.
    pub fn set_next(&mut self, next: ExpanderBranchedLinkerId) -> &mut Self {
        self.next = next;
        self
    }

    /// `CLinkerBase::hasNext`.
    pub fn has_next(&self) -> bool {
        self.next.is_some()
    }

    /// Port of `appendCacheValue`.
    pub fn append_cache_value(&mut self, cache_value: CCacheValue) -> &mut Self {
        // `mNonDetCacheValues.append(...)` (CCACHINGLIST) = push to the back.
        self.non_det_cache_values.push(cache_value);
        self.values_count += 1;
        self
    }

    /// Port of `getCacheValueList`.
    pub fn get_cache_value_list(&self) -> &Vec<CCacheValue> {
        &self.non_det_cache_values
    }

    /// Port of `getCacheValueCount`.
    pub fn get_cache_value_count(&self) -> Cint64 {
        self.values_count
    }
}

// ===========================================================================
// Cache entry (`CSignatureSatisfiableExpanderCacheEntry`).
// ===========================================================================

/// Port of `CSignatureSatisfiableExpanderCacheEntry`.
///
/// One cached signature's satisfiability record: its tag→value hash, the
/// deterministic expander-value linker chain, the branched linker chain, and the
/// satisfiability flags.
pub struct SignatureSatisfiableExpanderCacheEntry {
    // KONCLUDE-PORT-NOTE[ownership]: back-pointer to the owning cache's context.
    /// `CSignatureSatisfiableExpanderCacheEntry::mContext`.
    pub context: Cint64,
    // KONCLUDE-PORT-NOTE[memory-pool]: `CCACHINGHASH<cint64,CExpanderCacheValueLinker*>*`
    // pool-managed concurrent-modification hash.
    /// `CSignatureSatisfiableExpanderCacheEntry::mTagExpanderCacheValueHash`.
    pub tag_expander_cache_value_hash: SigExpanderTagHash,
    // KONCLUDE-PORT-NOTE[ownership]: `CExpanderCacheValueLinker* mDetExpandValueLinker`.
    /// `CSignatureSatisfiableExpanderCacheEntry::mDetExpandValueLinker`.
    pub det_expand_value_linker: ExpanderCacheValueLinkerId,
    // KONCLUDE-PORT-NOTE[ownership]: `CExpanderBranchedLinker* mExpandBranchedLinker`.
    /// `CSignatureSatisfiableExpanderCacheEntry::mExpandBranchedLinker`.
    pub expand_branched_linker: ExpanderBranchedLinkerId,
    /// `CSignatureSatisfiableExpanderCacheEntry::mDetExpandCount`.
    pub det_expand_count: Cint64,
    /// `CSignatureSatisfiableExpanderCacheEntry::mSatisfiable`.
    pub satisfiable: bool,
    /// `CSignatureSatisfiableExpanderCacheEntry::mSatisfiableWithoutBranchedConcept`.
    pub satisfiable_without_branched_concept: bool,
    /// `CSignatureSatisfiableExpanderCacheEntry::mMultipleExpanded`.
    pub multiple_expanded: bool,
}

impl Default for SignatureSatisfiableExpanderCacheEntry {
    fn default() -> Self {
        SignatureSatisfiableExpanderCacheEntry {
            context: 0,
            tag_expander_cache_value_hash: HashMap::new(),
            det_expand_value_linker: ExpanderCacheValueLinkerId::NONE,
            expand_branched_linker: ExpanderBranchedLinkerId::NONE,
            det_expand_count: 0,
            satisfiable: false,
            satisfiable_without_branched_concept: false,
            multiple_expanded: false,
        }
    }
}

impl SignatureSatisfiableExpanderCacheEntry {
    /// Port of `CSignatureSatisfiableExpanderCacheEntry::CSignatureSatisfiableExpanderCacheEntry`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `appendExpanderCacheValueLinker`.
    pub fn append_expander_cache_value_linker(
        &mut self,
        linker: ExpanderCacheValueLinkerId,
        cache_context: &mut CacheContext,
    ) -> &mut Self {
        let mut linker_it = linker;
        while linker_it.is_some() {
            self.det_expand_count += 1;
            linker_it = cache_context
                .expander_cache_value_linker(linker_it)
                .get_next();
        }
        if self.det_expand_value_linker.is_none() {
            self.det_expand_value_linker = linker;
            return self;
        }
        if linker.is_none() {
            return self;
        }

        let mut tail = self.det_expand_value_linker;
        while cache_context.expander_cache_value_linker(tail).has_next() {
            tail = cache_context.expander_cache_value_linker(tail).get_next();
        }
        cache_context
            .expander_cache_value_linker_mut(tail)
            .set_next(linker);
        self
    }

    /// Port of `getExpanderCacheValueLinker`.
    pub fn get_expander_cache_value_linker(&self) -> ExpanderCacheValueLinkerId {
        self.det_expand_value_linker
    }

    /// Port of `appendExpanderBranchedLinker`.
    pub fn append_expander_branched_linker(
        &mut self,
        linker: ExpanderBranchedLinkerId,
        cache_context: &mut CacheContext,
    ) -> &mut Self {
        if self.expand_branched_linker.is_none() {
            self.expand_branched_linker = linker;
            return self;
        }
        if linker.is_none() {
            return self;
        }

        let old_head = self.expand_branched_linker;
        let mut tail = linker;
        while cache_context.expander_branched_linker(tail).has_next() {
            tail = cache_context.expander_branched_linker(tail).get_next();
        }
        cache_context
            .expander_branched_linker_mut(tail)
            .set_next(old_head);
        self.expand_branched_linker = linker;
        self
    }

    /// Port of `getExpanderBranchedLinker`.
    pub fn get_expander_branched_linker(&self) -> ExpanderBranchedLinkerId {
        self.expand_branched_linker
    }

    /// Port of `getTagExpanderCacheValueHash`.
    pub fn get_tag_expander_cache_value_hash(&self) -> &SigExpanderTagHash {
        &self.tag_expander_cache_value_hash
    }

    /// Port of `setTagExpanderCacheValueHash`.
    pub fn set_tag_expander_cache_value_hash(&mut self, hash: SigExpanderTagHash) -> &mut Self {
        self.tag_expander_cache_value_hash = hash;
        self
    }

    /// Port of `getExpanderCacheValueCount`.
    pub fn get_expander_cache_value_count(&self) -> Cint64 {
        self.det_expand_count
    }

    /// Port of `isSatisfiable`.
    pub fn is_satisfiable(&self) -> bool {
        self.satisfiable
    }

    /// Port of `setSatisfiable`.
    pub fn set_satisfiable(&mut self, satisfiable: bool) -> &mut Self {
        self.satisfiable = satisfiable;
        self
    }

    /// Port of `isSatisfiableWithoutBranchedConcepts`.
    pub fn is_satisfiable_without_branched_concepts(&self) -> bool {
        self.satisfiable_without_branched_concept
    }

    /// Port of `setSatisfiableWithoutBranchedConcepts`.
    pub fn set_satisfiable_without_branched_concepts(&mut self, sat: bool) -> &mut Self {
        self.satisfiable_without_branched_concept = sat;
        self
    }

    /// Port of `hasMultipleExpanded`.
    pub fn has_multiple_expanded(&self) -> bool {
        self.multiple_expanded
    }

    /// Port of `setMultipleExpanded`.
    pub fn set_multiple_expanded(&mut self, expanded: bool) -> &mut Self {
        self.multiple_expanded = expanded;
        self
    }
}

// ===========================================================================
// Cache-value list/set (`CCACHINGLIST/SET<CCacheValue>`).
// ===========================================================================

/// Port slice of `CCACHINGLIST<CCacheValue>` for sig-expander branch payloads.
///
/// KONCLUDE-PORT-NOTE[memory-pool]: the C++ container is pool-managed and passed
/// by pointer. The Rust port stores the list payload in a `CacheContext` arena.
#[derive(Debug, Default, Clone)]
pub struct SignatureSatisfiableExpanderCacheValueList {
    /// Cache values in list iteration order.
    pub cache_values: Vec<CCacheValue>,
}

impl SignatureSatisfiableExpanderCacheValueList {
    /// Port of default `CCACHINGLIST<CCacheValue>` construction.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `CCACHINGLIST<CCacheValue>::append`.
    pub fn append(&mut self, cache_value: CCacheValue) -> &mut Self {
        self.cache_values.push(cache_value);
        self
    }

    /// Port of `CCACHINGLIST<CCacheValue>::isEmpty`.
    pub fn is_empty(&self) -> bool {
        self.cache_values.is_empty()
    }

    /// Port of `CCACHINGLIST<CCacheValue>::takeFirst`.
    pub fn take_first(&mut self) -> Option<CCacheValue> {
        if self.cache_values.is_empty() {
            None
        } else {
            Some(self.cache_values.remove(0))
        }
    }

    /// Port of const iteration over `CCACHINGLIST<CCacheValue>`.
    pub fn iter(&self) -> std::slice::Iter<'_, CCacheValue> {
        self.cache_values.iter()
    }
}

/// Port slice of `CCACHINGSET<CCacheValue>` for the sig-expander hasher.
///
/// KONCLUDE-PORT-NOTE[memory-pool]: the C++ container is pool-managed. The Rust
/// port keeps the container payload in a `CacheContext` arena and preserves
/// uniqueness plus iteration over the contained `CCacheValue`s, matching the
/// local `CCACHINGSET` precedent in `cache::reuse`.
#[derive(Debug, Default, Clone)]
pub struct SignatureSatisfiableExpanderCacheValueSet {
    /// Unique cache values in iteration order.
    pub cache_values: Vec<CCacheValue>,
}

impl SignatureSatisfiableExpanderCacheValueSet {
    /// Port of default `CCACHINGSET<CCacheValue>` construction.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `CCACHINGSET<CCacheValue>::insert`.
    pub fn insert(&mut self, cache_value: CCacheValue) -> &mut Self {
        if !self.cache_values.contains(&cache_value) {
            self.cache_values.push(cache_value);
        }
        self
    }

    /// Port of `CCACHINGSET<CCacheValue>::contains`.
    pub fn contains(&self, cache_value: CCacheValue) -> bool {
        self.cache_values.contains(&cache_value)
    }

    /// Port of `CCACHINGSET<CCacheValue>::count`.
    pub fn count(&self) -> Cint64 {
        self.cache_values.len() as Cint64
    }

    /// Port of const iteration over `CCACHINGSET<CCacheValue>`.
    pub fn iter(&self) -> std::slice::Iter<'_, CCacheValue> {
        self.cache_values.iter()
    }
}

/// Port slice of `CCACHINGHASH<cint64,cint64>` used as the expander dependency
/// multimap (`tag -> dependent tag`).
///
/// KONCLUDE-PORT-NOTE[memory-pool]: Qt's multi-hash iteration can return several
/// values for the same key. A vector of pairs preserves that grouped iteration
/// surface for the sig-expander dependency builder.
#[derive(Debug, Default, Clone)]
pub struct SignatureSatisfiableExpanderDepHash {
    /// Ordered `(tag, dependent_tag)` pairs.
    pub deps: Vec<(Cint64, Cint64)>,
}

impl SignatureSatisfiableExpanderDepHash {
    /// Port of default `CCACHINGHASH<cint64,cint64>` construction.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `CCACHINGHASH<cint64,cint64>::insert`.
    pub fn insert(&mut self, tag: Cint64, dep_tag: Cint64) -> &mut Self {
        self.deps.push((tag, dep_tag));
        self
    }

    /// Port of the `constFind(tag)`/same-key iteration used by Konclude.
    pub fn dep_tags_for(&self, tag: Cint64) -> impl Iterator<Item = Cint64> + '_ {
        self.deps
            .iter()
            .filter(move |(stored_tag, _)| *stored_tag == tag)
            .map(|(_, dep_tag)| *dep_tag)
    }
}

// ===========================================================================
// Hasher (`CSignatureSatisfiableExpanderCacheHasher`).
// ===========================================================================

/// Port of `CSignatureSatisfiableExpanderCacheHasher`.
///
/// The hash key over a cache-value set / expander-value linker chain (drives the
/// `mHasherItemHash` lookup).
#[derive(Clone)]
pub struct SignatureSatisfiableExpanderCacheHasher {
    /// `CSignatureSatisfiableExpanderCacheHasher::mHashValue`.
    pub hash_value: Cint64,
    /// `CSignatureSatisfiableExpanderCacheHasher::mCacheValueCount`.
    pub cache_value_count: Cint64,
    // KONCLUDE-PORT-NOTE[ownership]: `CExpanderCacheValueLinker* mCacheValueLinker`.
    /// `CSignatureSatisfiableExpanderCacheHasher::mCacheValueLinker`.
    pub cache_value_linker: ExpanderCacheValueLinkerId,
    // KONCLUDE-PORT-NOTE[memory-pool]: `CCACHINGSET<CCacheValue>*` pool set.
    /// `CSignatureSatisfiableExpanderCacheHasher::mCacheValueSet`.
    pub cache_value_set: SigExpanderCacheValueSetId,
}

impl Default for SignatureSatisfiableExpanderCacheHasher {
    fn default() -> Self {
        SignatureSatisfiableExpanderCacheHasher {
            hash_value: 0,
            cache_value_count: 0,
            cache_value_linker: ExpanderCacheValueLinkerId::NONE,
            cache_value_set: SigExpanderCacheValueSetId::NONE,
        }
    }
}

impl SignatureSatisfiableExpanderCacheHasher {
    /// Port of `CSignatureSatisfiableExpanderCacheHasher::CSignatureSatisfiableExpanderCacheHasher`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `CSignatureSatisfiableExpanderCacheHasher(CCACHINGSET<CCacheValue>* cacheValueSet)`.
    pub fn new_from_set(
        cache_value_set: SigExpanderCacheValueSetId,
        cache_context: &CacheContext,
    ) -> Self {
        let mut hasher = SignatureSatisfiableExpanderCacheHasher {
            cache_value_set,
            hash_value: 0,
            cache_value_count: cache_context
                .sig_expander_cache_value_set(cache_value_set)
                .count(),
            cache_value_linker: ExpanderCacheValueLinkerId::NONE,
        };
        hasher.calculate_hash_value_set(cache_value_set, cache_context);
        hasher
    }

    /// Port of `CSignatureSatisfiableExpanderCacheHasher(CExpanderCacheValueLinker*, cint64 count)`.
    pub fn new_from_linker(
        cache_value_linker: ExpanderCacheValueLinkerId,
        count: Cint64,
        cache_context: &CacheContext,
    ) -> Self {
        let mut hasher = SignatureSatisfiableExpanderCacheHasher {
            cache_value_set: SigExpanderCacheValueSetId::NONE,
            hash_value: 0,
            cache_value_count: count,
            cache_value_linker,
        };
        hasher.calculate_hash_value_linker(
            cache_value_linker,
            hasher.cache_value_count,
            cache_context,
        );
        hasher
    }

    /// Port of `getHashValue`.
    pub fn get_hash_value(&self) -> Cint64 {
        self.hash_value
    }

    /// Port of `operator==`.
    pub fn equals(
        &self,
        hasher: &SignatureSatisfiableExpanderCacheHasher,
        cache_context: &CacheContext,
    ) -> bool {
        if self.hash_value != hasher.hash_value {
            return false;
        }
        if self.cache_value_count != hasher.cache_value_count {
            return false;
        }
        if self.cache_value_linker.is_some() && hasher.cache_value_linker.is_some() {
            if !self.has_equal_cache_values_linker_linker(
                self.cache_value_linker,
                hasher.cache_value_linker,
                self.cache_value_count,
                cache_context,
            ) {
                return false;
            }
        } else if self.cache_value_set.is_some() && hasher.cache_value_set.is_some() {
            if !self.has_equal_cache_values_set_set(
                self.cache_value_set,
                hasher.cache_value_set,
                cache_context,
            ) {
                return false;
            }
        } else if self.cache_value_linker.is_some() && hasher.cache_value_set.is_some() {
            if !self.has_equal_cache_values_linker_set(
                self.cache_value_linker,
                hasher.cache_value_set,
                self.cache_value_count,
                cache_context,
            ) {
                return false;
            }
        } else if !self.has_equal_cache_values_linker_set(
            hasher.cache_value_linker,
            self.cache_value_set,
            self.cache_value_count,
            cache_context,
        ) {
            return false;
        }
        false
    }

    /// Port of the free `qHash(const CSignatureSatisfiableExpanderCacheHasher&)`.
    pub fn q_hash(&self) -> u32 {
        let key: Cint64 = self.get_hash_value();
        if std::mem::size_of::<Cint64>() > std::mem::size_of::<u32>() {
            ((key >> (8 * std::mem::size_of::<u32>() - 1)) ^ key) as u32
        } else {
            key as u32
        }
    }

    /// Port of protected `extendHashValue`.
    fn extend_hash_value(&mut self, cache_value: CCacheValue) {
        self.hash_value += cache_value.q_hash() as Cint64;
    }

    /// Port of protected `calculateHashValue(CCACHINGSET<CCacheValue>*)`.
    fn calculate_hash_value_set(
        &mut self,
        cache_value_set: SigExpanderCacheValueSetId,
        cache_context: &CacheContext,
    ) {
        self.hash_value = 0;
        for cache_value in cache_context
            .sig_expander_cache_value_set(cache_value_set)
            .iter()
        {
            self.extend_hash_value(*cache_value);
        }
    }

    /// Context-threaded port of protected `calculateHashValue(CExpanderCacheValueLinker*, cint64)`.
    fn calculate_hash_value_linker(
        &mut self,
        cache_value_linker: ExpanderCacheValueLinkerId,
        count: Cint64,
        cache_context: &CacheContext,
    ) {
        self.hash_value = 0;
        let mut cache_value_linker_it = cache_value_linker;
        let mut nr: Cint64 = 0;
        while cache_value_linker_it.is_some() && {
            let cond = nr < count;
            nr += 1;
            cond
        } {
            let linker = cache_context.expander_cache_value_linker(cache_value_linker_it);
            self.extend_hash_value(linker.get_cache_value());
            cache_value_linker_it = linker.get_next();
        }
    }

    /// Port of protected `hasEqualCacheValues(linker, linker2, count)`.
    fn has_equal_cache_values_linker_linker(
        &self,
        mut cache_value_linker: ExpanderCacheValueLinkerId,
        mut cache_value_linker2: ExpanderCacheValueLinkerId,
        count: Cint64,
        cache_context: &CacheContext,
    ) -> bool {
        let mut nr: Cint64 = 0;
        while cache_value_linker.is_some() && cache_value_linker2.is_some() && {
            let cond = nr < count;
            nr += 1;
            cond
        } {
            let linker = cache_context.expander_cache_value_linker(cache_value_linker);
            let linker2 = cache_context.expander_cache_value_linker(cache_value_linker2);
            if linker.get_cache_value() != linker2.get_cache_value() {
                return false;
            }
            cache_value_linker = linker.get_next();
            cache_value_linker2 = linker2.get_next();
        }
        if nr < count && (cache_value_linker.is_some() || cache_value_linker2.is_some()) {
            return false;
        }
        true
    }

    /// Port of protected `hasEqualCacheValues(set, set2)`.
    fn has_equal_cache_values_set_set(
        &self,
        cache_value_set: SigExpanderCacheValueSetId,
        cache_value_set2: SigExpanderCacheValueSetId,
        cache_context: &CacheContext,
    ) -> bool {
        let set = cache_context.sig_expander_cache_value_set(cache_value_set);
        let set2 = cache_context.sig_expander_cache_value_set(cache_value_set2);
        let mut it1 = set.iter();
        let mut it2 = set2.iter();
        while let Some(value1) = it1.next() {
            let Some(value2) = it2.next() else {
                return false;
            };
            if value1 != value2 {
                return false;
            }
        }
        if it2.next().is_some() {
            return false;
        }
        true
    }

    /// Port of protected `hasEqualCacheValues(linker, set, count)`.
    fn has_equal_cache_values_linker_set(
        &self,
        mut cache_value_linker: ExpanderCacheValueLinkerId,
        cache_value_set: SigExpanderCacheValueSetId,
        count: Cint64,
        cache_context: &CacheContext,
    ) -> bool {
        let mut nr: Cint64 = 0;
        while cache_value_linker.is_some() && {
            let cond = nr < count;
            nr += 1;
            cond
        } {
            let linker = cache_context.expander_cache_value_linker(cache_value_linker);
            if !cache_context
                .sig_expander_cache_value_set(cache_value_set)
                .contains(linker.get_cache_value())
            {
                return false;
            }
            cache_value_linker = linker.get_next();
        }
        true
    }
}

// ===========================================================================
// Redirection item (`CSignatureSatisfiableExpanderCacheRedirectionItem`).
// ===========================================================================

/// Port of `CSignatureSatisfiableExpanderCacheRedirectionItem`.
///
/// A signature→entry redirection record stored in the slot-item hashes.
pub struct SignatureSatisfiableExpanderCacheRedirectionItem {
    // KONCLUDE-PORT-NOTE[ownership]: `CSignatureSatisfiableExpanderCacheEntry* mCacheEntry`.
    /// `CSignatureSatisfiableExpanderCacheRedirectionItem::mCacheEntry`.
    pub cache_entry: SigExpanderCacheEntryId,
    /// `CSignatureSatisfiableExpanderCacheRedirectionItem::mSignature`.
    pub signature: Cint64,
    /// `CSignatureSatisfiableExpanderCacheRedirectionItem::mExpCount`.
    pub exp_count: Cint64,
}

impl Default for SignatureSatisfiableExpanderCacheRedirectionItem {
    fn default() -> Self {
        SignatureSatisfiableExpanderCacheRedirectionItem {
            cache_entry: SigExpanderCacheEntryId::NONE,
            signature: 0,
            exp_count: 0,
        }
    }
}

impl SignatureSatisfiableExpanderCacheRedirectionItem {
    /// Port of `CSignatureSatisfiableExpanderCacheRedirectionItem::CSignatureSatisfiableExpanderCacheRedirectionItem`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `initRedirectionItem`.
    pub fn init_redirection_item(
        &mut self,
        cache_entry: SigExpanderCacheEntryId,
        signature: Cint64,
        expander_count: Cint64,
    ) -> &mut Self {
        self.cache_entry = cache_entry;
        self.signature = signature;
        self.exp_count = expander_count;
        self
    }

    /// Port of `getCacheEntry`.
    pub fn get_cache_entry(&self) -> SigExpanderCacheEntryId {
        self.cache_entry
    }

    /// Port of `getSignature`.
    pub fn get_signature(&self) -> Cint64 {
        self.signature
    }

    /// Port of `getExpanderCount`.
    pub fn get_expander_count(&self) -> Cint64 {
        self.exp_count
    }
}

// ===========================================================================
// Slot item (`CSignatureSatisfiableExpanderCacheSlotItem`).
// ===========================================================================

/// Port of `CSignatureSatisfiableExpanderCacheSlotItem` (bases
/// `CMemoryPoolContainer`, `CLinkerBase`).
///
/// A reader-shared snapshot slot holding the signature/hasher → redirection-item
/// hashes plus the atomic reader-sharing refcount.
pub struct SignatureSatisfiableExpanderCacheSlotItem {
    // KONCLUDE-PORT-NOTE[memory-pool]: `CMemoryPoolContainer` base mem-pool handle.
    /// `CMemoryPoolContainer` memory pool back-handle.
    pub memory_pool: Cint64,
    // KONCLUDE-PORT-NOTE[ownership]: `CLinkerBase` intrusive self-chain → `next`.
    /// `CLinkerBase` next link.
    pub next: SigExpanderSlotItemId,
    // KONCLUDE-PORT-NOTE[memory-pool]: `CCACHINGHASH<cint64,…RedirectionItem*>*` pool hash.
    /// `CSignatureSatisfiableExpanderCacheSlotItem::mSigItemHash`.
    pub sig_item_hash: HashMap<Cint64, SigExpanderRedirectionItemId>,
    // KONCLUDE-PORT-NOTE[memory-pool]: `CCACHINGHASH<…Hasher,…RedirectionItem*>*` pool hash.
    /// `CSignatureSatisfiableExpanderCacheSlotItem::mHasherItemHash`.
    pub hasher_item_hash: SigExpanderHasherItemHash,
    // KONCLUDE-PORT-NOTE[threading]: `QAtomicInt mReaderSharingCount` → atomic word.
    /// `CSignatureSatisfiableExpanderCacheSlotItem::mReaderSharingCount`.
    pub reader_sharing_count: Cint64,
    /// `CSignatureSatisfiableExpanderCacheSlotItem::mReaderUsing`.
    pub reader_using: bool,
}

impl Default for SignatureSatisfiableExpanderCacheSlotItem {
    fn default() -> Self {
        SignatureSatisfiableExpanderCacheSlotItem {
            memory_pool: 0,
            next: SigExpanderSlotItemId::NONE,
            sig_item_hash: HashMap::new(),
            hasher_item_hash: Vec::new(),
            reader_sharing_count: 0,
            reader_using: false,
        }
    }
}

impl SignatureSatisfiableExpanderCacheSlotItem {
    /// Port of `CSignatureSatisfiableExpanderCacheSlotItem::CSignatureSatisfiableExpanderCacheSlotItem`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `incReader()`.
    pub fn inc_reader(&mut self) -> bool {
        // KONCLUDE-PORT-NOTE[threading]: `mReaderSharingCount.ref()` atomically increments and
        // returns whether the new value is non-zero; single-threaded inline here.
        self.reader_sharing_count += 1;
        if self.reader_sharing_count != 0 {
            self.reader_using = true;
        }
        true
    }

    /// Port of `incReader(cint64 incCount)`.
    pub fn inc_reader_count(&mut self, inc_count: Cint64) -> bool {
        let mut i: Cint64 = 0;
        while i < inc_count {
            self.inc_reader();
            i += 1;
        }
        self.reader_using
    }

    /// Port of `decReader()`.
    pub fn dec_reader(&mut self) -> bool {
        // KONCLUDE-PORT-NOTE[threading]: `mReaderSharingCount.deref()` atomically decrements and
        // returns whether the new value is non-zero; single-threaded inline here.
        self.reader_sharing_count -= 1;
        if self.reader_sharing_count == 0 {
            self.reader_using = false;
        }
        self.reader_using
    }

    /// Port of `setSignatureItemHash`.
    pub fn set_signature_item_hash(
        &mut self,
        sig_item_hash: HashMap<Cint64, SigExpanderRedirectionItemId>,
    ) -> &mut Self {
        self.sig_item_hash = sig_item_hash;
        self
    }

    /// Port of `setHasherItemHash`.
    pub fn set_hasher_item_hash(
        &mut self,
        hasher_item_hash: SigExpanderHasherItemHash,
    ) -> &mut Self {
        self.hasher_item_hash = hasher_item_hash;
        self
    }

    /// Port of `hasCacheReaders`.
    pub fn has_cache_readers(&self) -> bool {
        self.reader_using
    }

    /// Port of `getSignatureItemHash`.
    pub fn get_signature_item_hash(&self) -> &HashMap<Cint64, SigExpanderRedirectionItemId> {
        &self.sig_item_hash
    }

    /// Port of `getHasherItemHash`.
    pub fn get_hasher_item_hash(&self) -> &SigExpanderHasherItemHash {
        &self.hasher_item_hash
    }

    /// `CLinkerBase::getNext`.
    pub fn get_next(&self) -> SigExpanderSlotItemId {
        self.next
    }

    /// `CLinkerBase::setNext`.
    pub fn set_next(&mut self, next: SigExpanderSlotItemId) -> &mut Self {
        self.next = next;
        self
    }

    /// `CLinkerBase::hasNext`.
    pub fn has_next(&self) -> bool {
        self.next.is_some()
    }

    /// `CMemoryPoolContainer::getMemoryPools` (opaque pool handle).
    pub fn get_memory_pools(&self) -> Cint64 {
        self.memory_pool
    }
}

// ===========================================================================
// Reader (`CSignatureSatisfiableExpanderCacheReader`).
// ===========================================================================

/// Port of `CSignatureSatisfiableExpanderCacheReader` (base `CLinkerBase`).
///
/// A per-thread read cursor over the cache: a current slot plus an atomic
/// "updated slot" the writer publishes for lock-free version switching.
pub struct SignatureSatisfiableExpanderCacheReader {
    // KONCLUDE-PORT-NOTE[ownership]: `CLinkerBase` intrusive self-chain → `next`
    // (the cache's `mReaderLinker` reader list).
    /// `CLinkerBase` next link.
    pub next: SigExpanderCacheReaderId,
    // KONCLUDE-PORT-NOTE[ownership]: `CSignatureSatisfiableExpanderCacheSlotItem* mCurrentSlot`.
    /// `CSignatureSatisfiableExpanderCacheReader::mCurrentSlot`.
    pub current_slot: SigExpanderSlotItemId,
    // KONCLUDE-PORT-NOTE[threading]: `QAtomicPointer<…SlotItem> mUpdatedSlot` →
    // atomically-published slot id (lock-free reader version switch).
    /// `CSignatureSatisfiableExpanderCacheReader::mUpdatedSlot`.
    pub updated_slot: SigExpanderSlotItemId,
}

impl Default for SignatureSatisfiableExpanderCacheReader {
    fn default() -> Self {
        SignatureSatisfiableExpanderCacheReader {
            next: SigExpanderCacheReaderId::NONE,
            current_slot: SigExpanderSlotItemId::NONE,
            updated_slot: SigExpanderSlotItemId::NONE,
        }
    }
}

impl SignatureSatisfiableExpanderCacheReader {
    /// Port of `CSignatureSatisfiableExpanderCacheReader::CSignatureSatisfiableExpanderCacheReader`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `updateSlot`.
    pub fn update_slot(
        &mut self,
        updated_slot: SigExpanderSlotItemId,
        cache_context: &mut CacheContext,
    ) -> &mut Self {
        // KONCLUDE-PORT-NOTE[threading]: `mUpdatedSlot.fetchAndStoreOrdered(updatedSlot)` is an
        // atomic swap returning the previous value; single-threaded inline here.
        let prev_slot = self.updated_slot;
        self.updated_slot = updated_slot;
        if prev_slot.is_some() {
            cache_context
                .sig_expander_slot_item_mut(prev_slot)
                .dec_reader();
        }
        self
    }

    /// Port of protected `hasUpdatedSlotItem`.
    fn has_updated_slot_item(&self) -> bool {
        // KONCLUDE-PORT-NOTE[threading]: `mUpdatedSlot.fetchAndAddRelaxed(0) != nullptr`.
        self.updated_slot.is_some()
    }

    /// Port of protected `switchToUpdatedSlotItem`.
    fn switch_to_updated_slot_item(&mut self, cache_context: &mut CacheContext) -> bool {
        // KONCLUDE-PORT-NOTE[threading]: `mUpdatedSlot.fetchAndStoreOrdered(nullptr)`.
        let updated_slot = self.updated_slot;
        self.updated_slot = SigExpanderSlotItemId::NONE;
        if updated_slot.is_some() {
            let prev_slot = self.current_slot;
            self.current_slot = updated_slot;
            if prev_slot.is_some() {
                cache_context
                    .sig_expander_slot_item_mut(prev_slot)
                    .dec_reader();
            }
            return true;
        }
        false
    }

    /// Port of `hasCacheEntry(cint64 signature)`.
    pub fn has_cache_entry(&mut self, signature: Cint64, cache_context: &mut CacheContext) -> bool {
        if self.has_updated_slot_item() {
            self.switch_to_updated_slot_item(cache_context);
        }
        if self.current_slot.is_some() {
            let sig_item_hash = cache_context
                .sig_expander_slot_item(self.current_slot)
                .get_signature_item_hash();
            return sig_item_hash.contains_key(&signature);
        }
        false
    }

    /// Port of `getCacheEntry(cint64 signature)`.
    pub fn get_cache_entry_by_signature(
        &mut self,
        signature: Cint64,
        cache_context: &mut CacheContext,
    ) -> SigExpanderCacheEntryId {
        let entry = SigExpanderCacheEntryId::NONE;
        if self.has_updated_slot_item() {
            self.switch_to_updated_slot_item(cache_context);
        }
        if self.current_slot.is_some() {
            let item = cache_context
                .sig_expander_slot_item(self.current_slot)
                .get_signature_item_hash()
                .get(&signature)
                .copied()
                .unwrap_or(SigExpanderRedirectionItemId::NONE);
            if item.is_some() {
                return cache_context
                    .sig_expander_redirection_item(item)
                    .get_cache_entry();
            }
        }
        entry
    }

    /// Port of `getCacheEntry(CCACHINGSET<CCacheValue>* cacheValueSet)`.
    pub fn get_cache_entry_by_value_set(
        &mut self,
        cache_value_set: SigExpanderCacheValueSetId,
        cache_context: &mut CacheContext,
    ) -> SigExpanderCacheEntryId {
        let entry = SigExpanderCacheEntryId::NONE;
        if self.has_updated_slot_item() {
            self.switch_to_updated_slot_item(cache_context);
        }
        if self.current_slot.is_some() {
            let hash_value = SignatureSatisfiableExpanderCacheHasher::new_from_set(
                cache_value_set,
                cache_context,
            );
            let item = cache_context
                .sig_expander_slot_item(self.current_slot)
                .get_hasher_item_hash()
                .iter()
                .find_map(|(stored_hash, redirection)| {
                    if stored_hash.q_hash() == hash_value.q_hash()
                        && stored_hash.equals(&hash_value, cache_context)
                    {
                        Some(*redirection)
                    } else {
                        None
                    }
                })
                .unwrap_or(SigExpanderRedirectionItemId::NONE);
            if item.is_some() {
                return cache_context
                    .sig_expander_redirection_item(item)
                    .get_cache_entry();
            }
        }
        entry
    }

    /// `CLinkerBase::getNext`.
    pub fn get_next(&self) -> SigExpanderCacheReaderId {
        self.next
    }

    /// `CLinkerBase::setNext`.
    pub fn set_next(&mut self, next: SigExpanderCacheReaderId) -> &mut Self {
        self.next = next;
        self
    }

    /// `CLinkerBase::hasNext`.
    pub fn has_next(&self) -> bool {
        self.next.is_some()
    }
}

// ===========================================================================
// Writer (`CSignatureSatisfiableExpanderCacheWriter`).
// ===========================================================================

/// Port of `CSignatureSatisfiableExpanderCacheWriter`.
///
/// The serialised write facade: holds a back-pointer to the cache it drains
/// write events into.
pub struct SignatureSatisfiableExpanderCacheWriter {
    // KONCLUDE-PORT-NOTE[ownership]: `CSignatureSatisfiableExpanderCache* mCache`
    // — back-pointer to the long-lived facade thread → opaque handle.
    /// `CSignatureSatisfiableExpanderCacheWriter::mCache`.
    pub cache: Cint64,
}

impl Default for SignatureSatisfiableExpanderCacheWriter {
    fn default() -> Self {
        SignatureSatisfiableExpanderCacheWriter { cache: 0 }
    }
}

impl SignatureSatisfiableExpanderCacheWriter {
    /// Port of `CSignatureSatisfiableExpanderCacheWriter::CSignatureSatisfiableExpanderCacheWriter`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `CSignatureSatisfiableExpanderCacheWriter(CSignatureSatisfiableExpanderCache*)`.
    pub fn new_with_cache(cache: Cint64) -> Self {
        SignatureSatisfiableExpanderCacheWriter { cache }
    }

    /// Port of `writeCachedData` — forwards to the owning cache facade.
    pub fn write_cached_data(
        &mut self,
        cache: &mut SignatureSatisfiableExpanderCache,
        write_data: SigExpanderEntryWriteDataId,
        memory_pools: Cint64,
        cache_context: &mut CacheContext,
    ) -> &mut Self {
        // KONCLUDE-PORT-NOTE[ownership]: C++ forwards through `mCache`; the Rust
        // port threads the owning facade explicitly because there is no stable
        // raw `this` pointer for the long-lived cache singleton.
        cache.write_cached_data(write_data, memory_pools, cache_context);
        self
    }

    /// Port of `writeExpandCached` — forwards to the owning cache facade.
    pub fn write_expand_cached(
        &mut self,
        cache: &mut SignatureSatisfiableExpanderCache,
        prev_signature: Cint64,
        new_signature: Cint64,
        cache_value_list: SigExpanderCacheValueListId,
        dep_hash: SigExpanderDepHashId,
        memory_pools: Cint64,
        cache_context: &mut CacheContext,
    ) -> &mut Self {
        cache.write_expand_cached(
            prev_signature,
            new_signature,
            cache_value_list,
            dep_hash,
            memory_pools,
            cache_context,
        );
        self
    }

    /// Port of `writeSatisfiableBranchCached` — forwards to the owning cache facade.
    pub fn write_satisfiable_branch_cached(
        &mut self,
        cache: &mut SignatureSatisfiableExpanderCache,
        signature: Cint64,
        cache_value_list: SigExpanderCacheValueListId,
        branched_list: SigExpanderCacheValueListId,
        memory_pools: Cint64,
        cache_context: &mut CacheContext,
    ) -> &mut Self {
        cache.write_satisfiable_branch_cached(
            signature,
            cache_value_list,
            branched_list,
            memory_pools,
            cache_context,
        );
        self
    }
}

// ===========================================================================
// Entry write-data record family (manifest-flagged → tagged enum).
// Collapses `CSignatureSatisfiableExpanderCacheEntryWriteData` (base, empty),
// `…EntryExpandWriteData`, and `…EntrySatisfiableBranchWriteData`.
// ===========================================================================

/// Port of the `CSignatureSatisfiableExpanderCacheEntry*WriteData` family payload.
///
/// One variant per concrete C++ write-data subclass. `Base` is the empty
/// `CSignatureSatisfiableExpanderCacheEntryWriteData` itself.
pub enum SigExpanderEntryWriteDataKind {
    /// Port of `CSignatureSatisfiableExpanderCacheEntryWriteData` (base; no payload).
    Base,
    /// Port of `CSignatureSatisfiableExpanderCacheEntryExpandWriteData`.
    Expand {
        /// `mPrevSignature`.
        prev_signature: Cint64,
        /// `mNewSignature`.
        new_signature: Cint64,
        // KONCLUDE-PORT-NOTE[memory-pool]: `CCACHINGLIST<CCacheValue>* mCacheValueList`.
        /// `mCacheValueList`.
        cache_value_list: SigExpanderCacheValueListId,
        // KONCLUDE-PORT-NOTE[memory-pool]: `CCACHINGHASH<cint64,cint64>* mDepHash`.
        /// `mDepHash`.
        dep_hash: SigExpanderDepHashId,
    },
    /// Port of `CSignatureSatisfiableExpanderCacheEntrySatisfiableBranchWriteData`.
    SatisfiableBranch {
        /// `mSignature`.
        signature: Cint64,
        // KONCLUDE-PORT-NOTE[memory-pool]: `CCACHINGLIST<CCacheValue>* mCacheValueList`.
        /// `mCacheValueList`.
        cache_value_list: SigExpanderCacheValueListId,
        // KONCLUDE-PORT-NOTE[memory-pool]: `CCACHINGLIST<CCacheValue>* mBranchedValueList`.
        /// `mBranchedValueList`.
        branched_value_list: SigExpanderCacheValueListId,
    },
}

impl Default for SigExpanderEntryWriteDataKind {
    fn default() -> Self {
        SigExpanderEntryWriteDataKind::Base
    }
}

/// Port of `CSignatureSatisfiableExpanderCacheEntryWriteData` (+ its two
/// subclasses) as a tagged record (mirrors the W2 `DependencyNode`/`DepKind`
/// collapse). The shared `CCacheEntryWriteData` base header (type tag + the
/// `CLinkerBase` write-data chain) sits alongside the variant payload.
pub struct SignatureSatisfiableExpanderCacheEntryWriteData {
    // --- from CCacheEntryWriteData (F0 base, not yet ported) ---
    // KONCLUDE-PORT-NOTE[api]: `CCacheEntryWriteData::mType` (CACHEWRITEDATATYPE, F0).
    /// `CCacheEntryWriteData::mType`.
    pub cache_write_data_type: Cint64,
    // KONCLUDE-PORT-NOTE[ownership]: `CCacheEntryWriteData` `CLinkerBase` write-data
    // chain (the cache's `mCollectWriteData` collect list) → same-family `next`.
    /// `CLinkerBase` next write-data link.
    pub next: SigExpanderEntryWriteDataId,
    /// The concrete write-data payload.
    pub kind: SigExpanderEntryWriteDataKind,
}

impl Default for SignatureSatisfiableExpanderCacheEntryWriteData {
    fn default() -> Self {
        SignatureSatisfiableExpanderCacheEntryWriteData {
            cache_write_data_type: 0,
            next: SigExpanderEntryWriteDataId::NONE,
            kind: SigExpanderEntryWriteDataKind::Base,
        }
    }
}

impl SignatureSatisfiableExpanderCacheEntryWriteData {
    /// Port of `CSignatureSatisfiableExpanderCacheEntryWriteData::CSignatureSatisfiableExpanderCacheEntryWriteData`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `CSignatureSatisfiableExpanderCacheEntryExpandWriteData::initExpandWriteData`.
    pub fn init_expand_write_data(
        &mut self,
        prev_signature: Cint64,
        new_signature: Cint64,
        cache_value_list: SigExpanderCacheValueListId,
        dep_hash: SigExpanderDepHashId,
    ) -> &mut Self {
        self.kind = SigExpanderEntryWriteDataKind::Expand {
            prev_signature,
            new_signature,
            cache_value_list,
            dep_hash,
        };
        self.cache_write_data_type = CacheWriteDataType::SatExpandCacheWriteDataType as Cint64;
        self
    }

    /// Port of `CSignatureSatisfiableExpanderCacheEntrySatisfiableBranchWriteData::initSatisfiableBranchWriteData`.
    pub fn init_satisfiable_branch_write_data(
        &mut self,
        signature: Cint64,
        cache_value_list: SigExpanderCacheValueListId,
        branched_list: SigExpanderCacheValueListId,
    ) -> &mut Self {
        self.kind = SigExpanderEntryWriteDataKind::SatisfiableBranch {
            signature,
            cache_value_list,
            branched_value_list: branched_list,
        };
        self.cache_write_data_type = CacheWriteDataType::SatBranchCacheWriteDataType as Cint64;
        self
    }

    /// Port of `CCacheEntryWriteData::getCacheWriteDataType`.
    pub fn get_cache_write_data_type(&self) -> Cint64 {
        self.cache_write_data_type
    }

    // --- Expand-subclass getters (`CSignatureSatisfiableExpanderCacheEntryExpandWriteData`) ---

    /// Port of `getPrevSignature`.
    pub fn get_prev_signature(&self) -> Cint64 {
        if let SigExpanderEntryWriteDataKind::Expand { prev_signature, .. } = &self.kind {
            *prev_signature
        } else {
            0
        }
    }

    /// Port of `getNewSignature`.
    pub fn get_new_signature(&self) -> Cint64 {
        if let SigExpanderEntryWriteDataKind::Expand { new_signature, .. } = &self.kind {
            *new_signature
        } else {
            0
        }
    }

    /// Port of `getDepHash`.
    pub fn get_dep_hash(&self) -> SigExpanderDepHashId {
        if let SigExpanderEntryWriteDataKind::Expand { dep_hash, .. } = &self.kind {
            *dep_hash
        } else {
            SigExpanderDepHashId::NONE
        }
    }

    // --- SatisfiableBranch-subclass getters ---

    /// Port of `getSignature`.
    pub fn get_signature(&self) -> Cint64 {
        if let SigExpanderEntryWriteDataKind::SatisfiableBranch { signature, .. } = &self.kind {
            *signature
        } else {
            0
        }
    }

    /// Port of `getBranchedValueList` (opaque CCACHINGLIST handle).
    pub fn get_branched_value_list(&self) -> SigExpanderCacheValueListId {
        if let SigExpanderEntryWriteDataKind::SatisfiableBranch {
            branched_value_list,
            ..
        } = &self.kind
        {
            *branched_value_list
        } else {
            SigExpanderCacheValueListId::NONE
        }
    }

    /// Port of `getCacheValueList` (shared name across both subclasses).
    pub fn get_cache_value_list(&self) -> SigExpanderCacheValueListId {
        match &self.kind {
            SigExpanderEntryWriteDataKind::Expand {
                cache_value_list, ..
            } => *cache_value_list,
            SigExpanderEntryWriteDataKind::SatisfiableBranch {
                cache_value_list, ..
            } => *cache_value_list,
            SigExpanderEntryWriteDataKind::Base => SigExpanderCacheValueListId::NONE,
        }
    }

    /// `CLinkerBase::getNext`.
    pub fn get_next(&self) -> SigExpanderEntryWriteDataId {
        self.next
    }

    /// `CLinkerBase::setNext`.
    pub fn set_next(&mut self, next: SigExpanderEntryWriteDataId) -> &mut Self {
        self.next = next;
        self
    }

    /// `CLinkerBase::hasNext`.
    pub fn has_next(&self) -> bool {
        self.next.is_some()
    }

    /// Context-threaded port of `CLinkerBase::getCount` over the write-data chain.
    pub fn get_count(&self, cache_context: &CacheContext) -> Cint64 {
        let mut linker_count: Cint64 = 0;
        let mut item_linker = self.next;
        linker_count += 1;
        while item_linker.is_some() {
            linker_count += 1;
            item_linker = cache_context
                .sig_expander_entry_write_data(item_linker)
                .get_next();
        }
        linker_count
    }
}

// ===========================================================================
// Facade (`CSignatureSatisfiableExpanderCache`).
// ===========================================================================

/// Port of `CSignatureSatisfiableExpanderCache` (bases `CThread`,
/// `CSatisfiableCache`).
///
/// The cache facade / writer thread: owns the signature→redirection hashes, the
/// signature-reference-count gating, the write-collect buffer, the slot + reader
/// linker chains, and the per-cache memory-pool context.
pub struct SignatureSatisfiableExpanderCache {
    // KONCLUDE-PORT-NOTE[threading]: `CThread` base (Qt worker thread) → opaque
    // handle; the staged single-threaded port drains writes inline.
    /// `CThread` base handle.
    pub thread: Cint64,
    // KONCLUDE-PORT-NOTE[memory-pool]: `CCACHINGHASH<cint64,…RedirectionItem*>* mSigItemHash`.
    /// `CSignatureSatisfiableExpanderCache::mSigItemHash`.
    pub sig_item_hash: HashMap<Cint64, SigExpanderRedirectionItemId>,
    // KONCLUDE-PORT-NOTE[memory-pool]: `CCACHINGSET<cint64>* mIncompatibleSigSet`.
    /// `CSignatureSatisfiableExpanderCache::mIncompatibleSigSet`.
    pub incompatible_sig_set: HashSet<Cint64>,
    // KONCLUDE-PORT-NOTE[memory-pool]: `CCACHINGSET<cint64>* mAlreadyExpSigSet`.
    /// `CSignatureSatisfiableExpanderCache::mAlreadyExpSigSet`.
    pub already_exp_sig_set: HashSet<Cint64>,
    // KONCLUDE-PORT-NOTE[memory-pool]: `CCACHINGHASH<…Hasher,…RedirectionItem*>* mHasherItemHash`
    // (the header marks this "currently not used").
    /// `CSignatureSatisfiableExpanderCache::mHasherItemHash`.
    pub hasher_item_hash: SigExpanderHasherItemHash,
    // KONCLUDE-PORT-NOTE[memory-pool]: `CCACHINGHASH<cint64,cint64>* mSignatureReferCountSet`.
    /// `CSignatureSatisfiableExpanderCache::mSignatureReferCountSet`.
    pub signature_refer_count_set: HashMap<Cint64, Cint64>,
    /// `CSignatureSatisfiableExpanderCache::mNextCacheEntryRequiredSignatureRefCount`.
    pub next_cache_entry_required_signature_ref_count: Cint64,
    /// `CSignatureSatisfiableExpanderCache::mNextMemoryLevelRequiredSignatureRefCount`.
    pub next_memory_level_required_signature_ref_count: Cint64,
    /// `CSignatureSatisfiableExpanderCache::mNextCacheEntryRequiredSignatureReferenceCountIncrease`.
    pub next_cache_entry_required_signature_reference_count_increase: Cint64,
    /// `CSignatureSatisfiableExpanderCache::mNextMemoryLevelIncreaseForRequiredSignatureReferenceCount`.
    pub next_memory_level_increase_for_required_signature_reference_count: Cint64,
    /// `CSignatureSatisfiableExpanderCache::mWriteDataCount`.
    pub write_data_count: Cint64,
    /// `CSignatureSatisfiableExpanderCache::mStartWriteCollectCount`.
    pub start_write_collect_count: Cint64,
    /// `CSignatureSatisfiableExpanderCache::mNextWriteCollectCount`.
    pub next_write_collect_count: Cint64,
    /// `CSignatureSatisfiableExpanderCache::mCollectCount`.
    pub collect_count: Cint64,
    // KONCLUDE-PORT-NOTE[memory-pool]: `CMemoryPool* mCollectMemoryPools`.
    /// `CSignatureSatisfiableExpanderCache::mCollectMemoryPools`.
    pub collect_memory_pools: Cint64,
    // KONCLUDE-PORT-NOTE[ownership]: `CSignatureSatisfiableExpanderCacheEntryWriteData* mCollectWriteData`.
    /// `CSignatureSatisfiableExpanderCache::mCollectWriteData`.
    pub collect_write_data: SigExpanderEntryWriteDataId,
    // KONCLUDE-PORT-NOTE[api]: `CCacheStatistics mCacheStat` (F0) held by value → opaque.
    /// `CSignatureSatisfiableExpanderCache::mCacheStat`.
    pub cache_stat: Cint64,
    // KONCLUDE-PORT-NOTE[ownership]: `CSignatureSatisfiableExpanderCacheSlotItem* mSlotLinker`.
    /// `CSignatureSatisfiableExpanderCache::mSlotLinker`.
    pub slot_linker: SigExpanderSlotItemId,
    // KONCLUDE-PORT-NOTE[ownership]: `CSignatureSatisfiableExpanderCacheReader* mReaderLinker`.
    /// `CSignatureSatisfiableExpanderCache::mReaderLinker`.
    pub reader_linker: SigExpanderCacheReaderId,
    // KONCLUDE-PORT-NOTE[threading]: `QMutex mReaderSyncMutex` → opaque lock handle.
    /// `CSignatureSatisfiableExpanderCache::mReaderSyncMutex`.
    pub reader_sync_mutex: Cint64,
    /// `CSignatureSatisfiableExpanderCache::mContext` (held by value).
    pub context: SignatureSatisfiableExpanderCacheContext,
    // KONCLUDE-PORT-NOTE[api]: `CConfiguration* mConfig` → opaque cross-subsystem handle.
    /// `CSignatureSatisfiableExpanderCache::mConfig`.
    pub config: Cint64,
}

impl Default for SignatureSatisfiableExpanderCache {
    fn default() -> Self {
        SignatureSatisfiableExpanderCache {
            thread: 0,
            sig_item_hash: HashMap::new(),
            incompatible_sig_set: HashSet::new(),
            already_exp_sig_set: HashSet::new(),
            hasher_item_hash: Vec::new(),
            signature_refer_count_set: HashMap::new(),
            next_cache_entry_required_signature_ref_count:
                DEFAULT_SIG_EXPANDER_REQUIRED_SIGNATURE_REFERENCE_COUNT_INCREASE,
            next_memory_level_required_signature_ref_count:
                DEFAULT_SIG_EXPANDER_INITIAL_MEMORY_LEVEL_FOR_REF_COUNT_INCREASE,
            next_cache_entry_required_signature_reference_count_increase:
                DEFAULT_SIG_EXPANDER_REQUIRED_SIGNATURE_REFERENCE_COUNT_INCREASE,
            next_memory_level_increase_for_required_signature_reference_count:
                DEFAULT_SIG_EXPANDER_NEXT_MEMORY_LEVEL_INCREASE_FOR_REF_COUNT,
            write_data_count: 0,
            start_write_collect_count: 0,
            next_write_collect_count: 0,
            collect_count: 0,
            collect_memory_pools: 0,
            collect_write_data: SigExpanderEntryWriteDataId::NONE,
            cache_stat: 0,
            slot_linker: SigExpanderSlotItemId::NONE,
            reader_linker: SigExpanderCacheReaderId::NONE,
            reader_sync_mutex: 0,
            context: SignatureSatisfiableExpanderCacheContext::default(),
            config: 0,
        }
    }
}

impl SignatureSatisfiableExpanderCache {
    /// Port of `CSignatureSatisfiableExpanderCache::CSignatureSatisfiableExpanderCache`.
    /// KONCLUDE-PORT-NOTE[memory-pool][threading]: the C++ ctor allocates the four CCACHING
    /// containers from the context pool, reads config thresholds, and `startThread`s the
    /// writer thread. The main containers are typed Rust maps/sets; config reads
    /// + thread start remain W6-DEFER[api]/[threading].
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `getCacheStatistics` (opaque `CCacheStatistics` handle).
    pub fn get_cache_statistics(&self) -> Cint64 {
        self.cache_stat
    }

    /// Port of `createCacheReader`.
    pub fn create_cache_reader(
        &mut self,
        cache_context: &mut CacheContext,
    ) -> SigExpanderCacheReaderId {
        // KONCLUDE-PORT-NOTE[threading]: mReaderSyncMutex lock/unlock — single-threaded inline.
        let mut reader = SignatureSatisfiableExpanderCacheReader::new();
        reader.set_next(self.reader_linker);
        let reader = cache_context.alloc_sig_expander_cache_reader(reader);
        self.reader_linker = reader;
        reader
    }

    /// Port of `createCacheWriter`.
    pub fn create_cache_writer(&mut self) -> SignatureSatisfiableExpanderCacheWriter {
        // KONCLUDE-PORT-NOTE[ownership]: the C++ writer stores `this`; Rust call
        // sites pass the owning cache into the forwarding method explicitly.
        SignatureSatisfiableExpanderCacheWriter::new_with_cache(0)
    }

    /// Port of protected `isCachingDataExpandable`.
    /// KONCLUDE-PORT-NOTE[api]: `context` is the by-value `self.context`;
    /// `cacheValueList`, `mIncompatibleSigSet`, and the tag hash are typed local
    /// containers in this staged single-threaded port.
    fn is_caching_data_expandable(
        &self,
        entry: SigExpanderCacheEntryId,
        signature: Cint64,
        cache_value_list: SigExpanderCacheValueListId,
        cache_context: &mut CacheContext,
    ) -> bool {
        let incompatible_or_multiple_expanded = self.incompatible_sig_set.contains(&signature)
            || (entry.is_some()
                && cache_context
                    .sig_expander_cache_entry(entry)
                    .has_multiple_expanded());
        let mut prev_count = if entry.is_some() {
            cache_context
                .sig_expander_cache_entry(entry)
                .get_expander_cache_value_count()
        } else {
            0
        };
        if incompatible_or_multiple_expanded {
            while prev_count > 0
                && cache_value_list.is_some()
                && !cache_context
                    .sig_expander_cache_value_list(cache_value_list)
                    .is_empty()
            {
                prev_count -= 1;
                let cache_value = cache_context
                    .sig_expander_cache_value_list_mut(cache_value_list)
                    .take_first()
                    .unwrap();
                let tag = Self::cache_value_tag(cache_value);
                let cont_cache_value = cache_context
                    .sig_expander_cache_entry(entry)
                    .get_tag_expander_cache_value_hash()
                    .get(&tag)
                    .copied()
                    .unwrap_or(ExpanderCacheValueLinkerId::NONE);
                if cont_cache_value.is_none()
                    || cache_context
                        .expander_cache_value_linker(cont_cache_value)
                        .get_cache_value()
                        != cache_value
                {
                    return false;
                }
            }
        } else {
            while prev_count > 0
                && cache_value_list.is_some()
                && !cache_context
                    .sig_expander_cache_value_list(cache_value_list)
                    .is_empty()
            {
                prev_count -= 1;
                cache_context
                    .sig_expander_cache_value_list_mut(cache_value_list)
                    .take_first();
            }
        }
        true
    }

    fn cache_value_tag(cache_value: CCacheValue) -> Cint64 {
        cache_value.get_tag()
    }

    fn append_expander_linker_to_chain(
        first_last: &mut (ExpanderCacheValueLinkerId, ExpanderCacheValueLinkerId),
        linker: ExpanderCacheValueLinkerId,
        cache_context: &mut CacheContext,
    ) {
        if first_last.0.is_some() {
            cache_context
                .expander_cache_value_linker_mut(first_last.1)
                .set_next(linker);
            first_last.1 = linker;
        } else {
            first_last.0 = linker;
            first_last.1 = linker;
        }
    }

    fn append_expander_chain_to_entry(
        entry: SigExpanderCacheEntryId,
        linker: ExpanderCacheValueLinkerId,
        cache_context: &mut CacheContext,
    ) {
        if linker.is_none() {
            return;
        }
        let mut add_count: Cint64 = 0;
        let mut linker_it = linker;
        while linker_it.is_some() {
            add_count += 1;
            linker_it = cache_context
                .expander_cache_value_linker(linker_it)
                .get_next();
        }

        let old_head = cache_context
            .sig_expander_cache_entry(entry)
            .get_expander_cache_value_linker();
        if old_head.is_none() {
            let entry_mut = cache_context.sig_expander_cache_entry_mut(entry);
            entry_mut.det_expand_value_linker = linker;
            entry_mut.det_expand_count += add_count;
            return;
        }

        let mut tail = old_head;
        while cache_context.expander_cache_value_linker(tail).has_next() {
            tail = cache_context.expander_cache_value_linker(tail).get_next();
        }
        cache_context
            .expander_cache_value_linker_mut(tail)
            .set_next(linker);
        cache_context
            .sig_expander_cache_entry_mut(entry)
            .det_expand_count += add_count;
    }

    /// Port of the void overload of `writeExpanderCachingData` (entry-based).
    fn write_expander_caching_data_entry(
        &mut self,
        entry: SigExpanderCacheEntryId,
        extending: bool,
        cache_value_list: SigExpanderCacheValueListId,
        dep_hash: SigExpanderDepHashId,
        cache_context: &mut CacheContext,
    ) {
        let mut new_tag_hash = cache_context
            .sig_expander_cache_entry(entry)
            .get_tag_expander_cache_value_hash()
            .clone();
        let mut first_last = (
            ExpanderCacheValueLinkerId::NONE,
            ExpanderCacheValueLinkerId::NONE,
        );
        let mut tag_cache_value_hash: HashMap<Cint64, CCacheValue> = HashMap::new();
        let values = if cache_value_list.is_some() {
            cache_context
                .sig_expander_cache_value_list(cache_value_list)
                .cache_values
                .clone()
        } else {
            Vec::new()
        };

        for (index, cache_value) in values.iter().copied().enumerate() {
            let tag = Self::cache_value_tag(cache_value);
            if !new_tag_hash.contains_key(&tag) {
                let mut exp_cache_value = ExpanderCacheValueLinker::new();
                exp_cache_value.set_cache_value(cache_value);
                let exp_cache_value =
                    cache_context.alloc_expander_cache_value_linker(exp_cache_value);

                if dep_hash.is_some() {
                    let dep_tags: Vec<Cint64> = cache_context
                        .sig_expander_dep_hash(dep_hash)
                        .dep_tags_for(tag)
                        .collect();
                    for dep_tag in dep_tags {
                        let mut dep_exp_cache_value_linker = new_tag_hash
                            .get(&dep_tag)
                            .copied()
                            .unwrap_or(ExpanderCacheValueLinkerId::NONE);
                        if dep_exp_cache_value_linker.is_none() {
                            if tag_cache_value_hash.is_empty() {
                                for next_cache_value in values.iter().skip(index + 1).copied() {
                                    tag_cache_value_hash.insert(
                                        Self::cache_value_tag(next_cache_value),
                                        next_cache_value,
                                    );
                                }
                            }
                            let dep_cache_value = tag_cache_value_hash
                                .get(&dep_tag)
                                .copied()
                                .unwrap_or_else(CacheValue::new);
                            self.add_expander_caching_data(
                                dep_cache_value,
                                &mut new_tag_hash,
                                dep_hash,
                                &tag_cache_value_hash,
                                &mut first_last,
                                cache_context,
                            );
                            dep_exp_cache_value_linker = new_tag_hash
                                .get(&dep_tag)
                                .copied()
                                .unwrap_or(ExpanderCacheValueLinkerId::NONE);
                        }
                        cache_context
                            .expander_cache_value_linker_mut(exp_cache_value)
                            .add_expander_dependency(dep_exp_cache_value_linker);
                    }
                }

                new_tag_hash.insert(tag, exp_cache_value);
                Self::append_expander_linker_to_chain(
                    &mut first_last,
                    exp_cache_value,
                    cache_context,
                );
            }
        }

        cache_context
            .sig_expander_cache_entry_mut(entry)
            .set_tag_expander_cache_value_hash(new_tag_hash);
        Self::append_expander_chain_to_entry(entry, first_last.0, cache_context);
        let _ = extending;
    }

    /// Port of protected `addExpanderCachingData` (the recursive dependency builder).
    fn add_expander_caching_data(
        &mut self,
        cache_value: CCacheValue,
        new_tag_hash: &mut SigExpanderTagHash,
        dep_hash: SigExpanderDepHashId,
        tag_cache_value_hash: &HashMap<Cint64, CCacheValue>,
        first_last: &mut (ExpanderCacheValueLinkerId, ExpanderCacheValueLinkerId),
        cache_context: &mut CacheContext,
    ) {
        let tag = Self::cache_value_tag(cache_value);
        if !new_tag_hash.contains_key(&tag) {
            let mut exp_cache_value = ExpanderCacheValueLinker::new();
            exp_cache_value.set_cache_value(cache_value);
            let exp_cache_value = cache_context.alloc_expander_cache_value_linker(exp_cache_value);

            if dep_hash.is_some() {
                let dep_tags: Vec<Cint64> = cache_context
                    .sig_expander_dep_hash(dep_hash)
                    .dep_tags_for(tag)
                    .collect();
                for dep_tag in dep_tags {
                    let mut dep_exp_cache_value_linker = new_tag_hash
                        .get(&dep_tag)
                        .copied()
                        .unwrap_or(ExpanderCacheValueLinkerId::NONE);
                    if dep_exp_cache_value_linker.is_none() {
                        let dep_cache_value = tag_cache_value_hash
                            .get(&dep_tag)
                            .copied()
                            .unwrap_or_else(CacheValue::new);
                        self.add_expander_caching_data(
                            dep_cache_value,
                            new_tag_hash,
                            dep_hash,
                            tag_cache_value_hash,
                            first_last,
                            cache_context,
                        );
                        dep_exp_cache_value_linker = new_tag_hash
                            .get(&dep_tag)
                            .copied()
                            .unwrap_or(ExpanderCacheValueLinkerId::NONE);
                    }
                    cache_context
                        .expander_cache_value_linker_mut(exp_cache_value)
                        .add_expander_dependency(dep_exp_cache_value_linker);
                }
            }

            new_tag_hash.insert(tag, exp_cache_value);
            Self::append_expander_linker_to_chain(first_last, exp_cache_value, cache_context);
        }
    }

    /// Port of the bool overload of `writeExpanderCachingData` (signature-based).
    fn write_expander_caching_data_sig(
        &mut self,
        prev_signature: Cint64,
        new_signature: Cint64,
        cache_value_list: SigExpanderCacheValueListId,
        dep_hash: SigExpanderDepHashId,
        cache_context: &mut CacheContext,
    ) -> bool {
        if self.can_create_cache_entry_for_signature(new_signature) {
            if !self.sig_item_hash.contains_key(&new_signature) {
                let mut entry = SigExpanderCacheEntryId::NONE;
                if prev_signature != 0 {
                    let prev_sig_item = self
                        .sig_item_hash
                        .get(&prev_signature)
                        .copied()
                        .unwrap_or(SigExpanderRedirectionItemId::NONE);
                    if prev_sig_item.is_some() {
                        entry = cache_context
                            .sig_expander_redirection_item(prev_sig_item)
                            .get_cache_entry();
                        if !self.is_caching_data_expandable(
                            entry,
                            prev_signature,
                            cache_value_list,
                            cache_context,
                        ) {
                            self.incompatible_sig_set.insert(prev_signature);
                            return false;
                        }
                        if self.already_exp_sig_set.contains(&prev_signature) {
                            cache_context
                                .sig_expander_cache_entry_mut(entry)
                                .set_multiple_expanded(true);
                        }
                    }
                }

                if entry.is_none() {
                    // W6-DEFER[memory-pool]: allocateAndConstruct with CSignatureSatisfiableExpanderCacheContext.
                    entry = cache_context.alloc_sig_expander_cache_entry(
                        SignatureSatisfiableExpanderCacheEntry::new(),
                    );
                }

                self.write_expander_caching_data_entry(
                    entry,
                    prev_signature != 0,
                    cache_value_list,
                    dep_hash,
                    cache_context,
                );
                // W6-DEFER[memory-pool]: allocate redirection item with CObjectAllocator.
                let mut sig_item = SignatureSatisfiableExpanderCacheRedirectionItem::new();
                sig_item.init_redirection_item(
                    entry,
                    new_signature,
                    cache_context
                        .sig_expander_cache_entry(entry)
                        .get_expander_cache_value_count(),
                );
                let sig_item = cache_context.alloc_sig_expander_redirection_item(sig_item);
                self.sig_item_hash.insert(new_signature, sig_item);
                self.already_exp_sig_set.insert(prev_signature);
                return true;
            } else {
                self.incompatible_sig_set.insert(new_signature);
            }
        }
        false
    }

    /// Port of protected `writeSatisfiableBranchedCachingData`.
    fn write_satisfiable_branched_caching_data(
        &mut self,
        signature: Cint64,
        cache_value_list: SigExpanderCacheValueListId,
        branched_value_list: SigExpanderCacheValueListId,
        cache_context: &mut CacheContext,
    ) -> bool {
        let s_sig_item = self
            .sig_item_hash
            .get(&signature)
            .copied()
            .unwrap_or(SigExpanderRedirectionItemId::NONE);
        if s_sig_item.is_some() {
            let entry = cache_context
                .sig_expander_redirection_item(s_sig_item)
                .get_cache_entry();

            if self.is_caching_data_expandable(entry, signature, cache_value_list, cache_context) {
                let branched_empty = branched_value_list.is_none()
                    || cache_context
                        .sig_expander_cache_value_list(branched_value_list)
                        .is_empty();
                if branched_empty {
                    cache_context
                        .sig_expander_cache_entry_mut(entry)
                        .set_satisfiable_without_branched_concepts(true);
                } else {
                    let mut exp_branch = ExpanderBranchedLinker::new();
                    for cache_value in cache_context
                        .sig_expander_cache_value_list(branched_value_list)
                        .iter()
                    {
                        exp_branch.append_cache_value(*cache_value);
                    }
                    let exp_branch = cache_context.alloc_expander_branched_linker(exp_branch);
                    let old_head = cache_context
                        .sig_expander_cache_entry(entry)
                        .get_expander_branched_linker();
                    if old_head.is_some() {
                        let mut tail = exp_branch;
                        while cache_context.expander_branched_linker(tail).has_next() {
                            tail = cache_context.expander_branched_linker(tail).get_next();
                        }
                        cache_context
                            .expander_branched_linker_mut(tail)
                            .set_next(old_head);
                    }
                    cache_context
                        .sig_expander_cache_entry_mut(entry)
                        .expand_branched_linker = exp_branch;
                }
                cache_context
                    .sig_expander_cache_entry_mut(entry)
                    .set_satisfiable(true);
                return true;
            }
        }
        false
    }

    /// Port of protected `createReaderSlotUpdate`.
    fn create_reader_slot_update(&mut self, cache_context: &mut CacheContext) {
        // W6-DEFER[memory-pool]: slot = allocateWithMemoryPool CSignatureSatisfiableExpanderCacheSlotItem;
        let mut slot = SignatureSatisfiableExpanderCacheSlotItem::new();
        slot.set_signature_item_hash(self.sig_item_hash.clone());
        let slot = cache_context.alloc_sig_expander_slot_item(slot);

        if self.slot_linker.is_some() {
            let mut tail = self.slot_linker;
            while cache_context.sig_expander_slot_item(tail).has_next() {
                tail = cache_context.sig_expander_slot_item(tail).get_next();
            }
            cache_context
                .sig_expander_slot_item_mut(tail)
                .set_next(slot);
        } else {
            self.slot_linker = slot;
        }

        let mut reader_linker_it = self.reader_linker;
        while reader_linker_it.is_some() {
            cache_context.sig_expander_slot_item_mut(slot).inc_reader();
            let next_reader = cache_context
                .sig_expander_cache_reader(reader_linker_it)
                .get_next();
            let prev_slot = {
                let reader = cache_context.sig_expander_cache_reader_mut(reader_linker_it);
                let prev_slot = reader.updated_slot;
                reader.updated_slot = slot;
                prev_slot
            };
            if prev_slot.is_some() {
                cache_context
                    .sig_expander_slot_item_mut(prev_slot)
                    .dec_reader();
            }
            reader_linker_it = next_reader;
        }
    }

    /// Port of protected `cleanUnusedSlots`.
    fn clean_unused_slots(&mut self, cache_context: &mut CacheContext) {
        let mut slot_linker_it = self.slot_linker;
        let mut last_slot_linker = SigExpanderSlotItemId::NONE;
        while slot_linker_it.is_some() {
            let tmp_slot_linker = if !cache_context
                .sig_expander_slot_item(slot_linker_it)
                .has_cache_readers()
            {
                slot_linker_it
            } else {
                SigExpanderSlotItemId::NONE
            };
            let next_slot_linker = cache_context
                .sig_expander_slot_item(slot_linker_it)
                .get_next();
            if tmp_slot_linker.is_some() {
                if last_slot_linker.is_none() {
                    self.slot_linker = next_slot_linker;
                } else {
                    cache_context
                        .sig_expander_slot_item_mut(last_slot_linker)
                        .set_next(next_slot_linker);
                }
                // W6-DEFER[memory-pool]: memMan->releaseTemporaryMemoryPools(tmpSlotLinker->getMemoryPools());
            } else {
                last_slot_linker = slot_linker_it;
            }
            slot_linker_it = next_slot_linker;
        }
    }

    fn drain_write_data_chain(
        &mut self,
        write_data: SigExpanderEntryWriteDataId,
        cache_context: &mut CacheContext,
    ) -> (bool, bool, bool) {
        let mut data_linker_it = write_data;
        let mut all_caching_success = true;
        let mut one_caching_success = false;
        let mut one_caching_exp_success = false;
        while data_linker_it.is_some() {
            let (kind, next) = {
                let data = cache_context.sig_expander_entry_write_data(data_linker_it);
                (
                    match &data.kind {
                        SigExpanderEntryWriteDataKind::Base => SigExpanderEntryWriteDataKind::Base,
                        SigExpanderEntryWriteDataKind::Expand {
                            prev_signature,
                            new_signature,
                            cache_value_list,
                            dep_hash,
                        } => SigExpanderEntryWriteDataKind::Expand {
                            prev_signature: *prev_signature,
                            new_signature: *new_signature,
                            cache_value_list: *cache_value_list,
                            dep_hash: *dep_hash,
                        },
                        SigExpanderEntryWriteDataKind::SatisfiableBranch {
                            signature,
                            cache_value_list,
                            branched_value_list,
                        } => SigExpanderEntryWriteDataKind::SatisfiableBranch {
                            signature: *signature,
                            cache_value_list: *cache_value_list,
                            branched_value_list: *branched_value_list,
                        },
                    },
                    data.get_next(),
                )
            };

            let (cached, expansion_cached) = match kind {
                SigExpanderEntryWriteDataKind::Base => (false, false),
                SigExpanderEntryWriteDataKind::Expand {
                    prev_signature,
                    new_signature,
                    cache_value_list,
                    dep_hash,
                } => {
                    let cached = self.write_expander_caching_data_sig(
                        prev_signature,
                        new_signature,
                        cache_value_list,
                        dep_hash,
                        cache_context,
                    );
                    (cached, cached)
                }
                SigExpanderEntryWriteDataKind::SatisfiableBranch {
                    signature,
                    cache_value_list,
                    branched_value_list,
                } => (
                    self.write_satisfiable_branched_caching_data(
                        signature,
                        cache_value_list,
                        branched_value_list,
                        cache_context,
                    ),
                    false,
                ),
            };
            all_caching_success &= cached;
            one_caching_success |= cached;
            one_caching_exp_success |= expansion_cached;
            data_linker_it = next;
        }
        (
            all_caching_success,
            one_caching_success,
            one_caching_exp_success,
        )
    }

    /// Port of `writeCachedData` (facade entry; staged single-threaded inline drain).
    pub fn write_cached_data(
        &mut self,
        write_data: SigExpanderEntryWriteDataId,
        memory_pools: Cint64,
        cache_context: &mut CacheContext,
    ) -> &mut Self {
        // KONCLUDE-PORT-NOTE[threading]: the shipped C++ default posts a CWriteCachedDataEvent to the
        // writer thread; the staged single-threaded port drains inline (== the DIRECT_WRITING branch).
        let (all_caching_success, one_caching_success, one_caching_exp_success) =
            self.drain_write_data_chain(write_data, cache_context);

        if one_caching_exp_success {
            self.create_reader_slot_update(cache_context);
            self.clean_unused_slots(cache_context);
        }
        let _ = (all_caching_success, one_caching_success, memory_pools);
        self
    }

    /// Port of `writeExpandCached` (facade entry; staged single-threaded inline drain).
    pub fn write_expand_cached(
        &mut self,
        prev_signature: Cint64,
        new_signature: Cint64,
        cache_value_list: SigExpanderCacheValueListId,
        dep_hash: SigExpanderDepHashId,
        memory_pools: Cint64,
        cache_context: &mut CacheContext,
    ) -> &mut Self {
        // KONCLUDE-PORT-NOTE[threading]: shipped default posts CWriteExpandCachedEvent; inline here.
        if self.write_expander_caching_data_sig(
            prev_signature,
            new_signature,
            cache_value_list,
            dep_hash,
            cache_context,
        ) {
            self.create_reader_slot_update(cache_context);
            self.clean_unused_slots(cache_context);
        }
        let _ = memory_pools;
        self
    }

    /// Port of `writeSatisfiableBranchCached` (facade entry; staged single-threaded inline drain).
    pub fn write_satisfiable_branch_cached(
        &mut self,
        signature: Cint64,
        cache_value_list: SigExpanderCacheValueListId,
        branched_list: SigExpanderCacheValueListId,
        memory_pools: Cint64,
        cache_context: &mut CacheContext,
    ) -> &mut Self {
        // KONCLUDE-PORT-NOTE[threading]: shipped default posts CWriteSatisfiableBranchCachedEvent; inline here.
        self.write_satisfiable_branched_caching_data(
            signature,
            cache_value_list,
            branched_list,
            cache_context,
        );
        let _ = memory_pools;
        self
    }

    /// Typed Rust event drain for
    /// `CSignatureSatisfiableExpanderCache::processCustomsEvents`.
    ///
    /// Konclude receives one of the F8 `CWrite*Event` subclasses, reads its
    /// payload, calls the matching cache-write body, and releases the memory
    /// pools. The F8 Rust port collapses those event subclasses into
    /// `CacheEvent`, so this method is the live typed branch implementation.
    pub fn process_customs_cache_event(
        &mut self,
        event: &CacheEvent,
        cache_context: &mut CacheContext,
    ) -> bool {
        if event.event_type() == EVENT_WRITE_EXPAND_CACHED_ENTRY {
            let prev_signature = event.get_prev_signature().unwrap_or(0);
            let new_signature = event.get_new_signature().unwrap_or(0);
            let cache_value_list = event
                .get_cache_value_list()
                .unwrap_or(SigExpanderCacheValueListId::NONE);
            let dep_hash = event.get_dep_hash().unwrap_or(SigExpanderDepHashId::NONE);
            let memory_pools = event.get_memory_pools().unwrap_or(INVALID);

            if self.write_expander_caching_data_sig(
                prev_signature,
                new_signature,
                cache_value_list,
                dep_hash,
                cache_context,
            ) {
                self.create_reader_slot_update(cache_context);
                self.clean_unused_slots(cache_context);
            }

            // W6-DEFER[memory-pool]: releaseTemporaryMemoryPools(memoryPools)
            let _ = memory_pools;
            return true;
        } else if event.event_type() == EVENT_WRITE_SATISFIABLE_BRANCH_CACHED_ENTRY {
            let signature = event.get_signature().unwrap_or(0);
            let cache_value_list = event
                .get_cache_value_list()
                .unwrap_or(SigExpanderCacheValueListId::NONE);
            let branched_value_list = event
                .get_branched_value_list()
                .unwrap_or(SigExpanderCacheValueListId::NONE);
            let memory_pools = event.get_memory_pools().unwrap_or(INVALID);

            self.write_satisfiable_branched_caching_data(
                signature,
                cache_value_list,
                branched_value_list,
                cache_context,
            );

            // W6-DEFER[memory-pool]: releaseTemporaryMemoryPools(memoryPools)
            let _ = memory_pools;
            return true;
        } else if event.event_type() == EVENT_WRITE_CACHED_DATA_ENTRY {
            let memory_pools = event.get_memory_pools().unwrap_or(INVALID);
            let new_write_data = event
                .get_cache_entry_write_data()
                .unwrap_or(SigExpanderEntryWriteDataId::NONE);
            let data_write_count = if new_write_data.is_some() {
                cache_context
                    .sig_expander_entry_write_data(new_write_data)
                    .get_count(cache_context)
            } else {
                0
            };

            self.collect_count += data_write_count;
            // KONCLUDE-PORT-NOTE[memory-pool]: the C++ memory-pool chain append is
            // opaque in Rust; keep the newest pool handle for later release.
            self.collect_memory_pools = memory_pools;
            if new_write_data.is_some() {
                let old_collect_write_data = self.collect_write_data;
                let mut tail = new_write_data;
                while cache_context
                    .sig_expander_entry_write_data(tail)
                    .get_next()
                    .is_some()
                {
                    tail = cache_context.sig_expander_entry_write_data(tail).get_next();
                }
                cache_context
                    .sig_expander_entry_write_data_mut(tail)
                    .set_next(old_collect_write_data);
                self.collect_write_data = new_write_data;
            }

            if self.collect_count >= self.next_write_collect_count {
                if self.write_data_count > self.start_write_collect_count {
                    self.next_write_collect_count += 1;
                }

                let (all_caching_success, one_caching_success, one_caching_exp_success) =
                    self.drain_write_data_chain(self.collect_write_data, cache_context);

                if one_caching_exp_success {
                    self.create_reader_slot_update(cache_context);
                    self.clean_unused_slots(cache_context);
                }

                // W6-DEFER[memory-pool]: releaseTemporaryMemoryPools(mCollectMemoryPools)
                // W6-DEFER[api]: mCacheStat.setMemoryConsumption(mContext.getMemoryConsumption())

                self.collect_write_data = SigExpanderEntryWriteDataId::NONE;
                self.collect_memory_pools = 0;
                self.collect_count = 0;
                let _ = (all_caching_success, one_caching_success);
            }

            self.write_data_count += 1;
            return true;
        }
        false
    }

    /// Opaque-id compatibility wrapper for virtual `processCustomsEvents`.
    /// The faithful typed event branch is live in `process_customs_cache_event`.
    fn process_customs_events(
        &mut self,
        type_: Cint64,
        event: Cint64,
        cache_context: &mut CacheContext,
    ) -> bool {
        // W6-DEFER[threading]: if (CThread::processCustomsEvents(type,event)) return true;
        if type_ == super::value::event::WRITE_EXPAND_CACHED_ENTRY {
            // W6-DEFER[api]: extract prevSignature/newSignature/cacheValueList/depHash/memoryPools from event.
            if self.write_expander_caching_data_sig(
                0,
                0,
                SigExpanderCacheValueListId::NONE,
                SigExpanderDepHashId::NONE,
                cache_context,
            ) {
                self.create_reader_slot_update(cache_context);
                self.clean_unused_slots(cache_context);
            }
            // W6-DEFER[memory-pool]: mContext.getMemoryPoolAllocationManager()->releaseTemporaryMemoryPools(memoryPools);
            return true;
        } else if type_ == super::value::event::WRITE_SATISFIABLE_BRANCH_CACHED_ENTRY {
            // W6-DEFER[api]: extract signature/cacheValueList/branchedValueList/memoryPools from event.
            self.write_satisfiable_branched_caching_data(
                0,
                SigExpanderCacheValueListId::NONE,
                SigExpanderCacheValueListId::NONE,
                cache_context,
            );
            // W6-DEFER[memory-pool]: releaseTemporaryMemoryPools(memoryPools);
            return true;
        } else if type_ == super::value::event::WRITE_CACHED_DATA_ENTRY {
            // KONCLUDE-PORT-NOTE[api]: the collect-and-batch path: accumulate write-data + pools into
            // mCollectWriteData/mCollectMemoryPools, and once mCollectCount reaches mNextWriteCollectCount,
            // drain the whole collected chain (dispatching like writeCachedData), then release pools and
            // reset the collect buffer.
            // W6-DEFER[api]: dataWriteCount = newWriteData->getCount();
            let data_write_count: Cint64 = 0; // W6-DEFER[api]
            self.collect_count += data_write_count;
            // W6-DEFER[api]: mCollectMemoryPools = memoryPools->append(mCollectMemoryPools);
            // W6-DEFER[api]: mCollectWriteData = newWriteData->append(mCollectWriteData);

            if self.collect_count >= self.next_write_collect_count {
                if self.write_data_count > self.start_write_collect_count {
                    self.next_write_collect_count += 1;
                }

                let (all_caching_success, one_caching_success, one_caching_exp_success) =
                    self.drain_write_data_chain(self.collect_write_data, cache_context);

                if one_caching_exp_success {
                    self.create_reader_slot_update(cache_context);
                    self.clean_unused_slots(cache_context);
                }

                // W6-DEFER[memory-pool]: mContext.releaseTemporaryMemoryPools(mCollectMemoryPools);
                // W6-DEFER[api]: mCacheStat.setMemoryConsumption(mContext.getMemoryConsumption());

                self.collect_write_data = SigExpanderEntryWriteDataId::NONE;
                self.collect_memory_pools = 0;
                self.collect_count = 0;
                let _ = (all_caching_success, one_caching_success);
            }

            self.write_data_count += 1;
            return true;
        }
        let _ = event;
        false
    }

    /// Port of protected `getRequiredSignatureReferCountForNextCacheEntryCreation`.
    fn get_required_signature_refer_count_for_next_cache_entry_creation(&mut self) -> Cint64 {
        // KONCLUDE-PORT-NOTE[api]: C++ passes the context pointer; here it is the by-value self.context.
        let mem_consumption = self.context.get_memory_consumption();
        if mem_consumption >= self.next_memory_level_required_signature_ref_count {
            self.next_cache_entry_required_signature_ref_count +=
                self.next_cache_entry_required_signature_reference_count_increase;
            self.next_memory_level_required_signature_ref_count +=
                self.next_memory_level_increase_for_required_signature_reference_count;
        }
        self.next_cache_entry_required_signature_ref_count
    }

    /// Port of protected `canCreateCacheEntryForSignature`.
    fn can_create_cache_entry_for_signature(&mut self, signature: Cint64) -> bool {
        let ref_count = self.signature_refer_count_set.entry(signature).or_insert(0);
        *ref_count += 1;
        let ref_count = *ref_count;
        if ref_count >= self.get_required_signature_refer_count_for_next_cache_entry_creation() {
            return true;
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use super::super::value::CacheValueIdentifier;
    use super::*;

    fn cv(tag: Cint64) -> CCacheValue {
        CacheValue::new_value(tag, 0, CacheValueIdentifier::CacheValConceptOntologyTag)
    }

    fn alloc_value_linker(
        ctx: &mut CacheContext,
        value: Cint64,
        next: ExpanderCacheValueLinkerId,
    ) -> ExpanderCacheValueLinkerId {
        let mut linker = ExpanderCacheValueLinker::new();
        linker.set_cache_value(cv(value));
        linker.set_next(next);
        ctx.alloc_expander_cache_value_linker(linker)
    }

    fn alloc_branched_linker(
        ctx: &mut CacheContext,
        values: &[Cint64],
        next: ExpanderBranchedLinkerId,
    ) -> ExpanderBranchedLinkerId {
        let mut linker = ExpanderBranchedLinker::new();
        for value in values {
            linker.append_cache_value(cv(*value));
        }
        linker.set_next(next);
        ctx.alloc_expander_branched_linker(linker)
    }

    fn alloc_cache_value_set(
        ctx: &mut CacheContext,
        values: &[Cint64],
    ) -> SigExpanderCacheValueSetId {
        let mut set = SignatureSatisfiableExpanderCacheValueSet::new();
        for value in values {
            set.insert(cv(*value));
        }
        ctx.alloc_sig_expander_cache_value_set(set)
    }

    fn alloc_cache_value_list(
        ctx: &mut CacheContext,
        values: &[Cint64],
    ) -> SigExpanderCacheValueListId {
        let mut list = SignatureSatisfiableExpanderCacheValueList::new();
        for value in values {
            list.append(cv(*value));
        }
        ctx.alloc_sig_expander_cache_value_list(list)
    }

    fn alloc_dep_hash(ctx: &mut CacheContext, deps: &[(Cint64, Cint64)]) -> SigExpanderDepHashId {
        let mut dep_hash = SignatureSatisfiableExpanderDepHash::new();
        for (tag, dep_tag) in deps {
            dep_hash.insert(*tag, *dep_tag);
        }
        ctx.alloc_sig_expander_dep_hash(dep_hash)
    }

    fn alloc_slot_with_readers(ctx: &mut CacheContext, readers: Cint64) -> SigExpanderSlotItemId {
        let mut slot = SignatureSatisfiableExpanderCacheSlotItem::new();
        slot.inc_reader_count(readers);
        ctx.alloc_sig_expander_slot_item(slot)
    }

    fn alloc_slot_with_signature_entry(
        ctx: &mut CacheContext,
        signature: Cint64,
        entry: SigExpanderCacheEntryId,
    ) -> SigExpanderSlotItemId {
        let mut redirection = SignatureSatisfiableExpanderCacheRedirectionItem::new();
        redirection.init_redirection_item(entry, signature, 0);
        let redirection = ctx.alloc_sig_expander_redirection_item(redirection);
        let mut slot = SignatureSatisfiableExpanderCacheSlotItem::new();
        let mut hash = HashMap::new();
        hash.insert(signature, redirection);
        slot.set_signature_item_hash(hash);
        slot.inc_reader();
        ctx.alloc_sig_expander_slot_item(slot)
    }

    fn alloc_slot_with_hasher_entry(
        ctx: &mut CacheContext,
        set_values: &[Cint64],
        entry: SigExpanderCacheEntryId,
    ) -> (SigExpanderSlotItemId, SigExpanderCacheValueSetId) {
        let cache_value_set = alloc_cache_value_set(ctx, set_values);
        let mut redirection = SignatureSatisfiableExpanderCacheRedirectionItem::new();
        redirection.init_redirection_item(entry, 0, set_values.len() as Cint64);
        let redirection = ctx.alloc_sig_expander_redirection_item(redirection);
        let hasher = SignatureSatisfiableExpanderCacheHasher::new_from_set(cache_value_set, ctx);
        let mut slot = SignatureSatisfiableExpanderCacheSlotItem::new();
        slot.set_hasher_item_hash(vec![(hasher, redirection)]);
        slot.inc_reader();
        let slot = ctx.alloc_sig_expander_slot_item(slot);
        (slot, cache_value_set)
    }

    fn alloc_write_data(
        ctx: &mut CacheContext,
        next: SigExpanderEntryWriteDataId,
    ) -> SigExpanderEntryWriteDataId {
        let mut data = SignatureSatisfiableExpanderCacheEntryWriteData::new();
        data.set_next(next);
        ctx.alloc_sig_expander_entry_write_data(data)
    }

    fn qhash(value: Cint64) -> Cint64 {
        cv(value).q_hash() as Cint64
    }

    #[test]
    fn sig_expander_entry_appends_cache_value_linker_chain_with_context() {
        let mut ctx = CacheContext::new();
        let second = alloc_value_linker(&mut ctx, 20, ExpanderCacheValueLinkerId::NONE);
        let first = alloc_value_linker(&mut ctx, 10, second);
        let fourth = alloc_value_linker(&mut ctx, 40, ExpanderCacheValueLinkerId::NONE);
        let third = alloc_value_linker(&mut ctx, 30, fourth);
        let mut entry = SignatureSatisfiableExpanderCacheEntry::new();

        entry.append_expander_cache_value_linker(first, &mut ctx);
        entry.append_expander_cache_value_linker(third, &mut ctx);

        assert_eq!(entry.get_expander_cache_value_linker(), first);
        assert_eq!(entry.get_expander_cache_value_count(), 4);
        assert_eq!(ctx.expander_cache_value_linker(first).get_next(), second);
        assert_eq!(ctx.expander_cache_value_linker(second).get_next(), third);
        assert_eq!(ctx.expander_cache_value_linker(third).get_next(), fourth);
        assert_eq!(
            ctx.expander_cache_value_linker(fourth).get_next(),
            ExpanderCacheValueLinkerId::NONE
        );
    }

    #[test]
    fn sig_expander_entry_prepends_branched_linker_chain_with_context() {
        let mut ctx = CacheContext::new();
        let old_tail = alloc_branched_linker(&mut ctx, &[30], ExpanderBranchedLinkerId::NONE);
        let old_head = alloc_branched_linker(&mut ctx, &[20, 21], old_tail);
        let new_tail = alloc_branched_linker(&mut ctx, &[11], ExpanderBranchedLinkerId::NONE);
        let new_head = alloc_branched_linker(&mut ctx, &[10], new_tail);
        let mut entry = SignatureSatisfiableExpanderCacheEntry::new();

        entry.append_expander_branched_linker(old_head, &mut ctx);
        entry.append_expander_branched_linker(new_head, &mut ctx);

        assert_eq!(entry.get_expander_branched_linker(), new_head);
        assert_eq!(ctx.expander_branched_linker(new_head).get_next(), new_tail);
        assert_eq!(ctx.expander_branched_linker(new_tail).get_next(), old_head);
        assert_eq!(ctx.expander_branched_linker(old_head).get_next(), old_tail);
        assert_eq!(
            ctx.expander_branched_linker(old_tail).get_next(),
            ExpanderBranchedLinkerId::NONE
        );
        assert_eq!(
            ctx.expander_branched_linker(old_head)
                .get_cache_value_list(),
            &vec![cv(20), cv(21)]
        );
    }

    #[test]
    fn sig_expander_reader_update_slot_releases_previous_pending_slot_with_context() {
        let mut ctx = CacheContext::new();
        let previous = alloc_slot_with_readers(&mut ctx, 2);
        let replacement = alloc_slot_with_readers(&mut ctx, 1);
        let mut reader = SignatureSatisfiableExpanderCacheReader::new();
        reader.updated_slot = previous;

        reader.update_slot(replacement, &mut ctx);

        assert_eq!(reader.updated_slot, replacement);
        assert_eq!(ctx.sig_expander_slot_item(previous).reader_sharing_count, 1);
        assert!(ctx.sig_expander_slot_item(previous).has_cache_readers());
        assert_eq!(
            ctx.sig_expander_slot_item(replacement).reader_sharing_count,
            1
        );
    }

    #[test]
    fn sig_expander_reader_switches_to_updated_slot_and_releases_current_with_context() {
        let mut ctx = CacheContext::new();
        let current = alloc_slot_with_readers(&mut ctx, 1);
        let updated = alloc_slot_with_readers(&mut ctx, 1);
        let mut reader = SignatureSatisfiableExpanderCacheReader::new();
        reader.current_slot = current;
        reader.updated_slot = updated;

        assert!(reader.switch_to_updated_slot_item(&mut ctx));

        assert_eq!(reader.current_slot, updated);
        assert_eq!(reader.updated_slot, SigExpanderSlotItemId::NONE);
        assert_eq!(ctx.sig_expander_slot_item(current).reader_sharing_count, 0);
        assert!(!ctx.sig_expander_slot_item(current).has_cache_readers());
        assert_eq!(ctx.sig_expander_slot_item(updated).reader_sharing_count, 1);
    }

    #[test]
    fn sig_expander_reader_finds_signature_entry_through_slot_hash_with_context() {
        let mut ctx = CacheContext::new();
        let entry =
            ctx.alloc_sig_expander_cache_entry(SignatureSatisfiableExpanderCacheEntry::new());
        let slot = alloc_slot_with_signature_entry(&mut ctx, 123, entry);
        let mut reader = SignatureSatisfiableExpanderCacheReader::new();
        reader.current_slot = slot;

        assert!(reader.has_cache_entry(123, &mut ctx));
        assert!(!reader.has_cache_entry(124, &mut ctx));
        assert_eq!(reader.get_cache_entry_by_signature(123, &mut ctx), entry);
        assert_eq!(
            reader.get_cache_entry_by_signature(124, &mut ctx),
            SigExpanderCacheEntryId::NONE
        );
    }

    #[test]
    fn sig_expander_reader_signature_lookup_switches_to_updated_slot_with_context() {
        let mut ctx = CacheContext::new();
        let old_entry =
            ctx.alloc_sig_expander_cache_entry(SignatureSatisfiableExpanderCacheEntry::new());
        let new_entry =
            ctx.alloc_sig_expander_cache_entry(SignatureSatisfiableExpanderCacheEntry::new());
        let current = alloc_slot_with_signature_entry(&mut ctx, 7, old_entry);
        let updated = alloc_slot_with_signature_entry(&mut ctx, 8, new_entry);
        let mut reader = SignatureSatisfiableExpanderCacheReader::new();
        reader.current_slot = current;
        reader.updated_slot = updated;

        assert!(reader.has_cache_entry(8, &mut ctx));

        assert_eq!(reader.current_slot, updated);
        assert_eq!(reader.updated_slot, SigExpanderSlotItemId::NONE);
        assert_eq!(ctx.sig_expander_slot_item(current).reader_sharing_count, 0);
        assert_eq!(reader.get_cache_entry_by_signature(8, &mut ctx), new_entry);
        assert_eq!(
            reader.get_cache_entry_by_signature(7, &mut ctx),
            SigExpanderCacheEntryId::NONE
        );
    }

    #[test]
    fn sig_expander_reader_value_set_lookup_uses_typed_hasher_hash_with_context() {
        let mut ctx = CacheContext::new();
        let entry =
            ctx.alloc_sig_expander_cache_entry(SignatureSatisfiableExpanderCacheEntry::new());
        let (slot, cache_value_set) = alloc_slot_with_hasher_entry(&mut ctx, &[31, 37], entry);
        let mut reader = SignatureSatisfiableExpanderCacheReader::new();
        reader.current_slot = slot;

        assert_eq!(
            reader.get_cache_entry_by_value_set(cache_value_set, &mut ctx),
            SigExpanderCacheEntryId::NONE
        );
    }

    #[test]
    fn sig_expander_cache_create_reader_prepends_reader_linker_with_context() {
        let mut ctx = CacheContext::new();
        let mut cache = SignatureSatisfiableExpanderCache::new();

        let first = cache.create_cache_reader(&mut ctx);
        let second = cache.create_cache_reader(&mut ctx);

        assert_eq!(cache.reader_linker, second);
        assert_eq!(ctx.sig_expander_cache_reader(second).get_next(), first);
        assert_eq!(
            ctx.sig_expander_cache_reader(first).get_next(),
            SigExpanderCacheReaderId::NONE
        );
    }

    #[test]
    fn sig_expander_cache_clean_unused_slots_unlinks_unread_slots_with_context() {
        let mut ctx = CacheContext::new();
        let unused_tail = alloc_slot_with_readers(&mut ctx, 0);
        let used_tail = alloc_slot_with_readers(&mut ctx, 1);
        ctx.sig_expander_slot_item_mut(used_tail)
            .set_next(unused_tail);
        let unused_middle = alloc_slot_with_readers(&mut ctx, 0);
        ctx.sig_expander_slot_item_mut(unused_middle)
            .set_next(used_tail);
        let used_head = alloc_slot_with_readers(&mut ctx, 2);
        ctx.sig_expander_slot_item_mut(used_head)
            .set_next(unused_middle);
        let unused_head = alloc_slot_with_readers(&mut ctx, 0);
        ctx.sig_expander_slot_item_mut(unused_head)
            .set_next(used_head);
        let mut cache = SignatureSatisfiableExpanderCache::new();
        cache.slot_linker = unused_head;

        cache.clean_unused_slots(&mut ctx);

        assert_eq!(cache.slot_linker, used_head);
        assert_eq!(ctx.sig_expander_slot_item(used_head).get_next(), used_tail);
        assert_eq!(
            ctx.sig_expander_slot_item(used_tail).get_next(),
            SigExpanderSlotItemId::NONE
        );
    }

    #[test]
    fn sig_expander_cache_clean_unused_slots_clears_all_unused_slots_with_context() {
        let mut ctx = CacheContext::new();
        let tail = alloc_slot_with_readers(&mut ctx, 0);
        let head = alloc_slot_with_readers(&mut ctx, 0);
        ctx.sig_expander_slot_item_mut(head).set_next(tail);
        let mut cache = SignatureSatisfiableExpanderCache::new();
        cache.slot_linker = head;

        cache.clean_unused_slots(&mut ctx);

        assert_eq!(cache.slot_linker, SigExpanderSlotItemId::NONE);
    }

    #[test]
    fn sig_expander_cache_create_reader_slot_update_publishes_snapshot_to_readers_with_context() {
        let mut ctx = CacheContext::new();
        let entry =
            ctx.alloc_sig_expander_cache_entry(SignatureSatisfiableExpanderCacheEntry::new());
        let mut redirection = SignatureSatisfiableExpanderCacheRedirectionItem::new();
        redirection.init_redirection_item(entry, 42, 3);
        let redirection = ctx.alloc_sig_expander_redirection_item(redirection);
        let mut cache = SignatureSatisfiableExpanderCache::new();
        cache.sig_item_hash.insert(42, redirection);
        let first_reader = cache.create_cache_reader(&mut ctx);
        let second_reader = cache.create_cache_reader(&mut ctx);

        cache.create_reader_slot_update(&mut ctx);

        let slot = cache.slot_linker;
        assert!(slot.is_some());
        assert_eq!(
            ctx.sig_expander_slot_item(slot)
                .get_signature_item_hash()
                .get(&42),
            Some(&redirection)
        );
        assert_eq!(ctx.sig_expander_slot_item(slot).reader_sharing_count, 2);
        assert_eq!(
            ctx.sig_expander_cache_reader(first_reader).updated_slot,
            slot
        );
        assert_eq!(
            ctx.sig_expander_cache_reader(second_reader).updated_slot,
            slot
        );
    }

    #[test]
    fn sig_expander_cache_create_reader_slot_update_appends_after_existing_slot_with_context() {
        let mut ctx = CacheContext::new();
        let existing = alloc_slot_with_readers(&mut ctx, 1);
        let mut cache = SignatureSatisfiableExpanderCache::new();
        cache.slot_linker = existing;
        cache.create_cache_reader(&mut ctx);

        cache.create_reader_slot_update(&mut ctx);

        let appended = ctx.sig_expander_slot_item(existing).get_next();
        assert!(appended.is_some());
        assert_eq!(cache.slot_linker, existing);
        assert_eq!(
            ctx.sig_expander_slot_item(appended).get_next(),
            SigExpanderSlotItemId::NONE
        );
        assert_eq!(ctx.sig_expander_slot_item(appended).reader_sharing_count, 1);
    }

    #[test]
    fn sig_expander_write_expander_caching_data_inserts_new_signature_redirection_with_context() {
        let mut ctx = CacheContext::new();
        let mut cache = SignatureSatisfiableExpanderCache::new();

        assert!(cache.write_expander_caching_data_sig(
            0,
            91,
            SigExpanderCacheValueListId::NONE,
            SigExpanderDepHashId::NONE,
            &mut ctx
        ));

        let sig_item = *cache.sig_item_hash.get(&91).unwrap();
        let item = ctx.sig_expander_redirection_item(sig_item);
        assert_eq!(item.get_signature(), 91);
        assert!(item.get_cache_entry().is_some());
        assert_eq!(
            item.get_expander_count(),
            ctx.sig_expander_cache_entry(item.get_cache_entry())
                .get_expander_cache_value_count()
        );
        assert!(cache.already_exp_sig_set.contains(&0));
    }

    #[test]
    fn sig_expander_write_expander_caching_data_reuses_previous_entry_and_marks_multiple() {
        let mut ctx = CacheContext::new();
        let mut cache = SignatureSatisfiableExpanderCache::new();
        assert!(cache.write_expander_caching_data_sig(
            0,
            10,
            SigExpanderCacheValueListId::NONE,
            SigExpanderDepHashId::NONE,
            &mut ctx
        ));
        cache.already_exp_sig_set.insert(10);
        let previous_entry = ctx
            .sig_expander_redirection_item(*cache.sig_item_hash.get(&10).unwrap())
            .get_cache_entry();

        assert!(cache.write_expander_caching_data_sig(
            10,
            11,
            SigExpanderCacheValueListId::NONE,
            SigExpanderDepHashId::NONE,
            &mut ctx
        ));

        let new_entry = ctx
            .sig_expander_redirection_item(*cache.sig_item_hash.get(&11).unwrap())
            .get_cache_entry();
        assert_eq!(new_entry, previous_entry);
        assert!(ctx
            .sig_expander_cache_entry(previous_entry)
            .has_multiple_expanded());
        assert!(cache.already_exp_sig_set.contains(&10));
    }

    #[test]
    fn sig_expander_write_expander_caching_data_duplicate_marks_incompatible() {
        let mut ctx = CacheContext::new();
        let mut cache = SignatureSatisfiableExpanderCache::new();
        assert!(cache.write_expander_caching_data_sig(
            0,
            77,
            SigExpanderCacheValueListId::NONE,
            SigExpanderDepHashId::NONE,
            &mut ctx
        ));

        assert!(!cache.write_expander_caching_data_sig(
            0,
            77,
            SigExpanderCacheValueListId::NONE,
            SigExpanderDepHashId::NONE,
            &mut ctx
        ));

        assert!(cache.incompatible_sig_set.contains(&77));
    }

    #[test]
    fn sig_expander_write_expander_caching_data_installs_cache_value_linkers_with_context() {
        let mut ctx = CacheContext::new();
        let cache_values = alloc_cache_value_list(&mut ctx, &[10, 20]);
        let mut cache = SignatureSatisfiableExpanderCache::new();

        assert!(cache.write_expander_caching_data_sig(
            0,
            88,
            cache_values,
            SigExpanderDepHashId::NONE,
            &mut ctx
        ));

        let entry = ctx
            .sig_expander_redirection_item(*cache.sig_item_hash.get(&88).unwrap())
            .get_cache_entry();
        let entry_ref = ctx.sig_expander_cache_entry(entry);
        assert_eq!(entry_ref.get_expander_cache_value_count(), 2);
        let first = entry_ref.get_expander_cache_value_linker();
        let second = ctx.expander_cache_value_linker(first).get_next();
        assert_eq!(
            ctx.expander_cache_value_linker(first).get_cache_value(),
            cv(10)
        );
        assert_eq!(
            ctx.expander_cache_value_linker(second).get_cache_value(),
            cv(20)
        );
        assert_eq!(
            ctx.expander_cache_value_linker(second).get_next(),
            ExpanderCacheValueLinkerId::NONE
        );
        assert_eq!(
            entry_ref.get_tag_expander_cache_value_hash().get(&10),
            Some(&first)
        );
        assert_eq!(
            entry_ref.get_tag_expander_cache_value_hash().get(&20),
            Some(&second)
        );
    }

    #[test]
    fn sig_expander_write_expander_caching_data_wires_forward_dependency_with_context() {
        let mut ctx = CacheContext::new();
        let cache_values = alloc_cache_value_list(&mut ctx, &[10, 20]);
        let dep_hash = alloc_dep_hash(&mut ctx, &[(10, 20)]);
        let mut cache = SignatureSatisfiableExpanderCache::new();

        assert!(cache.write_expander_caching_data_sig(0, 89, cache_values, dep_hash, &mut ctx));

        let entry = ctx
            .sig_expander_redirection_item(*cache.sig_item_hash.get(&89).unwrap())
            .get_cache_entry();
        let tag_hash = ctx
            .sig_expander_cache_entry(entry)
            .get_tag_expander_cache_value_hash();
        let ten = *tag_hash.get(&10).unwrap();
        let twenty = *tag_hash.get(&20).unwrap();
        let dep = ctx
            .expander_cache_value_linker(ten)
            .get_expander_dependency_list()[0];
        assert_eq!(
            ctx.expander_cache_value_linker(ten).get_cache_value(),
            cv(10)
        );
        assert_eq!(
            ctx.expander_cache_value_linker(twenty).get_cache_value(),
            cv(20)
        );
        assert_eq!(
            ctx.expander_cache_value_linker(dep).get_cache_value(),
            cv(20)
        );
    }

    #[test]
    fn sig_expander_is_caching_data_expandable_uses_incompatible_signature_set_with_context() {
        let mut ctx = CacheContext::new();
        let mut cache = SignatureSatisfiableExpanderCache::new();
        cache.incompatible_sig_set.insert(12);

        assert!(cache.is_caching_data_expandable(
            SigExpanderCacheEntryId::NONE,
            12,
            SigExpanderCacheValueListId::NONE,
            &mut ctx,
        ));
    }

    #[test]
    fn sig_expander_is_caching_data_expandable_uses_entry_multiple_expanded_with_context() {
        let mut ctx = CacheContext::new();
        let mut entry = SignatureSatisfiableExpanderCacheEntry::new();
        entry.set_multiple_expanded(true);
        let entry = ctx.alloc_sig_expander_cache_entry(entry);
        let cache = SignatureSatisfiableExpanderCache::new();

        assert!(cache.is_caching_data_expandable(
            entry,
            13,
            SigExpanderCacheValueListId::NONE,
            &mut ctx
        ));
    }

    #[test]
    fn sig_expander_is_caching_data_expandable_drains_previous_count_with_context() {
        let mut ctx = CacheContext::new();
        let initial_values = alloc_cache_value_list(&mut ctx, &[10, 20]);
        let mut cache = SignatureSatisfiableExpanderCache::new();
        assert!(cache.write_expander_caching_data_sig(
            0,
            61,
            initial_values,
            SigExpanderDepHashId::NONE,
            &mut ctx
        ));
        let entry = ctx
            .sig_expander_redirection_item(*cache.sig_item_hash.get(&61).unwrap())
            .get_cache_entry();
        let new_values = alloc_cache_value_list(&mut ctx, &[10, 20, 30]);

        assert!(cache.is_caching_data_expandable(entry, 61, new_values, &mut ctx));

        assert_eq!(
            ctx.sig_expander_cache_value_list(new_values).cache_values,
            vec![cv(30)]
        );
    }

    #[test]
    fn sig_expander_is_caching_data_expandable_rejects_incompatible_mismatch_with_context() {
        let mut ctx = CacheContext::new();
        let initial_values = alloc_cache_value_list(&mut ctx, &[10]);
        let mut cache = SignatureSatisfiableExpanderCache::new();
        assert!(cache.write_expander_caching_data_sig(
            0,
            62,
            initial_values,
            SigExpanderDepHashId::NONE,
            &mut ctx
        ));
        cache.incompatible_sig_set.insert(62);
        let entry = ctx
            .sig_expander_redirection_item(*cache.sig_item_hash.get(&62).unwrap())
            .get_cache_entry();
        let new_values = alloc_cache_value_list(&mut ctx, &[99]);

        assert!(!cache.is_caching_data_expandable(entry, 62, new_values, &mut ctx));
    }

    #[test]
    fn sig_expander_write_satisfiable_branch_empty_marks_entry_satisfiable_with_context() {
        let mut ctx = CacheContext::new();
        let mut cache = SignatureSatisfiableExpanderCache::new();
        assert!(cache.write_expander_caching_data_sig(
            0,
            33,
            SigExpanderCacheValueListId::NONE,
            SigExpanderDepHashId::NONE,
            &mut ctx
        ));
        let entry = ctx
            .sig_expander_redirection_item(*cache.sig_item_hash.get(&33).unwrap())
            .get_cache_entry();

        assert!(cache.write_satisfiable_branched_caching_data(
            33,
            SigExpanderCacheValueListId::NONE,
            SigExpanderCacheValueListId::NONE,
            &mut ctx
        ));

        let entry = ctx.sig_expander_cache_entry(entry);
        assert!(entry.is_satisfiable());
        assert!(entry.is_satisfiable_without_branched_concepts());
    }

    #[test]
    fn sig_expander_write_satisfiable_branch_nonempty_appends_branch_linker_with_context() {
        let mut ctx = CacheContext::new();
        let mut cache = SignatureSatisfiableExpanderCache::new();
        assert!(cache.write_expander_caching_data_sig(
            0,
            34,
            SigExpanderCacheValueListId::NONE,
            SigExpanderDepHashId::NONE,
            &mut ctx
        ));
        let entry = ctx
            .sig_expander_redirection_item(*cache.sig_item_hash.get(&34).unwrap())
            .get_cache_entry();
        let branch_values = alloc_cache_value_list(&mut ctx, &[100, 101]);

        assert!(cache.write_satisfiable_branched_caching_data(
            34,
            SigExpanderCacheValueListId::NONE,
            branch_values,
            &mut ctx
        ));

        let entry_ref = ctx.sig_expander_cache_entry(entry);
        assert!(entry_ref.is_satisfiable());
        assert!(!entry_ref.is_satisfiable_without_branched_concepts());
        let branch = entry_ref.get_expander_branched_linker();
        assert!(branch.is_some());
        assert_eq!(
            ctx.expander_branched_linker(branch).get_cache_value_list(),
            &vec![cv(100), cv(101)]
        );
    }

    #[test]
    fn sig_expander_write_satisfiable_branch_missing_signature_returns_false() {
        let mut ctx = CacheContext::new();
        let mut cache = SignatureSatisfiableExpanderCache::new();

        assert!(!cache.write_satisfiable_branched_caching_data(
            404,
            SigExpanderCacheValueListId::NONE,
            SigExpanderCacheValueListId::NONE,
            &mut ctx
        ));
    }

    #[test]
    fn sig_expander_create_cache_writer_returns_forwarding_writer() {
        let mut ctx = CacheContext::new();
        let mut cache = SignatureSatisfiableExpanderCache::new();
        let reader = cache.create_cache_reader(&mut ctx);
        let mut writer = cache.create_cache_writer();

        writer.write_expand_cached(
            &mut cache,
            0,
            606,
            SigExpanderCacheValueListId::NONE,
            SigExpanderDepHashId::NONE,
            0,
            &mut ctx,
        );

        assert_eq!(writer.cache, 0);
        assert!(cache.sig_item_hash.contains_key(&606));
        let slot = ctx.sig_expander_cache_reader(reader).updated_slot;
        assert!(slot.is_some());
        assert_eq!(
            ctx.sig_expander_slot_item(slot)
                .get_signature_item_hash()
                .get(&606),
            cache.sig_item_hash.get(&606)
        );
    }

    #[test]
    fn sig_expander_writer_forwards_write_data_chain_to_cache() {
        let mut ctx = CacheContext::new();
        let mut expand = SignatureSatisfiableExpanderCacheEntryWriteData::new();
        expand.init_expand_write_data(
            0,
            707,
            SigExpanderCacheValueListId::NONE,
            SigExpanderDepHashId::NONE,
        );
        let expand = ctx.alloc_sig_expander_entry_write_data(expand);
        let mut cache = SignatureSatisfiableExpanderCache::new();
        let mut writer = cache.create_cache_writer();

        writer.write_cached_data(&mut cache, expand, 0, &mut ctx);

        assert!(cache.sig_item_hash.contains_key(&707));
    }

    #[test]
    fn sig_expander_process_custom_events_drains_collected_write_data_chain_with_context() {
        let mut ctx = CacheContext::new();
        let mut expand = SignatureSatisfiableExpanderCacheEntryWriteData::new();
        expand.init_expand_write_data(
            0,
            515,
            SigExpanderCacheValueListId::NONE,
            SigExpanderDepHashId::NONE,
        );
        let expand = ctx.alloc_sig_expander_entry_write_data(expand);
        let mut cache = SignatureSatisfiableExpanderCache::new();
        cache.collect_write_data = expand;
        cache.collect_count = 1;
        cache.next_write_collect_count = 1;

        assert!(cache.process_customs_events(
            super::super::value::event::WRITE_CACHED_DATA_ENTRY,
            0,
            &mut ctx,
        ));

        assert!(cache.sig_item_hash.contains_key(&515));
        assert_eq!(cache.collect_write_data, SigExpanderEntryWriteDataId::NONE);
        assert_eq!(cache.collect_count, 0);
    }

    #[test]
    fn sig_expander_typed_expand_event_uses_event_payload_with_context() {
        let mut ctx = CacheContext::new();
        let cache_values = alloc_cache_value_list(&mut ctx, &[21, 22]);
        let dep_hash = alloc_dep_hash(&mut ctx, &[(21, 210), (22, 220)]);
        let mut cache = SignatureSatisfiableExpanderCache::new();
        let event = CacheEvent::write_expand_cached(0, 616, cache_values, dep_hash, 41);

        assert!(cache.process_customs_cache_event(&event, &mut ctx));

        assert!(cache.sig_item_hash.contains_key(&616));
        let entry = ctx
            .sig_expander_redirection_item(*cache.sig_item_hash.get(&616).unwrap())
            .get_cache_entry();
        assert_eq!(
            ctx.sig_expander_cache_entry(entry)
                .get_expander_cache_value_count(),
            3
        );
    }

    #[test]
    fn sig_expander_typed_satisfiable_branch_event_uses_event_payload_with_context() {
        let mut ctx = CacheContext::new();
        let mut cache = SignatureSatisfiableExpanderCache::new();
        assert!(cache.write_expander_caching_data_sig(
            0,
            717,
            SigExpanderCacheValueListId::NONE,
            SigExpanderDepHashId::NONE,
            &mut ctx
        ));
        let cache_values = alloc_cache_value_list(&mut ctx, &[]);
        let branched_values = alloc_cache_value_list(&mut ctx, &[31, 32]);
        let event =
            CacheEvent::write_satisfiable_branch_cached(717, cache_values, branched_values, 42);

        assert!(cache.process_customs_cache_event(&event, &mut ctx));

        let entry = ctx
            .sig_expander_redirection_item(*cache.sig_item_hash.get(&717).unwrap())
            .get_cache_entry();
        assert!(ctx.sig_expander_cache_entry(entry).is_satisfiable());
        let branch = ctx
            .sig_expander_cache_entry(entry)
            .get_expander_branched_linker();
        assert!(branch.is_some());
        assert_eq!(
            ctx.expander_branched_linker(branch)
                .get_cache_value_list()
                .len(),
            2
        );
    }

    #[test]
    fn sig_expander_typed_write_cached_data_event_collects_and_drains_payload() {
        let mut ctx = CacheContext::new();
        let mut expand = SignatureSatisfiableExpanderCacheEntryWriteData::new();
        expand.init_expand_write_data(
            0,
            818,
            SigExpanderCacheValueListId::NONE,
            SigExpanderDepHashId::NONE,
        );
        let expand = ctx.alloc_sig_expander_entry_write_data(expand);
        let mut cache = SignatureSatisfiableExpanderCache::new();
        cache.next_write_collect_count = 1;
        let event = CacheEvent::write_cached_data(expand, 43);

        assert!(cache.process_customs_cache_event(&event, &mut ctx));

        assert!(cache.sig_item_hash.contains_key(&818));
        assert_eq!(cache.collect_write_data, SigExpanderEntryWriteDataId::NONE);
        assert_eq!(cache.collect_count, 0);
        assert_eq!(cache.write_data_count, 1);
    }

    #[test]
    fn sig_expander_write_data_get_count_walks_arena_chain_with_context() {
        let mut ctx = CacheContext::new();
        let third = alloc_write_data(&mut ctx, SigExpanderEntryWriteDataId::NONE);
        let second = alloc_write_data(&mut ctx, third);
        let first = alloc_write_data(&mut ctx, second);

        assert_eq!(ctx.sig_expander_entry_write_data(first).get_count(&ctx), 3);
        assert_eq!(ctx.sig_expander_entry_write_data(second).get_count(&ctx), 2);
        assert_eq!(ctx.sig_expander_entry_write_data(third).get_count(&ctx), 1);
    }

    #[test]
    fn sig_expander_signature_ref_gate_counts_signatures_independently() {
        let mut cache = SignatureSatisfiableExpanderCache::new();
        cache.next_cache_entry_required_signature_ref_count = 2;

        assert!(!cache.can_create_cache_entry_for_signature(17));
        assert!(!cache.can_create_cache_entry_for_signature(23));
        assert!(cache.can_create_cache_entry_for_signature(17));
        assert!(cache.can_create_cache_entry_for_signature(23));
        assert_eq!(cache.signature_refer_count_set.get(&17), Some(&2));
        assert_eq!(cache.signature_refer_count_set.get(&23), Some(&2));
    }

    #[test]
    fn sig_expander_signature_ref_gate_uses_konclude_defaults_and_one_step_memory_bump() {
        let mut cache = SignatureSatisfiableExpanderCache::new();
        assert_eq!(
            cache.next_memory_level_required_signature_ref_count,
            DEFAULT_SIG_EXPANDER_INITIAL_MEMORY_LEVEL_FOR_REF_COUNT_INCREASE
        );
        assert_eq!(
            cache.next_memory_level_increase_for_required_signature_reference_count,
            DEFAULT_SIG_EXPANDER_NEXT_MEMORY_LEVEL_INCREASE_FOR_REF_COUNT
        );
        assert_eq!(cache.next_cache_entry_required_signature_ref_count, 1);
        assert_eq!(
            cache.next_cache_entry_required_signature_reference_count_increase,
            1
        );

        cache.next_memory_level_required_signature_ref_count = 10;
        cache.next_memory_level_increase_for_required_signature_reference_count = 5;
        cache.next_cache_entry_required_signature_ref_count = 2;
        cache.next_cache_entry_required_signature_reference_count_increase = 3;
        cache.context.add_rel_memory = 20;

        assert_eq!(
            cache.get_required_signature_refer_count_for_next_cache_entry_creation(),
            5
        );
        assert_eq!(cache.next_memory_level_required_signature_ref_count, 15);
        assert_eq!(
            cache.get_required_signature_refer_count_for_next_cache_entry_creation(),
            8
        );
        assert_eq!(cache.next_memory_level_required_signature_ref_count, 20);
    }

    #[test]
    fn sig_expander_hasher_hashes_linker_values_with_context() {
        let mut ctx = CacheContext::new();
        let third = alloc_value_linker(&mut ctx, -9, ExpanderCacheValueLinkerId::NONE);
        let second = alloc_value_linker(&mut ctx, 7, third);
        let first = alloc_value_linker(&mut ctx, 5, second);

        let hasher = SignatureSatisfiableExpanderCacheHasher::new_from_linker(first, 3, &ctx);
        let partial = SignatureSatisfiableExpanderCacheHasher::new_from_linker(first, 2, &ctx);

        assert_eq!(hasher.get_hash_value(), qhash(5) + qhash(7) + qhash(-9));
        assert_eq!(partial.get_hash_value(), qhash(5) + qhash(7));
    }

    #[test]
    fn sig_expander_hasher_compares_linker_values_with_context() {
        let mut ctx = CacheContext::new();
        let left_second = alloc_value_linker(&mut ctx, 12, ExpanderCacheValueLinkerId::NONE);
        let left_first = alloc_value_linker(&mut ctx, 11, left_second);
        let right_second = alloc_value_linker(&mut ctx, 12, ExpanderCacheValueLinkerId::NONE);
        let right_first = alloc_value_linker(&mut ctx, 11, right_second);
        let mismatch_second = alloc_value_linker(&mut ctx, 13, ExpanderCacheValueLinkerId::NONE);
        let mismatch_first = alloc_value_linker(&mut ctx, 11, mismatch_second);
        let hasher = SignatureSatisfiableExpanderCacheHasher::new_from_linker(left_first, 2, &ctx);

        assert!(hasher.has_equal_cache_values_linker_linker(left_first, right_first, 2, &ctx,));
        assert!(!hasher.has_equal_cache_values_linker_linker(left_first, mismatch_first, 2, &ctx,));
    }

    #[test]
    fn sig_expander_hasher_hashes_cache_value_set_with_context() {
        let mut ctx = CacheContext::new();
        let set = alloc_cache_value_set(&mut ctx, &[5, 7, 5, -9]);

        let hasher = SignatureSatisfiableExpanderCacheHasher::new_from_set(set, &ctx);

        assert_eq!(hasher.cache_value_count, 3);
        assert_eq!(hasher.get_hash_value(), qhash(5) + qhash(7) + qhash(-9));
    }

    #[test]
    fn sig_expander_hasher_compares_cache_value_sets_with_context() {
        let mut ctx = CacheContext::new();
        let left = alloc_cache_value_set(&mut ctx, &[1, 2, 3]);
        let same = alloc_cache_value_set(&mut ctx, &[1, 2, 3]);
        let different_order = alloc_cache_value_set(&mut ctx, &[1, 3, 2]);
        let shorter = alloc_cache_value_set(&mut ctx, &[1, 2]);
        let hasher = SignatureSatisfiableExpanderCacheHasher::new_from_set(left, &ctx);

        assert!(hasher.has_equal_cache_values_set_set(left, same, &ctx));
        assert!(!hasher.has_equal_cache_values_set_set(left, different_order, &ctx));
        assert!(!hasher.has_equal_cache_values_set_set(left, shorter, &ctx));
    }

    #[test]
    fn sig_expander_hasher_compares_linker_values_against_set_with_context() {
        let mut ctx = CacheContext::new();
        let second = alloc_value_linker(&mut ctx, 12, ExpanderCacheValueLinkerId::NONE);
        let first = alloc_value_linker(&mut ctx, 11, second);
        let matching_set = alloc_cache_value_set(&mut ctx, &[12, 11, 13]);
        let missing_set = alloc_cache_value_set(&mut ctx, &[11, 13]);
        let hasher = SignatureSatisfiableExpanderCacheHasher::new_from_linker(first, 2, &ctx);

        assert!(hasher.has_equal_cache_values_linker_set(first, matching_set, 2, &ctx));
        assert!(!hasher.has_equal_cache_values_linker_set(first, missing_set, 2, &ctx));
    }
}
