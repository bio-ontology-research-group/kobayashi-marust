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
//! - `CCacheValue` (F0, `cache/value.rs`, not yet ported) is a CROSS-FAMILY value
//!   → opaque `Cint64` placeholder. [api]
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

use super::super::model::substrate::{Cint64, Id};
use super::value::CacheWriteDataType;

// --- cross-family opaque placeholder (F0 `cache/value.rs`) ---
/// Port of `CCacheValue` (F0, `cache/value.rs`). KONCLUDE-PORT-NOTE[api]:
/// cross-family value held opaque as a `Cint64` so F2 signatures read like the
/// C++ (`cacheValue: CCacheValue`) without pulling in the F0 unit; reconciles to
/// the real `value::CacheValue` struct when wired. A by-value `CCACHINGLIST<CCacheValue>`
/// → `Vec<CCacheValue>`; a *pointer* to a pool-managed `CCACHING*` container stays
/// opaque `Cint64` `[memory-pool]`.
pub type CCacheValue = Cint64;

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
/// `CSignatureSatisfiableExpanderCacheEntryWriteData*` (the write-data enum) →
/// `SigExpanderEntryWriteDataId`.
pub type SigExpanderEntryWriteDataId = Id<SignatureSatisfiableExpanderCacheEntryWriteData>;

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
    /// `CExpanderCacheValueLinker::mCacheValue` (`CCacheValue`, F0, held opaque).
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
            cache_value: 0,
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
    pub fn add_expander_dependency(&mut self, dep_exp_cache_value: ExpanderCacheValueLinkerId) -> &mut Self {
        // `mDepList.append(...)` on a CCACHINGLIST (QList-like) = push to the back.
        self.dep_list.push(dep_exp_cache_value);
        self
    }

    /// Port of `getExpanderDependencyList`.
    pub fn get_expander_dependency_list(&self) -> &Vec<ExpanderCacheValueLinkerId> {
        &self.dep_list
    }

    /// Port of `getCacheValue` (returns `&mCacheValue`; held opaque here).
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
    // pool-managed concurrent-modification hash → opaque handle.
    /// `CSignatureSatisfiableExpanderCacheEntry::mTagExpanderCacheValueHash`.
    pub tag_expander_cache_value_hash: Cint64,
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
            tag_expander_cache_value_hash: 0,
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
    pub fn append_expander_cache_value_linker(&mut self, linker: ExpanderCacheValueLinkerId) -> &mut Self {
        // KONCLUDE-PORT-NOTE[api]: C++ walks the linker chain incrementing mDetExpandCount,
        // then either sets mDetExpandValueLinker = linker (if empty) or tail-splices via
        // `mDetExpandValueLinker->append(linker)`. Both need the ExpanderCacheValueLinker
        // arena, which is not threaded into this method-batch wave.
        let mut linker_it = linker;
        while linker_it.is_some() {
            self.det_expand_count += 1;
            // W6-DEFER[api]: linkerIt = linkerIt->getNext();
            linker_it = ExpanderCacheValueLinkerId::NONE;
        }
        if self.det_expand_value_linker.is_none() {
            self.det_expand_value_linker = linker;
        } else {
            // W6-DEFER[api]: mDetExpandValueLinker->append(linker); (tail-splice, needs arena)
        }
        self
    }

    /// Port of `getExpanderCacheValueLinker`.
    pub fn get_expander_cache_value_linker(&self) -> ExpanderCacheValueLinkerId {
        self.det_expand_value_linker
    }

    /// Port of `appendExpanderBranchedLinker`.
    pub fn append_expander_branched_linker(&mut self, linker: ExpanderBranchedLinkerId) -> &mut Self {
        if self.expand_branched_linker.is_some() {
            // C++: mExpandBranchedLinker = linker->append(mExpandBranchedLinker);
            // `linker` tail-splices the prior chain after itself and becomes the new head.
            // W6-DEFER[api]: the tail-splice of the old chain needs the linker arena.
            self.expand_branched_linker = linker;
        } else {
            self.expand_branched_linker = linker;
        }
        self
    }

    /// Port of `getExpanderBranchedLinker`.
    pub fn get_expander_branched_linker(&self) -> ExpanderBranchedLinkerId {
        self.expand_branched_linker
    }

    /// Port of `getTagExpanderCacheValueHash` (opaque CCACHINGHASH handle).
    pub fn get_tag_expander_cache_value_hash(&self) -> Cint64 {
        self.tag_expander_cache_value_hash
    }

    /// Port of `setTagExpanderCacheValueHash`.
    pub fn set_tag_expander_cache_value_hash(&mut self, hash: Cint64) -> &mut Self {
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
// Hasher (`CSignatureSatisfiableExpanderCacheHasher`).
// ===========================================================================

/// Port of `CSignatureSatisfiableExpanderCacheHasher`.
///
/// The hash key over a cache-value set / expander-value linker chain (drives the
/// `mHasherItemHash` lookup).
pub struct SignatureSatisfiableExpanderCacheHasher {
    /// `CSignatureSatisfiableExpanderCacheHasher::mHashValue`.
    pub hash_value: Cint64,
    /// `CSignatureSatisfiableExpanderCacheHasher::mCacheValueCount`.
    pub cache_value_count: Cint64,
    // KONCLUDE-PORT-NOTE[ownership]: `CExpanderCacheValueLinker* mCacheValueLinker`.
    /// `CSignatureSatisfiableExpanderCacheHasher::mCacheValueLinker`.
    pub cache_value_linker: ExpanderCacheValueLinkerId,
    // KONCLUDE-PORT-NOTE[memory-pool]: `CCACHINGSET<CCacheValue>*` pool set → opaque.
    /// `CSignatureSatisfiableExpanderCacheHasher::mCacheValueSet`.
    pub cache_value_set: Cint64,
}

impl Default for SignatureSatisfiableExpanderCacheHasher {
    fn default() -> Self {
        SignatureSatisfiableExpanderCacheHasher {
            hash_value: 0,
            cache_value_count: 0,
            cache_value_linker: ExpanderCacheValueLinkerId::NONE,
            cache_value_set: 0,
        }
    }
}

impl SignatureSatisfiableExpanderCacheHasher {
    /// Port of `CSignatureSatisfiableExpanderCacheHasher::CSignatureSatisfiableExpanderCacheHasher`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `CSignatureSatisfiableExpanderCacheHasher(CCACHINGSET<CCacheValue>* cacheValueSet)`.
    pub fn new_from_set(cache_value_set: Cint64) -> Self {
        let mut hasher = SignatureSatisfiableExpanderCacheHasher {
            cache_value_set,
            hash_value: 0,
            // KONCLUDE-PORT-NOTE[api]: mCacheValueCount = cacheValueSet->count();
            // W6-DEFER[api]: count of the opaque CCACHINGSET handle.
            cache_value_count: 0,
            cache_value_linker: ExpanderCacheValueLinkerId::NONE,
        };
        hasher.calculate_hash_value_set(cache_value_set);
        hasher
    }

    /// Port of `CSignatureSatisfiableExpanderCacheHasher(CExpanderCacheValueLinker*, cint64 count)`.
    pub fn new_from_linker(cache_value_linker: ExpanderCacheValueLinkerId, count: Cint64) -> Self {
        let mut hasher = SignatureSatisfiableExpanderCacheHasher {
            cache_value_set: 0,
            hash_value: 0,
            cache_value_count: count,
            cache_value_linker,
        };
        hasher.calculate_hash_value_linker(cache_value_linker, hasher.cache_value_count);
        hasher
    }

    /// Port of `getHashValue`.
    pub fn get_hash_value(&self) -> Cint64 {
        self.hash_value
    }

    /// Port of `operator==`.
    pub fn equals(&self, hasher: &SignatureSatisfiableExpanderCacheHasher) -> bool {
        if self.hash_value != hasher.hash_value {
            return false;
        }
        if self.cache_value_count != hasher.cache_value_count {
            return false;
        }
        if self.cache_value_linker.is_some() && hasher.cache_value_linker.is_some() {
            if !self.has_equal_cache_values_linker_linker(self.cache_value_linker, hasher.cache_value_linker, self.cache_value_count) {
                return false;
            }
        } else if self.cache_value_set != 0 && hasher.cache_value_set != 0 {
            if !self.has_equal_cache_values_set_set(self.cache_value_set, hasher.cache_value_set) {
                return false;
            }
        } else if self.cache_value_linker.is_some() && hasher.cache_value_set != 0 {
            if !self.has_equal_cache_values_linker_set(self.cache_value_linker, hasher.cache_value_set, self.cache_value_count) {
                return false;
            }
        } else {
            if !self.has_equal_cache_values_linker_set(hasher.cache_value_linker, self.cache_value_set, self.cache_value_count) {
                return false;
            }
        }
        // KONCLUDE-PORT-NOTE[unclear]: the C++ `operator==` falls through to `return false;`
        // here (apparent upstream bug — even matching hashers compare unequal). Ported verbatim.
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
        // KONCLUDE-PORT-NOTE[api]: C++ does `mHashValue += qHash(*cacheValue)`.
        // W6-DEFER[api]: qHash over the opaque CCacheValue (F0 value, held opaque here).
        let _ = cache_value;
    }

    /// Port of protected `calculateHashValue(CCACHINGSET<CCacheValue>*)`.
    fn calculate_hash_value_set(&mut self, cache_value_set: Cint64) {
        self.hash_value = 0;
        // KONCLUDE-PORT-NOTE[api]: iterate the opaque CCACHINGSET, extendHashValue each value.
        // W6-DEFER[api]: for it in cacheValueSet { self.extend_hash_value(*it); }
        let _ = cache_value_set;
    }

    /// Port of protected `calculateHashValue(CExpanderCacheValueLinker*, cint64)`.
    fn calculate_hash_value_linker(&mut self, cache_value_linker: ExpanderCacheValueLinkerId, count: Cint64) {
        self.hash_value = 0;
        let mut cache_value_linker_it = cache_value_linker;
        let mut nr: Cint64 = 0;
        while cache_value_linker_it.is_some() && {
            let cond = nr < count;
            nr += 1;
            cond
        } {
            // W6-DEFER[api]: self.extend_hash_value(cacheValueLinkerIt->getCacheValue()); (needs arena)
            // W6-DEFER[api]: cacheValueLinkerIt = cacheValueLinkerIt->getNext();
            cache_value_linker_it = ExpanderCacheValueLinkerId::NONE;
        }
    }

    /// Port of protected `hasEqualCacheValues(linker, linker2, count)`.
    fn has_equal_cache_values_linker_linker(
        &self,
        mut cache_value_linker: ExpanderCacheValueLinkerId,
        mut cache_value_linker2: ExpanderCacheValueLinkerId,
        count: Cint64,
    ) -> bool {
        let mut nr: Cint64 = 0;
        while cache_value_linker.is_some() && cache_value_linker2.is_some() && {
            let cond = nr < count;
            nr += 1;
            cond
        } {
            // W6-DEFER[api]: if (*l1->getCacheValue() != *l2->getCacheValue()) return false; (needs arena)
            // W6-DEFER[api]: l1 = l1->getNext(); l2 = l2->getNext();
            cache_value_linker = ExpanderCacheValueLinkerId::NONE;
            cache_value_linker2 = ExpanderCacheValueLinkerId::NONE;
        }
        if nr < count {
            if cache_value_linker.is_some() || cache_value_linker2.is_some() {
                return false;
            }
        }
        true
    }

    /// Port of protected `hasEqualCacheValues(set, set2)`.
    fn has_equal_cache_values_set_set(&self, cache_value_set: Cint64, cache_value_set2: Cint64) -> bool {
        // KONCLUDE-PORT-NOTE[api]: iterate both opaque CCACHINGSETs in lockstep; any mismatch → false.
        // W6-DEFER[api]: opaque-set iteration.
        let _ = (cache_value_set, cache_value_set2);
        true
    }

    /// Port of protected `hasEqualCacheValues(linker, set, count)`.
    fn has_equal_cache_values_linker_set(
        &self,
        mut cache_value_linker: ExpanderCacheValueLinkerId,
        cache_value_set: Cint64,
        count: Cint64,
    ) -> bool {
        let mut nr: Cint64 = 0;
        while cache_value_linker.is_some() && {
            let cond = nr < count;
            nr += 1;
            cond
        } {
            // W6-DEFER[api]: if (!set->contains(*linker->getCacheValue())) return false; (needs arena + set)
            // W6-DEFER[api]: linker = linker->getNext();
            cache_value_linker = ExpanderCacheValueLinkerId::NONE;
        }
        let _ = cache_value_set;
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
    pub sig_item_hash: Cint64,
    // KONCLUDE-PORT-NOTE[memory-pool]: `CCACHINGHASH<…Hasher,…RedirectionItem*>*` pool hash.
    /// `CSignatureSatisfiableExpanderCacheSlotItem::mHasherItemHash`.
    pub hasher_item_hash: Cint64,
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
            sig_item_hash: 0,
            hasher_item_hash: 0,
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

    /// Port of `setSignatureItemHash` (opaque CCACHINGHASH handle).
    pub fn set_signature_item_hash(&mut self, sig_item_hash: Cint64) -> &mut Self {
        self.sig_item_hash = sig_item_hash;
        self
    }

    /// Port of `setHasherItemHash` (opaque CCACHINGHASH handle).
    pub fn set_hasher_item_hash(&mut self, hasher_item_hash: Cint64) -> &mut Self {
        self.hasher_item_hash = hasher_item_hash;
        self
    }

    /// Port of `hasCacheReaders`.
    pub fn has_cache_readers(&self) -> bool {
        self.reader_using
    }

    /// Port of `getSignatureItemHash`.
    pub fn get_signature_item_hash(&self) -> Cint64 {
        self.sig_item_hash
    }

    /// Port of `getHasherItemHash`.
    pub fn get_hasher_item_hash(&self) -> Cint64 {
        self.hasher_item_hash
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
    pub fn update_slot(&mut self, updated_slot: SigExpanderSlotItemId) -> &mut Self {
        // KONCLUDE-PORT-NOTE[threading]: `mUpdatedSlot.fetchAndStoreOrdered(updatedSlot)` is an
        // atomic swap returning the previous value; single-threaded inline here.
        let prev_slot = self.updated_slot;
        self.updated_slot = updated_slot;
        if prev_slot.is_some() {
            // W6-DEFER[api]: prevSlot->decReader(); needs the slot arena (cross-deref).
        }
        self
    }

    /// Port of protected `hasUpdatedSlotItem`.
    fn has_updated_slot_item(&self) -> bool {
        // KONCLUDE-PORT-NOTE[threading]: `mUpdatedSlot.fetchAndAddRelaxed(0) != nullptr`.
        self.updated_slot.is_some()
    }

    /// Port of protected `switchToUpdatedSlotItem`.
    fn switch_to_updated_slot_item(&mut self) -> bool {
        // KONCLUDE-PORT-NOTE[threading]: `mUpdatedSlot.fetchAndStoreOrdered(nullptr)`.
        let updated_slot = self.updated_slot;
        self.updated_slot = SigExpanderSlotItemId::NONE;
        if updated_slot.is_some() {
            let prev_slot = self.current_slot;
            self.current_slot = updated_slot;
            if prev_slot.is_some() {
                // W6-DEFER[api]: prevSlot->decReader(); needs the slot arena.
            }
            return true;
        }
        false
    }

    /// Port of `hasCacheEntry(cint64 signature)`.
    pub fn has_cache_entry(&mut self, signature: Cint64) -> bool {
        if self.has_updated_slot_item() {
            self.switch_to_updated_slot_item();
        }
        if self.current_slot.is_some() {
            // KONCLUDE-PORT-NOTE[api]: sigItemHash = mCurrentSlot->getSignatureItemHash();
            // if (sigItemHash) return sigItemHash->contains(signature);
            // W6-DEFER[api]: needs the slot arena + the opaque CCACHINGHASH lookup.
        }
        let _ = signature;
        false
    }

    /// Port of `getCacheEntry(cint64 signature)`.
    pub fn get_cache_entry_by_signature(&mut self, signature: Cint64) -> SigExpanderCacheEntryId {
        let entry = SigExpanderCacheEntryId::NONE;
        if self.has_updated_slot_item() {
            self.switch_to_updated_slot_item();
        }
        if self.current_slot.is_some() {
            // KONCLUDE-PORT-NOTE[api]: item = mCurrentSlot->getSignatureItemHash()->value(signature);
            // if (item) entry = item->getCacheEntry();
            // W6-DEFER[api]: needs the slot/redirection arenas + opaque CCACHINGHASH lookup.
        }
        let _ = signature;
        entry
    }

    /// Port of `getCacheEntry(CCACHINGSET<CCacheValue>* cacheValueSet)`.
    pub fn get_cache_entry_by_value_set(&mut self, cache_value_set: Cint64) -> SigExpanderCacheEntryId {
        let entry = SigExpanderCacheEntryId::NONE;
        if self.has_updated_slot_item() {
            self.switch_to_updated_slot_item();
        }
        if self.current_slot.is_some() {
            // KONCLUDE-PORT-NOTE[api]: hasherItemHash = mCurrentSlot->getHasherItemHash();
            // build CSignatureSatisfiableExpanderCacheHasher(cacheValueSet) and look it up.
            // W6-DEFER[api]: needs the slot/redirection arenas + opaque CCACHINGHASH lookup.
        }
        let _ = cache_value_set;
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

    /// Port of `writeCachedData` — forwards to the owning cache facade.
    pub fn write_cached_data(&mut self, write_data: SigExpanderEntryWriteDataId, memory_pools: Cint64) -> &mut Self {
        // W6-DEFER[api]: mCache->writeCachedData(writeData, memoryPools);
        // mCache is the opaque back-pointer to the facade thread.
        let _ = (write_data, memory_pools);
        self
    }

    /// Port of `writeExpandCached` — forwards to the owning cache facade.
    pub fn write_expand_cached(
        &mut self,
        prev_signature: Cint64,
        new_signature: Cint64,
        cache_value_list: Cint64,
        dep_hash: Cint64,
        memory_pools: Cint64,
    ) -> &mut Self {
        // W6-DEFER[api]: mCache->writeExpandCached(prevSignature, newSignature, cacheValueList, depHash, memoryPools);
        let _ = (prev_signature, new_signature, cache_value_list, dep_hash, memory_pools);
        self
    }

    /// Port of `writeSatisfiableBranchCached` — forwards to the owning cache facade.
    pub fn write_satisfiable_branch_cached(
        &mut self,
        signature: Cint64,
        cache_value_list: Cint64,
        branched_list: Cint64,
        memory_pools: Cint64,
    ) -> &mut Self {
        // W6-DEFER[api]: mCache->writeSatisfiableBranchCached(signature, cacheValueList, branchedList, memoryPools);
        let _ = (signature, cache_value_list, branched_list, memory_pools);
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
        cache_value_list: Cint64,
        // KONCLUDE-PORT-NOTE[memory-pool]: `CCACHINGHASH<cint64,cint64>* mDepHash`.
        /// `mDepHash`.
        dep_hash: Cint64,
    },
    /// Port of `CSignatureSatisfiableExpanderCacheEntrySatisfiableBranchWriteData`.
    SatisfiableBranch {
        /// `mSignature`.
        signature: Cint64,
        // KONCLUDE-PORT-NOTE[memory-pool]: `CCACHINGLIST<CCacheValue>* mCacheValueList`.
        /// `mCacheValueList`.
        cache_value_list: Cint64,
        // KONCLUDE-PORT-NOTE[memory-pool]: `CCACHINGLIST<CCacheValue>* mBranchedValueList`.
        /// `mBranchedValueList`.
        branched_value_list: Cint64,
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
        cache_value_list: Cint64,
        dep_hash: Cint64,
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
        cache_value_list: Cint64,
        branched_list: Cint64,
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

    /// Port of `getDepHash` (opaque CCACHINGHASH handle).
    pub fn get_dep_hash(&self) -> Cint64 {
        if let SigExpanderEntryWriteDataKind::Expand { dep_hash, .. } = &self.kind {
            *dep_hash
        } else {
            0
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
    pub fn get_branched_value_list(&self) -> Cint64 {
        if let SigExpanderEntryWriteDataKind::SatisfiableBranch { branched_value_list, .. } = &self.kind {
            *branched_value_list
        } else {
            0
        }
    }

    /// Port of `getCacheValueList` (shared name across both subclasses; opaque CCACHINGLIST handle).
    pub fn get_cache_value_list(&self) -> Cint64 {
        match &self.kind {
            SigExpanderEntryWriteDataKind::Expand { cache_value_list, .. } => *cache_value_list,
            SigExpanderEntryWriteDataKind::SatisfiableBranch { cache_value_list, .. } => *cache_value_list,
            SigExpanderEntryWriteDataKind::Base => 0,
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

    /// Port of `CLinkerBase::getCount` over the write-data chain.
    pub fn get_count(&self) -> Cint64 {
        // KONCLUDE-PORT-NOTE[api]: C++ walks the next chain counting every node (including self).
        // The chain walk needs the write-data arena, not threaded into this wave.
        let mut linker_count: Cint64 = 0;
        // W6-DEFER[api]: while (itemLinker) { ++linkerCount; itemLinker = itemLinker->getNext(); }
        linker_count += 1; // self
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
    pub sig_item_hash: Cint64,
    // KONCLUDE-PORT-NOTE[memory-pool]: `CCACHINGSET<cint64>* mIncompatibleSigSet`.
    /// `CSignatureSatisfiableExpanderCache::mIncompatibleSigSet`.
    pub incompatible_sig_set: Cint64,
    // KONCLUDE-PORT-NOTE[memory-pool]: `CCACHINGSET<cint64>* mAlreadyExpSigSet`.
    /// `CSignatureSatisfiableExpanderCache::mAlreadyExpSigSet`.
    pub already_exp_sig_set: Cint64,
    // KONCLUDE-PORT-NOTE[memory-pool]: `CCACHINGHASH<…Hasher,…RedirectionItem*>* mHasherItemHash`
    // (the header marks this "currently not used").
    /// `CSignatureSatisfiableExpanderCache::mHasherItemHash`.
    pub hasher_item_hash: Cint64,
    // KONCLUDE-PORT-NOTE[memory-pool]: `CCACHINGHASH<cint64,cint64>* mSignatureReferCountSet`.
    /// `CSignatureSatisfiableExpanderCache::mSignatureReferCountSet`.
    pub signature_refer_count_set: Cint64,
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
            sig_item_hash: 0,
            incompatible_sig_set: 0,
            already_exp_sig_set: 0,
            hasher_item_hash: 0,
            signature_refer_count_set: 0,
            next_cache_entry_required_signature_ref_count: 0,
            next_memory_level_required_signature_ref_count: 0,
            next_cache_entry_required_signature_reference_count_increase: 0,
            next_memory_level_increase_for_required_signature_reference_count: 0,
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
    /// writer thread. Containers stay opaque `Cint64`; config reads + thread start are
    /// W6-DEFER[api]/[threading].
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `getCacheStatistics` (opaque `CCacheStatistics` handle).
    pub fn get_cache_statistics(&self) -> Cint64 {
        self.cache_stat
    }

    /// Port of `createCacheReader`.
    pub fn create_cache_reader(&mut self) -> SigExpanderCacheReaderId {
        // KONCLUDE-PORT-NOTE[api]: `new CSignatureSatisfiableExpanderCacheReader()`; the reader
        // arena is not threaded into this wave.
        // KONCLUDE-PORT-NOTE[threading]: mReaderSyncMutex lock/unlock — single-threaded inline.
        let reader = SigExpanderCacheReaderId::NONE; // W6-DEFER[api]: allocate the reader
        // W6-DEFER[api]: mReaderLinker = reader->append(mReaderLinker); (prepend, needs reader arena)
        reader
    }

    /// Port of `createCacheWriter`.
    pub fn create_cache_writer(&mut self) -> Cint64 {
        // W6-DEFER[api]: `new CSignatureSatisfiableExpanderCacheWriter(this)`; writer not arena-tracked.
        0
    }

    /// Port of protected `isCachingDataExpandable`.
    /// KONCLUDE-PORT-NOTE[api]: `context` is the by-value `self.context`; `cacheValueList` and the
    /// `mIncompatibleSigSet` / tag hash are opaque container handles.
    fn is_caching_data_expandable(
        &self,
        entry: SigExpanderCacheEntryId,
        signature: Cint64,
        cache_value_list: Cint64,
    ) -> bool {
        // KONCLUDE-PORT-NOTE[api]: `mIncompatibleSigSet->contains(signature) || entry->hasMultipleExpanded()`.
        // W6-DEFER[api]: opaque-set lookup + entry-arena deref. Default branch (the non-incompatible
        // path) only drains `cacheValueList` and returns true.
        let incompatible_or_multiple_expanded = false; // W6-DEFER[api]
        if incompatible_or_multiple_expanded {
            // W6-DEFER[api]: tagHash = entry->getTagExpanderCacheValueHash(); prevCount = entry->getExpanderCacheValueCount();
            // while (prevCount-- > 0 && !cacheValueList->isEmpty()) {
            //   cacheValue = cacheValueList->takeFirst(); tag = cacheValue.getTag();
            //   contCacheValue = tagHash->value(tag);
            //   if (!contCacheValue || *contCacheValue->getCacheValue() != cacheValue) return false;
            // }
        } else {
            // W6-DEFER[api]: prevCount = entry->getExpanderCacheValueCount();
            // while (prevCount-- > 0 && !cacheValueList->isEmpty()) { cacheValueList->takeFirst(); }
        }
        let _ = (entry, signature, cache_value_list);
        true
    }

    /// Port of the void overload of `writeExpanderCachingData` (entry-based).
    fn write_expander_caching_data_entry(
        &mut self,
        entry: SigExpanderCacheEntryId,
        extending: bool,
        cache_value_list: Cint64,
        dep_hash: Cint64,
    ) {
        // KONCLUDE-PORT-NOTE[api][memory-pool]: this body clones the tag hash, allocates an
        // CExpanderCacheValueLinker per fresh tag, resolves expander dependencies (recursing via
        // addExpanderCachingData), threads them into a head→tail chain, then stores the new tag hash
        // + linker chain on `entry`. Every step touches opaque CCACHING containers / the pool
        // allocator / the linker arena, none threaded into this wave.
        // W6-DEFER[api]: newTagHash = clone(entry->getTagExpanderCacheValueHash());
        // W6-DEFER[api]: mCacheStat.incCacheEntriesCount();
        // W6-DEFER[api]: for each cacheValue in cacheValueList: allocate linker, wire deps via
        //                self.add_expander_caching_data(...), append to chain.
        // W6-DEFER[api]: entry->setTagExpanderCacheValueHash(newTagHash);
        // W6-DEFER[api]: entry->appendExpanderCacheValueLinker(firstExpCacheValueLinker);
        let _ = (entry, extending, cache_value_list, dep_hash);
    }

    /// Port of protected `addExpanderCachingData` (the recursive dependency builder).
    fn add_expander_caching_data(
        &mut self,
        cache_value: CCacheValue,
        new_tag_hash: Cint64,
        dep_hash: Cint64,
        tag_cache_value_hash: Cint64,
    ) {
        // KONCLUDE-PORT-NOTE[api]: faithful recursion in C++:
        //   if (!newTagHash->contains(tag)) { allocate linker; for each dep of tag, if dep linker
        //     missing recurse addExpanderCachingData(depCacheValue,...); add dependency; insert
        //     linker into newTagHash; splice onto the first/last linker chain. }
        // `lastExpCacheValueLinker` / `firstExpCacheValueLinker` are C++ out-params threading the
        // built chain; in the port they belong to the linker arena (not threaded this wave).
        // W6-DEFER[api]: whole body needs the opaque tag hashes + the CExpanderCacheValueLinker arena.
        let _ = (cache_value, new_tag_hash, dep_hash, tag_cache_value_hash);
    }

    /// Port of the bool overload of `writeExpanderCachingData` (signature-based).
    fn write_expander_caching_data_sig(
        &mut self,
        prev_signature: Cint64,
        new_signature: Cint64,
        cache_value_list: Cint64,
        dep_hash: Cint64,
    ) -> bool {
        if self.can_create_cache_entry_for_signature(new_signature) {
            // W6-DEFER[api]: if (!mSigItemHash->contains(newSignature)) { ... } else { mIncompatibleSigSet->insert(newSignature); }
            let sig_item_hash_contains_new = false; // W6-DEFER[api]: mSigItemHash->contains(newSignature)
            if !sig_item_hash_contains_new {
                let mut entry = SigExpanderCacheEntryId::NONE;
                if prev_signature != 0 {
                    // W6-DEFER[api]: prevSigItem = mSigItemHash->value(prevSignature);
                    let prev_sig_item = SigExpanderRedirectionItemId::NONE;
                    if prev_sig_item.is_some() {
                        // W6-DEFER[api]: entry = prevSigItem->getCacheEntry();
                        if !self.is_caching_data_expandable(entry, prev_signature, cache_value_list) {
                            // not compatible, only identical signatures
                            // W6-DEFER[api]: mIncompatibleSigSet->insert(prevSignature);
                            return false;
                        }
                        // W6-DEFER[api]: if (mAlreadyExpSigSet->contains(prevSignature)) entry->setMultipleExpanded(true);
                    }
                }

                if entry.is_none() {
                    // W6-DEFER[api][memory-pool]: entry = allocateAndConstruct CSignatureSatisfiableExpanderCacheEntry(context);
                }

                self.write_expander_caching_data_entry(entry, prev_signature != 0, cache_value_list, dep_hash);
                // W6-DEFER[api][memory-pool]: sigItem = allocate CSignatureSatisfiableExpanderCacheRedirectionItem;
                // W6-DEFER[api]: sigItem->initRedirectionItem(entry, newSignature, entry->getExpanderCacheValueCount());
                // W6-DEFER[api]: mSigItemHash->insert(newSignature, sigItem);
                // W6-DEFER[api]: mAlreadyExpSigSet->insert(prevSignature);
                return true;
            } else {
                // W6-DEFER[api]: mIncompatibleSigSet->insert(newSignature);
            }
        }
        false
    }

    /// Port of protected `writeSatisfiableBranchedCachingData`.
    fn write_satisfiable_branched_caching_data(
        &mut self,
        signature: Cint64,
        cache_value_list: Cint64,
        branched_value_list: Cint64,
    ) -> bool {
        // W6-DEFER[api]: sSigItem = mSigItemHash->value(signature);
        let s_sig_item = SigExpanderRedirectionItemId::NONE;
        if s_sig_item.is_some() {
            // W6-DEFER[api]: entry = sSigItem->getCacheEntry();
            let entry = SigExpanderCacheEntryId::NONE;

            if self.is_caching_data_expandable(entry, signature, cache_value_list) {
                // W6-DEFER[api]: if (!branchedValueList || branchedValueList->isEmpty())
                let branched_empty = branched_value_list == 0; // W6-DEFER[api]: || branchedValueList->isEmpty()
                if branched_empty {
                    // W6-DEFER[api]: entry->setSatisfiableWithoutBranchedConcepts(true);
                } else {
                    // W6-DEFER[api][memory-pool]: expBranch = allocate CExpanderBranchedLinker(context);
                    // W6-DEFER[api]: for cacheValue in branchedValueList: expBranch->appendCacheValue(cacheValue);
                    // W6-DEFER[api]: entry->appendExpanderBranchedLinker(expBranch);
                }
                // W6-DEFER[api]: entry->setSatisfiable(true);
                return true;
            }
        }
        false
    }

    /// Port of protected `createReaderSlotUpdate`.
    fn create_reader_slot_update(&mut self) {
        // KONCLUDE-PORT-NOTE[memory-pool][api]: allocates a slot from the pool, deep-copies
        // mSigItemHash into the slot's signature hash, links the slot into mSlotLinker, and pushes
        // it to every registered reader (incReader + updateSlot). All over opaque pools / arenas.
        // W6-DEFER[memory-pool]: slot = allocateWithMemoryPool CSignatureSatisfiableExpanderCacheSlotItem;
        // W6-DEFER[api]: slotSigItemHash = detached copy of mSigItemHash; slot->setSignatureItemHash(slotSigItemHash);
        // W6-DEFER[api]: append slot to mSlotLinker (or set as head);
        // W6-DEFER[api]: for readerLinkerIt in mReaderLinker { slot->incReader(); readerLinkerIt->updateSlot(slot); }
    }

    /// Port of protected `cleanUnusedSlots`.
    fn clean_unused_slots(&mut self) {
        // KONCLUDE-PORT-NOTE[api][memory-pool]: walks mSlotLinker unlinking every slot with no
        // readers and releasing its pooled memory. Needs the slot arena + pool manager.
        // W6-DEFER[api]: slotLinkerIt = mSlotLinker; lastSlotLinker = nullptr;
        // W6-DEFER[api]: while (slotLinkerIt) { if (!slotLinkerIt->hasCacheReaders()) unlink + releasePools; advance }
    }

    /// Port of `writeCachedData` (facade entry; staged single-threaded inline drain).
    pub fn write_cached_data(&mut self, write_data: SigExpanderEntryWriteDataId, memory_pools: Cint64) -> &mut Self {
        // KONCLUDE-PORT-NOTE[threading]: the shipped C++ default posts a CWriteCachedDataEvent to the
        // writer thread; the staged single-threaded port drains inline (== the DIRECT_WRITING branch).
        let mut data_linker_it = write_data;
        let mut all_caching_success = true;
        let mut one_caching_success = false;
        let mut one_caching_exp_success = false;
        while data_linker_it.is_some() {
            // KONCLUDE-PORT-NOTE[api]: dispatch each write-data node by its type to
            // write_expander_caching_data_sig / write_satisfiable_branched_caching_data.
            // W6-DEFER[api]: resolving the node's kind/payload + getNext needs the write-data arena.
            let cached = false; // W6-DEFER[api]
            all_caching_success &= cached;
            one_caching_success |= cached;
            one_caching_exp_success |= cached;
            data_linker_it = SigExpanderEntryWriteDataId::NONE;
        }

        if one_caching_exp_success {
            self.create_reader_slot_update();
            self.clean_unused_slots();
        }
        let _ = (all_caching_success, one_caching_success, memory_pools);
        self
    }

    /// Port of `writeExpandCached` (facade entry; staged single-threaded inline drain).
    pub fn write_expand_cached(
        &mut self,
        prev_signature: Cint64,
        new_signature: Cint64,
        cache_value_list: Cint64,
        dep_hash: Cint64,
        memory_pools: Cint64,
    ) -> &mut Self {
        // KONCLUDE-PORT-NOTE[threading]: shipped default posts CWriteExpandCachedEvent; inline here.
        if self.write_expander_caching_data_sig(prev_signature, new_signature, cache_value_list, dep_hash) {
            self.create_reader_slot_update();
            self.clean_unused_slots();
        }
        let _ = memory_pools;
        self
    }

    /// Port of `writeSatisfiableBranchCached` (facade entry; staged single-threaded inline drain).
    pub fn write_satisfiable_branch_cached(
        &mut self,
        signature: Cint64,
        cache_value_list: Cint64,
        branched_list: Cint64,
        memory_pools: Cint64,
    ) -> &mut Self {
        // KONCLUDE-PORT-NOTE[threading]: shipped default posts CWriteSatisfiableBranchCachedEvent; inline here.
        self.write_satisfiable_branched_caching_data(signature, cache_value_list, branched_list);
        let _ = memory_pools;
        self
    }

    /// Port of virtual `processCustomsEvents`.
    /// KONCLUDE-PORT-NOTE[threading]: the cross-thread writer drain. The staged single-threaded port
    /// keeps the dispatch skeleton; the `CCustomEvent` payloads are opaque, so each branch defers its
    /// payload extraction and forwards to the matching sibling, mirroring the C++ control flow.
    fn process_customs_events(&mut self, type_: Cint64, event: Cint64) -> bool {
        // W6-DEFER[threading]: if (CThread::processCustomsEvents(type,event)) return true;
        if type_ == super::value::event::WRITE_EXPAND_CACHED_ENTRY {
            // W6-DEFER[api]: extract prevSignature/newSignature/cacheValueList/depHash/memoryPools from event.
            if self.write_expander_caching_data_sig(0, 0, 0, 0) {
                self.create_reader_slot_update();
                self.clean_unused_slots();
            }
            // W6-DEFER[memory-pool]: mContext.getMemoryPoolAllocationManager()->releaseTemporaryMemoryPools(memoryPools);
            return true;
        } else if type_ == super::value::event::WRITE_SATISFIABLE_BRANCH_CACHED_ENTRY {
            // W6-DEFER[api]: extract signature/cacheValueList/branchedValueList/memoryPools from event.
            self.write_satisfiable_branched_caching_data(0, 0, 0);
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

                let mut data_linker_it = self.collect_write_data;
                let mut all_caching_success = true;
                let mut one_caching_success = false;
                let mut one_caching_exp_success = false;
                while data_linker_it.is_some() {
                    // W6-DEFER[api]: dispatch each node by type (see writeCachedData); getNext needs arena.
                    let cached = false; // W6-DEFER[api]
                    all_caching_success &= cached;
                    one_caching_success |= cached;
                    one_caching_exp_success |= cached;
                    data_linker_it = SigExpanderEntryWriteDataId::NONE;
                }

                if one_caching_exp_success {
                    self.create_reader_slot_update();
                    self.clean_unused_slots();
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
        // KONCLUDE-PORT-NOTE[api]: C++ does `cint64& refCount = (*mSignatureReferCountSet)[signature]; ++refCount;`
        // mSignatureReferCountSet is an opaque CCACHINGHASH handle in this wave.
        let ref_count: Cint64 = 0; // W6-DEFER[api]: ++(*mSignatureReferCountSet)[signature]
        let _ = signature;
        if ref_count >= self.get_required_signature_refer_count_for_next_cache_entry_creation() {
            return true;
        }
        false
    }
}
