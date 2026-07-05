//! `cache::reuse` — F4 reuse-completion-graph cache (Konclude
//! `Reasoner/Kernel/Cache/CReuseCompletionGraph*`).
//!
//! Caches whole completion-graph fragments so a later satisfiability test can
//! reuse an already-expanded graph instead of re-saturating. Driven by the
//! Algorithm-layer `CCompletionGraphCacheHandler` / `CReuseCompletionGraphCacheHandler`
//! (stubbed in `completion/stubs.rs`); this file provides the cache facade +
//! Reader + Writer + Entry storage they talk to.
//!
//! STRUCT-DEFINITION wave only: faithful fields, `new`/`Default`, NO method
//! bodies (each impl carries a `// W6-CACHE method-batch` marker).
//!
//! KONCLUDE-PORT-NOTE[threading]: this whole subtree is the cross-thread shared
//! surface. `QMutex`/`QSemaphore`/`QAtomicInt`/`QAtomicPointer` become opaque
//! `Cint64` handles for the struct wave; the Reader/Writer/event boundary is
//! preserved so real concurrency can be re-enabled later (per manifest §concurrency).
//! KONCLUDE-PORT-NOTE[memory-pool]: pool allocators / `CMemoryPool*` / freelists
//! become opaque `Cint64`; `CCACHINGHASH/SET/LIST` collapse to `HashMap`/`Vec`.
//! KONCLUDE-PORT-NOTE[ownership]: raw `CXxx*` back-pointers become typed arena
//! `Id`s, or opaque `Cint64` where they cross a family/subtree boundary.

#![allow(dead_code)]

use std::collections::{HashMap, HashSet};

use super::super::model::substrate::{Cint64, Id, NegLink, INVALID};
use super::super::model::ConceptId;
// F0 base, ported in `cache/base.rs`.
use super::base::CompletionGraphCache;
use super::context::CacheContext;

// ===========================================================================
// F4-local arena id aliases (the `CXxx*` → `Id<T>` replacement, PORT.md §5).
// ===========================================================================

/// `CReuseCompletionGraphCacheEntry*`       → `ReuseCacheEntryId`.
pub type ReuseCacheEntryId = Id<ReuseCompletionGraphCacheEntry>;
/// `CReuseCompletionGraphCacheSlotItem*`    → `ReuseCacheSlotItemId`.
pub type ReuseCacheSlotItemId = Id<ReuseCompletionGraphCacheSlotItem>;
/// `CReuseCompletionGraphCacheReader*`      → `ReuseCacheReaderId`.
pub type ReuseCacheReaderId = Id<ReuseCompletionGraphCacheReader>;
/// `CReuseCompletionGraphCompatibilityEntryHash*` → `CompatibilityEntryHashId`.
pub type CompatibilityEntryHashId = Id<ReuseCompletionGraphCompatibilityEntryHash>;

/// Cross-family alias for `CCacheValue` (F0, `cache/value.rs`, not yet ported).
/// KONCLUDE-PORT-NOTE[api]: opaque `Cint64` placeholder for the generic hashed
/// cache key; replace with the real `CacheValue` type when F0 lands.
pub type CacheValue = Cint64;

/// Cross-subtree alias for `CSatisfiableCalculationJobInstantiation*` (Task/).
/// KONCLUDE-PORT-NOTE[ownership]: opaque `Cint64`; lives outside this subtree.
pub type JobInstantiation = Cint64;

// ===========================================================================
// CReuseCompletionGraphCacheContext — per-cache memory context (CContext).
// ===========================================================================

/// Port of `CReuseCompletionGraphCacheContext : public CContext`.
#[derive(Debug, Clone)]
pub struct ReuseCompletionGraphCacheContext {
    /// `CMemoryPoolAllocationManager* mMemMan`.
    /// KONCLUDE-PORT-NOTE[memory-pool]: opaque pool-allocator handle.
    pub mem_man: Cint64,
    /// `CMemoryPoolProvider* mMemoryPoolProvider`.
    /// KONCLUDE-PORT-NOTE[memory-pool]: opaque pool-provider handle.
    pub memory_pool_provider: Cint64,
}

impl ReuseCompletionGraphCacheContext {
    pub fn new() -> Self {
        ReuseCompletionGraphCacheContext {
            mem_man: INVALID,
            memory_pool_provider: INVALID,
        }
    }
    // W6-CACHE method-batch

    /// Port of `getMemoryPoolAllocationManager`.
    /// KONCLUDE-PORT-NOTE[memory-pool]: returns the opaque pool-allocator handle
    /// (C++ ctor news a `CLimitedReserveMemoryPoolAllocationManager`).
    pub fn get_memory_pool_allocation_manager(&self) -> Cint64 {
        self.mem_man
    }

    /// Port of `getMemoryAllocationManager` (returns the same pool manager).
    pub fn get_memory_allocation_manager(&self) -> Cint64 {
        self.mem_man
    }

    /// Port of `getMemoryPoolProvider`.
    /// KONCLUDE-PORT-NOTE[memory-pool]: opaque pool-provider handle.
    pub fn get_memory_pool_provider(&self) -> Cint64 {
        self.memory_pool_provider
    }
}

impl Default for ReuseCompletionGraphCacheContext {
    fn default() -> Self {
        ReuseCompletionGraphCacheContext::new()
    }
}

// ===========================================================================
// CReuseCompletionGraphCompatibilityEntryHashData — per-key entry linkers.
// ===========================================================================

/// Port of `CReuseCompletionGraphCompatibilityEntryHashData`.
///
/// The value stored per `CCacheValue` key in the compatibility hash: two
/// intrusive entry chains (entailed / incompatible).
/// KONCLUDE-PORT-NOTE[ownership]: `CXLinker<CReuseCompletionGraphCacheEntry*>*`
/// chains → owned `Vec<ReuseCacheEntryId>`, head-at-FRONT (CLinker convention).
#[derive(Debug, Clone)]
pub struct ReuseCompletionGraphCompatibilityEntryHashData {
    /// `mEntailedEntryLinker`.
    pub entailed_entry_linker: Vec<ReuseCacheEntryId>,
    /// `mIncompatibleEntryLinker`.
    pub incompatible_entry_linker: Vec<ReuseCacheEntryId>,
}

impl ReuseCompletionGraphCompatibilityEntryHashData {
    pub fn new() -> Self {
        ReuseCompletionGraphCompatibilityEntryHashData {
            entailed_entry_linker: Vec::new(),
            incompatible_entry_linker: Vec::new(),
        }
    }
    // W6-CACHE method-batch

    /// Port of `getEntailedEntryLinker`.
    /// KONCLUDE-PORT-NOTE[ownership]: the chain as a head→tail slice (head-front Vec).
    pub fn get_entailed_entry_linker(&self) -> &[ReuseCacheEntryId] {
        &self.entailed_entry_linker
    }

    /// Port of `addEntailedEntyLinker` (`mEntailedEntryLinker = linker->append(mEntailedEntryLinker)`:
    /// the new node is prepended — head-at-FRONT per PORT.md §6).
    pub fn add_entailed_enty_linker(&mut self, entry: ReuseCacheEntryId) -> &mut Self {
        self.entailed_entry_linker.insert(0, entry);
        self
    }

    /// Port of `getIncompatibleEntryLinker`.
    pub fn get_incompatible_entry_linker(&self) -> &[ReuseCacheEntryId] {
        &self.incompatible_entry_linker
    }

    /// Port of `addIncompatibleEntyLinker` (head-front prepend).
    pub fn add_incompatible_enty_linker(&mut self, entry: ReuseCacheEntryId) -> &mut Self {
        self.incompatible_entry_linker.insert(0, entry);
        self
    }
}

impl Default for ReuseCompletionGraphCompatibilityEntryHashData {
    fn default() -> Self {
        ReuseCompletionGraphCompatibilityEntryHashData::new()
    }
}

// ===========================================================================
// CReuseCompletionGraphCompatibilityEntryHash — the CacheValue→data hash.
// ===========================================================================

/// Port of
/// `CReuseCompletionGraphCompatibilityEntryHash : public CCACHINGHASH<CCacheValue,CReuseCompletionGraphCompatibilityEntryHashData>`.
///
/// KONCLUDE-PORT-NOTE[memory-pool]/[threading]: `CCACHINGHASH`
/// (`CQtManagedRestrictedModificationHash`) collapses to a `HashMap` gated by a
/// tagging-pool generation counter (deferred to F0); the `CContext*` ctor arg is
/// kept as an opaque back-handle.
#[derive(Debug, Clone)]
pub struct ReuseCompletionGraphCompatibilityEntryHash {
    /// The managed-modification hash body.
    pub map: HashMap<CacheValue, ReuseCompletionGraphCompatibilityEntryHashData>,
    /// `CContext* context` ctor argument.
    /// KONCLUDE-PORT-NOTE[ownership]: opaque back-handle to the owning context.
    pub context: Cint64,
}

impl ReuseCompletionGraphCompatibilityEntryHash {
    pub fn new() -> Self {
        ReuseCompletionGraphCompatibilityEntryHash {
            map: HashMap::new(),
            context: INVALID,
        }
    }
    // W6-CACHE method-batch

    /// Port of `CReuseCompletionGraphCompatibilityEntryHash(CContext* context)`.
    /// KONCLUDE-PORT-NOTE[memory-pool]: the `CCACHINGHASH` body collapses to a
    /// `HashMap`; the `CContext*` is kept as an opaque back-handle.
    pub fn new_with_context(context: Cint64) -> Self {
        ReuseCompletionGraphCompatibilityEntryHash {
            map: HashMap::new(),
            context,
        }
    }

    /// `CCACHINGHASH::value(key)` surface (read; absent key → default data).
    /// KONCLUDE-PORT-NOTE[memory-pool]: inherited managed-modification-hash method.
    pub fn value(&self, key: &CacheValue) -> ReuseCompletionGraphCompatibilityEntryHashData {
        self.map.get(key).cloned().unwrap_or_default()
    }

    /// `CCACHINGHASH::operator[](key)` surface (insert-or-get the mutable data).
    pub fn get_or_create_mut(
        &mut self,
        key: CacheValue,
    ) -> &mut ReuseCompletionGraphCompatibilityEntryHashData {
        self.map.entry(key).or_default()
    }
}

impl Default for ReuseCompletionGraphCompatibilityEntryHash {
    fn default() -> Self {
        ReuseCompletionGraphCompatibilityEntryHash::new()
    }
}

// ===========================================================================
// CReuseCompletionGraphCacheEntry — one cached completion-graph fragment.
// ===========================================================================

/// Port of `CReuseCompletionGraphCacheEntry`.
#[derive(Debug, Clone)]
pub struct ReuseCompletionGraphCacheEntry {
    /// `CReuseCompletionGraphCacheContext* mContext`.
    /// KONCLUDE-PORT-NOTE[ownership]: opaque back-handle to the owning context.
    pub context: Cint64,
    /// `cint64 mEntryID`.
    pub entry_id: Cint64,
    /// `bool mMinimal`.
    pub minimal: bool,
    /// `CCACHINGSET<CCacheValue> mIncompatibleValues`.
    /// KONCLUDE-PORT-NOTE[memory-pool]: caching-set → owned `Vec`.
    pub incompatible_values: Vec<CacheValue>,
    /// `CCACHINGSET<CCacheValue> mEntailedValues`.
    pub entailed_values: Vec<CacheValue>,
    /// `CCACHINGSET<CCacheValue> mMinimalValues`.
    pub minimal_values: Vec<CacheValue>,
    /// `CSatisfiableCalculationJobInstantiation* mJobInstance`.
    pub job_instance: JobInstantiation,
}

impl ReuseCompletionGraphCacheEntry {
    pub fn new() -> Self {
        ReuseCompletionGraphCacheEntry {
            context: INVALID,
            entry_id: INVALID,
            minimal: false,
            incompatible_values: Vec::new(),
            entailed_values: Vec::new(),
            minimal_values: Vec::new(),
            job_instance: INVALID,
        }
    }
    // W6-CACHE method-batch

    /// Port of `getIncompatibleValues`.
    pub fn get_incompatible_values(&self) -> &Vec<CacheValue> {
        &self.incompatible_values
    }
    /// Port of `getEntailedValues`.
    pub fn get_entailed_values(&self) -> &Vec<CacheValue> {
        &self.entailed_values
    }
    /// Port of `getMinimalValues`.
    pub fn get_minimal_values(&self) -> &Vec<CacheValue> {
        &self.minimal_values
    }
    /// Port of `getJobInstantiation`.
    pub fn get_job_instantiation(&self) -> JobInstantiation {
        self.job_instance
    }

    /// Port of `setJobInstantiation`.
    pub fn set_job_instantiation(&mut self, job_instantiation: JobInstantiation) -> &mut Self {
        self.job_instance = job_instantiation;
        self
    }

    /// Port of `setEntailedValues` (`mEntailedValues += *valueSet`: set union).
    /// KONCLUDE-PORT-NOTE[memory-pool]: `CCACHINGSET` → head-order `Vec` with
    /// set-insert (skip-if-present) semantics.
    pub fn set_entailed_values(&mut self, value_set: &[CacheValue]) -> &mut Self {
        for &v in value_set {
            if !self.entailed_values.contains(&v) {
                self.entailed_values.push(v);
            }
        }
        self
    }
    /// Port of `addEntailedValue` (`mEntailedValues.insert(...)`).
    pub fn add_entailed_value(&mut self, cache_value: CacheValue) -> &mut Self {
        if !self.entailed_values.contains(&cache_value) {
            self.entailed_values.push(cache_value);
        }
        self
    }

    /// Port of `setIncompatibleValues`.
    pub fn set_incompatible_values(&mut self, value_set: &[CacheValue]) -> &mut Self {
        for &v in value_set {
            if !self.incompatible_values.contains(&v) {
                self.incompatible_values.push(v);
            }
        }
        self
    }
    /// Port of `addIncompatibleValue`.
    pub fn add_incompatible_value(&mut self, cache_value: CacheValue) -> &mut Self {
        if !self.incompatible_values.contains(&cache_value) {
            self.incompatible_values.push(cache_value);
        }
        self
    }

    /// Port of `setMinimalValues`.
    pub fn set_minimal_values(&mut self, value_set: &[CacheValue]) -> &mut Self {
        for &v in value_set {
            if !self.minimal_values.contains(&v) {
                self.minimal_values.push(v);
            }
        }
        self
    }
    /// Port of `addMinimalValue`.
    pub fn add_minimal_value(&mut self, cache_value: CacheValue) -> &mut Self {
        if !self.minimal_values.contains(&cache_value) {
            self.minimal_values.push(cache_value);
        }
        self
    }
    /// Port of `hasMinimalValue` (`mMinimalValues.contains(...)`).
    pub fn has_minimal_value(&self, cache_value: CacheValue) -> bool {
        self.minimal_values.contains(&cache_value)
    }

    /// Port of `setEntryID`.
    pub fn set_entry_id(&mut self, id: Cint64) -> &mut Self {
        self.entry_id = id;
        self
    }
    /// Port of `getEntryID`.
    pub fn get_entry_id(&self) -> Cint64 {
        self.entry_id
    }
}

impl Default for ReuseCompletionGraphCacheEntry {
    fn default() -> Self {
        ReuseCompletionGraphCacheEntry::new()
    }
}

// ===========================================================================
// CReuseCompletionGraphCacheEntry{,Expand}WriteData — RECORD FAMILY → enum.
// ===========================================================================

/// Port of the F4 entry write-data record family, collapsed to one tagged enum
/// (mirrors the W2 `DepKind` collapse; manifest §record-families):
///   * `Base`   ← `CReuseCompletionGraphCacheEntryWriteData : CCacheEntryWriteData`
///                (empty derived payload base — its `CCacheEntryWriteData` fields
///                are F0 cross-family, kept opaque).
///   * `Expand` ← `CReuseCompletionGraphCacheEntryExpandWriteData`.
#[derive(Debug, Clone)]
pub enum ReuseCacheEntryWriteData {
    /// Port of `CReuseCompletionGraphCacheEntryWriteData`.
    Base,
    /// Port of `CReuseCompletionGraphCacheEntryExpandWriteData`.
    Expand {
        /// `CSatisfiableCalculationJobInstantiation* mJobInstantiation`.
        job_instantiation: JobInstantiation,
        /// `CCACHINGLIST<CCacheValue>* mCacheValueList`.
        cache_value_list: Vec<CacheValue>,
        /// `CCACHINGLIST<CCacheValue>* mMinimalValueList`.
        minimal_value_list: Vec<CacheValue>,
    },
}

impl ReuseCacheEntryWriteData {
    pub fn new() -> Self {
        ReuseCacheEntryWriteData::Base
    }
    // W6-CACHE method-batch

    /// Port of `CReuseCompletionGraphCacheEntryExpandWriteData::initExpandWriteData`
    /// (sets the payload and `mType = REUSECOMPLETIONGRAPHWRITEEXPANDDATATYPE`; in
    /// the collapsed enum the `Expand` variant IS that discriminant).
    pub fn init_expand_write_data(
        cache_value_list: Vec<CacheValue>,
        minimal_value_list: Vec<CacheValue>,
        job_instantiation: JobInstantiation,
    ) -> Self {
        ReuseCacheEntryWriteData::Expand {
            job_instantiation,
            cache_value_list,
            minimal_value_list,
        }
    }

    /// Port of `getCacheValueList` (Expand payload; `None` for the base record).
    pub fn get_cache_value_list(&self) -> Option<&Vec<CacheValue>> {
        match self {
            ReuseCacheEntryWriteData::Expand {
                cache_value_list, ..
            } => Some(cache_value_list),
            _ => None,
        }
    }
    /// Port of `getMinimalCacheValueList`.
    pub fn get_minimal_cache_value_list(&self) -> Option<&Vec<CacheValue>> {
        match self {
            ReuseCacheEntryWriteData::Expand {
                minimal_value_list, ..
            } => Some(minimal_value_list),
            _ => None,
        }
    }
    /// Port of `getJobInstantiation`.
    pub fn get_job_instantiation(&self) -> JobInstantiation {
        match self {
            ReuseCacheEntryWriteData::Expand {
                job_instantiation, ..
            } => *job_instantiation,
            _ => INVALID,
        }
    }

    /// `getCacheWriteDataType() == REUSECOMPLETIONGRAPHWRITEEXPANDDATATYPE`.
    pub fn is_expand(&self) -> bool {
        matches!(self, ReuseCacheEntryWriteData::Expand { .. })
    }
}

impl Default for ReuseCacheEntryWriteData {
    fn default() -> Self {
        ReuseCacheEntryWriteData::new()
    }
}

// ===========================================================================
// CReuseCompletionGraphCacheWriter — per-thread write facade.
// ===========================================================================

/// Port of `CReuseCompletionGraphCacheWriter`.
#[derive(Debug, Clone)]
pub struct ReuseCompletionGraphCacheWriter {
    /// `CReuseCompletionGraphCache* mCache`.
    /// KONCLUDE-PORT-NOTE[ownership]: opaque back-handle to the owning facade.
    pub cache: Cint64,
}

impl ReuseCompletionGraphCacheWriter {
    pub fn new() -> Self {
        ReuseCompletionGraphCacheWriter { cache: INVALID }
    }
    // W6-CACHE method-batch

    /// Port of `CReuseCompletionGraphCacheWriter(CReuseCompletionGraphCache* cache)`.
    /// KONCLUDE-PORT-NOTE[ownership]: `mCache` opaque back-handle to the facade.
    pub fn new_with_cache(cache: Cint64) -> Self {
        ReuseCompletionGraphCacheWriter { cache }
    }

    /// Port of `writeExpandCache` (`mCache->writeExpandCache(writeData, memoryPools)`).
    pub fn write_expand_cache(
        &mut self,
        _write_data: &ReuseCacheEntryWriteData,
        _memory_pools: Cint64,
    ) -> &mut Self {
        // W6-DEFER[api]: mCache->writeExpandCache(writeData, memoryPools) — the
        // owning facade lives behind the opaque `cache` back-handle (cross-instance).
        self
    }
}

impl Default for ReuseCompletionGraphCacheWriter {
    fn default() -> Self {
        ReuseCompletionGraphCacheWriter::new()
    }
}

// ===========================================================================
// CReuseCompletionGraphCacheSlotItem — one open-addressing slot (linker node).
// ===========================================================================

/// Port of
/// `CReuseCompletionGraphCacheSlotItem : public CMemoryPoolContainer, public CLinkerBase<...>`.
///
/// KONCLUDE-PORT-NOTE[ownership]: the `CLinkerBase` intrusive `next` is dropped;
/// the slot chain is owned head-front by the facade's `slot_linker: Vec<..>`.
/// The `CMemoryPoolContainer` base (pool-bound allocation) is implicit under the
/// arena model.
#[derive(Debug, Clone)]
pub struct ReuseCompletionGraphCacheSlotItem {
    /// `CReuseCompletionGraphCompatibilityEntryHash* mEntryHash`.
    pub entry_hash: CompatibilityEntryHashId,
    /// `QAtomicInt mReaderSharingCount`.
    /// KONCLUDE-PORT-NOTE[threading]: opaque atomic reader-share counter.
    pub reader_sharing_count: Cint64,
    /// `bool mReaderUsing`.
    pub reader_using: bool,
    /// `cint64 mEntyCount`. (typo-faithful to the C++ member name.)
    pub enty_count: Cint64,
}

impl ReuseCompletionGraphCacheSlotItem {
    pub fn new() -> Self {
        ReuseCompletionGraphCacheSlotItem {
            entry_hash: Id::NONE,
            reader_sharing_count: 0,
            reader_using: false,
            enty_count: 0,
        }
    }
    // W6-CACHE method-batch

    /// Port of `incReader` (`mReaderSharingCount.ref()`).
    /// KONCLUDE-PORT-NOTE[threading]: `QAtomicInt::ref` → single-threaded inline
    /// increment; `ref()` is true iff the new value is non-zero.
    pub fn inc_reader(&mut self) -> bool {
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

    /// Port of `decReader` (`mReaderSharingCount.deref()`).
    /// KONCLUDE-PORT-NOTE[threading]: `QAtomicInt::deref` → single-threaded inline
    /// decrement; `deref()` is false iff the new value is zero.
    pub fn dec_reader(&mut self) -> bool {
        self.reader_sharing_count -= 1;
        if self.reader_sharing_count == 0 {
            self.reader_using = false;
        }
        self.reader_using
    }

    /// Port of `hasCacheReaders`.
    pub fn has_cache_readers(&self) -> bool {
        self.reader_using
    }

    /// Port of `setEntryHash`.
    pub fn set_entry_hash(&mut self, hash: CompatibilityEntryHashId) -> &mut Self {
        self.entry_hash = hash;
        self
    }
    /// Port of `getEntryHash`.
    pub fn get_entry_hash(&self) -> CompatibilityEntryHashId {
        self.entry_hash
    }
    /// Port of `getEntryCount`.
    pub fn get_entry_count(&self) -> Cint64 {
        self.enty_count
    }
    /// Port of `setEntryCount`.
    pub fn set_entry_count(&mut self, entry_count: Cint64) -> &mut Self {
        self.enty_count = entry_count;
        self
    }
}

impl Default for ReuseCompletionGraphCacheSlotItem {
    fn default() -> Self {
        ReuseCompletionGraphCacheSlotItem::new()
    }
}

// ===========================================================================
// CReuseCompletionGraphCacheReader — per-thread read cursor (linker node).
// ===========================================================================

/// Size of the per-connection-level test-concept linker ring.
/// Port of `static const cint64 mTestConceptLinkerVecSize = 4`.
pub const TEST_CONCEPT_LINKER_VEC_SIZE: usize = 4;

/// Port of the reader-local inner class
/// `CReuseCompletionGraphCacheReader::CCacheEntryVotingItem`.
///
/// Per-entry voting tallies the reader accumulates while scoring candidate cache
/// entries for reuse.
#[derive(Debug, Clone)]
pub struct CacheEntryVotingItem {
    /// `cint64 mIncompatibleCount`.
    pub incompatible_count: Cint64,
    /// `cint64 mEntailedCount`.
    pub entailed_count: Cint64,
    /// `cint64 mMissingCount`.
    pub missing_count: Cint64,
    /// `bool mTmpReferenced`.
    pub tmp_referenced: bool,
    /// `bool mMinimalFound`.
    pub minimal_found: bool,
    /// `cint64 mMinConnectionLevel`.
    pub min_connection_level: Cint64,
    /// `CReuseCompletionGraphCacheEntry* mEntry`.
    pub entry: ReuseCacheEntryId,
}

impl CacheEntryVotingItem {
    pub fn new() -> Self {
        CacheEntryVotingItem {
            incompatible_count: 0,
            entailed_count: 0,
            missing_count: 0,
            tmp_referenced: false,
            minimal_found: false,
            min_connection_level: TEST_CONCEPT_LINKER_VEC_SIZE as Cint64,
            entry: Id::NONE,
        }
    }
    // W6-CACHE method-batch

    /// Port of `CCacheEntryVotingItem::reset`.
    pub fn reset(&mut self) -> &mut Self {
        self.incompatible_count = 0;
        self.entailed_count = 0;
        self.missing_count = 0;
        self.tmp_referenced = false;
        self.minimal_found = false;
        self.entry = Id::NONE;
        self.min_connection_level = TEST_CONCEPT_LINKER_VEC_SIZE as Cint64;
        self
    }
}

impl Default for CacheEntryVotingItem {
    fn default() -> Self {
        CacheEntryVotingItem::new()
    }
}

/// Port of `CReuseCompletionGraphCacheReader : public CLinkerBase<...>`.
///
/// KONCLUDE-PORT-NOTE[ownership]: the `CLinkerBase` intrusive `next` is dropped;
/// the reader chain is owned head-front by the facade's `reader_linker: Vec<..>`.
#[derive(Debug, Clone)]
pub struct ReuseCompletionGraphCacheReader {
    /// `CReuseCompletionGraphCacheContext mContext` (held by value).
    pub context: ReuseCompletionGraphCacheContext,
    /// `CReuseCompletionGraphCacheSlotItem* mCurrentSlot`.
    pub current_slot: ReuseCacheSlotItemId,
    /// `QAtomicPointer<CReuseCompletionGraphCacheSlotItem> mUpdatedSlot`.
    pub updated_slot: ReuseCacheSlotItemId,
    /// `CXLinker<TConceptNegPair>* mFreeLinker`.
    /// KONCLUDE-PORT-NOTE[memory-pool]: opaque freelist head of reusable linker
    /// nodes.
    pub free_linker: Cint64,
    /// `QVector<CCacheEntryVotingItem> mEntryVotingVec`.
    pub entry_voting_vec: Vec<CacheEntryVotingItem>,
    /// `CXLinker<TConceptNegPair>* mTestConceptLinkerVec[mTestConceptLinkerVecSize]`.
    /// KONCLUDE-PORT-NOTE[ownership]: `TConceptNegPair = QPair<CConcept*,bool>`
    /// → `NegLink<ConceptId>`; each ring entry is a head-front owned chain.
    pub test_concept_linker_vec: [Vec<NegLink<ConceptId>>; TEST_CONCEPT_LINKER_VEC_SIZE],
    /// `cint64 mTestConceptLinkerCount`.
    pub test_concept_linker_count: Cint64,
    /// `cint64 mTestConceptLinkerLevel`.
    pub test_concept_linker_level: Cint64,
}

impl ReuseCompletionGraphCacheReader {
    pub fn new() -> Self {
        ReuseCompletionGraphCacheReader {
            context: ReuseCompletionGraphCacheContext::new(),
            current_slot: Id::NONE,
            updated_slot: Id::NONE,
            free_linker: INVALID,
            entry_voting_vec: Vec::new(),
            test_concept_linker_vec: [Vec::new(), Vec::new(), Vec::new(), Vec::new()],
            test_concept_linker_count: 0,
            test_concept_linker_level: 0,
        }
    }
    // W6-CACHE method-batch

    /// Port of `updateSlot` (`mUpdatedSlot.fetchAndStoreOrdered(updatedSlot)`).
    pub fn update_slot(
        &mut self,
        updated_slot: ReuseCacheSlotItemId,
        cache_context: &mut CacheContext,
    ) -> &mut Self {
        // KONCLUDE-PORT-NOTE[threading]: atomic exchange of the published slot id
        // becomes a single-threaded swap on the arena id.
        let prev_slot = self.updated_slot;
        self.updated_slot = updated_slot;
        if prev_slot.is_some() {
            cache_context
                .reuse_cache_slot_item_mut(prev_slot)
                .dec_reader();
        }
        self
    }

    /// Port of `hasUpdatedSlotItem` (`mUpdatedSlot.fetchAndAddRelaxed(0) != nullptr`).
    pub fn has_updated_slot_item(&self) -> bool {
        self.updated_slot.is_some()
    }

    /// Port of `switchToUpdatedSlotItem` (`mUpdatedSlot.fetchAndStoreOrdered(nullptr)`).
    /// KONCLUDE-PORT-NOTE[threading]: take the published slot id and clear the atomic.
    pub fn switch_to_updated_slot_item(&mut self, cache_context: &mut CacheContext) -> bool {
        let updated_slot = self.updated_slot;
        self.updated_slot = Id::NONE;
        if updated_slot.is_some() {
            let prev_slot = self.current_slot;
            self.current_slot = updated_slot;
            if prev_slot.is_some() {
                cache_context
                    .reuse_cache_slot_item_mut(prev_slot)
                    .dec_reader();
            }
            return true;
        }
        false
    }

    /// Port of `getConceptTestLinker`.
    /// KONCLUDE-PORT-NOTE[memory-pool]: the reusable-linker freelist (`mFreeLinker`)
    /// is subsumed by the head-front `Vec` collapse of the test-concept ring
    /// (PORT.md §6) — the live node is a `Vec` entry, so this pool accessor is
    /// retained only as the opaque freelist head.
    pub fn get_concept_test_linker(&mut self) -> Cint64 {
        // W6-DEFER[memory-pool]: pop mFreeLinker, else allocateAndConstruct<CXLinker<TConceptNegPair>>.
        INVALID
    }

    /// Port of `releaseConceptTestLinker` (`mFreeLinker = linker->append(mFreeLinker)`).
    pub fn release_concept_test_linker(&mut self, _linker: Cint64) -> &mut Self {
        // W6-DEFER[memory-pool]: prepend the released node onto the freelist.
        self
    }

    /// Port of `addTestingConcept`.
    pub fn add_testing_concept(
        &mut self,
        concept: ConceptId,
        negated: bool,
        mut adding_level: Cint64,
        tested_concept_set: &mut HashSet<ConceptId>,
    ) -> bool {
        if !tested_concept_set.contains(&concept) {
            tested_concept_set.insert(concept);
            // W6-DEFER[memory-pool]: getConceptTestLinker()/newLinker->initLinker — the
            // linker node is collapsed into the Vec entry (PORT.md §6).
            if adding_level < self.test_concept_linker_level {
                adding_level = self.test_concept_linker_level;
            }
            // head-at-FRONT prepend (`newLinker->append(mTestConceptLinkerVec[level])`).
            self.test_concept_linker_vec[adding_level as usize].insert(
                0,
                NegLink {
                    target: concept,
                    negated,
                },
            );
            self.test_concept_linker_count += 1;
            return true;
        }
        false
    }

    /// Port of `addTestingConcepts` (XOR the per-operand negation bit with `negate`).
    pub fn add_testing_concepts(
        &mut self,
        con_linker: &[NegLink<ConceptId>],
        negate: bool,
        adding_level: Cint64,
        tested_concept_set: &mut HashSet<ConceptId>,
    ) -> bool {
        let mut one_added = false;
        for link in con_linker {
            one_added |= self.add_testing_concept(
                link.target,
                link.negated ^ negate,
                adding_level,
                tested_concept_set,
            );
        }
        one_added
    }

    /// Port of `getCacheEntry`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: the current slot's compatibility hash + the cached
    /// `CReuseCompletionGraphCacheEntry`s live in the facade arena, and the
    /// `CConcept` operand/role traversal lives in the ontology arena — neither is
    /// threaded into the cache subtree's struct wave. Those dereferences are
    /// reproduced structurally over empty deferred iterators (`W6-DEFER[api]`,
    /// mirroring the W3 completion-unit convention); the voting-vec and
    /// test-concept-ring bookkeeping is fully ported.
    pub fn get_cache_entry(
        &mut self,
        cache_context: &mut CacheContext,
        concept: ConceptId,
        minimal_completion_graph: Option<&mut bool>,
        deterministic_connection: Option<&mut bool>,
    ) -> ReuseCacheEntryId {
        let mut entry: ReuseCacheEntryId = Id::NONE;
        if self.has_updated_slot_item() {
            self.switch_to_updated_slot_item(cache_context);
        }
        if self.current_slot.is_some() {
            let _entry_hash = cache_context
                .reuse_cache_slot_item(self.current_slot)
                .get_entry_hash();
            let entry_count = cache_context
                .reuse_cache_slot_item(self.current_slot)
                .get_entry_count();

            if entry_count > 0 {
                if (self.entry_voting_vec.len() as Cint64) < entry_count {
                    self.entry_voting_vec
                        .resize(entry_count as usize, CacheEntryVotingItem::new());
                }
                for i in 0..entry_count as usize {
                    self.entry_voting_vec[i].reset();
                }

                let mut tested_concept_set: HashSet<ConceptId> = HashSet::new();

                for i in 0..TEST_CONCEPT_LINKER_VEC_SIZE {
                    self.test_concept_linker_vec[i].clear();
                }
                self.test_concept_linker_count = 1;
                self.test_concept_linker_level = 0;
                // W6-DEFER[memory-pool]: getConceptTestLinker() — node collapsed into Vec.
                self.test_concept_linker_vec[0].insert(
                    0,
                    NegLink {
                        target: concept,
                        negated: false,
                    },
                );
                tested_concept_set.insert(concept);

                while self.test_concept_linker_count > 0 {
                    // advance to the first non-empty level >= current level, pop its head
                    let mut test_con: ConceptId = Id::NONE;
                    let mut test_con_neg = false;
                    let mut found = false;
                    while self.test_concept_linker_level < TEST_CONCEPT_LINKER_VEC_SIZE as Cint64 {
                        let lvl = self.test_concept_linker_level as usize;
                        if !self.test_concept_linker_vec[lvl].is_empty() {
                            let head = self.test_concept_linker_vec[lvl].remove(0);
                            test_con = head.target;
                            test_con_neg = head.negated;
                            found = true;
                            break;
                        }
                        self.test_concept_linker_level += 1;
                    }
                    self.test_concept_linker_count -= 1;
                    if !found {
                        continue;
                    }
                    let _ = test_con;

                    let mut search_operand_concepts = true;

                    // W6-DEFER[api]: testCon->hasClassName() — ontology-arena concept.
                    let test_con_has_class_name = false;
                    if !test_con_neg && test_con_has_class_name {
                        // W6-DEFER[api]: CCacheValue(testCon->getConceptTag(),(cint64)testCon,CACHEVALTAGANDCONCEPT)
                        // W6-DEFER[api]: const data = entryHash->value(cacheValue)
                        // W6-DEFER[api]: entailed/incompatible entry-linker chains (facade arena).
                        let entailed_entry_linker: &[ReuseCacheEntryId] = &[];
                        let incompatible_entry_linker: &[ReuseCacheEntryId] = &[];
                        if !entailed_entry_linker.is_empty()
                            || !incompatible_entry_linker.is_empty()
                        {
                            for &_e in entailed_entry_linker {
                                // W6-DEFER[api]: item = mEntryVotingVec[entry->getEntryID()];
                                //   item.mEntry = entry; item.mEntailedCount++; item.mTmpReferenced = true;
                                //   item.mMinConnectionLevel = qMin(.., mTestConceptLinkerLevel);
                                //   item.mMinimalFound |= entry->hasMinimalValue(cacheValue);
                            }
                            for &_e in incompatible_entry_linker {
                                // W6-DEFER[api]: item.mEntry = entry; item.mIncompatibleCount++;
                                //   item.mTmpReferenced = true;
                            }
                            for i in 0..entry_count as usize {
                                let item = &mut self.entry_voting_vec[i];
                                if !item.tmp_referenced {
                                    item.missing_count += 1;
                                } else {
                                    item.tmp_referenced = false;
                                }
                            }
                            search_operand_concepts = false;
                        }
                    }

                    if search_operand_concepts {
                        // W6-DEFER[api]: CRole* role = testCon->getRole();
                        //   addTestingConcepts(role->getDomainConceptList(),false,0,..)
                        //   addTestingConcepts(role->getRangeConceptList(),false,2,..)
                        // W6-DEFER[api]: opCode = testCon->getOperatorCode();
                        //   opLinker = testCon->getOperandList();
                        // The full operator dispatch routes operands to the appropriate
                        // ring level by polarity/operator (CCAND/CCEQ/CCSUB/CCAQAND/
                        // CCIMPLTRIG → lvl 0; CCOR → lvl 3 (or lvl 0 negated); CCSOME/
                        // CCAQSOME/¬CCALL → lvl 1; CCATLEAST/¬CCATMOST with cardinality≥1
                        // → lvl 1; CCAQALL/CCIMPLALL/CCBRANCHALL → lvl 2; CCATMOST/
                        // CCATLEAST → lvl 3; CCIMPL → single operand lvl 0; CCAQCHOOCE →
                        // matching-polarity operands lvl 0). Reproduced over empty
                        // deferred operand lists (ontology-arena concepts unported here).
                        let op_linker: &[NegLink<ConceptId>] = &[];
                        self.add_testing_concepts(
                            op_linker,
                            test_con_neg,
                            0,
                            &mut tested_concept_set,
                        );
                    }

                    // W6-DEFER[memory-pool]: releaseConceptTestLinker(tmpTestConLinker)
                }

                let mut min_missing_count: Cint64 = 0;
                let mut best_entry_index: Option<usize> = None;
                for i in 0..entry_count as usize {
                    let item = &self.entry_voting_vec[i];
                    if item.entailed_count >= 1
                        && item.incompatible_count <= 0
                        && (best_entry_index.is_none() || min_missing_count < item.missing_count)
                    {
                        min_missing_count = item.missing_count;
                        best_entry_index = Some(i);
                    }
                }

                if let Some(bi) = best_entry_index {
                    let item = &self.entry_voting_vec[bi];
                    entry = item.entry;
                    if let Some(dc) = deterministic_connection {
                        *dc = item.min_connection_level <= 1;
                    }
                    if let Some(mc) = minimal_completion_graph {
                        *mc = item.minimal_found;
                    }
                }
            }
        }
        entry
    }
}

impl Default for ReuseCompletionGraphCacheReader {
    fn default() -> Self {
        ReuseCompletionGraphCacheReader::new()
    }
}

// ===========================================================================
// CReuseCompletionGraphCache — the cache facade (writer thread).
// ===========================================================================

/// Port of
/// `CReuseCompletionGraphCache : public CThread, public CCompletionGraphCache`.
///
/// KONCLUDE-PORT-NOTE[threading]: the `CThread` base (Qt event-loop writer
/// thread) becomes an opaque `thread` handle for the struct wave; per manifest
/// the event channel runs single-threaded first (worker IS the writer).
#[derive(Debug, Clone)]
pub struct ReuseCompletionGraphCache {
    /// Inlined `CCompletionGraphCache` base (F0, `cache/base.rs`).
    pub base: CompletionGraphCache,
    /// `CThread` base infrastructure.
    /// KONCLUDE-PORT-NOTE[threading]: opaque writer-thread handle.
    pub thread: Cint64,
    /// `CReuseCompletionGraphCacheSlotItem* mSlotLinker`.
    /// KONCLUDE-PORT-NOTE[ownership]: linker chain → head-front `Vec<Id>`.
    pub slot_linker: Vec<ReuseCacheSlotItemId>,
    /// `CReuseCompletionGraphCacheReader* mReaderLinker`.
    pub reader_linker: Vec<ReuseCacheReaderId>,
    /// `QMutex mReaderSyncMutex`.
    /// KONCLUDE-PORT-NOTE[threading]: opaque reader-sync mutex handle.
    pub reader_sync_mutex: Cint64,
    /// `CReuseCompletionGraphCompatibilityEntryHash* mEntyHash`.
    pub enty_hash: CompatibilityEntryHashId,
    /// `CCACHINGLIST<CReuseCompletionGraphCacheEntry*>* mEntyList`.
    /// KONCLUDE-PORT-NOTE[ownership]: caching-list of entry pointers → `Vec<Id>`.
    pub enty_list: Vec<ReuseCacheEntryId>,
    /// `cint64 mEntryCount`.
    pub entry_count: Cint64,
    /// `CReuseCompletionGraphCacheContext mContext` (held by value).
    pub context: ReuseCompletionGraphCacheContext,
}

impl ReuseCompletionGraphCache {
    pub fn new() -> Self {
        ReuseCompletionGraphCache {
            base: CompletionGraphCache::new(),
            thread: INVALID,
            slot_linker: Vec::new(),
            reader_linker: Vec::new(),
            reader_sync_mutex: INVALID,
            enty_hash: Id::NONE,
            enty_list: Vec::new(),
            entry_count: 0,
            context: ReuseCompletionGraphCacheContext::new(),
        }
    }
    // W6-CACHE method-batch

    /// Port of `createCacheReader`.
    /// KONCLUDE-PORT-NOTE[threading]: `mReaderSyncMutex` guards the reader-list
    /// splice → single-threaded inline; `reader->append(mReaderLinker)` prepends
    /// (head-at-FRONT).
    pub fn create_cache_reader(&mut self, cache_context: &mut CacheContext) -> ReuseCacheReaderId {
        let reader = cache_context.alloc_reuse_cache_reader(ReuseCompletionGraphCacheReader::new());
        // mReaderSyncMutex.lock();
        self.reader_linker.insert(0, reader);
        // mReaderSyncMutex.unlock();
        reader
    }

    /// Port of `createCacheWriter` (`new CReuseCompletionGraphCacheWriter(this)`).
    pub fn create_cache_writer(&mut self) -> ReuseCompletionGraphCacheWriter {
        // W6-DEFER[ownership]: the writer holds an opaque back-handle to this facade.
        ReuseCompletionGraphCacheWriter::new_with_cache(INVALID)
    }

    /// Port of `writeExpandCache` (`postEvent(new CWriteCachedDataEvent(...))`).
    /// KONCLUDE-PORT-NOTE[threading]: the worker posts a write event to the
    /// dedicated writer thread; the staged single-thread port keeps the event
    /// boundary (manifest §Concurrency) and drains it inline (see
    /// `process_customs_events`).
    pub fn write_expand_cache(
        &mut self,
        _write_data: &ReuseCacheEntryWriteData,
        _memory_pools: Cint64,
    ) -> &mut Self {
        // W6-DEFER[threading]: postEvent(new CWriteCachedDataEvent(writeData, memoryPools))
        self
    }

    /// Port of `createReaderSlotUpdate`.
    /// KONCLUDE-PORT-NOTE[memory-pool]: the C++ slot-local memory pool becomes a
    /// normal arena allocation; the detached hash copy is a `Clone` of `mEntyHash`.
    pub fn create_reader_slot_update(&mut self, cache_context: &mut CacheContext) {
        if self.enty_hash.is_none() {
            self.enty_hash = cache_context.alloc_reuse_compat_entry_hash(
                ReuseCompletionGraphCompatibilityEntryHash::new_with_context(INVALID),
            );
        }
        let enty_hash = cache_context
            .reuse_compat_entry_hash(self.enty_hash)
            .clone();
        let enty_hash = cache_context.alloc_reuse_compat_entry_hash(enty_hash);
        let mut slot = ReuseCompletionGraphCacheSlotItem::new();
        slot.set_entry_hash(enty_hash);
        slot.set_entry_count(self.entry_count);
        let slot = cache_context.alloc_reuse_cache_slot_item(slot);
        // `mSlotLinker->append(slot)` — tail-append onto the live slot list.
        self.slot_linker.push(slot);
        // for each reader: slot->incReader(); readerLinkerIt->updateSlot(slot)
        for &reader in &self.reader_linker {
            cache_context.reuse_cache_slot_item_mut(slot).inc_reader();
            let prev_slot = {
                let reader = cache_context.reuse_cache_reader_mut(reader);
                let prev_slot = reader.updated_slot;
                reader.updated_slot = slot;
                prev_slot
            };
            if prev_slot.is_some() {
                cache_context
                    .reuse_cache_slot_item_mut(prev_slot)
                    .dec_reader();
            }
        }
    }

    /// Port of `cleanUnusedSlots` (drop slots whose reader count fell to zero).
    /// KONCLUDE-PORT-NOTE[memory-pool]: releasing a dropped slot's pools is deferred;
    /// arena allocation is reclaimed with the cache context.
    pub fn clean_unused_slots(&mut self, cache_context: &mut CacheContext) {
        let mut kept: Vec<ReuseCacheSlotItemId> = Vec::new();
        for &slot in &self.slot_linker {
            if cache_context
                .reuse_cache_slot_item(slot)
                .has_cache_readers()
            {
                kept.push(slot);
            }
        }
        self.slot_linker = kept;
    }

    /// Port of `writeExpandCacheData`.
    /// KONCLUDE-PORT-NOTE[memory-pool]: compatibility wrapper for older call sites
    /// that do not yet thread the cache-pool arena. The live port is
    /// `write_expand_cache_data_in_context`.
    pub fn write_expand_cache_data(
        &mut self,
        context: Cint64,
        cache_list: &[CacheValue],
        minimal_cache_list: &[CacheValue],
        job_inst: JobInstantiation,
    ) {
        let _ = (context, cache_list, minimal_cache_list, job_inst);
        // W6-DEFER[api]: legacy call sites must pass `CacheContext` so the entry
        // and `mEntyHash` can be materialized in the cache arena.
        let new_entry: ReuseCacheEntryId = Id::NONE;
        self.enty_list.push(new_entry);
        self.entry_count += 1;
    }

    /// Port of `writeExpandCacheData`.
    /// KONCLUDE-PORT-NOTE[ownership]: `CReuseCompletionGraphCacheContext` owns a
    /// memory manager in C++; the Rust port stores the allocated entry and
    /// compatibility hash in `CacheContext` typed arenas. `mEntyHash` is allocated
    /// lazily here because `ReuseCompletionGraphCache::new()` has no arena handle.
    pub fn write_expand_cache_data_in_context(
        &mut self,
        cache_context: &mut CacheContext,
        context: Cint64,
        cache_list: &[CacheValue],
        minimal_cache_list: &[CacheValue],
        job_inst: JobInstantiation,
    ) {
        if self.enty_hash.is_none() {
            self.enty_hash = cache_context.alloc_reuse_compat_entry_hash(
                ReuseCompletionGraphCompatibilityEntryHash::new_with_context(context),
            );
        }

        let mut entry = ReuseCompletionGraphCacheEntry::new();
        entry.context = context;
        entry.set_job_instantiation(job_inst);
        entry.set_entry_id(self.entry_count);
        let new_entry = cache_context.alloc_reuse_cache_entry(entry);
        self.enty_list.push(new_entry);

        for &cache_value in cache_list {
            cache_context
                .reuse_compat_entry_hash_mut(self.enty_hash)
                .get_or_create_mut(cache_value)
                .add_entailed_enty_linker(new_entry);
            cache_context
                .reuse_cache_entry_mut(new_entry)
                .add_entailed_value(cache_value);
        }

        for &cache_value in minimal_cache_list {
            cache_context
                .reuse_cache_entry_mut(new_entry)
                .add_minimal_value(cache_value);
        }

        self.entry_count += 1;
    }

    /// Port of `processCustomsEvents` (the writer-thread event drain).
    /// KONCLUDE-PORT-NOTE[threading]: `CWriteCachedDataEvent` carries the queued
    /// write-data linker chain + its memory pools; drained inline here (manifest
    /// §Concurrency single-thread staging). The `event_type` / `CThread` base
    /// dispatch is the opaque event seam.
    pub fn process_customs_events(
        &mut self,
        cache_context: &mut CacheContext,
        _event_type: Cint64,
        write_data_chain: &[ReuseCacheEntryWriteData],
        _memory_pools: Cint64,
    ) -> bool {
        // if (CThread::processCustomsEvents(type,event)) return true;
        // if (type == CWriteCachedDataEvent::EVENTTYPE) { ... }
        for data in write_data_chain {
            if data.is_expand() {
                let cache_list = data.get_cache_value_list().cloned().unwrap_or_default();
                // KONCLUDE-PORT-NOTE: faithful to the C++ — `minimalCacheList` is read
                // from `getCacheValueList()` (NOT `getMinimalCacheValueList()`), an
                // upstream copy/paste; the same chain is used for both. Preserved.
                let minimal_cache_list = data.get_cache_value_list().cloned().unwrap_or_default();
                let job_inst = data.get_job_instantiation();
                self.write_expand_cache_data_in_context(
                    cache_context,
                    INVALID,
                    &cache_list,
                    &minimal_cache_list,
                    job_inst,
                );
            }
        }
        self.create_reader_slot_update(cache_context);
        self.clean_unused_slots(cache_context);
        // W6-DEFER[memory-pool]: mContext.getMemoryPoolAllocationManager()->releaseTemporaryMemoryPools(memoryPools)
        false
    }
}

impl Default for ReuseCompletionGraphCache {
    fn default() -> Self {
        ReuseCompletionGraphCache::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn write_expand_cache_data_materializes_entry_and_hash() {
        let mut cache_context = CacheContext::new();
        let mut cache = ReuseCompletionGraphCache::new();
        let cache_values = vec![11, 17];
        let minimal_values = vec![17];

        cache.write_expand_cache_data_in_context(
            &mut cache_context,
            23,
            &cache_values,
            &minimal_values,
            31,
        );

        assert_eq!(cache.entry_count, 1);
        assert_eq!(cache.enty_list.len(), 1);
        assert_eq!(cache_context.reuse_cache_entries.len(), 1);
        assert_eq!(cache_context.reuse_compat_entry_hashes.len(), 1);

        let entry_id = cache.enty_list[0];
        let entry = cache_context.reuse_cache_entry(entry_id);
        assert_eq!(entry.context, 23);
        assert_eq!(entry.get_job_instantiation(), 31);
        assert_eq!(entry.get_entry_id(), 0);
        assert_eq!(entry.get_entailed_values(), &cache_values);
        assert_eq!(entry.get_minimal_values(), &minimal_values);
        assert!(entry.has_minimal_value(17));

        let hash = cache_context.reuse_compat_entry_hash(cache.enty_hash);
        assert_eq!(hash.value(&11).get_entailed_entry_linker(), &[entry_id]);
        assert_eq!(hash.value(&17).get_entailed_entry_linker(), &[entry_id]);
        assert!(hash.value(&11).get_incompatible_entry_linker().is_empty());
    }

    #[test]
    fn reuse_cache_create_reader_prepends_reader_linker_with_context() {
        let mut cache_context = CacheContext::new();
        let mut cache = ReuseCompletionGraphCache::new();

        let first = cache.create_cache_reader(&mut cache_context);
        let second = cache.create_cache_reader(&mut cache_context);

        assert_eq!(cache.reader_linker, vec![second, first]);
        assert_eq!(cache_context.reuse_cache_readers.len(), 2);
    }

    #[test]
    fn reuse_cache_create_reader_slot_update_publishes_snapshot_to_readers() {
        let mut cache_context = CacheContext::new();
        let mut cache = ReuseCompletionGraphCache::new();
        let first = cache.create_cache_reader(&mut cache_context);
        let second = cache.create_cache_reader(&mut cache_context);
        cache.write_expand_cache_data_in_context(&mut cache_context, 23, &[11, 17], &[17], 31);

        cache.create_reader_slot_update(&mut cache_context);

        assert_eq!(cache.slot_linker.len(), 1);
        let slot = cache.slot_linker[0];
        let slot_item = cache_context.reuse_cache_slot_item(slot);
        assert_eq!(slot_item.get_entry_count(), 1);
        assert_eq!(slot_item.reader_sharing_count, 2);
        assert!(slot_item.has_cache_readers());
        let slot_hash = cache_context.reuse_compat_entry_hash(slot_item.get_entry_hash());
        let entry = cache.enty_list[0];
        assert_eq!(slot_hash.value(&11).get_entailed_entry_linker(), &[entry]);
        assert_eq!(cache_context.reuse_cache_reader(first).updated_slot, slot);
        assert_eq!(cache_context.reuse_cache_reader(second).updated_slot, slot);
    }

    #[test]
    fn reuse_cache_reader_switches_updated_slot_and_decrements_previous_current_slot() {
        let mut cache_context = CacheContext::new();
        let mut old_slot = ReuseCompletionGraphCacheSlotItem::new();
        old_slot.inc_reader();
        let old_slot = cache_context.alloc_reuse_cache_slot_item(old_slot);
        let mut new_slot = ReuseCompletionGraphCacheSlotItem::new();
        new_slot.inc_reader();
        let new_slot = cache_context.alloc_reuse_cache_slot_item(new_slot);
        let mut reader = ReuseCompletionGraphCacheReader::new();
        reader.current_slot = old_slot;
        reader.update_slot(new_slot, &mut cache_context);

        assert!(reader.switch_to_updated_slot_item(&mut cache_context));

        assert_eq!(reader.current_slot, new_slot);
        assert_eq!(reader.updated_slot, ReuseCacheSlotItemId::NONE);
        assert!(!cache_context
            .reuse_cache_slot_item(old_slot)
            .has_cache_readers());
        assert!(cache_context
            .reuse_cache_slot_item(new_slot)
            .has_cache_readers());
    }

    #[test]
    fn reuse_cache_clean_unused_slots_removes_zero_reader_slots() {
        let mut cache_context = CacheContext::new();
        let unused_head =
            cache_context.alloc_reuse_cache_slot_item(ReuseCompletionGraphCacheSlotItem::new());
        let mut used = ReuseCompletionGraphCacheSlotItem::new();
        used.inc_reader_count(2);
        let used = cache_context.alloc_reuse_cache_slot_item(used);
        let unused_tail =
            cache_context.alloc_reuse_cache_slot_item(ReuseCompletionGraphCacheSlotItem::new());
        let mut cache = ReuseCompletionGraphCache::new();
        cache.slot_linker = vec![unused_head, used, unused_tail];

        cache.clean_unused_slots(&mut cache_context);

        assert_eq!(cache.slot_linker, vec![used]);
    }

    #[test]
    fn reuse_cache_process_customs_events_writes_and_publishes_slot() {
        let mut cache_context = CacheContext::new();
        let mut cache = ReuseCompletionGraphCache::new();
        let reader = cache.create_cache_reader(&mut cache_context);
        let write_data =
            ReuseCacheEntryWriteData::init_expand_write_data(vec![41, 43], vec![43], 47);

        assert!(!cache.process_customs_events(&mut cache_context, 0, &[write_data], INVALID));

        assert_eq!(cache.entry_count, 1);
        assert_eq!(cache.slot_linker.len(), 1);
        let slot = cache.slot_linker[0];
        assert_eq!(cache_context.reuse_cache_reader(reader).updated_slot, slot);
        assert_eq!(
            cache_context
                .reuse_cache_slot_item(slot)
                .reader_sharing_count,
            1
        );
    }
}
