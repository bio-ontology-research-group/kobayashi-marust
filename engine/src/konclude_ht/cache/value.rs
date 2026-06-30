//! `cache::value` — F0 shared cache value / entry / statistics / tagging infra
//! (Konclude `Reasoner/Kernel/Cache/`): the generic hashed cache key
//! (`CCacheValue` + `CCacheValueHasher`), the generic entry + entry-write-data
//! (`CCacheEntry` / `CCacheEntryWriteData`), `CCacheStatistics`, the incremental
//! bulk-reset tagging machinery (`CCacheModificationTagSet` / `CCacheTaggingPool`),
//! and the `CacheSettings.h` event-type constants + concurrent-modification
//! container typedefs.
//!
//! These are the data structures every cache family stores its entries in; they
//! are shared infra, not a cache facade.

#![allow(dead_code)]

use super::super::model::substrate::{Cint64, Id};
use super::context::CacheContext;

// ===========================================================================
// CCacheValue — the generic hashed cache key (a tagged i64 triple).
// ===========================================================================

/// Port of `CCacheValue::CACHEVALUEIDENTIFIER`.
///
/// Discriminates what the `(tag, identification)` pair of a `CacheValue` means
/// (concept ontology tag, role, terminator, individual id, entry tag, …).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(i64)]
pub enum CacheValueIdentifier {
    CacheValConceptOntologyTag = 0,
    CacheValNegatedConceptOntologyTag = 1,
    CacheValRoleOntologyTag = 2,
    CacheValueTerminator = 3,
    CacheValueNothing = 4,

    CacheValTagAndConcept = 5,
    CacheValTagAndNegatedConcept = 6,
    CacheValTagAndNondeterministicConcept = 7,
    CacheValTagAndNondeterministicNegatedConcept = 8,

    CacheValTagAndRole = 9,
    CacheValTagAndInversedRole = 10,
    CacheValTagAndAssertedRole = 11,
    CacheValTagAndInversedAssertedRole = 12,
    CacheValTagAndNominalConnectedRole = 13,
    CacheValTagAndInversedNominalConnectedRole = 14,

    CacheValTagAndNondeterministicRole = 15,
    CacheValTagAndNondeterministicInversedRole = 16,
    CacheValTagAndNondeterministicAssertedRole = 17,
    CacheValTagAndNondeterministicInversedAssertedRole = 18,
    CacheValTagAndNondeterministicNominalConnectedRole = 19,
    CacheValTagAndNondeterministicInversedNominalConnectedRole = 20,

    CacheValueIndividualId = 21,
    CacheValueNegatedIndividualId = 22,
    CacheValueTagAndEntry = 23,
    CacheValueTagAndTemporaryEntry = 24,
}

impl Default for CacheValueIdentifier {
    fn default() -> Self {
        CacheValueIdentifier::CacheValConceptOntologyTag
    }
}

/// Port of `CCacheValue : public CTrible<qint64>`.
///
/// KONCLUDE-PORT-NOTE[api]: C++ inherits `CTrible<qint64>` (a `QPair<QPair<T,T>,T>`)
/// and stores all three values in the inherited triple — `CCacheValue` declares
/// NO members of its own. The port inlines the triple as three `Cint64` fields,
/// mirroring the `CCacheValue(tag, identification, cacheValueIdentifier)`
/// constructor mapping: `tag → first`, `identification → second`,
/// `cacheValueIdentifier → third`. The first ctor `(first, second, third)` writes
/// the raw triple; the second derives `(first=tag, second=identification,
/// third=identifier)`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct CacheValue {
    /// `CTrible::first.first` — the tag (`getTag()`).
    pub first: Cint64,
    /// `CTrible::first.second` — the identification (`getIdentification()`).
    pub second: Cint64,
    /// `CTrible::second` — the cache-value identifier (`getCacheValueIdentifier()`),
    /// one of `CacheValueIdentifier` stored as its `i64` discriminant.
    pub third: Cint64,
}

impl CacheValue {
    /// Port of `CCacheValue::CCacheValue()` (`: CTrible<qint64>(0,0,0)`).
    pub fn new() -> Self {
        CacheValue::default()
    }

    /// Port of `CCacheValue::CCacheValue(first, second, third)`
    /// (`: CTrible<qint64>(first,second,third)`) — writes the raw triple.
    pub fn new_raw(first: Cint64, second: Cint64, third: Cint64) -> Self {
        CacheValue { first, second, third }
    }

    /// Port of
    /// `CCacheValue(tag, identification, cacheValueIdentifier = CACHEVALCONCEPTONTOLOGYTAG)`
    /// (`: CTrible<qint64>(tag, identification, (qint64)cacheValueIdentifier)`).
    pub fn new_value(
        tag: Cint64,
        identification: Cint64,
        cache_value_identifier: CacheValueIdentifier,
    ) -> Self {
        CacheValue {
            first: tag,
            second: identification,
            third: cache_value_identifier as Cint64,
        }
    }

    /// Port of `CCacheValue::initCacheValue`.
    /// C++ returns `this` (`CCacheValue*`) for chaining → `&mut Self`.
    /// Faithful to `set(tag, identification, (cint64)cacheValueIdentifier)`:
    /// `CTrible::set` writes `first.first=tag`, `first.second=identification`,
    /// `second=identifier` — i.e. the port's `first`/`second`/`third`.
    pub fn init_cache_value(
        &mut self,
        tag: Cint64,
        identification: Cint64,
        cache_value_identifier: CacheValueIdentifier,
    ) -> &mut Self {
        self.first = tag;
        self.second = identification;
        self.third = cache_value_identifier as Cint64;
        self
    }

    /// Port of `CCacheValue::isCachedConcept`.
    /// C++ tests `(CACHEVALUEIDENTIFIER)this->second == CACHEVALCONCEPTONTOLOGYTAG`
    /// where `CTrible::second` is the cache-value identifier — the port's `third`.
    pub fn is_cached_concept(&self) -> bool {
        self.third == CacheValueIdentifier::CacheValConceptOntologyTag as Cint64
    }

    /// Port of `CCacheValue::isCachedRole`.
    pub fn is_cached_role(&self) -> bool {
        self.third == CacheValueIdentifier::CacheValRoleOntologyTag as Cint64
    }

    /// Port of `CCacheValue::isCachedTerminator`.
    pub fn is_cached_terminator(&self) -> bool {
        self.third == CacheValueIdentifier::CacheValueTerminator as Cint64
    }

    /// Port of `CCacheValue::isCachedNothing`.
    pub fn is_cached_nothing(&self) -> bool {
        self.third == CacheValueIdentifier::CacheValueNothing as Cint64
    }

    /// Port of `CCacheValue::getTag` (`this->first.first`).
    pub fn get_tag(&self) -> Cint64 {
        self.first
    }

    /// Port of `CCacheValue::getIdentification` (`this->first.second`).
    pub fn get_identification(&self) -> Cint64 {
        self.second
    }

    /// Port of `CCacheValue::getCacheValueIdentifier` (`(CACHEVALUEIDENTIFIER)this->second`).
    /// KONCLUDE-PORT-NOTE[api]: C++ returns the `CACHEVALUEIDENTIFIER` enum via a
    /// reinterpret cast of the stored `cint64`; the port returns the raw `Cint64`
    /// discriminant (the `third` field) — the inverse `CacheValueIdentifier` enum
    /// is recovered by the caller when it needs the typed form. Behaviour is
    /// identical (the variant discriminants equal the stored ints).
    pub fn get_cache_value_identifier(&self) -> Cint64 {
        self.third
    }

    /// Port of `qHash(*const CCacheValue)` — the Qt `qHash` of a
    /// `CTrible<qint64>` (= `QPair<QPair<qint64,qint64>, qint64>`). Self-contained:
    /// a pure function of the three `i64` fields, reproducing Qt5's `qHash(QPair)`
    /// fold over `qHash(qint64)`. This is the substantive hash math the
    /// `CacheValueHasher` adapter forwards to.
    pub fn q_hash(&self) -> u32 {
        // inner = qHash(QPair<qint64,qint64>(tag, identification))
        let inner = qhash_pair(qhash_i64(self.first, 0), qhash_i64(self.second, 0), 0);
        // outer = qHash(QPair<innerPair, identifier>)
        qhash_pair(inner, qhash_i64(self.third, 0), 0)
    }
}

/// Port of Qt's `inline uint qHash(qint64 key, uint seed)` (via `quint64`):
/// `uint(((key >> 31) ^ key)) ^ seed` for a 32-bit `uint`.
fn qhash_i64(key: Cint64, seed: u32) -> u32 {
    let k = key as u64;
    if std::mem::size_of::<u64>() > std::mem::size_of::<u32>() {
        (((k >> (8 * std::mem::size_of::<u32>() as u64 - 1)) ^ k) as u32) ^ seed
    } else {
        (k as u32) ^ seed
    }
}

/// Port of Qt's `inline uint qHash(const QPair<T1,T2>&, uint seed)`:
/// `((h1 << 16) | (h1 >> 16)) ^ h2 ^ seed`, with `h1 = qHash(first)`,
/// `h2 = qHash(second)`.
fn qhash_pair(h1: u32, h2: u32, seed: u32) -> u32 {
    ((h1 << 16) | (h1 >> 16)) ^ h2 ^ seed
}

/// `CacheValue*` → `CacheValueId` (arena id; `[ownership]` per PORT.md §5).
pub type CacheValueId = Id<CacheValue>;

// ===========================================================================
// CCacheValueHasher — wraps a CacheValue* to provide qHash + operator==.
// ===========================================================================

/// Port of `CCacheValueHasher`.
///
/// Adapter that gives a `CacheValue` a hash/equality identity for use as a
/// `QHash` key (`getHashValue()` + `operator==`, plus the free `qHash`).
#[derive(Debug, Clone, Copy)]
pub struct CacheValueHasher {
    /// `CCacheValue* mCacheValue`.
    /// KONCLUDE-PORT-NOTE[ownership]: raw pointer → arena id (`Id::NONE` == null).
    pub cache_value: CacheValueId,
}

impl Default for CacheValueHasher {
    fn default() -> Self {
        CacheValueHasher { cache_value: CacheValueId::NONE }
    }
}

impl CacheValueHasher {
    /// Port of `CCacheValueHasher(CCacheValue* cacheValue)`.
    pub fn new(cache_value: CacheValueId) -> Self {
        CacheValueHasher { cache_value }
    }

    /// Port of `CCacheValueHasher::getHashValue` (`return qHash(*mCacheValue);`).
    /// KONCLUDE-PORT-NOTE[api]: the faithful body resolves `self.cache_value`
    /// against the cache-value arena and forwards to `CacheValue::q_hash`
    /// (`arena.get(self.cache_value).q_hash() as Cint64`). F0 deliberately leaves
    /// the cache-value container/arena undecided (see the `CCACHINGHASH` note at
    /// the foot of this file), so the resolution is deferred; the hash math itself
    /// is fully ported on `CacheValue::q_hash`. W6-DEFER[api].
    /// W6-UNDEFER (cache-arena): resolves `self.cache_value` against the
    /// cache-value arena and forwards to `CacheValue::q_hash`
    /// (`return qHash(*mCacheValue);`).
    pub fn get_hash_value(&self, ctx: &CacheContext) -> Cint64 {
        ctx.cache_value(self.cache_value).q_hash() as Cint64
    }

    /// Port of `CCacheValueHasher::operator==`
    /// (`if (*mCacheValue != *hasher.mCacheValue) return false; return true;`).
    /// KONCLUDE-PORT-NOTE[api]: the faithful test compares the two resolved
    /// `CacheValue`s by value (`CacheValue` derives the structural `Eq` that
    /// matches `CTrible::operator==`). Pending the cache-value arena, the interim
    /// compares the arena ids instead — equal id ⇒ equal value, but distinct ids
    /// with equal values are reported unequal (the one observable difference,
    /// flagged for the reconcile). Control flow is preserved. W6-DEFER[api].
    /// W6-UNDEFER (cache-arena): resolves both ids and compares the `CacheValue`s
    /// by value (`if (*mCacheValue != *hasher.mCacheValue) return false;`).
    pub fn eq_hasher(&self, other: &CacheValueHasher, ctx: &CacheContext) -> bool {
        if ctx.cache_value(self.cache_value) != ctx.cache_value(other.cache_value) {
            return false;
        }
        true
    }
}

/// Port of the free `inline uint qHash(const CCacheValueHasher& hasher)` from
/// `CCacheValueHasher.h` — folds the `cint64` hash value down to a 32-bit `uint`:
/// `uint((key >> (8*sizeof(uint)-1)) ^ key)` when `sizeof(cint64) > sizeof(uint)`,
/// else `uint(key)`. KONCLUDE-PORT-NOTE[api]: at the W6 reconcile this becomes the
/// `Hash` impl for `CacheValueHasher` (its `getHashValue()` resolves the arena).
pub fn q_hash_cache_value_hasher(hasher_hash_value: Cint64) -> u32 {
    let key = hasher_hash_value;
    if std::mem::size_of::<Cint64>() > std::mem::size_of::<u32>() {
        ((key >> (8 * std::mem::size_of::<u32>() as i64 - 1)) ^ key) as u32
    } else {
        key as u32
    }
}

// ===========================================================================
// CCacheEntry — empty generic cache entry base.
// ===========================================================================

/// Port of `CCacheEntry`.
///
/// [api] was-abstract — empty generic cache-entry base (virtual dtor only);
/// every family's concrete `*Entry` derives from it. No member variables.
#[derive(Debug, Default, Clone)]
pub struct CacheEntry;

impl CacheEntry {
    /// Port of `CCacheEntry::CCacheEntry()`.
    pub fn new() -> Self {
        CacheEntry
    }
    // [api] no methods to port: empty generic cache-entry base — C++ declares only
    // the constructor and a virtual destructor (both empty).
}

/// `CacheEntry*` → `CacheEntryId`.
pub type CacheEntryId = Id<CacheEntry>;

// ===========================================================================
// CCacheEntryWriteData — generic entry write payload (an intrusive linker node).
// ===========================================================================

/// Port of `CCacheEntryWriteData::CACHEWRITEDATATYPE`.
///
/// Tags which family a queued cache-write payload belongs to (the union the
/// writer thread drains).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(i64)]
pub enum CacheWriteDataType {
    SatExpandCacheWriteDataType = 0,
    SatBranchCacheWriteDataType = 1,
    ReuseCompletionGraphWriteExpandDataType = 2,
    BackendAssociationWriteDataType = 3,
}

impl Default for CacheWriteDataType {
    fn default() -> Self {
        CacheWriteDataType::SatExpandCacheWriteDataType
    }
}

/// Port of
/// `CCacheEntryWriteData : public CLinkerBase<CCacheEntryWriteData*, CCacheEntryWriteData>`.
///
/// The base of every family's queued write payload. KONCLUDE-PORT-NOTE[ownership]:
/// C++ is an intrusive `CLinkerBase` (carries its own `next` pointer); per the
/// canonical CLinker convention (PORT.md §6) the chain is collapsed to an owned
/// `Vec<Id<CacheEntryWriteData>>` head-at-FRONT held by the owner, so the
/// per-node `next` link is dropped here. Only the discriminant `mType` remains.
#[derive(Debug, Default, Clone)]
pub struct CacheEntryWriteData {
    /// `CACHEWRITEDATATYPE mType` — `getCacheWriteDataType()`.
    pub type_: CacheWriteDataType,
}

impl CacheEntryWriteData {
    /// Port of `CCacheEntryWriteData::CCacheEntryWriteData()`.
    /// KONCLUDE-PORT-NOTE[ownership]: the C++ ctor also threads `this` into its
    /// `CLinkerBase` base (`: CLinkerBase(this)`); per the canonical CLinker
    /// convention the intrusive `next` link is dropped (the chain is owned by the
    /// holder as a head-front `Vec`), so only the discriminant init remains.
    pub fn new() -> Self {
        CacheEntryWriteData::default()
    }

    /// Port of `CCacheEntryWriteData::getCacheWriteDataType` (`return mType;`).
    pub fn get_cache_write_data_type(&self) -> CacheWriteDataType {
        self.type_
    }
}

/// `CacheEntryWriteData*` → `CacheEntryWriteDataId`.
pub type CacheEntryWriteDataId = Id<CacheEntryWriteData>;

// ===========================================================================
// CCacheStatistics — per-cache entry-count + memory-consumption counters.
// ===========================================================================

/// Port of `CCacheStatistics`.
#[derive(Debug, Default, Clone)]
pub struct CacheStatistics {
    /// `cint64 mMemoryConsumption`.
    pub memory_consumption: Cint64,
    /// `cint64 mCacheEntriesCount`.
    pub cache_entries_count: Cint64,
}

impl CacheStatistics {
    /// Port of `CCacheStatistics::CCacheStatistics()` (`reset();`).
    pub fn new() -> Self {
        let mut s = CacheStatistics::default();
        s.reset();
        s
    }

    /// Port of `CCacheStatistics::reset`. C++ returns `this` → `&mut Self`.
    pub fn reset(&mut self) -> &mut Self {
        self.memory_consumption = 0;
        self.cache_entries_count = 0;
        self
    }

    /// Port of `CCacheStatistics::incCacheEntriesCount(cint64 incCount = 1)`.
    /// C++ returns `this` → `&mut Self`.
    pub fn inc_cache_entries_count(&mut self, inc_count: Cint64) -> &mut Self {
        self.cache_entries_count += inc_count;
        self
    }

    /// Port of `CCacheStatistics::setMemoryConsumption`. C++ returns `this`.
    pub fn set_memory_consumption(&mut self, memory_consumption: Cint64) -> &mut Self {
        self.memory_consumption = memory_consumption;
        self
    }

    /// Port of `CCacheStatistics::getCacheEntriesCount`.
    pub fn get_cache_entries_count(&self) -> Cint64 {
        self.cache_entries_count
    }

    /// Port of `CCacheStatistics::getMemoryConsumption`.
    pub fn get_memory_consumption(&self) -> Cint64 {
        self.memory_consumption
    }
}

// ===========================================================================
// CCacheModificationTagSet — a set of modification tags backed by a model-data
// array (the per-recomputation incremental invalidation set).
// ===========================================================================

/// Port of `CCacheModificationTagSet`.
///
/// KONCLUDE-PORT-NOTE[memory-pool]: C++ stores the tag set in a
/// `CModelDataArray*` carved from a `CDataArrayMemoryManager` pool, with a
/// `CTemporaryDataArrayMemoryStorer` value member managing the pooled allocation.
/// In the port this whole bulk-reset tag set is replaced by an arena
/// `Vec<Cint64>` + a generation counter (PORT.md §5 / manifest §"Concurrency"):
/// "reset between incremental recomputations" = bump the generation, not free.
/// Until that container lands, the model-data-array handle and the temporary
/// storer are kept as opaque `Cint64` handles.
#[derive(Debug, Default, Clone)]
pub struct CacheModificationTagSet {
    /// `CModelDataArray* tagSet` — the modification-tag set storage.
    /// [memory-pool] opaque handle (→ arena `Vec<Cint64>` + generation counter).
    pub tag_set: Cint64,
    /// `CTemporaryDataArrayMemoryStorer tmpDataArrayMemStorer` — the by-value
    /// pooled-allocation manager. [memory-pool] opaque handle.
    pub tmp_data_array_mem_storer: Cint64,
}

impl CacheModificationTagSet {
    /// Port of `CCacheModificationTagSet(CDataArrayMemoryManager* modelMemMan)` /
    /// `CCacheModificationTagSet(CCacheModificationTagSet*, CDataArrayMemoryManager*)`.
    /// KONCLUDE-PORT-NOTE[memory-pool]: the `CDataArrayMemoryManager*` ctor arg is
    /// the pool the array is carved from; opaque `Cint64` here.
    pub fn new() -> Self {
        // Port of `CCacheModificationTagSet(CDataArrayMemoryManager* modelMemMan)`:
        // `tmpDataArrayMemStorer(modelMemMan); tagSet = 0;`. The mem-manager arg and
        // the storer are opaque [memory-pool] handles; `tagSet = 0` == `Cint64::default`.
        CacheModificationTagSet::default()
    }

    /// Port of
    /// `CCacheModificationTagSet(CCacheModificationTagSet* modTagSet, CDataArrayMemoryManager*)`
    /// — the extend-and-copy ctor (`tagSet = 0; tagSet =
    /// CModelDataLevelArray::extendAndCopyModelFrom(tagSet, modTagSet->getModelDataArray(),
    /// &tmpDataArrayMemStorer);`).
    /// KONCLUDE-PORT-NOTE[memory-pool]: `extendAndCopyModelFrom` is a pooled
    /// `CModelDataArray` op not yet ported (the whole tag set collapses to an arena
    /// `Vec<Cint64>` + generation counter at the manifest's bulk-reset decision).
    /// Control flow preserved; the array op is deferred. W6-DEFER[memory-pool].
    pub fn new_extending(mod_tag_set: &CacheModificationTagSet) -> Self {
        let mut s = CacheModificationTagSet::default();
        // s.tag_set = extend_and_copy_model_from(0, mod_tag_set.get_model_data_array(), storer);
        let _ = mod_tag_set.get_model_data_array();
        s.tag_set = 0;
        s
    }

    /// Port of `CCacheModificationTagSet::addModificationTag`
    /// (`tagSet = CModelDataLevelArray::extendAndSetFlag(tagSet, tag, &tmpDataArrayMemStorer);
    /// return this;`). C++ returns `this` → `&mut Self`.
    /// KONCLUDE-PORT-NOTE[memory-pool]: `extendAndSetFlag` grows the pooled
    /// `CModelDataArray` and sets the `tag`-th flag; the pooled array op is deferred
    /// (→ arena `Vec<Cint64>` + generation). Control flow preserved. W6-DEFER[memory-pool].
    pub fn add_modification_tag(&mut self, tag: Cint64) -> &mut Self {
        // self.tag_set = extend_and_set_flag(self.tag_set, tag, &mut self.tmp_data_array_mem_storer);
        let _ = tag;
        self
    }

    /// Port of `CCacheModificationTagSet::getModelDataArray` (`return tagSet;`).
    /// KONCLUDE-PORT-NOTE[memory-pool]: returns the opaque `CModelDataArray*` handle.
    pub fn get_model_data_array(&self) -> Cint64 {
        self.tag_set
    }
}

// ===========================================================================
// CCacheTaggingPool — a pool of monotone tags handed out for bulk invalidation.
// ===========================================================================

/// Port of `CCacheTaggingPool`.
///
/// KONCLUDE-PORT-NOTE[memory-pool]: hands out a block of monotone `cint64` tags
/// (`takeNextTag`), chaining to a fresh pool when exhausted
/// (`createNextTaggingPool`). This is the generation-counter source for the
/// incremental bulk-reset described in the manifest: the port's eventual
/// replacement is a single monotone generation counter rather than a chained
/// pool of pre-reserved tags. The raw `cint64* mTagPool` block becomes an owned
/// `Vec<Cint64>` [memory-pool]; the scalar bookkeeping fields are kept verbatim.
#[derive(Debug, Default, Clone)]
pub struct CacheTaggingPool {
    /// `cint64 mPoolSize`.
    pub pool_size: Cint64,
    /// `cint64 mPoolSizeMask`.
    pub pool_size_mask: Cint64,
    /// `cint64 mNextPoolStartTag`.
    pub next_pool_start_tag: Cint64,
    /// `cint64* mTagPool` — the reserved tag block.
    /// KONCLUDE-PORT-NOTE[memory-pool]: raw pointer → owned `Vec<Cint64>`.
    pub tag_pool: Vec<Cint64>,
    /// `cint64 mPoolIndex`.
    pub pool_index: Cint64,
}

impl CacheTaggingPool {
    /// Port of `CCacheTaggingPool(cint64 poolSize = 1024)`.
    pub fn new() -> Self {
        Self::with_pool_size(1024)
    }

    /// Port of `CCacheTaggingPool::CCacheTaggingPool(cint64 poolSize = 1024)`:
    /// `mTagPool = nullptr; mPoolIndex = 0; mPoolSize = poolSize;
    /// mPoolSizeMask = mPoolSize-1; mNextPoolStartTag = 0; qsrand(...);`.
    /// KONCLUDE-PORT-NOTE[api]: `qsrand(QTime::currentTime().msec())` (time-seeding
    /// libc `rand`) is dropped — the pool's randomisation only spreads tag values
    /// (not behaviourally observable in reasoning); see `create_next_tagging_pool`
    /// for the deterministic replacement.
    pub fn with_pool_size(pool_size: Cint64) -> Self {
        CacheTaggingPool {
            tag_pool: Vec::new(),
            pool_index: 0,
            pool_size,
            pool_size_mask: pool_size - 1,
            next_pool_start_tag: 0,
        }
    }

    /// Port of `CCacheTaggingPool::takeNextTag`.
    pub fn take_next_tag(&mut self) -> Cint64 {
        let next_tag;
        if !self.has_more_tags() {
            self.create_next_tagging_pool();
        }
        next_tag = self.tag_pool[self.pool_index as usize];
        self.pool_index += 1;
        next_tag
    }

    /// Port of `CCacheTaggingPool::hasMoreTags`
    /// (`return mTagPool && mPoolIndex < mPoolSize;`).
    /// KONCLUDE-PORT-NOTE[memory-pool]: the null `mTagPool` test → "pool not yet
    /// allocated" == `tag_pool.is_empty()`.
    fn has_more_tags(&self) -> bool {
        !self.tag_pool.is_empty() && self.pool_index < self.pool_size
    }

    /// Port of `CCacheTaggingPool::createNextTaggingPool`. Fills the pool block with
    /// `[mNextPoolStartTag, mNextPoolStartTag + mPoolSize)`, advances the start tag,
    /// then in-place Fisher-Yates shuffles the block and resets `mPoolIndex`.
    /// C++ returns `this` → `&mut Self`.
    /// KONCLUDE-PORT-NOTE[api]: C++ shuffles with `qrand()` (time-seeded libc rand).
    /// The port reproduces the same Fisher-Yates control flow with a self-contained
    /// deterministic LCG seeded from `mNextPoolStartTag`; the exact permutation is
    /// not behaviourally observable (the tags are opaque unique invalidation keys).
    /// KONCLUDE-PORT-NOTE[memory-pool]: `new cint64[mPoolSize]` (allocated once) →
    /// the owned `tag_pool: Vec<Cint64>` resized once on first use.
    fn create_next_tagging_pool(&mut self) -> &mut Self {
        if self.tag_pool.is_empty() {
            self.tag_pool = vec![0; self.pool_size as usize];
        }
        for i in 0..self.pool_size {
            self.tag_pool[i as usize] = i + self.next_pool_start_tag;
        }
        self.next_pool_start_tag += self.pool_size;
        // build random permutation using Fisher-Yates algorithm
        // [api] deterministic LCG in place of qrand().
        let mut rng_state: u64 = (self.next_pool_start_tag as u64).wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        let mut next_rand = || -> i64 {
            rng_state = rng_state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            ((rng_state >> 33) & 0x7fff_ffff) as i64
        };
        let mut i = self.pool_size - 1;
        while i > 0 {
            let random_index = next_rand() % (i + 1);
            let tmp_val = self.tag_pool[random_index as usize];
            self.tag_pool[random_index as usize] = self.tag_pool[i as usize];
            self.tag_pool[i as usize] = tmp_val;
            i -= 1;
        }
        self.pool_index = 0;
        self
    }
}

// ===========================================================================
// CacheSettings.h — event-type constants + concurrent-modification container
// typedefs + the DummyValue placeholder.
// ===========================================================================

/// Port of `CacheSettings.h` event constants.
///
/// KONCLUDE-PORT-NOTE[threading]: these are the `QEvent::Type` ids of the
/// cross-thread cache-write messages drained by the dedicated writer thread (the
/// F8 `CWrite*Event` family). They are the concurrency seam: a worker posts one
/// of these instead of mutating the shared hash inline. Kept as plain `Cint64`
/// constants (the `QEvent::Type` is just a tagged int); the staged single-thread
/// port drains them inline (manifest §"Concurrency").
pub mod event {
    use super::Cint64;
    pub const WRITE_UNSATISFIABLE_CACHE_ENTRY: Cint64 = 2000;
    pub const WRITE_SATISFIABLE_CACHE_ENTRY: Cint64 = 2001;
    pub const WRITE_EXPAND_CACHED_ENTRY: Cint64 = 2002;
    pub const WRITE_SATISFIABLE_BRANCH_CACHED_ENTRY: Cint64 = 2003;
    pub const WRITE_CACHED_DATA_ENTRY: Cint64 = 2004;
    pub const WRITE_SATURATION_CACHE_DATA_ENTRY: Cint64 = 2005;
    pub const WRITE_COMPUTED_CONSEQUENCES_CACHE_DATA_ENTRY: Cint64 = 2006;
    pub const WRITE_BACKEND_ASSOCIATION_ENTRY: Cint64 = 2007;
    pub const RETRIEVE_INCOMPLETELY_ASSOCIATION_CACHED: Cint64 = 2008;
    pub const INITIALIZE_INDIVIDUALS_ASSOCIATIONS_CACHE: Cint64 = 2009;
    pub const REPORT_MAXIMUM_HANDLED_RECOMPUTATION_ID: Cint64 = 2010;
}

/// Port of `CacheSettings.h::DummyValue` — an empty placeholder value type used
/// as the value parameter of the value-less `CCACHINGSET` instantiations.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DummyValue;

// KONCLUDE-PORT-NOTE[threading][memory-pool]: the `CacheSettings.h` container
// typedefs
//   #define CCACHINGHASH CQtManagedRestrictedModificationHash
//   #define CCACHINGLIST CQtManagedRestrictedModificationList
//   #define CCACHINGSET  CQtManagedRestrictedModificationSet
//   #define CCACHINGMAP  CQtManagedRestrictedModificationMap
// are the shared concurrent-modification containers every cache stores its
// entries in. Per the manifest they map to an arena `Vec<Entry>` + a `HashMap`
// keyed by `CacheValueHasher`, gated by the `CacheModificationTagSet` /
// `CacheTaggingPool` generation counter for bulk reset between incremental
// recomputations. They are NOT given concrete Rust aliases here (the entry type
// they parameterise over is per-family and not yet ported); each family unit
// will pick the concrete container at its own port. Recorded here as the F0
// shared decision so the families reference it rather than re-deciding.
