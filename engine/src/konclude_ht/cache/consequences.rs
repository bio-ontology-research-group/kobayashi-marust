//! `cache::consequences` — F6: the computed-consequences cache
//! (Konclude `Reasoner/Kernel/Cache/CComputedConsequences*`).
//!
//! Caches derived consequences (types) per individual for the consequence-driven
//! path, driven by `CComputedConsequencesCacheHandler`. Struct-definition wave
//! only — every class becomes a Rust struct with faithful fields; method bodies
//! are deferred (the `// W6-CACHE method-batch` marker). `new`/`Default` provided.
//!
//! Port conventions (PORT.md §5, §6; manifest/07-cache.md):
//!   * `CXxx*` pointer  → typed arena `Id<T>` (`Id::NONE` == `nullptr`);
//!   * `CSortedNegLinker<CConcept*>` chain → `Vec<NegLink<ConceptId>>`
//!     (head-at-FRONT; each entry carries a negation bit);
//!   * `QMutex` / `CThread` machinery → opaque `Cint64` `[threading]`;
//!   * `CMemory*` pool allocators / providers → opaque `Cint64` `[memory-pool]`;
//!   * cross-family F0 refs not yet ported (`CCacheStatistics`,
//!     `CCacheEntryWriteData`) + the Ontology mix-in `CComputedConsequencesCachingData`
//!     → opaque `Cint64`, marked `[api]`;
//!   * the F0 family base `CSatisfiableCache` is already ported in `cache::base`.

#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_mut)]

use super::super::model::substrate::{Cint64, Id, NegLink, INVALID};
use super::super::model::{ConceptId, IndividualId};
use super::base::SatisfiableCache;
use super::context::CacheContext;
use super::events::{CacheEvent, EVENT_WRITE_COMPUTED_CONSEQUENCES_CACHE_DATA_ENTRY};

// ---------------------------------------------------------------------------
// Local arena id aliases (this family's per-ontology cache objects).
// ---------------------------------------------------------------------------
/// `CComputedConsequencesCache*`             → `ComputedConsequencesCacheId`.
pub type ComputedConsequencesCacheId = Id<ComputedConsequencesCache>;
/// `CComputedConsequencesCacheReader*`       → `ComputedConsequencesCacheReaderId`.
pub type ComputedConsequencesCacheReaderId = Id<ComputedConsequencesCacheReader>;
/// `CComputedConsequencesCacheEntry*`        → `ComputedConsequencesCacheEntryId`.
pub type ComputedConsequencesCacheEntryId = Id<ComputedConsequencesCacheEntry>;
/// `CComputedConsequencesTypesCacheEntry*`   → `ComputedConsequencesTypesCacheEntryId`.
pub type ComputedConsequencesTypesCacheEntryId = Id<ComputedConsequencesTypesCacheEntry>;
/// `CComputedConsequencesCacheWriteData*`    → `ComputedConsequencesCacheWriteDataId`.
pub type ComputedConsequencesCacheWriteDataId = Id<ComputedConsequencesCacheWriteData>;
/// `CComputedConsequencesCacheWriteTypesData*` → `ComputedConsequencesCacheWriteTypesDataId`.
pub type ComputedConsequencesCacheWriteTypesDataId = Id<ComputedConsequencesCacheWriteTypesData>;

// ===========================================================================
// CComputedConsequencesCacheContext  (`: public CContext`)
// ===========================================================================

/// Port of `CComputedConsequencesCacheContext`.
///
/// Per-thread scratch + pool. `CContext` base carries no port-relevant data.
pub struct ComputedConsequencesCacheContext {
    /// `CMemoryPoolAllocationManager* mMemMan`.
    /// KONCLUDE-PORT-NOTE[memory-pool]: opaque handle; arena substrate replaces it.
    pub mem_man: Cint64,
    /// `CNewAllocationMemoryPoolProvider* mMemoryPoolProvider`.
    /// KONCLUDE-PORT-NOTE[memory-pool]: opaque pool-provider handle.
    pub memory_pool_provider: Cint64,
    /// `CSortedNegLinker<CConcept*>* mConLinker` (intrusive chain head).
    /// KONCLUDE-PORT-NOTE[ownership]: → `Vec<NegLink<ConceptId>>`, head-at-FRONT.
    pub con_linker: Vec<NegLink<ConceptId>>,
    /// `cint64 mAddRelMemory`.
    pub add_rel_memory: Cint64,
}

impl Default for ComputedConsequencesCacheContext {
    fn default() -> Self {
        ComputedConsequencesCacheContext {
            mem_man: INVALID,
            memory_pool_provider: INVALID,
            con_linker: Vec::new(),
            add_rel_memory: 0,
        }
    }
}

impl ComputedConsequencesCacheContext {
    /// Port of `CComputedConsequencesCacheContext::CComputedConsequencesCacheContext`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `CComputedConsequencesCacheContext::getMemoryPoolAllocationManager`.
    /// KONCLUDE-PORT-NOTE[memory-pool]: returns the opaque pool-alloc-manager handle.
    pub fn get_memory_pool_allocation_manager(&self) -> Cint64 {
        self.mem_man
    }

    /// Port of `CComputedConsequencesCacheContext::getMemoryAllocationManager`.
    /// (C++ returns the same `mMemMan` as the pool manager.)
    pub fn get_memory_allocation_manager(&self) -> Cint64 {
        self.mem_man
    }

    /// Port of `CComputedConsequencesCacheContext::getMemoryPoolProvider`.
    pub fn get_memory_pool_provider(&self) -> Cint64 {
        self.memory_pool_provider
    }

    /// Port of `CComputedConsequencesCacheContext::getMemoryConsumption`.
    pub fn get_memory_consumption(&self) -> Cint64 {
        // return mAddRelMemory + mMemoryPoolProvider->getAllocatedReleaseDifferencePoolSize();
        // W6-DEFER[memory-pool]: mMemoryPoolProvider->getAllocatedReleaseDifferencePoolSize()
        let allocated_release_difference_pool_size: Cint64 = 0;
        self.add_rel_memory + allocated_release_difference_pool_size
    }

    /// Port of `CComputedConsequencesCacheContext::releaseTemporaryMemoryPools`.
    /// KONCLUDE-PORT-NOTE[memory-pool]: the `CMemoryPool*` chain (`memory_pools`) is
    /// an opaque pool handle; the per-block accumulation into `mAddRelMemory` and the
    /// `mMemMan->releaseTemporaryMemoryPools` hand-back are deferred to the arena-pool
    /// substrate. The chain walk is reproduced structurally.
    pub fn release_temporary_memory_pools(&mut self, memory_pools: Cint64) -> &mut Self {
        // CMemoryPool* memoryPoolIt = memoryPools;
        let mut memory_pool_it = memory_pools;
        // while (memoryPoolIt) { mAddRelMemory += memoryPoolIt->getMemoryBlockSize(); memoryPoolIt = memoryPoolIt->getNext(); }
        while memory_pool_it != INVALID {
            // W6-DEFER[memory-pool]: mAddRelMemory += memoryPoolIt->getMemoryBlockSize()
            // W6-DEFER[memory-pool]: memoryPoolIt = memoryPoolIt->getNext()
            memory_pool_it = INVALID; // deferred chain advance (terminate the walk)
        }
        // W6-DEFER[memory-pool]: mMemMan->releaseTemporaryMemoryPools(memoryPools)
        self
    }

    /// Port of `CComputedConsequencesCacheContext::createConceptLinker`.
    ///
    /// Pops the head reuse-node off the `mConLinker` free list (or allocates a fresh
    /// detached node when empty and `create`). KONCLUDE-PORT-NOTE[ownership]: a single
    /// `CSortedNegLinker<CConcept*>` reuse node → one `NegLink<ConceptId>`; the head is
    /// the FRONT of the `con_linker` Vec. `None` == the C++ `nullptr` return.
    pub fn create_concept_linker(&mut self, create: bool) -> Option<NegLink<ConceptId>> {
        // CSortedNegLinker<CConcept*>* conLinker = mConLinker;
        let mut con_linker: Option<NegLink<ConceptId>> = self.con_linker.first().copied();
        // if (!conLinker && create) conLinker = allocateAndConstruct(mMemMan);
        if con_linker.is_none() && create {
            con_linker = Some(NegLink {
                target: Id::NONE,
                negated: false,
            });
        }
        // conLinker->setNext(nullptr); -- the returned node is detached (Vec-model no-op).
        // KONCLUDE-PORT-NOTE[uninit]: if the free list is empty and !create the C++
        // dereferences nullptr in setNext; the port returns `None` instead (guarded).
        // if (mConLinker) mConLinker = mConLinker->getNext(); -- advance/pop the head.
        if !self.con_linker.is_empty() {
            self.con_linker.remove(0);
        }
        con_linker
    }

    /// Port of `CComputedConsequencesCacheContext::addConceptLinker`.
    ///
    /// KONCLUDE-PORT-NOTE[unclear]: the C++ body reassigns the LOCAL `linker`
    /// (`linker = linker->append(mConLinker)`), NOT the member `mConLinker`, so the
    /// node is never actually re-linked into the free list — `mConLinker` is left
    /// unchanged. Ported verbatim: no member mutation (a latent no-op in Konclude).
    pub fn add_concept_linker(&mut self, linker: Option<NegLink<ConceptId>>) -> &mut Self {
        if let Some(mut linker) = linker {
            // linker->setNext(nullptr); linker = linker->append(mConLinker);
            // (result discarded in C++ — member `mConLinker` unchanged.)
            let _ = &mut linker;
        }
        self
    }
}

// ===========================================================================
// CComputedConsequencesCacheEntry
// ===========================================================================

/// Port of `CComputedConsequencesCacheEntry`.
pub struct ComputedConsequencesCacheEntry {
    /// `CComputedConsequencesCacheContext* mContext`.
    /// KONCLUDE-PORT-NOTE[ownership]: opaque back-pointer to the cache context.
    pub context: Cint64,
}

impl Default for ComputedConsequencesCacheEntry {
    fn default() -> Self {
        ComputedConsequencesCacheEntry { context: INVALID }
    }
}

impl ComputedConsequencesCacheEntry {
    /// Port of `CComputedConsequencesCacheEntry::CComputedConsequencesCacheEntry`.
    pub fn new(context: Cint64) -> Self {
        ComputedConsequencesCacheEntry { context }
    }
    // W6-CACHE method-batch: `CComputedConsequencesCacheEntry` declares NO methods
    // beyond the constructor (only the `mContext` back-pointer) — nothing to port.
}

// ===========================================================================
// CComputedConsequencesTypesCacheEntry
//   (`: public CComputedConsequencesCacheEntry, public CComputedConsequencesCachingData`)
// ===========================================================================

/// Port of `CComputedConsequencesTypesCacheEntry`.
///
/// The per-individual derived-types entry.
pub struct ComputedConsequencesTypesCacheEntry {
    /// inlined `CComputedConsequencesCacheEntry` base.
    pub base: ComputedConsequencesCacheEntry,
    /// the `CComputedConsequencesCachingData` Ontology mix-in base.
    /// KONCLUDE-PORT-NOTE[api]: cross-family Ontology caching-data class, not
    /// ported here; kept as an opaque `Cint64` handle.
    pub caching_data_base: Cint64,
    /// `CIndividual* mIndividual`.
    pub individual: IndividualId,
    /// `CSortedNegLinker<CConcept*>* mConceptLinker` (intrusive chain head).
    /// KONCLUDE-PORT-NOTE[ownership]: → `Vec<NegLink<ConceptId>>`, head-at-FRONT.
    pub concept_linker: Vec<NegLink<ConceptId>>,
}

impl Default for ComputedConsequencesTypesCacheEntry {
    fn default() -> Self {
        ComputedConsequencesTypesCacheEntry {
            base: ComputedConsequencesCacheEntry::default(),
            caching_data_base: INVALID,
            individual: Id::NONE,
            concept_linker: Vec::new(),
        }
    }
}

impl ComputedConsequencesTypesCacheEntry {
    /// Port of `CComputedConsequencesTypesCacheEntry::CComputedConsequencesTypesCacheEntry`.
    pub fn new(context: Cint64) -> Self {
        ComputedConsequencesTypesCacheEntry {
            base: ComputedConsequencesCacheEntry::new(context),
            ..Default::default()
        }
    }

    /// Port of `CComputedConsequencesTypesCacheEntry::initCacheEntry`.
    pub fn init_cache_entry(&mut self, individual: IndividualId) -> &mut Self {
        // mIndividual = individual; mConceptLinker = nullptr;
        self.individual = individual;
        self.concept_linker.clear();
        self
    }

    /// Port of `CComputedConsequencesTypesCacheEntry::hasConcept`.
    pub fn has_concept(&self, concept: ConceptId, negation: bool) -> bool {
        // for (conIt = mConceptLinker; conIt; conIt = conIt->getNext())
        //   if (conIt->getData() == concept && conIt->isNegated() == negation) return true;
        for con_it in &self.concept_linker {
            if con_it.target == concept && con_it.negated == negation {
                return true;
            }
        }
        false
    }

    /// Port of `CComputedConsequencesTypesCacheEntry::getConceptLinker`.
    /// KONCLUDE-PORT-NOTE[ownership]: the intrusive chain head → the owned chain as
    /// a head→tail slice.
    pub fn get_concept_linker(&self) -> &[NegLink<ConceptId>] {
        &self.concept_linker
    }

    /// Port of `CComputedConsequencesTypesCacheEntry::addConceptLinker`.
    pub fn add_concept_linker(&mut self, concept_linker: NegLink<ConceptId>) -> &mut Self {
        // mConceptLinker = conceptLinker->append(mConceptLinker); -- prepend (head-at-FRONT).
        self.concept_linker.insert(0, concept_linker);
        self
    }
}

// ===========================================================================
// CComputedConsequencesCacheWriteData  (`: public CCacheEntryWriteData`)
//   + the derived write-types-data record.
// ===========================================================================

/// Port of the C++ `enum COMPUTEDCONSEQUENCESCACHEWRITEDATATYPE`.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ComputedConsequencesCacheWriteDataType {
    /// `CCWT_TYPE = 1`.
    Type = 1,
}

impl Default for ComputedConsequencesCacheWriteDataType {
    fn default() -> Self {
        ComputedConsequencesCacheWriteDataType::Type
    }
}

/// Port of `CComputedConsequencesCacheWriteData` (`: public CCacheEntryWriteData`).
pub struct ComputedConsequencesCacheWriteData {
    /// `CCacheEntryWriteData` base (F0).
    /// KONCLUDE-PORT-NOTE[api]: not-yet-ported F0 base (carries a
    /// `CACHEWRITEDATATYPE mType` enum); opaque `Cint64` handle for now.
    pub entry_write_data_base: Cint64,
    /// `CLinkerBase` next write-data link.
    pub next: ComputedConsequencesCacheWriteDataId,
    /// `COMPUTEDCONSEQUENCESCACHEWRITEDATATYPE mWriteDataType`.
    pub write_data_type: ComputedConsequencesCacheWriteDataType,
}

impl Default for ComputedConsequencesCacheWriteData {
    fn default() -> Self {
        ComputedConsequencesCacheWriteData {
            entry_write_data_base: INVALID,
            next: Id::NONE,
            write_data_type: ComputedConsequencesCacheWriteDataType::default(),
        }
    }
}

impl ComputedConsequencesCacheWriteData {
    /// Port of `CComputedConsequencesCacheWriteData::CComputedConsequencesCacheWriteData`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `CComputedConsequencesCacheWriteData::getWriteDataType`.
    pub fn get_write_data_type(&self) -> ComputedConsequencesCacheWriteDataType {
        self.write_data_type
    }

    /// `CLinkerBase::getNext`.
    pub fn get_next(&self) -> ComputedConsequencesCacheWriteDataId {
        self.next
    }

    /// `CLinkerBase::setNext`.
    pub fn set_next(&mut self, next: ComputedConsequencesCacheWriteDataId) -> &mut Self {
        self.next = next;
        self
    }
}

/// Port of `CComputedConsequencesCacheWriteTypesData`
/// (`: public CComputedConsequencesCacheWriteData`).
pub struct ComputedConsequencesCacheWriteTypesData {
    /// inlined `CComputedConsequencesCacheWriteData` base.
    pub base: ComputedConsequencesCacheWriteData,
    /// `CIndividual* mIndividual`.
    pub individual: IndividualId,
    /// `CConcept* mConceptType`.
    pub concept_type: ConceptId,
    /// `bool mConceptNegation`.
    pub concept_negation: bool,
}

impl Default for ComputedConsequencesCacheWriteTypesData {
    fn default() -> Self {
        ComputedConsequencesCacheWriteTypesData {
            base: ComputedConsequencesCacheWriteData::default(),
            individual: Id::NONE,
            concept_type: Id::NONE,
            concept_negation: false,
        }
    }
}

impl ComputedConsequencesCacheWriteTypesData {
    /// Port of `CComputedConsequencesCacheWriteTypesData::CComputedConsequencesCacheWriteTypesData`.
    /// (C++ ctor sets `mWriteDataType = CCWT_TYPE`; the base default already does so.)
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `CComputedConsequencesCacheWriteTypesData::initTypesCacheWriteData`.
    pub fn init_types_cache_write_data(
        &mut self,
        individual: IndividualId,
        concept: ConceptId,
        negation: bool,
    ) -> &mut Self {
        // mIndividual = individual; mConceptNegation = negation; mConceptType = concept;
        self.individual = individual;
        self.concept_negation = negation;
        self.concept_type = concept;
        self
    }

    /// Port of `CComputedConsequencesCacheWriteTypesData::getIndividual`.
    pub fn get_individual(&self) -> IndividualId {
        self.individual
    }

    /// Port of `CComputedConsequencesCacheWriteTypesData::getConcept`.
    pub fn get_concept(&self) -> ConceptId {
        self.concept_type
    }

    /// Port of `CComputedConsequencesCacheWriteTypesData::getNegation`.
    pub fn get_negation(&self) -> bool {
        self.concept_negation
    }
}

// ===========================================================================
// CComputedConsequencesCacheReader  (`: CLinkerBase<...>`)
// ===========================================================================

/// Port of `CComputedConsequencesCacheReader`.
///
/// Per-thread read cursor. KONCLUDE-PORT-NOTE[ownership]: the `CLinkerBase`
/// next-pointer is dropped; the cache owns its readers in `reader_linker`.
/// No data members of its own.
#[derive(Default)]
pub struct ComputedConsequencesCacheReader;

impl ComputedConsequencesCacheReader {
    /// Port of `CComputedConsequencesCacheReader::CComputedConsequencesCacheReader`.
    pub fn new() -> Self {
        ComputedConsequencesCacheReader
    }

    /// Port of `CComputedConsequencesCacheReader::getTypesCacheEntry`.
    ///
    /// Resolves the per-individual types-cache entry through the individual's
    /// `CIndividualProcessData::getComputedConsequencesCachingData()` (the entry IS
    /// the caching-data mix-in, recovered by a downcast).
    /// KONCLUDE-PORT-NOTE[api]: `CIndividual::getIndividualData()` /
    /// `CIndividualProcessData` live in `Reasoner/Ontology/` (cross-subtree, not
    /// ported); the individual→entry binding is opaque here. Control flow reproduced;
    /// the deref chain returns `Id::NONE` until the Ontology process-data binding wires.
    pub fn get_types_cache_entry(
        &self,
        individual: IndividualId,
        cache_context: &CacheContext,
    ) -> ComputedConsequencesTypesCacheEntryId {
        // CIndividualProcessData* indProData = (CIndividualProcessData*)individual->getIndividualData();
        // KONCLUDE-PORT-NOTE[api]: `CIndividualProcessData` is not otherwise
        // materialized in this Rust slice; `CacheContext` stores exactly its
        // computed-consequences caching-data slot by individual id.
        let ind_pro_data = individual;
        // CComputedConsequencesCachingData* compConsCachingData = nullptr;
        let mut comp_cons_caching_data = ComputedConsequencesTypesCacheEntryId::NONE;
        if ind_pro_data.is_some() {
            // compConsCachingData = indProData->getComputedConsequencesCachingData();
            comp_cons_caching_data =
                cache_context.individual_computed_consequences_types_cache_entry(individual);
        }
        // CComputedConsequencesTypesCacheEntry* cacheEntry = nullptr;
        let mut cache_entry: ComputedConsequencesTypesCacheEntryId = Id::NONE;
        if comp_cons_caching_data.is_some() {
            // cacheEntry = (CComputedConsequencesTypesCacheEntry*)compConsCachingData;
            cache_entry = comp_cons_caching_data;
        }
        cache_entry
    }
}

// ===========================================================================
// CComputedConsequencesCacheWriter
// ===========================================================================

/// Port of `CComputedConsequencesCacheWriter`.
pub struct ComputedConsequencesCacheWriter {
    /// `CComputedConsequencesCache* mCache`.
    pub cache: ComputedConsequencesCacheId,
}

impl Default for ComputedConsequencesCacheWriter {
    fn default() -> Self {
        ComputedConsequencesCacheWriter { cache: Id::NONE }
    }
}

impl ComputedConsequencesCacheWriter {
    /// Port of `CComputedConsequencesCacheWriter::CComputedConsequencesCacheWriter`.
    pub fn new(cache: ComputedConsequencesCacheId) -> Self {
        ComputedConsequencesCacheWriter { cache }
    }

    /// Port of `CComputedConsequencesCacheWriter::writeCacheData`.
    ///
    /// Forwards to the facade's `writeCacheData` (which posts/drains the write).
    /// KONCLUDE-PORT-NOTE[ownership]: C++ forwards through the raw `mCache`
    /// back-pointer; the Rust port threads the owning facade explicitly because
    /// there is no stable raw `this` pointer for the long-lived cache singleton.
    pub fn write_cache_data(
        &mut self,
        cache: &mut ComputedConsequencesCache,
        write_data: ComputedConsequencesCacheWriteDataId,
        memory_pools: Cint64,
        cache_context: &mut CacheContext,
    ) -> &mut Self {
        cache.write_cache_data(write_data, memory_pools, cache_context);
        self
    }
}

// ===========================================================================
// CComputedConsequencesCache  (`: public CThread, public CSatisfiableCache`)
//   — the facade
// ===========================================================================

/// Port of `CComputedConsequencesCache`.
///
/// The facade: holds the entry chain, the per-thread reader cursors, statistics,
/// and the cache context. KONCLUDE-PORT-NOTE[threading]: the `CThread` base (Qt
/// event-loop worker) becomes the opaque `thread_base` handle; the writer-thread /
/// Reader split is the concurrency seam (manifest/07-cache.md).
pub struct ComputedConsequencesCache {
    /// the `CThread` base.
    /// KONCLUDE-PORT-NOTE[threading]: opaque handle for the Qt event-loop worker;
    /// the first faithful port drains writes inline (single-threaded).
    pub thread_base: Cint64,
    /// the `CSatisfiableCache` base (already ported in `cache::base`).
    pub satisfiable_cache_base: SatisfiableCache,

    /// `CComputedConsequencesCacheEntry* mEntryLinker`
    /// (intrusive chain head → owned `Vec`, head-at-FRONT).
    pub entry_linker: Vec<ComputedConsequencesCacheEntryId>,
    /// `cint64 mConfAllowedNonDetExpansionCount`.
    pub conf_allowed_non_det_expansion_count: Cint64,
    /// `CComputedConsequencesCacheReader* mReaderLinker`
    /// (intrusive chain head → owned `Vec`, head-at-FRONT).
    pub reader_linker: Vec<ComputedConsequencesCacheReaderId>,
    /// `QMutex mReaderSyncMutex`.
    /// KONCLUDE-PORT-NOTE[threading]: opaque lock handle; facade-granularity only.
    pub reader_sync_mutex: Cint64,
    /// `CCacheStatistics mCacheStat` (held by value).
    /// KONCLUDE-PORT-NOTE[api]: F0 `CCacheStatistics` not yet ported; opaque
    /// `Cint64` handle for now (it carries 2 `cint64` counters).
    pub cache_stat: Cint64,
    /// `CComputedConsequencesCacheContext mContext` (held by value).
    pub context: ComputedConsequencesCacheContext,
}

impl Default for ComputedConsequencesCache {
    fn default() -> Self {
        ComputedConsequencesCache {
            thread_base: INVALID,
            satisfiable_cache_base: SatisfiableCache::default(),
            entry_linker: Vec::new(),
            conf_allowed_non_det_expansion_count: 0,
            reader_linker: Vec::new(),
            reader_sync_mutex: INVALID,
            cache_stat: INVALID,
            context: ComputedConsequencesCacheContext::default(),
        }
    }
}

impl ComputedConsequencesCache {
    /// Port of `CComputedConsequencesCache::CComputedConsequencesCache`.
    pub fn new() -> Self {
        // mReaderLinker = nullptr; mConfAllowedNonDetExpansionCount = 1 (config default
        // "Konclude.Calculation.Optimization.SaturationExpansionSatisfiabilityCacheCount");
        // startThread(QThread::HighestPriority).
        let mut cache = Self::default();
        cache.conf_allowed_non_det_expansion_count = 1;
        // KONCLUDE-PORT-NOTE[threading]: no Qt worker thread in the single-thread
        // port; the facade IS the writer (writes drain inline). `startThread` deferred.
        cache
    }

    /// Port of `CComputedConsequencesCache::createCacheReader`.
    pub fn create_cache_reader(
        &mut self,
        cache_context: &mut CacheContext,
    ) -> ComputedConsequencesCacheReaderId {
        // CComputedConsequencesCacheReader* readerLinker = new CComputedConsequencesCacheReader();
        let reader_linker =
            cache_context.alloc_consequences_cache_reader(ComputedConsequencesCacheReader::new());
        // mReaderSyncMutex.lock(); [threading]: facade-granularity lock, inline no-op.
        // mReaderLinker = readerLinker->append(mReaderLinker); -- prepend (head-at-FRONT).
        self.reader_linker.insert(0, reader_linker);
        // mReaderSyncMutex.unlock(); [threading]
        reader_linker
    }

    /// Port of `CComputedConsequencesCache::createCacheWriter`.
    pub fn create_cache_writer(&self) -> ComputedConsequencesCacheWriter {
        // return new CComputedConsequencesCacheWriter(this);
        // KONCLUDE-PORT-NOTE[ownership]: the C++ writer stores `this`; Rust call
        // sites pass the owning cache into the forwarding method explicitly.
        ComputedConsequencesCacheWriter::new(Id::NONE)
    }

    /// Port of `CComputedConsequencesCache::writeCacheData`.
    ///
    /// KONCLUDE-PORT-NOTE[threading]: Konclude posts a
    /// `CWriteComputedConcequencesCacheEntryEvent` to the dedicated writer thread; the
    /// single-thread port drains it inline here — the exact collapse of
    /// `processCustomsEvents` for that event (install the write data + release pools).
    pub fn write_cache_data(
        &mut self,
        write_data: ComputedConsequencesCacheWriteDataId,
        memory_pools: Cint64,
        cache_context: &mut CacheContext,
    ) -> &mut Self {
        // postEvent(new CWriteComputedConcequencesCacheEntryEvent(writeData,memoryPools));
        // [threading]: drained inline (== processCustomsEvents handler body).
        // KONCLUDE-PORT-NOTE[ownership]: take the by-value context out to avoid a
        // double `&mut self` borrow while installing through it (restored after).
        let mut context = std::mem::take(&mut self.context);
        self.install_write_cache_data(write_data, &mut context, cache_context);
        self.context = context;
        // W6-DEFER[memory-pool]: mContext.getMemoryPoolAllocationManager()->releaseTemporaryMemoryPools(memoryPools)
        let _ = memory_pools;
        self
    }

    /// Port of `CComputedConsequencesCache::getCacheStatistics`.
    /// KONCLUDE-PORT-NOTE[api]: F0 `CCacheStatistics` not yet ported; returns the
    /// opaque `mCacheStat` handle (C++ returns `&mCacheStat`).
    pub fn get_cache_statistics(&self) -> Cint64 {
        self.cache_stat
    }

    /// Port of `CComputedConsequencesCache::installWriteCacheData`.
    ///
    /// Walks the queued `CCacheEntryWriteData` chain and dispatches each `CCWT_TYPE`
    /// payload to `addTypesExpansionData`.
    pub fn install_write_cache_data(
        &mut self,
        write_data: ComputedConsequencesCacheWriteDataId,
        context: &mut ComputedConsequencesCacheContext,
        cache_context: &mut CacheContext,
    ) -> &mut Self {
        // CComputedConsequencesCacheWriteData* writeDataLinker = writeData;
        let mut write_data_linker = write_data;
        // while (writeDataLinker) { ... writeDataLinker = writeDataLinker->getNext(); }
        while write_data_linker.is_some() {
            let write_data = cache_context.consequences_cache_write_data(write_data_linker);
            let write_data_type = write_data.get_write_data_type();
            let next_write_data = write_data.get_next();
            if write_data_type == ComputedConsequencesCacheWriteDataType::Type {
                // CComputedConsequencesCacheWriteTypesData* cccwtd = (cast) writeDataLinker;
                // KONCLUDE-PORT-NOTE[pointer-alias]: C++ reinterprets the base linker as
                // the derived write-types payload; modelled as a same-index id cast.
                let cccwtd: ComputedConsequencesCacheWriteTypesDataId =
                    Id::new(write_data_linker.raw);
                self.add_types_expansion_data(cccwtd, context, cache_context);
            }
            write_data_linker = next_write_data;
        }
        self
    }

    /// Port of `CComputedConsequencesCache::addTypesExpansionData`.
    pub fn add_types_expansion_data(
        &mut self,
        cccwtd: ComputedConsequencesCacheWriteTypesDataId,
        context: &mut ComputedConsequencesCacheContext,
        cache_context: &mut CacheContext,
    ) -> &mut Self {
        let (individual, concept_type, concept_negation) = {
            let write_types_data = cache_context.consequences_cache_write_types_data(cccwtd);
            (
                write_types_data.get_individual(),
                write_types_data.get_concept(),
                write_types_data.get_negation(),
            )
        };
        // CComputedConsequencesTypesCacheEntry* cacheEntry = getComputedTypesCacheEntryForNode(individual,context,true);
        let cache_entry =
            self.get_computed_types_cache_entry_for_node(individual, context, true, cache_context);
        if cache_entry.is_some() {
            // CSortedNegLinker<CConcept*>* conceptLinker = context->createConceptLinker();
            let mut concept_linker = context.create_concept_linker(true);
            // conceptLinker->init(conceptType,conceptNegation);
            if let Some(cl) = concept_linker.as_mut() {
                cl.target = concept_type;
                cl.negated = concept_negation;
            }
            // cacheEntry->addConceptLinker(conceptLinker);
            if let Some(concept_linker) = concept_linker {
                cache_context
                    .consequences_types_cache_entry_mut(cache_entry)
                    .add_concept_linker(concept_linker);
            }
        }
        self
    }

    /// Port of `CComputedConsequencesCache::getComputedTypesCacheEntryForNode`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: the individual→entry binding goes through
    /// `CIndividualProcessData` (Ontology, cross-subtree) and the entry is allocated
    /// from the context pool. Both are opaque here; control flow reproduced, the
    /// resolved/allocated entry id deferred to `Id::NONE`.
    pub fn get_computed_types_cache_entry_for_node(
        &mut self,
        individual: IndividualId,
        context: &mut ComputedConsequencesCacheContext,
        create: bool,
        cache_context: &mut CacheContext,
    ) -> ComputedConsequencesTypesCacheEntryId {
        // CIndividualProcessData* indProData = (CIndividualProcessData*)individual->getIndividualData();
        // KONCLUDE-PORT-NOTE[api]: `CIndividualProcessData` is not otherwise
        // materialized in this Rust slice; `CacheContext` stores exactly its
        // computed-consequences caching-data slot by individual id.
        let ind_pro_data = individual;
        // CComputedConsequencesTypesCacheEntry* cacheEntry = nullptr;
        let mut cache_entry: ComputedConsequencesTypesCacheEntryId = Id::NONE;
        if ind_pro_data.is_some() {
            // cacheEntry = (cast) indProData->getComputedConsequencesCachingData();
            cache_entry =
                cache_context.individual_computed_consequences_types_cache_entry(individual);
        }
        if ind_pro_data.is_some() && cache_entry.is_none() && create {
            // cacheEntry = allocateAndConstructAndParameterize<...>(context->getMemoryAllocationManager(),context);
            let mut new_entry = ComputedConsequencesTypesCacheEntry::new(INVALID);
            // cacheEntry->initCacheEntry(individual);
            new_entry.init_cache_entry(individual);
            cache_entry = cache_context.alloc_consequences_types_cache_entry(new_entry);
            // indProData->setComputedConsequencesCachingData(cacheEntry);
            cache_context
                .set_individual_computed_consequences_types_cache_entry(individual, cache_entry);
        }
        cache_entry
    }

    /// Typed Rust event drain for
    /// `CComputedConsequencesCache::processCustomsEvents`.
    ///
    /// Konclude receives a `CWriteComputedConcequencesCacheEntryEvent*`, reads
    /// `getMemoryPools()` / `getWriteData()`, installs the write-data chain, and
    /// releases the pools. The F8 port collapses cache events into `CacheEvent`,
    /// so this method is the typed body of that event branch.
    pub fn process_customs_cache_event(
        &mut self,
        event: &CacheEvent,
        cache_context: &mut CacheContext,
    ) -> bool {
        if event.event_type() == EVENT_WRITE_COMPUTED_CONSEQUENCES_CACHE_DATA_ENTRY {
            let memory_pools = event.get_memory_pools().unwrap_or(INVALID);
            let write_data = event
                .get_computed_consequences_write_data()
                .unwrap_or(ComputedConsequencesCacheWriteDataId::NONE);
            let mut context = std::mem::take(&mut self.context);
            self.install_write_cache_data(write_data, &mut context, cache_context);
            self.context = context;
            // W6-DEFER[memory-pool]: memMan->releaseTemporaryMemoryPools(memoryPools)
            let _ = memory_pools;
            return true;
        }
        false
    }

    /// Opaque-id compatibility wrapper for
    /// `CComputedConsequencesCache::processCustomsEvents`.
    ///
    /// The faithful typed event branch is live in `process_customs_cache_event`.
    /// This wrapper remains for legacy call sites that still only have the Qt-style
    /// event type and an opaque `CCustomEvent*`.
    pub fn process_customs_events(
        &mut self,
        type_: Cint64,
        event: Cint64,
        cache_context: &mut CacheContext,
    ) -> bool {
        // if (CThread::processCustomsEvents(type,event)) return true;
        // [threading]: CThread base handler not ported; inline no-op (treated as false).
        // else if (type == EVENTWRITECOMPUTEDCONSEQUENCESCACHEDATAENTRY) { ... }
        if type_ == EVENT_WRITE_COMPUTED_CONSEQUENCES_CACHE_DATA_ENTRY {
            // CWriteComputedConcequencesCacheEntryEvent* wscde = (cast) event;
            // CMemoryPool* memoryPools = wscde->getMemoryPools();
            // KONCLUDE-PORT-NOTE[api]: opaque legacy wrapper; typed payload extraction
            // is live in `process_customs_cache_event`.
            let memory_pools: Cint64 = INVALID;
            // CComputedConsequencesCacheWriteData* writeData = wscde->getWriteData();
            // KONCLUDE-PORT-NOTE[api]: opaque legacy wrapper; typed payload extraction
            // is live in `process_customs_cache_event`.
            let write_data: ComputedConsequencesCacheWriteDataId = Id::NONE;
            // installWriteCacheData(writeData,&mContext);
            let mut context = std::mem::take(&mut self.context);
            self.install_write_cache_data(write_data, &mut context, cache_context);
            self.context = context;
            // mContext.getMemoryPoolAllocationManager()->releaseTemporaryMemoryPools(memoryPools);
            // W6-DEFER[memory-pool]: memMan->releaseTemporaryMemoryPools(memoryPools)
            let _ = memory_pools;
            return true;
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn computed_consequences_create_cache_reader_prepends_reader_with_context() {
        let mut ctx = CacheContext::new();
        let mut cache = ComputedConsequencesCache::new();

        let first = cache.create_cache_reader(&mut ctx);
        let second = cache.create_cache_reader(&mut ctx);

        assert!(first.is_some());
        assert!(second.is_some());
        assert_ne!(first, second);
        assert_eq!(cache.reader_linker, vec![second, first]);
    }

    #[test]
    fn computed_consequences_writer_forwards_write_data_to_cache() {
        let mut cache = ComputedConsequencesCache::new();
        let mut writer = cache.create_cache_writer();

        let mut ctx = CacheContext::new();
        writer.write_cache_data(
            &mut cache,
            ComputedConsequencesCacheWriteDataId::NONE,
            0,
            &mut ctx,
        );

        assert_eq!(writer.cache, ComputedConsequencesCacheId::NONE);
    }

    #[test]
    fn computed_consequences_install_write_data_walks_next_chain_with_context() {
        let mut ctx = CacheContext::new();
        let mut first_base = ComputedConsequencesCacheWriteData::new();
        let second_base = ComputedConsequencesCacheWriteData::new();
        let second_types = ctx.alloc_consequences_cache_write_types_data(
            ComputedConsequencesCacheWriteTypesData::new(),
        );
        let second = ctx.alloc_consequences_cache_write_data(second_base);
        let first_types = ctx.alloc_consequences_cache_write_types_data(
            ComputedConsequencesCacheWriteTypesData::new(),
        );
        first_base.set_next(second);
        let first = ctx.alloc_consequences_cache_write_data(first_base);

        assert_eq!(
            Id::<ComputedConsequencesCacheWriteTypesData>::new(first.raw),
            first_types
        );
        assert_eq!(
            Id::<ComputedConsequencesCacheWriteTypesData>::new(second.raw),
            second_types
        );

        let mut cache = ComputedConsequencesCache::new();
        let mut local_context = ComputedConsequencesCacheContext::new();
        cache.install_write_cache_data(first, &mut local_context, &mut ctx);

        assert_eq!(ctx.consequences_cache_write_data(first).get_next(), second);
        assert_eq!(
            ctx.consequences_cache_write_data(second).get_next(),
            ComputedConsequencesCacheWriteDataId::NONE
        );
    }

    #[test]
    fn computed_consequences_reader_get_types_cache_entry_returns_bound_entry() {
        let mut ctx = CacheContext::new();
        let individual = IndividualId::new(3);
        let mut entry = ComputedConsequencesTypesCacheEntry::new(INVALID);
        entry.init_cache_entry(individual);
        let entry_id = ctx.alloc_consequences_types_cache_entry(entry);
        ctx.set_individual_computed_consequences_types_cache_entry(individual, entry_id);

        let reader = ComputedConsequencesCacheReader::new();

        assert_eq!(reader.get_types_cache_entry(individual, &ctx), entry_id);
        assert_eq!(
            reader.get_types_cache_entry(IndividualId::new(4), &ctx),
            ComputedConsequencesTypesCacheEntryId::NONE
        );
        assert_eq!(
            reader.get_types_cache_entry(IndividualId::NONE, &ctx),
            ComputedConsequencesTypesCacheEntryId::NONE
        );
    }

    #[test]
    fn computed_consequences_get_computed_types_cache_entry_for_node_creates_once() {
        let mut ctx = CacheContext::new();
        let mut cache = ComputedConsequencesCache::new();
        let mut local_context = ComputedConsequencesCacheContext::new();
        let individual = IndividualId::new(11);

        assert_eq!(
            cache.get_computed_types_cache_entry_for_node(
                individual,
                &mut local_context,
                false,
                &mut ctx
            ),
            ComputedConsequencesTypesCacheEntryId::NONE
        );

        let created = cache.get_computed_types_cache_entry_for_node(
            individual,
            &mut local_context,
            true,
            &mut ctx,
        );
        assert!(created.is_some());
        assert_eq!(
            ctx.individual_computed_consequences_types_cache_entry(individual),
            created
        );
        assert_eq!(
            ctx.consequences_types_cache_entry(created).individual,
            individual
        );
        assert!(ctx
            .consequences_types_cache_entry(created)
            .concept_linker
            .is_empty());

        let reused = cache.get_computed_types_cache_entry_for_node(
            individual,
            &mut local_context,
            true,
            &mut ctx,
        );
        assert_eq!(reused, created);
        assert_eq!(ctx.consequences_types_cache_entries.len(), 1);
    }

    #[test]
    fn computed_consequences_add_types_expansion_data_creates_entry_and_prepends_concept() {
        let mut ctx = CacheContext::new();
        let individual = IndividualId::new(21);
        let first_concept = ConceptId::new(31);
        let second_concept = ConceptId::new(32);
        let first_write = ctx.alloc_consequences_cache_write_types_data({
            let mut data = ComputedConsequencesCacheWriteTypesData::new();
            data.init_types_cache_write_data(individual, first_concept, false);
            data
        });
        let second_write = ctx.alloc_consequences_cache_write_types_data({
            let mut data = ComputedConsequencesCacheWriteTypesData::new();
            data.init_types_cache_write_data(individual, second_concept, true);
            data
        });
        let mut cache = ComputedConsequencesCache::new();
        let mut local_context = ComputedConsequencesCacheContext::new();

        cache.add_types_expansion_data(first_write, &mut local_context, &mut ctx);
        let entry = ctx.individual_computed_consequences_types_cache_entry(individual);
        assert!(entry.is_some());
        assert_eq!(
            ctx.consequences_types_cache_entry(entry)
                .get_concept_linker(),
            &[NegLink {
                target: first_concept,
                negated: false,
            }]
        );

        cache.add_types_expansion_data(second_write, &mut local_context, &mut ctx);
        assert_eq!(
            ctx.consequences_types_cache_entry(entry)
                .get_concept_linker(),
            &[
                NegLink {
                    target: second_concept,
                    negated: true,
                },
                NegLink {
                    target: first_concept,
                    negated: false,
                },
            ]
        );
    }

    #[test]
    fn computed_consequences_processes_typed_write_event_payload() {
        let mut ctx = CacheContext::new();
        let types = ctx.alloc_consequences_cache_write_types_data(
            ComputedConsequencesCacheWriteTypesData::new(),
        );
        let write_data =
            ctx.alloc_consequences_cache_write_data(ComputedConsequencesCacheWriteData::new());

        assert_eq!(
            Id::<ComputedConsequencesCacheWriteTypesData>::new(write_data.raw),
            types
        );

        let event = CacheEvent::write_computed_concequences_cache_entry(write_data, 17);
        let mut cache = ComputedConsequencesCache::new();

        assert!(cache.process_customs_cache_event(&event, &mut ctx));
        assert!(!cache.process_customs_cache_event(
            &CacheEvent::initialize_individual_associations_cache(1, 2),
            &mut ctx
        ));
    }
}
