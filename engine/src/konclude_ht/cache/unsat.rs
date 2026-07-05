//! `cache::unsat` — F3, the **occurrence-unsatisfiable cache** family
//! (Konclude `Source/Reasoner/Kernel/Cache/`, manifest `07-cache.md` §F3).
//!
//! This is the clash-signature cache: when a label set has been proven
//! unsatisfiable, its occurrence signature is stored here so a later test over a
//! superset short-circuits to UNSAT without re-saturating. The completion engine
//! reaches it only through the Algorithm-layer `CUnsatisfiableCacheHandler` (a
//! marker in `completion::stubs`); this subtree is the cache + Reader + Writer +
//! Entry / EntriesHash / UpdateSlotItem storage that handler drives.
//!
//! ## What this file is (struct-definition sub-wave only)
//!
//! STRUCT DEFINITIONS for the 10 F3 classes, with faithful fields and `new` /
//! `Default` constructors. NO method bodies yet — every real method body lands in
//! the later `// W6-CACHE method-batch` (see markers). The file is intentionally
//! NOT wired into a `mod.rs`; it does not compile in isolation and is not meant
//! to (it references the global `substrate` by relative path so it slots in when
//! `cache/mod.rs` is eventually added).
//!
//! ## License (per `PORT.md` §License note)
//!
//! Function-by-function translation of LGPLv3 Konclude source; the LGPL terms
//! attach to this ported module. Keep `konclude_ht/` self-contained and
//! LGPL-headed so the obligation stays scoped.
//!
//! ## Port conventions applied (PORT.md §44)
//!
//! * `CXxx*` pointer → typed arena `Id<T>` (`Id::NONE` == `nullptr`).
//!   See `model/substrate.rs` for the single global `[ownership]` decision.
//! * intrusive / `QList` / `QVector` / `QLinkedList` chains → owned `Vec<Id>`,
//!   head-at-FRONT (the canonical CLinker convention, PORT.md §6).
//! * `QMutex` / `QSemaphore` / `QReadWriteLock` / `QAtomicInt` / `QAtomicPointer`
//!   → opaque `Cint64` `[threading]` (this whole subtree is the shared-mutable
//!   surface; the Reader/Writer/Event split is the concurrency model — see
//!   manifest §Concurrency). The first faithful port runs single-threaded.
//! * pool / tagging allocators (`CCacheTaggingPool`, `CDynamicExpandingMemoryManager`)
//!   → opaque `Cint64` `[memory-pool]`.
//! * **cross-family refs → opaque `Cint64`**: `CCacheValue`, `CCacheEntry`,
//!   `CCacheStatistics`, `CCacheTaggingPool` live in F0 (`cache/value.rs`,
//!   `cache/base.rs`, not yet ported) and `CThread` / `CWatchDog` are infra; they
//!   are referenced here opaquely until their own units land.
//!
//! ## Record-families / enums
//!
//! Per manifest §Record-families, the F3 `*UpdateSlotItem` is grouped with the
//! Backend/Signature/Reuse slot items into a future cross-family generic
//! `SlotItem<T>` — that collapse belongs to the shared F0 unit, NOT here, and the
//! OccurrenceUnsat update-slot is structurally distinct anyway (it carries an
//! updated-entry set + hash list + atomic reader count, not an open-addressing
//! slot). So **no F3-internal tagged enum is formed** in this file (enums = 0).

#![allow(dead_code)]

use std::collections::{HashMap, HashSet};

use super::super::model::concept_process::UnsatisfiableCachingTags;
use super::super::model::ontology::OntologyArenas;
use super::super::model::substrate::{Arena, Cint64, Id, INVALID};
use super::super::model::{ConceptId, ConceptProcessDataId};
use super::value::{CacheValue, CacheValueIdentifier};

// ===========================================================================
// Cross-family opaque placeholders (F0 / infra — ported in their own units).
// ===========================================================================

/// Port of `CCacheValue` (`CTrible<qint64>` + a `CACHEVALUEIDENTIFIER` tag) — the
/// generic hashed cache key/value every cache family stores.
///
/// KONCLUDE-PORT-NOTE[api]: F0 (`cache/value.rs`) is now ported, so per PORT.md
/// §W6 ("the per-family opaque value aliases are intentionally NOT yet unified
/// onto `value::CacheValue` — that is a method-batch-era decision") this
/// method-batch wave unifies the F3 alias onto the real `value::CacheValue`
/// struct. The method bodies need the value's `getTag()` (`.first`),
/// `getIdentification()` (`.second`) and `getCacheValueIdentifier()` (`.third`)
/// accessors and value-keyed hashing (`CacheValue: Hash + Eq + Copy`), which the
/// bare `Cint64` could not provide. A `QList<CCacheValue>` / `QVector<CCacheValue>`
/// value list → `Vec<CCacheValue>`.
pub type CCacheValue = CacheValue;

// ===========================================================================
// F3 arena id aliases (the typed replacements for the `CXxx*` back-pointers).
// KONCLUDE-PORT-NOTE[ownership]: an `Arena<T>` for each lives in the eventual
// cache context; these alias the `Id<T>` that indexes it.
// ===========================================================================

/// `COccurrenceUnsatisfiableCache*` → `CacheId`.
pub type CacheId = Id<OccurrenceUnsatisfiableCache>;
/// `COccurrenceUnsatisfiableCacheReader*` → `ReaderId`.
pub type ReaderId = Id<OccurrenceUnsatisfiableCacheReader>;
/// `COccurrenceUnsatisfiableCacheWriter*` → `WriterId`.
pub type WriterId = Id<OccurrenceUnsatisfiableCacheWriter>;
/// `COccurrenceUnsatisfiableCacheEntry*` → `EntryId`.
pub type EntryId = Id<OccurrenceUnsatisfiableCacheEntry>;
/// `COccurrenceUnsatisfiableCacheEntriesHash*` → `EntriesHashId`.
pub type EntriesHashId = Id<OccurrenceUnsatisfiableCacheEntriesHash>;
/// `COccurrenceUnsatisfiableCacheUpdateSlotItem*` → `UpdateSlotItemId`.
pub type UpdateSlotItemId = Id<OccurrenceUnsatisfiableCacheUpdateSlotItem>;

// ===========================================================================
// Abstract bases (F3 spine). Empty in Konclude — kept as faithful markers so the
// `is-a` chain (`COccurrenceUnsatisfiableCache : CUnsatisfiableCache : CCache`,
// reader/writer likewise) survives the port and methods can attach.
// ===========================================================================

/// Port of `CUnsatisfiableCache` (`: public CCache`). No fields; abstract marker.
#[derive(Debug, Default, Clone)]
pub struct UnsatisfiableCache;

impl UnsatisfiableCache {
    /// Port of `CUnsatisfiableCache::CUnsatisfiableCache`.
    pub fn new() -> Self {
        Self
    }
}

/// Port of `CUnsatisfiableCacheReader`. Abstract base (pure-virtual
/// `isUnsatisfiable` / `getUnsatisfiableItems`); no fields.
#[derive(Debug, Default, Clone)]
pub struct UnsatisfiableCacheReader;

impl UnsatisfiableCacheReader {
    /// Port of `CUnsatisfiableCacheReader::CUnsatisfiableCacheReader`.
    pub fn new() -> Self {
        Self
    }
}

/// Port of `CUnsatisfiableCacheWriter`. Abstract base (pure-virtual
/// `setUnsatisfiable`); no fields.
#[derive(Debug, Default, Clone)]
pub struct UnsatisfiableCacheWriter;

impl UnsatisfiableCacheWriter {
    /// Port of `CUnsatisfiableCacheWriter::CUnsatisfiableCacheWriter`.
    pub fn new() -> Self {
        Self
    }
}

/// Port of `CIncrementalUnsatisfiableCacheReader` (`: public CUnsatisfiableCacheReader`).
/// Adds the incremental single-value test contract; still no fields.
///
/// KONCLUDE-PORT-NOTE[ownership]: C++ inheritance → composition; the base
/// `UnsatisfiableCacheReader` is held as a `base` field on the concrete reader,
/// not re-declared here (this intermediate base is itself field-less).
#[derive(Debug, Default, Clone)]
pub struct IncrementalUnsatisfiableCacheReader;

impl IncrementalUnsatisfiableCacheReader {
    /// Port of `CIncrementalUnsatisfiableCacheReader::CIncrementalUnsatisfiableCacheReader`.
    pub fn new() -> Self {
        Self
    }
}

// ===========================================================================
// COccurrenceUnsatisfiableCacheEntriesHash
// ===========================================================================

/// Port of `COccurrenceUnsatisfiableCacheEntriesHash`
/// (`: public QHash<CCacheValue,COccurrenceUnsatisfiableCacheEntry*>`).
///
/// A reference-counted hash of cache-value → entry. The `QHash` base becomes the
/// `entries` map; the refcount governs shared deletion across update slots.
#[derive(Debug, Default, Clone)]
pub struct OccurrenceUnsatisfiableCacheEntriesHash {
    /// The `QHash<CCacheValue, COccurrenceUnsatisfiableCacheEntry*>` base.
    /// KONCLUDE-PORT-NOTE[api]: key is the opaque `CCacheValue` (`Cint64`).
    pub entries: HashMap<CCacheValue, EntryId>,
    /// `qint64 referenceCount` — shared between slots; `decReferenceCountReturnHasToBeDeleted`.
    pub reference_count: Cint64,
}

impl OccurrenceUnsatisfiableCacheEntriesHash {
    /// Port of `COccurrenceUnsatisfiableCacheEntriesHash::COccurrenceUnsatisfiableCacheEntriesHash()`
    /// — the default ctor sets `referenceCount = 1`.
    pub fn new() -> Self {
        OccurrenceUnsatisfiableCacheEntriesHash {
            entries: HashMap::new(),
            reference_count: 1,
        }
    }

    /// Port of the copy-ctor
    /// `COccurrenceUnsatisfiableCacheEntriesHash(const COccurrenceUnsatisfiableCacheEntriesHash &copyHash)`:
    /// copies the `QHash` base (`entries`) but resets `referenceCount = 1`.
    pub fn new_copy(copy_hash: &OccurrenceUnsatisfiableCacheEntriesHash) -> Self {
        OccurrenceUnsatisfiableCacheEntriesHash {
            entries: copy_hash.entries.clone(),
            reference_count: 1,
        }
    }

    /// Port of `qint64 incReferenceCount()`.
    pub fn inc_reference_count(&mut self) -> Cint64 {
        self.reference_count += 1;
        self.reference_count
    }

    /// Port of `bool decReferenceCountReturnHasToBeDeleted()`.
    pub fn dec_reference_count_return_has_to_be_deleted(&mut self) -> bool {
        self.reference_count -= 1;
        self.reference_count <= 0
    }
}

// ===========================================================================
// COccurrenceUnsatisfiableCacheEntry
// ===========================================================================

/// Port of `COccurrenceUnsatisfiableCacheEntry` (`: public CCacheEntry`).
///
/// One cached unsatisfiable-occurrence signature: its `cacheVal` key, the
/// per-slot entries-hashes that index continuation entries, read-count stats, and
/// the min/max candidate tags that bound the incremental test. `prevEntry` links
/// the global insertion chain (head-front).
#[derive(Debug, Clone)]
pub struct OccurrenceUnsatisfiableCacheEntry {
    /// KONCLUDE-PORT-NOTE[api]: the `CCacheEntry` base (F0, `cache/value.rs`) is
    /// referenced opaquely until ported; its fields fold in then.
    pub cache_entry_base: Cint64,

    /// `COccurrenceUnsatisfiableCacheEntry* prevEntry` — previous entry in the chain.
    pub prev_entry: EntryId,

    /// `qint64 updateSlotCount`.
    pub update_slot_count: Cint64,
    /// `qint64 activeSlot`.
    pub active_slot: Cint64,
    /// `COccurrenceUnsatisfiableCacheEntriesHash** cacheEntriesHashes` — one slot per
    /// update slot (a C array of pointers → `Vec`, indexed by slot).
    pub cache_entries_hashes: Vec<EntriesHashId>,
    /// `COccurrenceUnsatisfiableCacheEntriesHash* lastCacheEntriesHash`.
    pub last_cache_entries_hash: EntriesHashId,

    /// `qint64 maxItemEntry` — maximum candidate tag.
    pub max_item_entry: Cint64,
    /// `qint64 minItemEntry` — minimum candidate tag.
    pub min_item_entry: Cint64,

    /// `bool unsatTerm` — this entry is an unsatisfiable-termination point.
    pub unsat_term: bool,
    /// `bool serialized`.
    pub serialized: bool,

    /// `qint64 readCountCount` — length of `readCountVec`.
    pub read_count_count: Cint64,
    /// `qint64* readCountVec` — per-reader read counters (C array → `Vec`).
    pub read_count_vec: Vec<Cint64>,

    /// `CCacheValue cacheVal` — the key for this entry (held by value).
    pub cache_val: CCacheValue,

    /// `QList<CCacheValue>* cacheTermValuesList` — owned termination-values list.
    /// KONCLUDE-PORT-NOTE[ownership]: nullable owned pointer → `Option<Vec<_>>`
    /// (`None` == C++ `nullptr`, distinct from an empty list).
    pub cache_term_values_list: Option<Vec<CCacheValue>>,
}

impl Default for OccurrenceUnsatisfiableCacheEntry {
    fn default() -> Self {
        OccurrenceUnsatisfiableCacheEntry {
            cache_entry_base: Id::<()>::NONE.raw,
            prev_entry: EntryId::NONE,
            update_slot_count: 0,
            active_slot: 0,
            cache_entries_hashes: Vec::new(),
            last_cache_entries_hash: EntriesHashId::NONE,
            max_item_entry: 0,
            min_item_entry: 0,
            unsat_term: false,
            serialized: false,
            read_count_count: 0,
            read_count_vec: Vec::new(),
            cache_val: CacheValue::new(),
            cache_term_values_list: None,
        }
    }
}

impl OccurrenceUnsatisfiableCacheEntry {
    /// Port of `COccurrenceUnsatisfiableCacheEntry::COccurrenceUnsatisfiableCacheEntry`
    /// `(const CCacheValue &cacheValue, COccurrenceUnsatisfiableCacheEntry *prevUnsatCacheEntry,`
    /// `qint64 writeUpdateSlotCount, qint64 currentActiveSlot, qint64 readCountVecSize = 1)`.
    pub fn new(
        cache_value: CCacheValue,
        prev_unsat_cache_entry: EntryId,
        write_update_slot_count: Cint64,
        current_active_slot: Cint64,
        read_count_vec_size: Cint64,
    ) -> Self {
        // KONCLUDE-PORT-NOTE[uninit]: faithful to the C++ ctor field inits —
        // maxItemEntry = Q_INT64_C(0x8000000000000000) = i64::MIN,
        // minItemEntry = Q_INT64_C(0x7FFFFFFFFFFFFFFF) = i64::MAX. The
        // `cacheEntriesHashes` C array of `updateSlotCount` null pointers →
        // `Vec<EntriesHashId>` of `NONE`; `readCountVec` of `readCountVecSize`
        // zeros (or empty when the size is 0, matching the `readCountVec = 0`
        // null-array branch).
        let read_count_vec = if read_count_vec_size > 0 {
            vec![0 as Cint64; read_count_vec_size as usize]
        } else {
            Vec::new()
        };
        OccurrenceUnsatisfiableCacheEntry {
            cache_entry_base: Id::<()>::NONE.raw,
            prev_entry: prev_unsat_cache_entry,
            update_slot_count: write_update_slot_count,
            active_slot: current_active_slot,
            cache_entries_hashes: vec![EntriesHashId::NONE; write_update_slot_count as usize],
            last_cache_entries_hash: EntriesHashId::NONE,
            max_item_entry: i64::MIN,
            min_item_entry: i64::MAX,
            unsat_term: false,
            serialized: false,
            read_count_count: read_count_vec_size,
            read_count_vec,
            cache_val: cache_value,
            cache_term_values_list: None,
        }
    }

    /// Port of `bool isUnsatisfiableTermination()`.
    pub fn is_unsatisfiable_termination(&self) -> bool {
        self.unsat_term
    }

    /// Port of `void setMinimumCandidate(qint64 value)`.
    pub fn set_minimum_candidate(&mut self, value: Cint64) {
        self.min_item_entry = self.min_item_entry.min(value);
    }

    /// Port of `void setMaximumCandidate(qint64 value)`.
    pub fn set_maximum_candidate(&mut self, value: Cint64) {
        self.max_item_entry = self.max_item_entry.max(value);
    }

    /// Port of `void setActiveSlot(qint64 slotIndex)`.
    pub fn set_active_slot(&mut self, slot_index: Cint64) {
        self.active_slot = slot_index;
    }

    /// Port of
    /// `COccurrenceUnsatisfiableCacheEntriesHash *setCacheEntriesHashSlotGetPrevious(qint64 slotIndex, COccurrenceUnsatisfiableCacheEntriesHash *entriesHash)`.
    pub fn set_cache_entries_hash_slot_get_previous(
        &mut self,
        slot_index: Cint64,
        entries_hash: EntriesHashId,
    ) -> EntriesHashId {
        let tmp_hash = self.cache_entries_hashes[slot_index as usize];
        self.cache_entries_hashes[slot_index as usize] = entries_hash;
        self.last_cache_entries_hash = entries_hash;
        tmp_hash
    }

    /// Port of
    /// `COccurrenceUnsatisfiableCacheEntriesHash *updateSlotCacheHashGetPrevious(qint64 slotIndex)`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: dereferences the family-internal
    /// `lastCacheEntriesHash` to bump its refcount; the C++ raw pointer is the
    /// arena id here, so the owning `Arena<...EntriesHash>` is threaded in. The
    /// `is_some` guard makes the (theoretically reachable) null `lastCacheEntriesHash`
    /// case a no-op deref rather than a panic; the C++ relies on it being set.
    pub fn update_slot_cache_hash_get_previous(
        &mut self,
        slot_index: Cint64,
        hash_arena: &mut Arena<OccurrenceUnsatisfiableCacheEntriesHash>,
    ) -> EntriesHashId {
        let mut prev_hash = EntriesHashId::NONE;
        if self.cache_entries_hashes[slot_index as usize] != self.last_cache_entries_hash {
            prev_hash = self.cache_entries_hashes[slot_index as usize];
            self.cache_entries_hashes[slot_index as usize] = self.last_cache_entries_hash;
            if self.last_cache_entries_hash.is_some() {
                hash_arena
                    .get_mut(self.last_cache_entries_hash)
                    .inc_reference_count();
            }
        }
        prev_hash
    }

    /// Port of `void removeSlotCacheEntriesHash(qint64 slotIndex)`.
    pub fn remove_slot_cache_entries_hash(&mut self, slot_index: Cint64) {
        self.cache_entries_hashes[slot_index as usize] = EntriesHashId::NONE;
    }

    /// Port of `qint64 getMaxTag()`.
    pub fn get_max_tag(&self) -> Cint64 {
        self.max_item_entry
    }

    /// Port of `qint64 getMinTag()`.
    pub fn get_min_tag(&self) -> Cint64 {
        self.min_item_entry
    }

    /// Port of `COccurrenceUnsatisfiableCacheEntriesHash *getCacheEntriesHash()`.
    pub fn get_cache_entries_hash(&self) -> EntriesHashId {
        self.last_cache_entries_hash
    }

    /// Port of `COccurrenceUnsatisfiableCacheEntriesHash *getSlotCacheEntriesHash(qint64 slotIndex)`.
    pub fn get_slot_cache_entries_hash(&self, slot_index: Cint64) -> EntriesHashId {
        self.cache_entries_hashes[slot_index as usize]
    }

    /// Port of `CCacheValue getCacheValue()`.
    pub fn get_cache_value(&self) -> CCacheValue {
        self.cache_val
    }

    /// Port of `qint64 getTotalReadCount()`.
    pub fn get_total_read_count(&self) -> Cint64 {
        let mut read_count = 0;
        for i in 0..self.read_count_count as usize {
            read_count += self.read_count_vec[i];
        }
        read_count
    }

    /// Port of `void incReadCount(qint64 readCountIndex)`.
    pub fn inc_read_count(&mut self, read_count_index: Cint64) {
        if read_count_index >= 0 && read_count_index < self.read_count_count {
            self.read_count_vec[read_count_index as usize] += 1;
        }
    }

    /// Port of `COccurrenceUnsatisfiableCacheEntry *getPreviousUnsatisfiableCacheEntry()`.
    pub fn get_previous_unsatisfiable_cache_entry(&self) -> EntryId {
        self.prev_entry
    }

    /// Port of `bool isSerialized()`.
    pub fn is_serialized(&self) -> bool {
        self.serialized
    }

    /// Port of
    /// `COccurrenceUnsatisfiableCacheEntry *setCacheTerminationValuesList(QList<CCacheValue> *cacheTerminationValuesList)`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: the C++ takes ownership of the passed list
    /// pointer (deleting the previous one); the port moves the owned
    /// `Option<Vec<_>>` in. `unsatTerm` becomes `true` iff a list (non-null) is set.
    /// C++ returns `this`; the port returns `&mut Self` for the same chaining.
    pub fn set_cache_termination_values_list(
        &mut self,
        cache_termination_values_list: Option<Vec<CCacheValue>>,
    ) -> &mut Self {
        self.cache_term_values_list = cache_termination_values_list;
        self.unsat_term = self.cache_term_values_list.is_some();
        self
    }

    /// Port of
    /// `COccurrenceUnsatisfiableCacheEntry *copyCacheTerminationValuesList(QList<CCacheValue> *cacheTerminationValuesList)`.
    /// Deep-copies the passed list (or clears to `None`), then `unsatTerm` follows.
    pub fn copy_cache_termination_values_list(
        &mut self,
        cache_termination_values_list: Option<&[CCacheValue]>,
    ) -> &mut Self {
        self.cache_term_values_list = cache_termination_values_list.map(|l| l.to_vec());
        self.unsat_term = self.cache_term_values_list.is_some();
        self
    }

    /// Port of `QList<CCacheValue> *getCacheTerminationValuesList()`.
    pub fn get_cache_termination_values_list(&self) -> Option<&Vec<CCacheValue>> {
        self.cache_term_values_list.as_ref()
    }
}

// ===========================================================================
// COccurrenceUnsatisfiableCacheUpdateSlotItem
// ===========================================================================

/// Port of `COccurrenceUnsatisfiableCacheUpdateSlotItem`.
///
/// A versioned write-staging slot: a reader pins one slot (atomic share count)
/// while the writer accumulates `updatedEntrySet` / `updatedHashesList` into the
/// next slot, then activates it. This is the lock-free reader / serialised-writer
/// seam of the F3 cache.
#[derive(Debug, Default, Clone)]
pub struct OccurrenceUnsatisfiableCacheUpdateSlotItem {
    /// `QSet<COccurrenceUnsatisfiableCacheEntry*> updatedEntrySet`.
    pub updated_entry_set: HashSet<EntryId>,
    /// `QLinkedList<COccurrenceUnsatisfiableCacheEntriesHash*> updatedHashesList`
    /// (head-front; PORT.md §6).
    pub updated_hashes_list: Vec<EntriesHashId>,

    /// `QAtomicInt mReaderSharingCount`.
    /// KONCLUDE-PORT-NOTE[threading]: atomic → opaque `Cint64` (CAS share count).
    pub reader_sharing_count: Cint64,
    /// `bool mReaderUsing`.
    pub reader_using: bool,

    /// `qint64 readerCount`.
    pub reader_count: Cint64,
    /// `QMutex readerSyncMutex`.
    /// KONCLUDE-PORT-NOTE[threading]: lock → opaque `Cint64`.
    pub reader_sync_mutex: Cint64,

    /// `qint64 slotIndex`.
    pub slot_index: Cint64,
}

impl OccurrenceUnsatisfiableCacheUpdateSlotItem {
    /// Port of `COccurrenceUnsatisfiableCacheUpdateSlotItem::COccurrenceUnsatisfiableCacheUpdateSlotItem`
    /// `(qint64 updateSlotIndex)`.
    pub fn new(update_slot_index: Cint64) -> Self {
        // C++ ctor: slotIndex = updateSlotIndex; mReaderUsing = false; (the rest
        // default-constructed). Default::default() already gives mReaderUsing = false.
        OccurrenceUnsatisfiableCacheUpdateSlotItem {
            slot_index: update_slot_index,
            ..Default::default()
        }
    }

    /// Port of `bool incReader()`.
    ///
    /// KONCLUDE-PORT-NOTE[threading]: `QAtomicInt::ref()` increments and returns
    /// `newValue != 0`; modelled single-threaded inline on the plain `Cint64`
    /// share count.
    pub fn inc_reader(&mut self) -> bool {
        self.reader_sharing_count += 1;
        if self.reader_sharing_count != 0 {
            self.reader_using = true;
        }
        true
    }

    /// Port of `bool incReader(cint64 incCount)`.
    /// KONCLUDE-PORT-NOTE[overload]: C++ overload → distinct name `inc_reader_n`.
    pub fn inc_reader_n(&mut self, inc_count: Cint64) -> bool {
        let mut i = 0;
        while i < inc_count {
            self.inc_reader();
            i += 1;
        }
        self.reader_using
    }

    /// Port of `bool decReader()`.
    /// KONCLUDE-PORT-NOTE[threading]: `QAtomicInt::deref()` decrements and returns
    /// `newValue != 0`; `!deref()` ⇒ new value `== 0`.
    pub fn dec_reader(&mut self) -> bool {
        self.reader_sharing_count -= 1;
        if self.reader_sharing_count == 0 {
            self.reader_using = false;
        }
        self.reader_using
    }

    /// Port of `void addCacheEntry(COccurrenceUnsatisfiableCacheEntry *cacheEntry)`.
    pub fn add_cache_entry(&mut self, cache_entry: EntryId) {
        self.updated_entry_set.insert(cache_entry);
    }

    /// Port of `void addCacheEntriesHash(COccurrenceUnsatisfiableCacheEntriesHash *prevDelHash)`.
    pub fn add_cache_entries_hash(&mut self, cache_entries_hash: EntriesHashId) {
        // C++ `QLinkedList::append` (push-at-back); cleanup iterates the whole
        // list (order irrelevant), so plain `push` matches the append semantics.
        self.updated_hashes_list.push(cache_entries_hash);
    }

    /// Port of `void activateSlotUpdateItems()`.
    /// KONCLUDE-PORT-NOTE[ownership]: the `updatedEntrySet` holds entry ids; the
    /// owning `Arena<...Entry>` is threaded in to resolve the `setActiveSlot` call.
    pub fn activate_slot_update_items(
        &self,
        entry_arena: &mut Arena<OccurrenceUnsatisfiableCacheEntry>,
    ) {
        for &entry in &self.updated_entry_set {
            entry_arena.get_mut(entry).set_active_slot(self.slot_index);
        }
    }

    /// Port of `void cleanSlotUpdateItems()`.
    /// KONCLUDE-PORT-NOTE[memory-pool]: `delete hash` on the refcount reaching
    /// zero is the pool free; in the arena model the entry is left in place and
    /// dropped logically (arena reclaim happens on watermark reset). The refcount
    /// decrement is still applied faithfully.
    pub fn clean_slot_update_items(
        &mut self,
        hash_arena: &mut Arena<OccurrenceUnsatisfiableCacheEntriesHash>,
    ) {
        for &hash in &self.updated_hashes_list {
            if hash_arena
                .get_mut(hash)
                .dec_reference_count_return_has_to_be_deleted()
            {
                // delete hash; — [memory-pool] arena drop, no-op here.
            }
        }
        self.updated_hashes_list.clear();
        self.updated_entry_set.clear();
    }

    /// Port of `qint64 getSlotIndex()`.
    pub fn get_slot_index(&self) -> Cint64 {
        self.slot_index
    }

    /// Port of `bool hasCacheReaders()`.
    pub fn has_cache_readers(&self) -> bool {
        self.reader_using
    }
}

// ===========================================================================
// COccurrenceUnsatisfiableCacheReader
// ===========================================================================

/// Port of `COccurrenceUnsatisfiableCacheReader`
/// (`: public CIncrementalUnsatisfiableCacheReader`).
///
/// The per-thread read cursor over the F3 cache: it pins an update slot, walks the
/// incremental unsatisfiable test entry by entry, and reports the unsatisfiable
/// items it last matched.
#[derive(Debug, Clone)]
pub struct OccurrenceUnsatisfiableCacheReader {
    /// KONCLUDE-PORT-NOTE[ownership]: C++ base
    /// `CIncrementalUnsatisfiableCacheReader` → held by composition.
    pub base: IncrementalUnsatisfiableCacheReader,

    /// `COccurrenceUnsatisfiableCache* cache`.
    pub cache: CacheId,
    /// `COccurrenceUnsatisfiableCacheUpdateSlotItem* cacheSlotItem` — the pinned slot.
    pub cache_slot_item: UpdateSlotItemId,
    /// `QAtomicPointer<COccurrenceUnsatisfiableCacheUpdateSlotItem> mNextCacheSlotItemPointer`.
    /// KONCLUDE-PORT-NOTE[threading]: atomic pointer → opaque `Cint64` (an
    /// atomically-published `UpdateSlotItemId`).
    pub next_cache_slot_item_pointer: Cint64,

    /// `CDynamicExpandingMemoryManager<CDblLinker<...Entry*>> memManCacheEntryList`.
    /// KONCLUDE-PORT-NOTE[memory-pool]: per-reader linker pool → opaque `Cint64`.
    pub mem_man_cache_entry_list: Cint64,

    /// `CDblLinker<COccurrenceUnsatisfiableCacheEntry*>* incCacheEntriesLinker` —
    /// the incremental-test entry chain.
    /// KONCLUDE-PORT-NOTE[ownership]: doubly-linked `CDblLinker` chain → owned
    /// `Vec<EntryId>`, head-front (PORT.md §6).
    pub inc_cache_entries_linker: Vec<EntryId>,

    /// `QList<CCacheValue> lastUnsatItems`.
    pub last_unsat_items: Vec<CCacheValue>,
}

impl Default for OccurrenceUnsatisfiableCacheReader {
    fn default() -> Self {
        OccurrenceUnsatisfiableCacheReader {
            base: IncrementalUnsatisfiableCacheReader::new(),
            cache: CacheId::NONE,
            cache_slot_item: UpdateSlotItemId::NONE,
            next_cache_slot_item_pointer: Id::<()>::NONE.raw,
            mem_man_cache_entry_list: Id::<()>::NONE.raw,
            inc_cache_entries_linker: Vec::new(),
            last_unsat_items: Vec::new(),
        }
    }
}

impl OccurrenceUnsatisfiableCacheReader {
    /// Port of `COccurrenceUnsatisfiableCacheReader::COccurrenceUnsatisfiableCacheReader`
    /// `(COccurrenceUnsatisfiableCache *unsatisfiableCache)`.
    pub fn new(unsatisfiable_cache: CacheId) -> Self {
        // C++ ctor: cache = unsatisfiableCache; cacheSlotItem = 0;
        // incCacheEntriesLinker = 0; incrementUnsatisfiableTestReset();
        // Default already gives the empty linker / lastUnsatItems that the reset
        // produces, so this matches.
        OccurrenceUnsatisfiableCacheReader {
            cache: unsatisfiable_cache,
            ..Default::default()
        }
    }

    // KONCLUDE-PORT-NOTE[ownership][threading]: in C++ the reader holds a raw
    // back-pointer `cache` and dereferences it (`cache->getPrimarCacheEntry()`,
    // `cache->getCurrentCachingTag()`). There is no `Arena<...Cache>` (the facade
    // is a long-lived owner, not a per-test arena element), so the resolved facade
    // reference is threaded in as `cache: &OccurrenceUnsatisfiableCache`; the
    // `self.cache` id field mirrors the C++ member for identity. The entry / hash /
    // update-slot objects ARE family-internal arena elements, so their owning
    // arenas are threaded in to resolve the ids. `mNextCacheSlotItemPointer`
    // (`QAtomicPointer`) is the opaque `Cint64` slot-id (`< 0` == null); the atomic
    // fetch/store are single-threaded inline [threading].

    /// Port of
    /// `COccurrenceUnsatisfiableCacheUpdateSlotItem *changeUpdateSlot(COccurrenceUnsatisfiableCacheUpdateSlotItem *nextUpdateSlot)`.
    pub fn change_update_slot(
        &mut self,
        next_update_slot: UpdateSlotItemId,
        slot_arena: &mut Arena<OccurrenceUnsatisfiableCacheUpdateSlotItem>,
    ) -> UpdateSlotItemId {
        slot_arena.get_mut(next_update_slot).inc_reader();
        // tmpSlotItem = mNextCacheSlotItemPointer.fetchAndStoreOrdered(nextUpdateSlot);
        let tmp_raw = self.next_cache_slot_item_pointer;
        self.next_cache_slot_item_pointer = next_update_slot.raw;
        let tmp_slot_item = UpdateSlotItemId::new(tmp_raw);
        if tmp_slot_item.is_some() {
            slot_arena.get_mut(tmp_slot_item).dec_reader();
        }
        tmp_slot_item
    }

    /// Port of `bool moveToNextSlot()` (private).
    fn move_to_next_slot(
        &mut self,
        slot_arena: &mut Arena<OccurrenceUnsatisfiableCacheUpdateSlotItem>,
    ) -> bool {
        // mNextCacheSlotItemPointer.fetchAndAddRelaxed(0) != nullptr
        if self.next_cache_slot_item_pointer >= 0 {
            // nextSlotItem = mNextCacheSlotItemPointer.fetchAndStoreOrdered(nullptr);
            let next_slot_raw = self.next_cache_slot_item_pointer;
            self.next_cache_slot_item_pointer = Id::<()>::NONE.raw;
            if next_slot_raw >= 0 {
                if self.cache_slot_item.is_some() {
                    slot_arena.get_mut(self.cache_slot_item).dec_reader();
                }
                self.cache_slot_item = UpdateSlotItemId::new(next_slot_raw);
                return true;
            }
        }
        false
    }

    /// Port of `void incrementUnsatisfiableTestReset()`.
    /// KONCLUDE-PORT-NOTE[memory-pool]: releasing the `CDblLinker` chain back to
    /// `memManCacheEntryList` → clearing the owned `Vec` working chain.
    pub fn increment_unsatisfiable_test_reset(&mut self) {
        self.inc_cache_entries_linker.clear();
        self.last_unsat_items.clear();
    }

    /// Port of `bool incrementUnsatisfiableTest(CCacheValue *cacheValue, bool *continueTestingUseful)`.
    /// Returns `(unsatisfiable, continueTestingUseful)` (the C++ out-param).
    pub fn increment_unsatisfiable_test(
        &mut self,
        cache_value: &CCacheValue,
        cache: &OccurrenceUnsatisfiableCache,
        entry_arena: &Arena<OccurrenceUnsatisfiableCacheEntry>,
        hash_arena: &Arena<OccurrenceUnsatisfiableCacheEntriesHash>,
        slot_arena: &mut Arena<OccurrenceUnsatisfiableCacheUpdateSlotItem>,
    ) -> (bool, bool) {
        let linker = std::mem::take(&mut self.inc_cache_entries_linker);
        let (new_linker, unsat, continue_useful) = self.incremental_unsatisfiable_test(
            cache_value,
            linker,
            cache,
            entry_arena,
            hash_arena,
            slot_arena,
        );
        self.inc_cache_entries_linker = new_linker;
        (unsat, continue_useful)
    }

    /// Port of
    /// `CDblLinker<COccurrenceUnsatisfiableCacheEntry *> *incrementalUnsatisfiableTest(CCacheValue *cacheValue, CDblLinker<...> *cacheEntries, bool *unsatisfiable, bool *continueTesting)`.
    ///
    /// KONCLUDE-PORT-NOTE[memory-pool][ownership]: the `CDblLinker` working chain
    /// (allocated from `memManCacheEntryList`) → an owned `Vec<EntryId>`, head at
    /// FRONT (PORT.md §6). `init(d)` → `vec![d]`; an empty `Vec` is the null chain;
    /// `insertNext`/`allocate->init(d,next)` (prepend) → `insert(0, d)`;
    /// `release` → drop. Returns `(cacheEntries, unsatisfiable, continueTesting)`.
    pub fn incremental_unsatisfiable_test(
        &mut self,
        cache_value: &CCacheValue,
        cache_entries: Vec<EntryId>,
        cache: &OccurrenceUnsatisfiableCache,
        entry_arena: &Arena<OccurrenceUnsatisfiableCacheEntry>,
        hash_arena: &Arena<OccurrenceUnsatisfiableCacheEntriesHash>,
        slot_arena: &mut Arena<OccurrenceUnsatisfiableCacheUpdateSlotItem>,
    ) -> (Vec<EntryId>, bool, bool) {
        let mut cache_entries = cache_entries;
        if cache_entries.is_empty() {
            cache_entries = vec![cache.get_primar_cache_entry()];
        }
        let mut update_slot: Cint64 = 0;
        if self.next_cache_slot_item_pointer >= 0 {
            self.move_to_next_slot(slot_arena);
        }
        let mut unsatisfiable_found = false;
        let mut continue_testing_useful = false;
        if self.cache_slot_item.is_some() {
            update_slot = slot_arena.get(self.cache_slot_item).get_slot_index();

            let mut next_cache_entries: Vec<EntryId> = Vec::new();
            let item_tag = cache_value.first;

            let mut idx = 0;
            while idx < cache_entries.len() {
                if self.next_cache_slot_item_pointer >= 0 {
                    self.move_to_next_slot(slot_arena);
                    if self.cache_slot_item.is_some() {
                        update_slot = slot_arena.get(self.cache_slot_item).get_slot_index();
                    }
                }

                let cache_entry = cache_entries[idx];
                let e = entry_arena.get(cache_entry);
                let cache_max = e.get_max_tag();
                let serialized = e.is_serialized();
                let cache_hash_id = e.get_slot_cache_entries_hash(update_slot);

                // test min and max
                if cache_hash_id.is_none() || item_tag > cache_max {
                    // cache entry is no longer needed — release (drop).
                } else {
                    if !serialized {
                        // cache entry is needed, next round
                        next_cache_entries.insert(0, cache_entry);
                    }
                    // test to add additional cache entries
                    let cache_hash = hash_arena.get(cache_hash_id);
                    if let Some(&next_adding) = cache_hash.entries.get(cache_value) {
                        let na = entry_arena.get(next_adding);
                        if na.is_unsatisfiable_termination() {
                            unsatisfiable_found = true;
                            if let Some(list) = na.get_cache_termination_values_list() {
                                self.last_unsat_items = list.clone();
                            }
                            break;
                        }
                        next_cache_entries.insert(0, next_adding);
                    }
                }
                idx += 1;
            }
            // entries past the break point are released (drop).
            cache_entries = next_cache_entries;
        } else {
            cache_entries = Vec::new();
        }
        if unsatisfiable_found {
            cache_entries = Vec::new();
        }
        if !unsatisfiable_found && !cache_entries.is_empty() {
            continue_testing_useful = true;
        }
        (cache_entries, unsatisfiable_found, continue_testing_useful)
    }

    /// Port of `bool isUnsatisfiable(QVector<CCacheValue> &itemVec, qint64 count)`.
    pub fn is_unsatisfiable(
        &mut self,
        item_vec: &[CCacheValue],
        count: Cint64,
        cache: &OccurrenceUnsatisfiableCache,
        entry_arena: &Arena<OccurrenceUnsatisfiableCacheEntry>,
        hash_arena: &Arena<OccurrenceUnsatisfiableCacheEntriesHash>,
        slot_arena: &mut Arena<OccurrenceUnsatisfiableCacheUpdateSlotItem>,
    ) -> bool {
        self.is_unsatisfiable_with_list(
            item_vec,
            count,
            None,
            cache,
            entry_arena,
            hash_arena,
            slot_arena,
        )
    }

    /// Port of
    /// `bool isUnsatisfiable(QVector<CCacheValue> &itemVec, qint64 count, QList<CCacheValue> *unsatisfiableItemList)`.
    /// KONCLUDE-PORT-NOTE[overload]: the 3-arg overload → `is_unsatisfiable_with_list`.
    pub fn is_unsatisfiable_with_list(
        &mut self,
        item_vec: &[CCacheValue],
        count: Cint64,
        mut unsatisfiable_item_list: Option<&mut Vec<CCacheValue>>,
        cache: &OccurrenceUnsatisfiableCache,
        entry_arena: &Arena<OccurrenceUnsatisfiableCacheEntry>,
        hash_arena: &Arena<OccurrenceUnsatisfiableCacheEntriesHash>,
        slot_arena: &mut Arena<OccurrenceUnsatisfiableCacheUpdateSlotItem>,
    ) -> bool {
        let mut unsatisfiable = false;

        // list for cache entries (init with the primary entry).
        let mut cache_entries: Vec<EntryId> = vec![cache.get_primar_cache_entry()];

        let last_index = (count - 1) as usize;

        // make assumption that list is sorted
        let _min_item = item_vec[0].first;
        let max_item = item_vec[last_index].first;

        let mut update_slot: Cint64 = 0;
        if self.next_cache_slot_item_pointer >= 0 {
            self.move_to_next_slot(slot_arena);
        }
        if self.cache_slot_item.is_some() {
            update_slot = slot_arena.get(self.cache_slot_item).get_slot_index();

            let mut index: Cint64 = 0;
            while index < count && !unsatisfiable && !cache_entries.is_empty() {
                let item = item_vec[index as usize];
                index += 1;
                let item_tag = item.first;

                let mut next_cache_entries: Vec<EntryId> = Vec::new();

                let mut idx = 0;
                while idx < cache_entries.len() {
                    if self.next_cache_slot_item_pointer >= 0 {
                        self.move_to_next_slot(slot_arena);
                        if self.cache_slot_item.is_some() {
                            update_slot = slot_arena.get(self.cache_slot_item).get_slot_index();
                        }
                    }

                    let cache_entry = cache_entries[idx];
                    let e = entry_arena.get(cache_entry);
                    let cache_max = e.get_max_tag();
                    let cache_min = e.get_min_tag();
                    let cache_hash_id = e.get_slot_cache_entries_hash(update_slot);

                    // test min and max
                    if cache_hash_id.is_none() || cache_min > max_item || item_tag > cache_max {
                        // cache entry is no longer needed — release (drop).
                    } else {
                        // cache entry is needed, next round
                        next_cache_entries.insert(0, cache_entry);

                        // test to add additional cache entries
                        let cache_hash = hash_arena.get(cache_hash_id);
                        if let Some(&next_adding) = cache_hash.entries.get(&item) {
                            let na = entry_arena.get(next_adding);
                            if na.is_unsatisfiable_termination() {
                                unsatisfiable = true;
                                if let Some(list) = na.get_cache_termination_values_list() {
                                    self.last_unsat_items = list.clone();
                                    if let Some(out) = unsatisfiable_item_list.as_mut() {
                                        **out = list.clone();
                                    }
                                }
                                break;
                            }
                            next_cache_entries.insert(0, next_adding);
                        }
                    }
                    idx += 1;
                }

                // entries past the break point are released (drop).
                cache_entries = next_cache_entries;
            }
            // remaining cacheEntries released (drop).
        }

        if self.next_cache_slot_item_pointer >= 0 {
            self.move_to_next_slot(slot_arena);
            if self.cache_slot_item.is_some() {
                update_slot = slot_arena.get(self.cache_slot_item).get_slot_index();
            }
        }
        let _ = update_slot;
        unsatisfiable
    }

    /// Port of `QList<CCacheValue> getUnsatisfiableItems(QVector<CCacheValue> &itemVec, qint64 count)`.
    pub fn get_unsatisfiable_items(
        &mut self,
        item_vec: &[CCacheValue],
        count: Cint64,
        cache: &OccurrenceUnsatisfiableCache,
        entry_arena: &Arena<OccurrenceUnsatisfiableCacheEntry>,
        hash_arena: &Arena<OccurrenceUnsatisfiableCacheEntriesHash>,
        slot_arena: &mut Arena<OccurrenceUnsatisfiableCacheUpdateSlotItem>,
    ) -> Vec<CCacheValue> {
        let mut unsat_list: Vec<CCacheValue> = Vec::new();
        self.is_unsatisfiable_with_list(
            item_vec,
            count,
            Some(&mut unsat_list),
            cache,
            entry_arena,
            hash_arena,
            slot_arena,
        );
        unsat_list
    }

    /// Port of `QList<CCacheValue> getLastTestedUnsatisfiableItems()`.
    pub fn get_last_tested_unsatisfiable_items(&self) -> Vec<CCacheValue> {
        self.last_unsat_items.clone()
    }

    /// Port of
    /// `CXLinker<CCacheValue*>* getUnsatisfiableItems(CXLinker<CCacheValue*>* cacheValueTestLinker, CMemoryAllocationManager* memMan)`.
    ///
    /// KONCLUDE-PORT-NOTE[memory-pool][ownership]: both the input `CXLinker`
    /// (sorted item chain) and the result chain → owned `Vec<CCacheValue>`; the
    /// `memMan` object pool → arena/`Vec` allocation. Returns the matched-item
    /// sublist (in input order) on a termination with a termination-values list,
    /// the whole input on a termination without one, and `None` (the C++
    /// `nullptr`) when no termination is reached.
    pub fn get_unsatisfiable_items_linker(
        &mut self,
        cache_value_test_linker: &[CCacheValue],
        cache: &OccurrenceUnsatisfiableCache,
        entry_arena: &Arena<OccurrenceUnsatisfiableCacheEntry>,
        hash_arena: &Arena<OccurrenceUnsatisfiableCacheEntriesHash>,
        slot_arena: &mut Arena<OccurrenceUnsatisfiableCacheUpdateSlotItem>,
    ) -> Option<Vec<CCacheValue>> {
        let mut cache_entries: Vec<EntryId> = vec![cache.get_primar_cache_entry()];

        let first_item = cache_value_test_linker[0];
        let last_item = cache_value_test_linker[cache_value_test_linker.len() - 1];

        let _min_item = first_item.first;
        let max_item = last_item.first;

        let mut update_slot: Cint64 = 0;
        if self.next_cache_slot_item_pointer >= 0 {
            self.move_to_next_slot(slot_arena);
        }
        if self.cache_slot_item.is_some() {
            update_slot = slot_arena.get(self.cache_slot_item).get_slot_index();

            let mut test_idx = 0;
            while test_idx < cache_value_test_linker.len() && !cache_entries.is_empty() {
                let item = cache_value_test_linker[test_idx];
                let item_tag = item.first;

                let mut next_cache_entries: Vec<EntryId> = Vec::new();

                let mut idx = 0;
                while idx < cache_entries.len() {
                    let cache_entry = cache_entries[idx];
                    let e = entry_arena.get(cache_entry);
                    let cache_max = e.get_max_tag();
                    let cache_min = e.get_min_tag();
                    let cache_hash_id = e.get_slot_cache_entries_hash(update_slot);

                    // test min and max
                    if cache_hash_id.is_none() || cache_min > max_item || item_tag > cache_max {
                        // cache entry is no longer needed
                    } else {
                        // cache entry is needed, next round
                        next_cache_entries.insert(0, cache_entry);

                        let cache_hash = hash_arena.get(cache_hash_id);
                        if let Some(&next_adding) = cache_hash.entries.get(&item) {
                            let na = entry_arena.get(next_adding);
                            // test to add additional cache entries
                            if na.is_unsatisfiable_termination() {
                                match na.get_cache_termination_values_list() {
                                    Some(unsat_val_list) => {
                                        let mut result: Vec<CCacheValue> = Vec::new();
                                        let mut pos = 0;
                                        for &unsat_item in unsat_val_list {
                                            while cache_value_test_linker[pos] != unsat_item {
                                                pos += 1;
                                            }
                                            result.push(cache_value_test_linker[pos]);
                                        }
                                        return Some(result);
                                    }
                                    None => {
                                        return Some(cache_value_test_linker.to_vec());
                                    }
                                }
                            }
                            next_cache_entries.insert(0, next_adding);
                        }
                    }
                    idx += 1;
                }

                cache_entries = next_cache_entries;
                test_idx += 1;
            }
        }

        None
    }

    /// Port of `cint64 getCurrentCachingTag()`.
    pub fn get_current_caching_tag(&self, cache: &OccurrenceUnsatisfiableCache) -> Cint64 {
        cache.get_current_caching_tag()
    }
}

// ===========================================================================
// COccurrenceUnsatisfiableCacheWriter
// ===========================================================================

/// Port of `COccurrenceUnsatisfiableCacheWriter` (`: public CUnsatisfiableCacheWriter`).
///
/// The mutation facade: turns a proven-unsatisfiable item list into cache entries.
/// In the faithful single-threaded staging (manifest §Concurrency) the worker IS
/// the writer; later this drains the `CWriteUnsatisfiableCacheEntryEvent` queue.
#[derive(Debug, Clone)]
pub struct OccurrenceUnsatisfiableCacheWriter {
    /// KONCLUDE-PORT-NOTE[ownership]: C++ base `CUnsatisfiableCacheWriter` → composition.
    pub base: UnsatisfiableCacheWriter,
    /// `COccurrenceUnsatisfiableCache* cache`.
    pub cache: CacheId,
}

impl Default for OccurrenceUnsatisfiableCacheWriter {
    fn default() -> Self {
        OccurrenceUnsatisfiableCacheWriter {
            base: UnsatisfiableCacheWriter::new(),
            cache: CacheId::NONE,
        }
    }
}

impl OccurrenceUnsatisfiableCacheWriter {
    /// Port of `COccurrenceUnsatisfiableCacheWriter::COccurrenceUnsatisfiableCacheWriter`
    /// `(COccurrenceUnsatisfiableCache *unsatisfiableCache)`.
    pub fn new(unsatisfiable_cache: CacheId) -> Self {
        OccurrenceUnsatisfiableCacheWriter {
            cache: unsatisfiable_cache,
            ..Default::default()
        }
    }

    // KONCLUDE-PORT-NOTE[ownership]: like the reader, the writer holds a `cache`
    // id mirroring the C++ raw back-pointer, and the resolved facade reference is
    // threaded in so `cache->addUnsatisfiableCacheEntry(...)` resolves.

    /// Port of `void setUnsatisfiable(QList<CCacheValue> &itemList)`.
    /// KONCLUDE-PORT-NOTE[overload]: the `QList` overload → `set_unsatisfiable_list`.
    pub fn set_unsatisfiable_list(
        &self,
        item_list: &[CCacheValue],
        cache: &mut OccurrenceUnsatisfiableCache,
    ) {
        cache.add_unsatisfiable_cache_entry(item_list);
    }

    /// Port of
    /// `void setUnsatisfiable(QVector<CCacheValue> &itemVec, qint64 count, QVector<CCacheValue> &clashVec, qint64 clashCount)`.
    pub fn set_unsatisfiable(
        &self,
        _item_vec: &[CCacheValue],
        _count: Cint64,
        clash_vec: &[CCacheValue],
        clash_count: Cint64,
        cache: &mut OccurrenceUnsatisfiableCache,
    ) {
        if clash_count > 0 {
            let mut item_list: Vec<CCacheValue> = Vec::new();
            for i in 0..clash_count as usize {
                item_list.push(clash_vec[i]);
            }
            self.set_unsatisfiable_list(&item_list, cache);
        }
    }
}

// ===========================================================================
// COccurrenceUnsatisfiableCache (the facade)
// ===========================================================================

/// Port of `COccurrenceUnsatisfiableCache` (`: public CThread, public CUnsatisfiableCache`).
///
/// The F3 cache facade and its own writer thread. It owns the entry container, the
/// primary (root) entry, the update-slot ring (used / not-used / last), the lists
/// of attached readers and writers, the caching-tag generation counter, and the
/// lock-free-access bookkeeping that lets readers run without locking the writer.
///
/// KONCLUDE-PORT-NOTE[threading]: the `CThread` base (event loop + watchdog) is
/// infra; it is not modelled as a field here. The `QMutex` / `QSemaphore` members
/// become opaque `Cint64` `[threading]`. The faithful first port runs the cache
/// single-threaded (worker == writer), preserving this class boundary.
#[derive(Debug, Clone)]
pub struct OccurrenceUnsatisfiableCache {
    /// KONCLUDE-PORT-NOTE[ownership]: C++ base `CUnsatisfiableCache` → composition.
    pub base: UnsatisfiableCache,

    /// `QMutex cacheReaderSyncMutex`.  [threading] → opaque.
    pub cache_reader_sync_mutex: Cint64,
    /// `QMutex cacheWriterSyncMutex`.  [threading] → opaque.
    pub cache_writer_sync_mutex: Cint64,
    /// `QList<COccurrenceUnsatisfiableCacheReader*> cacheReaderList`.
    pub cache_reader_list: Vec<ReaderId>,
    /// `QList<COccurrenceUnsatisfiableCacheWriter*> cacheWriterList`.
    pub cache_writer_list: Vec<WriterId>,

    /// `COccurrenceUnsatisfiableCacheEntry* primarCacheEntry` — the root entry.
    pub primar_cache_entry: EntryId,
    /// `QList<COccurrenceUnsatisfiableCacheEntry*> container` — all entries.
    pub container: Vec<EntryId>,

    /// `qint64 updateSlotCount`.
    pub update_slot_count: Cint64,
    /// `QVector<COccurrenceUnsatisfiableCacheUpdateSlotItem*> updatesSlotItemVector`.
    pub updates_slot_item_vector: Vec<UpdateSlotItemId>,
    /// `QList<COccurrenceUnsatisfiableCacheUpdateSlotItem*> usedUpdatesSlotsList`.
    pub used_updates_slots_list: Vec<UpdateSlotItemId>,
    /// `QList<COccurrenceUnsatisfiableCacheUpdateSlotItem*> notusedUpdatesSlotsList`.
    pub notused_updates_slots_list: Vec<UpdateSlotItemId>,
    /// `COccurrenceUnsatisfiableCacheUpdateSlotItem* lastUpdateSlot`.
    pub last_update_slot: UpdateSlotItemId,

    /// `QMutex lockFreeMutexSync`.  [threading] → opaque.
    pub lock_free_mutex_sync: Cint64,
    /// `bool canGetLockFreeAccess`.
    pub can_get_lock_free_access: bool,
    /// `qint64 lockFreeAccessCount`.
    pub lock_free_access_count: Cint64,
    /// `QSemaphore lockFreeAccessLockSemaphore`.  [threading] → opaque.
    pub lock_free_access_lock_semaphore: Cint64,

    /// `bool cacheWritingRequested`.
    pub cache_writing_requested: bool,
    /// `qint64 writeOperationsCount`.
    pub write_operations_count: Cint64,

    /// `CCacheTaggingPool mCacheTaggingPool`.  [memory-pool] → opaque
    /// (cross-family F0, bulk-reset tagging generation pool).
    pub cache_tagging_pool: Cint64,
    /// `cint64 mCachingTag` — the current caching-generation tag.
    pub caching_tag: Cint64,

    /// `CCacheStatistics mCachStat`.  [api] → opaque (cross-family F0).
    pub cach_stat: Cint64,

    /// `QString mCachingString` (debug).
    pub caching_string: String,
    /// `QStringList mCachedStringList` (debug).
    pub cached_string_list: Vec<String>,
}

impl Default for OccurrenceUnsatisfiableCache {
    fn default() -> Self {
        OccurrenceUnsatisfiableCache {
            base: UnsatisfiableCache::new(),
            cache_reader_sync_mutex: Id::<()>::NONE.raw,
            cache_writer_sync_mutex: Id::<()>::NONE.raw,
            cache_reader_list: Vec::new(),
            cache_writer_list: Vec::new(),
            primar_cache_entry: EntryId::NONE,
            container: Vec::new(),
            update_slot_count: 0,
            updates_slot_item_vector: Vec::new(),
            used_updates_slots_list: Vec::new(),
            notused_updates_slots_list: Vec::new(),
            last_update_slot: UpdateSlotItemId::NONE,
            lock_free_mutex_sync: Id::<()>::NONE.raw,
            can_get_lock_free_access: false,
            lock_free_access_count: 0,
            lock_free_access_lock_semaphore: Id::<()>::NONE.raw,
            cache_writing_requested: false,
            write_operations_count: 0,
            cache_tagging_pool: Id::<()>::NONE.raw,
            caching_tag: 0,
            cach_stat: Id::<()>::NONE.raw,
            caching_string: String::new(),
            cached_string_list: Vec::new(),
        }
    }
}

impl OccurrenceUnsatisfiableCache {
    /// Port of `COccurrenceUnsatisfiableCache::COccurrenceUnsatisfiableCache`
    /// `(qint64 writeUpdateSlotCount, const QString &threadIdentifierName, CWatchDog *watchDogThread)`.
    ///
    /// KONCLUDE-PORT-NOTE[threading]: the `threadIdentifierName` / `CWatchDog*`
    /// args drive the `CThread` base (infra, not modelled); kept in the signature
    /// for fidelity. `_watch_dog_thread` is an opaque `Cint64` handle.
    pub fn new(
        write_update_slot_count: Cint64,
        _thread_identifier_name: &str,
        _watch_dog_thread: Cint64,
    ) -> Self {
        OccurrenceUnsatisfiableCache {
            update_slot_count: write_update_slot_count,
            ..Default::default()
        }
    }

    // KONCLUDE-PORT-NOTE[threading]: the C++ facade is a `CThread` whose own
    // worker thread builds the primary entry / slot ring (`threadStarted`) and
    // drains posted `CWriteUnsatisfiableCacheEntryEvent`s (`processCustomsEvents`).
    // The staged single-thread port (manifest §Concurrency) makes the worker the
    // writer: `thread_started` is called once at construction, and the event drain
    // is invoked inline as `process_customs_events(<decoded list>, ...)`. The
    // `QMutex`/`QSemaphore` syncs are inert no-ops. The per-test family arenas
    // (entries / hashes / slots / readers / writers) are threaded in because the
    // facade's `EntryId`/… members are arena ids, not owned heap pointers.

    /// Port of `COccurrenceUnsatisfiableCacheReader *getCacheReader()`.
    pub fn get_cache_reader(
        &mut self,
        self_id: CacheId,
        reader_arena: &mut Arena<OccurrenceUnsatisfiableCacheReader>,
    ) -> ReaderId {
        // [threading] cacheReaderSyncMutex.lock()/unlock() — inert single-threaded.
        let reader = reader_arena.push(OccurrenceUnsatisfiableCacheReader::new(self_id));
        self.cache_reader_list.push(reader);
        reader
    }

    /// Port of `COccurrenceUnsatisfiableCacheWriter *getCacheWriter()`.
    pub fn get_cache_writer(
        &mut self,
        self_id: CacheId,
        writer_arena: &mut Arena<OccurrenceUnsatisfiableCacheWriter>,
    ) -> WriterId {
        // [threading] cacheWriterSyncMutex.lock()/unlock() — inert single-threaded.
        let writer = writer_arena.push(OccurrenceUnsatisfiableCacheWriter::new(self_id));
        self.cache_writer_list.push(writer);
        writer
    }

    /// Port of `COccurrenceUnsatisfiableCacheEntry *getPrimarCacheEntry()`.
    pub fn get_primar_cache_entry(&self) -> EntryId {
        // [threading] C++ waits for the worker thread to finish initialising
        // (`CThread::waitSynchronization`); the staged port builds the primary
        // entry eagerly in `thread_started`, so it is already available.
        self.primar_cache_entry
    }

    /// Port of `void addUnsatisfiableCacheEntry(QList<CCacheValue> &itemList)`.
    ///
    /// KONCLUDE-PORT-NOTE[threading]: the C++ copies the item list into a
    /// `CWriteUnsatisfiableCacheEntryEvent` and posts it to the cache's own writer
    /// thread (`CThread::postEvent`), which later drains it via
    /// `processCustomsEvents`. The staged single-thread port has no event channel
    /// here; the caller drives the equivalent drain by calling
    /// `process_customs_events(item_list, ...)` directly with the family arenas
    /// (the worker IS the writer). This faithful post is therefore a documented
    /// [threading] hand-off point and carries no inline arena mutation.
    pub fn add_unsatisfiable_cache_entry(&mut self, _item_list: &[CCacheValue]) {
        // W6-DEFER[threading]: postEvent(new CWriteUnsatisfiableCacheEntryEvent(itemList));
        // see note above — the drain is process_customs_events.
    }

    /// Port of `bool isCacheWritePending()`.
    pub fn is_cache_write_pending(&self) -> bool {
        self.cache_writing_requested
    }

    /// Port of `cint64 getCurrentCachingTag()`.
    pub fn get_current_caching_tag(&self) -> Cint64 {
        self.caching_tag
    }

    /// Port of `CCacheStatistics* getCacheStatistics()`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: `CCacheStatistics` is cross-family F0
    /// (`cache/value.rs`); the `mCachStat` member is held opaque (`Cint64`) until
    /// the F0/F3 value-unification reconcile, so this returns the opaque handle.
    pub fn get_cache_statistics(&self) -> Cint64 {
        // W6-DEFER[api]: return &mCachStat (cross-family CacheStatistics).
        self.cach_stat
    }

    /// Port of `void threadStarted()`.
    ///
    /// KONCLUDE-PORT-NOTE[threading]: runs once on construction in the staged port.
    pub fn thread_started(
        &mut self,
        entry_arena: &mut Arena<OccurrenceUnsatisfiableCacheEntry>,
        slot_arena: &mut Arena<OccurrenceUnsatisfiableCacheUpdateSlotItem>,
    ) {
        // primarCacheEntry = new ...Entry(CCacheValue(0,0,CACHEVALCONCEPTONTOLOGYTAG),0,updateSlotCount,0);
        let primar_value = CacheValue {
            first: 0,
            second: 0,
            third: CacheValueIdentifier::CacheValConceptOntologyTag as i64,
        };
        let primar = entry_arena.push(OccurrenceUnsatisfiableCacheEntry::new(
            primar_value,
            EntryId::NONE,
            self.update_slot_count,
            0,
            1,
        ));
        self.primar_cache_entry = primar;
        self.container.push(primar);

        // updatesSlotItemVector(writeUpdateSlotCount, 0) → pre-sized, then filled.
        self.updates_slot_item_vector =
            vec![UpdateSlotItemId::NONE; self.update_slot_count as usize];
        let mut idx: Cint64 = 0;
        while idx < self.update_slot_count {
            let slot = slot_arena.push(OccurrenceUnsatisfiableCacheUpdateSlotItem::new(idx));
            self.updates_slot_item_vector[idx as usize] = slot;
            self.notused_updates_slots_list.push(slot);
            idx += 1;
        }
    }

    /// Port of `void threadStopped()`.
    pub fn thread_stopped(&mut self) {
        // delete updatesSlotItemVector[idx] / qDeleteAll(container) — [memory-pool]
        // arena drop (no-op here); only the bookkeeping is cleared.
        self.primar_cache_entry = EntryId::NONE;
        self.container.clear();
    }

    /// Port of `bool waitCacheWritePrepared()`.
    pub fn wait_cache_write_prepared(
        &mut self,
        slot_arena: &mut Arena<OccurrenceUnsatisfiableCacheUpdateSlotItem>,
        hash_arena: &mut Arena<OccurrenceUnsatisfiableCacheEntriesHash>,
    ) -> bool {
        let mut i = self.used_updates_slots_list.len() as i64;
        while i > 0 {
            let slot_item = self.used_updates_slots_list.remove(0); // takeFirst
            if !slot_arena.get(slot_item).has_cache_readers() {
                slot_arena
                    .get_mut(slot_item)
                    .clean_slot_update_items(hash_arena);
                self.notused_updates_slots_list.push(slot_item);
            } else {
                self.used_updates_slots_list.push(slot_item);
            }
            i -= 1;
        }
        while self.notused_updates_slots_list.is_empty() {
            // KONCLUDE-PORT-NOTE[threading]: C++ `QThread::msleep(10)` then re-scans
            // until a reader releases a slot. Single-threaded there is no concurrent
            // reader pinning a slot, so a re-scan with no movable slot would spin
            // forever; the `j == 0` break keeps the staged port progress-safe while
            // preserving the re-scan structure.
            let mut j = self.used_updates_slots_list.len() as i64;
            if j == 0 {
                break;
            }
            while j > 0 {
                let slot_item = self.used_updates_slots_list.remove(0);
                if !slot_arena.get(slot_item).has_cache_readers() {
                    slot_arena
                        .get_mut(slot_item)
                        .clean_slot_update_items(hash_arena);
                    self.notused_updates_slots_list.push(slot_item);
                } else {
                    self.used_updates_slots_list.push(slot_item);
                }
                j -= 1;
            }
        }
        true
    }

    /// Port of
    /// `bool activateCacheUpdate(COccurrenceUnsatisfiableCacheUpdateSlotItem *updateSlot)`.
    pub fn activate_cache_update(
        &mut self,
        update_slot: UpdateSlotItemId,
        entry_arena: &mut Arena<OccurrenceUnsatisfiableCacheEntry>,
        hash_arena: &mut Arena<OccurrenceUnsatisfiableCacheEntriesHash>,
        slot_arena: &mut Arena<OccurrenceUnsatisfiableCacheUpdateSlotItem>,
        reader_arena: &mut Arena<OccurrenceUnsatisfiableCacheReader>,
    ) -> bool {
        let slot_index = slot_arena.get(update_slot).get_slot_index();

        slot_arena
            .get(update_slot)
            .activate_slot_update_items(entry_arena);
        self.used_updates_slots_list.push(update_slot);

        // foreach entry in container
        // [ownership]: snapshot the container ids so the &mut arena loop does not
        // alias the facade's Vec.
        let container = self.container.clone();
        for entry in container {
            let prev_del_hash = entry_arena
                .get_mut(entry)
                .update_slot_cache_hash_get_previous(slot_index, hash_arena);
            if prev_del_hash.is_some() {
                slot_arena
                    .get_mut(update_slot)
                    .add_cache_entries_hash(prev_del_hash);
            }
        }

        self.last_update_slot = update_slot;

        // [threading] cacheReaderSyncMutex.lock()/unlock() — inert single-threaded.
        let readers = self.cache_reader_list.clone();
        for reader in readers {
            reader_arena
                .get_mut(reader)
                .change_update_slot(update_slot, slot_arena);
        }

        true
    }

    /// Port of
    /// `bool writeCacheTags(CCacheValue* cacheValue, cint64 cachingTag, cint64 cachedTag, cint64 cachingSize)`.
    pub fn write_cache_tags(
        &mut self,
        cache_value: &CCacheValue,
        caching_tag: Cint64,
        cached_tag: Cint64,
        caching_size: Cint64,
        ontology: &mut OntologyArenas,
    ) -> bool {
        let val_id = cache_value.get_cache_value_identifier();
        let mut has_concept = false;
        let mut concept_neg = false;
        if val_id == CacheValueIdentifier::CacheValTagAndConcept as Cint64 {
            has_concept = true;
            concept_neg = false;
        } else if val_id == CacheValueIdentifier::CacheValTagAndNegatedConcept as Cint64 {
            has_concept = true;
            concept_neg = true;
        }
        if has_concept {
            let identification = cache_value.get_identification();
            let concept = ConceptId::new(identification);
            if concept.is_some() && concept.raw < ontology.concept_count() {
                let concept_data = ontology.concept(concept).get_concept_data();
                if concept_data != INVALID {
                    let con_proc_data = ConceptProcessDataId::new(concept_data);
                    let mut unsat_caching_tags = ontology
                        .concept_process_data(con_proc_data)
                        .get_unsatisfiable_caching_tags(concept_neg);
                    if unsat_caching_tags.is_none() {
                        unsat_caching_tags = ontology
                            .alloc_unsatisfiable_caching_tags(UnsatisfiableCachingTags::new());
                        ontology
                            .concept_process_data_mut(con_proc_data)
                            .set_unsatisfiable_caching_tags(concept_neg, unsat_caching_tags);
                    }
                    ontology
                        .unsatisfiable_caching_tags_mut(unsat_caching_tags)
                        .update_caching_tags(cached_tag, caching_tag, caching_size);
                    return true;
                }
            }
        }
        false
    }

    /// Port of
    /// `bool writeCacheValues(COccurrenceUnsatisfiableCacheUpdateSlotItem *updateSlot, QList<CCacheValue> *cacheValueList)`.
    pub fn write_cache_values(
        &mut self,
        update_slot: UpdateSlotItemId,
        cache_value_list: &[CCacheValue],
        entry_arena: &mut Arena<OccurrenceUnsatisfiableCacheEntry>,
        hash_arena: &mut Arena<OccurrenceUnsatisfiableCacheEntriesHash>,
        slot_arena: &mut Arena<OccurrenceUnsatisfiableCacheUpdateSlotItem>,
        ontology: &mut OntologyArenas,
    ) -> bool {
        let slot_index = slot_arena.get(update_slot).get_slot_index();
        let mut cache = self.primar_cache_entry;

        let caching_tag = self.caching_tag + 1;
        // KONCLUDE-PORT-NOTE[memory-pool]: `mCacheTaggingPool.takeNextTag()` is the
        // monotone bulk-reset generation source (opaque `Cint64` pool here); the
        // resulting `cachedTag` feeds only the [api]-deferred `write_cache_tags`,
        // so a placeholder 0 is used until the tagging pool lands.
        let cached_tag: Cint64 = 0;

        let caching_size = cache_value_list.len() as Cint64;

        for &cache_value in cache_value_list {
            let cache_hash_id = entry_arena.get(cache).get_cache_entries_hash();
            let contains = cache_hash_id.is_some()
                && hash_arena
                    .get(cache_hash_id)
                    .entries
                    .contains_key(&cache_value);

            if cache_hash_id.is_none() || !contains {
                // build updatedCacheHash (copy of the existing hash, or a fresh one)
                let updated_cache_hash = if cache_hash_id.is_some() {
                    let copy = OccurrenceUnsatisfiableCacheEntriesHash::new_copy(
                        hash_arena.get(cache_hash_id),
                    );
                    hash_arena.push(copy)
                } else {
                    hash_arena.push(OccurrenceUnsatisfiableCacheEntriesHash::new())
                };
                slot_arena.get_mut(update_slot).add_cache_entry(cache);

                let next_cache = entry_arena.push(OccurrenceUnsatisfiableCacheEntry::new(
                    cache_value,
                    EntryId::NONE,
                    self.update_slot_count,
                    slot_index,
                    1,
                ));
                self.container.push(next_cache);

                let tag = cache_value.first;
                hash_arena
                    .get_mut(updated_cache_hash)
                    .entries
                    .insert(cache_value, next_cache);
                entry_arena.get_mut(cache).set_minimum_candidate(tag);
                entry_arena.get_mut(cache).set_maximum_candidate(tag);

                let prev_del_hash = entry_arena
                    .get_mut(cache)
                    .set_cache_entries_hash_slot_get_previous(slot_index, updated_cache_hash);
                if prev_del_hash.is_some() {
                    slot_arena
                        .get_mut(update_slot)
                        .add_cache_entries_hash(prev_del_hash);
                }

                cache = next_cache;
            } else {
                cache = hash_arena.get(cache_hash_id).entries[&cache_value];
            }

            self.write_cache_tags(
                &cache_value,
                caching_tag,
                cached_tag,
                caching_size,
                ontology,
            );
        }
        if cache.is_some() {
            entry_arena
                .get_mut(cache)
                .copy_cache_termination_values_list(Some(cache_value_list));
        }
        self.caching_tag += 1;

        true
    }

    /// Port of
    /// `bool testAlreadyCached(COccurrenceUnsatisfiableCacheUpdateSlotItem *updateSlot, QList<CCacheValue> *cacheValueList)`.
    ///
    /// KONCLUDE-PORT-NOTE: the C++ computes `slotIndex = updateSlot->getSlotIndex()`
    /// but never uses it (the lookup walks `getCacheEntriesHash()`, the last hash,
    /// not a per-slot one), so the `_update_slot` arg is unused here.
    pub fn test_already_cached(
        &self,
        _update_slot: UpdateSlotItemId,
        cache_value_list: &[CCacheValue],
        entry_arena: &Arena<OccurrenceUnsatisfiableCacheEntry>,
        hash_arena: &Arena<OccurrenceUnsatisfiableCacheEntriesHash>,
    ) -> bool {
        let mut cache = self.primar_cache_entry;
        for &cache_value in cache_value_list {
            if entry_arena.get(cache).is_unsatisfiable_termination() {
                return true;
            }
            let cache_hash_id = entry_arena.get(cache).get_cache_entries_hash();
            if cache_hash_id.is_none() {
                return false;
            }
            match hash_arena.get(cache_hash_id).entries.get(&cache_value) {
                Some(&next) => cache = next,
                None => return false,
            }
        }
        if entry_arena.get(cache).is_unsatisfiable_termination() {
            return true;
        }
        false
    }

    /// Port of `QString getCachingConceptsDebugString(QList<CCacheValue> &itemList)`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: debug-only; formats each concept cache value via
    /// `CConceptTextFormater::getConceptString((CConcept*)identification, neg)`
    /// (cross-subtree). The concept resolution is deferred; returns an empty
    /// string until the ontology arena is reachable here.
    pub fn get_caching_concepts_debug_string(&self, _item_list: &[CCacheValue]) -> String {
        // W6-DEFER[api]: CConceptTextFormater over CConcept* identifications.
        String::new()
    }

    /// Port of the `EVENTWRITEUNSATISFIABLECACHEENTRY` branch of
    /// `bool processCustomsEvents(QEvent::Type type, CCustomEvent *event)`.
    ///
    /// KONCLUDE-PORT-NOTE[threading]: the C++ first delegates to
    /// `CThread::processCustomsEvents` and dispatches on the `QEvent::Type`; the
    /// staged single-thread port receives the already-decoded
    /// `CWriteUnsatisfiableCacheEntryEvent` cache-value list (`cEL`) directly. The
    /// commented-out debug-string instrumentation is omitted (it is `#define`-gated
    /// off in the C++).
    pub fn process_customs_events(
        &mut self,
        cel: &[CCacheValue],
        entry_arena: &mut Arena<OccurrenceUnsatisfiableCacheEntry>,
        hash_arena: &mut Arena<OccurrenceUnsatisfiableCacheEntriesHash>,
        slot_arena: &mut Arena<OccurrenceUnsatisfiableCacheUpdateSlotItem>,
        reader_arena: &mut Arena<OccurrenceUnsatisfiableCacheReader>,
        ontology: &mut OntologyArenas,
    ) -> bool {
        if self.last_update_slot.is_none()
            || !self.test_already_cached(self.last_update_slot, cel, entry_arena, hash_arena)
        {
            self.cache_writing_requested = true;

            if self.wait_cache_write_prepared(slot_arena, hash_arena) {
                let update_slot = self.notused_updates_slots_list.remove(0); // takeFirst

                self.write_operations_count += 1;

                self.write_cache_values(
                    update_slot,
                    cel,
                    entry_arena,
                    hash_arena,
                    slot_arena,
                    ontology,
                );
                // mCachStat.incCacheEntriesCount(); — [api] cross-family CacheStatistics, deferred.

                self.activate_cache_update(
                    update_slot,
                    entry_arena,
                    hash_arena,
                    slot_arena,
                    reader_arena,
                );

                let mut i = self.used_updates_slots_list.len() as i64;
                while i > 0 {
                    let slot_item = self.used_updates_slots_list.remove(0);
                    if !slot_arena.get(slot_item).has_cache_readers() {
                        slot_arena
                            .get_mut(slot_item)
                            .clean_slot_update_items(hash_arena);
                        self.notused_updates_slots_list.push(slot_item);
                    } else {
                        self.used_updates_slots_list.push(slot_item);
                    }
                    i -= 1;
                }
            }

            self.cache_writing_requested = false;
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use super::super::super::model::concept::Concept;
    use super::super::super::model::concept_process::ConceptProcessData;
    use super::*;

    #[test]
    fn occurrence_unsat_write_cache_tags_allocates_and_updates_concept_process_tags() {
        let mut ontology = OntologyArenas::new();
        let con_proc = ontology.alloc_concept_process_data(ConceptProcessData::new());

        let mut concept = Concept::new();
        concept.set_concept_data(con_proc.raw);
        let concept_id = ontology.alloc_concept(concept);

        let mut cache = OccurrenceUnsatisfiableCache::new(1, "", INVALID);
        let pos_cache_value = CacheValue::new_value(
            11,
            concept_id.raw,
            CacheValueIdentifier::CacheValTagAndConcept,
        );
        assert!(cache.write_cache_tags(&pos_cache_value, 3, 7, 2, &mut ontology));

        let pos_tags = ontology
            .concept_process_data(con_proc)
            .get_unsatisfiable_caching_tags(false);
        assert!(pos_tags.is_some());
        assert_eq!(
            ontology
                .unsatisfiable_caching_tags(pos_tags)
                .get_last_caching_tag(),
            3
        );
        assert_eq!(
            ontology
                .unsatisfiable_caching_tags(pos_tags)
                .get_min_cached_tag(),
            7
        );
        assert_eq!(
            ontology
                .unsatisfiable_caching_tags(pos_tags)
                .get_max_cached_tag(),
            7
        );
        assert_eq!(
            ontology
                .unsatisfiable_caching_tags(pos_tags)
                .get_min_unsatisfiable_cached_size(),
            2
        );
        assert!(ontology
            .concept_process_data(con_proc)
            .get_unsatisfiable_caching_tags(true)
            .is_none());

        let neg_cache_value = CacheValue::new_value(
            13,
            concept_id.raw,
            CacheValueIdentifier::CacheValTagAndNegatedConcept,
        );
        assert!(cache.write_cache_tags(&neg_cache_value, 4, 9, 5, &mut ontology));
        let neg_tags = ontology
            .concept_process_data(con_proc)
            .get_unsatisfiable_caching_tags(true);
        assert!(neg_tags.is_some());
        assert_ne!(pos_tags, neg_tags);
        assert_eq!(
            ontology
                .unsatisfiable_caching_tags(neg_tags)
                .get_last_caching_tag(),
            4
        );
        assert_eq!(
            ontology
                .unsatisfiable_caching_tags(neg_tags)
                .get_min_cached_tag(),
            9
        );
        assert_eq!(
            ontology
                .unsatisfiable_caching_tags(neg_tags)
                .get_min_unsatisfiable_cached_size(),
            5
        );
    }

    #[test]
    fn occurrence_unsat_write_cache_tags_returns_false_without_concept_process_data() {
        let mut ontology = OntologyArenas::new();
        let concept_id = ontology.alloc_concept(Concept::new());
        let mut cache = OccurrenceUnsatisfiableCache::new(1, "", INVALID);
        let cache_value = CacheValue::new_value(
            11,
            concept_id.raw,
            CacheValueIdentifier::CacheValTagAndConcept,
        );

        assert!(!cache.write_cache_tags(&cache_value, 3, 7, 2, &mut ontology));
    }
}
