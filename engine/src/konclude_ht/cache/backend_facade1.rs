//! `cache::backend_facade1` — F1 facade method bodies, **FIRST THIRD** (Konclude
//! `Source/Reasoner/Kernel/Cache/CBackendRepresentativeMemoryCache.cpp`).
//!
//! ## Scope (the `CBackendRepresentativeMemoryCache::` facade method definitions)
//!
//! The facade's `CBackendRepresentativeMemoryCache::` method definitions span C++
//! **lines 34–5322**. Divided into THIRDS by source line (≈1763 lines each), the
//! FIRST third is **lines 34–1797**; respecting method boundaries it ends at the
//! last method that lies wholly within it, i.e. C++ **lines 34–1619**:
//!
//! * ctor (34) / dtor (143) / `getCacheStatistics` (148)
//! * memory-context lifecycle: `deleteExpiredIndividualAssociationMemoryContexts`
//!   (154) / `queueIndividualAssociationMemoryContextDeletion` (309) /
//!   `createReaderSlotUpdate` (317) / `prepareOntologyDataUpdate` (360) /
//!   `cleanUnusedSlots` (465)
//! * reader/writer factories: `createCacheReader` (511) /
//!   `createOntologyFixedCacheReader` (520) / `createCacheWriter` (534) /
//!   `writeCachedData` (541)
//! * the association/label writing+building core:
//!   `installTemporaryCardinalities` (562) / `installTemporaryLabels` (614) /
//!   `addCreatedLabelStatistics` (699) / `getExtendedLabel` (710) /
//!   `getReducedLabel` (811) / `getAdditionMergedLabel` (883) /
//!   `checkAssociationUsage` (1030) /
//!   `markRepresentativeReferencedIndividualAssociationIncompletelyHandled` (1061) /
//!   `markIndividualAssociationIncompletelyHandled` (1076) /
//!   `markIndividualAssociationCompletelyHandled` (1110) /
//!   `checkUpdateRejection` (1144) / `handleUpdateRejection` (1192) /
//!   `analyseDeterministicSameAsAssociationInstallation` (1213) /
//!   `installDeterministicSameAsAssociationUpdates` (1257) /
//!   `checkRequiresDeterministicSameAsAssociationUpdateInstallation` (1343) /
//!   `installDeterministicSameAsAssociationUpdate` (1366) /
//!   `installAssociationUpdates` (1416) /
//!   `createLocalizedIndividualAssociationData` (1450) /
//!   `getIndividualAssociationDataMemoryContext` (1533) /
//!   `isCacheValueRoleInverse` (1573) / `isCacheValueRoleNondeterministic` (1580) /
//!   `isRoleNeighbourLinkLabelItemCompatibility` (1588)
//!
//! **facade2 begins at `installAssociationUpdate` (C++ line 1620).** facade3 picks
//! up the remaining third. No overlap.
//!
//! ## License (per `PORT.md` §License note)
//! Function-by-function translation of LGPLv3 Konclude source; LGPL terms attach.
//!
//! ## Port conventions applied (PORT.md §44; manifest §Concurrency)
//!
//! * `CXxx*` pointer → typed arena `Id<T>` (`Id::NONE` == `nullptr`); intrusive
//!   `CLinkerBase` chains → owned `Vec<Id>` head-front (the facade's `slot_linker`
//!   / `reader_linker`).
//! * `QMutex` / `QSemaphore` / `QAtomicInt` → single-threaded inline `[threading]`.
//! * pool / context allocators (`CObjectAllocator` / `CObjectParameterizingAllocator`
//!   / `CMemoryPoolAllocationManager` / `CMemoryPoolContainer`) → `[memory-pool]`.
//! * **arena-resolution deferral (the W3.5 keystone, applied to F1).** The cache
//!   has no concrete per-cache arena yet (the W6 cache wave is struct-defs only;
//!   there is no `CProcessContext`-style container owning `Arena<OntologyData>` /
//!   `Arena<IndividualAssociationData>` / `Arena<LabelCacheItem>` / `Arena<SlotItem>`
//!   / `Arena<Reader>`). So every `ontologyData->…` / `associationData->…` /
//!   `labelItem->…` / `slot->…` / `reader->…` dereference is a faithful
//!   `// W6-DEFER[api]` stub: the control flow is preserved (loops, branches,
//!   self-field mutations execute), the object-graph derefs are deferred to the
//!   reconcile that lands the cache arena (then `ctx.ontology_data(id).get_x()`).
//! * Sibling facade methods (in this third or facade2/3) are called `self.x(…)`
//!   and resolve at the cache-family reconcile.
//! * `CCacheValue` unifies on `value::CacheValue` (F0 precedent).
//! * `CConfigDataReader` (the ctor's config reads) is cross-infra → the ctor is
//!   already represented by `BackendRepresentativeMemoryCache::new` + `Default`
//!   in `backend.rs` (the config defaults are baked into `Default`); it is NOT
//!   re-defined here (would duplicate `new`). See the ctor note below.

#![allow(dead_code)]
#![allow(unused_variables)]

use super::super::model::substrate::{Cint64, INVALID};
use super::backend::{
    BackendRepresentativeMemoryCache, BackendRepresentativeMemoryCacheReader,
    BackendRepresentativeMemoryCacheSlotItem, BaseContextId, CacheWriteDataId, ReaderId,
    SlotItemId, WriterId,
};
use super::backend_data::{
    BackendTempWriteRecordId, IndividualAssociationContextId, IndividualAssociationDataId,
    LabelCacheItemId, OntologyDataId, LABEL_CACHE_ITEM_ASSOCIATABLE_TYPE_COUNT,
};
use super::context::CacheContext;
use super::value::{CacheStatistics, CacheValue, CacheValueIdentifier};

impl BackendRepresentativeMemoryCache {
    // =======================================================================
    // ctor / dtor — C++ lines 34 / 143.
    //
    // KONCLUDE-PORT-NOTE[api]: `CBackendRepresentativeMemoryCache::CBackendReprese
    // ntativeMemoryCache(config, threadIdentifierName, watchDogThread)` (line 34)
    // is the config-reading constructor. It is ALREADY ported as
    // `BackendRepresentativeMemoryCache::new` + the `Default` impl in `backend.rs`:
    // the ~80 `CConfigDataReader::readConfig{Boolean,Integer,Double}` reads only
    // set the `conf_*` defaults, which `Default` bakes in verbatim (e.g.
    // `mConfWaitIndividualLabelAssociationIndexed = …, true` ⇒ `conf_wait_…: true`;
    // `mNextIndiUpdateId = 1`, `mNextNomConnUpdateId = 1`, etc.). The
    // `CConfigDataReader` calls are cross-infra (W6-DEFER[api]); `startThread(High
    // estPriority)` is `[threading]` (the single-threaded staging never spawns the
    // writer thread). It is NOT re-defined here to avoid a duplicate `new`.
    //
    // KONCLUDE-PORT-NOTE[api]: `~CBackendRepresentativeMemoryCache` (line 143) is
    // an empty destructor — no `Drop` impl is needed (the owned `Vec`s / `HashMap`s
    // drop automatically).
    // =======================================================================

    /// Port of `CBackendRepresentativeMemoryCache::getCacheStatistics`
    /// (`return &mCacheStat;`).
    pub fn get_cache_statistics(&self) -> &CacheStatistics {
        &self.cache_stat
    }

    /// Port of `CBackendRepresentativeMemoryCache::deleteExpiredIndividualAssociationMemoryContexts`.
    ///
    /// Walks the ontology's release-queued individual-association memory contexts,
    /// moving the ones whose ontology-data-update ids are no longer slot-referred
    /// into the recomputation-id releasing map keyed by their max referred
    /// recomputation id, then deletes (releases the pooled memory of) the contexts
    /// whose key is below the minimum slot-referring valid recomputation id.
    ///
    /// KONCLUDE-PORT-NOTE[api]: the body is one large `OntologyData` /
    /// `IndividualAssociationContext` / `OntologyDataRecomputationReferenceLinker` /
    /// `SlotItem` object-graph traversal; with no cache arena yet, the whole
    /// traversal is a faithful `W6-DEFER[api]` stub (the `[memory-pool]`
    /// `releaseTemporaryMemoryPools` calls and the `[threading]` slot scan are
    /// likewise deferred). The two `if`-guards on `self.stat_collect_statistics`
    /// drive only `LOG`/`mIndiContextCountHash` diagnostics (omitted). Control flow
    /// preserved in this doc; reconciles to walk the landed
    /// `OntologyData::release_queued_individual_association_context_linker` chain.
    pub fn delete_expired_individual_association_memory_contexts(
        &mut self,
        ontology_data: OntologyDataId,
        context: BaseContextId,
    ) {
        // W6-DEFER[api]: needs the cache arena to resolve `ontology_data` /
        // contexts. Faithful control flow (C++ 154–305):
        //   ontologyContext = ontologyData->getOntologyContext();
        //   if (ontologyData->isBasicPrecomputationMode()) return;
        //   for each releaseQueuedIndividualAssociationContextLinker:
        //     for each recomputationReferenceLinker in [last..firstNext):
        //       if (!active) { ++mStatIndividualAssociationSeparateMemoryManagment
        //         SlotReferredCheckingCount; scan mSlotLinker for a slot whose
        //         referredOntologyData update-id == ontologyDataUpdateId; … }
        //       else noneOntologyDataUpdateIdSlotReferred = false;
        //     if (noneOntologyDataUpdateIdSlotReferred):
        //       --mStatMemoryManagmentQueuedCheckingCount;
        //       ++mStatMemoryManagmentScheduledReleasingCount;
        //       ++mStatIndividualAssociationSeparateMemoryManagmentUnreferredSlotCount;
        //       move ctx into recomputationIdReleasingIndividualAssociationContextMap
        //         (keyed by maxReferedRecomputationId);
        //   if (map && !map->isEmpty()):
        //     minValidRecompId = getMinimumSlotReferreringInstalledValidRecomputationId(ontologyData);
        //     mLastMemoryContextDeletionMinValidRecompId = minValidRecompId;
        //     while (!map->isEmpty() && map.firstKey() < minValidRecompId):
        //       for each unusedIndiAssContext: releaseTemporaryMemoryPools(...);
        //         --mStatMemoryManagmentScheduledReleasingCount;
        //         ++mStatIndividualAssociationSeparateMemoryManagmentDeletionCount;
        //       map->erase(begin);
        let _ = (ontology_data, context);
    }

    /// Port of `CBackendRepresentativeMemoryCache::queueIndividualAssociationMemoryContextDeletion`.
    ///
    /// Appends the memory context to the ontology-data release queue and bumps the
    /// two queued-checking statistics.
    pub fn queue_individual_association_memory_context_deletion(
        &mut self,
        indi_ass_mem_context: IndividualAssociationContextId,
        ontology_data: OntologyDataId,
        cache_context: &mut CacheContext,
    ) {
        cache_context
            .ontology_data_mut(ontology_data)
            .add_release_queued_individual_association_context_linker(indi_ass_mem_context);
        self.stat_individual_association_separate_memory_managment_slot_referred_checking_queuing_count += 1;
        self.stat_memory_managment_queued_checking_count += 1;
    }

    /// Port of `CBackendRepresentativeMemoryCache::createReaderSlotUpdate`.
    ///
    /// Publishes a fresh reader slot: snapshots the ontology-identifier→data hash
    /// into a new pooled `SlotItem`, splices it onto the slot chain, bumps every
    /// referenced ontology-data's usage count, and re-points every reader at the
    /// new slot (incrementing the slot's reader count per reader).
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: `mSlotLinker->append(slot)` makes `slot` the
    /// new head (CLinker head-front) → `self.slot_linker.insert(0, slot)`.
    pub fn create_reader_slot_update(
        &mut self,
        ontology_data: OntologyDataId,
        cache_context: &mut CacheContext,
    ) {
        let next_update_minimum = cache_context
            .ontology_data(ontology_data)
            .get_next_update_minimum_valid_recomputation_id();
        cache_context
            .ontology_data_mut(ontology_data)
            .set_minimum_valid_recomputation_id(next_update_minimum)
            .set_slot_update_integrated(true);

        let ontology_identifier_data_hash = self.ontology_identifier_data_hash.clone();
        let mut slot = BackendRepresentativeMemoryCacheSlotItem::new();
        slot.set_ontology_identifier_data_hash(ontology_identifier_data_hash.clone());
        let new_slot = cache_context.alloc_backend_slot_item(slot);

        self.reader_slot_update_count += 1;

        self.last_updated_slot_linker = new_slot;
        // mLastUpdatedSlotLinker = slot; if (mSlotLinker) mSlotLinker->append(slot); else mSlotLinker = slot;
        // CLinker head-front splice (new slot becomes head):
        self.slot_linker.insert(0, new_slot);

        // for each (id,data) in ontologyIdentifierDataHash: data->incUsageCount();
        for &ontology_data in ontology_identifier_data_hash.values() {
            cache_context
                .ontology_data_mut(ontology_data)
                .inc_usage_count(1);
        }

        // for each reader in mReaderLinker: slot->incReader(); reader->updateSlot(slot);
        for &reader in &self.reader_linker {
            cache_context.backend_slot_item_mut(new_slot).inc_reader();
            let prev_slot = {
                let reader = cache_context.backend_cache_reader_mut(reader);
                let prev_slot = reader.updated_slot;
                reader.updated_slot = new_slot;
                prev_slot
            };
            if prev_slot.is_some() {
                cache_context.backend_slot_item_mut(prev_slot).dec_reader();
            }
        }
    }

    /// Port of `CBackendRepresentativeMemoryCache::prepareOntologyDataUpdate`.
    ///
    /// Returns the writable `OntologyData` for `ontology_identifier`: if absent or
    /// already slot-integrated it clones a fresh one (copying the 16 signature→label
    /// hashes, the nominal indirect-connection hash, the ontology context, and the
    /// individual-id→association-data vector, growing it to `min_indi_count+1`),
    /// installs a recomputation-reference linker, and releases the previous data if
    /// its usage count drops to zero.
    ///
    /// KONCLUDE-PORT-NOTE[api]: pure `OntologyData` construction + arena copying;
    /// faithful `W6-DEFER[api]` (the `self.ontology_data_update_count` bump is the
    /// only self-scalar effect and IS executed when the clone branch is taken).
    pub fn prepare_ontology_data_update(
        &mut self,
        ontology_identifier: Cint64,
        min_indi_count: Cint64,
    ) -> OntologyDataId {
        // CBackendRepresentativeMemoryCacheOntologyData*& ontologyData =
        //     (*mOntologyIdentifierDataHash)[ontologyIdentifier];
        let ontology_data: OntologyDataId = self
            .ontology_identifier_data_hash
            .get(&ontology_identifier)
            .copied()
            .unwrap_or(OntologyDataId::NONE);

        // if (!ontologyData || ontologyData->isSlotUpdateIntegrated()) { … }
        // W6-DEFER[api]: isSlotUpdateIntegrated() needs the OntologyData arena.
        let slot_update_integrated = false; // W6-DEFER[api]: ontologyData->isSlotUpdateIntegrated()
        if ontology_data == OntologyDataId::NONE || slot_update_integrated {
            // prevOntologyData = ontologyData;
            // ontologyData = new OntologyData(&mContext); ontologyData->initOntologyData(...);
            self.ontology_data_update_count += 1;
            // W6-DEFER[api]: clone the 16 signature-label hashes + nominal-indirect
            //   hash + ontology context + indi-id→assoc-data vector (grow to
            //   min_indi_count+1), copyOntologyData(prev), install recomputation
            //   reference linker, incUsageCount, and release prev when usage <= 0
            //   (++mOntologyDataReleasedCount; ++mOntologyDataReleasedWhileNewCreationCount).
            // self.ontology_identifier_data_hash.insert(ontology_identifier, newData);
        }
        let _ = min_indi_count;
        ontology_data
    }

    /// Port of `CBackendRepresentativeMemoryCache::cleanUnusedSlots`.
    ///
    /// Walks the slot chain dropping every slot with no cache readers: it
    /// decrements each referenced ontology-data's usage count (releasing the
    /// ontology data + its pooled memory when it reaches zero), then releases the
    /// slot's own pooled memory.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: the C++ in-place singly-linked unlink becomes
    /// a `retain`-style filter over `self.slot_linker` (head-front); the
    /// `hasCacheReaders` test + the pooled releases are `W6-DEFER[api]`.
    pub fn clean_unused_slots(&mut self, cache_context: &mut CacheContext) {
        // CMemoryPoolAllocationManager* memMan = context->getMemoryPoolAllocationManager();
        // KONCLUDE-PORT-NOTE[ownership]: take the chain out so the per-slot release
        // counters can mutate `self` while we re-filter (no aliasing borrow).
        let slots = std::mem::take(&mut self.slot_linker);
        let mut kept: Vec<SlotItemId> = Vec::with_capacity(slots.len());
        for slot in slots {
            // if (!slotLinkerIt->hasCacheReaders()) { remove + release } else keep.
            let has_cache_readers = cache_context.backend_slot_item(slot).has_cache_readers();
            if has_cache_readers {
                kept.push(slot);
            } else {
                let ontology_data_ids: Vec<OntologyDataId> = cache_context
                    .backend_slot_item(slot)
                    .get_ontology_identifier_data_hash()
                    .values()
                    .copied()
                    .collect();
                for ontology_data in ontology_data_ids {
                    cache_context
                        .ontology_data_mut(ontology_data)
                        .dec_usage_count(1);
                    if cache_context.ontology_data(ontology_data).get_usage_count() <= 0 {
                        self.ontology_data_released_count += 1;
                        self.ontology_data_released_while_slot_update_count += 1;
                        let rec_ref = cache_context
                            .ontology_data(ontology_data)
                            .get_recomputation_reference_linker();
                        if rec_ref.is_some() {
                            cache_context
                                .ontology_data_recomp_ref_linker_mut(rec_ref)
                                .set_ontology_data_inactive();
                        }
                    }
                }
                // releaseTemporaryMemoryPools(slot->getMemoryPools());
                self.reader_slot_released_count += 1; // ++mReaderSlotReleasedCount
            }
        }
        self.slot_linker = kept;
    }

    /// Port of `CBackendRepresentativeMemoryCache::createCacheReader`.
    ///
    /// Allocates a reader and prepends it to the reader chain under the reader-sync
    /// mutex.
    ///
    /// KONCLUDE-PORT-NOTE[threading]: `mReaderSyncMutex.lock()/unlock()` → inline
    /// (single-threaded). KONCLUDE-PORT-NOTE[ownership]: `reader->append(mReaderLinker)`
    /// makes the reader the new head → `self.reader_linker.insert(0, reader)`.
    pub fn create_cache_reader(&mut self, cache_context: &mut CacheContext) -> ReaderId {
        let reader =
            cache_context.alloc_backend_cache_reader(BackendRepresentativeMemoryCacheReader::new());
        // mReaderSyncMutex.lock(); [threading] inline
        self.reader_linker.insert(0, reader);
        // mReaderSyncMutex.unlock();
        reader
    }

    /// Port of `CBackendRepresentativeMemoryCache::createOntologyFixedCacheReader`.
    ///
    /// Allocates a reader pinned to the fixed ontology data for `ontology_identifier`
    /// (bumping that data's usage count), then waits until its individual-label
    /// associations are indexed.
    ///
    /// KONCLUDE-PORT-NOTE[threading]: `mFixedOntologyIdentifierDataHashLock` /
    /// `waitIndividualLabelAssociationIndexed()` → inline (single-threaded).
    pub fn create_ontology_fixed_cache_reader(
        &mut self,
        ontology_identifier: Cint64,
        cache_context: &mut CacheContext,
    ) -> ReaderId {
        let reader =
            cache_context.alloc_backend_cache_reader(BackendRepresentativeMemoryCacheReader::new());
        // mFixedOntologyIdentifierDataHashLock.lockForRead(); [threading] inline
        let ontology_data: OntologyDataId = self
            .fixed_ontology_identifier_data_hash
            .get(&ontology_identifier)
            .copied()
            .unwrap_or(OntologyDataId::NONE);
        if ontology_data != OntologyDataId::NONE {
            cache_context
                .ontology_data_mut(ontology_data)
                .inc_usage_count(1);
            cache_context
                .ontology_data_mut(ontology_data)
                .wait_individual_label_association_indexed();
        }
        cache_context
            .backend_cache_reader_mut(reader)
            .fix_ontology_data(ontology_data);
        // mFixedOntologyIdentifierDataHashLock.unlock(); [threading] inline
        reader
    }

    /// Port of `CBackendRepresentativeMemoryCache::createCacheWriter`
    /// (`return new CBackendRepresentativeMemoryCacheWriter(this);`).
    ///
    /// KONCLUDE-PORT-NOTE[api]: the writer holds `mCache = this`; with no cache
    /// arena there is no `BackendCacheId` for `self`, so the alloc + back-reference
    /// is `W6-DEFER[api]` (reconciles to
    /// `ctx.alloc_writer(BackendRepresentativeMemoryCacheWriter::new(self_id))`).
    pub fn create_cache_writer(&mut self) -> WriterId {
        // W6-DEFER[api]: alloc Writer with mCache = self.
        WriterId::NONE
    }

    /// Port of `CBackendRepresentativeMemoryCache::writeCachedData`
    /// (`return this;`).
    ///
    /// Forwards a queued write payload to the writer thread: bumps the pending
    /// count, throttles on the pending-write semaphore, then either drains the
    /// write inline (direct-update synchronization) or posts the event.
    ///
    /// KONCLUDE-PORT-NOTE[threading]: `mPendingUpdateCount.ref()` →
    /// `self.pending_update_count += 1`; `mRemainingWritePendingSemaphore.acquire()`,
    /// `mDirectUpdateSyncMutex`, `postEvent(...)` → inline (single-threaded). The
    /// posted/handled `CWriteBackendAssociationCachedEvent` is cross-family
    /// (`events.rs`) → `W6-DEFER[api]`; the inline drain forwards to the sibling
    /// `process_customs_events` (facade3).
    pub fn write_cached_data(
        &mut self,
        write_data: CacheWriteDataId,
        memory_pools: Cint64,
    ) -> &mut Self {
        if self.stat_collect_statistics {
            self.pending_update_count += 1; // mPendingUpdateCount.ref();
        }
        if self.limit_remaining_write_pending {
            // mRemainingWritePendingSemaphore.acquire(); [threading] inline (no block)
        }
        if self.conf_direct_update_synchronization {
            // mDirectUpdateSyncMutex.lock(); [threading] inline
            // CWriteBackendAssociationCachedEvent* procEvent = new …(writeData, memoryPools);
            // processCustomsEvents(CWriteBackendAssociationCachedEvent::EVENTTYPE, procEvent);
            // W6-DEFER[api]: build the event; sibling call:
            //   self.process_customs_events(event::WRITE_BACKEND_ASSOCIATION_ENTRY, procEvent);
            let _ = (write_data, memory_pools);
            // mDirectUpdateSyncMutex.unlock();
        } else {
            // postEvent(new CWriteBackendAssociationCachedEvent(writeData, memoryPools));
            // [threading] W6-DEFER[api]: enqueue onto the writer-thread event queue.
            let _ = (write_data, memory_pools);
        }
        self
    }

    /// Port of `CBackendRepresentativeMemoryCache::installTemporaryCardinalities`.
    ///
    /// For each temporary cardinality write record, resolves the label item it
    /// refers to and merges the per-role existential-max / minimal-restricting
    /// cardinalities into the label's cardinality extension data (creating a fresh
    /// extension when the existing one lacks a referenced role).
    ///
    /// KONCLUDE-PORT-NOTE[api]: an `OntologyData`/`LabelCacheItem`/temp-record
    /// object-graph traversal; faithful `W6-DEFER[api]` (the
    /// `[memory-pool]` cardinality-data allocations are deferred too).
    pub fn install_temporary_cardinalities(
        &mut self,
        temp_card_write_data_linker: BackendTempWriteRecordId,
        ontology_data: OntologyDataId,
    ) {
        // W6-DEFER[api]: faithful control flow (C++ 562–607):
        //   context = ontologyData->getOntologyContext();
        //   for each tempCardWriteDataLinkerIt:
        //     labelCacheItem = (LabelCacheItem*)tempCard…->getLabelWriteDataLinker()->getTemporaryData();
        //     cardValueLinker = tempCard…->getCardinalityCacheValueLinker();
        //     extensionData = labelCacheItem->getExtensionData(CARDINALITY_HASH);
        //     if (extensionData) { handled = true; for each cardValueLinkerIt:
        //         roleCardData = extensionData->getRoleCardinalityData(roleTag);
        //         if (roleCardData) { updateExistentialMaxUsedCardinality / updateMinimumRestrictingCardinality }
        //         else handled = false; }
        //     if (!handled) { newExtensionData = alloc + initCardinalityExtensionData();
        //         for each cardValueLinkerIt: cardData = alloc; cardData->initCardinalityData(cardCount,minRestCount);
        //           if (extensionData) merge prior roleCardData; newExtensionData->setRoleCardinalityData(roleTag,cardData); }
        //         labelCacheItem->setExtensionData(CARDINALITY_HASH, newExtensionData); }
        let _ = (temp_card_write_data_linker, ontology_data);
    }

    /// Port of `CBackendRepresentativeMemoryCache::installTemporaryLabels`.
    ///
    /// For each temporary label write record, recomputes the signature for the
    /// neighbour-instantiated-role-set-combination label (resolving its temporary
    /// entry cache-values to their installed label items), then resolves or creates
    /// the canonical label cache item for `(labelType, signature, value-set)`,
    /// merges its handled/saturated/nondeterministic flags, and writes the resolved
    /// item back onto the temp record.
    ///
    /// KONCLUDE-PORT-NOTE[api]: the central label-interning loop over the per-type
    /// signature→label hash; faithful `W6-DEFER[api]`. Calls the siblings
    /// `addCreatedLabelStatistics` and `getNeighbourArrayRoleTagResolvingLabelExtensionData`
    /// (facade3) when a new item / combination label is created.
    pub fn install_temporary_labels(
        &mut self,
        temp_label_write_data_linker: BackendTempWriteRecordId,
        ontology_data: OntologyDataId,
    ) {
        // W6-DEFER[api]: faithful control flow (C++ 614–696):
        //   context = ontologyData->getOntologyContext();
        //   for each tempLabelWriteDataLinkerIt:
        //     signature = tempLabel…->getSignature();
        //     if (labelType == NEIGHBOUR_INSTANTIATED_ROLE_SET_COMBINATION_LABEL):
        //       signature = 0; for each labelValueLinkerIt:
        //         if (cacheValue.getCacheValueIdentifier() == CACHE_VALUE_TAG_AND_TEMPORARY_ENTRY):
        //           resolve tmpLabelWriteData->getTemporaryData() label item, rewrite cacheValue;
        //         signature = Utilities::getSignatureExtensionByCacheValue(signature, cacheValue);
        //       tempLabel…->setSignature(signature);
        //     sigResolveItem = (*ontologyData->getSignatureLabelItemHash(labelType))[signature];
        //     scan sigResolveItem for an identical (count + tag/value) refLabelItem;
        //     if (!refLabelItem) { alloc + initCacheEntry(signature, ontologyData->getNextEntryID(), labelType);
        //       build tag→value hash + value chain; self.add_created_label_statistics(labelType, refLabelItem, ontologyData);
        //       sigResolveItem.appendLabelItem(refLabelItem); }
        //     merge completelyHandled/completelySaturated/nondeterministicElements flags;
        //     if (labelType == NEIGHBOUR_INSTANTIATED_ROLE_SET_COMBINATION_LABEL):
        //       self.get_neighbour_array_role_tag_resolving_label_extension_data(refLabelItem, ontologyData);
        //     tempLabel…->setTemporaryData(refLabelItem);
        let _ = (temp_label_write_data_linker, ontology_data);
    }

    /// Port of `CBackendRepresentativeMemoryCache::addCreatedLabelStatistics`
    /// (`return this;`).
    ///
    /// Bumps the per-type and overall label-count / max-value-count / all-value-count
    /// statistics for a newly created label item.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: `label->getCacheValueCount()` resolves through
    /// `CacheContext` because C++ stores the label as a raw pointer.
    pub fn add_created_label_statistics(
        &mut self,
        label_type: Cint64,
        label: LabelCacheItemId,
        ontology_data: OntologyDataId,
        cache_context: &CacheContext,
    ) -> &mut Self {
        let cache_value_count = cache_context
            .label_cache_item(label)
            .get_cache_value_count();
        let lt = label_type as usize;
        self.stat_label_count += 1;
        self.stat_max_label_value_count = self.stat_max_label_value_count.max(cache_value_count);
        self.stat_label_type_count[lt] += 1;
        self.stat_label_type_max_value_count[lt] =
            self.stat_label_type_max_value_count[lt].max(cache_value_count);
        self.stat_label_type_all_value_count[lt] += cache_value_count;
        let _ = ontology_data;
        self
    }

    /// Port of `CBackendRepresentativeMemoryCache::getExtendedLabel`.
    ///
    /// Returns the canonical label item equal to `label` plus `extending_cache_value`:
    /// returns `label` unchanged if the value is already present, otherwise resolves
    /// (by extended signature) or creates the extended label item (copying the
    /// cardinality extension for full-concept-set labels and the role-tag-resolving
    /// extension for combination labels).
    ///
    /// KONCLUDE-PORT-NOTE[api]: label-interning over the signature→label hash;
    /// faithful `W6-DEFER[api]`, returns the input `label` (the no-op branch).
    pub fn get_extended_label(
        &mut self,
        label_type: Cint64,
        label: LabelCacheItemId,
        extending_cache_value: CacheValue,
        ontology_data: OntologyDataId,
    ) -> LabelCacheItemId {
        // W6-DEFER[api]: faithful control flow (C++ 710–806):
        //   if (label->getTagCacheValueHash(false)->contains(extendingCacheValue.getTag())) return label;
        //   signature = label->getSignature() + qHash(extendingCacheValue.getTag());
        //   newCount = label->getCacheValueCount() + 1;
        //   scan (*ontologyData->getSignatureLabelItemHash(labelType))[signature] for identical item → return it;
        //   else alloc refLabelItem; initCacheEntry(signature, ontologyData->getNextEntryID(), labelType);
        //     copy value chain + add extendingCacheValue; copy NEIGHBOUR/FULL_CONCEPT_SET extensions;
        //     self.add_created_label_statistics(labelType, refLabelItem, ontologyData);
        //     sigResolveItem.appendLabelItem(refLabelItem); return refLabelItem;
        let _ = (label_type, extending_cache_value, ontology_data);
        label
    }

    /// Port of `CBackendRepresentativeMemoryCache::getReducedLabel`.
    ///
    /// Returns the canonical label item equal to `label` minus the values for which
    /// `reduce_check_function` returns true: returns `label` unchanged if nothing is
    /// removed, otherwise resolves (by reduced signature) or creates the reduced
    /// label item.
    ///
    /// KONCLUDE-PORT-NOTE[api]: `function<bool(const CCacheValue&)>` → the closure
    /// `reduce_check_function: &dyn Fn(&CacheValue) -> bool`. Faithful
    /// `W6-DEFER[api]` over the value-chain walk; returns the input `label`.
    pub fn get_reduced_label(
        &mut self,
        label_type: Cint64,
        label: LabelCacheItemId,
        reduce_check_function: &dyn Fn(&CacheValue) -> bool,
        ontology_data: OntologyDataId,
    ) -> LabelCacheItemId {
        // W6-DEFER[api]: faithful control flow (C++ 811–878):
        //   for each value: if (!reduceCheckFunction(cacheValue)) { signature += qHash(tag); newCount++; }
        //   if (newCount == label->getCacheValueCount()) return label;
        //   scan signature bucket for identical reduced item → return it;
        //   else alloc + initCacheEntry; copy kept values; combination-extension;
        //     self.add_created_label_statistics(...); appendLabelItem; return refLabelItem;
        let _ = (label_type, reduce_check_function, ontology_data);
        label
    }

    /// Port of `CBackendRepresentativeMemoryCache::getAdditionMergedLabel`.
    ///
    /// Returns the canonical label item equal to the union of `addition_label` and
    /// `associated_label`: handles the null / identical / already-subsumed shortcuts,
    /// otherwise resolves (by merged signature) or creates the merged label item
    /// (unioning the cardinality extensions for full-concept-set labels).
    ///
    /// KONCLUDE-PORT-NOTE[api]: faithful `W6-DEFER[api]`; the three pointer
    /// shortcuts are preserved on the input ids (null `addition` → `associated`;
    /// null `associated` → `addition`; equal ids → `associated`).
    pub fn get_addition_merged_label(
        &mut self,
        label_type: Cint64,
        addition_label: LabelCacheItemId,
        associated_label: LabelCacheItemId,
        ontology_data: OntologyDataId,
    ) -> LabelCacheItemId {
        if addition_label == LabelCacheItemId::NONE {
            return associated_label;
        }
        if associated_label == LabelCacheItemId::NONE {
            return addition_label;
        }
        if addition_label == associated_label {
            return associated_label;
        }
        // W6-DEFER[api]: faithful control flow (C++ 894–1022):
        //   check whether all additionLabel values are already in associatedLabel
        //     (valuesAlreadyIncluded) → return associatedlabel;
        //   else extend signature/newCount; scan signature bucket for identical merged item → return it;
        //   else alloc + initCacheEntry; copy associated + union addition values;
        //     combination-extension; union FULL_CONCEPT_SET cardinality extensions of both;
        //     self.add_created_label_statistics(...); appendLabelItem; return refLabelItem;
        let _ = (label_type, ontology_data);
        associated_label
    }

    /// Port of `CBackendRepresentativeMemoryCache::checkAssociationUsage`.
    ///
    /// For each association-use record, marks the referenced individual's
    /// association incompletely-handled when its current association data is missing
    /// or its update id has drifted from the used id while completely handled;
    /// returns whether any association was updated.
    ///
    /// KONCLUDE-PORT-NOTE[api]: the per-record `IndividualAssociationData` lookups
    /// are `W6-DEFER[api]`; the `self.checked_indi_count` / `self.check_incompatible_indi_count`
    /// bumps and the sibling call are kept in the control flow.
    pub fn check_association_usage(
        &mut self,
        temp_ass_use_data_linker: BackendTempWriteRecordId,
        ontology_data: OntologyDataId,
    ) -> bool {
        let mut associations_updated = false;
        // W6-DEFER[api]: for each tempAssUseDataLinkerIt in the chain:
        //   individualID = it->getIndividualID(); usedUpateID = it->getUsedAssociationUpdateId();
        //   associationData = ontologyData->getIndividualIdAssoiationDataVector()[individualID] (bounds-checked);
        //   self.checked_indi_count += 1;
        //   if (!associationData || (associationData->getAssociationDataUpdateId() != usedUpateID
        //                            && associationData->isCompletelyHandled())) {
        //     associations_updated |= self.mark_representative_referenced_individual_association_incompletely_handled(individualID, associationData, ontologyData);
        //     self.check_incompatible_indi_count += 1;
        //   }
        let _ = (temp_ass_use_data_linker, ontology_data);
        associations_updated
    }

    /// Port of `CBackendRepresentativeMemoryCache::markRepresentativeReferencedIndividualAssociationIncompletelyHandled`.
    ///
    /// Marks `indi_id`'s association incompletely handled, redirecting to its
    /// representative-same individual when one exists.
    ///
    /// KONCLUDE-PORT-NOTE[api]: the representative redirection is `W6-DEFER[api]`;
    /// the control flow forwards to the sibling `markIndividualAssociationIncompletelyHandled`.
    pub fn mark_representative_referenced_individual_association_incompletely_handled(
        &mut self,
        indi_id: Cint64,
        association_data: IndividualAssociationDataId,
        ontology_data: OntologyDataId,
    ) -> bool {
        // W6-DEFER[api]: faithful control flow (C++ 1061–1071):
        //   if (!associationData || !associationData->hasRepresentativeSameIndividualMerging())
        //     return self.mark_individual_association_incompletely_handled(indiId, associationData, ontologyData);
        //   else { repAssociationData = ontologyData->…[associationData->getRepresentativeSameIndividualId()];
        //     return self.mark_individual_association_incompletely_handled(repAssociationData->getRepresentativeSameIndividualId(), repAssociationData, ontologyData); }
        let has_representative_same_individual_merging = false; // W6-DEFER[api]
        if association_data == IndividualAssociationDataId::NONE
            || !has_representative_same_individual_merging
        {
            self.mark_individual_association_incompletely_handled(
                indi_id,
                association_data,
                ontology_data,
            )
        } else {
            // W6-DEFER[api]: redirect to representative-same association data.
            self.mark_individual_association_incompletely_handled(
                indi_id,
                association_data,
                ontology_data,
            )
        }
    }

    /// Port of `CBackendRepresentativeMemoryCache::markIndividualAssociationIncompletelyHandled`.
    ///
    /// Localises the individual's association data, stamps a fresh cache-update id,
    /// carries over the neighbour role-set hash / array, clears its completely-handled
    /// flag, and re-stores the updated association as incompletely marked.
    ///
    /// KONCLUDE-PORT-NOTE[api]: the localisation + flag/neighbour copies are
    /// `W6-DEFER[api]`; `self.next_indi_update_id` advance and the sibling calls
    /// (`createLocalizedIndividualAssociationData`, `getIndividualAssociationDataMemoryContext`,
    /// `storeIndividualIncompletelyMarked`, `setUpdatedIndividualAssociationData`)
    /// are kept in the control flow.
    pub fn mark_individual_association_incompletely_handled(
        &mut self,
        individual_id: Cint64,
        association_data: IndividualAssociationDataId,
        ontology_data: OntologyDataId,
    ) -> bool {
        let mut associations_updated = false;
        let is_completely_handled = true; // W6-DEFER[api]: associationData->isCompletelyHandled()
        if association_data == IndividualAssociationDataId::NONE || is_completely_handled {
            let loc_association_data = self.create_localized_individual_association_data(
                individual_id,
                association_data,
                ontology_data,
                false,
                true,
            );
            let _context = self.get_individual_association_data_memory_context_deferred(
                loc_association_data,
                ontology_data,
                None,
            );
            let cache_update_id = self.next_indi_update_id;
            self.next_indi_update_id += 1;
            // W6-DEFER[api]: locAssociationData->setCacheUpdateId(cache_update_id);
            //   if (associationData && associationData->getNeighbourRoleSetHash()) {
            //     locAssociationData->setNeighbourRoleSetHash(associationData->getNeighbourRoleSetHash());
            //     locAssociationData->setRoleSetNeighbourArray(associationData->getRoleSetNeighbourArray()); }
            //   locAssociationData->setCompletelyHandled(false);
            let _ = cache_update_id;
            associations_updated = true;
            // storeIndividualIncompletelyMarked(locAssociationData, !locAssociationData->isCompletelyHandled(), ontologyData);
            self.store_individual_incompletely_marked(loc_association_data, true, ontology_data);
            self.set_updated_individual_association_data(
                individual_id,
                loc_association_data,
                ontology_data,
            );
        }
        associations_updated
    }

    /// Port of `CBackendRepresentativeMemoryCache::markIndividualAssociationCompletelyHandled`.
    ///
    /// As `markIndividualAssociationIncompletelyHandled` but sets the
    /// completely-handled flag (entered only when the association is not already
    /// completely handled).
    pub fn mark_individual_association_completely_handled(
        &mut self,
        individual_id: Cint64,
        association_data: IndividualAssociationDataId,
        ontology_data: OntologyDataId,
    ) -> bool {
        let mut associations_updated = false;
        let is_completely_handled = false; // W6-DEFER[api]: associationData->isCompletelyHandled()
        if association_data == IndividualAssociationDataId::NONE || !is_completely_handled {
            let loc_association_data = self.create_localized_individual_association_data(
                individual_id,
                association_data,
                ontology_data,
                false,
                true,
            );
            let _context = self.get_individual_association_data_memory_context_deferred(
                loc_association_data,
                ontology_data,
                None,
            );
            let cache_update_id = self.next_indi_update_id;
            self.next_indi_update_id += 1;
            // W6-DEFER[api]: locAssociationData->setCacheUpdateId(cache_update_id);
            //   carry neighbour role-set hash/array; locAssociationData->setCompletelyHandled(true);
            let _ = cache_update_id;
            associations_updated = true;
            // storeIndividualIncompletelyMarked(locAssociationData, !locAssociationData->isCompletelyHandled(), ontologyData);
            self.store_individual_incompletely_marked(loc_association_data, false, ontology_data);
            self.set_updated_individual_association_data(
                individual_id,
                loc_association_data,
                ontology_data,
            );
        }
        associations_updated
    }

    /// Port of `CBackendRepresentativeMemoryCache::checkUpdateRejection`.
    ///
    /// Decides whether to reject a batch of association updates: rejects when too
    /// many propagation-cut-incompatible individuals' linked-neighbour counts /
    /// ratios exceed the configured limits, or when the incompatible-update ratio
    /// exceeds the configured threshold.
    ///
    /// KONCLUDE-PORT-NOTE[api]: the per-record `IndividualAssociationData` lookups
    /// are `W6-DEFER[api]`; the configured-threshold comparisons against
    /// `self.conf_update_rejecting_*` are ported into the (deferred) control flow.
    pub fn check_update_rejection(
        &mut self,
        temp_ass_write_data_linker: BackendTempWriteRecordId,
        ontology_data: OntologyDataId,
    ) -> bool {
        let mut rejection = false;
        let indi_update_count: Cint64 = 0;
        let incompatible_indi_update_count: Cint64 = 0;
        let _neighbour_link_count: Cint64 = 0;
        // W6-DEFER[api]: faithful control flow (C++ 1150–1186):
        //   for each tempAssWriteDataLinkerIt (while !rejection):
        //     if (it->getDeterministicSameIndividualId() == individualID) {
        //       ++indiUpdateCount; associationData = ontologyData->…[individualID];
        //       if (associationData && associationData->getAssociationDataUpdateId() != usedUpdateId) {
        //         ++incompatibleIndiUpdateCount;
        //         if (associationData->getLastPropagationCuttingUpdateId() > usedUpdateId) {
        //           neighbourLinkCount += associationData->getNeighbourRoleSetHash()->getNeighbourCount();
        //           totalIndiCount = ontologyData->getIndividualAssociationsCount();
        //           if (self.conf_update_rejecting_incompatible_propagation_cutted_individual_linked_neighbour_count >= 0
        //               && neighbourLinkCount > that) rejection = true;
        //           if ((double)neighbourLinkCount/totalIndiCount > self.conf_update_rejecting_incompatible_propagation_cutted_individual_linked_neighbour_ratio) rejection = true;
        //         } } } }
        let incom_update_ratio =
            (incompatible_indi_update_count as f64) / (indi_update_count as f64);
        if incom_update_ratio
            > self.conf_update_rejecting_incompatible_individual_associations_ratio
        {
            rejection = true;
        }
        let _ = (temp_ass_write_data_linker, ontology_data);
        rejection
    }

    /// Port of `CBackendRepresentativeMemoryCache::handleUpdateRejection`
    /// (`return true;`).
    ///
    /// On a rejected batch, touches the cache-touch id of every scheduled
    /// individual's existing association data.
    ///
    /// KONCLUDE-PORT-NOTE[api]: the per-record lookups + `setCacheTouchId` are
    /// `W6-DEFER[api]`; `self.next_indi_update_id` would advance once per scheduled
    /// individual (kept in the deferred control flow).
    pub fn handle_update_rejection(
        &mut self,
        temp_ass_write_data_linker: BackendTempWriteRecordId,
        ontology_data: OntologyDataId,
    ) -> bool {
        // W6-DEFER[api]: faithful control flow (C++ 1193–1207):
        //   for each tempAssWriteDataLinkerIt:
        //     if (it->isScheduledIndividual()) {
        //       associationData = ontologyData->…[individualID];
        //       if (associationData) associationData->setCacheTouchId(self.next_indi_update_id++); }
        let _ = (temp_ass_write_data_linker, ontology_data);
        true
    }

    /// Port of `CBackendRepresentativeMemoryCache::analyseDeterministicSameAsAssociationInstallation`.
    ///
    /// Collects, per deterministic-same-as target, the set of individuals whose
    /// associations could be installed against it (and the subset that would be a
    /// first installation), pulling in the already-considered same-handled members.
    ///
    /// KONCLUDE-PORT-NOTE[api]: the per-record lookups + label walks are
    /// `W6-DEFER[api]`; the writes into `self.deterministic_same_handling_installation_data_hash`
    /// are ported into the (deferred) control flow.
    pub fn analyse_deterministic_same_as_association_installation(
        &mut self,
        temp_ass_write_data_linker: BackendTempWriteRecordId,
        ontology_data: OntologyDataId,
    ) -> bool {
        let installable = false;
        // W6-DEFER[api]: faithful control flow (C++ 1215–1252):
        //   for each tempAssWriteDataLinkerIt:
        //     if (it->getDeterministicSameIndividualId() != individualID) {
        //       associationData = ontologyData->…[individualID];
        //       if (!associationData || (update-id matches && !hasDeterministicSameIndividualMerging())) {
        //         data = self.deterministic_same_handling_installation_data_hash[sameAsIndividualId];
        //         data.id_possible_installation_set.insert(individualID);
        //         if (!associationData || !hasDeterministicSameIndividualMerging())
        //           data.id_first_possible_installation_set.insert(individualID);
        //         installable = true;
        //         if (associationData) for each value of det-same-handled label:
        //           data.id_possible_installation_set.insert(otherId); } }
        let _ = (temp_ass_write_data_linker, ontology_data);
        installable
    }

    /// Port of `CBackendRepresentativeMemoryCache::installDeterministicSameAsAssociationUpdates`.
    ///
    /// For each record whose deterministic-same id differs from its individual,
    /// either installs the deterministic-same association update (when the target's
    /// same-handled label already covers the individual) or records the failure
    /// statistics and re-marks the individuals' handled state accordingly.
    ///
    /// KONCLUDE-PORT-NOTE[api]: the object-graph traversal is `W6-DEFER[api]`; the
    /// failure-statistic bumps on `self.stat_det_same_association_*` and the sibling
    /// calls (`installDeterministicSameAsAssociationUpdate`,
    /// `markIndividualAssociationCompletelyHandled`,
    /// `markRepresentativeReferencedIndividualAssociationIncompletelyHandled`) are
    /// kept in the control flow; `self.tmp_det_same_merging_completion_reference_hash`
    /// inserts are preserved.
    pub fn install_deterministic_same_as_association_updates(
        &mut self,
        temp_ass_write_data_linker: BackendTempWriteRecordId,
        ontology_data: OntologyDataId,
    ) -> bool {
        let associations_updated = false;
        // W6-DEFER[api]: faithful control flow (C++ 1260–1338):
        //   for each tempAssWriteDataLinkerIt:
        //     if (it->getDeterministicSameIndividualId() != individualID) {
        //       ontologyData->setSameIndividualsMergings(true);
        //       associationData = ontologyData->…[individualID];
        //       if (associationData) associationData->setCacheTouchId(self.next_indi_update_id++);
        //       if (!associationData || it->getDeterministicSameIndividualId() != associationData->getDeterministicSameIndividualId()) {
        //         detSameAsAssociationData = ontologyData->…[sameAsIndividualId];
        //         if (detSameAsAssociationData) {
        //           detSameHandledLabel = detSameAsAssociationData->getDeterministicMergedSameConsideredLabelCacheEntry();
        //           if (detSameHandledLabel && detSameHandledLabel->hasCachedTagValue(individualID)) {
        //             associations_updated = self.install_deterministic_same_as_association_update(associationData, individualID, detSameAsAssociationData, sameAsIndividualId, ontologyData);
        //             self.stat_det_same_association_install_count += 1;
        //           } else {
        //             self.stat_det_same_association_failed_count += 1; (+ the rep-merged / incomplete / update-id / dest-id sub-counters)
        //             if (label entries differ) self.tmp_det_same_merging_completion_reference_hash.insert(individualID, sameAsIndividualId);
        //             else if (!associationData || !isCompletelyHandled) self.mark_individual_association_completely_handled(individualID, associationData, ontologyData);
        //             self.mark_representative_referenced_individual_association_incompletely_handled(sameAsIndividualId, detSameAsAssociationData, ontologyData);
        //           } } }
        //       else if (associationData && update-id matches && !isCompletelyHandled)
        //         self.mark_individual_association_completely_handled(individualID, associationData, ontologyData); }
        let _ = (temp_ass_write_data_linker, ontology_data);
        associations_updated
    }

    /// Port of `CBackendRepresentativeMemoryCache::checkRequiresDeterministicSameAsAssociationUpdateInstallation`.
    ///
    /// Returns whether the individual's association still needs a deterministic-same
    /// update installed against the target: true unless its same/representative ids,
    /// neighbour array, completely-handled flag, and all associatable label entries
    /// already match the target's.
    ///
    pub fn check_requires_deterministic_same_as_association_update_installation(
        &self,
        association_data: IndividualAssociationDataId,
        individual_id: Cint64,
        det_same_as_association_data: IndividualAssociationDataId,
        same_as_individual_id: Cint64,
        ontology_data: OntologyDataId,
        cache_context: &CacheContext,
    ) -> bool {
        let _ = (individual_id, ontology_data);
        let association_data_ref = cache_context.individual_assoc_data(association_data);
        let det_same_as_association_data_ref =
            cache_context.individual_assoc_data(det_same_as_association_data);

        if association_data_ref.get_deterministic_same_individual_id() != same_as_individual_id {
            return true;
        }
        if association_data_ref.get_representative_same_individual_id()
            != det_same_as_association_data_ref.get_representative_same_individual_id()
        {
            return true;
        }
        if association_data_ref.get_role_set_neighbour_array()
            != det_same_as_association_data_ref.get_role_set_neighbour_array()
        {
            return true;
        }
        if association_data_ref.is_incompletely_marked() {
            return true;
        }
        for i in 0..LABEL_CACHE_ITEM_ASSOCIATABLE_TYPE_COUNT {
            if association_data_ref.get_label_cache_entry(i as Cint64)
                != det_same_as_association_data_ref.get_label_cache_entry(i as Cint64)
            {
                return true;
            }
        }
        false
    }

    /// Port of `CBackendRepresentativeMemoryCache::installDeterministicSameAsAssociationUpdate`
    /// (`return true;`).
    ///
    /// Installs the deterministic-same association: localises the individual's
    /// association, points its same/representative ids, neighbour array and label
    /// entries at the target's, merges the deterministic-same-individual-set label
    /// when it differs, and re-stores the updated (completely-handled) association.
    ///
    /// KONCLUDE-PORT-NOTE[api]: the localisation + per-label index-count updates +
    /// merge are `W6-DEFER[api]`; `self.next_indi_update_id` advance,
    /// `self.stat_det_same_representative_merging_count` bump, the sibling
    /// `getAdditionMergedLabel` / `updateIndexedAssociationCount` (facade2) calls,
    /// and `self.tmp_det_same_merging_completion_reference_hash` inserts are kept in
    /// the control flow.
    pub fn install_deterministic_same_as_association_update(
        &mut self,
        association_data: IndividualAssociationDataId,
        individual_id: Cint64,
        det_same_as_association_data: IndividualAssociationDataId,
        same_as_individual_id: Cint64,
        ontology_data: OntologyDataId,
    ) -> bool {
        let loc_association_data = self.create_localized_individual_association_data(
            individual_id,
            association_data,
            ontology_data,
            false,
            true,
        );
        let _context = self.get_individual_association_data_memory_context_deferred(
            loc_association_data,
            ontology_data,
            None,
        );
        let cache_update_id = self.next_indi_update_id;
        self.next_indi_update_id += 1;
        let _ = cache_update_id;
        // W6-DEFER[api]: faithful control flow (C++ 1376–1410):
        //   locAssociationData->setCacheUpdateId(cache_update_id);
        //   locAssociationData->setDeterministicSameIndividualId(sameAsIndividualId);
        //   locAssociationData->setRepresentativeSameIndividualId(detSameAsAssociationData->getRepresentativeSameIndividualId());
        //   if (locAssociationData->hasRepresentativeSameIndividualMerging() && (!associationData || !associationData->hasRepresentativeSameIndividualMerging())) {
        //     self.stat_det_same_representative_merging_count += 1; ontologyData->incIndividualAssociationMergingCount(); }
        //   locAssociationData->setRoleSetNeighbourArray(detSameAsAssociationData->getRoleSetNeighbourArray());
        //   locAssociationData->setNeighbourRoleSetHash(detSameAsAssociationData->getNeighbourRoleSetHash());
        //   locAssociationData->setCompletelyHandled(true);
        //   locAssociationData->setDeterministicConceptSetLabelCacheEntry(nullptr);
        //   for (i in 0..LABEL_CACHE_ITEM_ASSOCIATABLE_TYPE_COUNT) {
        //     locAssociationData->setLabelCacheEntry(i, detSameAsAssociationData->getLabelCacheEntry(i));
        //     self.update_indexed_association_count(locAssociationData, associationData, i, ontologyData); }  // facade2 overload (assoc-data)
        //   if (associationData->hasDeterministicSameIndividualMerging() && associationData->getDeterministicSameIndividualId() != sameAsIndividualId) {
        //     mergedSameAsLabelItem = self.get_addition_merged_label(DETERMINISTIC_SAME_INDIVIDUAL_SET_LABEL, prevSameAsLabelItem, detSameAsLabelItem, ontologyData);
        //     if (mergedSameAsLabelItem != detSameAsLabelItem) {
        //       locAssociationData->setLabelCacheEntry(DETERMINISTIC_SAME_INDIVIDUAL_SET_LABEL, mergedSameAsLabelItem);
        //       self.update_indexed_association_count(locAssociationData, detSameAsLabelItem, DETERMINISTIC_SAME_INDIVIDUAL_SET_LABEL, ontologyData);  // facade2 overload (label)
        //       self.tmp_det_same_merging_completion_reference_hash.insert(individualID, sameAsIndividualId); } }
        // KONCLUDE-PORT-NOTE[overload][unclear]: `updateIndexedAssociationCount` is
        //   C++-overloaded (assoc-data vs label-item 2nd arg); facade2 must split it
        //   into two names — left as a deferred sibling call here.
        let _ = LABEL_CACHE_ITEM_ASSOCIATABLE_TYPE_COUNT;
        self.store_individual_incompletely_marked(loc_association_data, false, ontology_data);
        self.set_updated_individual_association_data(
            individual_id,
            loc_association_data,
            ontology_data,
        );
        let _ = (det_same_as_association_data, same_as_individual_id);
        true
    }

    /// Port of `CBackendRepresentativeMemoryCache::installAssociationUpdates`.
    ///
    /// For each record whose deterministic-same id equals its individual, resolves
    /// any pending deterministic-same merge (completing + redirecting the individual)
    /// then installs the association update via `installAssociationUpdate` (facade2).
    ///
    /// KONCLUDE-PORT-NOTE[api]: the per-record lookups / redirection are
    /// `W6-DEFER[api]`; the sibling calls (`markIndividualAssociationCompletelyHandled`
    /// in this third, `installAssociationUpdate` in facade2) are kept in the flow.
    pub fn install_association_updates(
        &mut self,
        temp_ass_write_data_linker: BackendTempWriteRecordId,
        ontology_data: OntologyDataId,
    ) -> bool {
        let associations_updated = false;
        // W6-DEFER[api]: faithful control flow (C++ 1419–1444):
        //   for each tempAssWriteDataLinkerIt:
        //     if (it->getDeterministicSameIndividualId() == individualID) {
        //       associationData = ontologyData->…[individualID];
        //       if (associationData && associationData->hasDeterministicSameIndividualMerging()) {
        //         if (!associationData->isCompletelyHandled())
        //           self.mark_individual_association_completely_handled(individualID, associationData, ontologyData);
        //         individualID = associationData->getDeterministicSameIndividualId();
        //         associationData = ontologyData->…[individualID]; }
        //       associations_updated |= self.install_association_update(individualID, associationData, it, ontologyData);  // facade2
        //     }
        let _ = (temp_ass_write_data_linker, ontology_data);
        associations_updated
    }

    /// Port of `CBackendRepresentativeMemoryCache::createLocalizedIndividualAssociationData`.
    ///
    /// Allocates a fresh association-data record for the individual, choosing its
    /// memory home: reuse the existing separate memory-management context (when
    /// small enough or required), open a new separate context (when the heuristics
    /// for large/old/neighbour-heavy individuals fire, queueing the old one for
    /// deletion), or fall back to the shared ontology context; then initialises it
    /// from the prior association (or fresh for the individual).
    ///
    /// KONCLUDE-PORT-NOTE[api]: `incrementUpdateId` (C++ default `true`) is an
    /// explicit param. The whole body is `[memory-pool]` context selection +
    /// `IndividualAssociationData` init → faithful `W6-DEFER[api]`; the three
    /// `self.stat_individual_association_*` counters and the sibling
    /// `queueIndividualAssociationMemoryContextDeletion` call are kept in the flow.
    pub fn create_localized_individual_association_data(
        &mut self,
        individual_id: Cint64,
        association_data: IndividualAssociationDataId,
        ontology_data: OntologyDataId,
        allow_separated_management: bool,
        increment_update_id: bool,
    ) -> IndividualAssociationDataId {
        // W6-DEFER[api]: faithful control flow (C++ 1451–1529):
        //   existingIndiAssContext = associationData ? associationData->getIndividualAssociationMemoryContext() : null;
        //   decide separatedMemoryManagementReusing / separatedMemoryManagementNew via the size/age/neighbour heuristics;
        //   if (reusing) { locAssociationData = alloc in existing ctx; ctx->incIndividualAssociationDataUsageCount();
        //       ctx->setLastRecomputationReferenceLinker(ontologyData->getRecomputationReferenceLinker());
        //       self.stat_individual_association_separate_memory_managment_context_reuse_count += 1; }
        //   else if (new) { indiAssContext = alloc; locAssociationData = alloc in it; set first/last recomputation linkers;
        //       self.stat_individual_association_separate_memory_managment_context_creation_count += 1;
        //       if (existingIndiAssContext) { indiAssContext->setPreviousMemoryManagementCount(+1);
        //         existing->setLastRecomputationReferenceLinker(...); self.queue_individual_association_memory_context_deletion(existing, ontologyData); } }
        //   else { locAssociationData = alloc in shared ontology context;
        //       self.stat_individual_association_without_separate_memory_managment_count += 1; }
        //   if (associationData) locAssociationData->initAssociationData(associationData, incrementUpdateId);
        //   else locAssociationData->initAssociationData(individualID);
        let _ = (
            individual_id,
            association_data,
            ontology_data,
            allow_separated_management,
            increment_update_id,
        );
        IndividualAssociationDataId::NONE // W6-DEFER[api]: the freshly allocated localised association data.
    }

    /// Port of `CBackendRepresentativeMemoryCache::getIndividualAssociationDataMemoryContext`.
    ///
    /// Returns the association data's own separate memory-management context when it
    /// has one (flagging `requires_data_copying` when that context is now shared
    /// down to a single user that was previously separately managed), otherwise the
    /// shared ontology context.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: the returned
    /// `CBackendRepresentativeMemoryCacheContext*` may point at either an
    /// individual-association context or an ontology context. Until that base
    /// pointer has a Rust enum, the method returns the selected arena id's raw
    /// handle as the existing opaque `Cint64`.
    pub fn get_individual_association_data_memory_context(
        &self,
        association_data: IndividualAssociationDataId,
        ontology_data: OntologyDataId,
        requires_data_copying: Option<&mut bool>,
        cache_context: &CacheContext,
    ) -> Cint64 {
        let individual_context = cache_context
            .individual_assoc_data(association_data)
            .get_individual_association_memory_context();
        if individual_context.is_some() {
            let context_ref = cache_context.individual_assoc_context(individual_context);
            if let Some(requires_data_copying) = requires_data_copying {
                if context_ref.get_individual_association_data_usage_count() <= 1
                    && context_ref.get_previous_memory_management_count() > 0
                {
                    *requires_data_copying = true;
                }
            }
            return individual_context.raw;
        }
        cache_context
            .ontology_data(ontology_data)
            .get_ontology_context()
            .raw
    }

    /// Compatibility wrapper for deferred callers that have not yet been threaded
    /// with `CacheContext`.
    pub fn get_individual_association_data_memory_context_deferred(
        &self,
        association_data: IndividualAssociationDataId,
        ontology_data: OntologyDataId,
        requires_data_copying: Option<&mut bool>,
    ) -> Cint64 {
        // W6-DEFER[api]: call the context-threaded overload once the surrounding
        // facade method receives `CacheContext`.
        let _ = (association_data, ontology_data, requires_data_copying);
        INVALID
    }

    /// Port of `CBackendRepresentativeMemoryCache::isCacheValueRoleInverse`.
    ///
    /// True iff the cache value tags an inverse role (deterministic or
    /// nondeterministic; plain / asserted / nominal-connected).
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

    /// Port of `CBackendRepresentativeMemoryCache::isCacheValueRoleNondeterministic`.
    ///
    /// True iff the cache value tags a nondeterministic role (plain / inversed /
    /// asserted / inversed-asserted / nominal-connected / inversed-nominal-connected).
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

    /// Port of `CBackendRepresentativeMemoryCache::isRoleNeighbourLinkLabelItemCompatibility`.
    ///
    /// True iff the new role-neighbour-link label item is compatible with the prior
    /// one: same value count, every new value's role present in the prior with the
    /// same inverse-ness, and no role going from deterministic to nondeterministic.
    ///
    /// KONCLUDE-PORT-NOTE[api]: the `LabelCacheItem` / `LabelValueLinker` derefs are
    /// `W6-DEFER[api]`; the cache-value compatibility predicates call the siblings
    /// `is_cache_value_role_inverse` / `is_cache_value_role_nondeterministic` ported
    /// just above.
    pub fn is_role_neighbour_link_label_item_compatibility(
        &self,
        item_prev: LabelCacheItemId,
        item_new: LabelCacheItemId,
        cache_context: &CacheContext,
    ) -> bool {
        let item_prev_ref = cache_context.label_cache_item(item_prev);
        let item_new_ref = cache_context.label_cache_item(item_new);
        if item_prev_ref.get_cache_value_count() != item_new_ref.get_cache_value_count() {
            return false;
        }

        for linker_it in item_new_ref.get_cache_value_linker().iter().copied() {
            let new_cache_value = *cache_context
                .label_value_linker(linker_it)
                .get_cache_value();
            let tag = new_cache_value.get_tag();
            let Some(prev_linker) = item_prev_ref.tag_value_hash.get(&tag).copied() else {
                return false;
            };
            let prev_cache_value = cache_context
                .label_value_linker(prev_linker)
                .get_cache_value();
            if self.is_cache_value_role_inverse(prev_cache_value)
                != self.is_cache_value_role_inverse(&new_cache_value)
            {
                return false;
            }
            let prev_nondeterministic = self.is_cache_value_role_nondeterministic(prev_cache_value);
            let new_nondeterministic = self.is_cache_value_role_nondeterministic(&new_cache_value);
            if !prev_nondeterministic && new_nondeterministic {
                return false;
            }
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use super::super::backend::BackendRepresentativeMemoryCacheOntologyContext;
    use super::super::backend_data::{
        IndividualAssociationContext, IndividualAssociationData, OntologyData,
    };
    use super::super::backend_data::{LabelCacheItem, LabelCacheItemType};
    use super::*;

    fn label_with_value_count(
        cache_context: &mut CacheContext,
        value_count: Cint64,
    ) -> LabelCacheItemId {
        let mut label = LabelCacheItem::new(INVALID);
        label.init_cache_entry(0, value_count, LabelCacheItemType::FullConceptSetLabel);
        label.value_count = value_count;
        cache_context.alloc_label_cache_item(label)
    }

    #[test]
    fn add_created_label_statistics_uses_label_cache_value_count() {
        let mut cache = BackendRepresentativeMemoryCache::new(INVALID, "test", INVALID);
        let mut cache_context = CacheContext::new();
        let label_type = LabelCacheItemType::FullConceptSetLabel as Cint64;
        let first = label_with_value_count(&mut cache_context, 3);
        let second = label_with_value_count(&mut cache_context, 5);

        cache.add_created_label_statistics(label_type, first, OntologyDataId::NONE, &cache_context);
        cache.add_created_label_statistics(
            label_type,
            second,
            OntologyDataId::NONE,
            &cache_context,
        );

        let lt = label_type as usize;
        assert_eq!(cache.stat_label_count, 2);
        assert_eq!(cache.stat_max_label_value_count, 5);
        assert_eq!(cache.stat_label_type_count[lt], 2);
        assert_eq!(cache.stat_label_type_max_value_count[lt], 5);
        assert_eq!(cache.stat_label_type_all_value_count[lt], 8);
    }

    #[test]
    fn queue_individual_association_memory_context_deletion_prepends_to_ontology_queue() {
        let mut cache = BackendRepresentativeMemoryCache::new(INVALID, "test", INVALID);
        let mut cache_context = CacheContext::new();
        let ontology_data = cache_context.alloc_ontology_data(OntologyData::new());
        let first =
            cache_context.alloc_individual_assoc_context(IndividualAssociationContext::new(1));
        let second =
            cache_context.alloc_individual_assoc_context(IndividualAssociationContext::new(2));

        cache.queue_individual_association_memory_context_deletion(
            first,
            ontology_data,
            &mut cache_context,
        );
        cache.queue_individual_association_memory_context_deletion(
            second,
            ontology_data,
            &mut cache_context,
        );

        let ontology = cache_context.ontology_data(ontology_data);
        assert_eq!(
            ontology.get_release_queued_individual_association_context_linker(),
            second
        );
        assert_eq!(
            ontology.release_queued_individual_association_context_linker,
            vec![second, first]
        );
        assert_eq!(
            cache.stat_individual_association_separate_memory_managment_slot_referred_checking_queuing_count,
            2
        );
        assert_eq!(cache.stat_memory_managment_queued_checking_count, 2);
    }

    #[test]
    fn individual_association_data_memory_context_falls_back_to_ontology_context() {
        let cache = BackendRepresentativeMemoryCache::new(INVALID, "test", INVALID);
        let mut cache_context = CacheContext::new();
        let ontology_context = cache_context.alloc_backend_ontology_context(
            BackendRepresentativeMemoryCacheOntologyContext::new(BaseContextId::NONE),
        );
        let mut ontology = OntologyData::new();
        ontology.set_ontology_context(ontology_context);
        let ontology_data = cache_context.alloc_ontology_data(ontology);
        let association_data =
            cache_context.alloc_individual_assoc_data(IndividualAssociationData::new());
        let mut requires_data_copying = false;

        let context = cache.get_individual_association_data_memory_context(
            association_data,
            ontology_data,
            Some(&mut requires_data_copying),
            &cache_context,
        );

        assert_eq!(context, ontology_context.raw);
        assert!(!requires_data_copying);
    }

    #[test]
    fn individual_association_data_memory_context_flags_copying_for_last_previous_context() {
        let cache = BackendRepresentativeMemoryCache::new(INVALID, "test", INVALID);
        let mut cache_context = CacheContext::new();
        let ontology_context = cache_context.alloc_backend_ontology_context(
            BackendRepresentativeMemoryCacheOntologyContext::new(BaseContextId::NONE),
        );
        let mut ontology = OntologyData::new();
        ontology.set_ontology_context(ontology_context);
        let ontology_data = cache_context.alloc_ontology_data(ontology);
        let mut individual_context = IndividualAssociationContext::new(INVALID);
        individual_context.inc_individual_association_data_usage_count(1);
        individual_context.set_previous_memory_management_count(2);
        let individual_context = cache_context.alloc_individual_assoc_context(individual_context);
        let mut association = IndividualAssociationData::new();
        association.set_individual_association_memory_context(individual_context);
        let association_data = cache_context.alloc_individual_assoc_data(association);
        let mut requires_data_copying = false;

        let context = cache.get_individual_association_data_memory_context(
            association_data,
            ontology_data,
            Some(&mut requires_data_copying),
            &cache_context,
        );

        assert_eq!(context, individual_context.raw);
        assert!(requires_data_copying);
    }
}
