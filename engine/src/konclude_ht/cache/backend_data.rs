//! `cache::backend_data` — F1 **DEEP storage internals** for the backend
//! representative-memory association cache (Konclude
//! `Source/Reasoner/Kernel/Cache/CBackendRepresentativeMemory*`, manifest
//! `07-cache.md` §F1 "Ontology/label storage" + "Individual association" +
//! "Temporary write-data linker chains").
//!
//! These types are reachable only THROUGH the F1 facade / Reader / Writer (in the
//! sibling `cache/backend.rs`); the completion engine never names them. They are
//! the per-ontology data block, the per-individual association data, the label /
//! cardinality cache items + their extension data, the role-set-neighbour family,
//! the nominal indirect-connection data, the ~13 temporary write-data linker
//! chains, and the cross-thread retrieval-update coordination hash.
//!
//! Struct-definition sub-wave only: faithful fields + `new` / `Default`; method
//! bodies deferred (`// W6-CACHE method-batch`). NOT wired into a `mod.rs`.
//!
//! ## License (per `PORT.md` §License note)
//! Function-by-function translation of LGPLv3 Konclude source.
//!
//! ## Port conventions (PORT.md §44; manifest §Concurrency) — same as `backend.rs`
//! * `CXxx*` → typed arena `Id<T>` (`Id::NONE` == null); intrusive chains →
//!   owned `Vec<Id>` head-front; `QMutex`/`QSemaphore`/`QAtomic*` → opaque
//!   `Cint64` `[threading]`; pool allocators → opaque `Cint64` `[memory-pool]`;
//!   cross-family `CConcept`/`CRole`/`CIndividual`/`CIndividualReference`/
//!   `CIndividualBackendCachingData` → opaque `Cint64`.
//! * F0 shared: `CCacheValue` → `value::CacheValue`.
//!
//! ## Record-family enums formed here (manifest §Record-families)
//! * `BackendTempWriteRecord` — the ~13 `*Temporary*DataLinker` chains collapse
//!   (mirrors the W2 `DepKind` collapse): one tagged enum, the chain → `Vec<Id>`.
//! * `LabelCacheItemExtensionData` — the `*LabelCacheItemExtensionData`
//!   inheritance family (base + cardinality / association-map / neighbour-array
//!   -index / tag-label-resolving) collapse (PORT.md record-family→enum rule).

#![allow(dead_code)]

use std::collections::HashMap;

use super::super::model::substrate::{Cint64, Id, INVALID};
use super::value::CacheValue;
use super::backend::{
    BackendRepresentativeMemoryCachingFlags, BackendRepresentativeMemoryCacheOntologyContext,
    OntologyContextId,
};

// ===========================================================================
// Label-cache-item type / extension-type code constants (from
// CBackendRepresentativeMemoryLabelCacheItem.h).
// ===========================================================================

/// `CBackendRepresentativeMemoryLabelCacheItem::LABEL_CACHE_ITEM_ASSOCIATABLE_TYPE_COUNT`.
pub const LABEL_CACHE_ITEM_ASSOCIATABLE_TYPE_COUNT: usize = 15;
/// `CBackendRepresentativeMemoryLabelCacheItem::LABEL_CACHE_ITEM_TYPE_COUNT`.
pub const LABEL_CACHE_ITEM_TYPE_COUNT: usize = 16;

/// Port of `CBackendRepresentativeMemoryLabelCacheItem::LABEL_CACHE_ITEM_TYPE`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(i64)]
pub enum LabelCacheItemType {
    DeterministicConceptSetLabel = 0,
    NondeterministicConceptSetLabel = 1,
    FullConceptSetLabel = 2,
    DeterministicCombinedExistentialInstantiatedRoleSetLabel = 3,
    NondeterministicCombinedExistentialInstantiatedRoleSetLabel = 4,
    DeterministicCombinedNeighbourInstantiatedRoleSetLabel = 5,
    NondeterministicCombinedNeighbourInstantiatedRoleSetLabel = 6,
    DeterministicCombinedDataInstantiatedRoleSetLabel = 7,
    NondeterministicCombinedDataInstantiatedRoleSetLabel = 8,
    DeterministicSameIndividualSetLabel = 9,
    NondeterministicSameIndividualSetLabel = 10,
    DeterministicDiffrentIndividualSetLabel = 11,
    NondeterministicDiffrentIndividualSetLabel = 12,
    IndirectlyConnectedNominalIndividualSetLabel = 13,
    NeighbourInstantiatedRoleSetCombinationLabel = 14,
    NeighbourInstantiatedRoleSetLabel = 15,
}

impl Default for LabelCacheItemType {
    fn default() -> Self { LabelCacheItemType::DeterministicConceptSetLabel }
}

/// Port of `CBackendRepresentativeMemoryLabelCacheItemExtensionData::LABEL_CACHE_ITEM_EXTENSION_TYPE`.
/// (NB: `CARDINALITY_HASH` shares index 2 with `TAG_RESOLVING_HASH` in C++ — never
/// used together on the same label item type.)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(i64)]
pub enum LabelCacheItemExtensionType {
    IndividualAssociationMap = 0,
    IndividualNeighbourArrayIndex = 1,
    TagResolvingHash = 2,
}

impl Default for LabelCacheItemExtensionType {
    fn default() -> Self { LabelCacheItemExtensionType::IndividualAssociationMap }
}

/// `LABEL_CACHE_ITEM_EXTENSION_TYPE_COUNT`.
pub const LABEL_CACHE_ITEM_EXTENSION_TYPE_COUNT: usize = 3;

// ===========================================================================
// F1 DEEP arena id aliases.
// ===========================================================================
pub type OntologyDataId = Id<OntologyData>;
pub type IndividualAssociationDataId = Id<IndividualAssociationData>;
pub type IndividualAssociationContextId = Id<IndividualAssociationContext>;
pub type LabelCacheItemId = Id<LabelCacheItem>;
pub type CardinalityCacheItemId = Id<CardinalityCacheItem>;
pub type LabelValueLinkerId = Id<LabelValueLinker>;
pub type CardinalityValueLinkerId = Id<CardinalityValueLinker>;
pub type LabelCacheItemExtensionDataId = Id<LabelCacheItemExtensionData>;
pub type TagLabelResolvingDataLinkerId = Id<LabelCacheItemTagLabelResolvingDataLinker>;
pub type IndividualNeighbourRoleSetHashId = Id<IndividualNeighbourRoleSetHash>;
pub type IndividualRoleSetNeighbourArrayId = Id<IndividualRoleSetNeighbourArray>;
pub type IndividualRoleSetNeighbourDataId = Id<IndividualRoleSetNeighbourData>;
pub type IndividualRoleSetNeighbourIndividualIdLinkerId = Id<IndividualRoleSetNeighbourIndividualIdLinker>;
pub type NominalIndividualIndirectConnectionDataId = Id<NominalIndividualIndirectConnectionData>;
pub type ItemIndividualDataAssociationLinkerId = Id<ItemIndividualDataAssociationLinker>;
pub type RoleAssertionLinkerId = Id<RoleAssertionLinker>;
pub type OntologyDataRecomputationReferenceLinkerId = Id<OntologyDataRecomputationReferenceLinker>;
pub type CoordinationHashDataId = Id<BackendIndividualRetrievalComputationUpdateCoordinationHashData>;
/// the collapsed temporary-write-data linker chains (`BackendTempWriteRecord` enum).
pub type BackendTempWriteRecordId = Id<BackendTempWriteRecord>;

// ===========================================================================
// Value linkers + signature-resolve cache items (small DEEP payloads).
// ===========================================================================

/// Port of `CBackendRepresentativeMemoryLabelValueLinker` (`: CLinkerBase<CCacheValue,...>`).
/// The `CLinkerBase` payload is a `CCacheValue`; the chain is owned by the holder.
#[derive(Debug, Default, Clone)]
pub struct LabelValueLinker {
    /// the `CLinkerBase<CCacheValue>` payload.
    pub cache_value: CacheValue,
}
impl LabelValueLinker {
    pub fn new() -> Self { Self::default() }

    /// Port of `CBackendRepresentativeMemoryLabelValueLinker::initLabelValueLinker`
    /// (`setData(cacheValue); return this;`).
    pub fn init_label_value_linker(&mut self, cache_value: CacheValue) -> &mut Self {
        self.cache_value = cache_value; // the CLinkerBase<CCacheValue> payload.
        self
    }
    /// Port of `::getCacheValue` (`return getData();`).
    pub fn get_cache_value(&self) -> &CacheValue { &self.cache_value }
    /// Port of `::setCacheValue` (`setData(cacheValue); return this;`).
    pub fn set_cache_value(&mut self, cache_value: CacheValue) -> &mut Self {
        self.cache_value = cache_value;
        self
    }
}

/// Port of `CBackendRepresentativeMemoryCardinalityValueLinker` (`: CLinkerBase<cint64,...>`).
#[derive(Debug, Default, Clone)]
pub struct CardinalityValueLinker {
    /// the `CLinkerBase<cint64>` payload (the cardinality role tag).
    pub tag: Cint64,
    /// `cint64 mExistentialMaxUsedCardinality`.
    pub existential_max_used_cardinality: Cint64,
    /// `cint64 mMinimalRestrictingCardinality`.
    pub minimal_restricting_cardinality: Cint64,
}
impl CardinalityValueLinker {
    pub fn new() -> Self { Self::default() }

    /// Port of `CBackendRepresentativeMemoryCardinalityValueLinker::initCardinalityValueLinker`.
    pub fn init_cardinality_value_linker(
        &mut self,
        role_tag: Cint64,
        existential_max_used_cardinality: Cint64,
        minimal_restricting_cardinality: Cint64,
    ) -> &mut Self {
        self.tag = role_tag; // setData(roleTag) — the CLinkerBase<cint64> payload.
        self.existential_max_used_cardinality = existential_max_used_cardinality;
        self.minimal_restricting_cardinality = minimal_restricting_cardinality;
        self
    }
    /// Port of `::getRoleTag` (`return getData();`).
    pub fn get_role_tag(&self) -> Cint64 { self.tag }
    /// Port of `::getExistentialMaxUsedCardinality`.
    pub fn get_existential_max_used_cardinality(&self) -> Cint64 { self.existential_max_used_cardinality }
    /// Port of `::getMinimalRestrictingCardinality`.
    pub fn get_minimal_restricting_cardinality(&self) -> Cint64 { self.minimal_restricting_cardinality }
    /// Port of `::updateExistentialMaxUsedCardinality` (`qMax(...)`).
    pub fn update_existential_max_used_cardinality(&mut self, existential_max_used_cardinality: Cint64) -> &mut Self {
        self.existential_max_used_cardinality = existential_max_used_cardinality.max(self.existential_max_used_cardinality);
        self
    }
    /// Port of `::updateMinimalRestrictingCardinality` (`qMax(...)`).
    pub fn update_minimal_restricting_cardinality(&mut self, minimal_restricting_cardinality: Cint64) -> &mut Self {
        self.minimal_restricting_cardinality = minimal_restricting_cardinality.max(self.minimal_restricting_cardinality);
        self
    }
}

/// Port of `CBackendRepresentativeMemoryLabelSignatureResolveCacheItem`.
/// A signature → label-item-chain bucket (held by value in the reader scratch).
#[derive(Debug, Default, Clone)]
pub struct LabelSignatureResolveCacheItem {
    /// `CBackendRepresentativeMemoryLabelCacheItem* mLabelItemLinker` (chain → Vec head-front).
    pub label_item_linker: Vec<LabelCacheItemId>,
    /// `cint64 mLabelItemCount`.
    pub label_item_count: Cint64,
}
impl LabelSignatureResolveCacheItem {
    pub fn new() -> Self { Self::default() }

    /// Port of `::appendLabelItem`
    /// (`mLabelItemCount += linker->getCount(); mLabelItemLinker = linker->append(mLabelItemLinker);`).
    /// KONCLUDE-PORT-NOTE[ownership]: the C++ intrusive head-front prepend of a label-item
    /// CHAIN `linker` → owned-`Vec` prepend; `linker->getCount()` == the appended chain length.
    pub fn append_label_item(&mut self, linker: &[LabelCacheItemId]) -> &mut Self {
        self.label_item_count += linker.len() as Cint64;
        let mut new_chain = linker.to_vec();
        new_chain.append(&mut self.label_item_linker);
        self.label_item_linker = new_chain;
        self
    }
    /// Port of `::getLabelItems` (`return mLabelItemLinker;`).
    pub fn get_label_items(&self) -> &[LabelCacheItemId] { &self.label_item_linker }
    /// Port of `::getLabelItemCount`.
    pub fn get_label_item_count(&self) -> Cint64 { self.label_item_count }
}

/// Port of `CBackendRepresentativeMemoryCardinalitySignatureResolveCacheItem`.
#[derive(Debug, Default, Clone)]
pub struct CardinalitySignatureResolveCacheItem {
    /// `CBackendRepresentativeMemoryCardinalityCacheItem* mCardinalityCachetemLinker` (chain).
    pub cardinality_cache_item_linker: Vec<CardinalityCacheItemId>,
    /// `cint64 mCardinalityItemCount`.
    pub cardinality_item_count: Cint64,
}
impl CardinalitySignatureResolveCacheItem {
    pub fn new() -> Self { Self::default() }

    /// Port of `::appendCardinalityCacheItem`
    /// (`mCardinalityItemCount += linker->getCount(); mCardinalityCachetemLinker = linker->append(mCardinalityCachetemLinker);`).
    /// KONCLUDE-PORT-NOTE[ownership]: head-front chain prepend (see `LabelSignatureResolveCacheItem`).
    pub fn append_cardinality_cache_item(&mut self, linker: &[CardinalityCacheItemId]) -> &mut Self {
        self.cardinality_item_count += linker.len() as Cint64;
        let mut new_chain = linker.to_vec();
        new_chain.append(&mut self.cardinality_cache_item_linker);
        self.cardinality_cache_item_linker = new_chain;
        self
    }
    /// Port of `::getCardinalityCacheItems` (`return mCardinalityCachetemLinker;`).
    pub fn get_cardinality_cache_items(&self) -> &[CardinalityCacheItemId] { &self.cardinality_cache_item_linker }
    /// Port of `::getCardinalityCacheItemCount`.
    pub fn get_cardinality_cache_item_count(&self) -> Cint64 { self.cardinality_item_count }
}

// ===========================================================================
// Label cache item + cardinality cache item.
// ===========================================================================

/// Port of `CBackendRepresentativeMemoryLabelCacheItem`
/// (`: CLinkerBase<cint64,...>, CBackendRepresentativeMemoryCachingFlags`).
///
/// One cached label (a tagged cache-value set): its signature, the tag→value
/// linker hash + value chain, the individual-association count, and up to 3
/// extension-data slots (association map / neighbour-array index / tag-resolving
/// or cardinality hash). The `CLinkerBase<cint64>` payload is the entry id.
#[derive(Debug, Clone)]
pub struct LabelCacheItem {
    /// the `CLinkerBase<cint64>` payload (`getCacheEntryID`).
    pub cache_entry_id: Cint64,
    /// the `CBackendRepresentativeMemoryCachingFlags` base.
    pub flags: BackendRepresentativeMemoryCachingFlags,
    /// `CBackendRepresentativeMemoryCacheContext* mContext`.  [ownership] → opaque.
    pub context: Cint64,
    /// `LABEL_CACHE_ITEM_TYPE mCacheItemType`.
    pub cache_item_type: LabelCacheItemType,
    /// `cint64 mSignature`.
    pub signature: Cint64,
    /// `CCACHINGHASH<cint64, CBackendRepresentativeMemoryLabelValueLinker*>* mTagValueHash`.
    pub tag_value_hash: HashMap<Cint64, LabelValueLinkerId>,
    /// `CBackendRepresentativeMemoryLabelValueLinker* mValueLinker` (chain → Vec head-front).
    pub value_linker: Vec<LabelValueLinkerId>,
    /// `cint64 mValueCount`.
    pub value_count: Cint64,
    /// `cint64 mIndiAssociationCount`.
    pub indi_association_count: Cint64,
    /// `CBackendRepresentativeMemoryLabelCacheItemExtensionData* mExtensionData[3]`.
    pub extension_data: Vec<LabelCacheItemExtensionDataId>,
}

impl Default for LabelCacheItem {
    fn default() -> Self {
        LabelCacheItem {
            cache_entry_id: 0,
            flags: BackendRepresentativeMemoryCachingFlags::new(),
            context: INVALID,
            cache_item_type: LabelCacheItemType::default(),
            signature: 0,
            tag_value_hash: HashMap::new(),
            value_linker: Vec::new(),
            value_count: 0,
            indi_association_count: 0,
            extension_data: vec![Id::NONE; LABEL_CACHE_ITEM_EXTENSION_TYPE_COUNT],
        }
    }
}

impl LabelCacheItem {
    /// Port of `CBackendRepresentativeMemoryLabelCacheItem::CBackendRepresentativeMemoryLabelCacheItem(context)`.
    pub fn new(context: Cint64) -> Self {
        LabelCacheItem { context, ..Default::default() }
    }
    /// Port of `::initCacheEntry`.
    pub fn init_cache_entry(&mut self, signature: Cint64, entry_id: Cint64, type_: LabelCacheItemType) -> &mut Self {
        // C++: initCachingStatusFlags() — base flag reset (inlined; sibling method
        // CBackendRepresentativeMemoryCachingFlags::initCachingStatusFlags lives in
        // backend.rs's pending batch). [api]
        self.flags.status_flags = 0;
        self.cache_entry_id = entry_id; // setData(entryID)
        self.signature = signature;
        self.value_linker.clear(); // mValueLinker = nullptr
        self.tag_value_hash.clear(); // mTagValueHash = nullptr
        self.value_count = 0;
        self.cache_item_type = type_;
        self.indi_association_count = 0;
        for ext in self.extension_data.iter_mut() {
            *ext = Id::NONE;
        }
        self
    }
    /// Port of `::getLabelType`.
    pub fn get_label_type(&self) -> LabelCacheItemType { self.cache_item_type }
    /// Port of `::getCacheEntryID` (`return getData();`).
    pub fn get_cache_entry_id(&self) -> Cint64 { self.cache_entry_id }
    /// Port of `::setCacheEntryID` (`setData(entryID)`).
    pub fn set_cache_entry_id(&mut self, entry_id: Cint64) -> &mut Self { self.cache_entry_id = entry_id; self }
    /// Port of `::getSignature`.
    pub fn get_signature(&self) -> Cint64 { self.signature }
    /// Port of `::setSignature`.
    pub fn set_signature(&mut self, signature: Cint64) -> &mut Self { self.signature = signature; self }
    /// Port of `::addCacheValueLinker`
    /// (`mValueCount += linker->getCount(); mValueLinker = linker->append(mValueLinker);`).
    /// KONCLUDE-PORT-NOTE[ownership]: head-front chain prepend; `getCount()` == chain length.
    pub fn add_cache_value_linker(&mut self, linker: &[LabelValueLinkerId]) -> &mut Self {
        self.value_count += linker.len() as Cint64;
        let mut new_chain = linker.to_vec();
        new_chain.append(&mut self.value_linker);
        self.value_linker = new_chain;
        self
    }
    /// Port of `::getCacheValueLinker` (`return mValueLinker;`).
    pub fn get_cache_value_linker(&self) -> &[LabelValueLinkerId] { &self.value_linker }
    /// Port of `::getTagCacheValueHash(create)`.
    /// KONCLUDE-PORT-NOTE[memory-pool]: C++ lazily allocates the hash when `create`;
    /// the port's inline `tag_value_hash` is always present, so `create` is inert.
    pub fn get_tag_cache_value_hash(&mut self, _create: bool) -> &mut HashMap<Cint64, LabelValueLinkerId> {
        &mut self.tag_value_hash
    }
    /// Port of `::setTagCacheValueHash` (`mTagValueHash = hash;`).
    pub fn set_tag_cache_value_hash(&mut self, hash: HashMap<Cint64, LabelValueLinkerId>) -> &mut Self {
        self.tag_value_hash = hash;
        self
    }
    /// Port of `::getCacheValueCount`.
    pub fn get_cache_value_count(&self) -> Cint64 { self.value_count }
    /// Port of `::hasCachedTagValue` (`if (mTagValueHash) return mTagValueHash->contains(tag); return false;`).
    pub fn has_cached_tag_value(&self, tag: Cint64) -> bool { self.tag_value_hash.contains_key(&tag) }
    /// Port of `::getExtensionData` (`return mExtensionData[extensionType];`).
    pub fn get_extension_data(&self, extension_type: Cint64) -> LabelCacheItemExtensionDataId {
        self.extension_data[extension_type as usize]
    }
    /// Port of `::setExtensionData` (`mExtensionData[extensionType] = extensionData;`).
    pub fn set_extension_data(&mut self, extension_type: Cint64, extension_data: LabelCacheItemExtensionDataId) -> &mut Self {
        self.extension_data[extension_type as usize] = extension_data;
        self
    }
    /// Port of `::incIndividualAssociationCount`.
    pub fn inc_individual_association_count(&mut self, count: Cint64) -> &mut Self { self.indi_association_count += count; self }
    /// Port of `::decIndividualAssociationCount`.
    pub fn dec_individual_association_count(&mut self, count: Cint64) -> &mut Self { self.indi_association_count -= count; self }
    /// Port of `::getIndividualAssociationCount`.
    pub fn get_individual_association_count(&self) -> Cint64 { self.indi_association_count }
}

/// Port of `CBackendRepresentativeMemoryCardinalityCacheItem` (`: CLinkerBase<cint64,...>`).
#[derive(Debug, Clone)]
pub struct CardinalityCacheItem {
    /// the `CLinkerBase<cint64>` payload (`getCacheEntryID`).
    pub cache_entry_id: Cint64,
    /// `CBackendRepresentativeMemoryCacheContext* mContext`.  [ownership] → opaque.
    pub context: Cint64,
    /// `cint64 mSignature`.
    pub signature: Cint64,
    /// `CCACHINGHASH<cint64, CBackendRepresentativeMemoryCardinalityValueLinker*>* mTagCardValueHash`.
    pub tag_card_value_hash: HashMap<Cint64, CardinalityValueLinkerId>,
    /// `CBackendRepresentativeMemoryCardinalityValueLinker* mCardinalityValueLinker` (chain).
    pub cardinality_value_linker: Vec<CardinalityValueLinkerId>,
    /// `cint64 mCardinalityValueCount`.
    pub cardinality_value_count: Cint64,
}

impl Default for CardinalityCacheItem {
    fn default() -> Self {
        CardinalityCacheItem {
            cache_entry_id: 0,
            context: INVALID,
            signature: 0,
            tag_card_value_hash: HashMap::new(),
            cardinality_value_linker: Vec::new(),
            cardinality_value_count: 0,
        }
    }
}

impl CardinalityCacheItem {
    /// Port of `CBackendRepresentativeMemoryCardinalityCacheItem::CBackendRepresentativeMemoryCardinalityCacheItem(context)`.
    pub fn new(context: Cint64) -> Self {
        CardinalityCacheItem { context, ..Default::default() }
    }

    /// Port of `::initCacheEntry`.
    pub fn init_cache_entry(&mut self, signature: Cint64, entry_id: Cint64) -> &mut Self {
        self.cache_entry_id = entry_id; // setData(entryID)
        self.signature = signature;
        self.cardinality_value_linker.clear(); // mCardinalityValueLinker = nullptr
        self.tag_card_value_hash.clear(); // mTagCardValueHash = nullptr
        self.cardinality_value_count = 0;
        self
    }
    /// Port of `::getCacheEntryID` (`return getData();`).
    pub fn get_cache_entry_id(&self) -> Cint64 { self.cache_entry_id }
    /// Port of `::setCacheEntryID` (`setData(entryID)`).
    pub fn set_cache_entry_id(&mut self, entry_id: Cint64) -> &mut Self { self.cache_entry_id = entry_id; self }
    /// Port of `::getSignature`.
    pub fn get_signature(&self) -> Cint64 { self.signature }
    /// Port of `::setSignature`.
    pub fn set_signature(&mut self, signature: Cint64) -> &mut Self { self.signature = signature; self }
    /// Port of `::addCardinalityCacheValueLinker`
    /// (`mCardinalityValueCount += linker->getCount(); mCardinalityValueLinker = linker->append(mCardinalityValueLinker);`).
    pub fn add_cardinality_cache_value_linker(&mut self, linker: &[CardinalityValueLinkerId]) -> &mut Self {
        self.cardinality_value_count += linker.len() as Cint64;
        let mut new_chain = linker.to_vec();
        new_chain.append(&mut self.cardinality_value_linker);
        self.cardinality_value_linker = new_chain;
        self
    }
    /// Port of `::getCardinalityCacheValueLinker`.
    pub fn get_cardinality_cache_value_linker(&self) -> &[CardinalityValueLinkerId] { &self.cardinality_value_linker }
    /// Port of `::getTagCardinalityCacheValueHash(create)` (inline map; `create` inert, [memory-pool]).
    pub fn get_tag_cardinality_cache_value_hash(&mut self, _create: bool) -> &mut HashMap<Cint64, CardinalityValueLinkerId> {
        &mut self.tag_card_value_hash
    }
    /// Port of `::setTagCardinalityCacheValueHash`.
    pub fn set_tag_cardinality_cache_value_hash(&mut self, hash: HashMap<Cint64, CardinalityValueLinkerId>) -> &mut Self {
        self.tag_card_value_hash = hash;
        self
    }
    /// Port of `::getCardinalityCacheValueCount`.
    pub fn get_cardinality_cache_value_count(&self) -> Cint64 { self.cardinality_value_count }
}

// ===========================================================================
// Label-cache-item extension-data family → ONE tagged enum
//   (base + cardinality / association-map / neighbour-array-index / tag-resolving).
// ===========================================================================

/// Port of `CBackendRepresentativeMemoryLabelCacheItemCardinalityData` (the
/// per-role cardinality counters held in the cardinality extension hash).
#[derive(Debug, Default, Clone)]
pub struct LabelCacheItemCardinalityData {
    /// `QAtomicInteger<qint64> mExistentialMaxUsedCardinality`.  [threading] → opaque.
    pub existential_max_used_cardinality: Cint64,
    /// `QAtomicInteger<qint64> mMinimumRestrictingCardinality`.  [threading] → opaque.
    pub minimum_restricting_cardinality: Cint64,
}

impl LabelCacheItemCardinalityData {
    pub fn new() -> Self { Self::default() }

    /// Port of `CBackendRepresentativeMemoryLabelCacheItemCardinalityData::initCardinalityData`
    /// (`mExistentialMaxUsedCardinality.store(...); mMinimumRestrictingCardinality.store(...);`).
    pub fn init_cardinality_data(&mut self, existential_max_used_cardinality: Cint64, minimum_restricting_cardinality: Cint64) -> &mut Self {
        self.existential_max_used_cardinality = existential_max_used_cardinality;
        self.minimum_restricting_cardinality = minimum_restricting_cardinality;
        self
    }
    /// Port of `::getExistentialMaxUsedCardinality`.
    pub fn get_existential_max_used_cardinality(&self) -> Cint64 { self.existential_max_used_cardinality }
    /// Port of `::updateExistentialMaxUsedCardinality`.
    /// KONCLUDE-PORT-NOTE[threading]: the C++ CAS loop (`testAndSetOrdered`) reduces to a
    /// monotone max under the single-thread staging.
    pub fn update_existential_max_used_cardinality(&mut self, existential_max_used_cardinality: Cint64) -> &mut Self {
        if self.existential_max_used_cardinality < existential_max_used_cardinality {
            self.existential_max_used_cardinality = existential_max_used_cardinality;
        }
        self
    }
    /// Port of `::getMinimumRestrictingCardinality`.
    pub fn get_minimum_restricting_cardinality(&self) -> Cint64 { self.minimum_restricting_cardinality }
    /// Port of `::updateMinimumRestrictingCardinality` ([threading] CAS → monotone max).
    pub fn update_minimum_restricting_cardinality(&mut self, minimum_restricting_cardinality: Cint64) -> &mut Self {
        if self.minimum_restricting_cardinality < minimum_restricting_cardinality {
            self.minimum_restricting_cardinality = minimum_restricting_cardinality;
        }
        self
    }
}

/// Port of `CBackendRepresentativeMemoryLabelCacheItemTagLabelResolvingDataLinker`
/// (`: CLinkerBase<CBackendRepresentativeMemoryLabelCacheItem*,...>`).
#[derive(Debug, Clone)]
pub struct LabelCacheItemTagLabelResolvingDataLinker {
    /// the `CLinkerBase` payload — the resolved label item.
    pub label_item: LabelCacheItemId,
    /// `cint64 mIndex`.
    pub index: Cint64,
    /// `bool mDeterministic`.
    pub deterministic: bool,
}
impl Default for LabelCacheItemTagLabelResolvingDataLinker {
    fn default() -> Self {
        LabelCacheItemTagLabelResolvingDataLinker { label_item: Id::NONE, index: 0, deterministic: false }
    }
}

impl LabelCacheItemTagLabelResolvingDataLinker {
    pub fn new() -> Self { Self::default() }

    /// Port of `::initTagLabelResolvingData`
    /// (`setData(labelCacheItem); mIndex = index; mDeterministic = deterministic;`).
    pub fn init_tag_label_resolving_data(&mut self, label_cache_item: LabelCacheItemId, index: Cint64, deterministic: bool) -> &mut Self {
        self.label_item = label_cache_item; // the CLinkerBase payload.
        self.index = index;
        self.deterministic = deterministic;
        self
    }
    /// Port of `::getLabelCacheItem` (`return getData();`).
    pub fn get_label_cache_item(&self) -> LabelCacheItemId { self.label_item }
    /// Port of `::getIndex`.
    pub fn get_index(&self) -> Cint64 { self.index }
    /// Port of `::isDeterministic`.
    pub fn is_deterministic(&self) -> bool { self.deterministic }
}

/// Port of the `CBackendRepresentativeMemoryLabelCacheItemExtensionData` hierarchy
/// (base + the 4 derived extension-data classes), folded into one tagged record
/// per the PORT.md record-family→enum rule. Each variant carries its derived
/// fields; the shared base (`mContext` + `mCacheItemExtensionType`) is implied by
/// the variant tag.
///
/// KONCLUDE-PORT-NOTE[ownership]: the base back-pointer `CContext* mContext` and
/// the `QMap<cint64,DummyValue>` association maps are kept terse: maps → `Vec<Cint64>`
/// of keys (the `DummyValue` value is the C++ value-less set placeholder).
#[derive(Debug, Clone)]
pub enum LabelCacheItemExtensionData {
    /// `CBackendRepresentativeMemoryLabelCacheItemExtensionData` (base only).
    Base { context: Cint64 },
    /// `CBackendRepresentativeMemoryLabelCacheItemIndividualAssociationMapExtensionData`.
    IndividualAssociationMap {
        context: Cint64,
        /// `QMap<cint64, DummyValue> mBaseIndiAssoMap` (key set; ordered).
        base_indi_asso_map: Vec<Cint64>,
        /// `QMap<cint64, DummyValue> mSameIndiMergedAssoMap`.
        same_indi_merged_asso_map: Vec<Cint64>,
    },
    /// `CBackendRepresentativeMemoryLabelCacheItemIndividualRoleSetNeighbourArrayIndexExtensionData`.
    NeighbourArrayIndex {
        context: Cint64,
        /// `CBackendRepresentativeMemoryLabelCacheItem* mCombinedNeighbourRoleSetLabel`.
        combined_neighbour_role_set_label: LabelCacheItemId,
        /// `cint64 mArraySize`.
        array_size: Cint64,
        /// `CBackendRepresentativeMemoryLabelCacheItem** mIndexNeighbourRoleSetLabelArray`.
        index_neighbour_role_set_label_array: Vec<LabelCacheItemId>,
        /// `CCACHINGHASH<CBackendRepresentativeMemoryLabelCacheItem*, cint64>* mNeighbourRoleSetLabelIndexHash`.
        neighbour_role_set_label_index_hash: HashMap<LabelCacheItemId, Cint64>,
    },
    /// `CBackendRepresentativeMemoryLabelCacheItemTagLabelResolvingExtensionData`.
    TagLabelResolving {
        context: Cint64,
        /// `CCACHINGHASH<cint64, ...TagLabelResolvingDataLinker*>* mTagLabelResolvingDataLinkerHash`.
        tag_label_resolving_data_linker_hash: HashMap<Cint64, TagLabelResolvingDataLinkerId>,
    },
    /// `CBackendRepresentativeMemoryLabelCacheItemCardinalityExtensionData`.
    Cardinality {
        context: Cint64,
        /// `CCACHINGHASH<cint64, CBackendRepresentativeMemoryLabelCacheItemCardinalityData*>* mRoleCardinalityDataHash`.
        role_cardinality_data_hash: HashMap<Cint64, LabelCacheItemCardinalityData>,
    },
}

impl Default for LabelCacheItemExtensionData {
    fn default() -> Self { LabelCacheItemExtensionData::Base { context: INVALID } }
}

impl LabelCacheItemExtensionData {
    // ===== base =====

    /// Port of `CBackendRepresentativeMemoryLabelCacheItemExtensionData::getExtensionType`
    /// (`return mCacheItemExtensionType;`). The variant tag IS the extension type.
    /// KONCLUDE-PORT-NOTE[overload]: `CARDINALITY_HASH` and `TAG_RESOLVING_HASH` share index 2
    /// in C++ (never on the same label type), so both fold to `TagResolvingHash`.
    pub fn get_extension_type(&self) -> LabelCacheItemExtensionType {
        match self {
            LabelCacheItemExtensionData::IndividualAssociationMap { .. } => LabelCacheItemExtensionType::IndividualAssociationMap,
            LabelCacheItemExtensionData::NeighbourArrayIndex { .. } => LabelCacheItemExtensionType::IndividualNeighbourArrayIndex,
            LabelCacheItemExtensionData::TagLabelResolving { .. } => LabelCacheItemExtensionType::TagResolvingHash,
            LabelCacheItemExtensionData::Cardinality { .. } => LabelCacheItemExtensionType::TagResolvingHash,
            LabelCacheItemExtensionData::Base { .. } => LabelCacheItemExtensionType::IndividualAssociationMap,
        }
    }

    // ===== CBackendRepresentativeMemoryLabelCacheItemIndividualAssociationMapExtensionData =====

    /// Port of `::addIndividualIdAssociation(indiId, sameIndividualMerged)`
    /// (`QMap::insert(indiId, DummyValue())` into the base / same-merged map).
    /// KONCLUDE-PORT-NOTE[ownership]: the ordered `QMap` key set → sorted-deduped `Vec<Cint64>`.
    pub fn add_individual_id_association(&mut self, indi_id: Cint64, same_individual_merged: bool) -> &mut Self {
        if let LabelCacheItemExtensionData::IndividualAssociationMap { base_indi_asso_map, same_indi_merged_asso_map, .. } = self {
            let map = if !same_individual_merged { base_indi_asso_map } else { same_indi_merged_asso_map };
            if let Err(pos) = map.binary_search(&indi_id) {
                map.insert(pos, indi_id);
            }
        }
        self
    }
    /// Port of `::removeIndividualIdAssociation(indiId, sameIndividualMerged)` (`QMap::remove`).
    pub fn remove_individual_id_association(&mut self, indi_id: Cint64, same_individual_merged: bool) -> &mut Self {
        if let LabelCacheItemExtensionData::IndividualAssociationMap { base_indi_asso_map, same_indi_merged_asso_map, .. } = self {
            let map = if !same_individual_merged { base_indi_asso_map } else { same_indi_merged_asso_map };
            if let Ok(pos) = map.binary_search(&indi_id) {
                map.remove(pos);
            }
        }
        self
    }
    /// Port of `::addIndividualIdAssociation(indiAssocData)`
    /// (`addIndividualIdAssociation(indiAssocData->getAssociatedIndividualId(), indiAssocData->hasRepresentativeSameIndividualMerging())`).
    /// KONCLUDE-PORT-NOTE[ownership]: C++ takes a pointer; the port takes the sibling by ref.
    pub fn add_individual_id_association_data(&mut self, indi_assoc_data: &IndividualAssociationData) -> &mut Self {
        self.add_individual_id_association(indi_assoc_data.get_associated_individual_id(), indi_assoc_data.has_representative_same_individual_merging())
    }
    /// Port of `::removeIndividualIdAssociation(indiAssocData)`.
    pub fn remove_individual_id_association_data(&mut self, indi_assoc_data: &IndividualAssociationData) -> &mut Self {
        self.remove_individual_id_association(indi_assoc_data.get_associated_individual_id(), indi_assoc_data.has_representative_same_individual_merging())
    }
    /// Port of `::getIndividualIdAssociationCount` (`mBaseIndiAssoMap.size() + mSameIndiMergedAssoMap.size()`).
    pub fn get_individual_id_association_count(&self) -> Cint64 {
        if let LabelCacheItemExtensionData::IndividualAssociationMap { base_indi_asso_map, same_indi_merged_asso_map, .. } = self {
            (base_indi_asso_map.len() + same_indi_merged_asso_map.len()) as Cint64
        } else {
            0
        }
    }
    /// Port of `::visitIndividualIdAssociationsAscending` — ascending merge of the two sorted key sets.
    /// KONCLUDE-PORT-NOTE[api]: `function<bool(...)>` → `&mut dyn FnMut`; the C++ `continueVisiting`
    /// is computed but never used to break (faithfully reproduced — visiting is unconditional).
    /// The `if (visitSameMergedIndividuals) itMerged = itMergedEnd;` line is a verbatim C++ quirk.
    pub fn visit_individual_id_associations_ascending(&self, visit_func: &mut dyn FnMut(Cint64, bool) -> bool, visit_base_individuals: bool, visit_same_merged_individuals: bool) -> bool {
        let mut visited = false;
        let mut continue_visiting = true;
        if let LabelCacheItemExtensionData::IndividualAssociationMap { base_indi_asso_map: base, same_indi_merged_asso_map: same, .. } = self {
            let base_end = base.len();
            let same_end = same.len();
            let mut bi = 0usize;
            let mut mi = 0usize;
            if !visit_base_individuals {
                bi = base_end;
            }
            if visit_same_merged_individuals {
                mi = same_end; // verbatim C++ quirk (sets to end when the flag is set).
            }
            while bi != base_end || mi != same_end {
                let next_indi_id;
                let mut merged_indi = false;
                if bi == base_end {
                    next_indi_id = same[mi];
                    mi += 1;
                    merged_indi = true;
                } else if mi == same_end {
                    next_indi_id = base[bi];
                    bi += 1;
                } else if base[bi] < same[mi] {
                    next_indi_id = base[bi];
                    bi += 1;
                } else {
                    next_indi_id = same[mi];
                    mi += 1;
                    merged_indi = true;
                }
                continue_visiting = visit_func(next_indi_id, merged_indi);
                visited = true;
            }
        }
        let _ = continue_visiting;
        visited
    }
    /// Port of `::visitIndividualIdAssociationsDescending` — descending merge.
    /// KONCLUDE-PORT-NOTE[unclear]: the C++ unconditionally `toBack()`s both reverse iterators, so
    /// the `visitBaseIndividuals` / `visitSameMergedIndividuals` flags have NO effect here (faithfully
    /// reproduced — both maps are always visited in full).
    pub fn visit_individual_id_associations_descending(&self, visit_func: &mut dyn FnMut(Cint64, bool) -> bool, _visit_base_individuals: bool, _visit_same_merged_individuals: bool) -> bool {
        let mut visited = false;
        let mut continue_visiting = true;
        if let LabelCacheItemExtensionData::IndividualAssociationMap { base_indi_asso_map: base, same_indi_merged_asso_map: same, .. } = self {
            let mut bi = base.len(); // hasPrevious() == bi > 0; previous() == base[bi-1].
            let mut mi = same.len();
            while bi > 0 || mi > 0 {
                let next_indi_id;
                let mut merged_indi = false;
                if bi == 0 {
                    mi -= 1;
                    next_indi_id = same[mi];
                    merged_indi = true;
                } else if mi == 0 {
                    bi -= 1;
                    next_indi_id = base[bi];
                } else if base[bi - 1] < same[mi - 1] {
                    mi -= 1;
                    next_indi_id = same[mi];
                    merged_indi = true;
                } else {
                    bi -= 1;
                    next_indi_id = base[bi];
                }
                continue_visiting = visit_func(next_indi_id, merged_indi);
                visited = true;
            }
        }
        let _ = continue_visiting;
        visited
    }
    /// Port of `::visitIndividualIdAssociations(visitFunc, ascending, ...)`.
    pub fn visit_individual_id_associations(&self, visit_func: &mut dyn FnMut(Cint64, bool) -> bool, ascending: bool, visit_base_individuals: bool, visit_same_merged_individuals: bool) -> bool {
        if ascending {
            self.visit_individual_id_associations_ascending(visit_func, visit_base_individuals, visit_same_merged_individuals)
        } else {
            self.visit_individual_id_associations_descending(visit_func, visit_base_individuals, visit_same_merged_individuals)
        }
    }
    /// Port of `::getIterator(ascending, ...)` / `::getIterator(cursorId, moveOverCursor, ascending, ...)`.
    /// KONCLUDE-PORT-NOTE[api]: the C++ builds a `...MapIterator` from `QMap::const_iterator`
    /// begin/end (and `upperBound`/`lowerBound` cursors). That iterator class carries no ported
    /// behaviour yet, so the cursor→position construction is deferred and a default iterator is
    /// returned. W6-DEFER[api].
    pub fn get_iterator(&self, ascending: bool, _visit_base_individuals: bool, _visit_same_merged_individuals: bool) -> LabelCacheItemIndividualAssociationMapIterator {
        let mut it = LabelCacheItemIndividualAssociationMapIterator::default();
        it.iterate_ascending = ascending;
        it
    }
    /// Port of `::getIterator(cursorId, ...)` (cursor variant; see note above). W6-DEFER[api].
    pub fn get_iterator_from_cursor(&self, _cursor_id: Cint64, _move_over_cursor: bool, ascending: bool, _visit_base_individuals: bool, _visit_same_merged_individuals: bool) -> LabelCacheItemIndividualAssociationMapIterator {
        let mut it = LabelCacheItemIndividualAssociationMapIterator::default();
        it.iterate_ascending = ascending;
        it
    }

    // ===== CBackendRepresentativeMemoryLabelCacheItemIndividualRoleSetNeighbourArrayIndexExtensionData =====

    /// Port of `::initNeighbourArrayIndexData(combinedNeighbourRoleSetLabel)`.
    pub fn init_neighbour_array_index_data(&mut self, combined_neighbour_role_set_label: LabelCacheItemId) -> &mut Self {
        if let LabelCacheItemExtensionData::NeighbourArrayIndex { combined_neighbour_role_set_label: c, .. } = self {
            *c = combined_neighbour_role_set_label;
            // W6-DEFER[api]: `mArraySize = combined->getCacheValueCount()` plus the per-index fill of
            // `mIndexNeighbourRoleSetLabelArray` / `mNeighbourRoleSetLabelIndexHash` by walking the
            // combined label's value-linker chain need the LabelCacheItem / LabelValueLinker arenas
            // (not threaded into this struct). The array/hash build is deferred; control flow preserved.
        }
        self
    }
    /// Port of `::initNeighbourArrayIndexData(neighArrayIndexData)` — C++ body is `return this;` (no-op).
    pub fn init_neighbour_array_index_data_from(&mut self, _neigh_array_index_data: LabelCacheItemExtensionDataId) -> &mut Self {
        self
    }
    /// Port of `::getCombinedNeighbourRoleSetLabel`.
    pub fn get_combined_neighbour_role_set_label(&self) -> LabelCacheItemId {
        if let LabelCacheItemExtensionData::NeighbourArrayIndex { combined_neighbour_role_set_label, .. } = self {
            *combined_neighbour_role_set_label
        } else {
            Id::NONE
        }
    }
    /// Port of `::getArraySize`.
    pub fn get_array_size(&self) -> Cint64 {
        if let LabelCacheItemExtensionData::NeighbourArrayIndex { array_size, .. } = self {
            *array_size
        } else {
            0
        }
    }
    /// Port of `::getNeighbourRoleSetLabel(index)`
    /// (`if (index >= 0 && index < mArraySize) return mIndexNeighbourRoleSetLabelArray[index]; return nullptr;`).
    pub fn get_neighbour_role_set_label(&self, index: Cint64) -> LabelCacheItemId {
        if let LabelCacheItemExtensionData::NeighbourArrayIndex { array_size, index_neighbour_role_set_label_array, .. } = self {
            if index >= 0 && index < *array_size && (index as usize) < index_neighbour_role_set_label_array.len() {
                return index_neighbour_role_set_label_array[index as usize];
            }
        }
        Id::NONE
    }
    /// Port of `::getIndex(neighbourRoleSetLabel)` (`mNeighbourRoleSetLabelIndexHash->value(label, -1)`).
    pub fn get_index(&self, neighbour_role_set_label: LabelCacheItemId) -> Cint64 {
        if let LabelCacheItemExtensionData::NeighbourArrayIndex { neighbour_role_set_label_index_hash, .. } = self {
            *neighbour_role_set_label_index_hash.get(&neighbour_role_set_label).unwrap_or(&-1)
        } else {
            -1
        }
    }

    // ===== CBackendRepresentativeMemoryLabelCacheItemTagLabelResolvingExtensionData =====

    /// Port of `::initTagLabelResolvingExtensionData` (C++ allocates the hash; the inline map is
    /// always present, so this is a no-op, [memory-pool]).
    pub fn init_tag_label_resolving_extension_data(&mut self) -> &mut Self { self }
    /// Port of `::getTagLabelResolvingDataLinker(tag)` (`mTagLabelResolvingDataLinkerHash->value(tag)`).
    pub fn get_tag_label_resolving_data_linker(&self, tag: Cint64) -> TagLabelResolvingDataLinkerId {
        if let LabelCacheItemExtensionData::TagLabelResolving { tag_label_resolving_data_linker_hash, .. } = self {
            tag_label_resolving_data_linker_hash.get(&tag).copied().unwrap_or(Id::NONE)
        } else {
            Id::NONE
        }
    }
    /// Port of `::appendTagLabelResolvingDataLinker(tag, linker)`
    /// (`exLinker = linker->append(exLinker);` where `exLinker = (*hash)[tag]`).
    pub fn append_tag_label_resolving_data_linker(&mut self, tag: Cint64, linker: TagLabelResolvingDataLinkerId) -> &mut Self {
        if let LabelCacheItemExtensionData::TagLabelResolving { tag_label_resolving_data_linker_hash, .. } = self {
            // `linker` becomes the new chain head; its tail re-links to the prior head in the linker
            // arena (W6-DEFER[api]: the arena next-pointer is not threaded here — only the head id is stored).
            tag_label_resolving_data_linker_hash.insert(tag, linker);
        }
        self
    }

    // ===== CBackendRepresentativeMemoryLabelCacheItemCardinalityExtensionData =====

    /// Port of `::initCardinalityExtensionData` (inline map; no-op, [memory-pool]).
    pub fn init_cardinality_extension_data(&mut self) -> &mut Self { self }
    /// Port of `::getRoleCardinalityData(roleTag)` (`mRoleCardinalityDataHash->value(roleTag)`).
    pub fn get_role_cardinality_data(&self, role_tag: Cint64) -> Option<&LabelCacheItemCardinalityData> {
        if let LabelCacheItemExtensionData::Cardinality { role_cardinality_data_hash, .. } = self {
            role_cardinality_data_hash.get(&role_tag)
        } else {
            None
        }
    }
    /// Port of `::setRoleCardinalityData(roleTag, cardinalityData)` (`mRoleCardinalityDataHash->insert(...)`).
    pub fn set_role_cardinality_data(&mut self, role_tag: Cint64, cardinality_data: LabelCacheItemCardinalityData) -> &mut Self {
        if let LabelCacheItemExtensionData::Cardinality { role_cardinality_data_hash, .. } = self {
            role_cardinality_data_hash.insert(role_tag, cardinality_data);
        }
        self
    }
    /// Port of `::getRoleCardinalityDataHash` (`return mRoleCardinalityDataHash;`).
    pub fn get_role_cardinality_data_hash(&mut self) -> Option<&mut HashMap<Cint64, LabelCacheItemCardinalityData>> {
        if let LabelCacheItemExtensionData::Cardinality { role_cardinality_data_hash, .. } = self {
            Some(role_cardinality_data_hash)
        } else {
            None
        }
    }
}

/// Port of `CBackendRepresentativeMemoryLabelCacheItemIndividualAssociationMapIterator`.
/// A cursor over the association-map extension data (ascending/descending merge of
/// the base + same-merged maps). Held transiently; the `QMap::const_iterator`
/// cursors become plain index positions.
#[derive(Debug, Default, Clone)]
pub struct LabelCacheItemIndividualAssociationMapIterator {
    /// `bool mIterateAscending`.
    pub iterate_ascending: bool,
    /// `bool mHasCurrentIndiId`.
    pub has_current_indi_id: bool,
    /// `bool mCurrentIndiSameMerged`.
    pub current_indi_same_merged: bool,
    /// `cint64 mCurrentIndiId`.
    pub current_indi_id: Cint64,
    /// the 6 `QMap<cint64,DummyValue>::const_iterator` cursors → index positions
    /// `[base_it, base_begin, base_end, same_it, same_begin, same_end]`.
    /// KONCLUDE-PORT-NOTE[api]: STL/Qt iterators → `Cint64` positions into the
    /// extension's ordered key vectors.
    pub map_iterator_positions: [Cint64; 6],
}

// ===========================================================================
// Role-set-neighbour family.
// ===========================================================================

/// Port of `CBackendRepresentativeMemoryCacheIndividualNeighbourRoleSetHash`.
#[derive(Debug, Default, Clone)]
pub struct IndividualNeighbourRoleSetHash {
    /// `CBackendRepresentativeMemoryCacheContext* mContext`.  [ownership] → opaque.
    pub context: Cint64,
    /// `CCACHINGHASH<cint64, CBackendRepresentativeMemoryLabelCacheItem*>* mNeighbourRoleSetLabelHash`.
    pub neighbour_role_set_label_hash: HashMap<Cint64, LabelCacheItemId>,
    /// `CCACHINGHASH<cint64, CBackendRepresentativeMemoryLabelCacheItem*>* mPrevNeighbourRoleSetLabelHash`.
    pub prev_neighbour_role_set_label_hash: HashMap<Cint64, LabelCacheItemId>,
}
impl IndividualNeighbourRoleSetHash {
    pub fn new() -> Self { Self::default() }

    /// Port of `::initNeighbourRoleSetHash(neighbourRoleSetHash, detach)` — the prev-hash COW logic.
    /// KONCLUDE-PORT-NOTE[ownership]: C++ aliases the source's prev-hash by bare pointer; the
    /// inline-map port COPIES instead, and models `mPrevNeighbourRoleSetLabelHash == nullptr`
    /// as an EMPTY prev map. Lookups / counts are identical; only the sharing is by-copy.
    pub fn init_neighbour_role_set_hash(&mut self, neighbour_role_set_hash: &IndividualNeighbourRoleSetHash, detach: bool) -> &mut Self {
        let src_has_prev = !neighbour_role_set_hash.prev_neighbour_role_set_label_hash.is_empty();
        if detach {
            if src_has_prev {
                self.neighbour_role_set_label_hash = neighbour_role_set_hash.prev_neighbour_role_set_label_hash.clone();
                for (k, v) in neighbour_role_set_hash.neighbour_role_set_label_hash.iter() {
                    self.neighbour_role_set_label_hash.insert(*k, *v);
                }
            } else {
                self.neighbour_role_set_label_hash = neighbour_role_set_hash.neighbour_role_set_label_hash.clone();
            }
            self.prev_neighbour_role_set_label_hash.clear();
        } else if !src_has_prev && neighbour_role_set_hash.neighbour_role_set_label_hash.len() <= 20 {
            self.neighbour_role_set_label_hash = neighbour_role_set_hash.neighbour_role_set_label_hash.clone();
            self.prev_neighbour_role_set_label_hash.clear();
        } else if !src_has_prev {
            // size > 20: keep the source's main hash as prev.
            self.prev_neighbour_role_set_label_hash = neighbour_role_set_hash.neighbour_role_set_label_hash.clone();
        } else if neighbour_role_set_hash.neighbour_role_set_label_hash.len() > neighbour_role_set_hash.prev_neighbour_role_set_label_hash.len() {
            self.neighbour_role_set_label_hash = neighbour_role_set_hash.prev_neighbour_role_set_label_hash.clone();
            for (k, v) in neighbour_role_set_hash.neighbour_role_set_label_hash.iter() {
                self.neighbour_role_set_label_hash.insert(*k, *v);
            }
            self.prev_neighbour_role_set_label_hash.clear();
        } else {
            self.neighbour_role_set_label_hash = neighbour_role_set_hash.neighbour_role_set_label_hash.clone();
            self.prev_neighbour_role_set_label_hash = neighbour_role_set_hash.prev_neighbour_role_set_label_hash.clone();
        }
        self
    }
    /// Port of `::getNeighbourCount` (`main.size() (+ prev.size() if prev)`).
    pub fn get_neighbour_count(&self) -> Cint64 {
        let mut count = self.neighbour_role_set_label_hash.len() as Cint64;
        if !self.prev_neighbour_role_set_label_hash.is_empty() {
            count += self.prev_neighbour_role_set_label_hash.len() as Cint64;
        }
        count
    }
    /// Port of `::getNeighbourRoleSetLabel(neighbourIndiId)` (main, falling back to prev).
    pub fn get_neighbour_role_set_label(&self, neighbour_indi_id: Cint64) -> LabelCacheItemId {
        let mut item = self.neighbour_role_set_label_hash.get(&neighbour_indi_id).copied().unwrap_or(Id::NONE);
        if item.is_none() && !self.prev_neighbour_role_set_label_hash.is_empty() {
            item = self.prev_neighbour_role_set_label_hash.get(&neighbour_indi_id).copied().unwrap_or(Id::NONE);
        }
        item
    }
    /// Port of `::setNeighbourRoleSetLabel` (`mNeighbourRoleSetLabelHash->insert(...)`).
    pub fn set_neighbour_role_set_label(&mut self, neighbour_indi_id: Cint64, neighbour_role_set_label: LabelCacheItemId) -> &mut Self {
        self.neighbour_role_set_label_hash.insert(neighbour_indi_id, neighbour_role_set_label);
        self
    }
}

/// Port of `CBackendRepresentativeMemoryCacheIndividualRoleSetNeighbourArray`.
#[derive(Debug, Clone)]
pub struct IndividualRoleSetNeighbourArray {
    /// `CBackendRepresentativeMemoryCacheContext* mContext`.  [ownership] → opaque.
    pub context: Cint64,
    /// `CBackendRepresentativeMemoryLabelCacheItemIndividualRoleSetNeighbourArrayIndexExtensionData* mIndexData`.
    pub index_data: LabelCacheItemExtensionDataId,
    /// `CBackendRepresentativeMemoryCacheIndividualRoleSetNeighbourData* mDataArray` (array head).
    pub data_array: IndividualRoleSetNeighbourDataId,
}
impl Default for IndividualRoleSetNeighbourArray {
    fn default() -> Self {
        IndividualRoleSetNeighbourArray { context: INVALID, index_data: Id::NONE, data_array: Id::NONE }
    }
}
impl IndividualRoleSetNeighbourArray {
    pub fn new() -> Self { Self::default() }

    /// Port of `::initNeighbourArray(neighArray)`.
    /// KONCLUDE-PORT-NOTE[api]: C++ allocates a NeighbourData array of `mIndexData->getArraySize()`
    /// and copies each element from `neighArray->at(i)`; the data array lives in the cache pool
    /// (arena), not threaded into this struct. The element copy is deferred (W6-DEFER[api]); the
    /// index-data + array head are carried.
    pub fn init_neighbour_array(&mut self, neigh_array: &IndividualRoleSetNeighbourArray) -> &mut Self {
        self.index_data = neigh_array.index_data;
        self.data_array = neigh_array.data_array;
        self
    }
    /// Port of `::initNeighbourArray(indexData)` (allocates the per-index array — pool, W6-DEFER[api]).
    pub fn init_neighbour_array_from_index(&mut self, index_data: LabelCacheItemExtensionDataId) -> &mut Self {
        self.index_data = index_data;
        self
    }
    /// Port of `::at(index)` (`return mDataArray[index];`).
    /// W6-DEFER[api]: needs the pooled NeighbourData array (arena); returns the array head id.
    pub fn at(&self, _index: Cint64) -> IndividualRoleSetNeighbourDataId {
        self.data_array
    }
    /// Port of `::getIndexData`.
    pub fn get_index_data(&self) -> LabelCacheItemExtensionDataId { self.index_data }
}

/// Port of `CBackendRepresentativeMemoryCacheIndividualRoleSetNeighbourData`.
#[derive(Debug, Default, Clone)]
pub struct IndividualRoleSetNeighbourData {
    /// `cint64 mCount`.
    pub count: Cint64,
    /// `CBackendRepresentativeMemoryCacheIndividualRoleSetNeighbourIndividualIdLinker* mIndiIdLinker` (chain).
    pub indi_id_linker: Vec<IndividualRoleSetNeighbourIndividualIdLinkerId>,
}
impl IndividualRoleSetNeighbourData {
    pub fn new() -> Self { Self::default() }

    /// Port of `::visitNeighbourIndividualIds(visitFunc)` — walks `mIndiIdLinker` calling `getIndividualId()`.
    /// W6-DEFER[api]: resolving each `IndividualRoleSetNeighbourIndividualIdLinkerId` → its indi id needs
    /// the linker arena (not threaded here). Faithful stub: no nodes resolvable ⇒ reports unvisited.
    pub fn visit_neighbour_individual_ids(&self, _visit_func: &mut dyn FnMut(Cint64) -> bool) -> bool {
        let _ = &self.indi_id_linker;
        false
    }
    /// Port of `::visitNeighbourIndividualIdsFromCursor(visitFunc, cursor)` (cursor variant). W6-DEFER[api].
    pub fn visit_neighbour_individual_ids_from_cursor(&self, _visit_func: &mut dyn FnMut(Cint64, Cint64) -> bool, _cursor: Cint64) -> bool {
        let _ = &self.indi_id_linker;
        false
    }
    /// Port of `::getIndividualIdLinker`.
    pub fn get_individual_id_linker(&self) -> &[IndividualRoleSetNeighbourIndividualIdLinkerId] { &self.indi_id_linker }
    /// Port of `::setIndividualIdLinker(indiIdLinker, updateCounter)`
    /// (`mIndiIdLinker = indiIdLinker; if (updateCounter) mCount = mIndiIdLinker->getCount();`).
    pub fn set_individual_id_linker(&mut self, indi_id_linker: &[IndividualRoleSetNeighbourIndividualIdLinkerId], update_counter: bool) -> &mut Self {
        self.indi_id_linker = indi_id_linker.to_vec();
        if update_counter {
            self.count = self.indi_id_linker.len() as Cint64;
        }
        self
    }
    /// Port of `::addIndividualIdLinker(indiIdLinker, incCounter)`
    /// (`if (incCounter) mCount += indiIdLinker->getCount(); mIndiIdLinker = indiIdLinker->append(mIndiIdLinker);`).
    pub fn add_individual_id_linker(&mut self, indi_id_linker: &[IndividualRoleSetNeighbourIndividualIdLinkerId], inc_counter: bool) -> &mut Self {
        if inc_counter {
            self.count += indi_id_linker.len() as Cint64;
        }
        let mut new_chain = indi_id_linker.to_vec();
        new_chain.append(&mut self.indi_id_linker);
        self.indi_id_linker = new_chain;
        self
    }
    /// Port of `::getIndividualCount`.
    pub fn get_individual_count(&self) -> Cint64 { self.count }
    /// Port of `::incIndividualCount`.
    pub fn inc_individual_count(&mut self, count: Cint64) -> &mut Self { self.count += count; self }
    /// Port of `::decIndividualCount`.
    pub fn dec_individual_count(&mut self, count: Cint64) -> &mut Self { self.count -= count; self }
}

/// Port of `CBackendRepresentativeMemoryCacheIndividualRoleSetNeighbourIndividualIdLinker`
/// (`: CLinkerBase<cint64,...>`).
#[derive(Debug, Default, Clone)]
pub struct IndividualRoleSetNeighbourIndividualIdLinker {
    /// the `CLinkerBase<cint64>` payload — the neighbour individual id.
    pub indi_id: Cint64,
}
impl IndividualRoleSetNeighbourIndividualIdLinker {
    pub fn new() -> Self { Self::default() }

    /// Port of `::initIndividualIdLinker(indiId, nextLinker)` (`initLinker(indiId, nextLinker)`).
    /// KONCLUDE-PORT-NOTE[ownership]: the `nextLinker` chain pointer is dropped (owner holds the
    /// chain as a head-front `Vec`); only the `cint64` payload survives.
    pub fn init_individual_id_linker(&mut self, indi_id: Cint64) -> &mut Self {
        self.indi_id = indi_id;
        self
    }
    /// Port of `::getIndividualId` (`return getData();`).
    pub fn get_individual_id(&self) -> Cint64 { self.indi_id }
}

// ===========================================================================
// Nominal indirect-connection + assorted linkers.
// ===========================================================================

/// Port of `CBackendRepresentativeMemoryCacheNominalIndividualIndirectConnectionData`.
#[derive(Debug, Default, Clone)]
pub struct NominalIndividualIndirectConnectionData {
    /// `CXLinker<cint64>* mIndirectlyConnectedIndividualIdLinker` (chain → Vec head-front).
    pub indirectly_connected_individual_id_linker: Vec<Cint64>,
    /// `cint64 mLastChangeId`.
    pub last_change_id: Cint64,
}
impl NominalIndividualIndirectConnectionData {
    pub fn new() -> Self { Self::default() }

    /// Port of `::initNominalIndividualIndirectConnectionData(data)`.
    /// KONCLUDE-PORT-NOTE[ownership]: C++ shares the source linker by pointer; the port copies the
    /// owned `Vec<cint64>`.
    pub fn init_nominal_individual_indirect_connection_data(&mut self, data: Option<&NominalIndividualIndirectConnectionData>) -> &mut Self {
        self.indirectly_connected_individual_id_linker.clear(); // nullptr
        self.last_change_id = 0;
        if let Some(data) = data {
            self.indirectly_connected_individual_id_linker = data.indirectly_connected_individual_id_linker.clone();
            self.last_change_id = data.last_change_id;
        }
        self
    }
    /// Port of `::getIndirectlyConnectedIndividualIdLinker`.
    pub fn get_indirectly_connected_individual_id_linker(&self) -> &[Cint64] { &self.indirectly_connected_individual_id_linker }
    /// Port of `::setIndirectlyConnectedIndividualIdLinker`.
    pub fn set_indirectly_connected_individual_id_linker(&mut self, indirectly_connected_individual_id_linker: Vec<Cint64>) -> &mut Self {
        self.indirectly_connected_individual_id_linker = indirectly_connected_individual_id_linker;
        self
    }
    /// Port of `::addIndirectlyConnectedIndividualIdLinker`
    /// (`mLinker = indirectlyConnectedIndividualIdLinker->append(mLinker);` — head-front prepend).
    pub fn add_indirectly_connected_individual_id_linker(&mut self, indirectly_connected_individual_id_linker: &[Cint64]) -> &mut Self {
        let mut new_chain = indirectly_connected_individual_id_linker.to_vec();
        new_chain.append(&mut self.indirectly_connected_individual_id_linker);
        self.indirectly_connected_individual_id_linker = new_chain;
        self
    }
    /// Port of `::getLastChangeId`.
    pub fn get_last_change_id(&self) -> Cint64 { self.last_change_id }
    /// Port of `::setLastChangeId(id)`.
    /// KONCLUDE-PORT-NOTE[unclear]: the C++ body does NOT assign `mLastChangeId` (it only
    /// `return this;`) — faithfully reproduced as a no-op on the field.
    pub fn set_last_change_id(&mut self, _id: Cint64) -> &mut Self { self }
}

/// Port of `CBackendRepresentativeMemoryCacheItemIndividualDataAssociationLinker`
/// (`: CLinkerBase<CBackendRepresentativeMemoryCacheIndividualAssociationData*,...>`).
#[derive(Debug, Clone)]
pub struct ItemIndividualDataAssociationLinker {
    /// the `CLinkerBase` payload — the associated individual data.
    pub association_data: IndividualAssociationDataId,
    /// `bool mAssociationValid`.
    pub association_valid: bool,
}
impl Default for ItemIndividualDataAssociationLinker {
    fn default() -> Self {
        ItemIndividualDataAssociationLinker { association_data: Id::NONE, association_valid: false }
    }
}
impl ItemIndividualDataAssociationLinker {
    pub fn new() -> Self { Self::default() }

    /// Port of `::initIndividualDataAssociationLinker(data)` (`setData(data); mAssociationValid = true;`).
    pub fn init_individual_data_association_linker(&mut self, data: IndividualAssociationDataId) -> &mut Self {
        self.association_data = data; // the CLinkerBase payload.
        self.association_valid = true;
        self
    }
    /// Port of `::getAssociatedIndividualData` (`return getData();`).
    pub fn get_associated_individual_data(&self) -> IndividualAssociationDataId { self.association_data }
    /// Port of `::isAssociationValid`.
    pub fn is_association_valid(&self) -> bool { self.association_valid }
    /// Port of `::invalidateAssociation` (`mAssociationValid = false;`).
    pub fn invalidate_association(&mut self) -> &mut Self { self.association_valid = false; self }
}

/// Port of `CBackendRepresentativeMemoryCacheRoleAssertionLinker` (`: CSortedNegLinker<CRole*>`).
#[derive(Debug, Default, Clone)]
pub struct RoleAssertionLinker {
    /// the `CSortedNegLinker<CRole*>` payload — the role.  [api] cross-family → opaque.
    pub role: Cint64,
    /// `bool mABoxAsserted`.
    pub abox_asserted: bool,
    /// `bool mNominalConnected`.
    pub nominal_connected: bool,
    /// `bool mNondeterministic`.
    pub nondeterministic: bool,
}
impl RoleAssertionLinker {
    pub fn new() -> Self { Self::default() }

    /// Port of `::initRoleAssertionLinker(role, inversed, asserted, connected, nondeterministic)`
    /// (`init(role, inversed); mABoxAsserted = asserted; mNominalConnected = connected; mNondeterministic = nondeterministic;`).
    /// KONCLUDE-PORT-NOTE[api]: the `CSortedNegLinker<CRole*>` base stores the role pointer + its
    /// `inversed`/neg flag; the cross-family `CRole*` is opaque `Cint64` and the `inversed` neg-flag
    /// of the sorted-neg-linker base is not modelled on this struct (dropped, [api]).
    pub fn init_role_assertion_linker(&mut self, role: Cint64, _inversed: bool, asserted: bool, connected: bool, nondeterministic: bool) -> &mut Self {
        self.role = role; // init(role, inversed) — the CSortedNegLinker payload.
        self.abox_asserted = asserted;
        self.nominal_connected = connected;
        self.nondeterministic = nondeterministic;
        self
    }
    /// Port of `::isABoxAsserted`.
    pub fn is_abox_asserted(&self) -> bool { self.abox_asserted }
    /// Port of `::setABoxAsserted`.
    pub fn set_abox_asserted(&mut self, asserted: bool) -> &mut Self { self.abox_asserted = asserted; self }
    /// Port of `::isNominalConnected`.
    pub fn is_nominal_connected(&self) -> bool { self.nominal_connected }
    /// Port of `::setNominalConnected`.
    pub fn set_nominal_connected(&mut self, connected: bool) -> &mut Self { self.nominal_connected = connected; self }
    /// Port of `::isNondeterministic`.
    pub fn is_nondeterministic(&self) -> bool { self.nondeterministic }
    /// Port of `::setNondeterministic`.
    pub fn set_nondeterministic(&mut self, nondeterministic: bool) -> &mut Self { self.nondeterministic = nondeterministic; self }
}

/// Port of `CBackendRepresentativeMemoryCacheOntologyDataRecomputationReferenceLinker`.
#[derive(Debug, Default, Clone)]
pub struct OntologyDataRecomputationReferenceLinker {
    /// `cint64 mOntologyDataUpdateId`.
    pub ontology_data_update_id: Cint64,
    /// `bool mOntologyDataActive`.
    pub ontology_data_active: bool,
    /// `bool mNextOntologyDataAllInactive`.
    pub next_ontology_data_all_inactive: bool,
    /// `QAtomicInteger<cint64> mMinUsedRecomputationId`.  [threading] → opaque.
    pub min_used_recomputation_id: Cint64,
    /// `QAtomicInteger<cint64> mMaxUsedRecomputationId`.  [threading] → opaque.
    pub max_used_recomputation_id: Cint64,
}
impl OntologyDataRecomputationReferenceLinker {
    pub fn new() -> Self { Self::default() }

    /// Port of the ctor `(cint64 ontologyDataUpdateId)`
    /// (`mOntologyDataUpdateId = ...; setData(this); mOntologyDataActive = true; mNextOntologyDataAllInactive = false;`).
    /// KONCLUDE-PORT-NOTE[api]: the skeleton's `new()` takes no id; this `init_*` carries the ctor's
    /// field setup (`setData(this)` self-linker drop per CLinker convention).
    pub fn init_recomputation_reference_linker(&mut self, ontology_data_update_id: Cint64) -> &mut Self {
        self.ontology_data_update_id = ontology_data_update_id;
        self.ontology_data_active = true;
        self.next_ontology_data_all_inactive = false;
        self
    }
    /// Port of `::updateUsedRecomputationId(recomputationId)`.
    /// KONCLUDE-PORT-NOTE[threading]: the two `testAndSetOrdered` CAS loops reduce to a monotone
    /// `qMin` / `qMax` under the single-thread staging.
    pub fn update_used_recomputation_id(&mut self, recomputation_id: Cint64) -> &mut Self {
        self.min_used_recomputation_id = self.min_used_recomputation_id.min(recomputation_id);
        self.max_used_recomputation_id = self.max_used_recomputation_id.max(recomputation_id);
        self
    }
    /// Port of `::getMinUsedRecomputationId`.
    pub fn get_min_used_recomputation_id(&self) -> Cint64 { self.min_used_recomputation_id }
    /// Port of `::getMaxUsedRecomputationId`.
    pub fn get_max_used_recomputation_id(&self) -> Cint64 { self.max_used_recomputation_id }
    /// Port of `::getOntologyDataUpdateId`.
    pub fn get_ontology_data_update_id(&self) -> Cint64 { self.ontology_data_update_id }
    /// Port of `::isOntologyDataActive`.
    pub fn is_ontology_data_active(&self) -> bool { self.ontology_data_active }
    /// Port of `::setOntologyDataInactive`.
    pub fn set_ontology_data_inactive(&mut self) -> &mut Self { self.ontology_data_active = false; self }
    /// Port of `::isNextOntologyDataAllInactive`.
    pub fn is_next_ontology_data_all_inactive(&self) -> bool { self.next_ontology_data_all_inactive }
    /// Port of `::setNextOntologyDataAllInactive`.
    pub fn set_next_ontology_data_all_inactive(&mut self) -> &mut Self { self.next_ontology_data_all_inactive = true; self }
}

// ===========================================================================
// Individual association data + its memory context.
// ===========================================================================

/// Port of `CBackendRepresentativeMemoryCacheIndividualAssociationData`
/// (`: CIndividualBackendCachingData, CBackendRepresentativeMemoryCachingFlags`).
///
/// The per-individual realisation record: its per-type label cache entries,
/// cardinality entry, neighbour role-set hash + array, same-as merging ids,
/// problematic-level + incompletely-marked flags, update/touch ids, and the
/// memory context it is pooled in.
#[derive(Debug, Clone)]
pub struct IndividualAssociationData {
    /// `CIndividualBackendCachingData` base.  [api] cross-family → opaque handle.
    pub caching_data_base: Cint64,
    /// `CBackendRepresentativeMemoryCachingFlags` base.
    pub flags: BackendRepresentativeMemoryCachingFlags,

    /// `CBackendRepresentativeMemoryLabelCacheItem* mLabelCacheEntries[ASSOCIATABLE_TYPE_COUNT]` (15).
    pub label_cache_entries: Vec<LabelCacheItemId>,
    /// `CBackendRepresentativeMemoryCardinalityCacheItem* mCardinalityCacheEntry`.
    pub cardinality_cache_entry: CardinalityCacheItemId,
    /// `CBackendRepresentativeMemoryLabelCacheItem* mDetMergedSameConsideredLabelCacheEntry`.
    pub det_merged_same_considered_label_cache_entry: LabelCacheItemId,

    /// `cint64 mIndiID`.
    pub indi_id: Cint64,
    /// `bool mIncompletelyMarked`.
    pub incompletely_marked: bool,
    /// `bool mIndirectlyConnectedNominalIndividual`.
    pub indirectly_connected_nominal_individual: bool,
    /// `bool mIndirectlyConnectedIndividualIntegration`.
    pub indirectly_connected_individual_integration: bool,

    /// `cint64 mProblematicLevel`.
    pub problematic_level: Cint64,
    /// `bool mProblematicLeveledNeighbour`.
    pub problematic_leveled_neighbour: bool,

    /// `cint64 mAssociationDataUpdateId`.
    pub association_data_update_id: Cint64,
    /// `cint64 mCacheUpdateId`.
    pub cache_update_id: Cint64,
    /// `cint64 mCacheTouchId`.
    pub cache_touch_id: Cint64,
    /// `cint64 mLastIntegratedIndirectlyConnectedIndividualsChangeId`.
    pub last_integrated_indirectly_connected_individuals_change_id: Cint64,

    /// `CBackendRepresentativeMemoryCacheIndividualNeighbourRoleSetHash* mNeighbourRoleSetHash`.
    pub neighbour_role_set_hash: IndividualNeighbourRoleSetHashId,
    /// `CBackendRepresentativeMemoryCacheIndividualRoleSetNeighbourArray* mRoleSetNeighbourArray`.
    pub role_set_neighbour_array: IndividualRoleSetNeighbourArrayId,

    /// `cint64 mRepresentativeSameIndiId`.
    pub representative_same_indi_id: Cint64,
    /// `cint64 mDeterministicSameIndiId`.
    pub deterministic_same_indi_id: Cint64,

    /// `cint64 mLastPropagationCuttingUpdateId`.
    pub last_propagation_cutting_update_id: Cint64,
    /// `CBackendRepresentativeMemoryCacheIndividualAssociationContext* mMemContext`.
    pub mem_context: IndividualAssociationContextId,
    /// `CBackendRepresentativeMemoryCacheIndividualAssociationData* mPrevData = nullptr`.
    pub prev_data: IndividualAssociationDataId,
    /// `CBackendRepresentativeMemoryCacheIndividualRoleSetNeighbourIndividualIdLinker* mPropCutRemovedNeighbourIndiLinker` (chain).
    pub prop_cut_removed_neighbour_indi_linker: Vec<IndividualRoleSetNeighbourIndividualIdLinkerId>,
}

impl Default for IndividualAssociationData {
    fn default() -> Self {
        IndividualAssociationData {
            caching_data_base: INVALID,
            flags: BackendRepresentativeMemoryCachingFlags::new(),
            label_cache_entries: vec![Id::NONE; LABEL_CACHE_ITEM_ASSOCIATABLE_TYPE_COUNT],
            cardinality_cache_entry: Id::NONE,
            det_merged_same_considered_label_cache_entry: Id::NONE,
            indi_id: 0,
            incompletely_marked: false,
            indirectly_connected_nominal_individual: false,
            indirectly_connected_individual_integration: false,
            problematic_level: 0,
            problematic_leveled_neighbour: false,
            association_data_update_id: 0,
            cache_update_id: 0,
            cache_touch_id: 0,
            last_integrated_indirectly_connected_individuals_change_id: 0,
            neighbour_role_set_hash: Id::NONE,
            role_set_neighbour_array: Id::NONE,
            representative_same_indi_id: 0,
            deterministic_same_indi_id: 0,
            last_propagation_cutting_update_id: 0,
            mem_context: Id::NONE,
            prev_data: Id::NONE,
            prop_cut_removed_neighbour_indi_linker: Vec::new(),
        }
    }
}

impl IndividualAssociationData {
    /// Port of `CBackendRepresentativeMemoryCacheIndividualAssociationData::CBackendRepresentativeMemoryCacheIndividualAssociationData`.
    pub fn new() -> Self { Self::default() }

    /// Port of `::initAssociationData(assData, increaseUpdateId)`.
    /// KONCLUDE-PORT-NOTE[ownership]: C++ stores `mPrevData = assData` (the source pointer); the
    /// arena id `ass_data_id` is passed alongside the borrow so the prev link survives. The
    /// `KONCLUDE_CACHE_DEBUGGING` debug fields are omitted (build-flag only).
    pub fn init_association_data(&mut self, ass_data: &IndividualAssociationData, ass_data_id: IndividualAssociationDataId, increase_update_id: bool) -> &mut Self {
        self.flags.status_flags = ass_data.flags.status_flags; // initCachingStatusFlags(assData->getStatusFlags())
        self.indi_id = ass_data.indi_id;
        self.representative_same_indi_id = ass_data.representative_same_indi_id;
        self.deterministic_same_indi_id = ass_data.deterministic_same_indi_id;
        self.incompletely_marked = ass_data.incompletely_marked;
        self.indirectly_connected_nominal_individual = ass_data.indirectly_connected_nominal_individual;
        self.indirectly_connected_individual_integration = ass_data.indirectly_connected_individual_integration;
        self.cardinality_cache_entry = ass_data.cardinality_cache_entry;
        for i in 0..LABEL_CACHE_ITEM_ASSOCIATABLE_TYPE_COUNT {
            self.label_cache_entries[i] = ass_data.label_cache_entries[i];
        }
        self.neighbour_role_set_hash = Id::NONE;
        self.role_set_neighbour_array = Id::NONE;
        self.association_data_update_id = ass_data.association_data_update_id;
        if increase_update_id {
            self.association_data_update_id += 1;
        }
        self.problematic_level = ass_data.problematic_level;
        self.cache_update_id = 0;
        self.cache_touch_id = 0;
        self.last_integrated_indirectly_connected_individuals_change_id = ass_data.last_integrated_indirectly_connected_individuals_change_id;
        self.prev_data = ass_data_id;
        self.problematic_leveled_neighbour = ass_data.problematic_leveled_neighbour;
        self.det_merged_same_considered_label_cache_entry = ass_data.det_merged_same_considered_label_cache_entry;
        self.last_propagation_cutting_update_id = ass_data.last_propagation_cutting_update_id;
        self.prop_cut_removed_neighbour_indi_linker = ass_data.prop_cut_removed_neighbour_indi_linker.clone();
        self
    }
    /// Port of `::initAssociationData(indiId)`.
    pub fn init_association_data_for_id(&mut self, indi_id: Cint64) -> &mut Self {
        self.flags.status_flags = 0; // initCachingStatusFlags()
        self.association_data_update_id = 1;
        self.indi_id = indi_id;
        self.representative_same_indi_id = indi_id;
        self.deterministic_same_indi_id = indi_id;
        self.incompletely_marked = false;
        self.indirectly_connected_nominal_individual = false;
        self.indirectly_connected_individual_integration = false;
        self.cardinality_cache_entry = Id::NONE;
        for i in 0..LABEL_CACHE_ITEM_ASSOCIATABLE_TYPE_COUNT {
            self.label_cache_entries[i] = Id::NONE;
        }
        self.neighbour_role_set_hash = Id::NONE;
        self.role_set_neighbour_array = Id::NONE;
        self.problematic_level = 0;
        self.cache_update_id = 0;
        self.cache_touch_id = 0;
        self.last_integrated_indirectly_connected_individuals_change_id = 0;
        self.problematic_leveled_neighbour = false;
        self.det_merged_same_considered_label_cache_entry = Id::NONE;
        self.prop_cut_removed_neighbour_indi_linker.clear();
        self.last_propagation_cutting_update_id = -1;
        self
    }
    /// Port of `::setIndividualId`.
    pub fn set_individual_id(&mut self, indi_id: Cint64) -> &mut Self { self.indi_id = indi_id; self }
    /// Port of `::getDeterministicConceptSetLabelCacheEntry`
    /// (`getLabelCacheEntry(DETERMINISTIC_CONCEPT_SET_LABEL)`).
    pub fn get_deterministic_concept_set_label_cache_entry(&self) -> LabelCacheItemId {
        self.get_label_cache_entry(LabelCacheItemType::DeterministicConceptSetLabel as Cint64)
    }
    /// Port of `::setDeterministicConceptSetLabelCacheEntry`.
    pub fn set_deterministic_concept_set_label_cache_entry(&mut self, cache_entry: LabelCacheItemId) -> &mut Self {
        self.set_label_cache_entry(LabelCacheItemType::DeterministicConceptSetLabel as Cint64, cache_entry)
    }
    /// Port of `::getDeterministicMergedSameConsideredLabelCacheEntry`.
    pub fn get_deterministic_merged_same_considered_label_cache_entry(&self) -> LabelCacheItemId {
        self.det_merged_same_considered_label_cache_entry
    }
    /// Port of `::setDeterministicMergedSameConsideredLabelCacheEntry`.
    pub fn set_deterministic_merged_same_considered_label_cache_entry(&mut self, cache_entry: LabelCacheItemId) -> &mut Self {
        self.det_merged_same_considered_label_cache_entry = cache_entry;
        self
    }
    /// Port of `::getLabelCacheEntry(labelType)`.
    pub fn get_label_cache_entry(&self, label_type: Cint64) -> LabelCacheItemId {
        self.label_cache_entries[label_type as usize]
    }
    /// Port of `::setLabelCacheEntry(labelType, cacheEntry)`.
    pub fn set_label_cache_entry(&mut self, label_type: Cint64, cache_entry: LabelCacheItemId) -> &mut Self {
        self.label_cache_entries[label_type as usize] = cache_entry;
        self
    }
    /// Port of `::getBackendCardinalityCacheEntry`.
    pub fn get_backend_cardinality_cache_entry(&self) -> CardinalityCacheItemId { self.cardinality_cache_entry }
    /// Port of `::setBackendCardinalityCacheEntry`.
    pub fn set_backend_cardinality_cache_entry(&mut self, cache_entry: CardinalityCacheItemId) -> &mut Self {
        self.cardinality_cache_entry = cache_entry;
        self
    }
    /// Port of `::isIncompletelyMarked`.
    pub fn is_incompletely_marked(&self) -> bool { self.incompletely_marked }
    /// Port of `::setIncompletelyMarked`.
    pub fn set_incompletely_marked(&mut self, marked: bool) -> &mut Self { self.incompletely_marked = marked; self }
    /// Port of `::getNeighbourRoleSetHash`.
    pub fn get_neighbour_role_set_hash(&self) -> IndividualNeighbourRoleSetHashId { self.neighbour_role_set_hash }
    /// Port of `::setNeighbourRoleSetHash`.
    pub fn set_neighbour_role_set_hash(&mut self, neighbour_role_set_hash: IndividualNeighbourRoleSetHashId) -> &mut Self {
        self.neighbour_role_set_hash = neighbour_role_set_hash;
        self
    }
    /// Port of `::getRoleSetNeighbourArray`.
    pub fn get_role_set_neighbour_array(&self) -> IndividualRoleSetNeighbourArrayId { self.role_set_neighbour_array }
    /// Port of `::setRoleSetNeighbourArray`.
    pub fn set_role_set_neighbour_array(&mut self, role_set_neighbour_array: IndividualRoleSetNeighbourArrayId) -> &mut Self {
        self.role_set_neighbour_array = role_set_neighbour_array;
        self
    }
    /// Port of `::getAssociationDataUpdateId`.
    pub fn get_association_data_update_id(&self) -> Cint64 { self.association_data_update_id }
    /// Port of `::getCacheUpdateId`.
    pub fn get_cache_update_id(&self) -> Cint64 { self.cache_update_id }
    /// Port of `::getCacheTouchId`.
    pub fn get_cache_touch_id(&self) -> Cint64 { self.cache_touch_id }
    /// Port of `::setCacheUpdateId` (`mCacheUpdateId = updateId; mCacheTouchId = updateId;`).
    pub fn set_cache_update_id(&mut self, update_id: Cint64) -> &mut Self {
        self.cache_update_id = update_id;
        self.cache_touch_id = update_id;
        self
    }
    /// Port of `::setCacheTouchId`.
    pub fn set_cache_touch_id(&mut self, update_id: Cint64) -> &mut Self { self.cache_touch_id = update_id; self }
    /// Port of `::getLastIntegratedIndirectlyConnectedIndividualsChangeId`.
    pub fn get_last_integrated_indirectly_connected_individuals_change_id(&self) -> Cint64 {
        self.last_integrated_indirectly_connected_individuals_change_id
    }
    /// Port of `::setLastIntegratedIndirectlyConnectedIndividualsChangeId`.
    pub fn set_last_integrated_indirectly_connected_individuals_change_id(&mut self, last_integrated_change_id: Cint64) -> &mut Self {
        self.last_integrated_indirectly_connected_individuals_change_id = last_integrated_change_id;
        self
    }
    /// Port of `::isIndirectlyConnectedNominalIndividual`.
    pub fn is_indirectly_connected_nominal_individual(&self) -> bool { self.indirectly_connected_nominal_individual }
    /// Port of `::setIndirectlyConnectedNominalIndividual`.
    pub fn set_indirectly_connected_nominal_individual(&mut self, indirectly_connected: bool) -> &mut Self {
        self.indirectly_connected_nominal_individual = indirectly_connected;
        self
    }
    /// Port of `::hasIndirectlyConnectedIndividualIntegration`.
    pub fn has_indirectly_connected_individual_integration(&self) -> bool { self.indirectly_connected_individual_integration }
    /// Port of `::setIndirectlyConnectedIndividualIntegration`.
    pub fn set_indirectly_connected_individual_integration(&mut self, indirectly_connected_individual_integration: bool) -> &mut Self {
        self.indirectly_connected_individual_integration = indirectly_connected_individual_integration;
        self
    }
    /// Port of `::getRepresentativeSameIndividualId`.
    pub fn get_representative_same_individual_id(&self) -> Cint64 { self.representative_same_indi_id }
    /// Port of `::setRepresentativeSameIndividualId`.
    pub fn set_representative_same_individual_id(&mut self, indi_id: Cint64) -> &mut Self {
        self.representative_same_indi_id = indi_id;
        self
    }
    /// Port of `::hasRepresentativeSameIndividualMerging` (`mIndiID != mRepresentativeSameIndiId`).
    pub fn has_representative_same_individual_merging(&self) -> bool { self.indi_id != self.representative_same_indi_id }
    /// Port of `::getDeterministicSameIndividualId`.
    pub fn get_deterministic_same_individual_id(&self) -> Cint64 { self.deterministic_same_indi_id }
    /// Port of `::setDeterministicSameIndividualId`.
    pub fn set_deterministic_same_individual_id(&mut self, indi_id: Cint64) -> &mut Self {
        self.deterministic_same_indi_id = indi_id;
        self
    }
    /// Port of `::hasDeterministicSameIndividualMerging` (`mIndiID != mDeterministicSameIndiId`).
    pub fn has_deterministic_same_individual_merging(&self) -> bool { self.indi_id != self.deterministic_same_indi_id }
    /// Port of `::getAssociatedIndividualId` (`return mIndiID;`).
    pub fn get_associated_individual_id(&self) -> Cint64 { self.indi_id }
    /// Port of `::hasProblematicLevel` (`mProblematicLevel > 0`).
    pub fn has_problematic_level(&self) -> bool { self.problematic_level > 0 }
    /// Port of `::getProblematicLevel`.
    pub fn get_problematic_level(&self) -> Cint64 { self.problematic_level }
    /// Port of `::setProblematicLevel`.
    pub fn set_problematic_level(&mut self, level: Cint64) -> &mut Self { self.problematic_level = level; self }
    /// Port of `::incProblematicLevel`.
    pub fn inc_problematic_level(&mut self, count: Cint64) -> &mut Self { self.problematic_level += count; self }
    /// Port of `::hasProblematicLeveledNeigbour`.
    pub fn has_problematic_leveled_neigbour(&self) -> bool { self.problematic_leveled_neighbour }
    /// Port of `::setProblematicLeveledNeigbour`.
    pub fn set_problematic_leveled_neigbour(&mut self, neighbour_prop_leveled: bool) -> &mut Self {
        self.problematic_leveled_neighbour = neighbour_prop_leveled;
        self
    }
    /// Port of `::getIndividualAssociationMemoryContext`.
    pub fn get_individual_association_memory_context(&self) -> IndividualAssociationContextId { self.mem_context }
    /// Port of `::setIndividualAssociationMemoryContext`.
    pub fn set_individual_association_memory_context(&mut self, mem_con: IndividualAssociationContextId) -> &mut Self {
        self.mem_context = mem_con;
        self
    }
    /// Port of `::setLastPropagationCuttingUpdateId`.
    pub fn set_last_propagation_cutting_update_id(&mut self, id: Cint64) -> &mut Self {
        self.last_propagation_cutting_update_id = id;
        self
    }
    /// Port of `::getLastPropagationCuttingUpdateId`.
    pub fn get_last_propagation_cutting_update_id(&self) -> Cint64 { self.last_propagation_cutting_update_id }
    /// Port of `::hasLastPropagationCuttingUpdateId` (`mLastPropagationCuttingUpdateId != -1`).
    pub fn has_last_propagation_cutting_update_id(&self) -> bool { self.last_propagation_cutting_update_id != -1 }
    /// Port of `::getPreviousData`.
    pub fn get_previous_data(&self) -> IndividualAssociationDataId { self.prev_data }
    /// Port of `::getPropagationCutRemovedNeighbourIndividualLinker`.
    pub fn get_propagation_cut_removed_neighbour_individual_linker(&self) -> &[IndividualRoleSetNeighbourIndividualIdLinkerId] {
        &self.prop_cut_removed_neighbour_indi_linker
    }
    /// Port of `::setPropagationCutRemovedNeighbourIndividualLinker` (sets the chain head).
    pub fn set_propagation_cut_removed_neighbour_individual_linker(&mut self, linker: Vec<IndividualRoleSetNeighbourIndividualIdLinkerId>) -> &mut Self {
        self.prop_cut_removed_neighbour_indi_linker = linker;
        self
    }
}

/// Port of `CBackendRepresentativeMemoryCacheIndividualAssociationContext`
/// (`: CBackendRepresentativeMemoryCacheContext, CLinkerBase<...>`).
///
/// A per-individual(-group) pooled memory context with its own pool container and
/// the recomputation-reference linker span that pins its validity window.
#[derive(Debug, Clone)]
pub struct IndividualAssociationContext {
    /// `CMemoryPoolContainerAllocationManager mMemMan` (by value).  [memory-pool] → opaque.
    pub mem_man: Cint64,
    /// `CBackendRepresentativeMemoryCacheContext* mCacheContext`.  [ownership] → opaque.
    pub cache_context: Cint64,
    /// `CMemoryPoolProvider* mMemoryPoolProvider`.  [memory-pool] → opaque.
    pub memory_pool_provider: Cint64,
    /// `CMemoryPoolContainer mMemPoolContainer` (by value).  [memory-pool] → opaque.
    pub mem_pool_container: Cint64,
    /// `CBackendRepresentativeMemoryCacheOntologyDataRecomputationReferenceLinker* mFirstRecomputationReferenceLinker`.
    pub first_recomputation_reference_linker: OntologyDataRecomputationReferenceLinkerId,
    /// `... mLastRecomputationReferenceLinker`.
    pub last_recomputation_reference_linker: OntologyDataRecomputationReferenceLinkerId,
    /// `cint64 mIndividualAssociationDataUsageCount`.
    pub individual_association_data_usage_count: Cint64,
    /// `cint64 mPreviousMemoryManagementCount`.
    pub previous_memory_management_count: Cint64,
}

impl Default for IndividualAssociationContext {
    fn default() -> Self {
        IndividualAssociationContext {
            mem_man: INVALID,
            cache_context: INVALID,
            memory_pool_provider: INVALID,
            mem_pool_container: INVALID,
            first_recomputation_reference_linker: Id::NONE,
            last_recomputation_reference_linker: Id::NONE,
            individual_association_data_usage_count: 0,
            previous_memory_management_count: 0,
        }
    }
}

impl IndividualAssociationContext {
    /// Port of `CBackendRepresentativeMemoryCacheIndividualAssociationContext::CBackendRepresentativeMemoryCacheIndividualAssociationContext(cacheContext)`.
    pub fn new(cache_context: Cint64) -> Self {
        IndividualAssociationContext { cache_context, ..Default::default() }
    }

    /// Port of `::getMemoryAllocationManager` (`return &mMemMan;`).
    /// KONCLUDE-PORT-NOTE[memory-pool]: the pool managers are opaque `Cint64` handles.
    pub fn get_memory_allocation_manager(&self) -> Cint64 { self.mem_man }
    /// Port of `::getMemoryPoolProvider` (`return mMemoryPoolProvider;`).  [memory-pool]
    pub fn get_memory_pool_provider(&self) -> Cint64 { self.memory_pool_provider }
    /// Port of `::getMemoryPoolContainer` (`return &mMemPoolContainer;`).  [memory-pool]
    pub fn get_memory_pool_container(&self) -> Cint64 { self.mem_pool_container }
    /// Port of `::getLastRecomputationReferenceLinker`.
    pub fn get_last_recomputation_reference_linker(&self) -> OntologyDataRecomputationReferenceLinkerId {
        self.last_recomputation_reference_linker
    }
    /// Port of `::getFirstRecomputationReferenceLinker`.
    pub fn get_first_recomputation_reference_linker(&self) -> OntologyDataRecomputationReferenceLinkerId {
        self.first_recomputation_reference_linker
    }
    /// Port of `::setLastRecomputationReferenceLinker`.
    pub fn set_last_recomputation_reference_linker(&mut self, recomputation_reference_linker: OntologyDataRecomputationReferenceLinkerId) -> &mut Self {
        self.last_recomputation_reference_linker = recomputation_reference_linker;
        self
    }
    /// Port of `::setFirstRecomputationReferenceLinker`.
    pub fn set_first_recomputation_reference_linker(&mut self, recomputation_reference_linker: OntologyDataRecomputationReferenceLinkerId) -> &mut Self {
        self.first_recomputation_reference_linker = recomputation_reference_linker;
        self
    }
    /// Port of `::getIndividualAssociationDataUsageCount`.
    pub fn get_individual_association_data_usage_count(&self) -> Cint64 { self.individual_association_data_usage_count }
    /// Port of `::incIndividualAssociationDataUsageCount`.
    pub fn inc_individual_association_data_usage_count(&mut self, count: Cint64) -> &mut Self {
        self.individual_association_data_usage_count += count;
        self
    }
    /// Port of `::getPreviousMemoryManagementCount`.
    pub fn get_previous_memory_management_count(&self) -> Cint64 { self.previous_memory_management_count }
    /// Port of `::setPreviousMemoryManagementCount`.
    pub fn set_previous_memory_management_count(&mut self, previous_count: Cint64) -> &mut Self {
        self.previous_memory_management_count = previous_count;
        self
    }
}

// ===========================================================================
// CBackendRepresentativeMemoryCacheOntologyData — the per-ontology data block.
// ===========================================================================

/// Port of `CBackendRepresentativeMemoryCacheOntologyData`.
///
/// The root per-ontology storage the slot ring points at: the per-type signature
/// → label-item hashes, the individual-id → association-data hash + vector, the
/// nominal indirect-connection hash, the indexing / precomputation / recomputation
/// bookkeeping, and the temporary + persistent ontology allocation contexts.
#[derive(Debug, Clone)]
pub struct OntologyData {
    /// `cint64 mOntologyIdentifer`.
    pub ontology_identifer: Cint64,
    /// `cint64 mUsageCount`.
    pub usage_count: Cint64,

    /// `CCACHINGHASH<cint64, CBackendRepresentativeMemoryLabelSignatureResolveCacheItem>* mSigLabelItemHash[LABEL_CACHE_ITEM_TYPE_COUNT]` (16).
    pub sig_label_item_hash: Vec<HashMap<Cint64, LabelSignatureResolveCacheItem>>,
    /// `cint64 mNextEntryID`.
    pub next_entry_id: Cint64,

    /// `CCACHINGHASH<cint64, CBackendRepresentativeMemoryCacheIndividualAssociationData*>* mIndiIdAssoDataHash`.
    pub indi_id_asso_data_hash: HashMap<Cint64, IndividualAssociationDataId>,
    /// `CCACHINGHASH<cint64, CBackendRepresentativeMemoryCacheNominalIndividualIndirectConnectionData*>* mNominalIndiIdIndirectConnectionDataHash`.
    pub nominal_indi_id_indirect_connection_data_hash: HashMap<Cint64, NominalIndividualIndirectConnectionDataId>,

    /// `cint64 mMaxStoredIndvidualiId`.
    pub max_stored_indvidual_id: Cint64,
    /// `cint64 mIndiIdAssoDataVectorSize`.
    pub indi_id_asso_data_vector_size: Cint64,
    /// `CBackendRepresentativeMemoryCacheIndividualAssociationData** mIndiIdAssoDataVector`.
    pub indi_id_asso_data_vector: Vec<IndividualAssociationDataId>,

    /// `cint64 mLastMinIncompletelyHandledIndiId`.
    pub last_min_incompletely_handled_indi_id: Cint64,
    /// `cint64 mIncompletelyHandledIndiIdCount`.
    pub incompletely_handled_indi_id_count: Cint64,
    /// `cint64 mIndividualAssociationsCount`.
    pub individual_associations_count: Cint64,
    /// `bool mAssociationCompleted`.
    pub association_completed: bool,
    /// `bool mFirstIncompletelyHandledIndividualsRetrieved`.
    pub first_incompletely_handled_individuals_retrieved: bool,
    /// `cint64 mMaxIndiAssocDataUpdateCount`.
    pub max_indi_assoc_data_update_count: Cint64,
    /// `bool mSameMergedIndisInCache`.
    pub same_merged_indis_in_cache: bool,

    /// `CBackendRepresentativeMemoryCacheOntologyContext mTemporaryContext` (by value).
    pub temporary_context: BackendRepresentativeMemoryCacheOntologyContext,
    /// `CBackendRepresentativeMemoryCacheOntologyContext* mOntologyContext`.
    pub ontology_context: OntologyContextId,

    /// `CCACHINGSET<cint64>* mProblematicIncompletelyHandledIndiSet`.
    pub problematic_incompletely_handled_indi_set: Vec<Cint64>,
    /// `CBackendRepresentativeMemoryLabelCacheItem* mPrioritizedPropagationMarkedNeighbourLabelItem`.
    pub prioritized_propagation_marked_neighbour_label_item: LabelCacheItemId,

    /// `bool mIndividualLabelAssociationIndexed`.
    pub individual_label_association_indexed: bool,
    /// `QMutex mIndividualLabelAssociationIndexedWaitingMutex`.  [threading] → opaque.
    pub individual_label_association_indexed_waiting_mutex: Cint64,
    /// `cint64 mIndividualLabelAssociationIndexedWaitingCount`.
    pub individual_label_association_indexed_waiting_count: Cint64,
    /// `QAtomicInt mIndividualLabelAssociationIndexingCount`.  [threading] → opaque.
    pub individual_label_association_indexing_count: Cint64,
    /// `QSemaphore mIndividualLabelAssociationIndexedWaitingSemaphore`.  [threading] → opaque.
    pub individual_label_association_indexed_waiting_semaphore: Cint64,

    /// `cint64 mNextSlotUpdateWaitingCount`.
    pub next_slot_update_waiting_count: Cint64,
    /// `bool mSlotUpdateIntegrated`.
    pub slot_update_integrated: bool,

    /// `bool mBasicPrecomputationMode`.
    pub basic_precomputation_mode: bool,
    /// `CBackendRepresentativeMemoryCacheIndividualAssociationData** mBasicPrecompuationIndiIdAssoDataVector`.
    pub basic_precompuation_indi_id_asso_data_vector: Vec<IndividualAssociationDataId>,
    /// `cint64 mBasicPrecompuationIndiIdAssoDataVectorSize`.
    pub basic_precompuation_indi_id_asso_data_vector_size: Cint64,
    /// `cint64 mBasicPrecompuationRetrievalIndiIdPos`.
    pub basic_precompuation_retrieval_indi_id_pos: Cint64,
    /// `bool mBasicPrecomputationModeActivation`.
    pub basic_precomputation_mode_activation: bool,

    /// `cint64 mInvolvedIndividualCount`.
    pub involved_individual_count: Cint64,
    /// `cint64 mIndividualAssociationDataUpdateCount`.
    pub individual_association_data_update_count: Cint64,
    /// `cint64 mIndividualAssociationDataDirectUpdateCount`.
    pub individual_association_data_direct_update_count: Cint64,
    /// `cint64 mIndividualAssociationMergingCount`.
    pub individual_association_merging_count: Cint64,
    /// `cint64 mIncompletelyHandledIndividualsRetrievalCount`.
    pub incompletely_handled_individuals_retrieval_count: Cint64,
    /// `cint64 mCacheDataUpdateWritingCount`.
    pub cache_data_update_writing_count: Cint64,

    /// `cint64 mMinimumValidRecomputationId`.
    pub minimum_valid_recomputation_id: Cint64,
    /// `cint64 mNextUpdateMinimumValidRecomputationId`.
    pub next_update_minimum_valid_recomputation_id: Cint64,

    /// `... mRecomputationReferenceLinker`.
    pub recomputation_reference_linker: OntologyDataRecomputationReferenceLinkerId,
    /// `... mLastActiveRecomputationReferenceLinker`.
    pub last_active_recomputation_reference_linker: OntologyDataRecomputationReferenceLinkerId,
    /// `cint64 mOntologyDataUpdateId`.
    pub ontology_data_update_id: Cint64,
    /// `CCACHINGMAP<cint64, CBackendRepresentativeMemoryCacheIndividualAssociationContext*>* mRecomputationIdReleasingIndividualAssociationMap`.
    pub recomputation_id_releasing_individual_association_map: HashMap<Cint64, IndividualAssociationContextId>,
    /// `CBackendRepresentativeMemoryCacheIndividualAssociationContext* mReleaseQueuedIndividualAssociationContextLinker` (chain).
    pub release_queued_individual_association_context_linker: Vec<IndividualAssociationContextId>,
}

impl Default for OntologyData {
    fn default() -> Self {
        OntologyData {
            ontology_identifer: 0,
            usage_count: 0,
            sig_label_item_hash: vec![HashMap::new(); LABEL_CACHE_ITEM_TYPE_COUNT],
            next_entry_id: 0,
            indi_id_asso_data_hash: HashMap::new(),
            nominal_indi_id_indirect_connection_data_hash: HashMap::new(),
            max_stored_indvidual_id: 0,
            indi_id_asso_data_vector_size: 0,
            indi_id_asso_data_vector: Vec::new(),
            last_min_incompletely_handled_indi_id: 0,
            incompletely_handled_indi_id_count: 0,
            individual_associations_count: 0,
            association_completed: false,
            first_incompletely_handled_individuals_retrieved: false,
            max_indi_assoc_data_update_count: 0,
            same_merged_indis_in_cache: false,
            temporary_context: BackendRepresentativeMemoryCacheOntologyContext::default(),
            ontology_context: Id::NONE,
            problematic_incompletely_handled_indi_set: Vec::new(),
            prioritized_propagation_marked_neighbour_label_item: Id::NONE,
            individual_label_association_indexed: false,
            individual_label_association_indexed_waiting_mutex: INVALID,
            individual_label_association_indexed_waiting_count: 0,
            individual_label_association_indexing_count: 0,
            individual_label_association_indexed_waiting_semaphore: INVALID,
            next_slot_update_waiting_count: 0,
            slot_update_integrated: false,
            basic_precomputation_mode: false,
            basic_precompuation_indi_id_asso_data_vector: Vec::new(),
            basic_precompuation_indi_id_asso_data_vector_size: 0,
            basic_precompuation_retrieval_indi_id_pos: 0,
            basic_precomputation_mode_activation: false,
            involved_individual_count: 0,
            individual_association_data_update_count: 0,
            individual_association_data_direct_update_count: 0,
            individual_association_merging_count: 0,
            incompletely_handled_individuals_retrieval_count: 0,
            cache_data_update_writing_count: 0,
            minimum_valid_recomputation_id: 0,
            next_update_minimum_valid_recomputation_id: 0,
            recomputation_reference_linker: Id::NONE,
            last_active_recomputation_reference_linker: Id::NONE,
            ontology_data_update_id: 0,
            recomputation_id_releasing_individual_association_map: HashMap::new(),
            release_queued_individual_association_context_linker: Vec::new(),
        }
    }
}

impl OntologyData {
    /// Port of `CBackendRepresentativeMemoryCacheOntologyData::CBackendRepresentativeMemoryCacheOntologyData(baseContext)`.
    pub fn new() -> Self { Self::default() }

    /// Port of `::initOntologyData(ontologyIdentifer, directIndexing)`.
    /// KONCLUDE-PORT-NOTE[ownership]: the C++ raw pointers / hashes set to `nullptr` become the
    /// cleared inline containers; `CINT64_MAX` → `i64::MAX`.
    pub fn init_ontology_data(&mut self, ontology_identifer: Cint64, direct_indexing: bool) -> &mut Self {
        self.ontology_identifer = ontology_identifer;
        for h in self.sig_label_item_hash.iter_mut() {
            h.clear();
        }
        self.nominal_indi_id_indirect_connection_data_hash.clear();
        self.indi_id_asso_data_hash.clear();
        self.indi_id_asso_data_vector.clear();
        self.indi_id_asso_data_vector_size = 0;
        self.same_merged_indis_in_cache = false;
        self.association_completed = false;
        self.first_incompletely_handled_individuals_retrieved = false;
        self.last_min_incompletely_handled_indi_id = i64::MAX;
        self.max_indi_assoc_data_update_count = 0;
        self.incompletely_handled_indi_id_count = 0;
        self.individual_associations_count = 0;
        self.usage_count = 0;
        self.ontology_context = Id::NONE;
        self.next_entry_id = 1;
        self.problematic_incompletely_handled_indi_set.clear();
        self.prioritized_propagation_marked_neighbour_label_item = Id::NONE;
        self.individual_label_association_indexed = direct_indexing;
        self.individual_label_association_indexed_waiting_count = 0;
        self.individual_label_association_indexing_count = 0;
        self.max_stored_indvidual_id = 0;
        self.next_slot_update_waiting_count = 0;
        self.slot_update_integrated = false;
        self.basic_precomputation_mode = false;
        self.basic_precompuation_indi_id_asso_data_vector.clear();
        self.basic_precompuation_indi_id_asso_data_vector_size = 0;
        self.basic_precompuation_retrieval_indi_id_pos = 0;
        self.basic_precomputation_mode_activation = false;
        self.individual_association_data_update_count = 0;
        self.individual_association_data_direct_update_count = 0;
        self.individual_association_merging_count = 0;
        self.involved_individual_count = 0;
        self.incompletely_handled_individuals_retrieval_count = 0;
        self.cache_data_update_writing_count = 0;
        self.recomputation_reference_linker = Id::NONE;
        self.last_active_recomputation_reference_linker = Id::NONE;
        self.minimum_valid_recomputation_id = 0;
        self.next_update_minimum_valid_recomputation_id = 0;
        self.ontology_data_update_id = 1;
        self.release_queued_individual_association_context_linker.clear();
        self.recomputation_id_releasing_individual_association_map.clear();
        self
    }
    /// Port of `::copyOntologyData(data)`.
    /// KONCLUDE-PORT-NOTE[ownership]: pointer/vector members copied by id; inline containers cloned.
    pub fn copy_ontology_data(&mut self, data: &OntologyData) -> &mut Self {
        self.same_merged_indis_in_cache = data.same_merged_indis_in_cache;
        self.max_indi_assoc_data_update_count = data.max_indi_assoc_data_update_count;
        self.association_completed = data.association_completed;
        self.incompletely_handled_indi_id_count = data.incompletely_handled_indi_id_count;
        self.last_min_incompletely_handled_indi_id = data.last_min_incompletely_handled_indi_id;
        self.next_entry_id = data.next_entry_id;
        self.max_stored_indvidual_id = data.max_stored_indvidual_id;
        self.individual_label_association_indexed = data.individual_label_association_indexed;
        self.individual_associations_count = data.individual_associations_count;
        self.first_incompletely_handled_individuals_retrieved = data.first_incompletely_handled_individuals_retrieved;
        self.next_slot_update_waiting_count = data.next_slot_update_waiting_count;
        self.basic_precomputation_mode = data.basic_precomputation_mode;
        self.basic_precompuation_indi_id_asso_data_vector = data.basic_precompuation_indi_id_asso_data_vector.clone();
        self.basic_precompuation_indi_id_asso_data_vector_size = data.basic_precompuation_indi_id_asso_data_vector_size;
        self.basic_precompuation_retrieval_indi_id_pos = data.basic_precompuation_retrieval_indi_id_pos;
        self.basic_precomputation_mode_activation = data.basic_precomputation_mode_activation;
        self.individual_association_data_direct_update_count = data.individual_association_data_direct_update_count;
        self.individual_association_data_update_count = data.individual_association_data_update_count;
        self.individual_association_merging_count = data.individual_association_merging_count;
        self.involved_individual_count = data.involved_individual_count;
        self.incompletely_handled_individuals_retrieval_count = data.incompletely_handled_individuals_retrieval_count;
        self.cache_data_update_writing_count = data.cache_data_update_writing_count;
        self.recomputation_reference_linker = data.recomputation_reference_linker;
        self.last_active_recomputation_reference_linker = Id::NONE;
        self.minimum_valid_recomputation_id = data.minimum_valid_recomputation_id;
        self.next_update_minimum_valid_recomputation_id = data.next_update_minimum_valid_recomputation_id;
        self.ontology_data_update_id = data.ontology_data_update_id + 1;
        self.release_queued_individual_association_context_linker = data.release_queued_individual_association_context_linker.clone();
        self.recomputation_id_releasing_individual_association_map = data.recomputation_id_releasing_individual_association_map.clone();
        self.prioritized_propagation_marked_neighbour_label_item = data.prioritized_propagation_marked_neighbour_label_item;
        self
    }

    /// Port of `::getOntologyIdentifer`.
    pub fn get_ontology_identifer(&self) -> Cint64 { self.ontology_identifer }
    /// Port of `::getUsageCount`.
    pub fn get_usage_count(&self) -> Cint64 { self.usage_count }
    /// Port of `::incUsageCount`.
    pub fn inc_usage_count(&mut self, count: Cint64) -> &mut Self { self.usage_count += count; self }
    /// Port of `::decUsageCount`.
    pub fn dec_usage_count(&mut self, count: Cint64) -> &mut Self { self.usage_count -= count; self }

    /// Port of `::getSignatureLabelItemHash(labelType)`.  [ownership] inline container.
    pub fn get_signature_label_item_hash(&mut self, label_type: Cint64) -> &mut HashMap<Cint64, LabelSignatureResolveCacheItem> {
        &mut self.sig_label_item_hash[label_type as usize]
    }
    /// Port of `::setSignatureLabelItemHash`. [api] inline container — the pointer assign is inert.
    pub fn set_signature_label_item_hash(&mut self, _label_type: Cint64) -> &mut Self { self }
    /// Port of `::getNominaIIndividualdIndirectConnectionDataHash`.  [ownership] inline container.
    pub fn get_nominal_individual_indirect_connection_data_hash(&mut self) -> &mut HashMap<Cint64, NominalIndividualIndirectConnectionDataId> {
        &mut self.nominal_indi_id_indirect_connection_data_hash
    }
    /// Port of `::setNominaIIndividualdIndirectConnectionDataHash`. [api] inline container — inert.
    pub fn set_nominal_individual_indirect_connection_data_hash(&mut self) -> &mut Self { self }

    /// Port of `::hasSameIndividualsMergings`.
    pub fn has_same_individuals_mergings(&self) -> bool { self.same_merged_indis_in_cache }
    /// Port of `::setSameIndividualsMergings`.
    pub fn set_same_individuals_mergings(&mut self, same_indis_mergings: bool) -> &mut Self {
        self.same_merged_indis_in_cache = same_indis_mergings;
        self
    }

    /// Port of `::getIndividualIdAssociationDataHash`.  [ownership] inline container.
    pub fn get_individual_id_association_data_hash(&mut self) -> &mut HashMap<Cint64, IndividualAssociationDataId> {
        &mut self.indi_id_asso_data_hash
    }
    /// Port of `::setIndividualIdAssociationDataHash`. [api] inline container — inert.
    pub fn set_individual_id_association_data_hash(&mut self) -> &mut Self { self }

    /// Port of `::getIndividualIdAssoiationDataVectorSize`.
    pub fn get_individual_id_assoiation_data_vector_size(&self) -> Cint64 { self.indi_id_asso_data_vector_size }
    /// Port of `::setIndividualIdAssoiationDataVectorSize`.
    pub fn set_individual_id_assoiation_data_vector_size(&mut self, size: Cint64) -> &mut Self {
        self.indi_id_asso_data_vector_size = size;
        self
    }
    /// Port of `::getIndividualIdAssoiationDataVector`.
    pub fn get_individual_id_assoiation_data_vector(&self) -> &[IndividualAssociationDataId] { &self.indi_id_asso_data_vector }
    /// Port of `::setIndividualIdAssoiationDataVector(size, vector)`.
    pub fn set_individual_id_assoiation_data_vector(&mut self, indi_id_asso_data_vector_size: Cint64, indi_id_asso_data_vector: Vec<IndividualAssociationDataId>) -> &mut Self {
        self.indi_id_asso_data_vector = indi_id_asso_data_vector;
        self.indi_id_asso_data_vector_size = indi_id_asso_data_vector_size;
        self
    }

    /// Port of `::getNextEntryID(moveNext)`.
    pub fn get_next_entry_id(&mut self, move_next: bool) -> Cint64 {
        let next_entry_id = self.next_entry_id;
        if move_next {
            self.next_entry_id += 1;
        }
        next_entry_id
    }
    /// Port of `::setNextEntryID`.
    pub fn set_next_entry_id(&mut self, next_entry_id: Cint64) -> &mut Self { self.next_entry_id = next_entry_id; self }

    /// Port of `::getMaxStoredIndvidualiId`.
    pub fn get_max_stored_indvidual_id(&self) -> Cint64 { self.max_stored_indvidual_id }
    /// Port of `::updateMaxStoredIndvidualiId` (`qMax`).
    pub fn update_max_stored_indvidual_id(&mut self, id: Cint64) -> &mut Self {
        self.max_stored_indvidual_id = id.max(self.max_stored_indvidual_id);
        self
    }

    /// Port of `::getLastMinIncompletelyHandledIndvidualiId`.
    pub fn get_last_min_incompletely_handled_indvidual_id(&self) -> Cint64 { self.last_min_incompletely_handled_indi_id }
    /// Port of `::setLastMinIncompletelyHandledIndvidualiId`.
    pub fn set_last_min_incompletely_handled_indvidual_id(&mut self, id: Cint64) -> &mut Self {
        self.last_min_incompletely_handled_indi_id = id;
        self
    }
    /// Port of `::incLastMinIncompletelyHandledIndvidualiId`.
    pub fn inc_last_min_incompletely_handled_indvidual_id(&mut self, count: Cint64) -> &mut Self {
        self.last_min_incompletely_handled_indi_id += count;
        self
    }

    /// Port of `::getIncompletelyHandledIndividualIdCount`.
    pub fn get_incompletely_handled_individual_id_count(&self) -> Cint64 { self.incompletely_handled_indi_id_count }
    /// Port of `::setIncompletelyHandledIndividualIdCount`.
    pub fn set_incompletely_handled_individual_id_count(&mut self, count: Cint64) -> &mut Self {
        self.incompletely_handled_indi_id_count = count;
        self
    }
    /// Port of `::incIncompletelyHandledIndividualIdCount`.
    pub fn inc_incompletely_handled_individual_id_count(&mut self, count: Cint64) -> &mut Self {
        self.incompletely_handled_indi_id_count += count;
        self
    }
    /// Port of `::decIncompletelyHandledIndividualIdCount`.
    pub fn dec_incompletely_handled_individual_id_count(&mut self, count: Cint64) -> &mut Self {
        self.incompletely_handled_indi_id_count -= count;
        self
    }

    /// Port of `::getIndividualAssociationsCount`.
    pub fn get_individual_associations_count(&self) -> Cint64 { self.individual_associations_count }
    /// Port of `::setIndividualAssociationsCount`.
    pub fn set_individual_associations_count(&mut self, count: Cint64) -> &mut Self { self.individual_associations_count = count; self }
    /// Port of `::incIndividualAssociationsCount`.
    pub fn inc_individual_associations_count(&mut self, count: Cint64) -> &mut Self { self.individual_associations_count += count; self }

    /// Port of `::isAssociationCompleted`.
    pub fn is_association_completed(&self) -> bool { self.association_completed }
    /// Port of `::setAssociationCompleted`.
    pub fn set_association_completed(&mut self, completed: bool) -> &mut Self { self.association_completed = completed; self }

    /// Port of `::isFirstIncompletelyHandledIndividualsRetrieved`.
    pub fn is_first_incompletely_handled_individuals_retrieved(&self) -> bool { self.first_incompletely_handled_individuals_retrieved }
    /// Port of `::setFirstIncompletelyHandledIndividualsRetrieved`.
    pub fn set_first_incompletely_handled_individuals_retrieved(&mut self, retrieved: bool) -> &mut Self {
        self.first_incompletely_handled_individuals_retrieved = retrieved;
        self
    }

    /// Port of `::getMaxIndividualAssociationDataUpdateCount`.
    pub fn get_max_individual_association_data_update_count(&self) -> Cint64 { self.max_indi_assoc_data_update_count }
    /// Port of `::setMaxIndividualAssociationDataUpdateCount`.
    pub fn set_max_individual_association_data_update_count(&mut self, count: Cint64) -> &mut Self {
        self.max_indi_assoc_data_update_count = count;
        self
    }

    /// Port of `::getProblematicIncompletelyHandledIndividualSet`.  [ownership] inline container.
    pub fn get_problematic_incompletely_handled_individual_set(&mut self) -> &mut Vec<Cint64> { &mut self.problematic_incompletely_handled_indi_set }
    /// Port of `::setProblematicIncompletelyHandledIndividualSet`. [api] inline container — inert.
    pub fn set_problematic_incompletely_handled_individual_set(&mut self) -> &mut Self { self }

    /// Port of `::getTemporaryContext` (`return &mTemporaryContext;`).
    pub fn get_temporary_context(&mut self) -> &mut BackendRepresentativeMemoryCacheOntologyContext { &mut self.temporary_context }
    /// Port of `::getOntologyContext`.
    pub fn get_ontology_context(&self) -> OntologyContextId { self.ontology_context }
    /// Port of `::setOntologyContext`.
    pub fn set_ontology_context(&mut self, ont_context: OntologyContextId) -> &mut Self { self.ontology_context = ont_context; self }

    /// Port of `::getPrioritizedPropagationMarkedNeighbourLabelItem`.
    pub fn get_prioritized_propagation_marked_neighbour_label_item(&self) -> LabelCacheItemId { self.prioritized_propagation_marked_neighbour_label_item }
    /// Port of `::setPrioritizedPropagationMarkedNeighbourLabelItem`.
    pub fn set_prioritized_propagation_marked_neighbour_label_item(&mut self, label_item: LabelCacheItemId) -> &mut Self {
        self.prioritized_propagation_marked_neighbour_label_item = label_item;
        self
    }

    /// Port of `::isIndividualLabelAssociationIndexed`.
    pub fn is_individual_label_association_indexed(&self) -> bool { self.individual_label_association_indexed }
    /// Port of `::setIndividualLabelAssociationIndexed`.
    pub fn set_individual_label_association_indexed(&mut self, indexed: bool) -> &mut Self {
        self.individual_label_association_indexed = indexed;
        self
    }
    /// Port of `::setIndividualLabelAssociationIndexingCount`.
    pub fn set_individual_label_association_indexing_count(&mut self, count: Cint64) -> &mut Self {
        self.individual_label_association_indexing_count = count;
        self
    }
    /// Port of `::updateIndividualLabelAssociationIndexed(releaseWaiting, memoryPools)`.
    /// KONCLUDE-PORT-NOTE[threading]: the `QMutex`/`QSemaphore` guard drops under the single-thread
    /// staging; [memory-pool] the `appendMemoryPool(memoryPools)` is deferred.
    pub fn update_individual_label_association_indexed(&mut self, release_waiting: bool, _memory_pools: Cint64) -> Cint64 {
        self.individual_label_association_indexing_count -= 1; // mIndividualLabelAssociationIndexingCount.deref()
        let remaining_count = self.individual_label_association_indexing_count;
        if self.individual_label_association_indexing_count <= 0 {
            self.individual_label_association_indexed = true;
            if release_waiting {
                // [threading] semaphore release of the waiting threads.
                self.individual_label_association_indexed_waiting_count = 0;
            }
        }
        remaining_count
    }
    /// Port of `::waitIndividualLabelAssociationIndexed`.
    /// KONCLUDE-PORT-NOTE[threading]: single-thread — no blocking wait/acquire.
    pub fn wait_individual_label_association_indexed(&mut self) -> &mut Self { self }

    /// Port of `::getNextSlotUpdateWaitingCount`.
    pub fn get_next_slot_update_waiting_count(&self) -> Cint64 { self.next_slot_update_waiting_count }
    /// Port of `::setNextSlotUpdateWaitingCount`.
    pub fn set_next_slot_update_waiting_count(&mut self, update_count: Cint64) -> &mut Self {
        self.next_slot_update_waiting_count = update_count;
        self
    }
    /// Port of `::isSlotUpdateIntegrated`.
    pub fn is_slot_update_integrated(&self) -> bool { self.slot_update_integrated }
    /// Port of `::setSlotUpdateIntegrated`.
    pub fn set_slot_update_integrated(&mut self, integrated: bool) -> &mut Self { self.slot_update_integrated = integrated; self }

    /// Port of `::isBasicPrecomputationMode`.
    pub fn is_basic_precomputation_mode(&self) -> bool { self.basic_precomputation_mode }
    /// Port of `::setBasicPrecomputationMode`.
    pub fn set_basic_precomputation_mode(&mut self, basic_precomputation: bool) -> &mut Self {
        self.basic_precomputation_mode = basic_precomputation;
        self
    }
    /// Port of `::getBasicPrecomputationIndividualIdAssoiationDataVector`.
    pub fn get_basic_precomputation_individual_id_assoiation_data_vector(&self) -> &[IndividualAssociationDataId] {
        &self.basic_precompuation_indi_id_asso_data_vector
    }
    /// Port of `::setBasicPrecomputationIndividualIdAssoiationDataVector(size, vector)`.
    pub fn set_basic_precomputation_individual_id_assoiation_data_vector(&mut self, indi_id_asso_data_vector_size: Cint64, indi_id_asso_data_vector: Vec<IndividualAssociationDataId>) -> &mut Self {
        self.basic_precompuation_indi_id_asso_data_vector = indi_id_asso_data_vector;
        self.basic_precompuation_indi_id_asso_data_vector_size = indi_id_asso_data_vector_size;
        self
    }
    /// Port of `::getBasicPrecomputationIndividualIdAssoiationDataVectorSize`.
    pub fn get_basic_precomputation_individual_id_assoiation_data_vector_size(&self) -> Cint64 {
        self.basic_precompuation_indi_id_asso_data_vector_size
    }
    /// Port of `::getBasicPrecompuationRetrievalIndividualIdPosition`.
    pub fn get_basic_precompuation_retrieval_individual_id_position(&self) -> Cint64 { self.basic_precompuation_retrieval_indi_id_pos }
    /// Port of `::setBasicPrecompuationRetrievalIndividualIdPosition`.
    pub fn set_basic_precompuation_retrieval_individual_id_position(&mut self, indi_pos: Cint64) -> &mut Self {
        self.basic_precompuation_retrieval_indi_id_pos = indi_pos;
        self
    }
    /// Port of `::hasBasicPrecomputationModeActivation`.
    pub fn has_basic_precomputation_mode_activation(&self) -> bool { self.basic_precomputation_mode_activation }
    /// Port of `::setBasicPrecomputationModeActivation`.
    pub fn set_basic_precomputation_mode_activation(&mut self, basic_precomputation_activation: bool) -> &mut Self {
        self.basic_precomputation_mode_activation = basic_precomputation_activation;
        self
    }

    /// Port of `::getIndividualAssociationDataUpdateCount`.
    pub fn get_individual_association_data_update_count(&self) -> Cint64 { self.individual_association_data_update_count }
    /// Port of `::incIndividualAssociationDataUpdateCount`.
    pub fn inc_individual_association_data_update_count(&mut self, count: Cint64) -> &mut Self {
        self.individual_association_data_update_count += count;
        self
    }
    /// Port of `::getIndividualAssociationDataDirectUpdateCount`.
    pub fn get_individual_association_data_direct_update_count(&self) -> Cint64 { self.individual_association_data_direct_update_count }
    /// Port of `::incIndividualAssociationDataDirectUpdateCount`.
    pub fn inc_individual_association_data_direct_update_count(&mut self, count: Cint64) -> &mut Self {
        self.individual_association_data_direct_update_count += count;
        self
    }
    /// Port of `::getIndividualAssociationMergingCount`.
    pub fn get_individual_association_merging_count(&self) -> Cint64 { self.individual_association_merging_count }
    /// Port of `::incIndividualAssociationMergingCount`.
    pub fn inc_individual_association_merging_count(&mut self, count: Cint64) -> &mut Self {
        self.individual_association_merging_count += count;
        self
    }
    /// Port of `::getInvolvedIndividualCount`.
    pub fn get_involved_individual_count(&self) -> Cint64 { self.involved_individual_count }
    /// Port of `::hasInvolvedIndividuals` (`mInvolvedIndividualCount > 0`).
    pub fn has_involved_individuals(&self) -> bool { self.involved_individual_count > 0 }
    /// Port of `::incInvolvedIndividualCount`.
    pub fn inc_involved_individual_count(&mut self, count: Cint64) -> &mut Self { self.involved_individual_count += count; self }

    /// Port of `::getIncompletelyHandledIndividualsRetrievalCount`.
    pub fn get_incompletely_handled_individuals_retrieval_count(&self) -> Cint64 { self.incompletely_handled_individuals_retrieval_count }
    /// Port of `::incIncompletelyHandledIndividualsRetrievalCount`.
    pub fn inc_incompletely_handled_individuals_retrieval_count(&mut self, count: Cint64) -> &mut Self {
        self.incompletely_handled_individuals_retrieval_count += count;
        self
    }
    /// Port of `::getCacheDataUpdateWritingCount`.
    pub fn get_cache_data_update_writing_count(&self) -> Cint64 { self.cache_data_update_writing_count }
    /// Port of `::incCacheDataUpdateWritingCount`.
    pub fn inc_cache_data_update_writing_count(&mut self, count: Cint64) -> &mut Self {
        self.cache_data_update_writing_count += count;
        self
    }

    /// Port of `::getLastActiveRecomputationReferenceLinker`.
    /// KONCLUDE-PORT-NOTE[api]: the lazy compute walks the `mRecomputationReferenceLinker` chain
    /// (active/next-all-inactive flags) which needs the recomputation-linker arena (not threaded
    /// here); the chain walk is deferred (W6-DEFER[api]) — the cached field is returned.
    pub fn get_last_active_recomputation_reference_linker(&self) -> OntologyDataRecomputationReferenceLinkerId {
        self.last_active_recomputation_reference_linker
    }
    /// Port of `::getRecomputationReferenceLinker`.
    pub fn get_recomputation_reference_linker(&self) -> OntologyDataRecomputationReferenceLinkerId { self.recomputation_reference_linker }
    /// Port of `::setRecomputationReferenceLinker`
    /// (`mRecomputationReferenceLinker = linker->append(mRecomputationReferenceLinker);`).
    /// W6-DEFER[api]: `linker` becomes the new head; its tail re-links to the prior head in the arena.
    pub fn set_recomputation_reference_linker(&mut self, linker: OntologyDataRecomputationReferenceLinkerId) -> &mut Self {
        self.recomputation_reference_linker = linker;
        self
    }

    /// Port of `::getOntologyDataUpdateId`.
    pub fn get_ontology_data_update_id(&self) -> Cint64 { self.ontology_data_update_id }
    /// Port of `::getMinimumValidRecomputationId`.
    pub fn get_minimum_valid_recomputation_id(&self) -> Cint64 { self.minimum_valid_recomputation_id }
    /// Port of `::getNextUpdateMinimumValidRecomputationId`.
    pub fn get_next_update_minimum_valid_recomputation_id(&self) -> Cint64 { self.next_update_minimum_valid_recomputation_id }
    /// Port of `::setMinimumValidRecomputationId`.
    pub fn set_minimum_valid_recomputation_id(&mut self, recomputation_id: Cint64) -> &mut Self {
        self.minimum_valid_recomputation_id = recomputation_id;
        self
    }
    /// Port of `::setNextUpdateMinimumValidRecomputationId`.
    pub fn set_next_update_minimum_valid_recomputation_id(&mut self, recomputation_id: Cint64) -> &mut Self {
        self.next_update_minimum_valid_recomputation_id = recomputation_id;
        self
    }

    /// Port of `::getRecomputationIdReleasingIndividualAssociationContextMap`.  [ownership] inline container.
    pub fn get_recomputation_id_releasing_individual_association_context_map(&mut self) -> &mut HashMap<Cint64, IndividualAssociationContextId> {
        &mut self.recomputation_id_releasing_individual_association_map
    }
    /// Port of `::setRecomputationIdReleasingIndividualAssociationContextMap`. [api] inline container — inert.
    pub fn set_recomputation_id_releasing_individual_association_context_map(&mut self) -> &mut Self { self }
    /// Port of `::getReleaseQueuedIndividualAssociationContextLinker` (chain head).
    pub fn get_release_queued_individual_association_context_linker(&self) -> IndividualAssociationContextId {
        self.release_queued_individual_association_context_linker.first().copied().unwrap_or(Id::NONE)
    }
    /// Port of `::setReleaseQueuedIndividualAssociationContextLinker`.
    pub fn set_release_queued_individual_association_context_linker(&mut self, linker: IndividualAssociationContextId) -> &mut Self {
        self.release_queued_individual_association_context_linker.clear();
        if linker.is_some() {
            self.release_queued_individual_association_context_linker.push(linker);
        }
        self
    }
    /// Port of `::addReleaseQueuedIndividualAssociationContextLinker`
    /// (`mReleaseQueued = linker->append(mReleaseQueued);` — head-front prepend).
    pub fn add_release_queued_individual_association_context_linker(&mut self, linker: IndividualAssociationContextId) -> &mut Self {
        self.release_queued_individual_association_context_linker.insert(0, linker);
        self
    }
}

// ===========================================================================
// Cross-thread retrieval-update coordination hash (+ its per-entry data).
// ===========================================================================

/// Port of `CBackendIndividualRetrievalComputationUpdateCoordinationHashData`.
#[derive(Debug, Default, Clone)]
pub struct BackendIndividualRetrievalComputationUpdateCoordinationHashData {
    /// `cint64 mAssociationUpdateId`.
    pub association_update_id: Cint64,
    /// `bool mProcessed`.
    pub processed: bool,
    /// `bool mComputationIntegrated = false`.
    pub computation_integrated: bool,
    /// `bool mComputationOrdered = false`.
    pub computation_ordered: bool,
    /// `bool mNewlyRetrieved = false`.
    pub newly_retrieved: bool,
    /// `cint64 mUsageCount = 0`.
    pub usage_count: Cint64,
}
impl BackendIndividualRetrievalComputationUpdateCoordinationHashData {
    pub fn new() -> Self { Self::default() }

    /// Port of `::getAssociationUpdateId`.
    pub fn get_association_update_id(&self) -> Cint64 { self.association_update_id }
    /// Port of `::setAssociationUpdateId`.
    pub fn set_association_update_id(&mut self, update_id: Cint64) -> &mut Self { self.association_update_id = update_id; self }
    /// Port of `::isProcessed`.
    pub fn is_processed(&self) -> bool { self.processed }
    /// Port of `::setProcessed`.
    pub fn set_processed(&mut self, processed: bool) -> &mut Self { self.processed = processed; self }
    /// Port of `::setComputationOrdered`.
    pub fn set_computation_ordered(&mut self, ordered: bool) -> &mut Self { self.computation_ordered = ordered; self }
    /// Port of `::setComputationIntegrated`.
    pub fn set_computation_integrated(&mut self, integrated: bool) -> &mut Self { self.computation_integrated = integrated; self }
    /// Port of `::setNewlyRetrieved`.
    pub fn set_newly_retrieved(&mut self, retrieved: bool) -> &mut Self { self.newly_retrieved = retrieved; self }
    /// Port of `::isComputationOrdered`.
    pub fn is_computation_ordered(&self) -> bool { self.computation_ordered }
    /// Port of `::isComputationIntegrated`.
    pub fn is_computation_integrated(&self) -> bool { self.computation_integrated }
    /// Port of `::isNewlyRetrieved`.
    pub fn is_newly_retrieved(&self) -> bool { self.newly_retrieved }
    /// Port of `::incUsageCount`.
    pub fn inc_usage_count(&mut self, count: Cint64) -> &mut Self { self.usage_count += count; self }
    /// Port of `::decUsageCount`.
    pub fn dec_usage_count(&mut self, count: Cint64) -> &mut Self { self.usage_count -= count; self }
    /// Port of `::getUsageCount`.
    pub fn get_usage_count(&self) -> Cint64 { self.usage_count }
}

/// Port of `CBackendIndividualRetrievalComputationUpdateCoordinationHash`
/// (`: QMap<cint64, ...CoordinationHashData*>`).
///
/// Cross-thread retrieval/update coordination: the `QMap` base becomes the
/// `coordination_data` map; the scalar fields track the incompletely-handled /
/// processed / computation / remaining / removed / usage counts and the
/// basic-precomputation flags.
#[derive(Debug, Default, Clone)]
pub struct BackendIndividualRetrievalComputationUpdateCoordinationHash {
    /// the `QMap<cint64, CoordinationHashData*>` base (ordered).
    pub coordination_data: HashMap<Cint64, CoordinationHashDataId>,
    /// `cint64 mCorrectionIncompletelyHandledCount`.
    pub correction_incompletely_handled_count: Cint64,
    /// `cint64 mTotalIncompletelyHandledCount`.
    pub total_incompletely_handled_count: Cint64,
    /// `cint64 mHashProcessedCount`.
    pub hash_processed_count: Cint64,
    /// `cint64 mHashComputationCount`.
    pub hash_computation_count: Cint64,
    /// `cint64 mHashRemainingCount`.
    pub hash_remaining_count: Cint64,
    /// `cint64 mHashRemovedCount`.
    pub hash_removed_count: Cint64,
    /// `cint64 mUsageCount`.
    pub usage_count: Cint64,
    /// `bool mBasicPrecomputationMode`.
    pub basic_precomputation_mode: bool,
    /// `bool mBasicPrecomputationFinished`.
    pub basic_precomputation_finished: bool,
}
impl BackendIndividualRetrievalComputationUpdateCoordinationHash {
    pub fn new() -> Self { Self::default() }

    /// Port of `::getApproximateRemainingIncompletelyHandledCount`
    /// (`qMax(total + correction - (processed - removed) - computation, 0)`).
    pub fn get_approximate_remaining_incompletely_handled_count(&self) -> Cint64 {
        (self.total_incompletely_handled_count + self.correction_incompletely_handled_count
            - (self.hash_processed_count - self.hash_removed_count)
            - self.hash_computation_count)
            .max(0)
    }
    /// Port of `::getHashProcessedCount`.
    pub fn get_hash_processed_count(&self) -> Cint64 { self.hash_processed_count }
    /// Port of `::incHashProcessedCount`.
    pub fn inc_hash_processed_count(&mut self, count: Cint64) -> &mut Self { self.hash_processed_count += count; self }
    /// Port of `::decHashProcessedCount`.
    pub fn dec_hash_processed_count(&mut self, count: Cint64) -> &mut Self { self.hash_processed_count -= count; self }
    /// Port of `::getHashComputationCount`.
    pub fn get_hash_computation_count(&self) -> Cint64 { self.hash_computation_count }
    /// Port of `::incHashComputationCount`.
    pub fn inc_hash_computation_count(&mut self, count: Cint64) -> &mut Self { self.hash_computation_count += count; self }
    /// Port of `::decHashComputationCount`.
    pub fn dec_hash_computation_count(&mut self, count: Cint64) -> &mut Self { self.hash_computation_count -= count; self }
    /// Port of `::getHashRemainingCount`.
    pub fn get_hash_remaining_count(&self) -> Cint64 { self.hash_remaining_count }
    /// Port of `::incHashRemainingCount`.
    pub fn inc_hash_remaining_count(&mut self, count: Cint64) -> &mut Self { self.hash_remaining_count += count; self }
    /// Port of `::decHashRemainingCount`.
    pub fn dec_hash_remaining_count(&mut self, count: Cint64) -> &mut Self { self.hash_remaining_count -= count; self }
    /// Port of `::setHashRemainingCount`.
    pub fn set_hash_remaining_count(&mut self, count: Cint64) -> &mut Self { self.hash_remaining_count = count; self }
    /// Port of `::getHashRemovedCount`.
    pub fn get_hash_removed_count(&self) -> Cint64 { self.hash_removed_count }
    /// Port of `::incHashRemovedCount`.
    pub fn inc_hash_removed_count(&mut self, count: Cint64) -> &mut Self { self.hash_removed_count += count; self }
    /// Port of `::decHashRemovedCount`.
    pub fn dec_hash_removed_count(&mut self, count: Cint64) -> &mut Self { self.hash_removed_count -= count; self }
    /// Port of `::setHashRemovedCount`.
    pub fn set_hash_removed_count(&mut self, count: Cint64) -> &mut Self { self.hash_removed_count = count; self }
    /// Port of `::getApproximateCorrectionIncompletelyHandledCount`.
    pub fn get_approximate_correction_incompletely_handled_count(&self) -> Cint64 { self.correction_incompletely_handled_count }
    /// Port of `::incApproximateCorrectionIncompletelyHandledCount`.
    pub fn inc_approximate_correction_incompletely_handled_count(&mut self, count: Cint64) -> &mut Self {
        self.correction_incompletely_handled_count += count;
        self
    }
    /// Port of `::decApproximateCorrectionIncompletelyHandledCount`.
    pub fn dec_approximate_correction_incompletely_handled_count(&mut self, count: Cint64) -> &mut Self {
        self.correction_incompletely_handled_count -= count;
        self
    }
    /// Port of `::setApproximateCorrectionIncompletelyHandledCount`.
    pub fn set_approximate_correction_incompletely_handled_count(&mut self, count: Cint64) -> &mut Self {
        self.correction_incompletely_handled_count = count;
        self
    }
    /// Port of `::getApproximateTotalIncompletelyHandledCount`.
    pub fn get_approximate_total_incompletely_handled_count(&self) -> Cint64 { self.total_incompletely_handled_count }
    /// Port of `::incApproximateTotalIncompletelyHandledCount`.
    pub fn inc_approximate_total_incompletely_handled_count(&mut self, count: Cint64) -> &mut Self {
        self.total_incompletely_handled_count += count;
        self
    }
    /// Port of `::decApproximateTotalIncompletelyHandledCount`.
    pub fn dec_approximate_total_incompletely_handled_count(&mut self, count: Cint64) -> &mut Self {
        self.total_incompletely_handled_count -= count;
        self
    }
    /// Port of `::setApproximateTotalIncompletelyHandledCount`.
    pub fn set_approximate_total_incompletely_handled_count(&mut self, count: Cint64) -> &mut Self {
        self.total_incompletely_handled_count = count;
        self
    }
    /// Port of `::createCoordinationData` (`return new ...HashData();`).
    /// KONCLUDE-PORT-NOTE[memory-pool]: the arena/pool allocation is deferred; returns a fresh
    /// default by value.
    pub fn create_coordination_data(&self) -> BackendIndividualRetrievalComputationUpdateCoordinationHashData {
        BackendIndividualRetrievalComputationUpdateCoordinationHashData::new()
    }
    /// Port of `::getUsageCount`.
    pub fn get_usage_count(&self) -> Cint64 { self.usage_count }
    /// Port of `::incUsageCount`.
    pub fn inc_usage_count(&mut self, count: Cint64) -> &mut Self { self.usage_count += count; self }
    /// Port of `::decUsageCount`.
    pub fn dec_usage_count(&mut self, count: Cint64) -> &mut Self { self.usage_count -= count; self }
    /// Port of `::setBasicPrecomputationMode`.
    pub fn set_basic_precomputation_mode(&mut self, basic_mode: bool) -> &mut Self { self.basic_precomputation_mode = basic_mode; self }
    /// Port of `::hasBasicPrecomputationMode`.
    pub fn has_basic_precomputation_mode(&self) -> bool { self.basic_precomputation_mode }
    /// Port of `::setBasicPrecomputationFinished`.
    pub fn set_basic_precomputation_finished(&mut self, basic_mode_finished: bool) -> &mut Self {
        self.basic_precomputation_finished = basic_mode_finished;
        self
    }
    /// Port of `::hasBasicPrecomputationFinished`.
    pub fn has_basic_precomputation_finished(&self) -> bool { self.basic_precomputation_finished }
}

// ===========================================================================
// BackendTempWriteRecord — the ~13 `*Temporary*DataLinker` chains → ONE enum.
//   (mirrors the W2 `DepKind` collapse; chain → owned `Vec<BackendTempWriteRecordId>`,
//   head-front; the record discriminates which chain it belongs to.)
// ===========================================================================

/// Port of `CBackendRepresentativeMemoryCacheTemporaryAssociationWriteDataLinker::UPDATE_TYPE`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TempUpdateType {
    Addition,
    Replacement,
    Removal,
}
impl Default for TempUpdateType {
    fn default() -> Self { TempUpdateType::Addition }
}

/// Port of `CBackendRepresentativeMemoryCacheTemporaryLabelReference`
/// (`: QPair<TemporaryLabelWriteDataLinker*, CBackendRepresentativeMemoryLabelCacheItem*>`).
/// A (temp-label-write-record, resolved-label-item) pair.
#[derive(Debug, Clone, Copy)]
pub struct TempLabelReference {
    /// `.first` — the temporary label write record.
    pub temp_label_write: BackendTempWriteRecordId,
    /// `.second` — the resolved label cache item.
    pub label_item: LabelCacheItemId,
}
impl Default for TempLabelReference {
    fn default() -> Self {
        TempLabelReference { temp_label_write: Id::NONE, label_item: Id::NONE }
    }
}

impl TempLabelReference {
    /// Port of `CBackendRepresentativeMemoryCacheTemporaryLabelReference::CBackendRepresentativeMemoryCacheTemporaryLabelReference()`.
    pub fn new() -> Self { Self::default() }
    /// Port of the ctor `(CBackendRepresentativeMemoryLabelCacheItem* referredLabelData)` (`QPair(nullptr, referredLabelData)`).
    pub fn from_referred_label_data(referred_label_data: LabelCacheItemId) -> Self {
        TempLabelReference { temp_label_write: Id::NONE, label_item: referred_label_data }
    }
    /// Port of the ctor `(CBackendRepresentativeMemoryCacheTemporaryLabelWriteDataLinker* referredTmpLabelData)` (`QPair(referredTmpLabelData, nullptr)`).
    pub fn from_referred_temporary_label_data(referred_tmp_label_data: BackendTempWriteRecordId) -> Self {
        TempLabelReference { temp_label_write: referred_tmp_label_data, label_item: Id::NONE }
    }
    /// Port of `::initLabelReferenceData(labelReferenceData)`
    /// (`first = nullptr; second = nullptr; if (labelReferenceData) *this = *labelReferenceData;`).
    pub fn init_label_reference_data(&mut self, label_reference_data: Option<&TempLabelReference>) -> &mut Self {
        self.temp_label_write = Id::NONE;
        self.label_item = Id::NONE;
        if let Some(other) = label_reference_data {
            *self = *other;
        }
        self
    }
    /// Port of `::setReferredTemporaryLabelData` (`first = referredTmpLabelData;`).
    pub fn set_referred_temporary_label_data(&mut self, referred_tmp_label_data: BackendTempWriteRecordId) -> &mut Self {
        self.temp_label_write = referred_tmp_label_data;
        self
    }
    /// Port of `::setReferredLabelData` (`second = referredLabelData;`).
    pub fn set_referred_label_data(&mut self, referred_label_data: LabelCacheItemId) -> &mut Self {
        self.label_item = referred_label_data;
        self
    }
    /// Port of `::getReferredTemporaryLabelData` (`return first;`).
    pub fn get_referred_temporary_label_data(&self) -> BackendTempWriteRecordId { self.temp_label_write }
    /// Port of `::getReferredLabelData` (`return second;`).
    pub fn get_referred_label_data(&self) -> LabelCacheItemId { self.label_item }
}

/// Port of the ~13 `CBackendRepresentativeMemoryCacheTemporary*DataLinker` /
/// `*TemporaryNominalRoleConnectionData` / `*TemporaryLabelReference*` chains,
/// folded into one tagged write-record enum. Each variant carries that chain
/// node's payload; the intrusive `CLinkerBase` next-pointer is dropped (the owner
/// holds an owned `Vec<BackendTempWriteRecordId>` head-front).
#[derive(Debug, Clone)]
pub enum BackendTempWriteRecord {
    /// `CBackendRepresentativeMemoryCacheTemporaryAssociationWriteDataLinker`
    /// (`+ CBackendRepresentativeMemoryCachingFlags`).
    AssociationWrite {
        flags: BackendRepresentativeMemoryCachingFlags,
        label_update_type: TempUpdateType,
        links_update_type: TempUpdateType,
        association_update_id: Cint64,
        integrated_indirectly_connected_individuals_change_id: Cint64,
        indirectly_connected_individual_integration: bool,
        indirectly_connected_nominal_individual: bool,
        individual_id: Cint64,
        /// `CIndividual* mIndividual`.  [api] cross-family → opaque.
        individual: Cint64,
        /// `mReferredTmpLabelData[ASSOCIATABLE_TYPE_COUNT]` (15).
        referred_tmp_label_data: Vec<BackendTempWriteRecordId>,
        /// `mReferredLabelData[ASSOCIATABLE_TYPE_COUNT]` (15).
        referred_label_data: Vec<LabelCacheItemId>,
        referred_tmp_card_data: BackendTempWriteRecordId,
        referred_card_data: CardinalityCacheItemId,
        role_set_neighbour_update_data_linker: BackendTempWriteRecordId,
        representative_same_indi_id: Cint64,
        deterministic_same_indi_id: Cint64,
        require_same_as_neighbours_completion: bool,
        scheduled_individual: bool,
    },
    /// `CBackendRepresentativeMemoryCacheTemporaryAssociationUseDataLinker`.
    AssociationUse {
        individual_id: Cint64,
        association_update_id: Cint64,
    },
    /// `CBackendRepresentativeMemoryCacheTemporaryLabelWriteDataLinker`
    /// (`+ CBackendRepresentativeMemoryCachingFlags`).
    LabelWrite {
        flags: BackendRepresentativeMemoryCachingFlags,
        label_type: Cint64,
        signature: Cint64,
        det_value_linker: Vec<LabelValueLinkerId>,
        det_value_count: Cint64,
        /// `void* mTmpData`.  [api] → opaque.
        tmp_data: Cint64,
    },
    /// `CBackendRepresentativeMemoryCacheTemporaryLabelReferenceDataLinker`
    /// (`: CLinkerBase<CBackendRepresentativeMemoryCacheTemporaryLabelReference,...>`).
    LabelReference(TempLabelReference),
    /// `CBackendRepresentativeMemoryCacheTemporaryCardinalityWriteDataLinker`.
    CardinalityWrite {
        card_value_linker: Vec<CardinalityValueLinkerId>,
        card_value_count: Cint64,
        label_write_data_linker: BackendTempWriteRecordId,
    },
    /// `CBackendRepresentativeMemoryCacheTemporaryIndividualRoleSetNeighbourUpdateDataLinker`
    /// (`: CLinkerBase<CIndividualReference,...>`).
    IndividualRoleSetNeighbourUpdate {
        /// the `CLinkerBase<CIndividualReference>` payload.  [api] → opaque indi id.
        individual_reference: Cint64,
        role_set_combination_label_ref: TempLabelReference,
    },
    /// `CBackendRepresentativeMemoryCacheTemporaryInvolvedIndividualDataLinker`.
    InvolvedIndividual {
        /// `CXLinker<cint64>* mInvolvedIndividualIdsLinker` → Vec head-front.
        involved_individual_ids_linker: Vec<Cint64>,
    },
    /// `CBackendRepresentativeMemoryCacheTemporaryNominalIndirectConnectionDataLinker`.
    NominalIndirectConnection {
        nominal_indi_id: Cint64,
        last_integration_id: Cint64,
        indirectly_connected_individual_id_linker: Vec<Cint64>,
        association_update_id: Cint64,
    },
    /// `CBackendRepresentativeMemoryCacheTemporaryNominalRoleConnectionData`
    /// (`: CLinkerBase<CRole*,...>`).
    NominalRoleConnection {
        /// the `CLinkerBase<CRole*>` payload.  [api] cross-family → opaque.
        role: Cint64,
        /// `CIndividualReference mConnectedIndividual`.  [api] → opaque.
        connected_individual: Cint64,
        inversed_connection: bool,
    },
    /// `CBackendRepresentativeMemoryCacheTemporaryPropagationCutDataLinker`.
    PropagationCut {
        individual_id: Cint64,
        association_update_id: Cint64,
        expanded_individual_ids_linker: Vec<Cint64>,
        array_index: Cint64,
        concept_propagation_value: CacheValue,
        neighbour_propagation_cut_cursor: Cint64,
        prop_mark_role_value: CacheValue,
        missing_nondeterministic_expansion_propagation: bool,
    },
}

impl Default for BackendTempWriteRecord {
    fn default() -> Self {
        BackendTempWriteRecord::AssociationUse { individual_id: 0, association_update_id: 0 }
    }
}

impl BackendTempWriteRecord {
    /// Port of the `CBackendRepresentativeMemoryCacheTemporary*DataLinker` ctors;
    /// the variant selects which C++ chain node is being constructed.
    pub fn new(record: BackendTempWriteRecord) -> Self { record }

    // ===== CBackendRepresentativeMemoryCacheTemporaryAssociationWriteDataLinker =====

    /// Port of `::initAccociationWriteData(individualID, labelUpdateType, linksUpdateType)`.
    pub fn new_association_write(individual_id: Cint64, label_update_type: TempUpdateType, links_update_type: TempUpdateType) -> Self {
        let mut flags = BackendRepresentativeMemoryCachingFlags::new();
        flags.status_flags = BackendRepresentativeMemoryCachingFlags::FLAG_COMPLETELY_HANDLED
            | BackendRepresentativeMemoryCachingFlags::FLAG_COMPLETELY_SATURATED;
        BackendTempWriteRecord::AssociationWrite {
            flags,
            label_update_type,
            links_update_type,
            association_update_id: 0,
            integrated_indirectly_connected_individuals_change_id: 0,
            indirectly_connected_individual_integration: false,
            indirectly_connected_nominal_individual: false,
            individual_id,
            individual: INVALID, // mIndividual = nullptr
            referred_tmp_label_data: vec![Id::NONE; LABEL_CACHE_ITEM_ASSOCIATABLE_TYPE_COUNT],
            referred_label_data: vec![Id::NONE; LABEL_CACHE_ITEM_ASSOCIATABLE_TYPE_COUNT],
            referred_tmp_card_data: Id::NONE,
            referred_card_data: Id::NONE,
            role_set_neighbour_update_data_linker: Id::NONE,
            representative_same_indi_id: individual_id,
            deterministic_same_indi_id: individual_id,
            require_same_as_neighbours_completion: false,
            scheduled_individual: false,
        }
    }
    /// Port of `::setReferredTemporaryLabelData(labelType, referredTmpLabelData)`.
    pub fn set_referred_temporary_label_data(&mut self, label_type: Cint64, referred_tmp_label_data: BackendTempWriteRecordId) -> &mut Self {
        if let BackendTempWriteRecord::AssociationWrite { referred_tmp_label_data: arr, .. } = self {
            arr[label_type as usize] = referred_tmp_label_data;
        }
        self
    }
    /// Port of `::setReferredLabelData(labelType, referredLabelData)`.
    pub fn set_referred_label_data(&mut self, label_type: Cint64, referred_label_data: LabelCacheItemId) -> &mut Self {
        if let BackendTempWriteRecord::AssociationWrite { referred_label_data: arr, .. } = self {
            arr[label_type as usize] = referred_label_data;
        }
        self
    }
    /// Port of `::setReferredLabel(labelType, labelRef)`
    /// (`if (labelRef.getReferredLabelData()) setReferredLabelData(...); else setReferredTemporaryLabelData(...);`).
    pub fn set_referred_label(&mut self, label_type: Cint64, label_ref: &TempLabelReference) -> &mut Self {
        if label_ref.get_referred_label_data().is_some() {
            self.set_referred_label_data(label_type, label_ref.get_referred_label_data())
        } else {
            self.set_referred_temporary_label_data(label_type, label_ref.get_referred_temporary_label_data())
        }
    }
    /// Port of `::setReferredTemporaryCardinalityData`.
    pub fn set_referred_temporary_cardinality_data(&mut self, referred_tmp_card_data: BackendTempWriteRecordId) -> &mut Self {
        if let BackendTempWriteRecord::AssociationWrite { referred_tmp_card_data: c, .. } = self {
            *c = referred_tmp_card_data;
        }
        self
    }
    /// Port of `::setReferredCardinalityData`.
    pub fn set_referred_cardinality_data(&mut self, referred_card_data: CardinalityCacheItemId) -> &mut Self {
        if let BackendTempWriteRecord::AssociationWrite { referred_card_data: c, .. } = self {
            *c = referred_card_data;
        }
        self
    }
    /// Port of `::getIndividual` (the cross-family `CIndividual*`, opaque).
    pub fn get_individual(&self) -> Cint64 {
        if let BackendTempWriteRecord::AssociationWrite { individual, .. } = self { *individual } else { INVALID }
    }
    /// Port of the `getIndividualID` of AssociationWrite / AssociationUse / NominalIndirectConnection /
    /// PropagationCut (the same-named per-class getters fold to one over the variants that carry an id).
    pub fn get_individual_id(&self) -> Cint64 {
        match self {
            BackendTempWriteRecord::AssociationWrite { individual_id, .. } => *individual_id,
            BackendTempWriteRecord::AssociationUse { individual_id, .. } => *individual_id,
            BackendTempWriteRecord::NominalIndirectConnection { nominal_indi_id, .. } => *nominal_indi_id,
            BackendTempWriteRecord::PropagationCut { individual_id, .. } => *individual_id,
            _ => 0,
        }
    }
    /// Port of `::getReferredTemporaryLabelData(labelType)` (AssociationWrite).
    pub fn get_referred_temporary_label_data(&self, label_type: Cint64) -> BackendTempWriteRecordId {
        if let BackendTempWriteRecord::AssociationWrite { referred_tmp_label_data, .. } = self {
            referred_tmp_label_data[label_type as usize]
        } else {
            Id::NONE
        }
    }
    /// Port of `::getReferredLabelData(labelType)` (AssociationWrite).
    pub fn get_referred_label_data(&self, label_type: Cint64) -> LabelCacheItemId {
        if let BackendTempWriteRecord::AssociationWrite { referred_label_data, .. } = self {
            referred_label_data[label_type as usize]
        } else {
            Id::NONE
        }
    }
    /// Port of `::getReferredTemporaryCardinalityData`.
    pub fn get_referred_temporary_cardinality_data(&self) -> BackendTempWriteRecordId {
        if let BackendTempWriteRecord::AssociationWrite { referred_tmp_card_data, .. } = self { *referred_tmp_card_data } else { Id::NONE }
    }
    /// Port of `::getReferredCardinalityData`.
    pub fn get_referred_cardinality_data(&self) -> CardinalityCacheItemId {
        if let BackendTempWriteRecord::AssociationWrite { referred_card_data, .. } = self { *referred_card_data } else { Id::NONE }
    }
    /// Port of `::getLabelUpdateType`.
    pub fn get_label_update_type(&self) -> TempUpdateType {
        if let BackendTempWriteRecord::AssociationWrite { label_update_type, .. } = self { *label_update_type } else { TempUpdateType::default() }
    }
    /// Port of `::getLinksUpdateType`.
    pub fn get_links_update_type(&self) -> TempUpdateType {
        if let BackendTempWriteRecord::AssociationWrite { links_update_type, .. } = self { *links_update_type } else { TempUpdateType::default() }
    }
    /// Port of `::setLinksUpdateType`.
    pub fn set_links_update_type(&mut self, update_type: TempUpdateType) -> &mut Self {
        if let BackendTempWriteRecord::AssociationWrite { links_update_type, .. } = self { *links_update_type = update_type; }
        self
    }
    /// Port of `::getRoleSetNeighbourUpdateDataLinker`.
    pub fn get_role_set_neighbour_update_data_linker(&self) -> BackendTempWriteRecordId {
        if let BackendTempWriteRecord::AssociationWrite { role_set_neighbour_update_data_linker, .. } = self { *role_set_neighbour_update_data_linker } else { Id::NONE }
    }
    /// Port of `::setRoleSetNeighbourUpdateDataLinker`.
    pub fn set_role_set_neighbour_update_data_linker(&mut self, role_set_neighbour_update_data_linker: BackendTempWriteRecordId) -> &mut Self {
        if let BackendTempWriteRecord::AssociationWrite { role_set_neighbour_update_data_linker: r, .. } = self { *r = role_set_neighbour_update_data_linker; }
        self
    }
    /// Port of the `getUsedAssociationUpdateId` of AssociationWrite / AssociationUse.
    pub fn get_used_association_update_id(&self) -> Cint64 {
        match self {
            BackendTempWriteRecord::AssociationWrite { association_update_id, .. } => *association_update_id,
            BackendTempWriteRecord::AssociationUse { association_update_id, .. } => *association_update_id,
            _ => 0,
        }
    }
    /// Port of the `setUsedAssociationUpdateId` of AssociationWrite / AssociationUse.
    pub fn set_used_association_update_id(&mut self, id: Cint64) -> &mut Self {
        match self {
            BackendTempWriteRecord::AssociationWrite { association_update_id, .. } => *association_update_id = id,
            BackendTempWriteRecord::AssociationUse { association_update_id, .. } => *association_update_id = id,
            _ => {}
        }
        self
    }
    /// Port of `::getIntegratedIndirectlyConnectedIndividualsChangeId`.
    pub fn get_integrated_indirectly_connected_individuals_change_id(&self) -> Cint64 {
        if let BackendTempWriteRecord::AssociationWrite { integrated_indirectly_connected_individuals_change_id, .. } = self { *integrated_indirectly_connected_individuals_change_id } else { 0 }
    }
    /// Port of `::setIntegratedIndirectlyConnectedIndividualsChangeId`.
    pub fn set_integrated_indirectly_connected_individuals_change_id(&mut self, integrated_change_id: Cint64) -> &mut Self {
        if let BackendTempWriteRecord::AssociationWrite { integrated_indirectly_connected_individuals_change_id: c, .. } = self { *c = integrated_change_id; }
        self
    }
    /// Port of `::isIndirectlyConnectedNominalIndividual`.
    pub fn is_indirectly_connected_nominal_individual(&self) -> bool {
        if let BackendTempWriteRecord::AssociationWrite { indirectly_connected_nominal_individual, .. } = self { *indirectly_connected_nominal_individual } else { false }
    }
    /// Port of `::setIndirectlyConnectedNominalIndividual`.
    pub fn set_indirectly_connected_nominal_individual(&mut self, indirectly_connected: bool) -> &mut Self {
        if let BackendTempWriteRecord::AssociationWrite { indirectly_connected_nominal_individual, .. } = self { *indirectly_connected_nominal_individual = indirectly_connected; }
        self
    }
    /// Port of `::hasIndirectlyConnectedIndividualIntegration`.
    pub fn has_indirectly_connected_individual_integration(&self) -> bool {
        if let BackendTempWriteRecord::AssociationWrite { indirectly_connected_individual_integration, .. } = self { *indirectly_connected_individual_integration } else { false }
    }
    /// Port of `::setIndirectlyConnectedIndividualIntegration`.
    pub fn set_indirectly_connected_individual_integration(&mut self, indirectly_connected_individual_integration: bool) -> &mut Self {
        if let BackendTempWriteRecord::AssociationWrite { indirectly_connected_individual_integration: c, .. } = self { *c = indirectly_connected_individual_integration; }
        self
    }
    /// Port of `::getRepresentativeSameIndividualId`.
    pub fn get_representative_same_individual_id(&self) -> Cint64 {
        if let BackendTempWriteRecord::AssociationWrite { representative_same_indi_id, .. } = self { *representative_same_indi_id } else { 0 }
    }
    /// Port of `::setRepresentativeSameIndividualId`.
    pub fn set_representative_same_individual_id(&mut self, indi_id: Cint64) -> &mut Self {
        if let BackendTempWriteRecord::AssociationWrite { representative_same_indi_id, .. } = self { *representative_same_indi_id = indi_id; }
        self
    }
    /// Port of `::getDeterministicSameIndividualId`.
    pub fn get_deterministic_same_individual_id(&self) -> Cint64 {
        if let BackendTempWriteRecord::AssociationWrite { deterministic_same_indi_id, .. } = self { *deterministic_same_indi_id } else { 0 }
    }
    /// Port of `::setDeterministicSameIndividualId`.
    pub fn set_deterministic_same_individual_id(&mut self, indi_id: Cint64) -> &mut Self {
        if let BackendTempWriteRecord::AssociationWrite { deterministic_same_indi_id, .. } = self { *deterministic_same_indi_id = indi_id; }
        self
    }
    /// Port of `::requireSameAsNeighboursCompletion`.
    pub fn require_same_as_neighbours_completion(&self) -> bool {
        if let BackendTempWriteRecord::AssociationWrite { require_same_as_neighbours_completion, .. } = self { *require_same_as_neighbours_completion } else { false }
    }
    /// Port of `::setRequireSameAsNeighboursCompletion`.
    pub fn set_require_same_as_neighbours_completion(&mut self, require_completion: bool) -> &mut Self {
        if let BackendTempWriteRecord::AssociationWrite { require_same_as_neighbours_completion, .. } = self { *require_same_as_neighbours_completion = require_completion; }
        self
    }
    /// Port of `::isScheduledIndividual`.
    pub fn is_scheduled_individual(&self) -> bool {
        if let BackendTempWriteRecord::AssociationWrite { scheduled_individual, .. } = self { *scheduled_individual } else { false }
    }
    /// Port of `::setScheduledIndividual`.
    pub fn set_scheduled_individual(&mut self, scheduled: bool) -> &mut Self {
        if let BackendTempWriteRecord::AssociationWrite { scheduled_individual, .. } = self { *scheduled_individual = scheduled; }
        self
    }

    // ===== CBackendRepresentativeMemoryCacheTemporaryAssociationUseDataLinker =====

    /// Port of `::initAccociationUseData(individualID)`.
    pub fn new_association_use(individual_id: Cint64) -> Self {
        BackendTempWriteRecord::AssociationUse { individual_id, association_update_id: 0 }
    }

    // ===== CBackendRepresentativeMemoryCacheTemporaryLabelWriteDataLinker =====

    /// Port of `::initLabelWriteData(signature, labelType)`.
    pub fn new_label_write(signature: Cint64, label_type: Cint64) -> Self {
        BackendTempWriteRecord::LabelWrite {
            flags: BackendRepresentativeMemoryCachingFlags::new(), // mStatusFlags = 0
            label_type,
            signature,
            det_value_linker: Vec::new(),
            det_value_count: 0,
            tmp_data: INVALID, // mTmpData = nullptr
        }
    }
    /// Port of `::getSignature` (LabelWrite).
    pub fn get_signature(&self) -> Cint64 {
        if let BackendTempWriteRecord::LabelWrite { signature, .. } = self { *signature } else { 0 }
    }
    /// Port of `::setSignature` (LabelWrite).
    pub fn set_signature(&mut self, signature: Cint64) -> &mut Self {
        if let BackendTempWriteRecord::LabelWrite { signature: s, .. } = self { *s = signature; }
        self
    }
    /// Port of `::appendCacheValueLinker(linker)`
    /// (`while(linkerIt) { ++mDetValueCount; next } mDetValueLinker = linker->append(mDetValueLinker);`).
    pub fn append_cache_value_linker(&mut self, linker: &[LabelValueLinkerId]) -> &mut Self {
        if let BackendTempWriteRecord::LabelWrite { det_value_linker, det_value_count, .. } = self {
            *det_value_count += linker.len() as Cint64;
            let mut new_chain = linker.to_vec();
            new_chain.append(det_value_linker);
            *det_value_linker = new_chain;
        }
        self
    }
    /// Port of `::getCacheValueLinker` (LabelWrite).
    pub fn get_cache_value_linker(&self) -> &[LabelValueLinkerId] {
        if let BackendTempWriteRecord::LabelWrite { det_value_linker, .. } = self { det_value_linker } else { &[] }
    }
    /// Port of `::getCacheValueCount` (LabelWrite).
    pub fn get_cache_value_count(&self) -> Cint64 {
        if let BackendTempWriteRecord::LabelWrite { det_value_count, .. } = self { *det_value_count } else { 0 }
    }
    /// Port of `::getTemporaryData` (opaque `void*`).
    pub fn get_temporary_data(&self) -> Cint64 {
        if let BackendTempWriteRecord::LabelWrite { tmp_data, .. } = self { *tmp_data } else { INVALID }
    }
    /// Port of `::setTemporaryData`.
    pub fn set_temporary_data(&mut self, tmp_data: Cint64) -> &mut Self {
        if let BackendTempWriteRecord::LabelWrite { tmp_data: t, .. } = self { *t = tmp_data; }
        self
    }
    /// Port of `::clearTemporaryData` (`mTmpData = nullptr;`).
    pub fn clear_temporary_data(&mut self) -> &mut Self {
        if let BackendTempWriteRecord::LabelWrite { tmp_data, .. } = self { *tmp_data = INVALID; }
        self
    }
    /// Port of the `getLabelType` of LabelWrite.
    pub fn get_label_type(&self) -> Cint64 {
        if let BackendTempWriteRecord::LabelWrite { label_type, .. } = self { *label_type } else { 0 }
    }

    // ===== CBackendRepresentativeMemoryCacheTemporaryLabelReferenceDataLinker =====

    /// Port of `::initLabelReferenceDataLinker(labelReferenceData)` (`setData(labelReferenceData)`).
    pub fn new_label_reference(label_reference_data: TempLabelReference) -> Self {
        BackendTempWriteRecord::LabelReference(label_reference_data)
    }
    /// Port of `LabelReferenceDataLinker::getReferredTemporaryLabelData` (`getData().getReferredTemporaryLabelData()`).
    pub fn label_reference_get_referred_temporary_label_data(&self) -> BackendTempWriteRecordId {
        if let BackendTempWriteRecord::LabelReference(r) = self { r.get_referred_temporary_label_data() } else { Id::NONE }
    }
    /// Port of `LabelReferenceDataLinker::getReferredLabelData` (`getData().getReferredLabelData()`).
    pub fn label_reference_get_referred_label_data(&self) -> LabelCacheItemId {
        if let BackendTempWriteRecord::LabelReference(r) = self { r.get_referred_label_data() } else { Id::NONE }
    }

    // ===== CBackendRepresentativeMemoryCacheTemporaryCardinalityWriteDataLinker =====

    /// Port of `::initLabelWriteData(labelWriteDataLinker)` (CardinalityWrite).
    pub fn new_cardinality_write(label_write_data_linker: BackendTempWriteRecordId) -> Self {
        BackendTempWriteRecord::CardinalityWrite {
            card_value_linker: Vec::new(),
            card_value_count: 0,
            label_write_data_linker,
        }
    }
    /// Port of `::appendCardinalityCacheValueLinker(linker)`
    /// (`mCardValueCount += linker->getCount(); mCardValueLinker = linker->append(mCardValueLinker);`).
    pub fn append_cardinality_cache_value_linker(&mut self, linker: &[CardinalityValueLinkerId]) -> &mut Self {
        if let BackendTempWriteRecord::CardinalityWrite { card_value_linker, card_value_count, .. } = self {
            *card_value_count += linker.len() as Cint64;
            let mut new_chain = linker.to_vec();
            new_chain.append(card_value_linker);
            *card_value_linker = new_chain;
        }
        self
    }
    /// Port of `::getCardinalityCacheValueLinker`.
    pub fn get_cardinality_cache_value_linker(&self) -> &[CardinalityValueLinkerId] {
        if let BackendTempWriteRecord::CardinalityWrite { card_value_linker, .. } = self { card_value_linker } else { &[] }
    }
    /// Port of `::getCardinalityCacheValueCount`.
    pub fn get_cardinality_cache_value_count(&self) -> Cint64 {
        if let BackendTempWriteRecord::CardinalityWrite { card_value_count, .. } = self { *card_value_count } else { 0 }
    }
    /// Port of `::getLabelWriteDataLinker`.
    pub fn get_label_write_data_linker(&self) -> BackendTempWriteRecordId {
        if let BackendTempWriteRecord::CardinalityWrite { label_write_data_linker, .. } = self { *label_write_data_linker } else { Id::NONE }
    }

    // ===== CBackendRepresentativeMemoryCacheTemporaryIndividualRoleSetNeighbourUpdateDataLinker =====

    /// Port of `::initRoleSetNeighbourUpdateDataLinker(roleSetCombinationLabelRef, neighbourIndi)`
    /// (`setData(neighbourIndi); mRoleSetCombinationLabelRef = roleSetCombinationLabelRef;`).
    pub fn new_individual_role_set_neighbour_update(role_set_combination_label_ref: TempLabelReference, neighbour_indi: Cint64) -> Self {
        BackendTempWriteRecord::IndividualRoleSetNeighbourUpdate {
            individual_reference: neighbour_indi, // the CLinkerBase<CIndividualReference> payload (opaque id).
            role_set_combination_label_ref,
        }
    }
    /// Port of `::getNeighbourRoleInstantiatedCompinationLabelReference`.
    pub fn get_neighbour_role_instantiated_compination_label_reference(&self) -> TempLabelReference {
        if let BackendTempWriteRecord::IndividualRoleSetNeighbourUpdate { role_set_combination_label_ref, .. } = self { *role_set_combination_label_ref } else { TempLabelReference::default() }
    }
    /// Port of `::getNeighbourIndividualReference` (`return getData();`).
    pub fn get_neighbour_individual_reference(&self) -> Cint64 {
        if let BackendTempWriteRecord::IndividualRoleSetNeighbourUpdate { individual_reference, .. } = self { *individual_reference } else { INVALID }
    }

    // ===== CBackendRepresentativeMemoryCacheTemporaryInvolvedIndividualDataLinker =====

    /// Port of `::initInvolvedIndividualData(involvedIndividualIdsLinker)`.
    pub fn new_involved_individual(involved_individual_ids_linker: Vec<Cint64>) -> Self {
        BackendTempWriteRecord::InvolvedIndividual { involved_individual_ids_linker }
    }
    /// Port of `::getInvolvedIndividualIdsLinker`.
    pub fn get_involved_individual_ids_linker(&self) -> &[Cint64] {
        if let BackendTempWriteRecord::InvolvedIndividual { involved_individual_ids_linker, .. } = self { involved_individual_ids_linker } else { &[] }
    }

    // ===== CBackendRepresentativeMemoryCacheTemporaryNominalIndirectConnectionDataLinker =====

    /// Port of `::initNominalIndirectConnectionData(indiID)`.
    pub fn new_nominal_indirect_connection(indi_id: Cint64) -> Self {
        BackendTempWriteRecord::NominalIndirectConnection {
            nominal_indi_id: indi_id,
            last_integration_id: 0,
            indirectly_connected_individual_id_linker: Vec::new(),
            association_update_id: 0,
        }
    }
    /// Port of `::getIndirectlyConnectedIndividualIdLinker` (NominalIndirectConnection).
    pub fn get_indirectly_connected_individual_id_linker(&self) -> &[Cint64] {
        if let BackendTempWriteRecord::NominalIndirectConnection { indirectly_connected_individual_id_linker, .. } = self { indirectly_connected_individual_id_linker } else { &[] }
    }
    /// Port of `::setIndirectlyConnectedIndividualIdLinker` (NominalIndirectConnection).
    pub fn set_indirectly_connected_individual_id_linker(&mut self, indirectly_connected_individual_id_linker: Vec<Cint64>) -> &mut Self {
        if let BackendTempWriteRecord::NominalIndirectConnection { indirectly_connected_individual_id_linker: l, .. } = self { *l = indirectly_connected_individual_id_linker; }
        self
    }
    /// Port of `::addIndirectlyConnectedIndividualIdLinker` (head-front prepend).
    pub fn add_indirectly_connected_individual_id_linker(&mut self, indirectly_connected_individual_id_linker: &[Cint64]) -> &mut Self {
        if let BackendTempWriteRecord::NominalIndirectConnection { indirectly_connected_individual_id_linker: l, .. } = self {
            let mut new_chain = indirectly_connected_individual_id_linker.to_vec();
            new_chain.append(l);
            *l = new_chain;
        }
        self
    }
    /// Port of `::getLastChangeIntegrationId`.
    pub fn get_last_change_integration_id(&self) -> Cint64 {
        if let BackendTempWriteRecord::NominalIndirectConnection { last_integration_id, .. } = self { *last_integration_id } else { 0 }
    }
    /// Port of `::setLastChangeIntegrationId`.
    pub fn set_last_change_integration_id(&mut self, integration_id: Cint64) -> &mut Self {
        if let BackendTempWriteRecord::NominalIndirectConnection { last_integration_id, .. } = self { *last_integration_id = integration_id; }
        self
    }

    // ===== CBackendRepresentativeMemoryCacheTemporaryNominalRoleConnectionData =====

    /// Port of `::initNominalRoleConnectionData(connectionRole, inversedConnection, connectedIndi)`
    /// (`setData(connectionRole); mConnectedIndividual = connectedIndi; mInversedConnection = inversedConnection;`).
    pub fn new_nominal_role_connection(connection_role: Cint64, inversed_connection: bool, connected_indi: Cint64) -> Self {
        BackendTempWriteRecord::NominalRoleConnection {
            role: connection_role, // the CLinkerBase<CRole*> payload (opaque, [api]).
            connected_individual: connected_indi,
            inversed_connection,
        }
    }
    /// Port of `::getConnectionRole` (`return getData();`).
    pub fn get_connection_role(&self) -> Cint64 {
        if let BackendTempWriteRecord::NominalRoleConnection { role, .. } = self { *role } else { INVALID }
    }
    /// Port of `::getConnectedIndividual`.
    pub fn get_connected_individual(&self) -> Cint64 {
        if let BackendTempWriteRecord::NominalRoleConnection { connected_individual, .. } = self { *connected_individual } else { INVALID }
    }
    /// Port of `::isInversedConnection`.
    pub fn is_inversed_connection(&self) -> bool {
        if let BackendTempWriteRecord::NominalRoleConnection { inversed_connection, .. } = self { *inversed_connection } else { false }
    }

    // ===== CBackendRepresentativeMemoryCacheTemporaryPropagationCutDataLinker =====

    /// Port of `::initPropagationCutData(individualID, neighbourArrayIndex, neighbourPropagationCutCursor,
    /// conceptPropagationValue, associationUpdateId, expandedIndividualIdsLinker, propMarkRoleValue)`.
    #[allow(clippy::too_many_arguments)]
    pub fn new_propagation_cut(
        individual_id: Cint64,
        neighbour_array_index: Cint64,
        neighbour_propagation_cut_cursor: Cint64,
        concept_propagation_value: CacheValue,
        association_update_id: Cint64,
        expanded_individual_ids_linker: Vec<Cint64>,
        prop_mark_role_value: CacheValue,
    ) -> Self {
        BackendTempWriteRecord::PropagationCut {
            individual_id,
            association_update_id,
            expanded_individual_ids_linker,
            array_index: neighbour_array_index,
            concept_propagation_value,
            neighbour_propagation_cut_cursor,
            prop_mark_role_value,
            missing_nondeterministic_expansion_propagation: false,
        }
    }
    /// Port of the `getAssociationUpdateId` of PropagationCut.
    pub fn get_association_update_id(&self) -> Cint64 {
        if let BackendTempWriteRecord::PropagationCut { association_update_id, .. } = self { *association_update_id } else { 0 }
    }
    /// Port of `::setAssociationUpdateId` (PropagationCut).
    pub fn set_association_update_id(&mut self, id: Cint64) -> &mut Self {
        if let BackendTempWriteRecord::PropagationCut { association_update_id, .. } = self { *association_update_id = id; }
        self
    }
    /// Port of `::getExpandedIndividualIdsLinker`.
    pub fn get_expanded_individual_ids_linker(&self) -> &[Cint64] {
        if let BackendTempWriteRecord::PropagationCut { expanded_individual_ids_linker, .. } = self { expanded_individual_ids_linker } else { &[] }
    }
    /// Port of `::getArrayIndex`.
    pub fn get_array_index(&self) -> Cint64 {
        if let BackendTempWriteRecord::PropagationCut { array_index, .. } = self { *array_index } else { 0 }
    }
    /// Port of `::getConceptPropagationValue`.
    pub fn get_concept_propagation_value(&self) -> CacheValue {
        if let BackendTempWriteRecord::PropagationCut { concept_propagation_value, .. } = self { *concept_propagation_value } else { CacheValue::default() }
    }
    /// Port of `::getNeighbourPropagationCutCursor`.
    pub fn get_neighbour_propagation_cut_cursor(&self) -> Cint64 {
        if let BackendTempWriteRecord::PropagationCut { neighbour_propagation_cut_cursor, .. } = self { *neighbour_propagation_cut_cursor } else { 0 }
    }
    /// Port of `::getPropagationMarkingRoleValue`.
    pub fn get_propagation_marking_role_value(&self) -> CacheValue {
        if let BackendTempWriteRecord::PropagationCut { prop_mark_role_value, .. } = self { *prop_mark_role_value } else { CacheValue::default() }
    }
    /// Port of `::isMissingNondeterministicExpansionPropagation`.
    pub fn is_missing_nondeterministic_expansion_propagation(&self) -> bool {
        if let BackendTempWriteRecord::PropagationCut { missing_nondeterministic_expansion_propagation, .. } = self { *missing_nondeterministic_expansion_propagation } else { false }
    }
    /// Port of `::setMissingNondeterministicExpansionPropagation`.
    pub fn set_missing_nondeterministic_expansion_propagation(&mut self, missing_prop: bool) -> &mut Self {
        if let BackendTempWriteRecord::PropagationCut { missing_nondeterministic_expansion_propagation, .. } = self { *missing_nondeterministic_expansion_propagation = missing_prop; }
        self
    }
}
