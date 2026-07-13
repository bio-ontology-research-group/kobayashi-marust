//! `cache::satnode` — F5: the saturation-node associated-expansion cache
//! (Konclude `Reasoner/Kernel/Cache/CSaturationNode*` + the
//! `CSaturationNodeAssociatedExpansionCache*` family).
//!
//! The saturation pre-pass cache: per-saturation-node associated concept
//! expansions (deterministic / nondeterministic), driven by
//! `CSaturationNodeExpansionCacheHandler`. Struct-definition wave only — every
//! class becomes a Rust struct with faithful fields; method bodies are deferred
//! (the `// W6-CACHE method-batch` marker). `new`/`Default` are provided.
//!
//! Port conventions (PORT.md §5, §6; manifest/07-cache.md):
//!   * `CXxx*` pointer  → typed arena `Id<T>` (`Id::NONE` == `nullptr`);
//!   * intrusive `*Linker` chain → owned `Vec<Id>` (head-at-FRONT);
//!   * `QMutex` / `CThread` machinery → opaque `Cint64` `[threading]`;
//!   * `CMemory*` pool allocators / providers → opaque `Cint64` `[memory-pool]`;
//!   * cross-family F0 refs not yet ported (`CCacheValue`, `CCacheValueHasher`,
//!     `CCacheEntry`, `CCacheStatistics`, `CCacheEntryWriteData`,
//!     `CComputedConsequencesCachingData`, the saturation status-update linker)
//!     → opaque `Cint64`, marked `[api]`/`[unclear]`;
//!   * the F0 family base `CSaturationCache` is already ported in `cache::base`.
//!
//! KONCLUDE-PORT-NOTE[unclear]: `CCacheValue` (an `F0` shared key = `CTrible<i64>`
//! + identifier) is referenced pervasively here (concept-linker payload, hash
//! key). Per the manifest's CORE-vs-DEEP split it is ported once in the (not-yet-
//! written) `cache::value`; until then every `CCacheValue` is an opaque `Cint64`
//! handle. Re-thread to the real `CacheValue` on the F0 reconcile.

#![allow(dead_code)]

use std::collections::HashMap;

use super::super::model::substrate::{Cint64, Id, INVALID};
use super::super::process::context::ProcessContext;
use super::super::process::sat_node::IndividualSaturationProcessNodeStatusFlags;
use super::super::process::SatNodeId;
use super::base::SaturationCache;
use super::context::CacheContext;
use super::value::{CacheValue, CacheValueIdentifier};

// ---------------------------------------------------------------------------
// Local arena id aliases (this family's per-ontology cache objects).
// ---------------------------------------------------------------------------
/// `CSaturationNodeAssociatedExpansionCache*`            → `SatExpansionCacheId`.
pub type SatExpansionCacheId = Id<SaturationNodeAssociatedExpansionCache>;
/// `CSaturationNodeAssociatedExpansionCacheReader*`      → `SatExpansionCacheReaderId`.
pub type SatExpansionCacheReaderId = Id<SaturationNodeAssociatedExpansionCacheReader>;
/// `CSaturationNodeAssociatedExpansionCacheEntry*`       → `SatExpansionCacheEntryId`.
pub type SatExpansionCacheEntryId = Id<SaturationNodeAssociatedExpansionCacheEntry>;
/// `CSaturationNodeCacheUpdater*`                        → `SaturationNodeCacheUpdaterId`.
pub type SaturationNodeCacheUpdaterId = Id<SaturationNodeCacheUpdater>;
/// the determinism-tagged expansion record               → `AssociatedConceptExpansionId`.
pub type AssociatedConceptExpansionId = Id<AssociatedConceptExpansion>;
/// `CSaturationNodeAssociatedConceptLinker*`             → `AssociatedConceptLinkerId`.
pub type AssociatedConceptLinkerId = Id<SaturationNodeAssociatedConceptLinker>;
/// `CSaturationNodeAssociatedDependentNominalSet*`       → `DependentNominalSetId`.
pub type DependentNominalSetId = Id<SaturationNodeAssociatedDependentNominalSet>;

// ===========================================================================
// CSaturationNodeAssociatedExpansionCacheContext  (`: public CContext`)
// ===========================================================================

/// Port of `CSaturationNodeAssociatedExpansionCacheContext`.
///
/// Per-thread scratch + pool for the saturation-node expansion cache. `CContext`
/// base carries no port-relevant data.
pub struct SaturationNodeAssociatedExpansionCacheContext {
    /// `CMemoryPoolAllocationManager* mMemMan`.
    /// KONCLUDE-PORT-NOTE[memory-pool]: opaque handle; the arena substrate replaces it.
    pub mem_man: Cint64,
    /// `CNewAllocationMemoryPoolProvider* mMemoryPoolProvider`.
    /// KONCLUDE-PORT-NOTE[memory-pool]: opaque pool-provider handle.
    pub memory_pool_provider: Cint64,
    /// `CIndividualSaturationProcessNodeStatusUpdateLinker* mConSatUpdateLinker`
    /// (intrusive chain head).
    /// KONCLUDE-PORT-NOTE[api]: the status-update linker class is a Process-layer
    /// type not yet ported and with no `Id` alias; kept as an opaque `Cint64`
    /// chain head (`INVALID` == empty/`nullptr`).
    pub con_sat_update_linker: Cint64,
    /// `cint64 mAddRelMemory`.
    pub add_rel_memory: Cint64,
}

impl Default for SaturationNodeAssociatedExpansionCacheContext {
    fn default() -> Self {
        SaturationNodeAssociatedExpansionCacheContext {
            mem_man: INVALID,
            memory_pool_provider: INVALID,
            con_sat_update_linker: INVALID,
            add_rel_memory: 0,
        }
    }
}

impl SaturationNodeAssociatedExpansionCacheContext {
    /// Port of `CSaturationNodeAssociatedExpansionCacheContext::CSaturationNodeAssociatedExpansionCacheContext`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `getMemoryPoolAllocationManager`.
    /// KONCLUDE-PORT-NOTE[memory-pool]: opaque allocation-manager handle.
    pub fn get_memory_pool_allocation_manager(&self) -> Cint64 {
        self.mem_man
    }

    /// Port of `getMemoryAllocationManager` (returns the same `mMemMan`).
    /// KONCLUDE-PORT-NOTE[memory-pool]: opaque allocation-manager handle.
    pub fn get_memory_allocation_manager(&self) -> Cint64 {
        self.mem_man
    }

    /// Port of `getMemoryPoolProvider`.
    /// KONCLUDE-PORT-NOTE[memory-pool]: opaque pool-provider handle.
    pub fn get_memory_pool_provider(&self) -> Cint64 {
        self.memory_pool_provider
    }

    /// Port of `getMemoryConsumption`.
    pub fn get_memory_consumption(&self) -> Cint64 {
        // W6-DEFER[memory-pool]: the C++ adds
        // `mMemoryPoolProvider->getAllocatedReleaseDifferencePoolSize()`; the pool
        // provider is an opaque handle in this staged port, so only the accumulated
        // released-pool memory (`mAddRelMemory`) is returned.
        self.add_rel_memory
    }

    /// Port of `releaseTemporaryMemoryPools`.
    pub fn release_temporary_memory_pools(&mut self, memory_pools: Cint64) -> &mut Self {
        // W6-DEFER[memory-pool]: the C++ walks the `CMemoryPool` chain
        //   for (it = memoryPools; it; it = it->getNext()) mAddRelMemory += it->getMemoryBlockSize();
        // then `mMemMan->releaseTemporaryMemoryPools(memoryPools)`. The pool chain
        // and allocation manager are opaque handles here.
        let _ = memory_pools;
        self
    }

    /// Port of `getIndividualSaturationUpdateLinker`.
    pub fn get_individual_saturation_update_linker(&mut self, create: bool) -> Cint64 {
        // W6-DEFER[api]: `CIndividualSaturationProcessNodeStatusUpdateLinker` is a
        // Process-layer type with no `Id` alias; the recycling chain head
        // (`mConSatUpdateLinker`) is the opaque `con_sat_update_linker` handle.
        // Faithful logic: pull the head linker (allocating a fresh one when the
        // chain is empty and `create`), `clearNext()` it, and advance the chain head.
        let _ = create;
        self.con_sat_update_linker
    }

    /// Port of `addIndividualSaturationUpdateLinker`.
    pub fn add_individual_saturation_update_linker(&mut self, linker: Cint64) -> &mut Self {
        // W6-DEFER[api]: faithful logic prepends `linker` (after `clearNext()`) onto
        // the opaque `mConSatUpdateLinker` recycling chain head.
        let _ = linker;
        self
    }
}

// ===========================================================================
// CSaturationNodeAssociatedConceptLinker  (`: CLinkerBase<CCacheValue, ...>`)
// ===========================================================================

/// Port of `CSaturationNodeAssociatedConceptLinker`.
///
/// An intrusive linker whose payload is a `CCacheValue` (the cached concept/role
/// key). KONCLUDE-PORT-NOTE[ownership]: the `CLinkerBase` next-pointer is dropped;
/// the owning chain is an `AssociatedConceptLinkerId` `Vec` on the holder.
pub struct SaturationNodeAssociatedConceptLinker {
    /// `CCacheValue` payload (the linker data).
    pub cache_value: CacheValue,
}

impl Default for SaturationNodeAssociatedConceptLinker {
    fn default() -> Self {
        SaturationNodeAssociatedConceptLinker {
            cache_value: CacheValue::new(),
        }
    }
}

impl SaturationNodeAssociatedConceptLinker {
    /// Port of `CSaturationNodeAssociatedConceptLinker::CSaturationNodeAssociatedConceptLinker`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `initConceptLinker` (C++ `setData(cacheValue)`).
    pub fn init_concept_linker(&mut self, cache_value: CacheValue) -> &mut Self {
        self.cache_value = cache_value;
        self
    }

    /// Port of `setCacheValue` (C++ `setData(cacheValue)`).
    pub fn set_cache_value(&mut self, cache_value: CacheValue) -> &mut Self {
        self.cache_value = cache_value;
        self
    }

    /// Port of `getCacheValue` (C++ `return &getData()`).
    pub fn get_cache_value(&self) -> CacheValue {
        self.cache_value
    }
}

// ===========================================================================
// CSaturationNodeAssociatedDependentNominalSet  (`: public CCACHINGSET<cint64>`)
// ===========================================================================

/// Port of `CSaturationNodeAssociatedDependentNominalSet`.
///
/// The set of nominal ids a concept expansion depends on. KONCLUDE-PORT-NOTE
/// [memory-pool]: the `CCACHINGSET<cint64>` base (a pool-managed, bulk-resettable
/// concurrent-modification set) becomes an owned `Vec<Cint64>` of nominal ids.
pub struct SaturationNodeAssociatedDependentNominalSet {
    /// the `CCACHINGSET<cint64>` base contents — the dependent nominal ids.
    pub nominal_set: Vec<Cint64>,
    /// `CContext* mContext`. KONCLUDE-PORT-NOTE[ownership]: opaque back-pointer to
    /// the ambient cache context (`INVALID` == `nullptr`).
    pub context: Cint64,
}

impl Default for SaturationNodeAssociatedDependentNominalSet {
    fn default() -> Self {
        SaturationNodeAssociatedDependentNominalSet {
            nominal_set: Vec::new(),
            context: INVALID,
        }
    }
}

impl SaturationNodeAssociatedDependentNominalSet {
    /// Port of `CSaturationNodeAssociatedDependentNominalSet::CSaturationNodeAssociatedDependentNominalSet`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `initDependentNominalSet` (C++ returns `this` with no state change).
    pub fn init_dependent_nominal_set(&mut self) -> &mut Self {
        self
    }

    /// `CCACHINGSET<cint64>::insert` (the set base op the cache facade calls on
    /// this set). KONCLUDE-PORT-NOTE[memory-pool]: set semantics over the owned
    /// `Vec<Cint64>` (no duplicate nominal ids).
    pub fn insert(&mut self, nominal_id: Cint64) -> &mut Self {
        if !self.nominal_set.contains(&nominal_id) {
            self.nominal_set.push(nominal_id);
        }
        self
    }

    /// `CCACHINGSET<cint64>::isEmpty`.
    pub fn is_empty(&self) -> bool {
        self.nominal_set.is_empty()
    }
}

// ===========================================================================
// CSaturationNodeAssociated{,Deterministic,Nondeterministic}ConceptExpansion
//   → ONE determinism-tagged enum (mirrors the W2 `DepKind` collapse).
// ===========================================================================

/// Determinism tag for `AssociatedConceptExpansion`.
///
/// KONCLUDE-PORT-NOTE[api]: collapses the three C++ classes
/// `CSaturationNodeAssociatedConceptExpansion` (base / "plain"),
/// `CSaturationNodeAssociatedDeterministicConceptExpansion`, and
/// `CSaturationNodeAssociatedNondeterministicConceptExpansion` into one record
/// distinguished by this tag (per manifest/07-cache.md record-family collapse).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum AssociatedConceptExpansionKind {
    /// `CSaturationNodeAssociatedConceptExpansion` (the plain base record).
    Concept,
    /// `CSaturationNodeAssociatedDeterministicConceptExpansion`.
    Deterministic,
    /// `CSaturationNodeAssociatedNondeterministicConceptExpansion`
    /// (also a `CLinkerBase` chain element on the entry).
    Nondeterministic,
}

impl Default for AssociatedConceptExpansionKind {
    fn default() -> Self {
        AssociatedConceptExpansionKind::Concept
    }
}

/// Port of the `CSaturationNodeAssociatedConceptExpansion` hierarchy (base +
/// deterministic + nondeterministic), folded into one tagged record.
///
/// Fields up to `context` are the `CSaturationNodeAssociatedConceptExpansion`
/// base members; `requires_non_deterministic_expansion` is the lone
/// `Deterministic` subclass member (meaningful only when
/// `kind == Deterministic`); the `Nondeterministic` subclass adds no data of its
/// own (only the `CLinkerBase` chaining, owned by the holding `Vec`).
pub struct AssociatedConceptExpansion {
    /// which of the three C++ classes this record stands for.
    pub kind: AssociatedConceptExpansionKind,

    // --- CSaturationNodeAssociatedConceptExpansion base members ---------------
    /// `CCACHINGHASH<CCacheValueHasher, CSaturationNodeAssociatedConceptLinker*> mConceptExpansionHash`.
    /// KONCLUDE-PORT-NOTE[memory-pool]: the pool-managed hash → `HashMap`; key is
    /// the `CCacheValue` payload, value the concept-linker id.
    pub concept_expansion_hash: HashMap<CacheValue, AssociatedConceptLinkerId>,
    /// `CSaturationNodeAssociatedConceptLinker* mConceptExpansionLinker`
    /// (intrusive chain head → owned `Vec`, head-at-FRONT).
    pub concept_expansion_linker: Vec<AssociatedConceptLinkerId>,
    /// `cint64 mConceptExpansionCount`.
    pub concept_expansion_count: Cint64,
    /// `CSaturationNodeAssociatedDependentNominalSet* mDependentNominalSet`.
    pub dependent_nominal_set: DependentNominalSetId,
    /// `bool mHasTightCardinalityRestriction`.
    pub has_tight_cardinality_restriction: bool,
    /// `cint64 mConceptSetSignature`.
    pub concept_set_signature: Cint64,
    /// `cint64 mTotalConceptCount`.
    pub total_concept_count: Cint64,
    /// `CSaturationNodeAssociatedExpansionCacheContext* mContext`.
    /// KONCLUDE-PORT-NOTE[ownership]: opaque back-pointer to the cache context.
    pub context: Cint64,

    // --- CSaturationNodeAssociatedDeterministicConceptExpansion member -------
    /// `bool mRequiresNonDeterministicExpansion` (Deterministic subclass only).
    pub requires_non_deterministic_expansion: bool,
}

impl Default for AssociatedConceptExpansion {
    fn default() -> Self {
        AssociatedConceptExpansion {
            kind: AssociatedConceptExpansionKind::Concept,
            concept_expansion_hash: HashMap::new(),
            concept_expansion_linker: Vec::new(),
            concept_expansion_count: 0,
            dependent_nominal_set: Id::NONE,
            has_tight_cardinality_restriction: false,
            concept_set_signature: INVALID,
            total_concept_count: 0,
            context: INVALID,
            requires_non_deterministic_expansion: false,
        }
    }
}

impl AssociatedConceptExpansion {
    /// Port of the `CSaturationNodeAssociated*ConceptExpansion(context)` ctors;
    /// `kind` selects which C++ class is being constructed.
    pub fn new(kind: AssociatedConceptExpansionKind, context: Cint64) -> Self {
        AssociatedConceptExpansion {
            kind,
            context,
            ..Default::default()
        }
    }

    // --- CSaturationNodeAssociatedConceptExpansion base methods ---------------

    /// Port of `initConceptExpansion`.
    /// KONCLUDE-PORT-NOTE[api]: the C++ ctor builds `mConceptExpansionHash` from the
    /// context and `init` does not touch it, so the hash is left intact here.
    pub fn init_concept_expansion(&mut self) -> &mut Self {
        self.concept_expansion_linker.clear();
        self.has_tight_cardinality_restriction = false;
        self.concept_expansion_count = 0;
        self.dependent_nominal_set = Id::NONE;
        self.concept_set_signature = 0;
        self.total_concept_count = 0;
        self
    }

    /// Port of `getConceptExpansionHash`.
    pub fn get_concept_expansion_hash(
        &mut self,
    ) -> &mut HashMap<CacheValue, AssociatedConceptLinkerId> {
        &mut self.concept_expansion_hash
    }

    /// Port of `addConceptExpansionLinker`.
    pub fn add_concept_expansion_linker(
        &mut self,
        concept_linker: AssociatedConceptLinkerId,
        context: &CacheContext,
    ) -> &mut Self {
        if concept_linker.is_none() {
            return self;
        }
        let cache_value = context
            .associated_concept_linker(concept_linker)
            .get_cache_value();
        self.concept_expansion_count += 1;
        self.concept_expansion_linker.insert(0, concept_linker);
        self.concept_expansion_hash
            .insert(cache_value, concept_linker);
        self
    }

    /// Port of `getConceptExpansionLinker(CCacheValue*)` — the hash lookup overload.
    pub fn get_concept_expansion_linker_for_cache_value(
        &self,
        cache_value: CacheValue,
    ) -> AssociatedConceptLinkerId {
        self.concept_expansion_hash
            .get(&cache_value)
            .copied()
            .unwrap_or(Id::NONE)
    }

    /// Port of `hasConceptExpansionLinker(CCacheValue*)`.
    pub fn has_concept_expansion_linker(&self, cache_value: CacheValue) -> bool {
        self.concept_expansion_hash.contains_key(&cache_value)
    }

    /// Port of `getConceptExpansionLinker()` — the chain-head overload (head→tail).
    pub fn get_concept_expansion_linker(&self) -> &[AssociatedConceptLinkerId] {
        &self.concept_expansion_linker
    }

    /// Port of `getConceptExpansionCount`.
    pub fn get_concept_expansion_count(&self) -> Cint64 {
        self.concept_expansion_count
    }

    /// Port of `setConceptExpansionCount`.
    pub fn set_concept_expansion_count(&mut self, count: Cint64) -> &mut Self {
        self.concept_expansion_count = count;
        self
    }

    /// Port of `getDependentNominalSet(bool create)`.
    ///
    /// W6-UNDEFER (cache-arena): when absent and `create`, bump-allocates a
    /// `CSaturationNodeAssociatedDependentNominalSet` from the cache pool and
    /// `init`s it (`mDependentNominalSet = allocateAndConstructAndParameterize<…>;
    /// mDependentNominalSet->initDependentNominalSet();`).
    pub fn get_dependent_nominal_set(
        &mut self,
        create: bool,
        ctx: &mut CacheContext,
    ) -> DependentNominalSetId {
        if self.dependent_nominal_set.is_none() && create {
            let mut set = SaturationNodeAssociatedDependentNominalSet::new();
            set.init_dependent_nominal_set();
            self.dependent_nominal_set = ctx.alloc_dependent_nominal_set(set);
        }
        self.dependent_nominal_set
    }

    /// Port of `getHasTightAtMostRestriction`.
    pub fn get_has_tight_at_most_restriction(&self) -> bool {
        self.has_tight_cardinality_restriction
    }

    /// Port of `setHasTightCardinalityRestriction`.
    pub fn set_has_tight_cardinality_restriction(
        &mut self,
        tight_at_most_restrictions: bool,
    ) -> &mut Self {
        self.has_tight_cardinality_restriction = tight_at_most_restrictions;
        self
    }

    /// Port of `getConceptSetSignature`.
    pub fn get_concept_set_signature(&self) -> Cint64 {
        self.concept_set_signature
    }

    /// Port of `setConceptSetSignature`.
    pub fn set_concept_set_signature(&mut self, signature: Cint64) -> &mut Self {
        self.concept_set_signature = signature;
        self
    }

    /// Port of `getTotalConceptCount`.
    pub fn get_total_concept_count(&self) -> Cint64 {
        self.total_concept_count
    }

    /// Port of `setTotalConceptCount`.
    pub fn set_total_concept_count(&mut self, total_concept_count: Cint64) -> &mut Self {
        self.total_concept_count = total_concept_count;
        self
    }

    // --- CSaturationNodeAssociatedDeterministicConceptExpansion methods -------

    /// Port of `initDeterministicConceptExpansion`
    /// (C++ chains `CSaturationNodeAssociatedConceptExpansion::initConceptExpansion`).
    pub fn init_deterministic_concept_expansion(&mut self) -> &mut Self {
        self.init_concept_expansion();
        self.requires_non_deterministic_expansion = false;
        self
    }

    /// Port of `requiresNonDeterministicExpansion`.
    pub fn requires_non_deterministic_expansion(&self) -> bool {
        self.requires_non_deterministic_expansion
    }

    /// Port of `setNonDeterministicExpansionRequired`.
    pub fn set_non_deterministic_expansion_required(
        &mut self,
        nondeterministic_expansion_required: bool,
    ) -> &mut Self {
        self.requires_non_deterministic_expansion = nondeterministic_expansion_required;
        self
    }

    // --- CSaturationNodeAssociatedNondeterministicConceptExpansion methods ----

    /// Port of `initNondeterministicConceptExpansion`
    /// (C++ chains `CSaturationNodeAssociatedConceptExpansion::initConceptExpansion`).
    pub fn init_nondeterministic_concept_expansion(&mut self) -> &mut Self {
        self.init_concept_expansion();
        self
    }
}

// ===========================================================================
// CSaturationNodeAssociatedExpansionCacheWriteData  (`: CCacheEntryWriteData`)
//   + the two derived write-data records (Expansion / Unsatisfiability).
// ===========================================================================

/// Port of the C++ `enum SATURATIONNODEASSOCIATEDEXPANSIONCACHEWRITEDATATYPE`.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum SaturationNodeAssociatedExpansionCacheWriteDataType {
    /// `SNAECWT_UNSAT = 1`.
    Unsat = 1,
    /// `SNAECWT_EXPAND = 2`.
    Expand = 2,
}

impl Default for SaturationNodeAssociatedExpansionCacheWriteDataType {
    fn default() -> Self {
        SaturationNodeAssociatedExpansionCacheWriteDataType::Unsat
    }
}

/// Port of `CSaturationNodeAssociatedExpansionCacheWriteData`
/// (`: public CCacheEntryWriteData`).
pub struct SaturationNodeAssociatedExpansionCacheWriteData {
    /// `CCacheEntryWriteData` base (F0).
    /// KONCLUDE-PORT-NOTE[api]: not-yet-ported F0 base; it carries a
    /// `CACHEWRITEDATATYPE mType` enum + a `CLinkerBase` next-pointer — kept as an
    /// opaque `Cint64` handle until F0 `cache::value` lands.
    pub entry_write_data_base: Cint64,
    /// `SATURATIONNODEASSOCIATEDEXPANSIONCACHEWRITEDATATYPE mWriteDataType`.
    pub write_data_type: SaturationNodeAssociatedExpansionCacheWriteDataType,
}

impl Default for SaturationNodeAssociatedExpansionCacheWriteData {
    fn default() -> Self {
        SaturationNodeAssociatedExpansionCacheWriteData {
            entry_write_data_base: INVALID,
            write_data_type: SaturationNodeAssociatedExpansionCacheWriteDataType::default(),
        }
    }
}

impl SaturationNodeAssociatedExpansionCacheWriteData {
    /// Port of `CSaturationNodeAssociatedExpansionCacheWriteData::CSaturationNodeAssociatedExpansionCacheWriteData`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `getWriteDataType`.
    pub fn get_write_data_type(&self) -> SaturationNodeAssociatedExpansionCacheWriteDataType {
        self.write_data_type
    }
}

/// Port of `CSaturationNodeAssociatedExpansionCacheExpansionWriteData`
/// (`: public CSaturationNodeAssociatedExpansionCacheWriteData`).
pub struct SaturationNodeAssociatedExpansionCacheExpansionWriteData {
    /// inlined `CSaturationNodeAssociatedExpansionCacheWriteData` base.
    pub base: SaturationNodeAssociatedExpansionCacheWriteData,
    /// `CIndividualSaturationProcessNode* mSaturationNode`.
    pub saturation_node: SatNodeId,
    /// `bool mTightAtMostRestriction`.
    pub tight_at_most_restriction: bool,
    /// `bool mDeterministicExpansion`.
    pub deterministic_expansion: bool,
    /// `bool mRequiresNondeterministicExpansion`.
    pub requires_nondeterministic_expansion: bool,
    /// `cint64 mConceptSetSignature`.
    pub concept_set_signature: Cint64,
    /// `cint64 mTotalConceptCount`.
    pub total_concept_count: Cint64,
    /// `CSaturationNodeAssociatedDependentNominalSet* mDependentNominalSet`.
    pub dependent_nominal_set: DependentNominalSetId,
    /// `CSaturationNodeAssociatedConceptLinker* mExpansionConceptLinker`
    /// (intrusive chain head → owned `Vec`, head-at-FRONT).
    pub expansion_concept_linker: Vec<AssociatedConceptLinkerId>,
}

impl Default for SaturationNodeAssociatedExpansionCacheExpansionWriteData {
    fn default() -> Self {
        SaturationNodeAssociatedExpansionCacheExpansionWriteData {
            base: SaturationNodeAssociatedExpansionCacheWriteData {
                write_data_type: SaturationNodeAssociatedExpansionCacheWriteDataType::Expand,
                ..Default::default()
            },
            saturation_node: Id::NONE,
            tight_at_most_restriction: false,
            deterministic_expansion: false,
            requires_nondeterministic_expansion: false,
            concept_set_signature: INVALID,
            total_concept_count: 0,
            dependent_nominal_set: Id::NONE,
            expansion_concept_linker: Vec::new(),
        }
    }
}

impl SaturationNodeAssociatedExpansionCacheExpansionWriteData {
    /// Port of `CSaturationNodeAssociatedExpansionCacheExpansionWriteData::CSaturationNodeAssociatedExpansionCacheExpansionWriteData`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `initExpansionWriteData`.
    /// KONCLUDE-PORT-NOTE[ownership]: the C++ `conLinker` chain head becomes the
    /// owned `expansion_concept_linker` `Vec` (head→tail), per the CLinker convention.
    pub fn init_expansion_write_data(
        &mut self,
        saturation_node: SatNodeId,
        con_linker: Vec<AssociatedConceptLinkerId>,
    ) -> &mut Self {
        self.saturation_node = saturation_node;
        self.expansion_concept_linker = con_linker;
        self.dependent_nominal_set = Id::NONE;
        self.tight_at_most_restriction = false;
        self.deterministic_expansion = true;
        self.requires_nondeterministic_expansion = false;
        self.concept_set_signature = 0;
        self.total_concept_count = 0;
        self
    }

    /// Port of `getSaturationIndividualNode`.
    pub fn get_saturation_individual_node(&self) -> SatNodeId {
        self.saturation_node
    }

    /// Port of `getDependentNominalSet`.
    pub fn get_dependent_nominal_set(&self) -> DependentNominalSetId {
        self.dependent_nominal_set
    }

    /// Port of `setDependentNominalSet`.
    pub fn set_dependent_nominal_set(&mut self, dep_nom_set: DependentNominalSetId) -> &mut Self {
        self.dependent_nominal_set = dep_nom_set;
        self
    }

    /// Port of `getExpansionConceptLinker` (chain head → slice, head→tail).
    pub fn get_expansion_concept_linker(&self) -> &[AssociatedConceptLinkerId] {
        &self.expansion_concept_linker
    }

    /// Port of `hasTightAtMostRestriction`.
    pub fn has_tight_at_most_restriction(&self) -> bool {
        self.tight_at_most_restriction
    }

    /// Port of `setTightAtMostRestriction`.
    pub fn set_tight_at_most_restriction(&mut self, tight_at_most_restriction: bool) -> &mut Self {
        self.tight_at_most_restriction = tight_at_most_restriction;
        self
    }

    /// Port of `isDeterministicExpansion`.
    pub fn is_deterministic_expansion(&self) -> bool {
        self.deterministic_expansion
    }

    /// Port of `setDeterministicExpansion`.
    pub fn set_deterministic_expansion(&mut self, det_expansion: bool) -> &mut Self {
        self.deterministic_expansion = det_expansion;
        self
    }

    /// Port of `requiresNondeterministicExpansion`.
    pub fn requires_nondeterministic_expansion(&self) -> bool {
        self.requires_nondeterministic_expansion
    }

    /// Port of `setRequiresNondeterministicExpansion`.
    pub fn set_requires_nondeterministic_expansion(
        &mut self,
        requiresnondet_expansion: bool,
    ) -> &mut Self {
        self.requires_nondeterministic_expansion = requiresnondet_expansion;
        self
    }

    /// Port of `getConceptSetSignature`.
    pub fn get_concept_set_signature(&self) -> Cint64 {
        self.concept_set_signature
    }

    /// Port of `setConceptSetSignature`.
    pub fn set_concept_set_signature(&mut self, signature: Cint64) -> &mut Self {
        self.concept_set_signature = signature;
        self
    }

    /// Port of `getTotalConceptCount`.
    pub fn get_total_concept_count(&self) -> Cint64 {
        self.total_concept_count
    }

    /// Port of `setTotalConceptCount`.
    pub fn set_total_concept_count(&mut self, concept_count: Cint64) -> &mut Self {
        self.total_concept_count = concept_count;
        self
    }
}

/// Port of `CSaturationNodeAssociatedExpansionCacheUnsatisfiabilityWriteData`
/// (`: public CSaturationNodeAssociatedExpansionCacheWriteData`).
pub struct SaturationNodeAssociatedExpansionCacheUnsatisfiabilityWriteData {
    /// inlined `CSaturationNodeAssociatedExpansionCacheWriteData` base.
    pub base: SaturationNodeAssociatedExpansionCacheWriteData,
    /// `CIndividualSaturationProcessNode* mUnsatisfiableNode`.
    pub unsatisfiable_node: SatNodeId,
}

impl Default for SaturationNodeAssociatedExpansionCacheUnsatisfiabilityWriteData {
    fn default() -> Self {
        SaturationNodeAssociatedExpansionCacheUnsatisfiabilityWriteData {
            base: SaturationNodeAssociatedExpansionCacheWriteData {
                write_data_type: SaturationNodeAssociatedExpansionCacheWriteDataType::Unsat,
                ..Default::default()
            },
            unsatisfiable_node: Id::NONE,
        }
    }
}

impl SaturationNodeAssociatedExpansionCacheUnsatisfiabilityWriteData {
    /// Port of `CSaturationNodeAssociatedExpansionCacheUnsatisfiabilityWriteData::CSaturationNodeAssociatedExpansionCacheUnsatisfiabilityWriteData`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `initUnsatisfiabilityWriteData`.
    pub fn init_unsatisfiability_write_data(&mut self, unsatisfiable_node: SatNodeId) -> &mut Self {
        self.unsatisfiable_node = unsatisfiable_node;
        self
    }

    /// Port of `getUnsatisfiableSaturationIndividualNode`.
    pub fn get_unsatisfiable_saturation_individual_node(&self) -> SatNodeId {
        self.unsatisfiable_node
    }
}

/// Typed write-data record for the staged Rust drain of
/// `CSaturationNodeAssociatedExpansionCacheWriteData*` chains.
///
/// Konclude uses an intrusive base-class chain and downcasts by
/// `getWriteDataType()`. The port keeps the two concrete payloads in an enum for
/// typed dispatch while the legacy opaque `Cint64` compatibility methods remain
/// deferred.
pub enum SaturationNodeAssociatedExpansionCacheWriteDataRecord {
    /// `SNAECWT_UNSAT`.
    Unsat(SaturationNodeAssociatedExpansionCacheUnsatisfiabilityWriteData),
    /// `SNAECWT_EXPAND`.
    Expand(SaturationNodeAssociatedExpansionCacheExpansionWriteData),
}

impl SaturationNodeAssociatedExpansionCacheWriteDataRecord {
    /// Port of `getWriteDataType` on the base write-data pointer.
    pub fn get_write_data_type(&self) -> SaturationNodeAssociatedExpansionCacheWriteDataType {
        match self {
            Self::Unsat(_) => SaturationNodeAssociatedExpansionCacheWriteDataType::Unsat,
            Self::Expand(_) => SaturationNodeAssociatedExpansionCacheWriteDataType::Expand,
        }
    }
}

// ===========================================================================
// CSaturationNodeAssociatedExpansionCacheEntry
//   (`: public CIndividualSaturationProcessNodeCacheData, public CCacheEntry`)
// ===========================================================================

/// Port of `CSaturationNodeAssociatedExpansionCacheEntry`.
///
/// KONCLUDE-PORT-NOTE[api]: both base classes contribute no port-relevant fields
/// here — `CCacheEntry` is empty, and `CIndividualSaturationProcessNodeCacheData`
/// is a Process-layer cache-data marker (process::stubs); its identity is kept via
/// the `cache_data_base` opaque handle.
pub struct SaturationNodeAssociatedExpansionCacheEntry {
    /// the `CIndividualSaturationProcessNodeCacheData` base (Process-layer stub).
    /// KONCLUDE-PORT-NOTE[api]: opaque handle (the stub has no ported fields).
    pub cache_data_base: Cint64,
    /// `CSaturationNodeAssociatedExpansionCacheContext* mContext`.
    /// KONCLUDE-PORT-NOTE[ownership]: opaque back-pointer to the cache context.
    pub context: Cint64,
    /// `CIndividualSaturationProcessNode* mSaturationNode`.
    pub saturation_node: SatNodeId,
    /// `cint64 mRemainingAllowedNonDetExpansionCount`.
    pub remaining_allowed_non_det_expansion_count: Cint64,
    /// `CSaturationNodeAssociatedDeterministicConceptExpansion* mDetExpansion`
    /// (the determinism-tagged record, `kind == Deterministic`).
    pub det_expansion: AssociatedConceptExpansionId,
    /// `CSaturationNodeAssociatedNondeterministicConceptExpansion* mNondetExpansionLinker`
    /// (intrusive chain head → owned `Vec`, head-at-FRONT; each `kind == Nondeterministic`).
    pub nondet_expansion_linker: Vec<AssociatedConceptExpansionId>,
}

impl Default for SaturationNodeAssociatedExpansionCacheEntry {
    fn default() -> Self {
        SaturationNodeAssociatedExpansionCacheEntry {
            cache_data_base: INVALID,
            context: INVALID,
            saturation_node: Id::NONE,
            remaining_allowed_non_det_expansion_count: 0,
            det_expansion: Id::NONE,
            nondet_expansion_linker: Vec::new(),
        }
    }
}

impl SaturationNodeAssociatedExpansionCacheEntry {
    /// Port of `CSaturationNodeAssociatedExpansionCacheEntry::CSaturationNodeAssociatedExpansionCacheEntry`.
    pub fn new(context: Cint64) -> Self {
        SaturationNodeAssociatedExpansionCacheEntry {
            context,
            ..Default::default()
        }
    }

    /// Port of `initCacheEntry`.
    pub fn init_cache_entry(
        &mut self,
        saturation_node: SatNodeId,
        remaining_allowed_non_det_expansion_count: Cint64,
    ) -> &mut Self {
        self.saturation_node = saturation_node;
        self.nondet_expansion_linker.clear();
        self.det_expansion = Id::NONE;
        self.remaining_allowed_non_det_expansion_count = remaining_allowed_non_det_expansion_count;
        self
    }

    /// Port of `getSaturationIndividualNode`.
    pub fn get_saturation_individual_node(&self) -> SatNodeId {
        self.saturation_node
    }

    /// Port of `getDeterministicConceptExpansion`.
    pub fn get_deterministic_concept_expansion(&self) -> AssociatedConceptExpansionId {
        self.det_expansion
    }

    /// Port of `hasDeterministicConceptExpansion`.
    pub fn has_deterministic_concept_expansion(&self) -> bool {
        self.det_expansion.is_some()
    }

    /// Port of `getNondeterministicConceptExpansionLinker` (chain head → slice).
    pub fn get_nondeterministic_concept_expansion_linker(&self) -> &[AssociatedConceptExpansionId] {
        &self.nondet_expansion_linker
    }

    /// Port of `setDeterministicConceptExpansion`.
    pub fn set_deterministic_concept_expansion(
        &mut self,
        det_concept_expansion: AssociatedConceptExpansionId,
    ) -> &mut Self {
        self.det_expansion = det_concept_expansion;
        self
    }

    /// Port of `addNondeterministicConceptExpansion`
    /// (C++ `mNondetExpansionLinker = nondetConceptExpansion->append(mNondetExpansionLinker)`).
    pub fn add_nondeterministic_concept_expansion(
        &mut self,
        nondet_concept_expansion: AssociatedConceptExpansionId,
    ) -> &mut Self {
        self.nondet_expansion_linker
            .insert(0, nondet_concept_expansion);
        self
    }

    /// Port of `getRemainingAllowedNondeterministicExpansionCount`.
    pub fn get_remaining_allowed_nondeterministic_expansion_count(&self) -> Cint64 {
        self.remaining_allowed_non_det_expansion_count
    }

    /// Port of `areMoreNondeterministicExpansionAllowed`.
    pub fn are_more_nondeterministic_expansion_allowed(&self) -> bool {
        self.remaining_allowed_non_det_expansion_count > 0
    }

    /// Port of `decRemainingAllowedNondeterministicExpansionCount(cint64 decCount = 1)`.
    /// KONCLUDE-PORT-NOTE[overload]: Rust has no default args; the C++ default
    /// `decCount = 1` is supplied by the caller.
    pub fn dec_remaining_allowed_nondeterministic_expansion_count(
        &mut self,
        dec_count: Cint64,
    ) -> &mut Self {
        if self.remaining_allowed_non_det_expansion_count > 0 {
            self.remaining_allowed_non_det_expansion_count -= dec_count;
        }
        self
    }
}

// ===========================================================================
// CSaturationNodeCacheUpdater
// ===========================================================================

/// Port of `CSaturationNodeCacheUpdater`.
///
/// Propagates unsatisfiability + status-flag updates across saturation nodes for
/// the cache. Held by the cache facade.
pub struct SaturationNodeCacheUpdater {
    /// `CSaturationNodeAssociatedExpansionCacheContext* mContext`.
    /// KONCLUDE-PORT-NOTE[ownership]: opaque back-pointer to the cache context.
    pub context: Cint64,
    /// `cint64 mIndirectUpdatedStatusIndiNodeCount`.
    pub indirect_updated_status_indi_node_count: Cint64,
    /// `cint64 mDirectUpdatedStatusIndiNodeCount`.
    pub direct_updated_status_indi_node_count: Cint64,
}

impl Default for SaturationNodeCacheUpdater {
    fn default() -> Self {
        SaturationNodeCacheUpdater {
            context: INVALID,
            indirect_updated_status_indi_node_count: 0,
            direct_updated_status_indi_node_count: 0,
        }
    }
}

impl SaturationNodeCacheUpdater {
    /// Port of `CSaturationNodeCacheUpdater::CSaturationNodeCacheUpdater`.
    pub fn new(context: Cint64) -> Self {
        SaturationNodeCacheUpdater {
            context,
            ..Default::default()
        }
    }

    /// Port of `propagateUnsatisfibility`.
    pub fn propagate_unsatisfibility(
        &mut self,
        node: SatNodeId,
        process_context: &mut ProcessContext,
        context: Cint64,
    ) -> &mut Self {
        let mut flags = IndividualSaturationProcessNodeStatusFlags::default();
        flags.set_flags(
            IndividualSaturationProcessNodeStatusFlags::INDSATFLAGCLASHED,
            true,
        );
        self.update_direct_adding_individual_status_flags(node, &flags, process_context, context);
        self
    }

    /// Port of `createIndividualSaturationUpdateLinker`.
    pub fn create_individual_saturation_update_linker(&mut self, context: Cint64) -> Cint64 {
        // W6-DEFER[api]: `context->getIndividualSaturationUpdateLinker()` over the
        // opaque `CIndividualSaturationProcessNodeStatusUpdateLinker` recycling chain.
        let _ = context;
        INVALID
    }

    /// Port of `releaseIndividualSaturationUpdateLinker`.
    pub fn release_individual_saturation_update_linker(
        &mut self,
        con_sat_update_linker: Cint64,
        context: Cint64,
    ) {
        // W6-DEFER[api]: `context->addIndividualSaturationUpdateLinker(conSatUpdateLinker)`.
        let _ = (con_sat_update_linker, context);
    }

    /// Port of `requiresDirectAddingIndividualStatusFlagsUpdate`.
    pub fn requires_direct_adding_individual_status_flags_update(
        &self,
        indi_node: SatNodeId,
        adding_flags: &IndividualSaturationProcessNodeStatusFlags,
        process_context: &ProcessContext,
        context: Cint64,
    ) -> bool {
        let _ = context;
        indi_node.is_some()
            && !process_context
                .sat_node(indi_node)
                .direct_status_flags
                .has_flags(adding_flags, true)
    }

    /// Port of `requiresIndirectAddingIndividualStatusFlagsUpdate`.
    pub fn requires_indirect_adding_individual_status_flags_update(
        &self,
        indi_node: SatNodeId,
        adding_flags: &IndividualSaturationProcessNodeStatusFlags,
        process_context: &ProcessContext,
        context: Cint64,
    ) -> bool {
        let _ = context;
        indi_node.is_some()
            && !process_context
                .sat_node(indi_node)
                .indirect_status_flags
                .has_flags(adding_flags, true)
    }

    /// Port of `updateDirectAddingIndividualStatusFlags`.
    pub fn update_direct_adding_individual_status_flags(
        &mut self,
        indi_node: SatNodeId,
        adding_flags: &IndividualSaturationProcessNodeStatusFlags,
        process_context: &mut ProcessContext,
        context: Cint64,
    ) {
        if self.requires_direct_adding_individual_status_flags_update(
            indi_node,
            adding_flags,
            process_context,
            context,
        ) {
            let mut direct_update_linker = vec![indi_node];
            process_context
                .sat_node_mut(indi_node)
                .direct_status_flags
                .add_flags(adding_flags);
            self.direct_updated_status_indi_node_count += 1;

            while !direct_update_linker.is_empty() {
                let update_indi_node = direct_update_linker.remove(0);
                let depending_nodes: Vec<SatNodeId> = process_context
                    .sat_node(update_indi_node)
                    .get_copy_depending_individual_node_linker()
                    .iter()
                    .map(|link| link.target)
                    .filter(|id| id.is_some())
                    .collect();

                for depending_indi in depending_nodes {
                    if self.requires_direct_adding_individual_status_flags_update(
                        depending_indi,
                        adding_flags,
                        process_context,
                        context,
                    ) {
                        process_context
                            .sat_node_mut(depending_indi)
                            .direct_status_flags
                            .add_flags(adding_flags);
                        self.direct_updated_status_indi_node_count += 1;
                        direct_update_linker.insert(0, depending_indi);
                    }
                }

                self.update_indirect_adding_individual_status_flags(
                    update_indi_node,
                    adding_flags,
                    process_context,
                    context,
                );
            }
        }
    }

    /// Port of `updateIndirectAddingIndividualStatusFlags`.
    pub fn update_indirect_adding_individual_status_flags(
        &mut self,
        indi_node: SatNodeId,
        adding_flags: &IndividualSaturationProcessNodeStatusFlags,
        process_context: &mut ProcessContext,
        context: Cint64,
    ) {
        if self.requires_indirect_adding_individual_status_flags_update(
            indi_node,
            adding_flags,
            process_context,
            context,
        ) {
            let mut direct_update_linker = vec![indi_node];
            process_context
                .sat_node_mut(indi_node)
                .indirect_status_flags
                .add_flags(adding_flags);
            self.indirect_updated_status_indi_node_count += 1;

            while !direct_update_linker.is_empty() {
                let update_indi_node = direct_update_linker.remove(0);
                let depending_nodes: Vec<SatNodeId> = process_context
                    .sat_node(update_indi_node)
                    .get_copy_depending_individual_node_linker()
                    .iter()
                    .map(|link| link.target)
                    .filter(|id| id.is_some())
                    .collect();

                for depending_indi in depending_nodes {
                    if self.requires_indirect_adding_individual_status_flags_update(
                        depending_indi,
                        adding_flags,
                        process_context,
                        context,
                    ) {
                        process_context
                            .sat_node_mut(depending_indi)
                            .indirect_status_flags
                            .add_flags(adding_flags);
                        self.indirect_updated_status_indi_node_count += 1;
                        direct_update_linker.insert(0, depending_indi);
                    }
                }

                let role_backward_source_nodes =
                    process_context.sat_node_role_backward_source_individuals(update_indi_node);

                for source_individual in role_backward_source_nodes {
                    if self.requires_indirect_adding_individual_status_flags_update(
                        source_individual,
                        adding_flags,
                        process_context,
                        context,
                    ) {
                        process_context
                            .sat_node_mut(source_individual)
                            .indirect_status_flags
                            .add_flags(adding_flags);
                        self.indirect_updated_status_indi_node_count += 1;
                        direct_update_linker.insert(0, source_individual);
                    }
                }

                let non_inverse_connected_nodes: Vec<SatNodeId> = process_context
                    .sat_node(update_indi_node)
                    .get_non_inverse_connected_individual_node_linker()
                    .iter()
                    .copied()
                    .filter(|id| id.is_some())
                    .collect();

                for source_individual in non_inverse_connected_nodes {
                    if self.requires_indirect_adding_individual_status_flags_update(
                        source_individual,
                        adding_flags,
                        process_context,
                        context,
                    ) {
                        process_context
                            .sat_node_mut(source_individual)
                            .indirect_status_flags
                            .add_flags(adding_flags);
                        self.indirect_updated_status_indi_node_count += 1;
                        direct_update_linker.insert(0, source_individual);
                    }
                }
            }
        }
    }
}

// ===========================================================================
// CSaturationNodeAssociatedExpansionCacheReader  (`: CLinkerBase<...>`)
// ===========================================================================

/// Port of `CSaturationNodeAssociatedExpansionCacheReader`.
///
/// Per-thread read cursor. KONCLUDE-PORT-NOTE[ownership]: the `CLinkerBase`
/// next-pointer is dropped; the cache owns its readers in `reader_linker`.
/// No data members of its own.
#[derive(Default)]
pub struct SaturationNodeAssociatedExpansionCacheReader;

impl SaturationNodeAssociatedExpansionCacheReader {
    /// Port of `CSaturationNodeAssociatedExpansionCacheReader::CSaturationNodeAssociatedExpansionCacheReader`.
    pub fn new() -> Self {
        SaturationNodeAssociatedExpansionCacheReader
    }

    /// Port of `getCacheEntry`.
    pub fn get_cache_entry(&self, saturation_node: SatNodeId) -> SatExpansionCacheEntryId {
        // Faithful guard: `if (saturationNode) { ... }`.
        if saturation_node.is_some() {
            // W6-DEFER[api]: `(CSaturationNodeAssociatedExpansionCacheEntry*)
            // saturationNode->getCacheExpansionData()`. Resolving the `SatNodeId` and
            // reinterpreting the process-layer cache-data handle as this family's entry
            // needs the (un-threaded) process node arena.
            return Id::NONE;
        }
        Id::NONE
    }

    /// Port of `getCacheValue`.
    /// KONCLUDE-PORT-NOTE[api]: `concept` is the opaque `CConcept*` (`Cint64`); the
    /// model/ontology arena is not threaded into the reader.
    pub fn get_cache_value(&self, concept: Cint64, negation: bool) -> CacheValue {
        let cache_value_identifier = if negation {
            CacheValueIdentifier::CacheValTagAndNegatedConcept
        } else {
            CacheValueIdentifier::CacheValTagAndConcept
        };
        // W6-DEFER[api]: `first = concept->getConceptTag()`; the tag read needs the
        // ontology arena, so it is left unset. `second = (cint64)concept` (the
        // identity) and `third = identifier` are filled faithfully.
        CacheValue {
            first: INVALID,
            second: concept,
            third: cache_value_identifier as i64,
        }
    }
}

// ===========================================================================
// CSaturationNodeAssociatedExpansionCacheWriter
// ===========================================================================

/// Port of `CSaturationNodeAssociatedExpansionCacheWriter`.
pub struct SaturationNodeAssociatedExpansionCacheWriter {
    /// `CSaturationNodeAssociatedExpansionCache* mCache`.
    pub cache: SatExpansionCacheId,
}

impl Default for SaturationNodeAssociatedExpansionCacheWriter {
    fn default() -> Self {
        SaturationNodeAssociatedExpansionCacheWriter { cache: Id::NONE }
    }
}

impl SaturationNodeAssociatedExpansionCacheWriter {
    /// Port of `CSaturationNodeAssociatedExpansionCacheWriter::CSaturationNodeAssociatedExpansionCacheWriter`.
    pub fn new(cache: SatExpansionCacheId) -> Self {
        SaturationNodeAssociatedExpansionCacheWriter { cache }
    }

    /// Port of `writeCacheData` (delegates to `mCache->writeCacheData`).
    /// KONCLUDE-PORT-NOTE[api]: `write_data` is the opaque write-data linker head
    /// (`CSaturationNodeAssociatedExpansionCacheWriteData*`); `memory_pools` the
    /// `CMemoryPool*` chain. Both are opaque handles in this staged port.
    pub fn write_cache_data(&mut self, write_data: Cint64, memory_pools: Cint64) -> &mut Self {
        // W6-DEFER[api]: `mCache->writeCacheData(writeData, memoryPools)` — `mCache`
        // (`SatExpansionCacheId`) resolves through the (un-threaded) cache-facade arena.
        let _ = (write_data, memory_pools);
        self
    }
}

// ===========================================================================
// CSaturationNodeAssociatedExpansionCache
//   (`: public CThread, public CSaturationCache`)  — the facade
// ===========================================================================

/// Port of `CSaturationNodeAssociatedExpansionCache`.
///
/// The facade: holds the entry chain, the per-thread reader cursors, the cache
/// updater, statistics, and the cache context. KONCLUDE-PORT-NOTE[threading]: the
/// `CThread` base (Qt event-loop worker) becomes the opaque `thread_base` handle;
/// the writer-thread / Reader split is the concurrency seam (manifest/07-cache.md).
pub struct SaturationNodeAssociatedExpansionCache {
    /// the `CThread` base.
    /// KONCLUDE-PORT-NOTE[threading]: opaque handle for the Qt event-loop worker;
    /// the first faithful port drains writes inline (single-threaded).
    pub thread_base: Cint64,
    /// the `CSaturationCache` base (already ported in `cache::base`).
    pub sat_cache_base: SaturationCache,

    /// `CSaturationNodeAssociatedExpansionCacheEntry* mEntryLinker`
    /// (intrusive chain head → owned `Vec`, head-at-FRONT).
    pub entry_linker: Vec<SatExpansionCacheEntryId>,
    /// `CSaturationNodeCacheUpdater* mSaturationNodeCacheUpdate`.
    pub saturation_node_cache_update: SaturationNodeCacheUpdaterId,
    /// `cint64 mConfAllowedNonDetExpansionCount`.
    pub conf_allowed_non_det_expansion_count: Cint64,
    /// `CSaturationNodeAssociatedExpansionCacheReader* mReaderLinker`
    /// (intrusive chain head → owned `Vec`, head-at-FRONT).
    pub reader_linker: Vec<SatExpansionCacheReaderId>,
    /// `QMutex mReaderSyncMutex`.
    /// KONCLUDE-PORT-NOTE[threading]: opaque lock handle; applied only at the
    /// facade granularity, never per entry.
    pub reader_sync_mutex: Cint64,
    /// `CCacheStatistics mCacheStat` (held by value).
    /// KONCLUDE-PORT-NOTE[api]: F0 `CCacheStatistics` not yet ported (`cache::value`);
    /// opaque `Cint64` handle for now (it carries 2 `cint64` counters).
    pub cache_stat: Cint64,
    /// `CSaturationNodeAssociatedExpansionCacheContext mContext` (held by value).
    pub context: SaturationNodeAssociatedExpansionCacheContext,
}

impl Default for SaturationNodeAssociatedExpansionCache {
    fn default() -> Self {
        SaturationNodeAssociatedExpansionCache {
            thread_base: INVALID,
            sat_cache_base: SaturationCache::default(),
            entry_linker: Vec::new(),
            saturation_node_cache_update: Id::NONE,
            // CSaturationNodeAssociatedExpansionCache.cpp ctor lines 36-40:
            // Konclude permits one nondeterministic expansion per saturation
            // node unless the configuration overrides that count.
            conf_allowed_non_det_expansion_count: 1,
            reader_linker: Vec::new(),
            reader_sync_mutex: INVALID,
            cache_stat: INVALID,
            context: SaturationNodeAssociatedExpansionCacheContext::default(),
        }
    }
}

impl SaturationNodeAssociatedExpansionCache {
    /// Port of `CSaturationNodeAssociatedExpansionCache::CSaturationNodeAssociatedExpansionCache`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `createCacheReader`.
    pub fn create_cache_reader(&mut self) -> SatExpansionCacheReaderId {
        // W6-DEFER[api][threading]: the C++ allocates a fresh reader, takes
        // `mReaderSyncMutex`, prepends it onto `mReaderLinker`, and returns it. The
        // reader arena is not threaded into the facade; the facade-granularity mutex
        // is the opaque `reader_sync_mutex` handle (single-thread staged port).
        Id::NONE
    }

    /// Port of `createCacheWriter` (C++ `new CSaturationNodeAssociatedExpansionCacheWriter(this)`).
    pub fn create_cache_writer(&mut self) -> SaturationNodeAssociatedExpansionCacheWriter {
        // W6-DEFER[api]: the writer binds to `this` (the facade's own
        // `SatExpansionCacheId`), which is not reachable from inside the value here;
        // bound to `Id::NONE` until the facade arena is threaded.
        SaturationNodeAssociatedExpansionCacheWriter::new(Id::NONE)
    }

    /// Port of `writeCacheData`.
    pub fn write_cache_data(&mut self, write_data: Cint64, memory_pools: Cint64) -> &mut Self {
        // W6-DEFER[threading]: the C++ posts a `CWriteSaturationCacheDataEvent` to the
        // cache's own `CThread` event loop; the writer thread later drains it via
        // `processCustomsEvents` → `installWriteCacheData`. In the single-threaded
        // staged port the worker IS the writer (manifest §Concurrency): the inline
        // drain is `self.install_write_cache_data(write_data, &mContext)` followed by
        // releasing `memory_pools` back to the context pool. Deferred together with
        // `install_write_cache_data`.
        let _ = (write_data, memory_pools);
        self
    }

    /// Port of `getCacheStatistics` (C++ `return &mCacheStat`).
    /// KONCLUDE-PORT-NOTE[api]: `CCacheStatistics` (F0) is the opaque `cache_stat`
    /// handle until `cache::value` is threaded in.
    pub fn get_cache_statistics(&self) -> Cint64 {
        self.cache_stat
    }

    /// Port of `installWriteCacheData`.
    pub fn install_write_cache_data(&mut self, write_data: Cint64, context: Cint64) -> &mut Self {
        // W6-DEFER[api]: faithful logic walks the `writeData` linker chain and, per
        // node, dispatches by `getWriteDataType()`:
        //   SNAECWT_UNSAT  → `propagateUnsatisfibility(snaecuwd->getUnsatisfiableSaturationIndividualNode(), context)`
        //   SNAECWT_EXPAND → `addNodeExpansionData(snaecewd, context)`
        // The write-data records live in an arena not threaded into the facade, so the
        // chain walk + downcast dispatch are deferred (siblings already ported below).
        let _ = (write_data, context);
        self
    }

    /// Port of `addNodeExpansionData`.
    pub fn add_node_expansion_data(&mut self, snaecewd: Cint64, context: Cint64) -> &mut Self {
        // W6-DEFER[api]: faithful logic —
        //   cacheEntry = getCacheEntryForNode(snaecewd->getSaturationIndividualNode(), context, true);
        //   if deterministic: when the entry has no det expansion, allocate+init a
        //     CSaturationNodeAssociatedDeterministicConceptExpansion, fillExpansionData,
        //     setNonDeterministicExpansionRequired, setDeterministicConceptExpansion;
        //     else extendDeterministicExpansionData(...) + re-set.
        //   else (nondeterministic): if areMoreNondeterministicExpansionAllowed,
        //     decRemaining…, allocate+init a nondet expansion, fillExpansionData,
        //     addNondeterministicConceptExpansion.
        // Allocation of family expansion objects needs an arena not threaded here.
        let _ = (snaecewd, context);
        self
    }

    /// Port of `extendDeterministicExpansionData`.
    pub fn extend_deterministic_expansion_data(
        &mut self,
        prev_concept_expansion: AssociatedConceptExpansionId,
        snaecewd: Cint64,
        context: Cint64,
    ) -> AssociatedConceptExpansionId {
        // W6-DEFER[api]: faithful logic walks `snaecewd->getExpansionConceptLinker()`,
        // and for each cache value NOT already in `prevConceptExpansion`, lazily
        // allocates a new det expansion + a concept linker (initConceptLinker) and
        // addConceptExpansionLinker. If nothing new and nondet not required, still
        // allocates an empty det expansion. When a new det expansion exists, copies the
        // dependent-nominal set (insert each id), setHasTightCardinalityRestriction,
        // setConceptSetSignature, setTotalConceptCount. Object allocation needs an arena.
        let _ = (prev_concept_expansion, snaecewd, context);
        Id::NONE
    }

    /// Port of `fillExpansionData`.
    pub fn fill_expansion_data(
        &mut self,
        concept_expansion: AssociatedConceptExpansionId,
        snaecewd: Cint64,
        context: Cint64,
    ) -> &mut Self {
        // W6-DEFER[api]: faithful logic walks `snaecewd->getExpansionConceptLinker()`,
        // allocates a concept linker per cache value (initConceptLinker) and
        // addConceptExpansionLinker into `conceptExpansion`; copies the dependent-nominal
        // set (insert each id); then setHasTightCardinalityRestriction /
        // setConceptSetSignature / setTotalConceptCount from the write data. Linker
        // allocation needs an arena not threaded here.
        let _ = (concept_expansion, snaecewd, context);
        self
    }

    /// Port of `getCacheEntryForNode`.
    pub fn get_cache_entry_for_node(
        &mut self,
        node: SatNodeId,
        context: Cint64,
        create: bool,
    ) -> SatExpansionCacheEntryId {
        // W6-DEFER[api]: faithful logic reads `node->getCacheExpansionData()`; when
        // absent (and create), allocates+initCacheEntry(node, mConfAllowedNonDetExpansionCount)
        // and `node->setCacheExpansionData(cacheEntry)`. Needs the process node arena
        // + a cache-entry arena.
        let _ = (node, context, create);
        Id::NONE
    }

    /// Port of `propagateUnsatisfibility`
    /// (delegates to `mSaturationNodeCacheUpdate->propagateUnsatisfibility`).
    pub fn propagate_unsatisfibility(&mut self, node: SatNodeId, context: Cint64) -> &mut Self {
        // W6-DEFER[api]: `mSaturationNodeCacheUpdate` (`SaturationNodeCacheUpdaterId`)
        // resolves through the (un-threaded) updater arena; the updater body is itself
        // deferred (see `SaturationNodeCacheUpdater::propagate_unsatisfibility`).
        let _ = (node, context);
        self
    }

    /// Port of `processCustomsEvents`.
    pub fn process_customs_events(&mut self, type_: Cint64, event: Cint64) -> bool {
        // W6-DEFER[threading]: the C++ first delegates to `CThread::processCustomsEvents`;
        // on `EVENTWRITESATURATIONCACHEDATAENTRY` it unpacks the
        // `CWriteSaturationCacheDataEvent` (write data + memory pools), calls
        // `installWriteCacheData(writeData, &mContext)`, releases the temporary memory
        // pools, and returns true. The `CThread` event loop is the opaque `thread_base`;
        // the staged single-thread port drains writes inline (see `write_cache_data`).
        let _ = (type_, event);
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn alloc_concept_linker(
        context: &mut CacheContext,
        cache_value: CacheValue,
    ) -> AssociatedConceptLinkerId {
        let mut linker = SaturationNodeAssociatedConceptLinker::new();
        linker.init_concept_linker(cache_value);
        context.alloc_associated_concept_linker(linker)
    }

    #[test]
    fn add_concept_expansion_linker_prepends_counts_and_indexes_by_cache_value() {
        let mut context = CacheContext::new();
        let cache_value_1 =
            CacheValue::new_value(11, 101, CacheValueIdentifier::CacheValTagAndConcept);
        let cache_value_2 =
            CacheValue::new_value(22, 202, CacheValueIdentifier::CacheValTagAndNegatedConcept);
        let linker_1 = alloc_concept_linker(&mut context, cache_value_1);
        let linker_2 = alloc_concept_linker(&mut context, cache_value_2);

        let mut expansion =
            AssociatedConceptExpansion::new(AssociatedConceptExpansionKind::Concept, 0);

        expansion.add_concept_expansion_linker(linker_1, &context);
        assert_eq!(expansion.get_concept_expansion_count(), 1);
        assert_eq!(expansion.get_concept_expansion_linker(), &[linker_1]);
        assert_eq!(
            expansion.get_concept_expansion_linker_for_cache_value(cache_value_1),
            linker_1
        );

        expansion.add_concept_expansion_linker(linker_2, &context);
        assert_eq!(expansion.get_concept_expansion_count(), 2);
        assert_eq!(
            expansion.get_concept_expansion_linker(),
            &[linker_2, linker_1]
        );
        assert_eq!(
            expansion.get_concept_expansion_linker_for_cache_value(cache_value_1),
            linker_1
        );
        assert_eq!(
            expansion.get_concept_expansion_linker_for_cache_value(cache_value_2),
            linker_2
        );
    }
}
