//! `cache::occstats` — F7, the **occurrence-statistics cache** (Konclude
//! `Source/Reasoner/Kernel/Cache/COccurrenceStatistics*`).
//!
//! Caches per-concept / per-role occurrence statistics (deterministic /
//! non-deterministic / individual / existential instance counts, plus role
//! in/out edge counts) accumulated across satisfiability tests; these feed the
//! processing-priority heuristics. The algorithm reaches it only through the
//! Algorithm-layer `COccurrenceStatisticsCacheHandler` (stubbed in
//! `completion::stubs`).
//!
//! W6-CACHE struct-skeleton unit (manifest/07-cache.md §F7): struct/template
//! DATA MODEL only — every method body deferred to the W6-CACHE method-batch
//! wave. `mod.rs` is intentionally NOT wired and this file is not built yet.
//!
//! ## Port conventions applied (see `model/substrate.rs` + `PORT.md`)
//! - `CXxx*` pointer to a same-family record (CacheData / OntologyData /
//!   OntologyDataVector) → typed arena `Id<T>` (`Id::NONE` == `nullptr`). [ownership]
//! - Back-pointer to the long-lived facade `COccurrenceStatisticsCache` (a
//!   `CThread`) → opaque `Cint64`. [ownership]
//! - C++ inheritance (`*ConceptData : *Data`, `*RoleData : *Data`) → the base
//!   `COccurrenceStatisticsData` fields are INLINED into each subclass struct
//!   (the `model/individual.rs` "inherited base inlined" convention). The base is
//!   also kept as its own struct for fidelity.
//! - `CXLinker<…>*` intrusive chain / `QList<…*>` → owned `Vec<Id>`
//!   (head-at-front CLinker convention). [ownership]
//! - `QHash<cint64,…*>` → `HashMap<Cint64, Id<…>>`.
//! - `QReadWriteLock` / `QAtomicInteger` → opaque `Cint64`. [threading]
//! - `CCacheEntryWriteData` (F0 base) / `CCacheStatistics` (F0) / `CMemoryPool*` /
//!   `CConfiguration*` / `COccurrenceStatisticsCacheContext` mem handles → opaque
//!   `Cint64`. [api]/[memory-pool]

#![allow(dead_code)]

use std::collections::HashMap;

use super::super::model::substrate::{Cint64, Id, INVALID};
use super::context::CacheContext;
use super::value::event;

// --- F7 same-family arena ids (would live in `cache/mod.rs` once wired) ---
/// `COccurrenceStatisticsCacheData*`        → `OccStatCacheDataId`.
pub type OccStatCacheDataId = Id<OccurrenceStatisticsCacheData>;
/// `COccurrenceStatisticsCacheOntologyData*`→ `OccStatOntologyDataId`.
pub type OccStatOntologyDataId = Id<OccurrenceStatisticsCacheOntologyData>;
/// `COccurrenceStatisticsCacheOntologyDataVector<COccurrenceStatisticsConceptData>*`
/// → `OccStatConceptDataVecId`.
pub type OccStatConceptDataVecId =
    Id<OccurrenceStatisticsCacheOntologyDataVector<OccurrenceStatisticsConceptData>>;
/// `COccurrenceStatisticsCacheOntologyDataVector<COccurrenceStatisticsRoleData>*`
/// → `OccStatRoleDataVecId`.
pub type OccStatRoleDataVecId =
    Id<OccurrenceStatisticsCacheOntologyDataVector<OccurrenceStatisticsRoleData>>;

// ===========================================================================
// Statistics data records (`COccurrenceStatistics{,Concept,Role}Data`).
// ===========================================================================

/// Port of `COccurrenceStatisticsData`.
///
/// The shared occurrence-count base: deterministic / non-deterministic /
/// individual / existential instance-occurrence counters. Inlined into the
/// concept and role subclasses below; kept as its own struct for fidelity.
pub struct OccurrenceStatisticsData {
    /// `COccurrenceStatisticsData::mDeterministicInstanceOccurrencesCount`.
    pub deterministic_instance_occurrences_count: Cint64,
    /// `COccurrenceStatisticsData::mNonDeterministicInstanceOccurrencesCount`.
    pub non_deterministic_instance_occurrences_count: Cint64,
    /// `COccurrenceStatisticsData::mIndividualInstanceOccurrencesCount`.
    pub individual_instance_occurrences_count: Cint64,
    /// `COccurrenceStatisticsData::mExistentialInstanceOccurrencesCount`.
    pub existential_instance_occurrences_count: Cint64,
}

impl Default for OccurrenceStatisticsData {
    fn default() -> Self {
        OccurrenceStatisticsData {
            deterministic_instance_occurrences_count: 0,
            non_deterministic_instance_occurrences_count: 0,
            individual_instance_occurrences_count: 0,
            existential_instance_occurrences_count: 0,
        }
    }
}

impl OccurrenceStatisticsData {
    /// Port of `COccurrenceStatisticsData::COccurrenceStatisticsData`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `COccurrenceStatisticsData::getDeterministicInstanceOccurrencesCount`.
    pub fn get_deterministic_instance_occurrences_count(&self) -> Cint64 {
        self.deterministic_instance_occurrences_count
    }

    /// Port of `COccurrenceStatisticsData::getNonDeterministicInstanceOccurrencesCount`.
    pub fn get_non_deterministic_instance_occurrences_count(&self) -> Cint64 {
        self.non_deterministic_instance_occurrences_count
    }

    /// Port of `COccurrenceStatisticsData::getIndividualInstanceOccurrencesCount`.
    pub fn get_individual_instance_occurrences_count(&self) -> Cint64 {
        self.individual_instance_occurrences_count
    }

    /// Port of `COccurrenceStatisticsData::getExistentialInstanceOccurrencesCount`.
    pub fn get_existential_instance_occurrences_count(&self) -> Cint64 {
        self.existential_instance_occurrences_count
    }

    /// Port of `COccurrenceStatisticsData::incDeterministicInstanceOccurrencesCount(cint64 incCount = 1)`.
    /// KONCLUDE-PORT-NOTE[overload]: C++ default arg `incCount = 1` → explicit param
    /// (Rust has no default args); callers pass the count. Returns `&mut self` for the
    /// C++ `return this` chaining idiom.
    pub fn inc_deterministic_instance_occurrences_count(&mut self, inc_count: Cint64) -> &mut Self {
        self.deterministic_instance_occurrences_count += inc_count;
        self
    }

    /// Port of `COccurrenceStatisticsData::incNonDeterministicInstanceOccurrencesCount`.
    pub fn inc_non_deterministic_instance_occurrences_count(
        &mut self,
        inc_count: Cint64,
    ) -> &mut Self {
        self.non_deterministic_instance_occurrences_count += inc_count;
        self
    }

    /// Port of `COccurrenceStatisticsData::incIndividualInstanceOccurrencesCount`.
    pub fn inc_individual_instance_occurrences_count(&mut self, inc_count: Cint64) -> &mut Self {
        self.individual_instance_occurrences_count += inc_count;
        self
    }

    /// Port of `COccurrenceStatisticsData::incExistentialInstanceOccurrencesCount`.
    pub fn inc_existential_instance_occurrences_count(&mut self, inc_count: Cint64) -> &mut Self {
        self.existential_instance_occurrences_count += inc_count;
        self
    }
}

/// Port of `COccurrenceStatisticsConceptData` (base `COccurrenceStatisticsData`).
///
/// Per-concept occurrence statistics. Adds no fields over the base; the base
/// fields are inlined for the flattened single-struct port.
#[derive(Clone)]
pub struct OccurrenceStatisticsConceptData {
    // --- from COccurrenceStatisticsData (inlined base) ---
    /// `COccurrenceStatisticsData::mDeterministicInstanceOccurrencesCount`.
    pub deterministic_instance_occurrences_count: Cint64,
    /// `COccurrenceStatisticsData::mNonDeterministicInstanceOccurrencesCount`.
    pub non_deterministic_instance_occurrences_count: Cint64,
    /// `COccurrenceStatisticsData::mIndividualInstanceOccurrencesCount`.
    pub individual_instance_occurrences_count: Cint64,
    /// `COccurrenceStatisticsData::mExistentialInstanceOccurrencesCount`.
    pub existential_instance_occurrences_count: Cint64,
}

impl Default for OccurrenceStatisticsConceptData {
    fn default() -> Self {
        OccurrenceStatisticsConceptData {
            deterministic_instance_occurrences_count: 0,
            non_deterministic_instance_occurrences_count: 0,
            individual_instance_occurrences_count: 0,
            existential_instance_occurrences_count: 0,
        }
    }
}

impl OccurrenceStatisticsConceptData {
    /// Port of `COccurrenceStatisticsConceptData::COccurrenceStatisticsConceptData`.
    pub fn new() -> Self {
        Self::default()
    }

    // KONCLUDE-PORT-NOTE[template]: `COccurrenceStatisticsConceptData` inherits these
    // accessors from `COccurrenceStatisticsData`. Rust has no inheritance, and the base
    // fields are inlined here (the flattened single-struct port), so the inherited
    // getters/incrementers are re-implemented over the inlined fields. Bodies are
    // byte-for-byte the same as `OccurrenceStatisticsData`'s.

    /// Inherited `COccurrenceStatisticsData::getDeterministicInstanceOccurrencesCount`.
    pub fn get_deterministic_instance_occurrences_count(&self) -> Cint64 {
        self.deterministic_instance_occurrences_count
    }

    /// Inherited `COccurrenceStatisticsData::getNonDeterministicInstanceOccurrencesCount`.
    pub fn get_non_deterministic_instance_occurrences_count(&self) -> Cint64 {
        self.non_deterministic_instance_occurrences_count
    }

    /// Inherited `COccurrenceStatisticsData::getIndividualInstanceOccurrencesCount`.
    pub fn get_individual_instance_occurrences_count(&self) -> Cint64 {
        self.individual_instance_occurrences_count
    }

    /// Inherited `COccurrenceStatisticsData::getExistentialInstanceOccurrencesCount`.
    pub fn get_existential_instance_occurrences_count(&self) -> Cint64 {
        self.existential_instance_occurrences_count
    }

    /// Inherited `COccurrenceStatisticsData::incDeterministicInstanceOccurrencesCount`.
    pub fn inc_deterministic_instance_occurrences_count(&mut self, inc_count: Cint64) -> &mut Self {
        self.deterministic_instance_occurrences_count += inc_count;
        self
    }

    /// Inherited `COccurrenceStatisticsData::incNonDeterministicInstanceOccurrencesCount`.
    pub fn inc_non_deterministic_instance_occurrences_count(
        &mut self,
        inc_count: Cint64,
    ) -> &mut Self {
        self.non_deterministic_instance_occurrences_count += inc_count;
        self
    }

    /// Inherited `COccurrenceStatisticsData::incIndividualInstanceOccurrencesCount`.
    pub fn inc_individual_instance_occurrences_count(&mut self, inc_count: Cint64) -> &mut Self {
        self.individual_instance_occurrences_count += inc_count;
        self
    }

    /// Inherited `COccurrenceStatisticsData::incExistentialInstanceOccurrencesCount`.
    pub fn inc_existential_instance_occurrences_count(&mut self, inc_count: Cint64) -> &mut Self {
        self.existential_instance_occurrences_count += inc_count;
        self
    }
}

/// Port of `COccurrenceStatisticsRoleData` (base `COccurrenceStatisticsData`).
///
/// Per-role occurrence statistics: the inlined base counters plus the
/// outgoing/incoming node-instance occurrence counts.
#[derive(Clone)]
pub struct OccurrenceStatisticsRoleData {
    // --- from COccurrenceStatisticsData (inlined base) ---
    /// `COccurrenceStatisticsData::mDeterministicInstanceOccurrencesCount`.
    pub deterministic_instance_occurrences_count: Cint64,
    /// `COccurrenceStatisticsData::mNonDeterministicInstanceOccurrencesCount`.
    pub non_deterministic_instance_occurrences_count: Cint64,
    /// `COccurrenceStatisticsData::mIndividualInstanceOccurrencesCount`.
    pub individual_instance_occurrences_count: Cint64,
    /// `COccurrenceStatisticsData::mExistentialInstanceOccurrencesCount`.
    pub existential_instance_occurrences_count: Cint64,
    // --- COccurrenceStatisticsRoleData own fields ---
    /// `COccurrenceStatisticsRoleData::mOutgoingNodeInstanceOccurrencesCount`.
    pub outgoing_node_instance_occurrences_count: Cint64,
    /// `COccurrenceStatisticsRoleData::mIncomingNodeInstanceOccurrencesCount`.
    pub incoming_node_instance_occurrences_count: Cint64,
}

impl Default for OccurrenceStatisticsRoleData {
    fn default() -> Self {
        OccurrenceStatisticsRoleData {
            deterministic_instance_occurrences_count: 0,
            non_deterministic_instance_occurrences_count: 0,
            individual_instance_occurrences_count: 0,
            existential_instance_occurrences_count: 0,
            outgoing_node_instance_occurrences_count: 0,
            incoming_node_instance_occurrences_count: 0,
        }
    }
}

impl OccurrenceStatisticsRoleData {
    /// Port of `COccurrenceStatisticsRoleData::COccurrenceStatisticsRoleData`.
    pub fn new() -> Self {
        Self::default()
    }

    // --- inherited from COccurrenceStatisticsData (inlined base) ---
    // KONCLUDE-PORT-NOTE[template]: re-implemented over the inlined base fields; see
    // the same note on `OccurrenceStatisticsConceptData`.

    /// Inherited `COccurrenceStatisticsData::getDeterministicInstanceOccurrencesCount`.
    pub fn get_deterministic_instance_occurrences_count(&self) -> Cint64 {
        self.deterministic_instance_occurrences_count
    }

    /// Inherited `COccurrenceStatisticsData::getNonDeterministicInstanceOccurrencesCount`.
    pub fn get_non_deterministic_instance_occurrences_count(&self) -> Cint64 {
        self.non_deterministic_instance_occurrences_count
    }

    /// Inherited `COccurrenceStatisticsData::getIndividualInstanceOccurrencesCount`.
    pub fn get_individual_instance_occurrences_count(&self) -> Cint64 {
        self.individual_instance_occurrences_count
    }

    /// Inherited `COccurrenceStatisticsData::getExistentialInstanceOccurrencesCount`.
    pub fn get_existential_instance_occurrences_count(&self) -> Cint64 {
        self.existential_instance_occurrences_count
    }

    /// Inherited `COccurrenceStatisticsData::incDeterministicInstanceOccurrencesCount`.
    pub fn inc_deterministic_instance_occurrences_count(&mut self, inc_count: Cint64) -> &mut Self {
        self.deterministic_instance_occurrences_count += inc_count;
        self
    }

    /// Inherited `COccurrenceStatisticsData::incNonDeterministicInstanceOccurrencesCount`.
    pub fn inc_non_deterministic_instance_occurrences_count(
        &mut self,
        inc_count: Cint64,
    ) -> &mut Self {
        self.non_deterministic_instance_occurrences_count += inc_count;
        self
    }

    /// Inherited `COccurrenceStatisticsData::incIndividualInstanceOccurrencesCount`.
    pub fn inc_individual_instance_occurrences_count(&mut self, inc_count: Cint64) -> &mut Self {
        self.individual_instance_occurrences_count += inc_count;
        self
    }

    /// Inherited `COccurrenceStatisticsData::incExistentialInstanceOccurrencesCount`.
    pub fn inc_existential_instance_occurrences_count(&mut self, inc_count: Cint64) -> &mut Self {
        self.existential_instance_occurrences_count += inc_count;
        self
    }

    // --- COccurrenceStatisticsRoleData own methods ---

    /// Port of `COccurrenceStatisticsRoleData::getOutgoingNodeInstanceOccurrencesCount`.
    pub fn get_outgoing_node_instance_occurrences_count(&self) -> Cint64 {
        self.outgoing_node_instance_occurrences_count
    }

    /// Port of `COccurrenceStatisticsRoleData::getIncomingNodeInstanceOccurrencesCount`.
    pub fn get_incoming_node_instance_occurrences_count(&self) -> Cint64 {
        self.incoming_node_instance_occurrences_count
    }

    /// Port of `COccurrenceStatisticsRoleData::incOutgoingNodeInstanceOccurrencesCount(cint64 incCount = 1)`.
    pub fn inc_outgoing_node_instance_occurrences_count(&mut self, inc_count: Cint64) -> &mut Self {
        self.outgoing_node_instance_occurrences_count += inc_count;
        self
    }

    /// Port of `COccurrenceStatisticsRoleData::incIncomingNodeInstanceOccurrencesCount(cint64 incCount = 1)`.
    pub fn inc_incoming_node_instance_occurrences_count(&mut self, inc_count: Cint64) -> &mut Self {
        self.incoming_node_instance_occurrences_count += inc_count;
        self
    }
}

// ===========================================================================
// Per-ontology data vector (`COccurrenceStatisticsCacheOntologyDataVector<T>`).
// ===========================================================================

/// Port of `COccurrenceStatisticsCacheOntologyDataVector<T>` (template).
///
/// A fixed-size occurrence-statistics array indexed by concept/role id.
///
/// KONCLUDE-PORT-NOTE[ownership]: the C++ `T* mVector` (heap C-array of `mCount`
/// elements) becomes an owned `Vec<T>`; the separate `cint64 mCount` is the
/// `Vec` length and is dropped (kept implicitly).
pub struct OccurrenceStatisticsCacheOntologyDataVector<T> {
    /// `COccurrenceStatisticsCacheOntologyDataVector::mVector` (+ `mCount` as len).
    pub vector: Vec<T>,
}

impl<T> Default for OccurrenceStatisticsCacheOntologyDataVector<T> {
    fn default() -> Self {
        OccurrenceStatisticsCacheOntologyDataVector { vector: Vec::new() }
    }
}

impl<T: Default + Clone> OccurrenceStatisticsCacheOntologyDataVector<T> {
    /// Port of `COccurrenceStatisticsCacheOntologyDataVector::COccurrenceStatisticsCacheOntologyDataVector(cint64 count)`.
    pub fn new(count: usize) -> Self {
        OccurrenceStatisticsCacheOntologyDataVector {
            vector: vec![T::default(); count],
        }
    }

    /// Port of `COccurrenceStatisticsCacheOntologyDataVector::getOccurrenceStatisticsData(cint64 idx)`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: C++ returns `T*` (a borrow into `mVector`, or
    /// `nullptr` when out of range) → `Option<&mut T>` (`None` == `nullptr`). The
    /// owning writer mutates through it (`inc*`); the reader's accumulation reads
    /// through the same `&mut` borrow. The `mCount` bound check becomes the `Vec`
    /// length check (`mCount` is the `Vec` length).
    pub fn get_occurrence_statistics_data(&mut self, idx: Cint64) -> Option<&mut T> {
        if idx >= 0 && (idx as usize) < self.vector.len() {
            return Some(&mut self.vector[idx as usize]);
        }
        None
    }
}

// ===========================================================================
// Per-ontology data (`COccurrenceStatisticsCacheOntologyData`).
// ===========================================================================

/// Port of `COccurrenceStatisticsCacheOntologyData`.
///
/// The accumulated occurrence statistics for one ontology: a usage refcount plus
/// the active and free concept/role data-vector chains.
pub struct OccurrenceStatisticsCacheOntologyData {
    // KONCLUDE-PORT-NOTE[threading]: `QAtomicInteger<cint64> mUsageCounter` → atomic word.
    /// `COccurrenceStatisticsCacheOntologyData::mUsageCounter`.
    pub usage_counter: Cint64,
    // KONCLUDE-PORT-NOTE[ownership]: `CXLinker<…ConceptData-vector*>* mConceptDataVecLinker`
    // intrusive chain → owned `Vec<Id>` (head-front).
    /// `COccurrenceStatisticsCacheOntologyData::mConceptDataVecLinker`.
    pub concept_data_vec_linker: Vec<OccStatConceptDataVecId>,
    // KONCLUDE-PORT-NOTE[ownership]: `CXLinker<…RoleData-vector*>* mRoleDataVecLinker`.
    /// `COccurrenceStatisticsCacheOntologyData::mRoleDataVecLinker`.
    pub role_data_vec_linker: Vec<OccStatRoleDataVecId>,
    // KONCLUDE-PORT-NOTE[ownership]: `QList<…ConceptData-vector*> mFreeConceptDataVecList`.
    /// `COccurrenceStatisticsCacheOntologyData::mFreeConceptDataVecList`.
    pub free_concept_data_vec_list: Vec<OccStatConceptDataVecId>,
    // KONCLUDE-PORT-NOTE[ownership]: `QList<…RoleData-vector*> mFreeRoleDataVecList`.
    /// `COccurrenceStatisticsCacheOntologyData::mFreeRoleDataVecList`.
    pub free_role_data_vec_list: Vec<OccStatRoleDataVecId>,
}

impl Default for OccurrenceStatisticsCacheOntologyData {
    fn default() -> Self {
        OccurrenceStatisticsCacheOntologyData {
            usage_counter: 0,
            concept_data_vec_linker: Vec::new(),
            role_data_vec_linker: Vec::new(),
            free_concept_data_vec_list: Vec::new(),
            free_role_data_vec_list: Vec::new(),
        }
    }
}

impl OccurrenceStatisticsCacheOntologyData {
    /// Port of `COccurrenceStatisticsCacheOntologyData::COccurrenceStatisticsCacheOntologyData`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `COccurrenceStatisticsCacheOntologyData::getUsageCount`.
    /// KONCLUDE-PORT-NOTE[threading]: `QAtomicInteger::load` → plain field read
    /// (single-threaded inline; the atomic is an opaque-free `Cint64`).
    pub fn get_usage_count(&self) -> Cint64 {
        self.usage_counter
    }

    /// Port of `COccurrenceStatisticsCacheOntologyData::incUsageCount` (`mUsageCounter.ref()`).
    /// KONCLUDE-PORT-NOTE[threading]: atomic `ref()` → `+= 1` inline.
    pub fn inc_usage_count(&mut self) -> &mut Self {
        self.usage_counter += 1;
        self
    }

    /// Port of `COccurrenceStatisticsCacheOntologyData::decUsageCount` (`mUsageCounter.deref()`).
    /// KONCLUDE-PORT-NOTE[threading]: atomic `deref()` → `-= 1` inline.
    pub fn dec_usage_count(&mut self) -> &mut Self {
        self.usage_counter -= 1;
        self
    }

    /// Port of `COccurrenceStatisticsCacheOntologyData::getAccummulatedRoleDataOccurrenceStatistics(cint64 id)`.
    ///
    /// C++ folds the six role counters across every role-data vector in
    /// `mRoleDataVecLinker` (for each, `getOccurrenceStatisticsData(id)`, and when
    /// non-null `inc{Deterministic,NonDeterministic,Existential,Individual,Incoming,
    /// Outgoing}…(data->get…())`).
    pub fn get_accummulated_role_data_occurrence_statistics(
        &self,
        id: Cint64,
    ) -> OccurrenceStatisticsRoleData {
        let acc_data = OccurrenceStatisticsRoleData::new();
        // W6-DEFER[api]: for each role_data_vec_linker id (head→tail), resolve it to its
        // OccurrenceStatisticsCacheOntologyDataVector<RoleData> via the cache vector arena
        // (no cache-side ProcessContext equivalent ported yet), then
        //   if let Some(data) = vec.get_occurrence_statistics_data(id) {
        //       acc_data.inc_deterministic_instance_occurrences_count(data.get_deterministic_instance_occurrences_count());
        //       acc_data.inc_non_deterministic_instance_occurrences_count(data.get_non_deterministic_instance_occurrences_count());
        //       acc_data.inc_existential_instance_occurrences_count(data.get_existential_instance_occurrences_count());
        //       acc_data.inc_individual_instance_occurrences_count(data.get_individual_instance_occurrences_count());
        //       acc_data.inc_incoming_node_instance_occurrences_count(data.get_incoming_node_instance_occurrences_count());
        //       acc_data.inc_outgoing_node_instance_occurrences_count(data.get_outgoing_node_instance_occurrences_count());
        //   }
        let _ = (id, &self.role_data_vec_linker);
        acc_data
    }

    /// Port of `COccurrenceStatisticsCacheOntologyData::getAccummulatedConceptDataOccurrenceStatistics(cint64 id)`.
    ///
    /// As the role variant but over `mConceptDataVecLinker` and only the four base
    /// counters (concept data has no in/out edge counts).
    pub fn get_accummulated_concept_data_occurrence_statistics(
        &self,
        id: Cint64,
    ) -> OccurrenceStatisticsConceptData {
        let acc_data = OccurrenceStatisticsConceptData::new();
        // W6-DEFER[api]: for each concept_data_vec_linker id (head→tail), resolve it to its
        // OccurrenceStatisticsCacheOntologyDataVector<ConceptData> via the cache vector arena, then
        //   if let Some(data) = vec.get_occurrence_statistics_data(id) {
        //       acc_data.inc_deterministic_instance_occurrences_count(data.get_deterministic_instance_occurrences_count());
        //       acc_data.inc_non_deterministic_instance_occurrences_count(data.get_non_deterministic_instance_occurrences_count());
        //       acc_data.inc_existential_instance_occurrences_count(data.get_existential_instance_occurrences_count());
        //       acc_data.inc_individual_instance_occurrences_count(data.get_individual_instance_occurrences_count());
        //   }
        let _ = (id, &self.concept_data_vec_linker);
        acc_data
    }

    /// Port of `COccurrenceStatisticsCacheOntologyData::getWriteableConceptDataVector(cint64 conCount)`.
    ///
    /// Reuses a freed vector if one is available, else allocates a fresh one and
    /// front-splices it onto the linker chain.
    pub fn get_writeable_concept_data_vector(
        &mut self,
        con_count: Cint64,
    ) -> OccStatConceptDataVecId {
        // C++: if (!mFreeConceptDataVecList.isEmpty()) vec = takeLast();
        let mut vec = OccStatConceptDataVecId::NONE;
        if let Some(free) = self.free_concept_data_vec_list.pop() {
            vec = free;
        }
        if vec == OccStatConceptDataVecId::NONE {
            // W6-DEFER[api]: vec = arena.alloc(OccurrenceStatisticsCacheOntologyDataVector::new(conCount));
            // CLinker head-front (PORT.md §6): self.concept_data_vec_linker.insert(0, vec);
            // (cache vector arena not yet ported.)
            let _ = con_count;
        }
        vec
    }

    /// Port of `COccurrenceStatisticsCacheOntologyData::getWriteableRoleDataVector(cint64 roleCount)`.
    pub fn get_writeable_role_data_vector(&mut self, role_count: Cint64) -> OccStatRoleDataVecId {
        let mut vec = OccStatRoleDataVecId::NONE;
        if let Some(free) = self.free_role_data_vec_list.pop() {
            vec = free;
        }
        if vec == OccStatRoleDataVecId::NONE {
            // W6-DEFER[api]: vec = arena.alloc(OccurrenceStatisticsCacheOntologyDataVector::new(roleCount));
            // CLinker head-front: self.role_data_vec_linker.insert(0, vec);
            let _ = role_count;
        }
        vec
    }

    /// Port of `COccurrenceStatisticsCacheOntologyData::releaseWrittenConceptDataVector` —
    /// `mFreeConceptDataVecList.append(vec)` (QList::append = push back).
    pub fn release_written_concept_data_vector(
        &mut self,
        vec: OccStatConceptDataVecId,
    ) -> &mut Self {
        self.free_concept_data_vec_list.push(vec);
        self
    }

    /// Port of `COccurrenceStatisticsCacheOntologyData::releaseWrittenRoleDataVector`.
    pub fn release_written_role_data_vector(&mut self, vec: OccStatRoleDataVecId) -> &mut Self {
        self.free_role_data_vec_list.push(vec);
        self
    }
}

// ===========================================================================
// Cache data store (`COccurrenceStatisticsCacheData`).
// ===========================================================================

/// Port of `COccurrenceStatisticsCacheData`.
///
/// The shared store: a read/write lock, the global update id, and the
/// ontology-id → per-ontology-data hash.
pub struct OccurrenceStatisticsCacheData {
    // KONCLUDE-PORT-NOTE[threading]: `QReadWriteLock mReadWriteLock` → opaque lock handle.
    /// `COccurrenceStatisticsCacheData::mReadWriteLock`.
    pub read_write_lock: Cint64,
    /// `COccurrenceStatisticsCacheData::mUpdateId`.
    pub update_id: Cint64,
    // KONCLUDE-PORT-NOTE[ownership]: `QHash<cint64,…OntologyData*> mOntologyDataHash`.
    /// `COccurrenceStatisticsCacheData::mOntologyDataHash`.
    pub ontology_data_hash: HashMap<Cint64, OccStatOntologyDataId>,
}

impl Default for OccurrenceStatisticsCacheData {
    fn default() -> Self {
        OccurrenceStatisticsCacheData {
            read_write_lock: 0,
            update_id: 0,
            ontology_data_hash: HashMap::new(),
        }
    }
}

impl OccurrenceStatisticsCacheData {
    /// Port of `COccurrenceStatisticsCacheData::COccurrenceStatisticsCacheData`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `COccurrenceStatisticsCacheData::getReadWriteLock` (`return &mReadWriteLock`).
    /// KONCLUDE-PORT-NOTE[threading]: the `QReadWriteLock*` is an opaque handle in the
    /// staged single-threaded port; callers' `lockForRead/lockForWrite/unlock` become
    /// inline no-ops (manifest §"Concurrency"). Returned by value for fidelity.
    pub fn get_read_write_lock(&self) -> Cint64 {
        self.read_write_lock
    }

    /// Port of `COccurrenceStatisticsCacheData::getUpdateId`.
    pub fn get_update_id(&self) -> Cint64 {
        self.update_id
    }

    /// Port of `COccurrenceStatisticsCacheData::incUpdateId` (`++mUpdateId`).
    pub fn inc_update_id(&mut self) -> &mut Self {
        self.update_id += 1;
        self
    }

    /// Port of `COccurrenceStatisticsCacheData::getOntologyData(cint64 ontologyId, bool createIfNotExists)`.
    ///
    /// Lookup-only branch is faithful (`QHash::value` → `nullptr` miss == `Id::NONE`);
    /// the create branch's allocation of a new ontology-data record needs the cache
    /// ontology-data arena, deferred.
    pub fn get_ontology_data(
        &mut self,
        ontology_id: Cint64,
        create_if_not_exists: bool,
    ) -> OccStatOntologyDataId {
        if !create_if_not_exists {
            // C++: return mOntologyDataHash.value(ontologyId);  (default-constructed nullptr on miss)
            self.ontology_data_hash
                .get(&ontology_id)
                .copied()
                .unwrap_or(OccStatOntologyDataId::NONE)
        } else {
            // C++: COccurrenceStatisticsCacheOntologyData*& ontologyData = mOntologyDataHash[ontologyId];
            let ontology_data = self
                .ontology_data_hash
                .get(&ontology_id)
                .copied()
                .unwrap_or(OccStatOntologyDataId::NONE);
            if ontology_data == OccStatOntologyDataId::NONE {
                // W6-DEFER[api]: ontologyData = arena.alloc(OccurrenceStatisticsCacheOntologyData::new());
                // self.ontology_data_hash.insert(ontology_id, ontologyData);
                // (cache ontology-data arena not yet ported.)
            }
            ontology_data
        }
    }
}

// ===========================================================================
// Context (`COccurrenceStatisticsCacheContext`).
// ===========================================================================

/// Port of `COccurrenceStatisticsCacheContext` (base `CContext`).
///
/// The per-cache memory-pool scratch context (structurally identical to the F2
/// expander-cache context).
pub struct OccurrenceStatisticsCacheContext {
    // KONCLUDE-PORT-NOTE[memory-pool]: `CMemoryPoolAllocationManager* mMemMan`.
    /// `COccurrenceStatisticsCacheContext::mMemMan`.
    pub mem_man: Cint64,
    // KONCLUDE-PORT-NOTE[memory-pool]: `CNewAllocationMemoryPoolProvider* mMemoryPoolProvider`.
    /// `COccurrenceStatisticsCacheContext::mMemoryPoolProvider`.
    pub memory_pool_provider: Cint64,
    /// `COccurrenceStatisticsCacheContext::mAddRelMemory`.
    pub add_rel_memory: Cint64,
}

impl Default for OccurrenceStatisticsCacheContext {
    fn default() -> Self {
        OccurrenceStatisticsCacheContext {
            mem_man: 0,
            memory_pool_provider: 0,
            add_rel_memory: 0,
        }
    }
}

impl OccurrenceStatisticsCacheContext {
    /// Port of `COccurrenceStatisticsCacheContext::COccurrenceStatisticsCacheContext`.
    ///
    /// KONCLUDE-PORT-NOTE[memory-pool]: the C++ ctor news a
    /// `CNewAllocationMemoryPoolProvider` and a `CLimitedReserveMemoryPoolAllocationManager`
    /// over it; both are opaque pool handles in the port. The dtor's `delete`s drop
    /// with the struct.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `COccurrenceStatisticsCacheContext::getMemoryAllocationManager` (`return mMemMan`).
    /// KONCLUDE-PORT-NOTE[memory-pool]: opaque pool-manager handle.
    pub fn get_memory_allocation_manager(&self) -> Cint64 {
        self.mem_man
    }

    /// Port of `COccurrenceStatisticsCacheContext::getMemoryPoolAllocationManager` (`return mMemMan`).
    pub fn get_memory_pool_allocation_manager(&self) -> Cint64 {
        self.mem_man
    }

    /// Port of `COccurrenceStatisticsCacheContext::getMemoryPoolProvider` (`return mMemoryPoolProvider`).
    pub fn get_memory_pool_provider(&self) -> Cint64 {
        self.memory_pool_provider
    }

    /// Port of `COccurrenceStatisticsCacheContext::getMemoryConsumption`.
    ///
    /// C++: `return mAddRelMemory + mMemoryPoolProvider->getAllocatedReleaseDifferencePoolSize();`
    pub fn get_memory_consumption(&self) -> Cint64 {
        // W6-DEFER[memory-pool]: + mMemoryPoolProvider->getAllocatedReleaseDifferencePoolSize()
        // (opaque pool-provider handle; the live-pool delta is 0 until the pool lands).
        self.add_rel_memory
    }

    /// Port of `COccurrenceStatisticsCacheContext::releaseTemporaryMemoryPools(CMemoryPool* memoryPools)`.
    ///
    /// C++ walks the `CMemoryPool*` chain summing `getMemoryBlockSize()` into
    /// `mAddRelMemory`, then `mMemMan->releaseTemporaryMemoryPools(memoryPools)`.
    /// KONCLUDE-PORT-NOTE[memory-pool]: the `CMemoryPool*` chain and the pool manager
    /// are opaque handles; both the size accumulation and the release are deferred.
    pub fn release_temporary_memory_pools(&mut self, memory_pools: Cint64) -> &mut Self {
        // W6-DEFER[memory-pool]: for (memoryPoolIt = memoryPools; memoryPoolIt; memoryPoolIt = memoryPoolIt->getNext())
        //     self.add_rel_memory += memoryPoolIt->getMemoryBlockSize();
        // mMemMan->releaseTemporaryMemoryPools(memoryPools);
        let _ = memory_pools;
        self
    }
}

// ===========================================================================
// Write data (`COccurrenceStatisticsCacheWriteData`).
// ===========================================================================

/// Port of `COccurrenceStatisticsCacheWriteData` (base `CCacheEntryWriteData`).
///
/// An empty write-data subclass (carries only the inherited F0 base header).
/// Not a record-family in F7 (single class), so ported as a plain struct.
pub struct OccurrenceStatisticsCacheWriteData {
    // --- from CCacheEntryWriteData (F0 base, not yet ported) ---
    // KONCLUDE-PORT-NOTE[api]: `CCacheEntryWriteData::mType` (CACHEWRITEDATATYPE, F0).
    /// `CCacheEntryWriteData::mType`.
    pub cache_write_data_type: Cint64,
    // KONCLUDE-PORT-NOTE[ownership]: `CCacheEntryWriteData` `CLinkerBase` write-data
    // chain → opaque (heterogeneous F0 base chain).
    /// `CLinkerBase` next write-data link.
    pub next: Cint64,
}

impl Default for OccurrenceStatisticsCacheWriteData {
    fn default() -> Self {
        OccurrenceStatisticsCacheWriteData {
            cache_write_data_type: 0,
            next: 0,
        }
    }
}

impl OccurrenceStatisticsCacheWriteData {
    /// Port of `COccurrenceStatisticsCacheWriteData::COccurrenceStatisticsCacheWriteData`.
    pub fn new() -> Self {
        Self::default()
    }
    // No further methods: `COccurrenceStatisticsCacheWriteData` is an empty subclass of
    // `CCacheEntryWriteData` (the .cpp has only the empty ctor; the discriminant
    // accessors live on the F0 base `cache::value::CacheEntryWriteData`).
}

// ===========================================================================
// Reader (`COccurrenceStatisticsCacheReader`).
// ===========================================================================

/// Port of `COccurrenceStatisticsCacheReader`.
///
/// A per-thread read cursor over the cache data, with the loaded per-ontology
/// data vectors cached behind the ontology tag / update id.
pub struct OccurrenceStatisticsCacheReader {
    // KONCLUDE-PORT-NOTE[ownership]: `COccurrenceStatisticsCacheData* mData`.
    /// `COccurrenceStatisticsCacheReader::mData`.
    pub data: OccStatCacheDataId,
    /// `COccurrenceStatisticsCacheReader::mOntologyTag`.
    pub ontology_tag: Cint64,
    /// `COccurrenceStatisticsCacheReader::mOntologyUpdateId`.
    pub ontology_update_id: Cint64,
    // KONCLUDE-PORT-NOTE[ownership]: `COccurrenceStatisticsCacheOntologyData* mOntologyData`.
    /// `COccurrenceStatisticsCacheReader::mOntologyData`.
    pub ontology_data: OccStatOntologyDataId,
}

impl Default for OccurrenceStatisticsCacheReader {
    fn default() -> Self {
        OccurrenceStatisticsCacheReader {
            data: OccStatCacheDataId::NONE,
            ontology_tag: 0,
            ontology_update_id: 0,
            ontology_data: OccStatOntologyDataId::NONE,
        }
    }
}

impl OccurrenceStatisticsCacheReader {
    /// Port of `COccurrenceStatisticsCacheReader::COccurrenceStatisticsCacheReader`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `COccurrenceStatisticsCacheReader::COccurrenceStatisticsCacheReader(COccurrenceStatisticsCacheData* data)`.
    ///
    /// The real (only) C++ constructor: `mData = data; mOntologyUpdateId = 0;
    /// mOntologyTag = -1; mOntologyData = nullptr;` (note `mOntologyTag = -1`, which
    /// `Default` cannot express).
    pub fn with_data(data: OccStatCacheDataId) -> Self {
        OccurrenceStatisticsCacheReader {
            data,
            ontology_tag: INVALID,
            ontology_update_id: 0,
            ontology_data: OccStatOntologyDataId::NONE,
        }
    }

    /// Port of `COccurrenceStatisticsCacheReader::getAccummulatedRoleDataOccurrenceStatistics(cint64 ontologyId, cint64 roleId)`.
    pub fn get_accummulated_role_data_occurrence_statistics(
        &mut self,
        ontology_id: Cint64,
        role_id: Cint64,
    ) -> OccurrenceStatisticsRoleData {
        let data = OccurrenceStatisticsRoleData::new();
        self.load_ontology_data_vectors(ontology_id);
        if self.ontology_data != OccStatOntologyDataId::NONE {
            // W6-DEFER[api]: data = ontology_data_arena.get(self.ontology_data)
            //     .get_accummulated_role_data_occurrence_statistics(role_id);
            // (cache ontology-data arena not yet ported.)
            let _ = role_id;
        }
        data
    }

    /// Context-threaded live port of
    /// `COccurrenceStatisticsCacheReader::getAccummulatedRoleDataOccurrenceStatistics`.
    pub fn get_accummulated_role_data_occurrence_statistics_with_context(
        &mut self,
        ontology_id: Cint64,
        role_id: Cint64,
        cache_context: &mut CacheContext,
    ) -> OccurrenceStatisticsRoleData {
        self.load_ontology_data_vectors_with_context(ontology_id, cache_context);
        if self.ontology_data == OccStatOntologyDataId::NONE {
            return OccurrenceStatisticsRoleData::new();
        }
        cache_context.occ_stat_ontology_data_get_accummulated_role_data_occurrence_statistics(
            self.ontology_data,
            role_id,
        )
    }

    /// Port of `COccurrenceStatisticsCacheReader::getAccummulatedConceptDataOccurrenceStatistics(cint64 ontologyId, cint64 conceptId)`.
    pub fn get_accummulated_concept_data_occurrence_statistics(
        &mut self,
        ontology_id: Cint64,
        concept_id: Cint64,
    ) -> OccurrenceStatisticsConceptData {
        let data = OccurrenceStatisticsConceptData::new();
        self.load_ontology_data_vectors(ontology_id);
        if self.ontology_data != OccStatOntologyDataId::NONE {
            // W6-DEFER[api]: data = ontology_data_arena.get(self.ontology_data)
            //     .get_accummulated_concept_data_occurrence_statistics(concept_id);
            let _ = concept_id;
        }
        data
    }

    /// Context-threaded live port of
    /// `COccurrenceStatisticsCacheReader::getAccummulatedConceptDataOccurrenceStatistics`.
    pub fn get_accummulated_concept_data_occurrence_statistics_with_context(
        &mut self,
        ontology_id: Cint64,
        concept_id: Cint64,
        cache_context: &mut CacheContext,
    ) -> OccurrenceStatisticsConceptData {
        self.load_ontology_data_vectors_with_context(ontology_id, cache_context);
        if self.ontology_data == OccStatOntologyDataId::NONE {
            return OccurrenceStatisticsConceptData::new();
        }
        cache_context.occ_stat_ontology_data_get_accummulated_concept_data_occurrence_statistics(
            self.ontology_data,
            concept_id,
        )
    }

    /// Port of `COccurrenceStatisticsCacheReader::loadOntologyDataVectors(cint64 ontologyId)` (protected).
    ///
    /// Refreshes the cached per-ontology data cursor when the requested ontology
    /// changes (or the data was never loaded and the global update id moved on),
    /// under a read lock. The `mData` dereferences (`getUpdateId` / `getOntologyData`)
    /// and the per-record usage refcount bumps need the cache-data + ontology-data
    /// arenas, deferred; the local cursor fields that don't require the arena are
    /// updated faithfully inside the same guard.
    pub fn load_ontology_data_vectors(&mut self, ontology_id: Cint64) -> &mut Self {
        // C++ guard: ontologyId != mOntologyTag || !mOntologyData && mOntologyUpdateId != mData->getUpdateId()
        // W6-DEFER[api]: the `mData->getUpdateId()` half of the condition derefs the
        // cache-data arena; conservatively re-evaluated whenever the ontology tag changes.
        if ontology_id != self.ontology_tag
            || (self.ontology_data == OccStatOntologyDataId::NONE/* W6-DEFER[api]: && self.ontology_update_id != data_arena.get(self.data).get_update_id() */)
        {
            // KONCLUDE-PORT-NOTE[threading]: mData->getReadWriteLock()->lockForRead() — no-op (staged single-thread).
            // W6-DEFER[api]: if (mOntologyData) mOntologyData->decUsageCount();
            // W6-DEFER[api]: mOntologyData = mData->getOntologyData(ontologyId, false);
            // W6-DEFER[api]: mOntologyData->incUsageCount();
            self.ontology_tag = ontology_id;
            // W6-DEFER[api]: mOntologyUpdateId = mData->getUpdateId();
            // KONCLUDE-PORT-NOTE[threading]: unlock() — no-op.
        }
        self
    }

    /// Context-threaded live port of
    /// `COccurrenceStatisticsCacheReader::loadOntologyDataVectors`.
    pub fn load_ontology_data_vectors_with_context(
        &mut self,
        ontology_id: Cint64,
        cache_context: &mut CacheContext,
    ) -> &mut Self {
        let update_id = if self.data.is_some() {
            cache_context.occ_stat_cache_data(self.data).get_update_id()
        } else {
            0
        };
        if ontology_id != self.ontology_tag
            || (self.ontology_data == OccStatOntologyDataId::NONE
                && self.ontology_update_id != update_id)
        {
            // KONCLUDE-PORT-NOTE[threading]: mData->getReadWriteLock()->lockForRead() — no-op.
            if self.ontology_data.is_some() {
                cache_context
                    .occ_stat_ontology_data_mut(self.ontology_data)
                    .dec_usage_count();
            }
            self.ontology_data =
                cache_context.occ_stat_cache_data_get_ontology_data(self.data, ontology_id, false);
            if self.ontology_data.is_some() {
                cache_context
                    .occ_stat_ontology_data_mut(self.ontology_data)
                    .inc_usage_count();
            }
            self.ontology_tag = ontology_id;
            self.ontology_update_id = update_id;
            // KONCLUDE-PORT-NOTE[threading]: unlock() — no-op.
        }
        self
    }
}

// ===========================================================================
// Writer (`COccurrenceStatisticsCacheWriter`).
// ===========================================================================

/// Port of `COccurrenceStatisticsCacheWriter`.
///
/// The write facade: holds the cache back-pointer + data store and the loaded
/// per-ontology concept/role data vectors being written.
pub struct OccurrenceStatisticsCacheWriter {
    // KONCLUDE-PORT-NOTE[ownership]: `COccurrenceStatisticsCache* mCache`
    // — back-pointer to the long-lived facade thread → opaque handle.
    /// `COccurrenceStatisticsCacheWriter::mCache`.
    pub cache: Cint64,
    // KONCLUDE-PORT-NOTE[ownership]: `COccurrenceStatisticsCacheData* mData`.
    /// `COccurrenceStatisticsCacheWriter::mData`.
    pub data: OccStatCacheDataId,
    /// `COccurrenceStatisticsCacheWriter::mOntologyTag`.
    pub ontology_tag: Cint64,
    // KONCLUDE-PORT-NOTE[ownership]: `COccurrenceStatisticsCacheOntologyData* mOntologyData`.
    /// `COccurrenceStatisticsCacheWriter::mOntologyData`.
    pub ontology_data: OccStatOntologyDataId,
    // KONCLUDE-PORT-NOTE[ownership]: `…OntologyDataVector<…ConceptData>* mConceptDataVector`.
    /// `COccurrenceStatisticsCacheWriter::mConceptDataVector`.
    pub concept_data_vector: OccStatConceptDataVecId,
    // KONCLUDE-PORT-NOTE[ownership]: `…OntologyDataVector<…RoleData>* mRoleDataVector`.
    /// `COccurrenceStatisticsCacheWriter::mRoleDataVector`.
    pub role_data_vector: OccStatRoleDataVecId,
}

impl Default for OccurrenceStatisticsCacheWriter {
    fn default() -> Self {
        OccurrenceStatisticsCacheWriter {
            cache: 0,
            data: OccStatCacheDataId::NONE,
            ontology_tag: 0,
            ontology_data: OccStatOntologyDataId::NONE,
            concept_data_vector: OccStatConceptDataVecId::NONE,
            role_data_vector: OccStatRoleDataVecId::NONE,
        }
    }
}

impl OccurrenceStatisticsCacheWriter {
    /// Port of `COccurrenceStatisticsCacheWriter::COccurrenceStatisticsCacheWriter`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `COccurrenceStatisticsCacheWriter::COccurrenceStatisticsCacheWriter(COccurrenceStatisticsCache* cache, COccurrenceStatisticsCacheData* data)`.
    ///
    /// `mCache(cache), mData(data)`, then `mOntologyTag = -1; mOntologyData = nullptr;`.
    /// KONCLUDE-PORT-NOTE[ownership]: `cache` is the opaque facade back-pointer.
    pub fn with_cache_data(cache: Cint64, data: OccStatCacheDataId) -> Self {
        OccurrenceStatisticsCacheWriter {
            cache,
            data,
            ontology_tag: INVALID,
            ontology_data: OccStatOntologyDataId::NONE,
            concept_data_vector: OccStatConceptDataVecId::NONE,
            role_data_vector: OccStatRoleDataVecId::NONE,
        }
    }

    /// Port of `COccurrenceStatisticsCacheWriter::writeCachedData(COccurrenceStatisticsCacheWriteData* writeData, CMemoryPool* memoryPools)`.
    ///
    /// C++: `mCache->writeCachedData(writeData, memoryPools); return this;`
    pub fn write_cached_data(
        &mut self,
        write_data: Id<OccurrenceStatisticsCacheWriteData>,
        memory_pools: Cint64,
    ) -> &mut Self {
        // W6-DEFER[api]: mCache->writeCachedData(writeData, memoryPools) — forwards to the
        // opaque facade back-pointer (which posts a CWriteCachedDataEvent to the writer thread).
        let _ = (write_data, memory_pools);
        self
    }

    /// Port of `COccurrenceStatisticsCacheWriter::loadOntologyDataVectors(CConcreteOntology* ontology)` (protected).
    ///
    /// When the working ontology changes: release the previously written vectors back
    /// to their free lists, drop the usage refcount, fetch (creating if needed) the new
    /// ontology data, bump its refcount, acquire fresh writeable concept/role vectors,
    /// and bump the global update id — all under a write lock.
    pub fn load_ontology_data_vectors(
        &mut self,
        ontology_id: Cint64,
        concept_count: Cint64,
        role_count: Cint64,
        cache_context: &mut CacheContext,
    ) -> &mut Self {
        if ontology_id != self.ontology_tag {
            // KONCLUDE-PORT-NOTE[threading]: mData->getReadWriteLock()->lockForWrite() — no-op.
            if self.ontology_data.is_some() {
                cache_context
                    .occ_stat_ontology_data_mut(self.ontology_data)
                    .release_written_concept_data_vector(self.concept_data_vector)
                    .release_written_role_data_vector(self.role_data_vector)
                    .dec_usage_count();
            }
            self.ontology_data =
                cache_context.occ_stat_cache_data_get_ontology_data(self.data, ontology_id, true);
            cache_context
                .occ_stat_ontology_data_mut(self.ontology_data)
                .inc_usage_count();
            self.concept_data_vector = cache_context
                .occ_stat_ontology_data_get_writeable_concept_data_vector(
                    self.ontology_data,
                    concept_count,
                );
            self.role_data_vector = cache_context
                .occ_stat_ontology_data_get_writeable_role_data_vector(
                    self.ontology_data,
                    role_count,
                );
            self.ontology_tag = ontology_id;
            cache_context
                .occ_stat_cache_data_mut(self.data)
                .inc_update_id();
            // KONCLUDE-PORT-NOTE[threading]: unlock() — no-op.
        }
        self
    }

    /// Port of `COccurrenceStatisticsCacheWriter::incConceptInstanceOccurrencceStatistics(...)`.
    ///
    /// (Name keeps the C++ spelling `Occurrencce` — typo-faithful per PORT.md §3.)
    /// Loads the vectors for `ontology`, then conditionally increments the four base
    /// counters of the concept-data slot for `conceptId` (each guarded by `!= 0`).
    pub fn inc_concept_instance_occurrencce_statistics(
        &mut self,
        ontology_id: Cint64,
        concept_count: Cint64,
        role_count: Cint64,
        concept_id: Cint64,
        deterministic_count: Cint64,
        nondeterministic_count: Cint64,
        individual_count: Cint64,
        existential_count: Cint64,
        cache_context: &mut CacheContext,
    ) -> &mut Self {
        self.load_ontology_data_vectors(ontology_id, concept_count, role_count, cache_context);
        if let Some(concept_data) = cache_context
            .occ_stat_concept_data_vec_mut(self.concept_data_vector)
            .get_occurrence_statistics_data(concept_id)
        {
            if deterministic_count != 0 {
                concept_data.inc_deterministic_instance_occurrences_count(deterministic_count);
            }
            if nondeterministic_count != 0 {
                concept_data
                    .inc_non_deterministic_instance_occurrences_count(nondeterministic_count);
            }
            if existential_count != 0 {
                concept_data.inc_existential_instance_occurrences_count(existential_count);
            }
            if individual_count != 0 {
                concept_data.inc_individual_instance_occurrences_count(individual_count);
            }
        }
        self
    }

    /// Port of `COccurrenceStatisticsCacheWriter::incRoleInstanceOccurrencceStatistics(...)`.
    ///
    /// As the concept variant, plus the role's outgoing/incoming edge counters.
    pub fn inc_role_instance_occurrencce_statistics(
        &mut self,
        ontology_id: Cint64,
        concept_count: Cint64,
        role_count: Cint64,
        role_id: Cint64,
        deterministic_count: Cint64,
        nondeterministic_count: Cint64,
        individual_count: Cint64,
        existential_count: Cint64,
        outgoing_count: Cint64,
        incoming_count: Cint64,
        cache_context: &mut CacheContext,
    ) -> &mut Self {
        self.load_ontology_data_vectors(ontology_id, concept_count, role_count, cache_context);
        if let Some(role_data) = cache_context
            .occ_stat_role_data_vec_mut(self.role_data_vector)
            .get_occurrence_statistics_data(role_id)
        {
            if deterministic_count != 0 {
                role_data.inc_deterministic_instance_occurrences_count(deterministic_count);
            }
            if nondeterministic_count != 0 {
                role_data.inc_non_deterministic_instance_occurrences_count(nondeterministic_count);
            }
            if existential_count != 0 {
                role_data.inc_existential_instance_occurrences_count(existential_count);
            }
            if individual_count != 0 {
                role_data.inc_individual_instance_occurrences_count(individual_count);
            }
            if outgoing_count != 0 {
                role_data.inc_outgoing_node_instance_occurrences_count(outgoing_count);
            }
            if incoming_count != 0 {
                role_data.inc_incoming_node_instance_occurrences_count(incoming_count);
            }
        }
        self
    }
}

// ===========================================================================
// Facade (`COccurrenceStatisticsCache`).
// ===========================================================================

/// Port of `COccurrenceStatisticsCache` (base `CThread`).
///
/// The cache facade / writer thread: owns the config, the cache-data store, the
/// write-data counter, statistics, and the per-cache memory-pool context.
pub struct OccurrenceStatisticsCache {
    // KONCLUDE-PORT-NOTE[threading]: `CThread` base (Qt worker thread) → opaque handle.
    /// `CThread` base handle.
    pub thread: Cint64,
    // KONCLUDE-PORT-NOTE[api]: `CConfiguration* mConfig` → opaque cross-subsystem handle.
    /// `COccurrenceStatisticsCache::mConfig`.
    pub config: Cint64,
    // KONCLUDE-PORT-NOTE[ownership]: `COccurrenceStatisticsCacheData* mCacheData`.
    /// `COccurrenceStatisticsCache::mCacheData`.
    pub cache_data: OccStatCacheDataId,
    /// `COccurrenceStatisticsCache::mWriteDataCount`.
    pub write_data_count: Cint64,
    // KONCLUDE-PORT-NOTE[api]: `CCacheStatistics mCacheStat` (F0) held by value → opaque.
    /// `COccurrenceStatisticsCache::mCacheStat`.
    pub cache_stat: Cint64,
    /// `COccurrenceStatisticsCache::mContext` (held by value).
    pub context: OccurrenceStatisticsCacheContext,
}

impl Default for OccurrenceStatisticsCache {
    fn default() -> Self {
        OccurrenceStatisticsCache {
            thread: 0,
            config: 0,
            cache_data: OccStatCacheDataId::NONE,
            write_data_count: 0,
            cache_stat: 0,
            context: OccurrenceStatisticsCacheContext::default(),
        }
    }
}

impl OccurrenceStatisticsCache {
    /// Port of `COccurrenceStatisticsCache::COccurrenceStatisticsCache`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `COccurrenceStatisticsCache::getCacheStatistics` (`return &mCacheStat`).
    /// KONCLUDE-PORT-NOTE[api]: `CCacheStatistics` is held opaque (`Cint64`) in the
    /// struct skeleton; returned by value as the handle.
    pub fn get_cache_statistics(&self) -> Cint64 {
        self.cache_stat
    }

    /// Port of `COccurrenceStatisticsCache::createCacheReader`.
    ///
    /// `new COccurrenceStatisticsCacheReader(mCacheData)`. KONCLUDE-PORT-NOTE[ownership]:
    /// the reader is a per-thread cursor, not an arena element, so it is returned by
    /// value (the caller owns it) rather than as an `Id`.
    pub fn create_cache_reader(&self) -> OccurrenceStatisticsCacheReader {
        OccurrenceStatisticsCacheReader::with_data(self.cache_data)
    }

    /// Port of `COccurrenceStatisticsCache::createCacheWriter`.
    ///
    /// `new COccurrenceStatisticsCacheWriter(this, mCacheData)`. KONCLUDE-PORT-NOTE[ownership]:
    /// `this` (the facade back-pointer) is opaque; passed as `0` (no stable handle in the
    /// staged port). Returned by value like the reader.
    pub fn create_cache_writer(&self) -> OccurrenceStatisticsCacheWriter {
        OccurrenceStatisticsCacheWriter::with_cache_data(0, self.cache_data)
    }

    /// Port of `COccurrenceStatisticsCache::writeCachedData(COccurrenceStatisticsCacheWriteData* writeData, CMemoryPool* memoryPools)`.
    ///
    /// C++: `postEvent(new CWriteCachedDataEvent(writeData, memoryPools)); return this;`
    pub fn write_cached_data(
        &mut self,
        write_data: Id<OccurrenceStatisticsCacheWriteData>,
        memory_pools: Cint64,
    ) -> &mut Self {
        // W6-DEFER[threading]: postEvent(new CWriteCachedDataEvent(writeData, memoryPools)).
        // In the staged single-thread port the worker IS the writer; the event would be
        // drained inline by self.process_customs_events(WRITE_CACHED_DATA_ENTRY, ...).
        let _ = (write_data, memory_pools);
        self
    }

    /// Port of `COccurrenceStatisticsCache::processCustomsEvents(QEvent::Type type, CCustomEvent* event)` (protected).
    ///
    /// The writer-thread event handler: defers to the `CThread` base, else handles the
    /// cached-data write event by releasing its temporary memory pools and refreshing
    /// the memory-consumption statistic.
    pub fn process_customs_events(&mut self, type_: Cint64, event_: Cint64) -> bool {
        // W6-DEFER[threading]: if (CThread::processCustomsEvents(type, event)) return true;
        if false {
            return true;
        } else if type_ == event::WRITE_CACHED_DATA_ENTRY {
            // W6-DEFER[api]: CWriteCachedDataEvent* wcde = (CWriteCachedDataEvent*)event;
            //                CMemoryPool* memoryPools = wcde->getMemoryPools();
            let memory_pools: Cint64 = 0;
            let _ = event_;
            self.context.release_temporary_memory_pools(memory_pools);
            // W6-DEFER[api]: mCacheStat.setMemoryConsumption(mContext.getMemoryConsumption());
            let _ = self.context.get_memory_consumption();
            return true;
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn occurrence_statistics_reader_accumulates_concept_vectors() {
        let mut ctx = CacheContext::new();
        let cache_data = ctx.alloc_occ_stat_cache_data(OccurrenceStatisticsCacheData::new());
        let mut writer_a = OccurrenceStatisticsCacheWriter::with_cache_data(0, cache_data);
        let mut writer_b = OccurrenceStatisticsCacheWriter::with_cache_data(0, cache_data);

        writer_a.inc_concept_instance_occurrencce_statistics(7, 4, 2, 3, 2, 0, 0, 1, &mut ctx);
        writer_b.inc_concept_instance_occurrencce_statistics(7, 4, 2, 3, 0, 5, 6, 0, &mut ctx);

        let mut reader = OccurrenceStatisticsCacheReader::with_data(cache_data);
        let stats =
            reader.get_accummulated_concept_data_occurrence_statistics_with_context(7, 3, &mut ctx);

        assert_eq!(stats.get_deterministic_instance_occurrences_count(), 2);
        assert_eq!(stats.get_non_deterministic_instance_occurrences_count(), 5);
        assert_eq!(stats.get_existential_instance_occurrences_count(), 1);
        assert_eq!(stats.get_individual_instance_occurrences_count(), 6);
    }

    #[test]
    fn occurrence_statistics_reader_accumulates_role_vectors() {
        let mut ctx = CacheContext::new();
        let cache_data = ctx.alloc_occ_stat_cache_data(OccurrenceStatisticsCacheData::new());
        let mut writer_a = OccurrenceStatisticsCacheWriter::with_cache_data(0, cache_data);
        let mut writer_b = OccurrenceStatisticsCacheWriter::with_cache_data(0, cache_data);

        writer_a.inc_role_instance_occurrencce_statistics(11, 3, 5, 4, 1, 0, 2, 0, 3, 4, &mut ctx);
        writer_b.inc_role_instance_occurrencce_statistics(11, 3, 5, 4, 0, 6, 0, 7, 8, 9, &mut ctx);

        let mut reader = OccurrenceStatisticsCacheReader::with_data(cache_data);
        let stats =
            reader.get_accummulated_role_data_occurrence_statistics_with_context(11, 4, &mut ctx);

        assert_eq!(stats.get_deterministic_instance_occurrences_count(), 1);
        assert_eq!(stats.get_non_deterministic_instance_occurrences_count(), 6);
        assert_eq!(stats.get_existential_instance_occurrences_count(), 7);
        assert_eq!(stats.get_individual_instance_occurrences_count(), 2);
        assert_eq!(stats.get_outgoing_node_instance_occurrences_count(), 11);
        assert_eq!(stats.get_incoming_node_instance_occurrences_count(), 13);
    }
}
