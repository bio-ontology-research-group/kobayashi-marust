//! `cache::context` — the cache-pool arena container (the cache analogue of
//! `process::context::ProcessContext`).
//!
//! Port note: Konclude does NOT have a single `CCacheContext`. Each cache family
//! carries its OWN context object (`CComputedConsequencesCacheContext`,
//! `COccurrenceStatisticsCacheContext`, `CReuseCompletionGraphCacheContext`,
//! `CSaturationNodeAssociatedExpansionCacheContext`,
//! `CSignatureSatisfiableExpanderCacheContext`,
//! `CBackendRepresentativeMemoryCache{Base,Ontology,IndividualAssociation}Context`,
//! `CCacheTaggingPool`, …), each holding the per-family memory pools /
//! `CObjectAllocator<T>`s from which that family's records are bump-allocated.
//!
//! KONCLUDE-PORT-NOTE[memory-pool]: this `CacheContext` COLLAPSES all of those
//! per-family pools into one typed-arena container, exactly as
//! `process::context::ProcessContext` collapsed Konclude's single typeless
//! per-test pool. Each cache record family (every `CXxx*` that the cache stores
//! by pointer — i.e. every `Id<T>` alias the cache files declare) gets one
//! `Arena<T>` field here, addressed by the matching `Id<T>`. A `new CXxx(…)`
//! becomes `ctx.alloc_<stem>(Xxx::new(…))`; a `ptr->m()` becomes
//! `ctx.<stem>(id).m()`; a mutate becomes `ctx.<stem>_mut(id).m()`.
//!
//! Ownership / threading: the caches themselves (`CBackendRepresentativeMemoryCache`,
//! `CComputedConsequencesCache`, …) are long-lived singletons held by the cache
//! manager; their per-entry records are pool-allocated. The port keeps that split
//! — `CacheContext` is a standalone root that OWNS all the record arenas and is
//! threaded by `&CacheContext` / `&mut CacheContext` into the facade methods that
//! resolve/allocate records. It is NOT a `process::context::ProcessContext` field
//! (cache records outlive a single satisfiability test).

#![allow(dead_code)]

use super::super::model::substrate::{Arena, Id};
use super::{
    backend, backend_data, consequences, events, occstats, reuse, satnode, sigexpand, unsat, value,
};

/// Generate the `get / get_mut / alloc` accessor trio for one cache arena field.
///
/// Mirrors `process::context`'s `arena_accessors!`, adapted to derive the id type
/// as `Id<$ty>` directly (the cache files' per-family `…Id` aliases collide by
/// short name across modules — `ReaderId`, `WriterId`, `CacheEntryWriteDataId`, …
/// — so the macro keys off the unique struct type instead).
///
/// `obj->method()` (C++) ≡ `ctx.$get(id).method()` (Rust);
/// `obj->mutate()`       ≡ `ctx.$get_mut(id).mutate()`;
/// `new CXxx(…)`         ≡ `ctx.$alloc(Xxx::new(…))`.
macro_rules! cache_arena_accessors {
    ($field:ident, $ty:ty, $get:ident, $get_mut:ident, $alloc:ident) => {
        /// Resolve an id to a shared borrow (the `obj->` read path).
        #[inline]
        pub fn $get(&self, id: Id<$ty>) -> &$ty {
            self.$field.get(id)
        }
        /// Resolve an id to a mutable borrow (the `obj->` mutate path).
        #[inline]
        pub fn $get_mut(&mut self, id: Id<$ty>) -> &mut $ty {
            self.$field.get_mut(id)
        }
        /// Pool-allocate a new record, returning its stable id (`new CXxx(…)`).
        #[inline]
        pub fn $alloc(&mut self, v: $ty) -> Id<$ty> {
            self.$field.push(v)
        }
    };
}

/// The cache-pool arena container. One `Arena<T>` per cache record family.
#[derive(Default)]
pub struct CacheContext {
    // --- value ---
    pub cache_values: Arena<value::CacheValue>,
    pub cache_entries: Arena<value::CacheEntry>,
    pub cache_entry_write_datas: Arena<value::CacheEntryWriteData>,
    // --- unsat ---
    pub unsat_caches: Arena<unsat::OccurrenceUnsatisfiableCache>,
    pub unsat_cache_readers: Arena<unsat::OccurrenceUnsatisfiableCacheReader>,
    pub unsat_cache_writers: Arena<unsat::OccurrenceUnsatisfiableCacheWriter>,
    pub unsat_cache_entries: Arena<unsat::OccurrenceUnsatisfiableCacheEntry>,
    pub unsat_cache_entries_hashes: Arena<unsat::OccurrenceUnsatisfiableCacheEntriesHash>,
    pub unsat_cache_update_slot_items: Arena<unsat::OccurrenceUnsatisfiableCacheUpdateSlotItem>,
    // --- reuse ---
    pub reuse_cache_entries: Arena<reuse::ReuseCompletionGraphCacheEntry>,
    pub reuse_cache_slot_items: Arena<reuse::ReuseCompletionGraphCacheSlotItem>,
    pub reuse_cache_readers: Arena<reuse::ReuseCompletionGraphCacheReader>,
    pub reuse_compat_entry_hashes: Arena<reuse::ReuseCompletionGraphCompatibilityEntryHash>,
    // --- satnode ---
    pub sat_expansion_caches: Arena<satnode::SaturationNodeAssociatedExpansionCache>,
    pub sat_expansion_cache_readers: Arena<satnode::SaturationNodeAssociatedExpansionCacheReader>,
    pub sat_expansion_cache_entries: Arena<satnode::SaturationNodeAssociatedExpansionCacheEntry>,
    pub sat_node_cache_updaters: Arena<satnode::SaturationNodeCacheUpdater>,
    pub associated_concept_expansions: Arena<satnode::AssociatedConceptExpansion>,
    pub associated_concept_linkers: Arena<satnode::SaturationNodeAssociatedConceptLinker>,
    pub dependent_nominal_sets: Arena<satnode::SaturationNodeAssociatedDependentNominalSet>,
    // --- consequences ---
    pub consequences_caches: Arena<consequences::ComputedConsequencesCache>,
    pub consequences_cache_readers: Arena<consequences::ComputedConsequencesCacheReader>,
    pub consequences_cache_entries: Arena<consequences::ComputedConsequencesCacheEntry>,
    pub consequences_types_cache_entries: Arena<consequences::ComputedConsequencesTypesCacheEntry>,
    pub consequences_cache_write_datas: Arena<consequences::ComputedConsequencesCacheWriteData>,
    pub consequences_cache_write_types_datas: Arena<consequences::ComputedConsequencesCacheWriteTypesData>,
    // --- sigexpand ---
    pub sig_expander_cache_entries: Arena<sigexpand::SignatureSatisfiableExpanderCacheEntry>,
    pub sig_expander_slot_items: Arena<sigexpand::SignatureSatisfiableExpanderCacheSlotItem>,
    pub sig_expander_redirection_items: Arena<sigexpand::SignatureSatisfiableExpanderCacheRedirectionItem>,
    pub sig_expander_cache_readers: Arena<sigexpand::SignatureSatisfiableExpanderCacheReader>,
    pub expander_cache_value_linkers: Arena<sigexpand::ExpanderCacheValueLinker>,
    pub expander_branched_linkers: Arena<sigexpand::ExpanderBranchedLinker>,
    pub sig_expander_entry_write_datas: Arena<sigexpand::SignatureSatisfiableExpanderCacheEntryWriteData>,
    // --- occstats ---
    pub occ_stat_cache_datas: Arena<occstats::OccurrenceStatisticsCacheData>,
    pub occ_stat_ontology_datas: Arena<occstats::OccurrenceStatisticsCacheOntologyData>,
    // --- events ---
    pub caching_value_lists: Arena<events::CachingValueList>,
    pub caching_dep_hashes: Arena<events::CachingDepHash>,
    // --- backend ---
    pub backend_caches: Arena<backend::BackendRepresentativeMemoryCache>,
    pub backend_cache_readers: Arena<backend::BackendRepresentativeMemoryCacheReader>,
    pub backend_cache_writers: Arena<backend::BackendRepresentativeMemoryCacheWriter>,
    pub backend_label_assoc_write_datas: Arena<backend::BackendRepresentativeMemoryCacheLabelAssociationWriteData>,
    pub backend_slot_items: Arena<backend::BackendRepresentativeMemoryCacheSlotItem>,
    pub backend_base_contexts: Arena<backend::BackendRepresentativeMemoryCacheBaseContext>,
    pub backend_ontology_contexts: Arena<backend::BackendRepresentativeMemoryCacheOntologyContext>,
    pub backend_cache_write_datas: Arena<backend::CacheWriteData>,
    // --- backend_data ---
    pub ontology_datas: Arena<backend_data::OntologyData>,
    pub individual_assoc_datas: Arena<backend_data::IndividualAssociationData>,
    pub individual_assoc_contexts: Arena<backend_data::IndividualAssociationContext>,
    pub label_cache_items: Arena<backend_data::LabelCacheItem>,
    pub cardinality_cache_items: Arena<backend_data::CardinalityCacheItem>,
    pub label_value_linkers: Arena<backend_data::LabelValueLinker>,
    pub cardinality_value_linkers: Arena<backend_data::CardinalityValueLinker>,
    pub label_cache_item_ext_datas: Arena<backend_data::LabelCacheItemExtensionData>,
    pub tag_label_resolving_data_linkers: Arena<backend_data::LabelCacheItemTagLabelResolvingDataLinker>,
    pub individual_neighbour_role_set_hashes: Arena<backend_data::IndividualNeighbourRoleSetHash>,
    pub individual_role_set_neighbour_arrays: Arena<backend_data::IndividualRoleSetNeighbourArray>,
    pub individual_role_set_neighbour_datas: Arena<backend_data::IndividualRoleSetNeighbourData>,
    pub individual_role_set_neighbour_id_linkers: Arena<backend_data::IndividualRoleSetNeighbourIndividualIdLinker>,
    pub nominal_indirect_connection_datas: Arena<backend_data::NominalIndividualIndirectConnectionData>,
    pub item_individual_data_assoc_linkers: Arena<backend_data::ItemIndividualDataAssociationLinker>,
    pub role_assertion_linkers: Arena<backend_data::RoleAssertionLinker>,
    pub ontology_data_recomp_ref_linkers: Arena<backend_data::OntologyDataRecomputationReferenceLinker>,
    pub coordination_hash_datas: Arena<backend_data::BackendIndividualRetrievalComputationUpdateCoordinationHashData>,
    pub backend_temp_write_records: Arena<backend_data::BackendTempWriteRecord>,
}

impl CacheContext {
    /// Construct an empty cache context (all arenas empty).
    pub fn new() -> Self {
        Self::default()
    }

    // --- value accessors ---
    cache_arena_accessors!(cache_values, value::CacheValue, cache_value, cache_value_mut, alloc_cache_value);
    cache_arena_accessors!(cache_entries, value::CacheEntry, cache_entry, cache_entry_mut, alloc_cache_entry);
    cache_arena_accessors!(cache_entry_write_datas, value::CacheEntryWriteData, cache_entry_write_data, cache_entry_write_data_mut, alloc_cache_entry_write_data);
    // --- unsat accessors ---
    cache_arena_accessors!(unsat_caches, unsat::OccurrenceUnsatisfiableCache, unsat_cache, unsat_cache_mut, alloc_unsat_cache);
    cache_arena_accessors!(unsat_cache_readers, unsat::OccurrenceUnsatisfiableCacheReader, unsat_cache_reader, unsat_cache_reader_mut, alloc_unsat_cache_reader);
    cache_arena_accessors!(unsat_cache_writers, unsat::OccurrenceUnsatisfiableCacheWriter, unsat_cache_writer, unsat_cache_writer_mut, alloc_unsat_cache_writer);
    cache_arena_accessors!(unsat_cache_entries, unsat::OccurrenceUnsatisfiableCacheEntry, unsat_cache_entry, unsat_cache_entry_mut, alloc_unsat_cache_entry);
    cache_arena_accessors!(unsat_cache_entries_hashes, unsat::OccurrenceUnsatisfiableCacheEntriesHash, unsat_cache_entries_hash, unsat_cache_entries_hash_mut, alloc_unsat_cache_entries_hash);
    cache_arena_accessors!(unsat_cache_update_slot_items, unsat::OccurrenceUnsatisfiableCacheUpdateSlotItem, unsat_cache_update_slot_item, unsat_cache_update_slot_item_mut, alloc_unsat_cache_update_slot_item);
    // --- reuse accessors ---
    cache_arena_accessors!(reuse_cache_entries, reuse::ReuseCompletionGraphCacheEntry, reuse_cache_entry, reuse_cache_entry_mut, alloc_reuse_cache_entry);
    cache_arena_accessors!(reuse_cache_slot_items, reuse::ReuseCompletionGraphCacheSlotItem, reuse_cache_slot_item, reuse_cache_slot_item_mut, alloc_reuse_cache_slot_item);
    cache_arena_accessors!(reuse_cache_readers, reuse::ReuseCompletionGraphCacheReader, reuse_cache_reader, reuse_cache_reader_mut, alloc_reuse_cache_reader);
    cache_arena_accessors!(reuse_compat_entry_hashes, reuse::ReuseCompletionGraphCompatibilityEntryHash, reuse_compat_entry_hash, reuse_compat_entry_hash_mut, alloc_reuse_compat_entry_hash);
    // --- satnode accessors ---
    cache_arena_accessors!(sat_expansion_caches, satnode::SaturationNodeAssociatedExpansionCache, sat_expansion_cache, sat_expansion_cache_mut, alloc_sat_expansion_cache);
    cache_arena_accessors!(sat_expansion_cache_readers, satnode::SaturationNodeAssociatedExpansionCacheReader, sat_expansion_cache_reader, sat_expansion_cache_reader_mut, alloc_sat_expansion_cache_reader);
    cache_arena_accessors!(sat_expansion_cache_entries, satnode::SaturationNodeAssociatedExpansionCacheEntry, sat_expansion_cache_entry, sat_expansion_cache_entry_mut, alloc_sat_expansion_cache_entry);
    cache_arena_accessors!(sat_node_cache_updaters, satnode::SaturationNodeCacheUpdater, sat_node_cache_updater, sat_node_cache_updater_mut, alloc_sat_node_cache_updater);
    cache_arena_accessors!(associated_concept_expansions, satnode::AssociatedConceptExpansion, associated_concept_expansion, associated_concept_expansion_mut, alloc_associated_concept_expansion);
    cache_arena_accessors!(associated_concept_linkers, satnode::SaturationNodeAssociatedConceptLinker, associated_concept_linker, associated_concept_linker_mut, alloc_associated_concept_linker);
    cache_arena_accessors!(dependent_nominal_sets, satnode::SaturationNodeAssociatedDependentNominalSet, dependent_nominal_set, dependent_nominal_set_mut, alloc_dependent_nominal_set);
    // --- consequences accessors ---
    cache_arena_accessors!(consequences_caches, consequences::ComputedConsequencesCache, consequences_cache, consequences_cache_mut, alloc_consequences_cache);
    cache_arena_accessors!(consequences_cache_readers, consequences::ComputedConsequencesCacheReader, consequences_cache_reader, consequences_cache_reader_mut, alloc_consequences_cache_reader);
    cache_arena_accessors!(consequences_cache_entries, consequences::ComputedConsequencesCacheEntry, consequences_cache_entry, consequences_cache_entry_mut, alloc_consequences_cache_entry);
    cache_arena_accessors!(consequences_types_cache_entries, consequences::ComputedConsequencesTypesCacheEntry, consequences_types_cache_entry, consequences_types_cache_entry_mut, alloc_consequences_types_cache_entry);
    cache_arena_accessors!(consequences_cache_write_datas, consequences::ComputedConsequencesCacheWriteData, consequences_cache_write_data, consequences_cache_write_data_mut, alloc_consequences_cache_write_data);
    cache_arena_accessors!(consequences_cache_write_types_datas, consequences::ComputedConsequencesCacheWriteTypesData, consequences_cache_write_types_data, consequences_cache_write_types_data_mut, alloc_consequences_cache_write_types_data);
    // --- sigexpand accessors ---
    cache_arena_accessors!(sig_expander_cache_entries, sigexpand::SignatureSatisfiableExpanderCacheEntry, sig_expander_cache_entry, sig_expander_cache_entry_mut, alloc_sig_expander_cache_entry);
    cache_arena_accessors!(sig_expander_slot_items, sigexpand::SignatureSatisfiableExpanderCacheSlotItem, sig_expander_slot_item, sig_expander_slot_item_mut, alloc_sig_expander_slot_item);
    cache_arena_accessors!(sig_expander_redirection_items, sigexpand::SignatureSatisfiableExpanderCacheRedirectionItem, sig_expander_redirection_item, sig_expander_redirection_item_mut, alloc_sig_expander_redirection_item);
    cache_arena_accessors!(sig_expander_cache_readers, sigexpand::SignatureSatisfiableExpanderCacheReader, sig_expander_cache_reader, sig_expander_cache_reader_mut, alloc_sig_expander_cache_reader);
    cache_arena_accessors!(expander_cache_value_linkers, sigexpand::ExpanderCacheValueLinker, expander_cache_value_linker, expander_cache_value_linker_mut, alloc_expander_cache_value_linker);
    cache_arena_accessors!(expander_branched_linkers, sigexpand::ExpanderBranchedLinker, expander_branched_linker, expander_branched_linker_mut, alloc_expander_branched_linker);
    cache_arena_accessors!(sig_expander_entry_write_datas, sigexpand::SignatureSatisfiableExpanderCacheEntryWriteData, sig_expander_entry_write_data, sig_expander_entry_write_data_mut, alloc_sig_expander_entry_write_data);
    // --- occstats accessors ---
    cache_arena_accessors!(occ_stat_cache_datas, occstats::OccurrenceStatisticsCacheData, occ_stat_cache_data, occ_stat_cache_data_mut, alloc_occ_stat_cache_data);
    cache_arena_accessors!(occ_stat_ontology_datas, occstats::OccurrenceStatisticsCacheOntologyData, occ_stat_ontology_data, occ_stat_ontology_data_mut, alloc_occ_stat_ontology_data);
    // --- events accessors ---
    cache_arena_accessors!(caching_value_lists, events::CachingValueList, caching_value_list, caching_value_list_mut, alloc_caching_value_list);
    cache_arena_accessors!(caching_dep_hashes, events::CachingDepHash, caching_dep_hash, caching_dep_hash_mut, alloc_caching_dep_hash);
    // --- backend accessors ---
    cache_arena_accessors!(backend_caches, backend::BackendRepresentativeMemoryCache, backend_cache, backend_cache_mut, alloc_backend_cache);
    cache_arena_accessors!(backend_cache_readers, backend::BackendRepresentativeMemoryCacheReader, backend_cache_reader, backend_cache_reader_mut, alloc_backend_cache_reader);
    cache_arena_accessors!(backend_cache_writers, backend::BackendRepresentativeMemoryCacheWriter, backend_cache_writer, backend_cache_writer_mut, alloc_backend_cache_writer);
    cache_arena_accessors!(backend_label_assoc_write_datas, backend::BackendRepresentativeMemoryCacheLabelAssociationWriteData, backend_label_assoc_write_data, backend_label_assoc_write_data_mut, alloc_backend_label_assoc_write_data);
    cache_arena_accessors!(backend_slot_items, backend::BackendRepresentativeMemoryCacheSlotItem, backend_slot_item, backend_slot_item_mut, alloc_backend_slot_item);
    cache_arena_accessors!(backend_base_contexts, backend::BackendRepresentativeMemoryCacheBaseContext, backend_base_context, backend_base_context_mut, alloc_backend_base_context);
    cache_arena_accessors!(backend_ontology_contexts, backend::BackendRepresentativeMemoryCacheOntologyContext, backend_ontology_context, backend_ontology_context_mut, alloc_backend_ontology_context);
    cache_arena_accessors!(backend_cache_write_datas, backend::CacheWriteData, backend_cache_write_data, backend_cache_write_data_mut, alloc_backend_cache_write_data);
    // --- backend_data accessors ---
    cache_arena_accessors!(ontology_datas, backend_data::OntologyData, ontology_data, ontology_data_mut, alloc_ontology_data);
    cache_arena_accessors!(individual_assoc_datas, backend_data::IndividualAssociationData, individual_assoc_data, individual_assoc_data_mut, alloc_individual_assoc_data);
    cache_arena_accessors!(individual_assoc_contexts, backend_data::IndividualAssociationContext, individual_assoc_context, individual_assoc_context_mut, alloc_individual_assoc_context);
    cache_arena_accessors!(label_cache_items, backend_data::LabelCacheItem, label_cache_item, label_cache_item_mut, alloc_label_cache_item);
    cache_arena_accessors!(cardinality_cache_items, backend_data::CardinalityCacheItem, cardinality_cache_item, cardinality_cache_item_mut, alloc_cardinality_cache_item);
    cache_arena_accessors!(label_value_linkers, backend_data::LabelValueLinker, label_value_linker, label_value_linker_mut, alloc_label_value_linker);
    cache_arena_accessors!(cardinality_value_linkers, backend_data::CardinalityValueLinker, cardinality_value_linker, cardinality_value_linker_mut, alloc_cardinality_value_linker);
    cache_arena_accessors!(label_cache_item_ext_datas, backend_data::LabelCacheItemExtensionData, label_cache_item_ext_data, label_cache_item_ext_data_mut, alloc_label_cache_item_ext_data);
    cache_arena_accessors!(tag_label_resolving_data_linkers, backend_data::LabelCacheItemTagLabelResolvingDataLinker, tag_label_resolving_data_linker, tag_label_resolving_data_linker_mut, alloc_tag_label_resolving_data_linker);
    cache_arena_accessors!(individual_neighbour_role_set_hashes, backend_data::IndividualNeighbourRoleSetHash, individual_neighbour_role_set_hash, individual_neighbour_role_set_hash_mut, alloc_individual_neighbour_role_set_hash);
    cache_arena_accessors!(individual_role_set_neighbour_arrays, backend_data::IndividualRoleSetNeighbourArray, individual_role_set_neighbour_array, individual_role_set_neighbour_array_mut, alloc_individual_role_set_neighbour_array);
    cache_arena_accessors!(individual_role_set_neighbour_datas, backend_data::IndividualRoleSetNeighbourData, individual_role_set_neighbour_data, individual_role_set_neighbour_data_mut, alloc_individual_role_set_neighbour_data);
    cache_arena_accessors!(individual_role_set_neighbour_id_linkers, backend_data::IndividualRoleSetNeighbourIndividualIdLinker, individual_role_set_neighbour_id_linker, individual_role_set_neighbour_id_linker_mut, alloc_individual_role_set_neighbour_id_linker);
    cache_arena_accessors!(nominal_indirect_connection_datas, backend_data::NominalIndividualIndirectConnectionData, nominal_indirect_connection_data, nominal_indirect_connection_data_mut, alloc_nominal_indirect_connection_data);
    cache_arena_accessors!(item_individual_data_assoc_linkers, backend_data::ItemIndividualDataAssociationLinker, item_individual_data_assoc_linker, item_individual_data_assoc_linker_mut, alloc_item_individual_data_assoc_linker);
    cache_arena_accessors!(role_assertion_linkers, backend_data::RoleAssertionLinker, role_assertion_linker, role_assertion_linker_mut, alloc_role_assertion_linker);
    cache_arena_accessors!(ontology_data_recomp_ref_linkers, backend_data::OntologyDataRecomputationReferenceLinker, ontology_data_recomp_ref_linker, ontology_data_recomp_ref_linker_mut, alloc_ontology_data_recomp_ref_linker);
    cache_arena_accessors!(coordination_hash_datas, backend_data::BackendIndividualRetrievalComputationUpdateCoordinationHashData, coordination_hash_data, coordination_hash_data_mut, alloc_coordination_hash_data);
    cache_arena_accessors!(backend_temp_write_records, backend_data::BackendTempWriteRecord, backend_temp_write_record, backend_temp_write_record_mut, alloc_backend_temp_write_record);
}
