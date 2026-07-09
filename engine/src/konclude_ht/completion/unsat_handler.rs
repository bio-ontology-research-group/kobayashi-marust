//! `completion::unsat_handler` — port of
//! `CUnsatisfiableCacheHandler` slices.
//!
//! The full handler is the occurrence-unsat cache lookup bridge used by
//! `testIndividualNodeUnsatisfiableCached`. This module ports the memoization
//! guard and concept-data precheck/update substrate first; cache hash extraction
//! and clash descriptor generation remain explicit later slices.

#![allow(dead_code)]

use super::super::cache::context::CacheContext;
use super::super::cache::unsat::{ReaderId, WriterId};
use super::super::cache::value::{CacheValue, CacheValueIdentifier};
use super::super::model::concept::Concept;
use super::super::model::substrate::{Cint64, Id};
use super::super::process::descriptor::ClashDescriptor;
use super::super::process::unsat_retrieval::IndividualNodeUnsatisfiableOccurenceCacheRetrievalData;
use super::super::process::{ClashDescId, ConDescId, NodeId, TrackPointId};
use super::context::CalculationAlgorithmContextBase;

/// Port of `CUnsatisfiableCacheHandler`.
#[derive(Debug, Clone)]
pub struct UnsatisfiableCacheHandler {
    /// `mOccurUnsatCacheReader`.
    pub occur_unsat_cache_reader: ReaderId,
    /// `mOccurUnsatCacheWriter`.
    pub occur_unsat_cache_writer: WriterId,
    /// `mConfConceptDataUnsatisfiablePrecheck`.
    pub conf_concept_data_unsatisfiable_precheck: bool,
    /// `mUnsatItemList`.
    pub unsat_item_list: Vec<CacheValue>,
    /// KM diagnostics (not in Konclude): cache lines written this
    /// classification. Lives on the handler so it survives the per-probe env
    /// reset (the handler is CARRIED, see `reset_probe_env`).
    pub stat_write_count: u64,
    /// KM diagnostics: read probes answered "cached unsatisfiable".
    pub stat_hit_count: u64,
}

impl Default for UnsatisfiableCacheHandler {
    fn default() -> Self {
        Self {
            occur_unsat_cache_reader: ReaderId::NONE,
            occur_unsat_cache_writer: WriterId::NONE,
            conf_concept_data_unsatisfiable_precheck: true,
            unsat_item_list: Vec::new(),
            stat_write_count: 0,
            stat_hit_count: 0,
        }
    }
}

impl UnsatisfiableCacheHandler {
    /// Port of `CUnsatisfiableCacheHandler::CUnsatisfiableCacheHandler`.
    pub fn new(occur_unsat_cache_reader: ReaderId, occur_unsat_cache_writer: WriterId) -> Self {
        Self {
            occur_unsat_cache_reader,
            occur_unsat_cache_writer,
            ..Default::default()
        }
    }

    /// Port slice of `isIndividualNodeUnsatisfiableCached`.
    ///
    /// This implements the initial retrieval-data memoization guard, the
    /// concept-data unsatisfiable-cache precheck through
    /// `CUnsatisfiableCachingTags`, the exact-tag precheck clash extraction, the
    /// occurrence-reader hash fallback, and the final negative-check
    /// retrieval-data update.
    pub fn is_individual_node_unsatisfiable_cached(
        &mut self,
        individual_node: NodeId,
        clash_descriptors: &mut ClashDescId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
        cache_context: &mut CacheContext,
    ) -> bool {
        let label_set = calc_alg_context
            .process_context()
            .node(individual_node)
            .use_reapply_con_label_set;
        if label_set.is_none() || self.occur_unsat_cache_reader.is_none() {
            return false;
        }

        let con_des_linker = calc_alg_context
            .process_context()
            .label_set(label_set)
            .get_adding_sorted_concept_description_linker();
        let current_caching_tag = self.current_caching_tag(cache_context);

        let mut unsatisfiable_checked = false;
        let mut last_con_des = ConDescId::NONE;
        let mut last_ret_caching_tag: Cint64 = 0;

        let unsat_ret_data = calc_alg_context
            .process_context()
            .node(individual_node)
            .individual_unsatisfiable_cache_retrieval_data(false);
        if unsat_ret_data.is_some() {
            let ret_data = calc_alg_context
                .process_context()
                .unsat_cache_ret_data(unsat_ret_data);
            last_ret_caching_tag = ret_data.get_last_retrieval_caching_tag();
            last_con_des = ret_data.get_last_retrieval_concept_descriptor();
            if last_ret_caching_tag >= current_caching_tag && last_con_des == con_des_linker {
                return false;
            }
        }

        if last_con_des != con_des_linker {
            last_ret_caching_tag = 0;
        }

        if self.conf_concept_data_unsatisfiable_precheck {
            let precheck = self.collect_concept_data_unsatisfiable_precheck(
                con_des_linker,
                last_con_des,
                last_ret_caching_tag,
                calc_alg_context,
            );
            if precheck.direct_failed() {
                unsatisfiable_checked = true;
            } else if precheck.exact_tag_candidate()
                && self.extract_exact_tag_precheck_clashes(
                    individual_node,
                    label_set,
                    con_des_linker,
                    last_con_des,
                    last_ret_caching_tag,
                    precheck.min_max_cached_tag,
                    precheck.max_min_cached_tag,
                    clash_descriptors,
                    calc_alg_context,
                )
            {
                self.stat_hit_count += 1;
                return true;
            }
        }

        if !unsatisfiable_checked {
            match self.get_hash_cached_unsatisfiable_clashes(
                individual_node,
                label_set,
                clash_descriptors,
                calc_alg_context,
                cache_context,
            ) {
                HashCachedUnsatisfiableResult::Unsatisfiable => {
                    self.stat_hit_count += 1;
                    return true;
                }
                HashCachedUnsatisfiableResult::CheckedSatisfiable => {
                    unsatisfiable_checked = true;
                }
                HashCachedUnsatisfiableResult::NoCacheTestValues => return false,
            }
        }

        if unsatisfiable_checked {
            self.update_individual_node_unsat_retrieval_data(
                individual_node,
                con_des_linker,
                current_caching_tag,
                calc_alg_context,
            );
        }

        false
    }

    /// Port slice of `writeUnsatisfiableClashedDescriptors`.
    ///
    /// Converts the sorted tracked-clash descriptor chain into the occurrence
    /// unsat cache's `CCacheValue` list and sends it through the cache writer
    /// event path.
    pub fn write_unsatisfiable_clashed_descriptors(
        &mut self,
        tracked_clashed_des: ClashDescId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
        cache_context: &mut CacheContext,
    ) -> bool {
        if tracked_clashed_des.is_none() || self.occur_unsat_cache_writer.is_none() {
            return false;
        }

        self.unsat_item_list.clear();
        let mut tracked_it = tracked_clashed_des;
        while tracked_it.is_some() {
            let con_des = calc_alg_context
                .process_context()
                .clash_desc(tracked_it)
                .get_concept_descriptor();
            if con_des.is_some() {
                let con_des_ref = calc_alg_context.process_context().con_desc(con_des);
                let concept = con_des_ref.get_concept();
                if concept.is_some() {
                    let concept_tag = calc_alg_context
                        .base
                        .ontology_arenas
                        .concept(concept)
                        .get_concept_tag();
                    self.unsat_item_list.push(CacheValue::new_value(
                        concept_tag,
                        concept.raw,
                        if !con_des_ref.is_negated() {
                            CacheValueIdentifier::CacheValTagAndConcept
                        } else {
                            CacheValueIdentifier::CacheValTagAndNegatedConcept
                        },
                    ));
                }
            }
            tracked_it = calc_alg_context
                .process_context()
                .clash_desc(tracked_it)
                .get_next_descriptor();
        }

        let written = self.write_unsat_item_list_to_cache(calc_alg_context, cache_context);
        if written {
            self.stat_write_count += 1;
        }
        written
    }

    /// Port slice of `writeUnsatisfiableClashedConcept`.
    pub fn write_unsatisfiable_clashed_concept(
        &mut self,
        concept: Id<Concept>,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
        cache_context: &mut CacheContext,
    ) -> bool {
        if concept.is_none() || self.occur_unsat_cache_writer.is_none() {
            return false;
        }

        let concept_tag = calc_alg_context
            .base
            .ontology_arenas
            .concept(concept)
            .get_concept_tag();
        self.unsat_item_list.clear();
        self.unsat_item_list.push(CacheValue::new_value(
            concept_tag,
            concept.raw,
            CacheValueIdentifier::CacheValTagAndConcept,
        ));
        let written = self.write_unsat_item_list_to_cache(calc_alg_context, cache_context);
        if written {
            self.stat_write_count += 1;
        }
        written
    }

    fn write_unsat_item_list_to_cache(
        &self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
        cache_context: &mut CacheContext,
    ) -> bool {
        if self.unsat_item_list.is_empty() || self.occur_unsat_cache_writer.is_none() {
            return false;
        }

        let cache = cache_context
            .unsat_cache_writers
            .get(self.occur_unsat_cache_writer)
            .cache;
        let CacheContext {
            unsat_caches,
            unsat_cache_entries,
            unsat_cache_entries_hashes,
            unsat_cache_update_slot_items,
            unsat_cache_readers,
            ..
        } = cache_context;
        unsat_caches.get_mut(cache).process_customs_events(
            &self.unsat_item_list,
            unsat_cache_entries,
            unsat_cache_entries_hashes,
            unsat_cache_update_slot_items,
            unsat_cache_readers,
            &mut calc_alg_context.base.ontology_arenas,
        )
    }

    fn get_hash_cached_unsatisfiable_clashes(
        &mut self,
        individual_node: NodeId,
        label_set: super::super::process::LabelSetId,
        clash_descriptors: &mut ClashDescId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
        cache_context: &mut CacheContext,
    ) -> HashCachedUnsatisfiableResult {
        let mut cache_test_values: Vec<CacheValue> = Vec::new();
        let mut con_set_it = calc_alg_context
            .process_context()
            .label_set(label_set)
            .get_concept_label_set_iterator(true, false, false);
        while con_set_it.has_next() {
            let con_des = con_set_it.get_concept_descriptor();
            if self
                .descriptor_unsat_caching_tags(con_des, calc_alg_context)
                .is_some()
            {
                let con_des_ref = calc_alg_context.process_context().con_desc(con_des);
                let concept = con_des_ref.get_concept();
                let concept_tag = calc_alg_context
                    .base
                    .ontology_arenas
                    .concept(concept)
                    .get_concept_tag();
                cache_test_values.push(CacheValue::new_value(
                    concept_tag,
                    concept.raw,
                    if !con_des_ref.is_negated() {
                        CacheValueIdentifier::CacheValTagAndConcept
                    } else {
                        CacheValueIdentifier::CacheValTagAndNegatedConcept
                    },
                ));
            }
            con_set_it.move_next(calc_alg_context.process_context());
        }

        if cache_test_values.is_empty() {
            return HashCachedUnsatisfiableResult::NoCacheTestValues;
        }

        let cache = cache_context
            .unsat_cache_readers
            .get(self.occur_unsat_cache_reader)
            .cache;
        let unsat_items = {
            let reader = cache_context
                .unsat_cache_readers
                .get_mut(self.occur_unsat_cache_reader);
            reader.get_unsatisfiable_items_linker(
                &cache_test_values,
                cache_context.unsat_caches.get(cache),
                &cache_context.unsat_cache_entries,
                &cache_context.unsat_cache_entries_hashes,
                &mut cache_context.unsat_cache_update_slot_items,
            )
        };

        match unsat_items {
            Some(unsat_items) => {
                for cache_value in unsat_items {
                    let mut con_des = ConDescId::NONE;
                    let mut dep_track_point = TrackPointId::NONE;
                    if calc_alg_context
                        .process_context()
                        .label_set(label_set)
                        .get_concept_descriptor_by_tag(
                            cache_value.get_tag(),
                            &mut con_des,
                            &mut dep_track_point,
                        )
                    {
                        *clash_descriptors = self.create_clashed_concept_descriptor(
                            *clash_descriptors,
                            individual_node,
                            con_des,
                            dep_track_point,
                            calc_alg_context,
                        );
                    }
                }
                HashCachedUnsatisfiableResult::Unsatisfiable
            }
            None => HashCachedUnsatisfiableResult::CheckedSatisfiable,
        }
    }

    fn current_caching_tag(&self, cache_context: &CacheContext) -> Cint64 {
        let reader = cache_context.unsat_cache_reader(self.occur_unsat_cache_reader);
        let cache = cache_context.unsat_cache(reader.cache);
        reader.get_current_caching_tag(cache)
    }

    fn collect_concept_data_unsatisfiable_precheck(
        &self,
        con_des_linker: ConDescId,
        last_con_des: ConDescId,
        last_ret_caching_tag: Cint64,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> ConceptDataUnsatisfiablePrecheck {
        let mut min_max_cached_tag = Cint64::MAX;
        let mut max_min_cached_tag = Cint64::MIN;
        let mut min_unsat_cached_size = Cint64::MAX;
        let mut poss_cached_count: Cint64 = 0;

        let mut con_des_it = con_des_linker;
        while con_des_it.is_some() && last_con_des != con_des_it {
            let con_des = calc_alg_context.process_context().con_desc(con_des_it);
            let concept = con_des.get_concept();
            let con_neg = con_des.is_negated();
            if concept.is_some() {
                let concept_data = calc_alg_context
                    .base
                    .ontology_arenas
                    .concept(concept)
                    .get_concept_data();
                if concept_data >= 0 {
                    let con_proc_data = Id::new(concept_data);
                    let caching_tags = calc_alg_context
                        .base
                        .ontology_arenas
                        .concept_process_data(con_proc_data)
                        .get_unsatisfiable_caching_tags(con_neg);
                    if caching_tags.is_some() {
                        let tags = calc_alg_context
                            .base
                            .ontology_arenas
                            .unsatisfiable_caching_tags(caching_tags);
                        if tags.candidate_tags(
                            &mut min_max_cached_tag,
                            &mut max_min_cached_tag,
                            &mut min_unsat_cached_size,
                            last_ret_caching_tag + 1,
                        ) {
                            poss_cached_count += 1;
                        }
                    }
                }
            }
            con_des_it = con_des.get_next_concept_descriptor();
        }

        ConceptDataUnsatisfiablePrecheck {
            min_max_cached_tag,
            max_min_cached_tag,
            min_unsat_cached_size,
            poss_cached_count,
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn extract_exact_tag_precheck_clashes(
        &self,
        individual_node: NodeId,
        label_set: super::super::process::LabelSetId,
        con_des_linker: ConDescId,
        last_con_des: ConDescId,
        last_ret_caching_tag: Cint64,
        min_max_cached_tag: Cint64,
        max_min_cached_tag: Cint64,
        clash_descriptors: &mut ClashDescId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut unsat_line_count = Cint64::MAX;
        let mut found_unsat_line_count: Cint64 = 0;
        let mut con_des_it = con_des_linker;
        while con_des_it.is_some()
            && last_con_des != con_des_it
            && found_unsat_line_count <= unsat_line_count
        {
            if self.descriptor_has_candidate_tags(
                con_des_it,
                min_max_cached_tag,
                max_min_cached_tag,
                last_ret_caching_tag + 1,
                calc_alg_context,
            ) {
                found_unsat_line_count += 1;
                self.descriptor_candidate_min_unsatisfiable_size(
                    con_des_it,
                    &mut unsat_line_count,
                    max_min_cached_tag,
                    calc_alg_context,
                );
            }
            con_des_it = calc_alg_context
                .process_context()
                .con_desc(con_des_it)
                .get_next_concept_descriptor();
        }

        if found_unsat_line_count != unsat_line_count {
            return false;
        }

        let mut clash_linker_gen_count: Cint64 = 0;
        let mut clashed_dep_des_linker = ClashDescId::NONE;
        let mut con_set_it = calc_alg_context
            .process_context()
            .label_set(label_set)
            .get_concept_label_set_iterator(false, true, false);
        while con_set_it.has_next() {
            let con_des = con_set_it.get_concept_descriptor();
            if con_des.is_some()
                && self.descriptor_has_candidate_tags(
                    con_des,
                    min_max_cached_tag,
                    max_min_cached_tag,
                    last_ret_caching_tag + 1,
                    calc_alg_context,
                )
            {
                clash_linker_gen_count += 1;
                let dep_track_point =
                    con_set_it.get_dependency_track_point(calc_alg_context.process_context());
                clashed_dep_des_linker = self.create_clashed_concept_descriptor(
                    clashed_dep_des_linker,
                    individual_node,
                    con_des,
                    dep_track_point,
                    calc_alg_context,
                );
                if clash_linker_gen_count == unsat_line_count {
                    *clash_descriptors = self.append_clash_chain(
                        clashed_dep_des_linker,
                        *clash_descriptors,
                        calc_alg_context,
                    );
                    return true;
                }
            }
            con_set_it.move_next(calc_alg_context.process_context());
        }

        false
    }

    fn descriptor_has_candidate_tags(
        &self,
        con_des: ConDescId,
        min_max_cached_tag: Cint64,
        max_min_cached_tag: Cint64,
        required_last_caching_tag: Cint64,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> bool {
        if let Some(caching_tags) = self.descriptor_unsat_caching_tags(con_des, calc_alg_context) {
            let tags = calc_alg_context
                .base
                .ontology_arenas
                .unsatisfiable_caching_tags(caching_tags);
            tags.has_candidate_tags(
                min_max_cached_tag,
                max_min_cached_tag,
                required_last_caching_tag,
            )
        } else {
            false
        }
    }

    fn descriptor_candidate_min_unsatisfiable_size(
        &self,
        con_des: ConDescId,
        min_unsat_cached_size: &mut Cint64,
        cached_tag: Cint64,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> bool {
        if let Some(caching_tags) = self.descriptor_unsat_caching_tags(con_des, calc_alg_context) {
            let tags = calc_alg_context
                .base
                .ontology_arenas
                .unsatisfiable_caching_tags(caching_tags);
            tags.candidate_min_unsatisfiable_size(min_unsat_cached_size, cached_tag)
        } else {
            false
        }
    }

    fn descriptor_unsat_caching_tags(
        &self,
        con_des: ConDescId,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> Option<super::super::model::UnsatisfiableCachingTagsId> {
        let con_des_ref = calc_alg_context.process_context().con_desc(con_des);
        let concept = con_des_ref.get_concept();
        if concept.is_none() {
            return None;
        }
        let concept_data = calc_alg_context
            .base
            .ontology_arenas
            .concept(concept)
            .get_concept_data();
        if concept_data < 0 {
            return None;
        }
        let con_proc_data = Id::new(concept_data);
        let caching_tags = calc_alg_context
            .base
            .ontology_arenas
            .concept_process_data(con_proc_data)
            .get_unsatisfiable_caching_tags(con_des_ref.is_negated());
        caching_tags.is_some().then_some(caching_tags)
    }

    fn create_clashed_concept_descriptor(
        &self,
        prev_clashes: ClashDescId,
        process_indi: NodeId,
        con_des: ConDescId,
        prev_dep_track_point: super::super::process::TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> ClashDescId {
        let mut clash_descriptor = ClashDescriptor::new();
        clash_descriptor.init_clashed_concept_descriptor(
            con_des,
            prev_dep_track_point,
            process_indi,
        );
        if prev_clashes.is_some() {
            clash_descriptor.set_next(prev_clashes);
        }
        calc_alg_context
            .process_context_mut()
            .alloc_clash_desc(clash_descriptor)
    }

    fn append_clash_chain(
        &self,
        chain_head: ClashDescId,
        append_tail: ClashDescId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> ClashDescId {
        if chain_head.is_none() {
            return append_tail;
        }
        let mut tail = chain_head;
        loop {
            let next = calc_alg_context
                .process_context()
                .clash_desc(tail)
                .get_next_descriptor();
            if next.is_none() {
                calc_alg_context
                    .process_context_mut()
                    .clash_desc_mut(tail)
                    .set_next(append_tail);
                return chain_head;
            }
            tail = next;
        }
    }

    fn update_individual_node_unsat_retrieval_data(
        &self,
        individual_node: NodeId,
        con_des_linker: ConDescId,
        current_caching_tag: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let mut loc_unsat_ret_data = calc_alg_context
            .process_context()
            .node(individual_node)
            .individual_unsatisfiable_cache_retrieval_data(true);
        if loc_unsat_ret_data.is_none() {
            loc_unsat_ret_data = calc_alg_context
                .process_context_mut()
                .alloc_unsat_cache_ret_data(
                    IndividualNodeUnsatisfiableOccurenceCacheRetrievalData::new(),
                );
            calc_alg_context
                .process_context_mut()
                .node_mut(individual_node)
                .set_individual_unsatisfiable_cache_retrieval_data(loc_unsat_ret_data);
        }
        calc_alg_context
            .process_context_mut()
            .unsat_cache_ret_data_mut(loc_unsat_ret_data)
            .set_last_retrieval_caching_tag(current_caching_tag)
            .set_last_retrieval_concept_descriptor(con_des_linker);
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
struct ConceptDataUnsatisfiablePrecheck {
    min_max_cached_tag: Cint64,
    max_min_cached_tag: Cint64,
    min_unsat_cached_size: Cint64,
    poss_cached_count: Cint64,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum HashCachedUnsatisfiableResult {
    Unsatisfiable,
    CheckedSatisfiable,
    NoCacheTestValues,
}

impl ConceptDataUnsatisfiablePrecheck {
    fn direct_failed(&self) -> bool {
        self.poss_cached_count < self.min_unsat_cached_size
    }

    fn exact_tag_candidate(&self) -> bool {
        self.min_max_cached_tag == self.max_min_cached_tag
    }
}

#[cfg(test)]
mod tests {
    use super::super::super::cache::unsat::{
        OccurrenceUnsatisfiableCache, OccurrenceUnsatisfiableCacheReader,
        OccurrenceUnsatisfiableCacheWriter,
    };
    use super::super::super::model::concept::Concept;
    use super::super::super::model::concept_process::{
        ConceptProcessData, UnsatisfiableCachingTags,
    };
    use super::super::super::process::descriptor::{ClashDescriptorKind, ConceptDescriptor};
    use super::super::super::process::node::IndividualProcessNode;
    use super::super::super::process::satellites::{
        ConceptDescriptorDependencyReapplyData, ReapplyConceptLabelSet,
    };
    use super::super::super::process::unsat_retrieval::IndividualNodeUnsatisfiableOccurenceCacheRetrievalData;
    use super::*;

    fn cache_context_with_current_tag(tag: Cint64) -> (CacheContext, ReaderId, WriterId) {
        let mut cache_context = CacheContext::new();
        let cache = cache_context.alloc_unsat_cache(OccurrenceUnsatisfiableCache::new(1, "", 0));
        {
            let CacheContext {
                unsat_caches,
                unsat_cache_entries,
                unsat_cache_update_slot_items,
                ..
            } = &mut cache_context;
            unsat_caches
                .get_mut(cache)
                .thread_started(unsat_cache_entries, unsat_cache_update_slot_items);
            unsat_caches.get_mut(cache).caching_tag = tag;
        }
        let reader = {
            let CacheContext {
                unsat_caches,
                unsat_cache_readers,
                ..
            } = &mut cache_context;
            unsat_caches
                .get_mut(cache)
                .get_cache_reader(cache, unsat_cache_readers)
        };
        let writer = {
            let CacheContext {
                unsat_caches,
                unsat_cache_writers,
                ..
            } = &mut cache_context;
            unsat_caches
                .get_mut(cache)
                .get_cache_writer(cache, unsat_cache_writers)
        };
        (cache_context, reader, writer)
    }

    fn add_unsat_tags_for_descriptor(
        calc: &mut CalculationAlgorithmContextBase,
        con_desc: ConDescId,
        caching_tag: Cint64,
        cached_tag: Cint64,
        size: Cint64,
    ) {
        let concept = calc.process_context().con_desc(con_desc).get_concept();
        let con_proc = calc
            .base
            .ontology_arenas
            .alloc_concept_process_data(ConceptProcessData::new());
        calc.base
            .ontology_arenas
            .concept_mut(concept)
            .set_concept_data(con_proc.raw);
        let mut tags = UnsatisfiableCachingTags::new();
        tags.update_caching_tags(caching_tag, cached_tag, size);
        let tags = calc
            .base
            .ontology_arenas
            .alloc_unsatisfiable_caching_tags(tags);
        calc.base
            .ontology_arenas
            .concept_process_data_mut(con_proc)
            .set_unsatisfiable_caching_tags(false, tags);
    }

    fn add_descriptor_to_label_set_map(
        calc: &mut CalculationAlgorithmContextBase,
        node: NodeId,
        con_desc: ConDescId,
    ) {
        let concept_tag = calc
            .process_context()
            .con_desc(con_desc)
            .get_concept_tag(&calc.base.ontology_arenas);
        let label_set = calc.process_context().node(node).use_reapply_con_label_set;
        calc.process_context_mut()
            .label_set_mut(label_set)
            .concept_des_dep_map
            .insert(
                concept_tag,
                ConceptDescriptorDependencyReapplyData {
                    concept_descriptor: con_desc,
                    ..Default::default()
                },
            );
    }

    fn write_unsat_cache_entry(
        cache_context: &mut CacheContext,
        reader: ReaderId,
        cache_values: &[CacheValue],
        calc: &mut CalculationAlgorithmContextBase,
    ) {
        let cache = cache_context.unsat_cache_reader(reader).cache;
        let CacheContext {
            unsat_caches,
            unsat_cache_entries,
            unsat_cache_entries_hashes,
            unsat_cache_update_slot_items,
            unsat_cache_readers,
            ..
        } = cache_context;
        unsat_caches.get_mut(cache).process_customs_events(
            cache_values,
            unsat_cache_entries,
            unsat_cache_entries_hashes,
            unsat_cache_update_slot_items,
            unsat_cache_readers,
            &mut calc.base.ontology_arenas,
        );
    }

    fn context_with_labelled_node() -> (CalculationAlgorithmContextBase, NodeId, ConDescId) {
        let mut calc = CalculationAlgorithmContextBase::new();
        let mut concept_data = Concept::new();
        concept_data.set_concept_tag(11);
        let concept = calc.base.ontology_arenas.alloc_concept(concept_data);
        let mut con_desc = ConceptDescriptor::new();
        con_desc.concept = concept;
        let con_desc = calc.process_context_mut().alloc_con_desc(con_desc);

        let mut label_set = ReapplyConceptLabelSet::new(0);
        label_set.concept_des_linker = con_desc;
        label_set.concept_count = 1;
        let label_set = calc.process_context_mut().alloc_label_set(label_set);

        let node = calc
            .process_context_mut()
            .alloc_node(IndividualProcessNode::new(Id::NONE));
        calc.process_context_mut()
            .node_mut(node)
            .set_reapply_concept_label_set(label_set);

        (calc, node, con_desc)
    }

    #[test]
    fn unsat_cache_handler_memo_guard_returns_false_without_update() {
        let (mut cache_context, reader, writer) = cache_context_with_current_tag(5);
        let (mut calc, node, con_desc) = context_with_labelled_node();
        let mut data = IndividualNodeUnsatisfiableOccurenceCacheRetrievalData::new();
        data.set_last_retrieval_caching_tag(5)
            .set_last_retrieval_concept_descriptor(con_desc);
        let data = calc.process_context_mut().alloc_unsat_cache_ret_data(data);
        calc.process_context_mut()
            .node_mut(node)
            .set_individual_unsatisfiable_cache_retrieval_data(data);

        let mut handler = UnsatisfiableCacheHandler::new(reader, writer);
        let mut clash = ClashDescId::NONE;
        assert!(!handler.is_individual_node_unsatisfiable_cached(
            node,
            &mut clash,
            &mut calc,
            &mut cache_context
        ));
        assert_eq!(
            calc.process_context()
                .unsat_cache_ret_data(data)
                .get_last_retrieval_caching_tag(),
            5
        );
    }

    #[test]
    fn unsat_cache_handler_precheck_direct_fail_updates_retrieval_data() {
        let (mut cache_context, reader, writer) = cache_context_with_current_tag(7);
        let (mut calc, node, con_desc) = context_with_labelled_node();

        let concept = calc.process_context().con_desc(con_desc).get_concept();
        let con_proc = calc
            .base
            .ontology_arenas
            .alloc_concept_process_data(ConceptProcessData::new());
        calc.base
            .ontology_arenas
            .concept_mut(concept)
            .set_concept_data(con_proc.raw);
        let mut tags = UnsatisfiableCachingTags::new();
        tags.update_caching_tags(11, 6, 2);
        let tags = calc
            .base
            .ontology_arenas
            .alloc_unsatisfiable_caching_tags(tags);
        calc.base
            .ontology_arenas
            .concept_process_data_mut(con_proc)
            .set_unsatisfiable_caching_tags(false, tags);

        let mut handler = UnsatisfiableCacheHandler::new(reader, writer);
        let mut clash = ClashDescId::NONE;
        assert!(!handler.is_individual_node_unsatisfiable_cached(
            node,
            &mut clash,
            &mut calc,
            &mut cache_context
        ));

        let data = calc
            .process_context()
            .node(node)
            .individual_unsatisfiable_cache_retrieval_data(false);
        assert!(data.is_some());
        assert_eq!(
            calc.process_context()
                .unsat_cache_ret_data(data)
                .get_last_retrieval_caching_tag(),
            7
        );
        assert_eq!(
            calc.process_context()
                .unsat_cache_ret_data(data)
                .get_last_retrieval_concept_descriptor(),
            con_desc
        );
    }

    #[test]
    fn unsat_cache_handler_exact_tag_precheck_returns_clash_chain() {
        let (mut cache_context, reader, writer) = cache_context_with_current_tag(7);
        let (mut calc, node, con_desc) = context_with_labelled_node();

        let concept = calc.process_context().con_desc(con_desc).get_concept();
        let con_proc = calc
            .base
            .ontology_arenas
            .alloc_concept_process_data(ConceptProcessData::new());
        calc.base
            .ontology_arenas
            .concept_mut(concept)
            .set_concept_data(con_proc.raw);
        let mut tags = UnsatisfiableCachingTags::new();
        tags.update_caching_tags(11, 6, 1);
        let tags = calc
            .base
            .ontology_arenas
            .alloc_unsatisfiable_caching_tags(tags);
        calc.base
            .ontology_arenas
            .concept_process_data_mut(con_proc)
            .set_unsatisfiable_caching_tags(false, tags);

        let label_set = calc.process_context().node(node).use_reapply_con_label_set;
        calc.process_context_mut()
            .label_set_mut(label_set)
            .concept_des_dep_map
            .insert(
                11,
                ConceptDescriptorDependencyReapplyData {
                    concept_descriptor: con_desc,
                    ..Default::default()
                },
            );

        let existing_tail = calc
            .process_context_mut()
            .alloc_clash_desc(ClashDescriptor::new());
        let mut clash = existing_tail;
        let mut handler = UnsatisfiableCacheHandler::new(reader, writer);

        assert!(handler.is_individual_node_unsatisfiable_cached(
            node,
            &mut clash,
            &mut calc,
            &mut cache_context
        ));
        assert_ne!(clash, existing_tail);

        let head = calc.process_context().clash_desc(clash);
        assert_eq!(head.get_concept_descriptor(), con_desc);
        assert_eq!(head.get_appropriated_individual(), node);
        assert_eq!(head.get_next_descriptor(), existing_tail);
        assert!(matches!(head.kind, ClashDescriptorKind::Concept { .. }));
    }

    #[test]
    fn unsat_cache_handler_hash_miss_updates_retrieval_data() {
        let (mut cache_context, reader, writer) = cache_context_with_current_tag(9);
        let (mut calc, node, con_desc) = context_with_labelled_node();
        add_unsat_tags_for_descriptor(&mut calc, con_desc, 11, 8, 1);
        add_descriptor_to_label_set_map(&mut calc, node, con_desc);

        let mut handler = UnsatisfiableCacheHandler::new(reader, writer);
        handler.conf_concept_data_unsatisfiable_precheck = false;
        let mut clash = ClashDescId::NONE;

        assert!(!handler.is_individual_node_unsatisfiable_cached(
            node,
            &mut clash,
            &mut calc,
            &mut cache_context
        ));
        assert!(clash.is_none());

        let data = calc
            .process_context()
            .node(node)
            .individual_unsatisfiable_cache_retrieval_data(false);
        assert!(data.is_some());
        assert_eq!(
            calc.process_context()
                .unsat_cache_ret_data(data)
                .get_last_retrieval_caching_tag(),
            9
        );
        assert_eq!(
            calc.process_context()
                .unsat_cache_ret_data(data)
                .get_last_retrieval_concept_descriptor(),
            con_desc
        );
    }

    #[test]
    fn unsat_cache_handler_hash_hit_returns_clash_chain() {
        let (mut cache_context, reader, writer) = cache_context_with_current_tag(0);
        let (mut calc, node, con_desc) = context_with_labelled_node();
        add_unsat_tags_for_descriptor(&mut calc, con_desc, 11, 0, 1);
        add_descriptor_to_label_set_map(&mut calc, node, con_desc);

        let concept = calc.process_context().con_desc(con_desc).get_concept();
        let cache_value =
            CacheValue::new_value(11, concept.raw, CacheValueIdentifier::CacheValTagAndConcept);
        write_unsat_cache_entry(&mut cache_context, reader, &[cache_value], &mut calc);

        let existing_tail = calc
            .process_context_mut()
            .alloc_clash_desc(ClashDescriptor::new());
        let mut clash = existing_tail;
        let mut handler = UnsatisfiableCacheHandler::new(reader, writer);
        handler.conf_concept_data_unsatisfiable_precheck = false;

        assert!(handler.is_individual_node_unsatisfiable_cached(
            node,
            &mut clash,
            &mut calc,
            &mut cache_context
        ));
        assert_ne!(clash, existing_tail);

        let head = calc.process_context().clash_desc(clash);
        assert_eq!(head.get_concept_descriptor(), con_desc);
        assert_eq!(head.get_appropriated_individual(), node);
        assert_eq!(head.get_next_descriptor(), existing_tail);
        assert!(matches!(head.kind, ClashDescriptorKind::Concept { .. }));
    }

    #[test]
    fn unsat_cache_handler_write_clashed_descriptors_round_trips_to_reader() {
        let (mut cache_context, reader, writer) = cache_context_with_current_tag(0);
        let (mut calc, node, con_desc) = context_with_labelled_node();
        add_unsat_tags_for_descriptor(&mut calc, con_desc, 11, 0, 1);
        add_descriptor_to_label_set_map(&mut calc, node, con_desc);

        let mut tracked = ClashDescriptor::new();
        tracked.init_tracked_clashed_descriptor(
            node,
            0,
            0,
            false,
            con_desc,
            super::super::super::process::varbind::VarBindingPathId::NONE,
            TrackPointId::NONE,
            true,
            false,
            1,
            0,
            false,
        );
        let tracked = calc.process_context_mut().alloc_clash_desc(tracked);

        let mut handler = UnsatisfiableCacheHandler::new(reader, writer);
        assert!(handler.write_unsatisfiable_clashed_descriptors(
            tracked,
            &mut calc,
            &mut cache_context
        ));

        handler.conf_concept_data_unsatisfiable_precheck = false;
        let mut clash = ClashDescId::NONE;
        assert!(handler.is_individual_node_unsatisfiable_cached(
            node,
            &mut clash,
            &mut calc,
            &mut cache_context
        ));
        assert_eq!(
            calc.process_context()
                .clash_desc(clash)
                .get_concept_descriptor(),
            con_desc
        );
    }

    #[test]
    fn unsat_cache_handler_write_clashed_concept_round_trips_to_reader() {
        let (mut cache_context, reader, writer) = cache_context_with_current_tag(0);
        let (mut calc, node, con_desc) = context_with_labelled_node();
        add_unsat_tags_for_descriptor(&mut calc, con_desc, 11, 0, 1);
        add_descriptor_to_label_set_map(&mut calc, node, con_desc);
        let concept = calc.process_context().con_desc(con_desc).get_concept();

        let mut handler = UnsatisfiableCacheHandler::new(reader, writer);
        assert!(handler.write_unsatisfiable_clashed_concept(
            concept,
            &mut calc,
            &mut cache_context
        ));

        handler.conf_concept_data_unsatisfiable_precheck = false;
        let mut clash = ClashDescId::NONE;
        assert!(handler.is_individual_node_unsatisfiable_cached(
            node,
            &mut clash,
            &mut calc,
            &mut cache_context
        ));
        assert_eq!(
            calc.process_context()
                .clash_desc(clash)
                .get_concept_descriptor(),
            con_desc
        );
    }
}
