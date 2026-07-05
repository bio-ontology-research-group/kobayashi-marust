//! `completion::computed_cons_handler` — port of
//! `CComputedConsequencesCacheHandler` slices.
//!
//! The full handler caches inferred type consequences per nominal individual.
//! This module ports the root-unsat cache-writing surface: reader duplicate check,
//! cacheability gate seam, type write-data construction, add/commit message flow,
//! and cached-type linker access.

#![allow(dead_code)]

use super::super::cache::consequences::{
    ComputedConsequencesCacheReaderId, ComputedConsequencesCacheWriteTypesData,
    ComputedConsequencesCacheWriter, ComputedConsequencesTypesCacheEntryId,
};
use super::super::model::substrate::{Id, NegLink, INVALID};
use super::super::model::{ConceptId, IndividualId};
use super::context::CalculationAlgorithmContextBase;

/// Port of `CComputedConsequencesCacheHandler`.
pub struct ComputedConsequencesCacheHandler {
    /// `mSatCacheReader`.
    pub sat_cache_reader: ComputedConsequencesCacheReaderId,
    /// `mSatCacheWriter`.
    pub sat_cache_writer: ComputedConsequencesCacheWriter,
    /// `mWriteData`, modelled as a head-at-front chain.
    pub write_data: Vec<ComputedConsequencesCacheWriteTypesData>,
    /// Writes forwarded by the staged `commitCacheMessages` path.
    pub committed_type_write_data: Vec<ComputedConsequencesCacheWriteTypesData>,
    /// W6-DEFER[api]: stand-in for the upstream `canCacheTypeConcept` proof from
    /// consistence task data / deterministic and completion-graph cached tasks.
    pub cacheable_type_concepts: Vec<(IndividualId, ConceptId, bool)>,
}

impl Default for ComputedConsequencesCacheHandler {
    fn default() -> Self {
        Self {
            sat_cache_reader: Id::NONE,
            sat_cache_writer: ComputedConsequencesCacheWriter::default(),
            write_data: Vec::new(),
            committed_type_write_data: Vec::new(),
            cacheable_type_concepts: Vec::new(),
        }
    }
}

impl ComputedConsequencesCacheHandler {
    /// Port of `CComputedConsequencesCacheHandler::CComputedConsequencesCacheHandler`.
    pub fn new(
        sat_cache_reader: ComputedConsequencesCacheReaderId,
        sat_cache_writer: ComputedConsequencesCacheWriter,
    ) -> Self {
        Self {
            sat_cache_reader,
            sat_cache_writer,
            ..Default::default()
        }
    }

    /// Test/port seam for the still-deferred `canCacheTypeConcept` upstream proof.
    pub fn allow_type_concept_cache(
        &mut self,
        individual: IndividualId,
        concept: ConceptId,
        negation: bool,
    ) -> &mut Self {
        let key = (individual, concept, negation);
        if !self.cacheable_type_concepts.contains(&key) {
            self.cacheable_type_concepts.push(key);
        }
        self
    }

    /// Port slice of `canCacheTypeConcept`.
    pub fn can_cache_type_concept(
        &self,
        individual: IndividualId,
        concept: ConceptId,
        negation: bool,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> bool {
        if calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_terminology()
            == INVALID
        {
            return false;
        }

        // W6-DEFER[api]: the exact C++ proof walks ontology consistence model data
        // to the deterministic satisfiable task and completion-graph cached task.
        // Until that task-data bridge is live, callers can seed the same proof
        // result on the handler; default false preserves Konclude's guard.
        self.cacheable_type_concepts
            .contains(&(individual, concept, negation))
    }

    /// Port of `tryCacheTypeConcept`.
    pub fn try_cache_type_concept(
        &mut self,
        individual: IndividualId,
        concept: ConceptId,
        negation: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let _ = individual;
        let type_cache_entry = ComputedConsequencesTypesCacheEntryId::NONE;
        // W6-DEFER[api]: `getTypesCacheEntry` currently returns `Id::NONE` until
        // the individual process-data → computed-consequences entry bridge is live.
        let already_cached = type_cache_entry.is_some();

        if !already_cached
            && self.can_cache_type_concept(individual, concept, negation, calc_alg_context)
        {
            self.prepare_cache_messages(calc_alg_context);
            let mut write_data = ComputedConsequencesCacheWriteTypesData::new();
            write_data.init_types_cache_write_data(individual, concept, negation);
            self.add_cache_messages(write_data, calc_alg_context);
            return true;
        }

        false
    }

    /// Port of `getCachedTypesConceptLinker`.
    pub fn get_cached_types_concept_linker(
        &self,
        individual: IndividualId,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> Vec<NegLink<ConceptId>> {
        let _ = individual;
        let type_cache_entry = ComputedConsequencesTypesCacheEntryId::NONE;
        let _ = (type_cache_entry, calc_alg_context);
        Vec::new()
    }

    /// Port of `prepareCacheMessages`.
    pub fn prepare_cache_messages(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let _ = calc_alg_context;
        true
    }

    /// Port of `addCacheMessages`.
    pub fn add_cache_messages(
        &mut self,
        write_data: ComputedConsequencesCacheWriteTypesData,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        self.write_data.insert(0, write_data);
        self.commit_cache_messages(calc_alg_context);
        true
    }

    /// Port slice of `commitCacheMessages`.
    pub fn commit_cache_messages(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let _ = calc_alg_context;
        if self.write_data.is_empty() {
            return false;
        }
        let mut commit_write_data = Vec::new();
        while !self.write_data.is_empty() {
            let tmp_write_data = self.write_data.remove(0);
            commit_write_data.insert(0, tmp_write_data);
        }
        self.committed_type_write_data.extend(commit_write_data);
        true
    }
}
