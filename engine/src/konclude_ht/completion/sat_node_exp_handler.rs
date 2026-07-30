//! `completion::sat_node_exp_handler` — port of
//! `CSaturationNodeExpansionCacheHandler` slices.
//!
//! The full handler bridges completion/saturation concepts to the saturation-node
//! associated-expansion cache. This module ports the concept-unsatisfiability
//! queueing path first: concept → saturation node lookup, already-clashed guard,
//! unsat write-data construction, and the handler's pending write-data chain.

#![allow(dead_code)]

use super::super::cache::context::CacheContext;
use super::super::cache::satnode::{
    AssociatedConceptExpansionId, AssociatedConceptLinkerId, DependentNominalSetId,
    SatExpansionCacheEntryId, SatExpansionCacheReaderId, SaturationNodeAssociatedConceptLinker,
    SaturationNodeAssociatedDependentNominalSet,
    SaturationNodeAssociatedExpansionCacheExpansionWriteData,
    SaturationNodeAssociatedExpansionCacheUnsatisfiabilityWriteData,
    SaturationNodeAssociatedExpansionCacheWriteDataRecord,
    SaturationNodeAssociatedExpansionCacheWriter,
};
use super::super::cache::value::{CacheValue, CacheValueIdentifier};
use super::super::model::op::{CCATLEAST, CCATMOST};
use super::super::model::substrate::{Cint64, Id, INVALID};
use super::super::model::{ConceptId, RoleId};
use super::super::process::dependency::DepKind;
use super::super::process::node::IndividualProcessNode;
use super::super::process::sat_node::IndividualSaturationProcessNodeStatusFlags;
use super::super::process::stubs::IndiSatBlockDataId;
use super::super::process::{ConDescId, LabelSetId, NodeId, SatNodeId, TrackPointId};
use super::context::CalculationAlgorithmContextBase;

/// Rust equivalent of the three out-parameters of
/// `CSaturationNodeExpansionCacheHandler::testNodeCachingPossible`.
pub struct SaturationNodeCachingPossibleData {
    pub only_if_completely_deterministic: bool,
    pub only_all_nondeterministic: bool,
    pub cache_entry: SatExpansionCacheEntryId,
}

/// Port of `CSaturationNodeExpansionCacheHandler`.
pub struct SaturationNodeExpansionCacheHandler {
    /// `mSatCacheReader`.
    pub sat_cache_reader: SatExpansionCacheReaderId,
    /// `mSatCacheWriter`.
    pub sat_cache_writer: SaturationNodeAssociatedExpansionCacheWriter,
    /// `mWriteData`, modelled as a head-at-front chain.
    pub write_data: Vec<SaturationNodeAssociatedExpansionCacheWriteDataRecord>,
}

impl Default for SaturationNodeExpansionCacheHandler {
    fn default() -> Self {
        Self {
            sat_cache_reader: Id::NONE,
            sat_cache_writer: SaturationNodeAssociatedExpansionCacheWriter::default(),
            write_data: Vec::new(),
        }
    }
}

impl SaturationNodeExpansionCacheHandler {
    /// Port of `CSaturationNodeExpansionCacheHandler::CSaturationNodeExpansionCacheHandler`.
    pub fn new(
        sat_cache_reader: SatExpansionCacheReaderId,
        sat_cache_writer: SaturationNodeAssociatedExpansionCacheWriter,
    ) -> Self {
        Self {
            sat_cache_reader,
            sat_cache_writer,
            ..Default::default()
        }
    }

    /// Port of `getSaturationIndividualNodeForConcept`.
    pub fn get_saturation_individual_node_for_concept(
        &self,
        concept: ConceptId,
        negation: bool,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> SatNodeId {
        let concept_data = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_concept_data();
        if concept_data == INVALID {
            return Id::NONE;
        }

        let con_ref_linking = calc_alg_context
            .ontology_arenas()
            .concept_process_data(Id::new(concept_data))
            .get_concept_reference_linking();
        if con_ref_linking.is_none() {
            return Id::NONE;
        }

        let sat_calc_ref_link_data = calc_alg_context
            .ontology_arenas()
            .concept_saturation_reference_linking_data(con_ref_linking)
            .get_concept_saturation_reference_linking_data(negation);
        if sat_calc_ref_link_data.is_none() {
            return Id::NONE;
        }

        calc_alg_context
            .ontology_arenas()
            .saturation_concept_reference_linking(sat_calc_ref_link_data)
            .get_individual_process_node_for_concept()
    }

    /// Port of `cacheUnsatisfiableConcept`.
    pub fn cache_unsatisfiable_concept(
        &mut self,
        concept: ConceptId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let saturation_indi_node =
            self.get_saturation_individual_node_for_concept(concept, false, calc_alg_context);

        if saturation_indi_node.is_some()
            && !calc_alg_context
                .process_context()
                .sat_node(saturation_indi_node)
                .indirect_status_flags
                .has_clashed_flag()
        {
            self.prepare_cache_messages(calc_alg_context);
            let mut unsat_write_data =
                SaturationNodeAssociatedExpansionCacheUnsatisfiabilityWriteData::new();
            unsat_write_data.init_unsatisfiability_write_data(saturation_indi_node);
            self.add_unsat_cache_message(unsat_write_data, calc_alg_context);
            return true;
        }

        false
    }

    /// Port of `isConceptUnsatisfiableCached`.
    pub fn is_concept_unsatisfiable_cached(
        &self,
        concept: ConceptId,
        negation: bool,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> bool {
        let saturation_indi_node =
            self.get_saturation_individual_node_for_concept(concept, negation, calc_alg_context);
        saturation_indi_node.is_some()
            && calc_alg_context
                .process_context()
                .sat_node(saturation_indi_node)
                .indirect_status_flags
                .has_clashed_flag()
    }

    /// Port of `isNodeSatisfiableCached`.
    ///
    /// Returns the C++ bool result plus the nullable out-parameter
    /// `CSaturationNodeAssociatedConceptExpansion*& expansion`.
    pub fn is_node_satisfiable_cached(
        &self,
        individual_process_node: NodeId,
        calc_alg_context: &CalculationAlgorithmContextBase,
        cache_context: &CacheContext,
    ) -> (bool, AssociatedConceptExpansionId) {
        let process_context = calc_alg_context.process_context();
        let node = process_context.node(individual_process_node);
        let sat_block_data = node.individual_saturation_blocking_data(false);
        let con_set = node.use_reapply_con_label_set;
        if con_set.is_none() || sat_block_data.is_none() {
            return (false, AssociatedConceptExpansionId::NONE);
        }

        let con_set_ref = process_context.label_set(con_set);
        let last_added_con_des = con_set_ref.get_adding_sorted_concept_description_linker();
        let sat_block_data_ref = process_context.indi_sat_block_data(sat_block_data);
        let saturation_node = sat_block_data_ref.get_saturation_individual_node();
        if saturation_node.is_none() {
            return (false, AssociatedConceptExpansionId::NONE);
        }

        if sat_block_data_ref.get_last_confirmed_concept_descriptior() == last_added_con_des {
            let flags = &process_context
                .sat_node(saturation_node)
                .indirect_status_flags;
            if !flags.has_flags_code(
                IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT
                    | IndividualSaturationProcessNodeStatusFlags::INDSATFLAGCLASHED,
                false,
            ) {
                return (true, AssociatedConceptExpansionId::NONE);
            }
        }

        let cache_data = process_context
            .sat_node(saturation_node)
            .get_cache_expansion_data();
        if cache_data.is_none() {
            return (false, AssociatedConceptExpansionId::NONE);
        }
        let cache_entry = Id::new(cache_data.raw);
        let det_expansion = cache_context
            .sat_expansion_cache_entry(cache_entry)
            .get_deterministic_concept_expansion();
        if det_expansion.is_some()
            && !cache_context
                .associated_concept_expansion(det_expansion)
                .requires_non_deterministic_expansion()
            && Self::test_node_matching_expansion(
                det_expansion,
                AssociatedConceptExpansionId::NONE,
                con_set,
                sat_block_data,
                calc_alg_context,
                cache_context,
            )
        {
            return (true, det_expansion);
        }

        for nondet_expansion in cache_context
            .sat_expansion_cache_entry(cache_entry)
            .get_nondeterministic_concept_expansion_linker()
        {
            if Self::test_node_matching_expansion(
                *nondet_expansion,
                det_expansion,
                con_set,
                sat_block_data,
                calc_alg_context,
                cache_context,
            ) {
                return (true, *nondet_expansion);
            }
        }

        (false, AssociatedConceptExpansionId::NONE)
    }

    /// Port of `testNodeMatchingExpansion`.
    fn test_node_matching_expansion(
        expansion: AssociatedConceptExpansionId,
        alternative_expansion: AssociatedConceptExpansionId,
        con_set: LabelSetId,
        sat_block_data: IndiSatBlockDataId,
        calc_alg_context: &CalculationAlgorithmContextBase,
        cache_context: &CacheContext,
    ) -> bool {
        if expansion.is_none() {
            return false;
        }
        let process_context = calc_alg_context.process_context();
        let con_set_ref = process_context.label_set(con_set);
        let expansion_ref = cache_context.associated_concept_expansion(expansion);
        if expansion_ref.get_concept_set_signature() != con_set_ref.get_concept_signature_value() {
            return false;
        }
        if expansion_ref.get_total_concept_count() != con_set_ref.get_concept_count() {
            return false;
        }

        let last_con_des = process_context
            .indi_sat_block_data(sat_block_data)
            .get_last_confirmed_concept_descriptior();
        let mut con_des_it = con_set_ref.get_adding_sorted_concept_description_linker();
        while con_des_it.is_some() && con_des_it != last_con_des {
            let con_des_ref = process_context.con_desc(con_des_it);
            let cache_value = Self::get_cache_value_for_concept(
                con_des_ref.get_concept(),
                con_des_ref.is_negated(),
                calc_alg_context,
            );
            if !cache_context
                .associated_concept_expansion(expansion)
                .has_concept_expansion_linker(cache_value)
                && (alternative_expansion.is_none()
                    || !cache_context
                        .associated_concept_expansion(alternative_expansion)
                        .has_concept_expansion_linker(cache_value))
            {
                return false;
            }
            con_des_it = con_des_ref.get_next_concept_descriptor();
        }

        let dependent_nominal_set = expansion_ref.dependent_nominal_set;
        if dependent_nominal_set.is_some() {
            let dependent_nominal_ids = cache_context
                .dependent_nominal_set(dependent_nominal_set)
                .nominal_set
                .clone();
            let indi_vec = calc_alg_context
                .processing_data_box()
                .individual_process_node_vector();
            let max_cached_id = calc_alg_context
                .base
                .max_completion_graph_cached_individual_node_id();
            for dependent_nominal_id in dependent_nominal_ids {
                let dependent_nominal_id = -dependent_nominal_id;
                let indi_node = indi_vec.get_data(dependent_nominal_id);
                let mut nominal_still_cached = indi_node.is_none();
                if indi_node.is_some() {
                    let indi_node_ref = process_context.node(indi_node);
                    if dependent_nominal_id <= max_cached_id
                        && indi_node_ref.has_processing_restriction_flags(
                            IndividualProcessNode::PRF_COMPLETIONGRAPHCACHED,
                        )
                    {
                        if !indi_node_ref.has_processing_restriction_flags(
                            IndividualProcessNode::PRF_COMPLETIONGRAPHCACHINGINVALID,
                        ) && !indi_node_ref.has_processing_restriction_flags(
                            IndividualProcessNode::PRF_COMPLETIONGRAPHCACHINGINVALIDATED,
                        ) {
                            nominal_still_cached = true;
                        }
                    } else if indi_node_ref.has_processing_restriction_flags(
                        IndividualProcessNode::PRF_SYNCHRONIZEDBACKEND,
                    ) {
                        nominal_still_cached = true;
                    }
                }
                if !nominal_still_cached {
                    return false;
                }
            }
        }

        true
    }

    /// Port slice of `testNodeCachingPossible`.
    pub fn test_node_caching_possible(
        &self,
        individual_process_node: NodeId,
        calc_alg_context: &CalculationAlgorithmContextBase,
        cache_context: &CacheContext,
    ) -> Option<SaturationNodeCachingPossibleData> {
        let process_context = calc_alg_context.process_context();
        let node = process_context.node(individual_process_node);
        let sat_block_data = node.individual_saturation_blocking_data(false);
        let con_set = node.use_reapply_con_label_set;
        if con_set.is_none() || sat_block_data.is_none() {
            return None;
        }

        let sat_block_data_ref = process_context.indi_sat_block_data(sat_block_data);
        let saturation_node = sat_block_data_ref.get_saturation_individual_node();
        if saturation_node.is_none() || !process_context.sat_node(saturation_node).is_completed() {
            return None;
        }

        let con_set_signature = process_context
            .label_set(con_set)
            .get_concept_signature_value();
        let mut data = SaturationNodeCachingPossibleData {
            only_if_completely_deterministic: false,
            only_all_nondeterministic: false,
            cache_entry: Id::NONE,
        };

        let cache_data = process_context
            .sat_node(saturation_node)
            .get_cache_expansion_data();
        if cache_data.is_some() {
            data.cache_entry = Id::new(cache_data.raw);
            let cache_entry = cache_context.sat_expansion_cache_entry(data.cache_entry);
            let det_expansion = cache_entry.get_deterministic_concept_expansion();
            if det_expansion.is_some()
                && !cache_context
                    .associated_concept_expansion(det_expansion)
                    .requires_non_deterministic_expansion()
            {
                return None;
            }
            if !cache_entry.are_more_nondeterministic_expansion_allowed()
                || det_expansion.is_some()
                    && cache_context
                        .associated_concept_expansion(det_expansion)
                        .get_concept_set_signature()
                        == con_set_signature
            {
                data.only_if_completely_deterministic = true;
            } else {
                for nondet_expansion in cache_entry.get_nondeterministic_concept_expansion_linker()
                {
                    if cache_context
                        .associated_concept_expansion(*nondet_expansion)
                        .get_concept_set_signature()
                        == con_set_signature
                    {
                        data.only_if_completely_deterministic = true;
                        break;
                    }
                }
            }
        }

        let successor_nominal_set = node.use_nominal_connection_set;
        if successor_nominal_set.is_some() {
            let nominal_ids = process_context
                .nominal_conn_set(successor_nominal_set)
                .iter_snapshot();
            let indi_vec = calc_alg_context
                .processing_data_box()
                .individual_process_node_vector();
            let max_cached_id = calc_alg_context
                .base
                .max_completion_graph_cached_individual_node_id();
            for nominal_node_id in nominal_ids {
                let indi_node = indi_vec.get_data(nominal_node_id);
                let mut nominal_still_cached = false;
                if indi_node.is_some() {
                    let indi_node_ref = process_context.node(indi_node);
                    if nominal_node_id <= max_cached_id
                        && indi_node_ref.has_processing_restriction_flags(
                            IndividualProcessNode::PRF_COMPLETIONGRAPHCACHED,
                        )
                    {
                        if !indi_node_ref.has_processing_restriction_flags(
                            IndividualProcessNode::PRF_COMPLETIONGRAPHCACHINGINVALID,
                        ) && !indi_node_ref.has_processing_restriction_flags(
                            IndividualProcessNode::PRF_COMPLETIONGRAPHCACHINGINVALIDATED,
                        ) {
                            nominal_still_cached = true;
                            if indi_node_ref.has_processing_restriction_flags(
                                IndividualProcessNode::PRF_COMPLETIONGRAPHCACHEDNODEEXTENDED,
                            ) {
                                data.only_all_nondeterministic = true;
                            }
                        }
                    } else if indi_node_ref.has_processing_restriction_flags(
                        IndividualProcessNode::PRF_SYNCHRONIZEDBACKEND,
                    ) {
                        nominal_still_cached = true;
                    }
                }
                if !nominal_still_cached {
                    return None;
                }
            }
        }

        Some(data)
    }

    /// Port slice of `tryNodeSatisfiableCaching`.
    pub fn try_node_satisfiable_caching(
        &mut self,
        individual_process_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
        cache_context: &mut CacheContext,
    ) -> bool {
        let Some(cache_data) = self.test_node_caching_possible(
            individual_process_node,
            calc_alg_context,
            cache_context,
        ) else {
            return false;
        };

        let process_context = calc_alg_context.process_context();
        let node = process_context.node(individual_process_node);
        let sat_block_data = node.individual_saturation_blocking_data(false);
        let con_set = node.use_reapply_con_label_set;
        if sat_block_data.is_none() || con_set.is_none() {
            return false;
        }

        let sat_block_data_ref = process_context.indi_sat_block_data(sat_block_data);
        let last_con_des = sat_block_data_ref.get_last_confirmed_concept_descriptior();
        let sat_indi_node = sat_block_data_ref.get_saturation_individual_node();
        if sat_indi_node.is_none() {
            return false;
        }

        let saturation_concept = Self::saturation_concept_for_node(sat_indi_node, calc_alg_context);
        if saturation_concept.is_none() {
            return false;
        }

        let con_set_ref = process_context.label_set(con_set);
        let con_set_signature = con_set_ref.get_concept_signature_value();
        let total_concept_count = con_set_ref.get_concept_count();
        let con_des = con_set_ref.get_adding_sorted_concept_description_linker();

        let mut sat_con_des = ConDescId::NONE;
        let mut sat_con_dep_track_point = TrackPointId::NONE;
        let sat_con_tag = calc_alg_context
            .ontology_arenas()
            .concept(saturation_concept)
            .get_concept_tag();
        if !con_set_ref.get_concept_descriptor_and_reapply_queue_by_tag(
            sat_con_tag,
            &mut sat_con_des,
            &mut sat_con_dep_track_point,
        ) {
            return false;
        }
        sat_con_dep_track_point = process_context
            .con_desc(sat_con_des)
            .get_dependency_track_point();

        let mut last_possibly_nondeterministic_con_des = ConDescId::NONE;
        let cache_trace_tags = super::sat_cache_trace_tags();
        let mut con_des_it = con_des;
        while con_des_it.is_some() && con_des_it != last_con_des {
            let dep_track_point = process_context
                .con_desc(con_des_it)
                .get_dependency_track_point();
            let deterministically_depending = !cache_data.only_all_nondeterministic
                && Self::is_deterministically_depending_on_saturation_concept(
                    individual_process_node,
                    dep_track_point,
                    sat_con_dep_track_point,
                    calc_alg_context,
                );
            let possibly_nondeterministic =
                cache_data.only_all_nondeterministic || !deterministically_depending;
            let descriptor = process_context.con_desc(con_des_it);
            let descriptor_tag = calc_alg_context
                .ontology_arenas()
                .concept(descriptor.get_concept())
                .get_concept_tag();
            if cache_trace_tags.contains(&descriptor_tag) {
                let dep_node = if dep_track_point.is_some() {
                    process_context
                        .track_point(dep_track_point)
                        .dependency_node()
                } else {
                    Id::NONE
                };
                let dep_branch = if dep_track_point.is_some() {
                    process_context
                        .track_point(dep_track_point)
                        .get_branching_tag()
                } else {
                    -1
                };
                let sat_branch = if sat_con_dep_track_point.is_some() {
                    process_context
                        .track_point(sat_con_dep_track_point)
                        .get_branching_tag()
                } else {
                    -1
                };
                let (dep_kind, dep_indi) = if dep_node.is_some() {
                    let dependency = process_context.dep_node(dep_node);
                    (
                        dependency.kind() as Cint64,
                        dependency.individual_node().raw,
                    )
                } else {
                    (-1, -1)
                };
                eprintln!(
                    "SAT-CACHE-CLASSIFY concept-tag={} node={} sat-node={} sat-tag={} dep={} dep-kind={} dep-indi={} dep-branch={} sat-branch={} anc-depth={} only-all-nondet={} deterministic={} possibly-nondet={}",
                    descriptor_tag,
                    process_context
                        .node(individual_process_node)
                        .individual_node_id(),
                    sat_indi_node.raw,
                    sat_con_tag,
                    dep_track_point.raw,
                    dep_kind,
                    dep_indi,
                    dep_branch,
                    sat_branch,
                    process_context
                        .node(individual_process_node)
                        .individual_ancestor_depth(),
                    cache_data.only_all_nondeterministic,
                    deterministically_depending,
                    possibly_nondeterministic,
                );
            }
            if possibly_nondeterministic {
                last_possibly_nondeterministic_con_des = con_des_it;
            }
            con_des_it = process_context
                .con_desc(con_des_it)
                .get_next_concept_descriptor();
        }

        if cache_data.only_if_completely_deterministic
            && last_possibly_nondeterministic_con_des.is_some()
        {
            return false;
        }

        self.prepare_cache_messages(calc_alg_context);
        let has_tight_at_most_restriction =
            Self::has_tight_at_most_restriction(individual_process_node, con_des, calc_alg_context);
        let nom_dep_set = Self::create_dependent_nominal_set_for_node(
            individual_process_node,
            calc_alg_context,
            cache_context,
        );

        let mut nondet_exp_write_data = None;
        if last_possibly_nondeterministic_con_des.is_some() {
            let con_des_stop = calc_alg_context
                .process_context()
                .con_desc(last_possibly_nondeterministic_con_des)
                .get_next_concept_descriptor();
            let non_det_concept_linker = self.create_concept_linkers_for_descriptor_range(
                con_des,
                con_des_stop,
                AssociatedConceptExpansionId::NONE,
                calc_alg_context,
                cache_context,
            );
            let mut write_data = SaturationNodeAssociatedExpansionCacheExpansionWriteData::new();
            write_data.init_expansion_write_data(sat_indi_node, non_det_concept_linker);
            write_data
                .set_deterministic_expansion(false)
                .set_tight_at_most_restriction(has_tight_at_most_restriction)
                .set_concept_set_signature(con_set_signature)
                .set_total_concept_count(total_concept_count)
                .set_dependent_nominal_set(nom_dep_set);
            nondet_exp_write_data = Some(write_data);
        }

        let mut det_exp_write_data = None;
        let nondet_next = if last_possibly_nondeterministic_con_des.is_some() {
            calc_alg_context
                .process_context()
                .con_desc(last_possibly_nondeterministic_con_des)
                .get_next_concept_descriptor()
        } else {
            ConDescId::NONE
        };
        if last_possibly_nondeterministic_con_des.is_none() || nondet_next != last_con_des {
            let det_con_exp = if cache_data.cache_entry.is_some() {
                cache_context
                    .sat_expansion_cache_entry(cache_data.cache_entry)
                    .get_deterministic_concept_expansion()
            } else {
                AssociatedConceptExpansionId::NONE
            };

            let con_des_start = if nondet_next.is_some() {
                nondet_next
            } else {
                con_des
            };
            let det_concept_linker = self.create_concept_linkers_for_descriptor_range(
                con_des_start,
                last_con_des,
                det_con_exp,
                calc_alg_context,
                cache_context,
            );

            let requires_old_nondet = det_con_exp.is_some()
                && cache_context
                    .associated_concept_expansion(det_con_exp)
                    .requires_non_deterministic_expansion();
            if !det_concept_linker.is_empty()
                || det_con_exp.is_none()
                || requires_old_nondet && det_concept_linker.is_empty()
            {
                let mut write_data =
                    SaturationNodeAssociatedExpansionCacheExpansionWriteData::new();
                write_data.init_expansion_write_data(sat_indi_node, det_concept_linker);
                write_data.set_deterministic_expansion(true);
                if last_possibly_nondeterministic_con_des.is_none() {
                    write_data
                        .set_requires_nondeterministic_expansion(false)
                        .set_tight_at_most_restriction(has_tight_at_most_restriction)
                        .set_concept_set_signature(con_set_signature)
                        .set_total_concept_count(total_concept_count)
                        .set_dependent_nominal_set(nom_dep_set);
                }
                det_exp_write_data = Some(write_data);
            }
        }

        let mut wrote_cache_data = false;
        if let Some(write_data) = nondet_exp_write_data {
            wrote_cache_data = true;
            self.add_expansion_cache_message(write_data, calc_alg_context);
        }
        if let Some(write_data) = det_exp_write_data {
            wrote_cache_data = true;
            self.add_expansion_cache_message(write_data, calc_alg_context);
        }
        wrote_cache_data
    }

    fn saturation_concept_for_node(
        sat_indi_node: SatNodeId,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> ConceptId {
        let sat_ref = calc_alg_context
            .process_context()
            .sat_node(sat_indi_node)
            .get_saturation_concept_reference_linking();
        if sat_ref.is_none() {
            return ConceptId::NONE;
        }
        calc_alg_context
            .process_context()
            .extended_con_ref_linking_data(sat_ref)
            .get_saturation_concept()
    }

    fn create_dependent_nominal_set_for_node(
        individual_process_node: NodeId,
        calc_alg_context: &CalculationAlgorithmContextBase,
        cache_context: &mut CacheContext,
    ) -> DependentNominalSetId {
        let nominal_ids = calc_alg_context
            .process_context()
            .node_successor_connected_nominals(individual_process_node);
        if nominal_ids.is_empty() {
            return Id::NONE;
        }

        let mut dep_set = SaturationNodeAssociatedDependentNominalSet::new();
        dep_set.init_dependent_nominal_set();
        for nominal_id in nominal_ids {
            dep_set.insert(-nominal_id);
        }
        cache_context.alloc_dependent_nominal_set(dep_set)
    }

    fn is_deterministically_depending_on_saturation_concept(
        individual_process_node: NodeId,
        dep_track_point: TrackPointId,
        sat_con_dep_track_point: TrackPointId,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> bool {
        if dep_track_point.is_none() || sat_con_dep_track_point.is_none() {
            return false;
        }
        let process_context = calc_alg_context.process_context();
        if process_context
            .track_point(dep_track_point)
            .get_branching_tag()
            != process_context
                .track_point(sat_con_dep_track_point)
                .get_branching_tag()
        {
            return false;
        }

        let ancestor_depth = process_context
            .node(individual_process_node)
            .individual_ancestor_depth();
        let dep_node_id = process_context
            .track_point(dep_track_point)
            .dependency_node();
        if dep_node_id.is_none() {
            return false;
        }
        let dep_node = process_context.dep_node(dep_node_id);
        if ancestor_depth <= 0 {
            if dep_node.is_independent_base_dependency_type() {
                return false;
            }
        } else {
            let app_indi_node = dep_node.individual_node();
            if app_indi_node.is_some() {
                if process_context
                    .node(app_indi_node)
                    .individual_ancestor_depth()
                    < ancestor_depth
                {
                    return false;
                }
            } else if dep_node.kind() == DepKind::MergedConcept {
                return false;
            }
        }
        true
    }

    fn has_tight_at_most_restriction(
        individual_process_node: NodeId,
        con_des: ConDescId,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> bool {
        let process_context = calc_alg_context.process_context();
        let mut con_des_it = con_des;
        while con_des_it.is_some() {
            let descriptor = process_context.con_desc(con_des_it);
            let concept = calc_alg_context
                .ontology_arenas()
                .concept(descriptor.get_concept());
            let negation = descriptor.is_negated();
            let con_code = concept.get_operator_code();
            if (negation && con_code == CCATLEAST) || (!negation && con_code == CCATMOST) {
                let role = concept.get_role();
                let parameter = concept.get_parameter();
                let cardinality = parameter + if negation { 1 } else { 0 };
                if Self::role_successor_count(individual_process_node, role, calc_alg_context)
                    >= cardinality
                {
                    return true;
                }
            }
            con_des_it = descriptor.get_next_concept_descriptor();
        }
        false
    }

    fn role_successor_count(
        individual_process_node: NodeId,
        role: RoleId,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> Cint64 {
        if role.is_none() {
            return 0;
        }
        let process_context = calc_alg_context.process_context();
        let role_succ_hash = process_context
            .node(individual_process_node)
            .use_reapply_role_succ_hash;
        if role_succ_hash.is_none() {
            return 0;
        }
        process_context
            .role_succ_hash(role_succ_hash)
            .get_role_successor_count(role)
    }

    fn create_concept_linkers_for_descriptor_range(
        &self,
        start: ConDescId,
        stop: ConDescId,
        previous_deterministic_expansion: AssociatedConceptExpansionId,
        calc_alg_context: &CalculationAlgorithmContextBase,
        cache_context: &mut CacheContext,
    ) -> Vec<AssociatedConceptLinkerId> {
        let mut linkers = Vec::new();
        let mut con_des_it = start;
        while con_des_it.is_some() && con_des_it != stop {
            let descriptor = calc_alg_context.process_context().con_desc(con_des_it);
            let cache_value = Self::get_cache_value_for_concept(
                descriptor.get_concept(),
                descriptor.is_negated(),
                calc_alg_context,
            );
            if previous_deterministic_expansion.is_none()
                || !cache_context
                    .associated_concept_expansion(previous_deterministic_expansion)
                    .has_concept_expansion_linker(cache_value)
            {
                let mut linker = SaturationNodeAssociatedConceptLinker::new();
                linker.init_concept_linker(cache_value);
                let linker = cache_context.alloc_associated_concept_linker(linker);
                linkers.insert(0, linker);
            }
            con_des_it = descriptor.get_next_concept_descriptor();
        }
        linkers
    }

    fn get_cache_value_for_concept(
        concept: ConceptId,
        negation: bool,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> CacheValue {
        let concept_tag = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_concept_tag();
        let cache_value_identifier = if negation {
            CacheValueIdentifier::CacheValTagAndNegatedConcept
        } else {
            CacheValueIdentifier::CacheValTagAndConcept
        };
        CacheValue::new_value(concept_tag, concept.raw, cache_value_identifier)
    }

    /// Port slice of `prepareCacheMessages`.
    pub fn prepare_cache_messages(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let _ = calc_alg_context;
        true
    }

    /// Port of `addCacheMessages(CSaturationNodeAssociatedExpansionCacheWriteData*)`.
    pub fn add_cache_messages(
        &mut self,
        write_data: SaturationNodeAssociatedExpansionCacheWriteDataRecord,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let _ = calc_alg_context;
        self.write_data.insert(0, write_data);
        true
    }

    /// Typed convenience wrapper for `SNAECWT_UNSAT` producers.
    pub fn add_unsat_cache_message(
        &mut self,
        write_data: SaturationNodeAssociatedExpansionCacheUnsatisfiabilityWriteData,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        self.add_cache_messages(
            SaturationNodeAssociatedExpansionCacheWriteDataRecord::Unsat(write_data),
            calc_alg_context,
        )
    }

    /// Typed convenience wrapper for `SNAECWT_EXPAND` producers.
    pub fn add_expansion_cache_message(
        &mut self,
        write_data: SaturationNodeAssociatedExpansionCacheExpansionWriteData,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        self.add_cache_messages(
            SaturationNodeAssociatedExpansionCacheWriteDataRecord::Expand(write_data),
            calc_alg_context,
        )
    }

    /// Number of pending write-data records in the staged `mWriteData` chain.
    pub fn pending_cache_message_count(&self) -> usize {
        self.write_data.len()
    }

    /// Port helper mirroring the commit-time reversal of the intrusive C++ chain.
    fn take_commit_write_data(
        &mut self,
    ) -> Vec<SaturationNodeAssociatedExpansionCacheWriteDataRecord> {
        let mut commit_write_data = std::mem::take(&mut self.write_data);
        commit_write_data.reverse();
        commit_write_data
    }

    /// Queue an already-constructed expansion write-data record.
    ///
    /// This is the producer-side handoff used by the staged Rust port while the
    /// full `tryNodeSatisfiableCaching` concept-label walk is still being ported.
    pub fn queue_expansion_write_data(
        &mut self,
        write_data: SaturationNodeAssociatedExpansionCacheExpansionWriteData,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        self.prepare_cache_messages(calc_alg_context);
        self.add_expansion_cache_message(write_data, calc_alg_context);
        true
    }

    /// Port slice of `commitCacheMessages`.
    pub fn commit_cache_messages(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
        cache_context: &mut CacheContext,
    ) -> bool {
        if self.write_data.is_empty() {
            return false;
        }

        if self.sat_cache_writer.cache.is_none() {
            return false;
        } else {
            let writes = self.take_commit_write_data();
            cache_context.write_sat_expansion_cache_data(
                self.sat_cache_writer.cache,
                writes,
                calc_alg_context.process_context_mut(),
                INVALID,
            )
        }
    }
}
