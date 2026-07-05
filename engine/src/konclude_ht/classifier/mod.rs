//! `classifier` — narrow ports from Konclude `Source/Reasoner/Classifier/`.
//!
//! This module is introduced at the individual-dependence adapter call site. The
//! full classifier threads/items contain taxonomy scheduling and many result
//! queues; this wave ports only the collector/marker fields and the job-adapter
//! setup branch they use.

#![allow(dead_code)]

use std::collections::{BTreeMap, HashMap, HashSet};

use super::completion::context::CalculationAlgorithmContext;
use super::model::concept::Concept;
use super::model::concept_process::{ConceptProcessData, ConceptSaturationReferenceLinkingData};
use super::model::individual::Individual;
use super::model::ontology::OntologyArenas;
use super::model::op::{CCALL, CCAND, CCEQ, CCEQCAND, CCMARKER, CCTOP, CCVALUE};
use super::model::substrate::{Arena, Cint64, Id, INVALID};
use super::model::{ConceptId, IndividualId, RoleId};
use super::task::adapters::{
    IndividualDependenceTrackingCollectorId, IndividualDependenceTrackingMarker,
    IndividualDependenceTrackingMarkerId, SatisfiableTaskClassificationMessageAdapter,
    SatisfiableTaskClassificationRoleMarkedMessageAdapter,
    SatisfiableTaskIndividualDependenceTrackingAdapter, EFEXTRACTALL,
    EFEXTRACTOTHERNODESMULTIPLEDEPENDENCY, EFEXTRACTPOSSIBLESUBSUMERSOTHERNODES,
    EFEXTRACTPOSSIBLESUBSUMERSROOTNODE, EFEXTRACTSUBSUMERSOTHERNODES,
};
use super::task::calculation_job::SatisfiableCalculationJob;

/// Port of the individual-dependence collector field on
/// `COptimizedSubClassOntologyClassificationItem`.
#[derive(Debug, Clone)]
pub struct OptimizedSubClassOntologyClassificationItem {
    /// `CIndividualDependenceTrackingCollector* mIndiDepTrackCollector`.
    individual_dependence_tracking_collector: IndividualDependenceTrackingCollectorId,
}

/// Port of the individual-dependence collector field on
/// `COptimizedKPSetClassOntologyClassificationItem`.
#[derive(Debug, Clone)]
pub struct OptimizedKPSetClassOntologyClassificationItem {
    /// `CIndividualDependenceTrackingCollector* mIndiDepTrackCollector`.
    individual_dependence_tracking_collector: IndividualDependenceTrackingCollectorId,
    concept_sat_item_hash: HashMap<ConceptId, OptimizedKPSetClassTestingItemId>,
    sat_test_item_container: Vec<OptimizedKPSetClassTestingItem>,
    top_sat_test_item: OptimizedKPSetClassTestingItemId,
    bottom_sat_test_item: OptimizedKPSetClassTestingItemId,
    next_item_list: Vec<OptimizedKPSetClassTestingItemId>,
    next_cand_item_set: HashSet<OptimizedKPSetClassTestingItemId>,
    remaining_cand_item_set: HashSet<OptimizedKPSetClassTestingItemId>,
    next_poss_subsum_item_list: Vec<OptimizedKPSetClassTestingItemId>,
    current_poss_subsum_item_set: HashSet<OptimizedKPSetClassTestingItemId>,
    remaining_sat_tests: Cint64,
    running_sat_tests: Cint64,
    satisfiable_item_list: Vec<OptimizedKPSetClassTestingItemId>,
    concept_ref_link_data: HashMap<ConceptId, Cint64>,
    satisfiable_testing_phase_finished: bool,
    possible_subsumption_testing_phase_finished: bool,
    remaining_possible_subsumption_tests: Cint64,
    running_possible_subsumption_tests: Cint64,
    rem_poss_class_testing_set: HashSet<OptimizedKPSetClassTestingItemId>,
    equivalent_concept_non_candidate_set: HashSet<ConceptId>,
    equivalent_concept_candidate_hash: HashMap<ConceptId, ConceptId>,
    calculated_possible_subsum_count: Cint64,
    calculated_true_possible_subsum_count: Cint64,
    calculated_false_possible_subsum_count: Cint64,
    possible_subsum_count: Cint64,
    true_possible_subsum_count: Cint64,
    false_possible_subsum_count: Cint64,
    memory_pools: Vec<Cint64>,
    current_calculating_count: Cint64,
    taxonomy_construction_failed: bool,
    reused_statistics_collections: Vec<Cint64>,
    work_item_hash: HashMap<Cint64, ClassClassificationComputationItem>,
}

/// Port of the individual-dependence collector field on
/// `COptimizedKPSetRoleOntologyClassificationItem`.
#[derive(Debug, Clone)]
pub struct OptimizedKPSetRoleOntologyClassificationItem {
    /// `CIndividualDependenceTrackingCollector* mIndiDepTrackCollector`.
    individual_dependence_tracking_collector: IndividualDependenceTrackingCollectorId,
    role_sat_item_hash: HashMap<RoleId, OptimizedKPSetRoleTestingItemId>,
    sat_test_item_container: Vec<OptimizedKPSetRoleTestingItem>,
    top_sat_test_item: OptimizedKPSetRoleTestingItemId,
    bottom_sat_test_item: OptimizedKPSetRoleTestingItemId,
    next_item_list: Vec<OptimizedKPSetRoleTestingItemId>,
    next_cand_item_set: HashSet<OptimizedKPSetRoleTestingItemId>,
    remaining_cand_item_set: HashSet<OptimizedKPSetRoleTestingItemId>,
    next_poss_subsum_item_list: Vec<OptimizedKPSetRoleTestingItemId>,
    current_poss_subsum_item_set: HashSet<OptimizedKPSetRoleTestingItemId>,
    remaining_sat_tests: Cint64,
    running_sat_tests: Cint64,
    satisfiable_item_list: Vec<OptimizedKPSetRoleTestingItemId>,
    concept_ref_link_data: HashMap<ConceptId, Cint64>,
    satisfiable_testing_phase_finished: bool,
    possible_subsumption_testing_phase_finished: bool,
    remaining_possible_subsumption_tests: Cint64,
    running_possible_subsumption_tests: Cint64,
    rem_poss_class_testing_set: HashSet<OptimizedKPSetRoleTestingItemId>,
    calculated_possible_subsum_count: Cint64,
    calculated_true_possible_subsum_count: Cint64,
    calculated_false_possible_subsum_count: Cint64,
    possible_subsum_count: Cint64,
    true_possible_subsum_count: Cint64,
    false_possible_subsum_count: Cint64,
    data_roles_classification: bool,
    temporary_role_classification_ontology: Cint64,
    temporary_top_concept: ConceptId,
    temporary_top_data_range_concept: ConceptId,
    marker_concept_instances_item_hash: HashMap<ConceptId, OptimizedKPSetRoleTestingItemId>,
    temporary_all_propagation_concept: ConceptId,
    temporary_propagation_individual: IndividualId,
    temporary_marker_individual: IndividualId,
    current_calculating_count: Cint64,
    hierarchy_construction_failed: bool,
    reused_statistics_collections: Vec<Cint64>,
    work_item_hash: HashMap<Cint64, PropertyClassificationComputationItem>,
}

impl Default for OptimizedKPSetRoleOntologyClassificationItem {
    fn default() -> Self {
        Self::new()
    }
}

impl OptimizedKPSetRoleOntologyClassificationItem {
    /// Constructor-side default: no collector until configuration enables
    /// individual-dependence tracking.
    pub fn new() -> Self {
        Self {
            individual_dependence_tracking_collector: IndividualDependenceTrackingCollectorId::NONE,
            role_sat_item_hash: HashMap::new(),
            sat_test_item_container: Vec::new(),
            top_sat_test_item: OptimizedKPSetRoleTestingItemId::NONE,
            bottom_sat_test_item: OptimizedKPSetRoleTestingItemId::NONE,
            next_item_list: Vec::new(),
            next_cand_item_set: HashSet::new(),
            remaining_cand_item_set: HashSet::new(),
            next_poss_subsum_item_list: Vec::new(),
            current_poss_subsum_item_set: HashSet::new(),
            remaining_sat_tests: 0,
            running_sat_tests: 0,
            satisfiable_item_list: Vec::new(),
            concept_ref_link_data: HashMap::new(),
            satisfiable_testing_phase_finished: false,
            possible_subsumption_testing_phase_finished: false,
            remaining_possible_subsumption_tests: 0,
            running_possible_subsumption_tests: 0,
            rem_poss_class_testing_set: HashSet::new(),
            calculated_possible_subsum_count: 0,
            calculated_true_possible_subsum_count: 0,
            calculated_false_possible_subsum_count: 0,
            possible_subsum_count: 0,
            true_possible_subsum_count: 0,
            false_possible_subsum_count: 0,
            data_roles_classification: false,
            temporary_role_classification_ontology: INVALID,
            temporary_top_concept: ConceptId::NONE,
            temporary_top_data_range_concept: ConceptId::NONE,
            marker_concept_instances_item_hash: HashMap::new(),
            temporary_all_propagation_concept: ConceptId::NONE,
            temporary_propagation_individual: IndividualId::NONE,
            temporary_marker_individual: IndividualId::NONE,
            current_calculating_count: 0,
            hierarchy_construction_failed: false,
            reused_statistics_collections: Vec::new(),
            work_item_hash: HashMap::new(),
        }
    }

    pub fn get_role_satisfiable_test_item_hash(
        &self,
    ) -> &HashMap<RoleId, OptimizedKPSetRoleTestingItemId> {
        &self.role_sat_item_hash
    }

    pub fn get_role_satisfiable_test_item_list(&self) -> &[OptimizedKPSetRoleTestingItem] {
        &self.sat_test_item_container
    }

    pub fn get_role_satisfiable_test_item_mut(
        &mut self,
        item: OptimizedKPSetRoleTestingItemId,
    ) -> Option<&mut OptimizedKPSetRoleTestingItem> {
        if item.is_some() && item.index() < self.sat_test_item_container.len() {
            Some(&mut self.sat_test_item_container[item.index()])
        } else {
            None
        }
    }

    pub fn get_top_role_satisfiable_test_item(&self) -> OptimizedKPSetRoleTestingItemId {
        self.top_sat_test_item
    }

    pub fn get_bottom_role_satisfiable_test_item(&self) -> OptimizedKPSetRoleTestingItemId {
        self.bottom_sat_test_item
    }

    pub fn set_top_role_satisfiable_test_item(
        &mut self,
        item: OptimizedKPSetRoleTestingItemId,
    ) -> &mut Self {
        self.top_sat_test_item = item;
        self
    }

    pub fn set_bottom_role_satisfiable_test_item(
        &mut self,
        item: OptimizedKPSetRoleTestingItemId,
    ) -> &mut Self {
        self.bottom_sat_test_item = item;
        self
    }

    pub fn get_next_satisfiable_testing_item_list(&self) -> &[OptimizedKPSetRoleTestingItemId] {
        &self.next_item_list
    }

    pub fn get_next_satisfiable_testing_item_list_mut(
        &mut self,
    ) -> &mut Vec<OptimizedKPSetRoleTestingItemId> {
        &mut self.next_item_list
    }

    pub fn get_next_candidate_satisfiable_testing_item_set(
        &self,
    ) -> &HashSet<OptimizedKPSetRoleTestingItemId> {
        &self.next_cand_item_set
    }

    pub fn get_next_candidate_satisfiable_testing_item_set_mut(
        &mut self,
    ) -> &mut HashSet<OptimizedKPSetRoleTestingItemId> {
        &mut self.next_cand_item_set
    }

    pub fn get_remaining_candidate_satisfiable_testing_item_set(
        &self,
    ) -> &HashSet<OptimizedKPSetRoleTestingItemId> {
        &self.remaining_cand_item_set
    }

    pub fn get_remaining_candidate_satisfiable_testing_item_set_mut(
        &mut self,
    ) -> &mut HashSet<OptimizedKPSetRoleTestingItemId> {
        &mut self.remaining_cand_item_set
    }

    pub fn get_next_possible_subsumption_testing_item_list(
        &self,
    ) -> &[OptimizedKPSetRoleTestingItemId] {
        &self.next_poss_subsum_item_list
    }

    pub fn get_next_possible_subsumption_testing_item_list_mut(
        &mut self,
    ) -> &mut Vec<OptimizedKPSetRoleTestingItemId> {
        &mut self.next_poss_subsum_item_list
    }

    pub fn get_current_possible_subsumption_testing_item_set(
        &self,
    ) -> &HashSet<OptimizedKPSetRoleTestingItemId> {
        &self.current_poss_subsum_item_set
    }

    pub fn get_current_possible_subsumption_testing_item_set_mut(
        &mut self,
    ) -> &mut HashSet<OptimizedKPSetRoleTestingItemId> {
        &mut self.current_poss_subsum_item_set
    }

    pub fn init_top_bottom_satisfiable_testing_items(
        &mut self,
        top_item: OptimizedKPSetRoleTestingItemId,
        bottom_item: OptimizedKPSetRoleTestingItemId,
    ) -> &mut Self {
        self.top_sat_test_item = top_item;
        self.bottom_sat_test_item = bottom_item;
        self
    }

    pub fn get_role_satisfiable_test_item(
        &mut self,
        sat_test_role: RoleId,
        create: bool,
    ) -> OptimizedKPSetRoleTestingItemId {
        if let Some(item) = self.role_sat_item_hash.get(&sat_test_role) {
            return *item;
        }
        if create {
            let item_id =
                OptimizedKPSetRoleTestingItemId::new(self.sat_test_item_container.len() as Cint64);
            let mut item = OptimizedKPSetRoleTestingItem::new();
            item.init_satisfiable_testing_item(sat_test_role);
            self.sat_test_item_container.push(item);
            self.role_sat_item_hash.insert(sat_test_role, item_id);
            item_id
        } else {
            OptimizedKPSetRoleTestingItemId::NONE
        }
    }

    pub fn has_all_satisfiable_tests_completed(&self) -> bool {
        self.remaining_sat_tests <= 0 && self.running_sat_tests <= 0
    }

    pub fn has_remaining_satisfiable_tests(&self) -> bool {
        self.remaining_sat_tests > 0
    }

    pub fn get_remaining_satisfiable_tests_count(&self) -> Cint64 {
        self.remaining_sat_tests
    }

    pub fn get_running_satisfiable_tests_count(&self) -> Cint64 {
        self.running_sat_tests
    }

    pub fn inc_remaining_satisfiable_tests_count(&mut self, inc_count: Cint64) -> &mut Self {
        self.remaining_sat_tests += inc_count;
        self
    }

    pub fn inc_running_satisfiable_tests_count(&mut self, inc_count: Cint64) -> &mut Self {
        self.running_sat_tests += inc_count;
        self
    }

    pub fn dec_remaining_satisfiable_tests_count(&mut self, dec_count: Cint64) -> &mut Self {
        self.remaining_sat_tests -= dec_count;
        self
    }

    pub fn dec_running_satisfiable_tests_count(&mut self, dec_count: Cint64) -> &mut Self {
        self.running_sat_tests -= dec_count;
        self
    }

    pub fn get_satisfiable_role_item_list(&self) -> &[OptimizedKPSetRoleTestingItemId] {
        &self.satisfiable_item_list
    }

    pub fn add_satisfiable_role_item(
        &mut self,
        item: OptimizedKPSetRoleTestingItemId,
    ) -> &mut Self {
        self.satisfiable_item_list.push(item);
        self
    }

    pub fn get_concept_reference_linking_data_hash(&self) -> &HashMap<ConceptId, Cint64> {
        &self.concept_ref_link_data
    }

    pub fn get_concept_reference_linking_data_hash_mut(
        &mut self,
    ) -> &mut HashMap<ConceptId, Cint64> {
        &mut self.concept_ref_link_data
    }

    pub fn has_satisfiable_testing_phase_finished(&self) -> bool {
        self.satisfiable_testing_phase_finished
    }

    pub fn has_possible_subsumption_testing_phase_finished(&self) -> bool {
        self.possible_subsumption_testing_phase_finished
    }

    pub fn set_satisfiable_testing_phase_finished(&mut self, finished: bool) -> &mut Self {
        self.satisfiable_testing_phase_finished = finished;
        self
    }

    pub fn set_possible_subsumption_testing_phase_finished(&mut self, finished: bool) -> &mut Self {
        self.possible_subsumption_testing_phase_finished = finished;
        self
    }

    pub fn get_remaining_possible_subsumption_tests_count(&self) -> Cint64 {
        self.remaining_possible_subsumption_tests
    }

    pub fn has_remaining_possible_subsumption_tests(&self) -> bool {
        self.remaining_possible_subsumption_tests > 0
    }

    pub fn inc_remaining_possible_subsumption_tests_count(
        &mut self,
        inc_count: Cint64,
    ) -> &mut Self {
        self.remaining_possible_subsumption_tests += inc_count;
        self
    }

    pub fn dec_remaining_possible_subsumption_tests_count(
        &mut self,
        dec_count: Cint64,
    ) -> &mut Self {
        self.remaining_possible_subsumption_tests -= dec_count;
        self
    }

    pub fn set_remaining_possible_subsumption_tests_count(
        &mut self,
        test_count: Cint64,
    ) -> &mut Self {
        self.remaining_possible_subsumption_tests = test_count;
        self
    }

    pub fn get_remaining_possible_subsumption_testing_set(
        &self,
    ) -> &HashSet<OptimizedKPSetRoleTestingItemId> {
        &self.rem_poss_class_testing_set
    }

    pub fn get_remaining_possible_subsumption_testing_set_mut(
        &mut self,
    ) -> &mut HashSet<OptimizedKPSetRoleTestingItemId> {
        &mut self.rem_poss_class_testing_set
    }

    pub fn get_remaining_possible_subsumption_testing_count(&self) -> Cint64 {
        self.rem_poss_class_testing_set.len() as Cint64
    }

    pub fn inc_running_possible_subsumption_tests_count(&mut self, inc_count: Cint64) -> &mut Self {
        self.running_possible_subsumption_tests += inc_count;
        self
    }

    pub fn dec_running_possible_subsumption_tests_count(&mut self, dec_count: Cint64) -> &mut Self {
        self.running_possible_subsumption_tests -= dec_count;
        self
    }

    pub fn get_running_possible_subsumption_tests_count(&self) -> Cint64 {
        self.running_possible_subsumption_tests
    }

    pub fn get_calculated_possible_subsumer_count(&self) -> Cint64 {
        self.calculated_possible_subsum_count
    }

    pub fn get_calculated_true_possible_subsumer_count(&self) -> Cint64 {
        self.calculated_true_possible_subsum_count
    }

    pub fn get_calculated_false_possible_subsumer_count(&self) -> Cint64 {
        self.calculated_false_possible_subsum_count
    }

    pub fn set_calculated_possible_subsumer_count(&mut self, subsum_count: Cint64) -> &mut Self {
        self.calculated_possible_subsum_count = subsum_count;
        self
    }

    pub fn set_calculated_true_possible_subsumer_count(
        &mut self,
        subsum_count: Cint64,
    ) -> &mut Self {
        self.calculated_true_possible_subsum_count = subsum_count;
        self
    }

    pub fn set_calculated_false_possible_subsumer_count(
        &mut self,
        subsum_count: Cint64,
    ) -> &mut Self {
        self.calculated_false_possible_subsum_count = subsum_count;
        self
    }

    pub fn inc_calculated_possible_subsumer_count(
        &mut self,
        inc_subsum_count: Cint64,
    ) -> &mut Self {
        self.calculated_possible_subsum_count += inc_subsum_count;
        self
    }

    pub fn inc_calculated_true_possible_subsumer_count(
        &mut self,
        inc_subsum_count: Cint64,
    ) -> &mut Self {
        self.calculated_true_possible_subsum_count += inc_subsum_count;
        self
    }

    pub fn inc_calculated_false_possible_subsumer_count(
        &mut self,
        inc_subsum_count: Cint64,
    ) -> &mut Self {
        self.calculated_false_possible_subsum_count += inc_subsum_count;
        self
    }

    pub fn get_possible_subsumer_count(&self) -> Cint64 {
        self.possible_subsum_count
    }

    pub fn get_true_possible_subsumer_count(&self) -> Cint64 {
        self.true_possible_subsum_count
    }

    pub fn get_false_possible_subsumer_count(&self) -> Cint64 {
        self.false_possible_subsum_count
    }

    pub fn set_possible_subsumer_count(&mut self, subsum_count: Cint64) -> &mut Self {
        self.possible_subsum_count = subsum_count;
        self
    }

    pub fn set_true_possible_subsumer_count(&mut self, subsum_count: Cint64) -> &mut Self {
        self.true_possible_subsum_count = subsum_count;
        self
    }

    pub fn set_false_possible_subsumer_count(&mut self, subsum_count: Cint64) -> &mut Self {
        self.false_possible_subsum_count = subsum_count;
        self
    }

    pub fn inc_possible_subsumer_count(&mut self, inc_subsum_count: Cint64) -> &mut Self {
        self.possible_subsum_count += inc_subsum_count;
        self
    }

    pub fn inc_true_possible_subsumer_count(&mut self, inc_subsum_count: Cint64) -> &mut Self {
        self.true_possible_subsum_count += inc_subsum_count;
        self
    }

    pub fn inc_false_possible_subsumer_count(&mut self, inc_subsum_count: Cint64) -> &mut Self {
        self.false_possible_subsum_count += inc_subsum_count;
        self
    }

    pub fn dec_possible_subsumer_count(&mut self, dec_subsum_count: Cint64) -> &mut Self {
        self.possible_subsum_count -= dec_subsum_count;
        self
    }

    pub fn get_temporary_role_classification_ontology(&self) -> Cint64 {
        self.temporary_role_classification_ontology
    }

    pub fn is_data_roles_classification(&self) -> bool {
        self.data_roles_classification
    }

    pub fn set_data_roles_classification(&mut self, data_roles: bool) -> &mut Self {
        self.data_roles_classification = data_roles;
        self
    }

    pub fn get_temporary_top_concept(&self) -> ConceptId {
        self.temporary_top_concept
    }

    pub fn set_temporary_top_concept(&mut self, concept: ConceptId) -> &mut Self {
        self.temporary_top_concept = concept;
        self
    }

    pub fn get_temporary_top_data_range_concept(&self) -> ConceptId {
        self.temporary_top_data_range_concept
    }

    pub fn set_temporary_top_data_range_concept(&mut self, concept: ConceptId) -> &mut Self {
        self.temporary_top_data_range_concept = concept;
        self
    }

    pub fn get_temporary_role_setup_top_concept(&self) -> ConceptId {
        if self.is_data_roles_classification() {
            self.get_temporary_top_data_range_concept()
        } else {
            self.get_temporary_top_concept()
        }
    }

    pub fn get_current_calculating_count(&self) -> Cint64 {
        self.current_calculating_count
    }

    pub fn inc_current_calculating_count(&mut self, inc_count: Cint64) -> &mut Self {
        self.current_calculating_count += inc_count;
        self
    }

    pub fn dec_current_calculating_count(&mut self, dec_count: Cint64) -> &mut Self {
        self.current_calculating_count -= dec_count;
        self
    }

    pub fn is_hierarchy_construction_failed(&self) -> bool {
        self.hierarchy_construction_failed
    }

    pub fn set_hierarchy_construction_failed(&mut self) -> &mut Self {
        self.hierarchy_construction_failed = true;
        self
    }

    pub fn reuse_calculation_statistics_collection(&mut self, statistics: Cint64) -> &mut Self {
        if statistics != INVALID {
            self.reused_statistics_collections.push(statistics);
        }
        self
    }

    pub fn get_reused_statistics_collections(&self) -> &[Cint64] {
        &self.reused_statistics_collections
    }

    pub fn get_computation_item_hash(
        &self,
    ) -> &HashMap<Cint64, PropertyClassificationComputationItem> {
        &self.work_item_hash
    }

    pub fn get_computation_item_hash_mut(
        &mut self,
    ) -> &mut HashMap<Cint64, PropertyClassificationComputationItem> {
        &mut self.work_item_hash
    }

    pub fn insert_computation_item(
        &mut self,
        sat_calc_job: Cint64,
        work_item: PropertyClassificationComputationItem,
    ) -> &mut Self {
        self.work_item_hash.insert(sat_calc_job, work_item);
        self
    }

    pub fn remove_computation_item_if_matching(
        &mut self,
        sat_calc_job: Cint64,
        work_item: &PropertyClassificationComputationItem,
    ) -> bool {
        if self
            .work_item_hash
            .get(&sat_calc_job)
            .map(|stored_work_item| stored_work_item == work_item)
            .unwrap_or(false)
        {
            self.work_item_hash.remove(&sat_calc_job);
            true
        } else {
            false
        }
    }

    pub fn set_temporary_role_classification_ontology(&mut self, ont: Cint64) -> &mut Self {
        self.temporary_role_classification_ontology = ont;
        self
    }

    pub fn get_marker_concept_instances_item_hash(
        &self,
    ) -> &HashMap<ConceptId, OptimizedKPSetRoleTestingItemId> {
        &self.marker_concept_instances_item_hash
    }

    pub fn get_marker_concept_instances_item_hash_mut(
        &mut self,
    ) -> &mut HashMap<ConceptId, OptimizedKPSetRoleTestingItemId> {
        &mut self.marker_concept_instances_item_hash
    }

    pub fn get_temporary_all_propagation_concept(&self) -> ConceptId {
        self.temporary_all_propagation_concept
    }

    pub fn set_temporary_all_propagation_concept(&mut self, concept: ConceptId) -> &mut Self {
        self.temporary_all_propagation_concept = concept;
        self
    }

    pub fn get_temporary_propagation_individual(&self) -> IndividualId {
        self.temporary_propagation_individual
    }

    pub fn get_temporary_marker_individual(&self) -> IndividualId {
        self.temporary_marker_individual
    }

    pub fn set_temporary_propagation_individual(&mut self, indi: IndividualId) -> &mut Self {
        self.temporary_propagation_individual = indi;
        self
    }

    pub fn set_temporary_marker_individual(&mut self, indi: IndividualId) -> &mut Self {
        self.temporary_marker_individual = indi;
        self
    }

    /// Port of `setIndividualDependenceTrackingCollector`.
    pub fn set_individual_dependence_tracking_collector(
        &mut self,
        collector: IndividualDependenceTrackingCollectorId,
    ) -> &mut Self {
        self.individual_dependence_tracking_collector = collector;
        self
    }

    /// Port of `getIndividualDependenceTrackingCollector`.
    pub fn get_individual_dependence_tracking_collector(
        &self,
    ) -> IndividualDependenceTrackingCollectorId {
        self.individual_dependence_tracking_collector
    }
}

impl Default for OptimizedKPSetClassOntologyClassificationItem {
    fn default() -> Self {
        Self::new()
    }
}

impl OptimizedKPSetClassOntologyClassificationItem {
    /// Constructor-side default: no collector until configuration enables
    /// individual-dependence tracking.
    pub fn new() -> Self {
        Self {
            individual_dependence_tracking_collector: IndividualDependenceTrackingCollectorId::NONE,
            concept_sat_item_hash: HashMap::new(),
            sat_test_item_container: Vec::new(),
            top_sat_test_item: OptimizedKPSetClassTestingItemId::NONE,
            bottom_sat_test_item: OptimizedKPSetClassTestingItemId::NONE,
            next_item_list: Vec::new(),
            next_cand_item_set: HashSet::new(),
            remaining_cand_item_set: HashSet::new(),
            next_poss_subsum_item_list: Vec::new(),
            current_poss_subsum_item_set: HashSet::new(),
            remaining_sat_tests: 0,
            running_sat_tests: 0,
            satisfiable_item_list: Vec::new(),
            concept_ref_link_data: HashMap::new(),
            satisfiable_testing_phase_finished: false,
            possible_subsumption_testing_phase_finished: false,
            remaining_possible_subsumption_tests: 0,
            running_possible_subsumption_tests: 0,
            rem_poss_class_testing_set: HashSet::new(),
            equivalent_concept_non_candidate_set: HashSet::new(),
            equivalent_concept_candidate_hash: HashMap::new(),
            calculated_possible_subsum_count: 0,
            calculated_true_possible_subsum_count: 0,
            calculated_false_possible_subsum_count: 0,
            possible_subsum_count: 0,
            true_possible_subsum_count: 0,
            false_possible_subsum_count: 0,
            memory_pools: Vec::new(),
            current_calculating_count: 0,
            taxonomy_construction_failed: false,
            reused_statistics_collections: Vec::new(),
            work_item_hash: HashMap::new(),
        }
    }

    pub fn get_concept_satisfiable_test_item_hash(
        &self,
    ) -> &HashMap<ConceptId, OptimizedKPSetClassTestingItemId> {
        &self.concept_sat_item_hash
    }

    pub fn get_concept_satisfiable_test_item_container(&self) -> &[OptimizedKPSetClassTestingItem] {
        &self.sat_test_item_container
    }

    pub fn get_concept_satisfiable_test_item_container_mut(
        &mut self,
    ) -> &mut [OptimizedKPSetClassTestingItem] {
        &mut self.sat_test_item_container
    }

    pub fn get_concept_satisfiable_test_item_mut(
        &mut self,
        item: OptimizedKPSetClassTestingItemId,
    ) -> Option<&mut OptimizedKPSetClassTestingItem> {
        if item.is_some() && item.index() < self.sat_test_item_container.len() {
            Some(&mut self.sat_test_item_container[item.index()])
        } else {
            None
        }
    }

    pub fn get_top_concept_satisfiable_test_item(&self) -> OptimizedKPSetClassTestingItemId {
        self.top_sat_test_item
    }

    pub fn get_bottom_concept_satisfiable_test_item(&self) -> OptimizedKPSetClassTestingItemId {
        self.bottom_sat_test_item
    }

    pub fn get_next_satisfiable_testing_item_list(&self) -> &[OptimizedKPSetClassTestingItemId] {
        &self.next_item_list
    }

    pub fn get_next_satisfiable_testing_item_list_mut(
        &mut self,
    ) -> &mut Vec<OptimizedKPSetClassTestingItemId> {
        &mut self.next_item_list
    }

    pub fn get_next_candidate_satisfiable_testing_item_set(
        &self,
    ) -> &HashSet<OptimizedKPSetClassTestingItemId> {
        &self.next_cand_item_set
    }

    pub fn get_next_candidate_satisfiable_testing_item_set_mut(
        &mut self,
    ) -> &mut HashSet<OptimizedKPSetClassTestingItemId> {
        &mut self.next_cand_item_set
    }

    pub fn get_remaining_candidate_satisfiable_testing_item_set(
        &self,
    ) -> &HashSet<OptimizedKPSetClassTestingItemId> {
        &self.remaining_cand_item_set
    }

    pub fn get_remaining_candidate_satisfiable_testing_item_set_mut(
        &mut self,
    ) -> &mut HashSet<OptimizedKPSetClassTestingItemId> {
        &mut self.remaining_cand_item_set
    }

    pub fn get_next_possible_subsumption_testing_item_list(
        &self,
    ) -> &[OptimizedKPSetClassTestingItemId] {
        &self.next_poss_subsum_item_list
    }

    pub fn get_next_possible_subsumption_testing_item_list_mut(
        &mut self,
    ) -> &mut Vec<OptimizedKPSetClassTestingItemId> {
        &mut self.next_poss_subsum_item_list
    }

    pub fn get_current_possible_subsumption_testing_item_set(
        &self,
    ) -> &HashSet<OptimizedKPSetClassTestingItemId> {
        &self.current_poss_subsum_item_set
    }

    pub fn get_current_possible_subsumption_testing_item_set_mut(
        &mut self,
    ) -> &mut HashSet<OptimizedKPSetClassTestingItemId> {
        &mut self.current_poss_subsum_item_set
    }

    pub fn init_top_bottom_satisfiable_testing_items(
        &mut self,
        top_item: OptimizedKPSetClassTestingItemId,
        bottom_item: OptimizedKPSetClassTestingItemId,
    ) -> &mut Self {
        self.top_sat_test_item = top_item;
        self.bottom_sat_test_item = bottom_item;
        self
    }

    fn resolve_class_satisfiable_test_concept(
        sat_test_concept: ConceptId,
        concepts: &Arena<Concept>,
    ) -> ConceptId {
        let concept = concepts.get(sat_test_concept);
        if concept.get_operator_code() == CCEQCAND {
            concept
                .get_operand_list()
                .first()
                .map(|operand| operand.target)
                .unwrap_or(sat_test_concept)
        } else {
            sat_test_concept
        }
    }

    pub fn get_concept_satisfiable_test_item(
        &mut self,
        sat_test_concept: ConceptId,
        create: bool,
        concepts: &Arena<Concept>,
    ) -> OptimizedKPSetClassTestingItemId {
        let resolved_concept =
            Self::resolve_class_satisfiable_test_concept(sat_test_concept, concepts);
        if let Some(item) = self.concept_sat_item_hash.get(&resolved_concept) {
            return *item;
        }
        if create {
            let item_id =
                OptimizedKPSetClassTestingItemId::new(self.sat_test_item_container.len() as Cint64);
            let mut item = OptimizedKPSetClassTestingItem::new();
            item.init_kpset_class_testing_item(
                resolved_concept,
                IndividualDependenceTrackingMarkerId::NONE,
            );
            self.sat_test_item_container.push(item);
            self.concept_sat_item_hash.insert(resolved_concept, item_id);
            item_id
        } else {
            OptimizedKPSetClassTestingItemId::NONE
        }
    }

    pub fn add_memory_pools(&mut self, memory_pools: Cint64) -> &mut Self {
        if memory_pools != INVALID {
            self.memory_pools.push(memory_pools);
        }
        self
    }

    pub fn get_memory_pool_list(&self) -> &[Cint64] {
        &self.memory_pools
    }

    pub fn get_current_calculating_count(&self) -> Cint64 {
        self.current_calculating_count
    }

    pub fn inc_current_calculating_count(&mut self, inc_count: Cint64) -> &mut Self {
        self.current_calculating_count += inc_count;
        self
    }

    pub fn dec_current_calculating_count(&mut self, dec_count: Cint64) -> &mut Self {
        self.current_calculating_count -= dec_count;
        self
    }

    pub fn is_taxonomy_construction_failed(&self) -> bool {
        self.taxonomy_construction_failed
    }

    pub fn set_taxonomy_construction_failed(&mut self) -> &mut Self {
        self.taxonomy_construction_failed = true;
        self
    }

    pub fn reuse_calculation_statistics_collection(&mut self, statistics: Cint64) -> &mut Self {
        if statistics != INVALID {
            self.reused_statistics_collections.push(statistics);
        }
        self
    }

    pub fn get_reused_statistics_collections(&self) -> &[Cint64] {
        &self.reused_statistics_collections
    }

    pub fn get_work_item_hash(&self) -> &HashMap<Cint64, ClassClassificationComputationItem> {
        &self.work_item_hash
    }

    pub fn get_work_item_hash_mut(
        &mut self,
    ) -> &mut HashMap<Cint64, ClassClassificationComputationItem> {
        &mut self.work_item_hash
    }

    pub fn insert_work_item(
        &mut self,
        sat_calc_job: Cint64,
        work_item: ClassClassificationComputationItem,
    ) -> &mut Self {
        self.work_item_hash.insert(sat_calc_job, work_item);
        self
    }

    pub fn remove_work_item_if_matching(
        &mut self,
        sat_calc_job: Cint64,
        work_item: &ClassClassificationComputationItem,
    ) -> bool {
        if self
            .work_item_hash
            .get(&sat_calc_job)
            .map(|stored_work_item| stored_work_item == work_item)
            .unwrap_or(false)
        {
            self.work_item_hash.remove(&sat_calc_job);
            true
        } else {
            false
        }
    }

    pub fn has_all_satisfiable_tests_completed(&self) -> bool {
        self.remaining_sat_tests <= 0 && self.running_sat_tests <= 0
    }

    pub fn has_remaining_satisfiable_tests(&self) -> bool {
        self.remaining_sat_tests > 0
    }

    pub fn get_remaining_satisfiable_tests_count(&self) -> Cint64 {
        self.remaining_sat_tests
    }

    pub fn get_running_satisfiable_tests_count(&self) -> Cint64 {
        self.running_sat_tests
    }

    pub fn inc_remaining_satisfiable_tests_count(&mut self, inc_count: Cint64) -> &mut Self {
        self.remaining_sat_tests += inc_count;
        self
    }

    pub fn inc_running_satisfiable_tests_count(&mut self, inc_count: Cint64) -> &mut Self {
        self.running_sat_tests += inc_count;
        self
    }

    pub fn dec_remaining_satisfiable_tests_count(&mut self, dec_count: Cint64) -> &mut Self {
        self.remaining_sat_tests -= dec_count;
        self
    }

    pub fn dec_running_satisfiable_tests_count(&mut self, dec_count: Cint64) -> &mut Self {
        self.running_sat_tests -= dec_count;
        self
    }

    pub fn get_satisfiable_concept_item_list(&self) -> &[OptimizedKPSetClassTestingItemId] {
        &self.satisfiable_item_list
    }

    pub fn add_satisfiable_concept_item(
        &mut self,
        item: OptimizedKPSetClassTestingItemId,
    ) -> &mut Self {
        self.satisfiable_item_list.push(item);
        self
    }

    pub fn get_concept_reference_linking_data_hash(&self) -> &HashMap<ConceptId, Cint64> {
        &self.concept_ref_link_data
    }

    pub fn get_concept_reference_linking_data_hash_mut(
        &mut self,
    ) -> &mut HashMap<ConceptId, Cint64> {
        &mut self.concept_ref_link_data
    }

    pub fn has_satisfiable_testing_phase_finished(&self) -> bool {
        self.satisfiable_testing_phase_finished
    }

    pub fn has_possible_subsumption_testing_phase_finished(&self) -> bool {
        self.possible_subsumption_testing_phase_finished
    }

    pub fn set_satisfiable_testing_phase_finished(&mut self, finished: bool) -> &mut Self {
        self.satisfiable_testing_phase_finished = finished;
        self
    }

    pub fn set_possible_subsumption_testing_phase_finished(&mut self, finished: bool) -> &mut Self {
        self.possible_subsumption_testing_phase_finished = finished;
        self
    }

    pub fn get_remaining_possible_subsumption_tests_count(&self) -> Cint64 {
        self.remaining_possible_subsumption_tests
    }

    pub fn has_remaining_possible_subsumption_tests(&self) -> bool {
        self.remaining_possible_subsumption_tests > 0
    }

    pub fn inc_remaining_possible_subsumption_tests_count(
        &mut self,
        inc_count: Cint64,
    ) -> &mut Self {
        self.remaining_possible_subsumption_tests += inc_count;
        self
    }

    pub fn dec_remaining_possible_subsumption_tests_count(
        &mut self,
        dec_count: Cint64,
    ) -> &mut Self {
        self.remaining_possible_subsumption_tests -= dec_count;
        self
    }

    pub fn set_remaining_possible_subsumption_tests_count(
        &mut self,
        test_count: Cint64,
    ) -> &mut Self {
        self.remaining_possible_subsumption_tests = test_count;
        self
    }

    pub fn get_remaining_possible_subsumption_class_testing_set(
        &self,
    ) -> &HashSet<OptimizedKPSetClassTestingItemId> {
        &self.rem_poss_class_testing_set
    }

    pub fn get_remaining_possible_subsumption_class_testing_set_mut(
        &mut self,
    ) -> &mut HashSet<OptimizedKPSetClassTestingItemId> {
        &mut self.rem_poss_class_testing_set
    }

    pub fn get_remaining_possible_subsumption_class_testing_count(&self) -> Cint64 {
        self.rem_poss_class_testing_set.len() as Cint64
    }

    pub fn inc_running_possible_subsumption_tests_count(&mut self, inc_count: Cint64) -> &mut Self {
        self.running_possible_subsumption_tests += inc_count;
        self
    }

    pub fn dec_running_possible_subsumption_tests_count(&mut self, dec_count: Cint64) -> &mut Self {
        self.running_possible_subsumption_tests -= dec_count;
        self
    }

    pub fn get_running_possible_subsumption_tests_count(&self) -> Cint64 {
        self.running_possible_subsumption_tests
    }

    pub fn get_equivaltent_concept_non_candidate_set(&self) -> &HashSet<ConceptId> {
        &self.equivalent_concept_non_candidate_set
    }

    pub fn get_equivaltent_concept_non_candidate_set_mut(&mut self) -> &mut HashSet<ConceptId> {
        &mut self.equivalent_concept_non_candidate_set
    }

    pub fn get_equivalent_concept_candidate_hash(&self) -> &HashMap<ConceptId, ConceptId> {
        &self.equivalent_concept_candidate_hash
    }

    pub fn get_equivalent_concept_candidate_hash_mut(
        &mut self,
    ) -> &mut HashMap<ConceptId, ConceptId> {
        &mut self.equivalent_concept_candidate_hash
    }

    pub fn get_calculated_possible_subsumer_count(&self) -> Cint64 {
        self.calculated_possible_subsum_count
    }

    pub fn get_calculated_true_possible_subsumer_count(&self) -> Cint64 {
        self.calculated_true_possible_subsum_count
    }

    pub fn get_calculated_false_possible_subsumer_count(&self) -> Cint64 {
        self.calculated_false_possible_subsum_count
    }

    pub fn set_calculated_possible_subsumer_count(&mut self, subsum_count: Cint64) -> &mut Self {
        self.calculated_possible_subsum_count = subsum_count;
        self
    }

    pub fn set_calculated_true_possible_subsumer_count(
        &mut self,
        subsum_count: Cint64,
    ) -> &mut Self {
        self.calculated_true_possible_subsum_count = subsum_count;
        self
    }

    pub fn set_calculated_false_possible_subsumer_count(
        &mut self,
        subsum_count: Cint64,
    ) -> &mut Self {
        self.calculated_false_possible_subsum_count = subsum_count;
        self
    }

    pub fn inc_calculated_possible_subsumer_count(
        &mut self,
        inc_subsum_count: Cint64,
    ) -> &mut Self {
        self.calculated_possible_subsum_count += inc_subsum_count;
        self
    }

    pub fn inc_calculated_true_possible_subsumer_count(
        &mut self,
        inc_subsum_count: Cint64,
    ) -> &mut Self {
        self.calculated_true_possible_subsum_count += inc_subsum_count;
        self
    }

    pub fn inc_calculated_false_possible_subsumer_count(
        &mut self,
        inc_subsum_count: Cint64,
    ) -> &mut Self {
        self.calculated_false_possible_subsum_count += inc_subsum_count;
        self
    }

    pub fn get_possible_subsumer_count(&self) -> Cint64 {
        self.possible_subsum_count
    }

    pub fn get_true_possible_subsumer_count(&self) -> Cint64 {
        self.true_possible_subsum_count
    }

    pub fn get_false_possible_subsumer_count(&self) -> Cint64 {
        self.false_possible_subsum_count
    }

    pub fn set_possible_subsumer_count(&mut self, subsum_count: Cint64) -> &mut Self {
        self.possible_subsum_count = subsum_count;
        self
    }

    pub fn set_true_possible_subsumer_count(&mut self, subsum_count: Cint64) -> &mut Self {
        self.true_possible_subsum_count = subsum_count;
        self
    }

    pub fn set_false_possible_subsumer_count(&mut self, subsum_count: Cint64) -> &mut Self {
        self.false_possible_subsum_count = subsum_count;
        self
    }

    pub fn inc_possible_subsumer_count(&mut self, inc_subsum_count: Cint64) -> &mut Self {
        self.possible_subsum_count += inc_subsum_count;
        self
    }

    pub fn inc_true_possible_subsumer_count(&mut self, inc_subsum_count: Cint64) -> &mut Self {
        self.true_possible_subsum_count += inc_subsum_count;
        self
    }

    pub fn inc_false_possible_subsumer_count(&mut self, inc_subsum_count: Cint64) -> &mut Self {
        self.false_possible_subsum_count += inc_subsum_count;
        self
    }

    /// Port of `setIndividualDependenceTrackingCollector`.
    pub fn set_individual_dependence_tracking_collector(
        &mut self,
        collector: IndividualDependenceTrackingCollectorId,
    ) -> &mut Self {
        self.individual_dependence_tracking_collector = collector;
        self
    }

    /// Port of `getIndividualDependenceTrackingCollector`.
    pub fn get_individual_dependence_tracking_collector(
        &self,
    ) -> IndividualDependenceTrackingCollectorId {
        self.individual_dependence_tracking_collector
    }
}

impl Default for OptimizedSubClassOntologyClassificationItem {
    fn default() -> Self {
        Self::new()
    }
}

impl OptimizedSubClassOntologyClassificationItem {
    /// Constructor-side default: no collector until configuration enables
    /// individual-dependence tracking.
    pub fn new() -> Self {
        Self {
            individual_dependence_tracking_collector: IndividualDependenceTrackingCollectorId::NONE,
        }
    }

    /// Port of `setIndividualDependenceTrackingCollector`.
    pub fn set_individual_dependence_tracking_collector(
        &mut self,
        collector: IndividualDependenceTrackingCollectorId,
    ) -> &mut Self {
        self.individual_dependence_tracking_collector = collector;
        self
    }

    /// Port of `getIndividualDependenceTrackingCollector`.
    pub fn get_individual_dependence_tracking_collector(
        &self,
    ) -> IndividualDependenceTrackingCollectorId {
        self.individual_dependence_tracking_collector
    }
}

/// Minimal port of `COptimizedSubClassSatisfiableTestingItem` fields needed at
/// the individual-dependence adapter call site.
#[derive(Debug, Clone)]
pub struct OptimizedSubClassSatisfiableTestingItem {
    /// `CConcept* mConceptSat`.
    satisfiable_concept: ConceptId,
    /// The item's `CIndividualDependenceTrackingMarker` base payload.
    individual_dependence_tracking_marker: IndividualDependenceTrackingMarkerId,
}

/// Port of `CClassificationClassPseudoModelDeterministicFlag`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ClassificationClassPseudoModelDeterministicFlag {
    deterministic_flag: bool,
}

impl Default for ClassificationClassPseudoModelDeterministicFlag {
    fn default() -> Self {
        Self::new()
    }
}

impl ClassificationClassPseudoModelDeterministicFlag {
    pub fn new() -> Self {
        Self {
            deterministic_flag: false,
        }
    }

    pub fn is_deterministic(&self) -> bool {
        self.deterministic_flag
    }

    pub fn is_non_deterministic(&self) -> bool {
        !self.deterministic_flag
    }

    pub fn set_deterministic(&mut self, deterministic: bool) -> bool {
        let different = self.deterministic_flag != deterministic;
        self.deterministic_flag = deterministic;
        different
    }
}

/// Port of `CClassificationClassPseudoModelConceptData`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ClassificationClassPseudoModelConceptData {
    deterministic_flag: ClassificationClassPseudoModelDeterministicFlag,
}

impl Default for ClassificationClassPseudoModelConceptData {
    fn default() -> Self {
        Self::new()
    }
}

impl ClassificationClassPseudoModelConceptData {
    pub fn new() -> Self {
        Self {
            deterministic_flag: ClassificationClassPseudoModelDeterministicFlag::new(),
        }
    }

    pub fn new_with_deterministic(deterministic: bool) -> Self {
        let mut data = Self::new();
        data.set_deterministic(deterministic);
        data
    }

    pub fn is_deterministic(&self) -> bool {
        self.deterministic_flag.is_deterministic()
    }

    pub fn is_non_deterministic(&self) -> bool {
        self.deterministic_flag.is_non_deterministic()
    }

    pub fn set_deterministic(&mut self, deterministic: bool) -> bool {
        self.deterministic_flag.set_deterministic(deterministic)
    }
}

/// Port of `CClassificationClassPseudoModelRoleData`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ClassificationClassPseudoModelRoleData {
    deterministic_flag: ClassificationClassPseudoModelDeterministicFlag,
    lower_at_least: Cint64,
    upper_at_least: Cint64,
    lower_at_most: Cint64,
    upper_at_most: Cint64,
    successor_model: Cint64,
}

impl Default for ClassificationClassPseudoModelRoleData {
    fn default() -> Self {
        Self::new()
    }
}

impl ClassificationClassPseudoModelRoleData {
    pub fn new() -> Self {
        Self {
            deterministic_flag: ClassificationClassPseudoModelDeterministicFlag::new(),
            lower_at_least: 0,
            upper_at_least: 0,
            lower_at_most: 0,
            upper_at_most: 0,
            successor_model: 0,
        }
    }

    pub fn is_deterministic(&self) -> bool {
        self.deterministic_flag.is_deterministic()
    }

    pub fn is_non_deterministic(&self) -> bool {
        self.deterministic_flag.is_non_deterministic()
    }

    pub fn set_deterministic(&mut self, deterministic: bool) -> bool {
        self.deterministic_flag.set_deterministic(deterministic)
    }

    pub fn get_lower_at_least_bound(&self) -> Cint64 {
        self.lower_at_least
    }

    pub fn get_upper_at_least_bound(&self) -> Cint64 {
        self.upper_at_least
    }

    pub fn get_lower_at_most_bound(&self) -> Cint64 {
        self.lower_at_most
    }

    pub fn get_upper_at_most_bound(&self) -> Cint64 {
        self.upper_at_most
    }

    pub fn get_successor_model_id(&self) -> Cint64 {
        self.successor_model
    }

    pub fn set_lower_at_least_bound(&mut self, bound: Cint64) -> bool {
        let diff = self.lower_at_least != bound;
        self.lower_at_least = bound;
        diff
    }

    pub fn set_upper_at_least_bound(&mut self, bound: Cint64) -> bool {
        let diff = self.upper_at_least != bound;
        self.upper_at_least = bound;
        diff
    }

    pub fn set_lower_at_most_bound(&mut self, bound: Cint64) -> bool {
        let diff = self.lower_at_most != bound;
        self.lower_at_most = bound;
        diff
    }

    pub fn set_upper_at_most_bound(&mut self, bound: Cint64) -> bool {
        let diff = self.upper_at_most != bound;
        self.upper_at_most = bound;
        diff
    }

    pub fn set_successor_model_id(&mut self, model_id: Cint64) -> bool {
        let diff = self.successor_model != model_id;
        self.successor_model = model_id;
        diff
    }

    pub fn is_possible_subsumer_of(
        &self,
        possible_subsumed_data: &ClassificationClassPseudoModelRoleData,
    ) -> bool {
        if self.is_deterministic() {
            if self.lower_at_least > possible_subsumed_data.upper_at_least {
                return false;
            }
            if self.upper_at_most < possible_subsumed_data.lower_at_most {
                return false;
            }
        }
        true
    }
}

/// Port of `CClassificationClassPseudoModelConceptMap`.
#[derive(Debug, Clone, Default)]
pub struct ClassificationClassPseudoModelConceptMap {
    data: BTreeMap<Cint64, (ConceptId, ClassificationClassPseudoModelConceptData)>,
}

impl ClassificationClassPseudoModelConceptMap {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn init_pseudo_model_concept_map(
        &mut self,
        con_map: Option<&ClassificationClassPseudoModelConceptMap>,
    ) -> &mut Self {
        if let Some(con_map) = con_map {
            *self = con_map.clone();
        }
        self
    }

    pub fn insert(
        &mut self,
        concept: ConceptId,
        data: ClassificationClassPseudoModelConceptData,
    ) -> Option<ClassificationClassPseudoModelConceptData> {
        self.data
            .insert(concept.raw, (concept, data))
            .map(|(_, data)| data)
    }

    pub fn get(&self, concept: ConceptId) -> Option<&ClassificationClassPseudoModelConceptData> {
        self.data.get(&concept.raw).map(|(_, data)| data)
    }

    pub fn entry(&mut self, concept: ConceptId) -> &mut ClassificationClassPseudoModelConceptData {
        &mut self
            .data
            .entry(concept.raw)
            .or_insert((concept, ClassificationClassPseudoModelConceptData::new()))
            .1
    }

    pub fn iter(
        &self,
    ) -> impl Iterator<Item = (ConceptId, &ClassificationClassPseudoModelConceptData)> {
        self.data.values().map(|(concept, data)| (*concept, data))
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }

    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }
}

/// Port of `CClassificationClassPseudoModelRoleMap`.
#[derive(Debug, Clone, Default)]
pub struct ClassificationClassPseudoModelRoleMap {
    data: BTreeMap<Cint64, (RoleId, ClassificationClassPseudoModelRoleData)>,
}

impl ClassificationClassPseudoModelRoleMap {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn init_pseudo_model_role_map(
        &mut self,
        role_map: Option<&ClassificationClassPseudoModelRoleMap>,
    ) -> &mut Self {
        if let Some(role_map) = role_map {
            *self = role_map.clone();
        }
        self
    }

    pub fn insert(
        &mut self,
        role: RoleId,
        data: ClassificationClassPseudoModelRoleData,
    ) -> Option<ClassificationClassPseudoModelRoleData> {
        self.data
            .insert(role.raw, (role, data))
            .map(|(_, data)| data)
    }

    pub fn get(&self, role: RoleId) -> Option<&ClassificationClassPseudoModelRoleData> {
        self.data.get(&role.raw).map(|(_, data)| data)
    }

    pub fn entry(&mut self, role: RoleId) -> &mut ClassificationClassPseudoModelRoleData {
        &mut self
            .data
            .entry(role.raw)
            .or_insert((role, ClassificationClassPseudoModelRoleData::new()))
            .1
    }

    pub fn iter(&self) -> impl Iterator<Item = (RoleId, &ClassificationClassPseudoModelRoleData)> {
        self.data.values().map(|(role, data)| (*role, data))
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }

    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }
}

/// Port of `CClassificationClassPseudoModelData`.
#[derive(Debug, Clone)]
pub struct ClassificationClassPseudoModelData {
    concept_map: Option<ClassificationClassPseudoModelConceptMap>,
    role_map: Option<ClassificationClassPseudoModelRoleMap>,
    valid_role_map: bool,
    valid_concept_map: bool,
}

impl Default for ClassificationClassPseudoModelData {
    fn default() -> Self {
        Self::new()
    }
}

impl ClassificationClassPseudoModelData {
    pub fn new() -> Self {
        Self {
            concept_map: None,
            role_map: None,
            valid_role_map: false,
            valid_concept_map: false,
        }
    }

    pub fn init_pseudo_model_data(
        &mut self,
        data: Option<&ClassificationClassPseudoModelData>,
    ) -> &mut Self {
        if let Some(data) = data {
            self.concept_map = data.concept_map.clone();
            self.role_map = data.role_map.clone();
            self.valid_concept_map = data.valid_concept_map;
            self.valid_role_map = data.valid_role_map;
        }
        self
    }

    pub fn get_pseudo_model_concept_map(
        &self,
    ) -> Option<&ClassificationClassPseudoModelConceptMap> {
        self.concept_map.as_ref()
    }

    pub fn get_pseudo_model_concept_map_mut(
        &mut self,
        create: bool,
    ) -> Option<&mut ClassificationClassPseudoModelConceptMap> {
        if self.concept_map.is_none() && create {
            self.concept_map = Some(ClassificationClassPseudoModelConceptMap::new());
        }
        self.concept_map.as_mut()
    }

    pub fn get_pseudo_model_role_map(&self) -> Option<&ClassificationClassPseudoModelRoleMap> {
        self.role_map.as_ref()
    }

    pub fn get_pseudo_model_role_map_mut(
        &mut self,
        create: bool,
    ) -> Option<&mut ClassificationClassPseudoModelRoleMap> {
        if self.role_map.is_none() && create {
            self.role_map = Some(ClassificationClassPseudoModelRoleMap::new());
        }
        self.role_map.as_mut()
    }

    pub fn has_valid_role_map(&self) -> bool {
        self.valid_role_map
    }

    pub fn has_valid_concept_map(&self) -> bool {
        self.valid_concept_map
    }

    pub fn set_valid_role_map(&mut self, valid: bool) -> &mut Self {
        self.valid_role_map = valid;
        self
    }

    pub fn set_valid_concept_map(&mut self, valid: bool) -> &mut Self {
        self.valid_concept_map = valid;
        self
    }
}

/// Port of `CClassificationClassPseudoModelHash`.
#[derive(Debug, Clone, Default)]
pub struct ClassificationClassPseudoModelHash {
    data: BTreeMap<Cint64, ClassificationClassPseudoModelData>,
}

impl ClassificationClassPseudoModelHash {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn init_pseudo_model_hash(
        &mut self,
        hash: Option<&ClassificationClassPseudoModelHash>,
    ) -> &mut Self {
        if let Some(hash) = hash {
            self.data = hash.data.clone();
        } else {
            self.data.clear();
        }
        self
    }

    pub fn get_pseudo_model_data(
        &self,
        node: Cint64,
    ) -> Option<&ClassificationClassPseudoModelData> {
        self.data.get(&node)
    }

    pub fn get_pseudo_model_data_mut(
        &mut self,
        node: Cint64,
        create: bool,
    ) -> Option<&mut ClassificationClassPseudoModelData> {
        if create {
            self.data
                .entry(node)
                .or_insert_with(ClassificationClassPseudoModelData::new);
        }
        self.data.get_mut(&node)
    }

    pub fn get_count(&self) -> Cint64 {
        self.data.len() as Cint64
    }
}

/// Port of `CClassificationClassPseudoModel`.
#[derive(Debug, Clone, Default)]
pub struct ClassificationClassPseudoModel {
    pseudo_model_hash: Option<ClassificationClassPseudoModelHash>,
}

impl ClassificationClassPseudoModel {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn get_pseudo_model_hash(&self) -> Option<&ClassificationClassPseudoModelHash> {
        self.pseudo_model_hash.as_ref()
    }

    pub fn get_pseudo_model_hash_mut(&mut self) -> Option<&mut ClassificationClassPseudoModelHash> {
        self.pseudo_model_hash.as_mut()
    }

    pub fn set_pseudo_model_hash(
        &mut self,
        pm_hash: Option<ClassificationClassPseudoModelHash>,
    ) -> &mut Self {
        self.pseudo_model_hash = pm_hash;
        self
    }
}

/// Port of `CClassificationMessageData::CLASSIFICATIONMESSAGEDATA`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ClassificationMessageDataType {
    TellClassSubsumption,
    TellPropertySubsumption,
    TellClassPseudoModelIdentifiers,
    TellClassInitializePossibleSubsumption,
    TellPropertyInitializePossibleSubsumption,
    TellClassUpdatePossibleSubsumption,
    TellPropertyUpdatePossibleSubsumption,
}

/// Port of the base `CClassificationMessageData` message header.
#[derive(Debug, Clone)]
pub struct ClassificationMessageData {
    message_data_type: ClassificationMessageDataType,
}

impl ClassificationMessageData {
    pub fn new(message_data_type: ClassificationMessageDataType) -> Self {
        Self { message_data_type }
    }

    pub fn get_classification_message_data_type(&self) -> ClassificationMessageDataType {
        self.message_data_type
    }
}

/// Typed Rust payload for a `CClassificationMessageData*` chain.
#[derive(Debug, Clone)]
pub enum ClassificationMessageDataPayload {
    /// Port of `CClassificationClassSubsumptionMessageData`.
    ClassSubsumption(ClassificationClassSubsumptionMessageData),
    /// Port of `CClassificationInitializePossibleClassSubsumptionMessageData`.
    InitializePossibleClassSubsumption(ClassificationInitializePossibleClassSubsumptionMessageData),
    /// Port of `CClassificationUpdatePossibleClassSubsumptionMessageData`.
    UpdatePossibleClassSubsumption(ClassificationUpdatePossibleClassSubsumptionMessageData),
    /// Port of a `CClassificationPseudoModelIdentifierMessageData` node.
    PseudoModelIdentifier(ClassificationPseudoModelIdentifierMessageData),
    /// Header-only placeholder for message subtypes whose concrete payload is
    /// still ported elsewhere.
    Header(ClassificationMessageData),
}

impl ClassificationMessageDataPayload {
    pub fn from_class_subsumption(message: ClassificationClassSubsumptionMessageData) -> Self {
        ClassificationMessageDataPayload::ClassSubsumption(message)
    }

    pub fn from_initialize_possible_class_subsumption(
        message: ClassificationInitializePossibleClassSubsumptionMessageData,
    ) -> Self {
        ClassificationMessageDataPayload::InitializePossibleClassSubsumption(message)
    }

    pub fn from_update_possible_class_subsumption(
        message: ClassificationUpdatePossibleClassSubsumptionMessageData,
    ) -> Self {
        ClassificationMessageDataPayload::UpdatePossibleClassSubsumption(message)
    }

    pub fn from_pseudo_model_identifier(
        message: ClassificationPseudoModelIdentifierMessageData,
    ) -> Self {
        ClassificationMessageDataPayload::PseudoModelIdentifier(message)
    }

    pub fn get_classification_message_data_type(&self) -> ClassificationMessageDataType {
        match self {
            ClassificationMessageDataPayload::ClassSubsumption(message) => {
                message.get_classification_message_data_type()
            }
            ClassificationMessageDataPayload::InitializePossibleClassSubsumption(message) => {
                message.get_classification_message_data_type()
            }
            ClassificationMessageDataPayload::UpdatePossibleClassSubsumption(message) => {
                message.get_classification_message_data_type()
            }
            ClassificationMessageDataPayload::PseudoModelIdentifier(message) => {
                message.get_classification_message_data_type()
            }
            ClassificationMessageDataPayload::Header(message) => {
                message.get_classification_message_data_type()
            }
        }
    }
}

/// Port of the `CLinkerBase<CClassificationMessageData*>` chain.
///
/// KONCLUDE-PORT-NOTE[ownership]: C++ stores the next pointer on every message
/// object. The port keeps an owned head-to-tail vector; `prepend_message`
/// corresponds to `message->append(existingHead)`, while
/// `append_linker_as_head` corresponds to `headChain->append(tailChain)`.
#[derive(Debug, Clone, Default)]
pub struct ClassificationMessageDataLinker {
    messages: Vec<ClassificationMessageDataPayload>,
}

impl ClassificationMessageDataLinker {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn from_message(message: ClassificationMessageDataPayload) -> Self {
        Self {
            messages: vec![message],
        }
    }

    pub fn push_front_message(&mut self, message: ClassificationMessageDataPayload) -> &mut Self {
        self.messages.insert(0, message);
        self
    }

    pub fn prepend_message(&mut self, message: ClassificationMessageDataPayload) -> &mut Self {
        self.push_front_message(message)
    }

    pub fn append_linker(
        mut self,
        tail: ClassificationMessageDataLinker,
    ) -> ClassificationMessageDataLinker {
        self.messages.extend(tail.messages);
        self
    }

    pub fn append_linker_as_head(
        head: ClassificationMessageDataLinker,
        tail: ClassificationMessageDataLinker,
    ) -> ClassificationMessageDataLinker {
        head.append_linker(tail)
    }

    pub fn is_empty(&self) -> bool {
        self.messages.is_empty()
    }

    pub fn len(&self) -> usize {
        self.messages.len()
    }

    pub fn iter(&self) -> impl Iterator<Item = &ClassificationMessageDataPayload> {
        self.messages.iter()
    }

    pub fn message_types(&self) -> Vec<ClassificationMessageDataType> {
        self.messages
            .iter()
            .map(|message| message.get_classification_message_data_type())
            .collect()
    }
}

/// Port of `CClassificationMessageDataObserver`.
///
/// KONCLUDE-PORT-NOTE[threading]: Konclude implementations usually post an
/// event and process it on the classifier thread. This trait preserves the
/// observer call surface while the event/ontology lookup layer remains separate.
pub trait ClassificationMessageDataObserver {
    fn tell_classification_message(
        &mut self,
        ontology: Cint64,
        message_data: ClassificationMessageDataLinker,
        memory_pool: Cint64,
    ) -> &mut Self;
}

/// Port-side registry for `CClassificationMessageDataObserver*` handles.
///
/// Konclude stores the observer pointer directly on
/// `CSatisfiableTaskClassificationMessageAdapter` and dereferences it at the
/// final analyser delivery call. The Rust port keeps the adapter field as the
/// raw pointer-shaped `cint64` handle and resolves it through this arena when a
/// classifier thread/driver owns concrete observers.
pub struct ClassificationMessageDataObserverRegistry<O: ClassificationMessageDataObserver> {
    observers: Arena<O>,
}

impl<O: ClassificationMessageDataObserver> ClassificationMessageDataObserverRegistry<O> {
    pub fn new() -> Self {
        Self {
            observers: Arena::new(),
        }
    }

    /// Port of storing a concrete `CClassificationMessageDataObserver*`.
    pub fn alloc_observer(&mut self, observer: O) -> Cint64 {
        self.observers.push(observer).raw
    }

    /// Resolve the adapter's opaque observer pointer handle.
    pub fn get_observer(&self, observer: Cint64) -> Option<&O> {
        if observer >= 0 && (observer as usize) < self.observers.len() {
            Some(self.observers.get(Id::new(observer)))
        } else {
            None
        }
    }

    /// Mutable resolve used by `tellClassificationMessage`.
    pub fn get_observer_mut(&mut self, observer: Cint64) -> Option<&mut O> {
        if observer >= 0 && (observer as usize) < self.observers.len() {
            Some(self.observers.get_mut(Id::new(observer)))
        } else {
            None
        }
    }
}

impl<O: ClassificationMessageDataObserver> Default
    for ClassificationMessageDataObserverRegistry<O>
{
    fn default() -> Self {
        Self::new()
    }
}

/// Test and bridge implementation of `CClassificationMessageDataObserver` that
/// stores delivered message chains in call order.
#[derive(Debug, Default, Clone)]
pub struct RecordingClassificationMessageDataObserver {
    told_messages: Vec<(Cint64, ClassificationMessageDataLinker, Cint64)>,
}

impl RecordingClassificationMessageDataObserver {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn get_told_messages(&self) -> &[(Cint64, ClassificationMessageDataLinker, Cint64)] {
        &self.told_messages
    }
}

impl ClassificationMessageDataObserver for RecordingClassificationMessageDataObserver {
    fn tell_classification_message(
        &mut self,
        ontology: Cint64,
        message_data: ClassificationMessageDataLinker,
        memory_pool: Cint64,
    ) -> &mut Self {
        self.told_messages
            .push((ontology, message_data, memory_pool));
        self
    }
}

/// Bounded port of the analyser's final
/// `classMessObserver->tellClassificationMessage(testOntology, messageDataLinker,
/// memPoolCon.takeMemoryPools())` delivery call.
///
/// The adapter still stores the observer as an opaque handle until classifier
/// thread event routing is live. This helper preserves the C++ call surface by
/// requiring both the opaque handle and a concrete bridge observer.
pub fn deliver_classification_message_data_to_observer<O: ClassificationMessageDataObserver>(
    adapter: &SatisfiableTaskClassificationMessageAdapter,
    message_data_linker: Option<ClassificationMessageDataLinker>,
    memory_pool: Cint64,
    observer: Option<&mut O>,
) -> bool {
    if adapter.get_classification_message_data_observer() == INVALID {
        return false;
    }
    let Some(message_data_linker) = message_data_linker else {
        return false;
    };
    if message_data_linker.is_empty() {
        return false;
    }
    let Some(observer) = observer else {
        return false;
    };

    observer.tell_classification_message(
        adapter.get_testing_ontology(),
        message_data_linker,
        memory_pool,
    );
    true
}

/// Registry-backed form of the same final analyser delivery call.
pub fn deliver_classification_message_data_to_registered_observer<
    O: ClassificationMessageDataObserver,
>(
    adapter: &SatisfiableTaskClassificationMessageAdapter,
    message_data_linker: Option<ClassificationMessageDataLinker>,
    memory_pool: Cint64,
    observer_registry: Option<&mut ClassificationMessageDataObserverRegistry<O>>,
) -> bool {
    let Some(observer_registry) = observer_registry else {
        return false;
    };
    let observer =
        observer_registry.get_observer_mut(adapter.get_classification_message_data_observer());
    deliver_classification_message_data_to_observer(
        adapter,
        message_data_linker,
        memory_pool,
        observer,
    )
}

/// Bounded port of the analyser-side classifier-reference lookup used before
/// scheduling an other-node analysed concept.
///
/// Konclude first tries `CConceptProcessData::getConceptReferenceLinking()` when
/// the concept data is present and not invalidated. If no live concept reference
/// exists, it falls back to the adapter's
/// `mConRefLinkDataHash[analyseConcept]`. The resolved classifier reference is
/// then queried for
/// `isMoreConceptClassificationInformationRequired()`.
pub fn is_more_classification_information_required_for_concept(
    concept: ConceptId,
    concepts: &Arena<Concept>,
    concept_process_datas: &Arena<ConceptProcessData>,
    concept_reference_linking_datas: &Arena<ConceptSaturationReferenceLinkingData>,
    adapter: &SatisfiableTaskClassificationMessageAdapter,
    testing_items: &[OptimizedKPSetClassTestingItem],
) -> bool {
    let Some(class_ref_link_data) = resolve_classification_reference_linking_data(
        concept,
        concepts,
        concept_process_datas,
        concept_reference_linking_datas,
        Some(adapter.get_concept_reference_linking_data_hash()),
    ) else {
        return false;
    };

    let item_id = OptimizedKPSetClassTestingItemId::new(class_ref_link_data);
    item_id.is_some()
        && item_id.index() < testing_items.len()
        && testing_items[item_id.index()].is_more_concept_classification_information_required()
}

fn resolve_classification_reference_linking_data(
    concept: ConceptId,
    concepts: &Arena<Concept>,
    concept_process_datas: &Arena<ConceptProcessData>,
    concept_reference_linking_datas: &Arena<ConceptSaturationReferenceLinkingData>,
    concept_reference_linking_data_hash: Option<&HashMap<ConceptId, Cint64>>,
) -> Option<Cint64> {
    if concept.is_none() || concept.index() >= concepts.len() {
        return None;
    }
    let concept_data = concepts.get(concept);
    if !concept_data.has_concept_data() {
        return concept_reference_linking_data_hash
            .and_then(|hash| hash.get(&concept).copied())
            .filter(|raw| *raw != INVALID);
    }

    let con_proc_data_id = Id::<ConceptProcessData>::new(concept_data.get_concept_data());
    if con_proc_data_id.is_none() || con_proc_data_id.index() >= concept_process_datas.len() {
        return concept_reference_linking_data_hash
            .and_then(|hash| hash.get(&concept).copied())
            .filter(|raw| *raw != INVALID);
    }
    let con_proc_data = concept_process_datas.get(con_proc_data_id);
    if !con_proc_data.is_invalidated_reference_linking() {
        let con_sat_ref_linking_id = con_proc_data.get_concept_reference_linking();
        if con_sat_ref_linking_id.is_some()
            && con_sat_ref_linking_id.index() < concept_reference_linking_datas.len()
        {
            let class_ref_link_data = concept_reference_linking_datas
                .get(con_sat_ref_linking_id)
                .get_classifier_reference_linking_data();
            if class_ref_link_data != INVALID {
                return Some(class_ref_link_data);
            }
        }
    }

    concept_reference_linking_data_hash
        .and_then(|hash| hash.get(&concept).copied())
        .filter(|raw| *raw != INVALID)
}

/// Port of `CClassificationClassSubsumptionMessageData`.
#[derive(Debug, Clone)]
pub struct ClassificationClassSubsumptionMessageData {
    base: ClassificationMessageData,
    subsumed_concept: ConceptId,
    subsumer_list: Option<Vec<ConceptId>>,
}

impl Default for ClassificationClassSubsumptionMessageData {
    fn default() -> Self {
        Self::new()
    }
}

impl ClassificationClassSubsumptionMessageData {
    pub fn new() -> Self {
        Self {
            base: ClassificationMessageData::new(
                ClassificationMessageDataType::TellClassSubsumption,
            ),
            subsumed_concept: ConceptId::NONE,
            subsumer_list: None,
        }
    }

    pub fn init_classification_subsumption_message_data(
        &mut self,
        subsumed_concept: ConceptId,
        subsumer_list: Option<Vec<ConceptId>>,
    ) -> &mut Self {
        self.subsumed_concept = subsumed_concept;
        self.subsumer_list = subsumer_list;
        self
    }

    pub fn get_classification_message_data_type(&self) -> ClassificationMessageDataType {
        self.base.get_classification_message_data_type()
    }

    pub fn get_class_subsumer_list(&self) -> Option<&[ConceptId]> {
        self.subsumer_list.as_deref()
    }

    pub fn get_subsumed_concept(&self) -> ConceptId {
        self.subsumed_concept
    }
}

/// Port of `CClassificationInitializePossibleClassSubsumptionData`.
#[derive(Debug, Clone)]
pub struct ClassificationInitializePossibleClassSubsumptionData {
    possible_subsumer_concept: ConceptId,
    valid: bool,
}

impl ClassificationInitializePossibleClassSubsumptionData {
    pub fn new(possible_subsumer_concept: ConceptId) -> Self {
        Self {
            possible_subsumer_concept,
            valid: true,
        }
    }

    pub fn init_classification_possible_subsumption_data(
        &mut self,
        possible_subsumer_concept: ConceptId,
    ) -> &mut Self {
        self.possible_subsumer_concept = possible_subsumer_concept;
        self.valid = true;
        self
    }

    pub fn get_possible_subsumer_concept(&self) -> ConceptId {
        self.possible_subsumer_concept
    }

    pub fn is_possible_subsumer_valid(&self) -> bool {
        self.valid
    }

    pub fn set_possible_subsumer_invalid(&mut self) -> &mut Self {
        self.valid = false;
        self
    }
}

/// Port of `CClassificationInitializePossibleClassSubsumptionMessageData`.
#[derive(Debug, Clone)]
pub struct ClassificationInitializePossibleClassSubsumptionMessageData {
    base: ClassificationMessageData,
    subsumed_concept: ConceptId,
    possible_subsumer_list: Option<Vec<ClassificationInitializePossibleClassSubsumptionData>>,
    eq_concepts_non_candidate_possible_subsumers: bool,
    eq_concept_non_candidate_possible_subsumer_list: Option<Vec<ConceptId>>,
}

impl Default for ClassificationInitializePossibleClassSubsumptionMessageData {
    fn default() -> Self {
        Self::new()
    }
}

impl ClassificationInitializePossibleClassSubsumptionMessageData {
    pub fn new() -> Self {
        Self {
            base: ClassificationMessageData::new(
                ClassificationMessageDataType::TellClassInitializePossibleSubsumption,
            ),
            subsumed_concept: ConceptId::NONE,
            possible_subsumer_list: None,
            eq_concepts_non_candidate_possible_subsumers: false,
            eq_concept_non_candidate_possible_subsumer_list: None,
        }
    }

    pub fn init_classification_possible_subsumption_message_data(
        &mut self,
        subsumed_concept: ConceptId,
        possible_subsumer_list: Option<Vec<ClassificationInitializePossibleClassSubsumptionData>>,
        eq_concepts_non_candidate_possible_subsumers: bool,
        eq_concept_non_candidate_possible_subsumer_list: Option<Vec<ConceptId>>,
    ) -> &mut Self {
        self.subsumed_concept = subsumed_concept;
        self.possible_subsumer_list = possible_subsumer_list;
        self.eq_concepts_non_candidate_possible_subsumers =
            eq_concepts_non_candidate_possible_subsumers;
        self.eq_concept_non_candidate_possible_subsumer_list =
            eq_concept_non_candidate_possible_subsumer_list;
        self
    }

    pub fn get_classification_message_data_type(&self) -> ClassificationMessageDataType {
        self.base.get_classification_message_data_type()
    }

    pub fn get_class_possible_subsumer_list(
        &self,
    ) -> Option<&[ClassificationInitializePossibleClassSubsumptionData]> {
        self.possible_subsumer_list.as_deref()
    }

    pub fn get_class_eq_concept_non_candidate_possible_subsumer_list(
        &self,
    ) -> Option<&[ConceptId]> {
        self.eq_concept_non_candidate_possible_subsumer_list
            .as_deref()
    }

    pub fn get_subsumed_concept(&self) -> ConceptId {
        self.subsumed_concept
    }

    pub fn has_eq_concepts_non_candidate_poss_subsumers(&self) -> bool {
        self.eq_concepts_non_candidate_possible_subsumers
    }
}

/// Port of `CClassificationUpdatePossibleClassSubsumptionMessageData`.
#[derive(Debug, Clone)]
pub struct ClassificationUpdatePossibleClassSubsumptionMessageData {
    base: ClassificationMessageData,
    subsumed_concept: ConceptId,
}

impl Default for ClassificationUpdatePossibleClassSubsumptionMessageData {
    fn default() -> Self {
        Self::new()
    }
}

impl ClassificationUpdatePossibleClassSubsumptionMessageData {
    pub fn new() -> Self {
        Self {
            base: ClassificationMessageData::new(
                ClassificationMessageDataType::TellClassUpdatePossibleSubsumption,
            ),
            subsumed_concept: ConceptId::NONE,
        }
    }

    pub fn init_classification_possible_subsumption_message_data(
        &mut self,
        subsumed_concept: ConceptId,
    ) -> &mut Self {
        self.subsumed_concept = subsumed_concept;
        self
    }

    pub fn get_classification_message_data_type(&self) -> ClassificationMessageDataType {
        self.base.get_classification_message_data_type()
    }

    pub fn get_subsumed_concept(&self) -> ConceptId {
        self.subsumed_concept
    }
}

/// Port of `CClassificationPseudoModelIdentifierMessageData`.
#[derive(Debug, Clone)]
pub struct ClassificationPseudoModelIdentifierMessageData {
    base: ClassificationMessageData,
    pseudo_model_concept: ConceptId,
    pseudo_model_memory_pools: Cint64,
    pseudo_model_hash: ClassificationClassPseudoModelHash,
}

impl Default for ClassificationPseudoModelIdentifierMessageData {
    fn default() -> Self {
        Self::new()
    }
}

impl ClassificationPseudoModelIdentifierMessageData {
    pub fn new() -> Self {
        Self {
            base: ClassificationMessageData::new(
                ClassificationMessageDataType::TellClassPseudoModelIdentifiers,
            ),
            pseudo_model_concept: ConceptId::NONE,
            pseudo_model_memory_pools: INVALID,
            pseudo_model_hash: ClassificationClassPseudoModelHash::new(),
        }
    }

    pub fn init_classification_pseudo_model_identifier_message_data(
        &mut self,
        pm_concept: ConceptId,
        pm_model_hash: ClassificationClassPseudoModelHash,
        pm_memory_pools: Cint64,
    ) -> &mut Self {
        self.pseudo_model_concept = pm_concept;
        self.pseudo_model_hash = pm_model_hash;
        self.pseudo_model_memory_pools = pm_memory_pools;
        self
    }

    pub fn get_classification_message_data_type(&self) -> ClassificationMessageDataType {
        self.base.get_classification_message_data_type()
    }

    pub fn get_pseudo_model_concept(&self) -> ConceptId {
        self.pseudo_model_concept
    }

    pub fn get_pseudo_model_memory_pools(&self) -> Cint64 {
        self.pseudo_model_memory_pools
    }

    pub fn get_pseudo_model_hash(&self) -> &ClassificationClassPseudoModelHash {
        &self.pseudo_model_hash
    }
}

/// Minimal port of `COptimizedKPSetClassTestingItem` fields needed at the
/// individual-dependence adapter call sites.
#[derive(Debug, Clone)]
pub struct OptimizedKPSetClassTestingItem {
    /// `CConcept* mConceptSat`.
    testing_concept: ConceptId,
    /// The item's `CIndividualDependenceTrackingMarker` base payload.
    individual_dependence_tracking_marker: IndividualDependenceTrackingMarkerId,
    satisfiable_concept_hierarchy_node: Cint64,
    subsuming_concept_item_set: HashSet<OptimizedKPSetClassTestingItemId>,
    subsuming_concept_item_list: Vec<OptimizedKPSetClassTestingItemId>,
    successor_item_list: Vec<OptimizedKPSetClassTestingItemId>,
    pred_counter: Cint64,
    sat_tested_result: bool,
    sat_test_ordered: bool,
    tested_sat: bool,
    unsat_derivated: bool,
    sat_derivated: bool,
    equi_item: bool,
    pred_of_item: bool,
    possible_subsumption_map: Option<OptimizedKPSetClassPossibleSubsumptionMap>,
    poss_subsum_map_initialized: bool,
    propagation_connected: bool,
    pseudo_model: ClassificationClassPseudoModel,
    pseudo_model_initialized: bool,
    up_propagation_item_set: HashSet<OptimizedKPSetClassTestingItemId>,
    down_propagation_item_set: HashSet<OptimizedKPSetClassTestingItemId>,
    possible_subsumed_list: Option<Vec<OptimizedKPSetClassTestingItemId>>,
    possible_subsumed_set: Option<HashSet<OptimizedKPSetClassTestingItemId>>,
    fast_sat_cache_entry: Cint64,
    succ_fast_sat_tested: bool,
}

pub type OptimizedKPSetClassTestingItemId = Id<OptimizedKPSetClassTestingItem>;

/// Minimal port of `COptimizedKPSetRoleTestingItem` fields needed by the
/// ontology classification item state-holder APIs.
#[derive(Debug, Clone)]
pub struct OptimizedKPSetRoleTestingItem {
    /// `CRole* mRoleSat`.
    testing_role: RoleId,
    temporary_marker_concept: ConceptId,
    temporary_propagation_concept: ConceptId,
    temporary_exist_concept: ConceptId,
    satisfiable_role_hierarchy_node: Cint64,
    subsuming_role_item_set: HashSet<OptimizedKPSetRoleTestingItemId>,
    subsuming_role_item_list: Vec<OptimizedKPSetRoleTestingItemId>,
    successor_item_list: Vec<OptimizedKPSetRoleTestingItemId>,
    pred_counter: Cint64,
    sat_tested_result: bool,
    sat_test_ordered: bool,
    tested_sat: bool,
    unsat_derivated: bool,
    sat_derivated: bool,
    equi_item: bool,
    pred_of_item: bool,
    possible_subsumption_map: Option<OptimizedKPSetRolePossibleSubsumptionMap>,
    poss_subsum_map_initialized: bool,
    propagation_connected: bool,
    up_propagation_item_set: HashSet<OptimizedKPSetRoleTestingItemId>,
    down_propagation_item_set: HashSet<OptimizedKPSetRoleTestingItemId>,
    possible_subsumed_list: Option<Vec<OptimizedKPSetRoleTestingItemId>>,
    possible_subsumed_set: Option<HashSet<OptimizedKPSetRoleTestingItemId>>,
}

pub type OptimizedKPSetRoleTestingItemId = Id<OptimizedKPSetRoleTestingItem>;

impl Default for OptimizedKPSetRoleTestingItem {
    fn default() -> Self {
        Self::new()
    }
}

impl OptimizedKPSetRoleTestingItem {
    pub fn new() -> Self {
        Self {
            testing_role: RoleId::NONE,
            temporary_marker_concept: ConceptId::NONE,
            temporary_propagation_concept: ConceptId::NONE,
            temporary_exist_concept: ConceptId::NONE,
            satisfiable_role_hierarchy_node: 0,
            subsuming_role_item_set: HashSet::new(),
            subsuming_role_item_list: Vec::new(),
            successor_item_list: Vec::new(),
            pred_counter: 0,
            sat_tested_result: false,
            sat_test_ordered: false,
            tested_sat: false,
            unsat_derivated: false,
            sat_derivated: false,
            equi_item: false,
            pred_of_item: false,
            possible_subsumption_map: None,
            poss_subsum_map_initialized: false,
            propagation_connected: false,
            up_propagation_item_set: HashSet::new(),
            down_propagation_item_set: HashSet::new(),
            possible_subsumed_list: None,
            possible_subsumed_set: None,
        }
    }

    /// Port of the currently live part of `initSatisfiableTestingItem`.
    pub fn init_satisfiable_testing_item(&mut self, testing_role: RoleId) -> &mut Self {
        self.testing_role = testing_role;
        self.temporary_marker_concept = ConceptId::NONE;
        self.temporary_propagation_concept = ConceptId::NONE;
        self.temporary_exist_concept = ConceptId::NONE;
        self.satisfiable_role_hierarchy_node = 0;
        self.subsuming_role_item_set.clear();
        self.subsuming_role_item_list.clear();
        self.successor_item_list.clear();
        self.pred_counter = 0;
        self.sat_tested_result = false;
        self.sat_test_ordered = false;
        self.tested_sat = false;
        self.unsat_derivated = false;
        self.sat_derivated = false;
        self.equi_item = false;
        self.pred_of_item = false;
        self.possible_subsumption_map = None;
        self.poss_subsum_map_initialized = false;
        self.propagation_connected = false;
        self.up_propagation_item_set.clear();
        self.down_propagation_item_set.clear();
        self.possible_subsumed_list = None;
        self.possible_subsumed_set = None;
        self
    }

    /// Port of `getTestingRole`.
    pub fn get_testing_role(&self) -> RoleId {
        self.testing_role
    }

    pub fn get_temporary_marker_concept(&self) -> ConceptId {
        self.temporary_marker_concept
    }

    pub fn get_temporary_propagation_concept(&self) -> ConceptId {
        self.temporary_propagation_concept
    }

    pub fn get_temporary_exist_concept(&self) -> ConceptId {
        self.temporary_exist_concept
    }

    pub fn set_temporary_marker_concept(&mut self, marker_concept: ConceptId) -> &mut Self {
        self.temporary_marker_concept = marker_concept;
        self
    }

    pub fn set_temporary_propagation_concept(&mut self, prop_concept: ConceptId) -> &mut Self {
        self.temporary_propagation_concept = prop_concept;
        self
    }

    pub fn set_temporary_exist_concept(&mut self, exist_concept: ConceptId) -> &mut Self {
        self.temporary_exist_concept = exist_concept;
        self
    }

    pub fn get_satisfiable_role_hierarchy_node(&self) -> Cint64 {
        self.satisfiable_role_hierarchy_node
    }

    pub fn set_satisfiable_role_hierarchy_node(&mut self, hier_node: Cint64) -> &mut Self {
        self.satisfiable_role_hierarchy_node = hier_node;
        self
    }

    pub fn get_subsumer_role_item_set(&self) -> &HashSet<OptimizedKPSetRoleTestingItemId> {
        &self.subsuming_role_item_set
    }

    pub fn get_subsumer_role_item_list(&self) -> &[OptimizedKPSetRoleTestingItemId] {
        &self.subsuming_role_item_list
    }

    pub fn get_subsumer_role_item_count(&self) -> Cint64 {
        self.subsuming_role_item_set.len() as Cint64
    }

    pub fn has_subsumer_role_item(&self, item: OptimizedKPSetRoleTestingItemId) -> bool {
        self.subsuming_role_item_set.contains(&item)
    }

    pub fn get_successor_item_list(&self) -> &[OptimizedKPSetRoleTestingItemId] {
        &self.successor_item_list
    }

    pub fn get_unprocessed_predecessor_item_count(&self) -> Cint64 {
        self.pred_counter
    }

    pub fn has_only_processed_predecessor_items(&self) -> bool {
        self.pred_counter <= 0
    }

    pub fn dec_unprocessed_predecessor_items(&mut self, dec_count: Cint64) -> &mut Self {
        self.pred_counter -= dec_count;
        self
    }

    pub fn inc_unprocessed_predecessor_items(&mut self, inc_count: Cint64) -> &mut Self {
        self.pred_counter += inc_count;
        self
    }

    pub fn set_unprocessed_predecessor_items(&mut self, pred_count: Cint64) -> &mut Self {
        self.pred_counter = pred_count;
        self
    }

    pub fn add_successor_satisfiable_test_item(
        &mut self,
        succ_item: OptimizedKPSetRoleTestingItemId,
    ) -> &mut Self {
        self.successor_item_list.push(succ_item);
        self
    }

    pub fn is_satisfiable_test_ordered(&self) -> bool {
        self.sat_test_ordered
    }

    pub fn is_satisfiable_tested(&self) -> bool {
        self.tested_sat
    }

    pub fn is_result_unsatisfiable_derivated(&self) -> bool {
        self.unsat_derivated
    }

    pub fn is_result_satisfiable_derivated(&self) -> bool {
        self.sat_derivated
    }

    pub fn get_satisfiable_tested_result(&self) -> bool {
        self.sat_tested_result
    }

    pub fn set_satisfiable_test_ordered(&mut self, sat_test_ordered: bool) -> &mut Self {
        self.sat_test_ordered = sat_test_ordered;
        self
    }

    pub fn set_satisfiable_tested(&mut self, sat_tested: bool) -> &mut Self {
        self.tested_sat = sat_tested;
        self
    }

    pub fn set_satisfiable_tested_result(&mut self, sat_tested_result: bool) -> &mut Self {
        self.sat_tested_result = sat_tested_result;
        self
    }

    pub fn set_result_unsatisfiable_derivated(&mut self, unsat_derivated: bool) -> &mut Self {
        self.unsat_derivated = unsat_derivated;
        self
    }

    pub fn set_result_satisfiable_derivated(&mut self, sat_derivated: bool) -> &mut Self {
        self.sat_derivated = sat_derivated;
        self
    }

    pub fn add_subsumer_role_item(
        &mut self,
        subsuming_item: OptimizedKPSetRoleTestingItemId,
    ) -> &mut Self {
        if self.subsuming_role_item_set.insert(subsuming_item) {
            self.subsuming_role_item_list.push(subsuming_item);
        }
        self
    }

    /// Port of `COptimizedKPSetRoleTestingItem::tellConceptSupsumption`.
    pub fn tell_concept_supsumption(
        &mut self,
        _subsumed_concept: ConceptId,
        subsumer_concept: ConceptId,
        concepts: &Arena<Concept>,
        concept_process_datas: &Arena<ConceptProcessData>,
        concept_reference_linking_datas: &Arena<ConceptSaturationReferenceLinkingData>,
    ) -> &mut Self {
        if subsumer_concept.is_none() || subsumer_concept.index() >= concepts.len() {
            return self;
        }
        let subsumer_concept_data = concepts.get(subsumer_concept);
        if subsumer_concept_data.get_operator_code() == CCTOP
            || !subsumer_concept_data.has_concept_data()
        {
            return self;
        }

        let con_pro_data_id =
            Id::<ConceptProcessData>::new(subsumer_concept_data.get_concept_data());
        if con_pro_data_id.is_none() || con_pro_data_id.index() >= concept_process_datas.len() {
            return self;
        }
        let con_pro_data = concept_process_datas.get(con_pro_data_id);
        let con_sat_ref_linking_id = con_pro_data.get_concept_reference_linking();
        if con_sat_ref_linking_id.is_some()
            && con_sat_ref_linking_id.index() < concept_reference_linking_datas.len()
        {
            let con_sat_ref_linking = concept_reference_linking_datas.get(con_sat_ref_linking_id);
            let subsumer_role_item = OptimizedKPSetRoleTestingItemId::new(
                con_sat_ref_linking.get_classifier_reference_linking_data(),
            );
            if subsumer_role_item.is_some() {
                self.add_subsumer_role_item(subsumer_role_item);
            }
        }
        self
    }

    pub fn sort_subsuming_concept_item_list(
        &mut self,
        items: &[OptimizedKPSetRoleTestingItem],
    ) -> &[OptimizedKPSetRoleTestingItemId] {
        self.subsuming_role_item_list.sort_by(|item1, item2| {
            let count1 = items[item1.index()].get_subsumer_role_item_count();
            let count2 = items[item2.index()].get_subsumer_role_item_count();
            count2.cmp(&count1)
        });
        &self.subsuming_role_item_list
    }

    pub fn is_equivalent_item(&self) -> bool {
        self.equi_item
    }

    pub fn set_equivalent_item(&mut self, equivalent: bool) -> &mut Self {
        self.equi_item = equivalent;
        self
    }

    pub fn is_predecessor_item(&self) -> bool {
        self.pred_of_item
    }

    pub fn set_predecessor_item(&mut self, is_predecessor_of_one_item: bool) -> &mut Self {
        self.pred_of_item = is_predecessor_of_one_item;
        self
    }

    pub fn is_more_concept_classification_information_required(&self) -> bool {
        !(self.sat_test_ordered || self.tested_sat || self.unsat_derivated || self.sat_derivated)
    }

    pub fn get_possible_subsumption_map(
        &mut self,
        create: bool,
    ) -> Option<&mut OptimizedKPSetRolePossibleSubsumptionMap> {
        if self.possible_subsumption_map.is_none() && create {
            self.possible_subsumption_map = Some(OptimizedKPSetRolePossibleSubsumptionMap::new());
        }
        self.possible_subsumption_map.as_mut()
    }

    pub fn get_possible_subsumption_map_ref(
        &self,
    ) -> Option<&OptimizedKPSetRolePossibleSubsumptionMap> {
        self.possible_subsumption_map.as_ref()
    }

    pub fn has_property_possible_subsumption_map(&self) -> bool {
        self.possible_subsumption_map.is_some()
    }

    pub fn get_up_propagation_item_set(&self) -> &HashSet<OptimizedKPSetRoleTestingItemId> {
        &self.up_propagation_item_set
    }

    pub fn get_down_propagation_item_set(&self) -> &HashSet<OptimizedKPSetRoleTestingItemId> {
        &self.down_propagation_item_set
    }

    pub fn add_up_propagation_item(&mut self, item: OptimizedKPSetRoleTestingItemId) -> &mut Self {
        self.up_propagation_item_set.insert(item);
        self
    }

    pub fn add_down_propagation_item(
        &mut self,
        item: OptimizedKPSetRoleTestingItemId,
    ) -> &mut Self {
        self.down_propagation_item_set.insert(item);
        self
    }

    pub fn is_possible_subsumption_map_initialized(&self) -> bool {
        self.poss_subsum_map_initialized
    }

    pub fn set_possible_subsumption_map_initialized(&mut self, initialized: bool) -> &mut Self {
        self.poss_subsum_map_initialized = initialized;
        self
    }

    pub fn is_propagation_connected(&self) -> bool {
        self.propagation_connected
    }

    pub fn set_propagation_connected(&mut self, connected: bool) -> &mut Self {
        self.propagation_connected = connected;
        self
    }

    pub fn get_possible_subsumer_set(
        &mut self,
        create: bool,
    ) -> Option<&mut HashSet<OptimizedKPSetRoleTestingItemId>> {
        if self.possible_subsumed_set.is_none() && create {
            self.possible_subsumed_set = Some(HashSet::new());
        }
        self.possible_subsumed_set.as_mut()
    }

    pub fn get_possible_subsumer_set_ref(
        &self,
    ) -> Option<&HashSet<OptimizedKPSetRoleTestingItemId>> {
        self.possible_subsumed_set.as_ref()
    }

    pub fn get_possible_subsumer_list(&self) -> Option<&[OptimizedKPSetRoleTestingItemId]> {
        self.possible_subsumed_list.as_deref()
    }

    pub fn set_possible_subsumed_list(
        &mut self,
        poss_subsumed_list: Vec<OptimizedKPSetRoleTestingItemId>,
    ) -> &mut Self {
        self.possible_subsumed_list = Some(poss_subsumed_list);
        self
    }

    pub fn has_remaining_possible_subsumed_items(&self) -> bool {
        self.possible_subsumed_list
            .as_ref()
            .map(|list| !list.is_empty())
            .unwrap_or(false)
    }
}

/// Port of `COptimizedKPSetClassPossibleSubsumptionData`.
#[derive(Debug, Clone)]
pub struct OptimizedKPSetClassPossibleSubsumptionData {
    subsumption_updated_flag: bool,
    subsumption_confirmed_flag: bool,
    subsumption_invalid_flag: bool,
    class_item: OptimizedKPSetClassTestingItemId,
}

impl OptimizedKPSetClassPossibleSubsumptionData {
    pub fn new(item: OptimizedKPSetClassTestingItemId) -> Self {
        Self {
            subsumption_updated_flag: false,
            subsumption_confirmed_flag: false,
            subsumption_invalid_flag: false,
            class_item: item,
        }
    }

    pub fn is_update_required(&self) -> bool {
        !self.subsumption_updated_flag
            && (self.subsumption_confirmed_flag || self.subsumption_invalid_flag)
    }

    pub fn is_subsumption_updated(&self) -> bool {
        self.subsumption_updated_flag
    }

    pub fn set_subsumption_updated(&mut self, updated: bool) -> &mut Self {
        self.subsumption_updated_flag = updated;
        self
    }

    pub fn is_subsumption_confirmed(&self) -> bool {
        self.subsumption_confirmed_flag
    }

    pub fn set_subsumption_confirmed(&mut self, confirmed_subsumption: bool) -> &mut Self {
        self.subsumption_confirmed_flag = confirmed_subsumption;
        self
    }

    pub fn is_subsumption_invalided(&self) -> bool {
        self.subsumption_invalid_flag
    }

    pub fn set_subsumption_invalid(&mut self, invalid_subsumption: bool) -> &mut Self {
        self.subsumption_invalid_flag = invalid_subsumption;
        self
    }

    pub fn is_subsumption_known(&self) -> bool {
        self.subsumption_invalid_flag || self.subsumption_confirmed_flag
    }

    pub fn is_subsumption_unknown(&self) -> bool {
        !self.subsumption_confirmed_flag && !self.subsumption_invalid_flag
    }

    pub fn get_class_item(&self) -> OptimizedKPSetClassTestingItemId {
        self.class_item
    }

    pub fn set_class_item(&mut self, item: OptimizedKPSetClassTestingItemId) -> &mut Self {
        self.class_item = item;
        self
    }
}

/// Port of `COptimizedKPSetRolePossibleSubsumptionData`.
#[derive(Debug, Clone)]
pub struct OptimizedKPSetRolePossibleSubsumptionData {
    subsumption_updated_flag: bool,
    subsumption_confirmed_flag: bool,
    subsumption_invalid_flag: bool,
    testing_item: OptimizedKPSetRoleTestingItemId,
}

impl OptimizedKPSetRolePossibleSubsumptionData {
    pub fn new(item: OptimizedKPSetRoleTestingItemId) -> Self {
        Self {
            subsumption_updated_flag: false,
            subsumption_confirmed_flag: false,
            subsumption_invalid_flag: false,
            testing_item: item,
        }
    }

    pub fn is_update_required(&self) -> bool {
        !self.subsumption_updated_flag
            && (self.subsumption_confirmed_flag || self.subsumption_invalid_flag)
    }

    pub fn is_subsumption_updated(&self) -> bool {
        self.subsumption_updated_flag
    }

    pub fn set_subsumption_updated(&mut self, updated: bool) -> &mut Self {
        self.subsumption_updated_flag = updated;
        self
    }

    pub fn is_subsumption_confirmed(&self) -> bool {
        self.subsumption_confirmed_flag
    }

    pub fn set_subsumption_confirmed(&mut self, confirmed_subsumption: bool) -> &mut Self {
        self.subsumption_confirmed_flag = confirmed_subsumption;
        self
    }

    pub fn is_subsumption_invalided(&self) -> bool {
        self.subsumption_invalid_flag
    }

    pub fn set_subsumption_invalid(&mut self, invalid_subsumption: bool) -> &mut Self {
        self.subsumption_invalid_flag = invalid_subsumption;
        self
    }

    pub fn is_subsumption_known(&self) -> bool {
        self.subsumption_invalid_flag || self.subsumption_confirmed_flag
    }

    pub fn is_subsumption_unknown(&self) -> bool {
        !self.subsumption_confirmed_flag && !self.subsumption_invalid_flag
    }

    pub fn get_testing_item(&self) -> OptimizedKPSetRoleTestingItemId {
        self.testing_item
    }

    pub fn set_testing_item(&mut self, item: OptimizedKPSetRoleTestingItemId) -> &mut Self {
        self.testing_item = item;
        self
    }
}

/// Port of `COptimizedKPSetClassPossibleSubsumptionMap`.
#[derive(Debug, Clone)]
pub struct OptimizedKPSetClassPossibleSubsumptionMap {
    require_possible_subsumption_update: bool,
    remaining_possible_subsumption_count: Cint64,
    data: BTreeMap<Cint64, (ConceptId, OptimizedKPSetClassPossibleSubsumptionData)>,
}

impl Default for OptimizedKPSetClassPossibleSubsumptionMap {
    fn default() -> Self {
        Self::new()
    }
}

impl OptimizedKPSetClassPossibleSubsumptionMap {
    pub fn new() -> Self {
        Self {
            require_possible_subsumption_update: false,
            remaining_possible_subsumption_count: 0,
            data: BTreeMap::new(),
        }
    }

    pub fn insert(
        &mut self,
        concept: ConceptId,
        data: OptimizedKPSetClassPossibleSubsumptionData,
    ) -> Option<OptimizedKPSetClassPossibleSubsumptionData> {
        self.data
            .insert(concept.raw, (concept, data))
            .map(|(_, data)| data)
    }

    pub fn get(&self, concept: ConceptId) -> Option<&OptimizedKPSetClassPossibleSubsumptionData> {
        self.data.get(&concept.raw).map(|(_, data)| data)
    }

    pub fn contains(&self, concept: ConceptId) -> bool {
        self.data.contains_key(&concept.raw)
    }

    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }

    pub fn get_mut(
        &mut self,
        concept: ConceptId,
    ) -> Option<&mut OptimizedKPSetClassPossibleSubsumptionData> {
        self.data.get_mut(&concept.raw).map(|(_, data)| data)
    }

    pub fn is_possible_subsumption_update_required(&self) -> bool {
        self.require_possible_subsumption_update
    }

    pub fn get_remaining_possible_subsumption_count(&self) -> Cint64 {
        self.remaining_possible_subsumption_count
    }

    pub fn set_remaining_possible_subsumption_count(
        &mut self,
        poss_subsum_count: Cint64,
    ) -> &mut Self {
        self.remaining_possible_subsumption_count = poss_subsum_count;
        self
    }

    pub fn dec_remaining_possible_subsumption_count(&mut self, dec_count: Cint64) -> &mut Self {
        self.remaining_possible_subsumption_count -= dec_count;
        self
    }

    pub fn inc_remaining_possible_subsumption_count(&mut self, inc_count: Cint64) -> &mut Self {
        self.remaining_possible_subsumption_count += inc_count;
        self
    }

    pub fn set_possible_subsumption_update_required(&mut self, required_update: bool) -> &mut Self {
        self.require_possible_subsumption_update = required_update;
        self
    }

    pub fn has_remaining_possible_subsumptions(&self) -> bool {
        self.remaining_possible_subsumption_count > 0
    }

    pub fn get_iterator(&mut self) -> OptimizedKPSetClassPossibleSubsumptionMapIterator<'_> {
        OptimizedKPSetClassPossibleSubsumptionMapIterator::new(self)
    }

    pub fn update_required_concepts(&self) -> Vec<ConceptId> {
        self.data
            .values()
            .filter_map(|(concept, data)| data.is_update_required().then_some(*concept))
            .collect()
    }

    pub fn concepts(&self) -> Vec<ConceptId> {
        self.data.values().map(|(concept, _)| *concept).collect()
    }
}

/// Port of `COptimizedKPSetRolePossibleSubsumptionMap`.
#[derive(Debug, Clone)]
pub struct OptimizedKPSetRolePossibleSubsumptionMap {
    require_possible_subsumption_update: bool,
    remaining_possible_subsumption_count: Cint64,
    data: BTreeMap<Cint64, (RoleId, OptimizedKPSetRolePossibleSubsumptionData)>,
}

impl Default for OptimizedKPSetRolePossibleSubsumptionMap {
    fn default() -> Self {
        Self::new()
    }
}

impl OptimizedKPSetRolePossibleSubsumptionMap {
    pub fn new() -> Self {
        Self {
            require_possible_subsumption_update: false,
            remaining_possible_subsumption_count: 0,
            data: BTreeMap::new(),
        }
    }

    pub fn insert(
        &mut self,
        role: RoleId,
        data: OptimizedKPSetRolePossibleSubsumptionData,
    ) -> Option<OptimizedKPSetRolePossibleSubsumptionData> {
        self.data
            .insert(role.raw, (role, data))
            .map(|(_, data)| data)
    }

    pub fn get(&self, role: RoleId) -> Option<&OptimizedKPSetRolePossibleSubsumptionData> {
        self.data.get(&role.raw).map(|(_, data)| data)
    }

    pub fn get_mut(
        &mut self,
        role: RoleId,
    ) -> Option<&mut OptimizedKPSetRolePossibleSubsumptionData> {
        self.data.get_mut(&role.raw).map(|(_, data)| data)
    }

    pub fn contains(&self, role: RoleId) -> bool {
        self.data.contains_key(&role.raw)
    }

    pub fn is_possible_subsumption_update_required(&self) -> bool {
        self.require_possible_subsumption_update
    }

    pub fn get_remaining_possible_subsumption_count(&self) -> Cint64 {
        self.remaining_possible_subsumption_count
    }

    pub fn set_remaining_possible_subsumption_count(
        &mut self,
        poss_subsum_count: Cint64,
    ) -> &mut Self {
        self.remaining_possible_subsumption_count = poss_subsum_count;
        self
    }

    pub fn dec_remaining_possible_subsumption_count(&mut self, dec_count: Cint64) -> &mut Self {
        self.remaining_possible_subsumption_count -= dec_count;
        self
    }

    pub fn inc_remaining_possible_subsumption_count(&mut self, inc_count: Cint64) -> &mut Self {
        self.remaining_possible_subsumption_count += inc_count;
        self
    }

    pub fn set_possible_subsumption_update_required(&mut self, required_update: bool) -> &mut Self {
        self.require_possible_subsumption_update = required_update;
        self
    }

    pub fn has_remaining_possible_subsumptions(&self) -> bool {
        self.remaining_possible_subsumption_count > 0
    }

    pub fn get_iterator(&mut self) -> OptimizedKPSetRolePossibleSubsumptionMapIterator<'_> {
        OptimizedKPSetRolePossibleSubsumptionMapIterator::new(self)
    }
}

/// Port of `COptimizedKPSetClassPossibleSubsumptionMapIterator`.
pub struct OptimizedKPSetClassPossibleSubsumptionMapIterator<'a> {
    map: &'a mut OptimizedKPSetClassPossibleSubsumptionMap,
    keys: Vec<Cint64>,
    index: usize,
}

impl<'a> OptimizedKPSetClassPossibleSubsumptionMapIterator<'a> {
    fn new(map: &'a mut OptimizedKPSetClassPossibleSubsumptionMap) -> Self {
        let keys = map.data.keys().copied().collect();
        Self {
            map,
            keys,
            index: 0,
        }
    }

    pub fn has_next(&self) -> bool {
        self.index < self.keys.len()
    }

    fn current(&self) -> &(ConceptId, OptimizedKPSetClassPossibleSubsumptionData) {
        self.map
            .data
            .get(&self.keys[self.index])
            .expect("possible-subsumption iterator key must exist")
    }

    fn current_mut(&mut self) -> &mut (ConceptId, OptimizedKPSetClassPossibleSubsumptionData) {
        self.map
            .data
            .get_mut(&self.keys[self.index])
            .expect("possible-subsumption iterator key must exist")
    }

    pub fn is_subsumption_confirmed(&self) -> bool {
        self.current().1.is_subsumption_confirmed()
    }

    pub fn is_subsumption_invalided(&self) -> bool {
        self.current().1.is_subsumption_invalided()
    }

    pub fn is_update_required(&self) -> bool {
        self.current().1.is_update_required()
    }

    pub fn get_subsumption_concept(&self) -> ConceptId {
        self.current().0
    }

    pub fn invalidate_subsumption(&mut self) -> bool {
        let was_invalid = self.is_subsumption_invalided();
        self.current_mut().1.set_subsumption_invalid(true);
        was_invalid
    }

    pub fn confirm_subsumption(&mut self) -> bool {
        let was_confirmed = self.is_subsumption_confirmed();
        self.current_mut().1.set_subsumption_confirmed(true);
        was_confirmed
    }

    pub fn move_next(&mut self) -> bool {
        self.index += 1;
        true
    }
}

/// Port of `COptimizedKPSetRolePossibleSubsumptionMapIterator`.
pub struct OptimizedKPSetRolePossibleSubsumptionMapIterator<'a> {
    map: &'a mut OptimizedKPSetRolePossibleSubsumptionMap,
    keys: Vec<Cint64>,
    index: usize,
}

impl<'a> OptimizedKPSetRolePossibleSubsumptionMapIterator<'a> {
    fn new(map: &'a mut OptimizedKPSetRolePossibleSubsumptionMap) -> Self {
        let keys = map.data.keys().copied().collect();
        Self {
            map,
            keys,
            index: 0,
        }
    }

    pub fn has_next(&self) -> bool {
        self.index < self.keys.len()
    }

    fn current(&self) -> &(RoleId, OptimizedKPSetRolePossibleSubsumptionData) {
        self.map
            .data
            .get(&self.keys[self.index])
            .expect("possible-subsumption iterator key must exist")
    }

    fn current_mut(&mut self) -> &mut (RoleId, OptimizedKPSetRolePossibleSubsumptionData) {
        self.map
            .data
            .get_mut(&self.keys[self.index])
            .expect("possible-subsumption iterator key must exist")
    }

    pub fn is_subsumption_confirmed(&self) -> bool {
        self.current().1.is_subsumption_confirmed()
    }

    pub fn is_subsumption_invalided(&self) -> bool {
        self.current().1.is_subsumption_invalided()
    }

    pub fn get_subsumption_role(&self) -> RoleId {
        self.current().0
    }

    pub fn invalidate_subsumption(&mut self) -> bool {
        let was_invalid = self.is_subsumption_invalided();
        self.current_mut().1.set_subsumption_invalid(true);
        was_invalid
    }

    pub fn confirm_subsumption(&mut self) -> bool {
        let was_confirmed = self.is_subsumption_confirmed();
        self.current_mut().1.set_subsumption_confirmed(true);
        was_confirmed
    }

    pub fn move_next(&mut self) -> bool {
        self.index += 1;
        true
    }
}

impl Default for OptimizedKPSetClassTestingItem {
    fn default() -> Self {
        Self::new()
    }
}

impl OptimizedKPSetClassTestingItem {
    /// Constructor-side shell; `initKPSetClassTestingItem` installs the concept
    /// and C++ resets `mIndiDepTracked` to false.
    pub fn new() -> Self {
        Self {
            testing_concept: ConceptId::NONE,
            individual_dependence_tracking_marker: IndividualDependenceTrackingMarkerId::NONE,
            satisfiable_concept_hierarchy_node: 0,
            subsuming_concept_item_set: HashSet::new(),
            subsuming_concept_item_list: Vec::new(),
            successor_item_list: Vec::new(),
            pred_counter: 0,
            sat_tested_result: false,
            sat_test_ordered: false,
            tested_sat: false,
            unsat_derivated: false,
            sat_derivated: false,
            equi_item: false,
            pred_of_item: false,
            possible_subsumption_map: None,
            poss_subsum_map_initialized: false,
            propagation_connected: false,
            pseudo_model: ClassificationClassPseudoModel::new(),
            pseudo_model_initialized: false,
            up_propagation_item_set: HashSet::new(),
            down_propagation_item_set: HashSet::new(),
            possible_subsumed_list: None,
            possible_subsumed_set: None,
            fast_sat_cache_entry: 0,
            succ_fast_sat_tested: false,
        }
    }

    /// Port of the currently live part of `initKPSetClassTestingItem`.
    pub fn init_kpset_class_testing_item(
        &mut self,
        testing_concept: ConceptId,
        marker: IndividualDependenceTrackingMarkerId,
    ) -> &mut Self {
        self.testing_concept = testing_concept;
        self.individual_dependence_tracking_marker = marker;
        self.satisfiable_concept_hierarchy_node = 0;
        self.subsuming_concept_item_set.clear();
        self.subsuming_concept_item_list.clear();
        self.successor_item_list.clear();
        self.pred_counter = 0;
        self.sat_tested_result = false;
        self.sat_test_ordered = false;
        self.tested_sat = false;
        self.unsat_derivated = false;
        self.sat_derivated = false;
        self.equi_item = false;
        self.pred_of_item = false;
        self.possible_subsumption_map = None;
        self.poss_subsum_map_initialized = false;
        self.propagation_connected = false;
        self.pseudo_model_initialized = false;
        self.up_propagation_item_set.clear();
        self.down_propagation_item_set.clear();
        self.possible_subsumed_list = None;
        self.possible_subsumed_set = None;
        self.fast_sat_cache_entry = 0;
        self.succ_fast_sat_tested = false;
        self
    }

    /// Port of `getTestingConcept`.
    pub fn get_testing_concept(&self) -> ConceptId {
        self.testing_concept
    }

    pub fn get_satisfiable_concept_hierarchy_node(&self) -> Cint64 {
        self.satisfiable_concept_hierarchy_node
    }

    pub fn set_satisfiable_concept_hierarchy_node(&mut self, hier_node: Cint64) -> &mut Self {
        self.satisfiable_concept_hierarchy_node = hier_node;
        self
    }

    pub fn get_subsuming_concept_item_set(&self) -> &HashSet<OptimizedKPSetClassTestingItemId> {
        &self.subsuming_concept_item_set
    }

    pub fn get_subsuming_concept_item_list(&self) -> &[OptimizedKPSetClassTestingItemId] {
        &self.subsuming_concept_item_list
    }

    pub fn get_subsuming_concept_item_count(&self) -> Cint64 {
        self.subsuming_concept_item_set.len() as Cint64
    }

    pub fn has_subsumer_concept_item(&self, item: OptimizedKPSetClassTestingItemId) -> bool {
        self.subsuming_concept_item_set.contains(&item)
    }

    pub fn get_successor_item_list(&self) -> &[OptimizedKPSetClassTestingItemId] {
        &self.successor_item_list
    }

    pub fn get_unprocessed_predecessor_item_count(&self) -> Cint64 {
        self.pred_counter
    }

    pub fn has_only_processed_predecessor_items(&self) -> bool {
        self.pred_counter <= 0
    }

    pub fn dec_unprocessed_predecessor_items(&mut self, dec_count: Cint64) -> &mut Self {
        self.pred_counter -= dec_count;
        self
    }

    pub fn inc_unprocessed_predecessor_items(&mut self, inc_count: Cint64) -> &mut Self {
        self.pred_counter += inc_count;
        self
    }

    pub fn set_unprocessed_predecessor_items(&mut self, pred_count: Cint64) -> &mut Self {
        self.pred_counter = pred_count;
        self
    }

    pub fn add_successor_satisfiable_test_item(
        &mut self,
        succ_item: OptimizedKPSetClassTestingItemId,
    ) -> &mut Self {
        self.successor_item_list.push(succ_item);
        self
    }

    pub fn is_satisfiable_test_ordered(&self) -> bool {
        self.sat_test_ordered
    }

    pub fn is_satisfiable_tested(&self) -> bool {
        self.tested_sat
    }

    pub fn is_result_unsatisfiable_derivated(&self) -> bool {
        self.unsat_derivated
    }

    pub fn is_result_satisfiable_derivated(&self) -> bool {
        self.sat_derivated
    }

    pub fn get_satisfiable_tested_result(&self) -> bool {
        self.sat_tested_result
    }

    pub fn set_satisfiable_test_ordered(&mut self, sat_test_ordered: bool) -> &mut Self {
        self.sat_test_ordered = sat_test_ordered;
        self
    }

    pub fn set_satisfiable_tested(&mut self, sat_tested: bool) -> &mut Self {
        self.tested_sat = sat_tested;
        self
    }

    pub fn set_satisfiable_tested_result(&mut self, sat_tested_result: bool) -> &mut Self {
        self.sat_tested_result = sat_tested_result;
        self
    }

    pub fn set_result_unsatisfiable_derivated(&mut self, unsat_derivated: bool) -> &mut Self {
        self.unsat_derivated = unsat_derivated;
        self
    }

    pub fn set_result_satisfiable_derivated(&mut self, sat_derivated: bool) -> &mut Self {
        self.sat_derivated = sat_derivated;
        self
    }

    pub fn add_subsuming_concept_item(
        &mut self,
        subsuming_item: OptimizedKPSetClassTestingItemId,
    ) -> &mut Self {
        if self.subsuming_concept_item_set.insert(subsuming_item) {
            self.subsuming_concept_item_list.push(subsuming_item);
        }
        self
    }

    /// Port of `COptimizedKPSetClassTestingItem::tellConceptSupsumption`.
    pub fn tell_concept_supsumption(
        &mut self,
        _subsumed_concept: ConceptId,
        subsumer_concept: ConceptId,
        concepts: &Arena<Concept>,
        concept_process_datas: &Arena<ConceptProcessData>,
        concept_reference_linking_datas: &Arena<ConceptSaturationReferenceLinkingData>,
        concept_reference_linking_data_hash: Option<&HashMap<ConceptId, Cint64>>,
    ) -> &mut Self {
        if subsumer_concept.is_none() || subsumer_concept.index() >= concepts.len() {
            return self;
        }
        let subsumer_concept_data = concepts.get(subsumer_concept);
        if subsumer_concept_data.get_operator_code() == CCTOP
            || !subsumer_concept_data.has_concept_data()
        {
            return self;
        }

        let con_pro_data_id =
            Id::<ConceptProcessData>::new(subsumer_concept_data.get_concept_data());
        if con_pro_data_id.is_none() || con_pro_data_id.index() >= concept_process_datas.len() {
            return self;
        }
        let con_pro_data = concept_process_datas.get(con_pro_data_id);

        if !con_pro_data.is_invalidated_reference_linking() {
            let con_sat_ref_linking_id = con_pro_data.get_concept_reference_linking();
            if con_sat_ref_linking_id.is_some()
                && con_sat_ref_linking_id.index() < concept_reference_linking_datas.len()
            {
                let con_sat_ref_linking =
                    concept_reference_linking_datas.get(con_sat_ref_linking_id);
                let subsumer_class_item = OptimizedKPSetClassTestingItemId::new(
                    con_sat_ref_linking.get_classifier_reference_linking_data(),
                );
                if subsumer_class_item.is_some() {
                    self.add_subsuming_concept_item(subsumer_class_item);
                }
            }
        } else if let Some(con_ref_link_data_hash) = concept_reference_linking_data_hash {
            if let Some(subsumer_class_item_raw) = con_ref_link_data_hash.get(&subsumer_concept) {
                let subsumer_class_item =
                    OptimizedKPSetClassTestingItemId::new(*subsumer_class_item_raw);
                if subsumer_class_item.is_some() {
                    self.add_subsuming_concept_item(subsumer_class_item);
                }
            }
        }

        self
    }

    pub fn sort_subsuming_concept_item_list(
        &mut self,
        items: &[OptimizedKPSetClassTestingItem],
    ) -> &[OptimizedKPSetClassTestingItemId] {
        self.subsuming_concept_item_list.sort_by(|item1, item2| {
            let count1 = items[item1.index()].get_subsuming_concept_item_count();
            let count2 = items[item2.index()].get_subsuming_concept_item_count();
            count2.cmp(&count1)
        });
        &self.subsuming_concept_item_list
    }

    pub fn is_equivalent_item(&self) -> bool {
        self.equi_item
    }

    pub fn set_equivalent_item(&mut self, equivalent: bool) -> &mut Self {
        self.equi_item = equivalent;
        self
    }

    pub fn is_predecessor_item(&self) -> bool {
        self.pred_of_item
    }

    pub fn set_predecessor_item(&mut self, is_predecessor_of_one_item: bool) -> &mut Self {
        self.pred_of_item = is_predecessor_of_one_item;
        self
    }

    pub fn is_more_concept_classification_information_required(&self) -> bool {
        !(self.sat_test_ordered || self.tested_sat || self.unsat_derivated || self.sat_derivated)
    }

    pub fn get_possible_subsumption_map(
        &mut self,
        create: bool,
    ) -> Option<&mut OptimizedKPSetClassPossibleSubsumptionMap> {
        if self.possible_subsumption_map.is_none() && create {
            self.possible_subsumption_map = Some(OptimizedKPSetClassPossibleSubsumptionMap::new());
        }
        self.possible_subsumption_map.as_mut()
    }

    pub fn has_class_possible_subsumption_map(&self) -> bool {
        self.possible_subsumption_map.is_some()
    }

    pub fn get_possible_subsumption_map_ref(
        &self,
    ) -> Option<&OptimizedKPSetClassPossibleSubsumptionMap> {
        self.possible_subsumption_map.as_ref()
    }

    pub fn get_up_propagation_item_set(&self) -> &HashSet<OptimizedKPSetClassTestingItemId> {
        &self.up_propagation_item_set
    }

    pub fn get_down_propagation_item_set(&self) -> &HashSet<OptimizedKPSetClassTestingItemId> {
        &self.down_propagation_item_set
    }

    pub fn add_up_propagation_item(&mut self, item: OptimizedKPSetClassTestingItemId) -> &mut Self {
        self.up_propagation_item_set.insert(item);
        self
    }

    pub fn add_down_propagation_item(
        &mut self,
        item: OptimizedKPSetClassTestingItemId,
    ) -> &mut Self {
        self.down_propagation_item_set.insert(item);
        self
    }

    pub fn is_possible_subsumption_map_initialized(&self) -> bool {
        self.poss_subsum_map_initialized
    }

    pub fn set_possible_subsumption_map_initialized(&mut self, initialized: bool) -> &mut Self {
        self.poss_subsum_map_initialized = initialized;
        self
    }

    pub fn is_propagation_connected(&self) -> bool {
        self.propagation_connected
    }

    pub fn set_propagation_connected(&mut self, connected: bool) -> &mut Self {
        self.propagation_connected = connected;
        self
    }

    pub fn is_class_pseudo_model_initalized(&self) -> bool {
        self.pseudo_model_initialized
    }

    pub fn set_class_pseudo_model_initalized(&mut self, initialized: bool) -> &mut Self {
        self.pseudo_model_initialized = initialized;
        self
    }

    pub fn get_class_pseudo_model(&self) -> &ClassificationClassPseudoModel {
        &self.pseudo_model
    }

    pub fn get_class_pseudo_model_mut(&mut self) -> &mut ClassificationClassPseudoModel {
        &mut self.pseudo_model
    }

    pub fn get_possible_subsumed_set(
        &mut self,
        create: bool,
    ) -> Option<&mut HashSet<OptimizedKPSetClassTestingItemId>> {
        if self.possible_subsumed_set.is_none() && create {
            self.possible_subsumed_set = Some(HashSet::new());
        }
        self.possible_subsumed_set.as_mut()
    }

    pub fn get_possible_subsumed_set_ref(
        &self,
    ) -> Option<&HashSet<OptimizedKPSetClassTestingItemId>> {
        self.possible_subsumed_set.as_ref()
    }

    pub fn get_possible_subsumed_list(&self) -> Option<&[OptimizedKPSetClassTestingItemId]> {
        self.possible_subsumed_list.as_deref()
    }

    pub fn set_possible_subsumed_list(
        &mut self,
        poss_subsumed_list: Vec<OptimizedKPSetClassTestingItemId>,
    ) -> &mut Self {
        self.possible_subsumed_list = Some(poss_subsumed_list);
        self
    }

    pub fn has_remaining_possible_subsumed_items(&self) -> bool {
        self.possible_subsumed_list
            .as_ref()
            .map(|list| !list.is_empty())
            .unwrap_or(false)
    }

    pub fn get_fast_satisfiability_tested_saturation_cache_entry(&self) -> Cint64 {
        self.fast_sat_cache_entry
    }

    pub fn set_fast_satisfiability_tested_saturation_cache_entry(
        &mut self,
        cache_entry: Cint64,
    ) -> &mut Self {
        self.fast_sat_cache_entry = cache_entry;
        self
    }

    pub fn has_successfully_fast_satisfiability_tested(&self) -> bool {
        self.succ_fast_sat_tested
    }

    pub fn set_successfully_fast_satisfiability_tested(
        &mut self,
        successfully_tested: bool,
    ) -> &mut Self {
        self.succ_fast_sat_tested = successfully_tested;
        self
    }

    /// Marker id used when this item is passed as
    /// `CIndividualDependenceTrackingMarker*`.
    pub fn individual_dependence_tracking_marker(&self) -> IndividualDependenceTrackingMarkerId {
        self.individual_dependence_tracking_marker
    }
}

impl Default for OptimizedSubClassSatisfiableTestingItem {
    fn default() -> Self {
        Self::new()
    }
}

impl OptimizedSubClassSatisfiableTestingItem {
    /// Constructor-side shell; `initSatisfiableTestingItem` installs the concept
    /// and resets the marker payload in C++.
    pub fn new() -> Self {
        Self {
            satisfiable_concept: ConceptId::NONE,
            individual_dependence_tracking_marker: IndividualDependenceTrackingMarkerId::NONE,
        }
    }

    /// Port of the currently live part of `initSatisfiableTestingItem`.
    pub fn init_satisfiable_testing_item(
        &mut self,
        sat_test_concept: ConceptId,
        marker: IndividualDependenceTrackingMarkerId,
    ) -> &mut Self {
        self.satisfiable_concept = sat_test_concept;
        self.individual_dependence_tracking_marker = marker;
        self
    }

    /// Port of `getSatisfiableConcept`.
    pub fn get_satisfiable_concept(&self) -> ConceptId {
        self.satisfiable_concept
    }

    /// Marker id used when this item is passed as
    /// `CIndividualDependenceTrackingMarker*`.
    pub fn individual_dependence_tracking_marker(&self) -> IndividualDependenceTrackingMarkerId {
        self.individual_dependence_tracking_marker
    }
}

/// Port of the individual-dependence adapter setup branch in
/// `COptimizedSubClassSubsumptionClassifierThread`.
#[derive(Debug, Default, Clone)]
pub struct OptimizedSubClassSubsumptionClassifierThread;

impl OptimizedSubClassSubsumptionClassifierThread {
    /// Port of the branch:
    ///
    /// ```text
    /// if (optSubClassItem->getIndividualDependenceTrackingCollector()) {
    ///   satCalcJob->setSatisfiableTaskIndividualDependenceTrackingAdapter(
    ///     new CSatisfiableTaskIndividualDependenceTrackingAdapter(
    ///       optSubClassItem->getIndividualDependenceTrackingCollector(),
    ///       nextSatTestItem));
    /// }
    /// ```
    pub fn set_satisfiable_task_individual_dependence_tracking_adapter(
        opt_sub_class_item: &OptimizedSubClassOntologyClassificationItem,
        next_sat_test_item: &OptimizedSubClassSatisfiableTestingItem,
        sat_calc_job: &mut SatisfiableCalculationJob,
        calc_context: &mut CalculationAlgorithmContext,
    ) {
        let collector = opt_sub_class_item.get_individual_dependence_tracking_collector();
        if collector.is_some() {
            let adapter = calc_context.alloc_individual_dependence_tracking_adapter(
                SatisfiableTaskIndividualDependenceTrackingAdapter::new(
                    collector,
                    next_sat_test_item.individual_dependence_tracking_marker(),
                ),
            );
            sat_calc_job.set_satisfiable_task_individual_dependence_tracking_adapter(adapter);
        }
    }
}

/// Port of `CClassClassificationComputationItem`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClassClassificationComputationItem {
    sat_calc_job: Cint64,
    test_valid: bool,
    concept_satisfiable_test: bool,
    concept_subsumption_test: bool,
    con0: ConceptId,
    con1: ConceptId,
}

impl ClassClassificationComputationItem {
    pub fn new_satisfiable(sat_calc_job: Cint64, satisfiable_tested_concept: ConceptId) -> Self {
        Self {
            sat_calc_job,
            test_valid: true,
            concept_satisfiable_test: true,
            concept_subsumption_test: false,
            con0: satisfiable_tested_concept,
            con1: ConceptId::NONE,
        }
    }

    pub fn new_subsumption(
        sat_calc_job: Cint64,
        subsumer_tested_concept: ConceptId,
        subsumed_tested_concept: ConceptId,
    ) -> Self {
        Self {
            sat_calc_job,
            test_valid: true,
            concept_satisfiable_test: false,
            concept_subsumption_test: true,
            con0: subsumer_tested_concept,
            con1: subsumed_tested_concept,
        }
    }

    pub fn get_satisfiable_calculation_job(&self) -> Cint64 {
        self.sat_calc_job
    }

    pub fn is_test_valid(&self) -> bool {
        self.test_valid
    }

    pub fn set_test_invalid(&mut self) -> &mut Self {
        self.test_valid = false;
        self
    }

    pub fn is_concept_satisfiable_test(&self) -> bool {
        self.concept_satisfiable_test
    }

    pub fn is_concept_subsumption_test(&self) -> bool {
        self.concept_subsumption_test
    }

    pub fn get_satisfiable_tested_concept(&self) -> ConceptId {
        if self.concept_satisfiable_test {
            self.con0
        } else {
            ConceptId::NONE
        }
    }

    pub fn get_subsumer_tested_concept(&self) -> ConceptId {
        if self.concept_subsumption_test {
            self.con0
        } else {
            ConceptId::NONE
        }
    }

    pub fn get_subsumed_tested_concept(&self) -> ConceptId {
        if self.concept_subsumption_test {
            self.con1
        } else {
            ConceptId::NONE
        }
    }
}

/// Port of `CPropertyClassificationComputationItem`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PropertyClassificationComputationItem {
    sat_calc_job: Cint64,
    role_satisfiable_test: bool,
    role_subsumption_test: bool,
    role1: RoleId,
    role2: RoleId,
}

impl PropertyClassificationComputationItem {
    pub fn new_satisfiable(sat_calc_job: Cint64, satisfiable_tested_role: RoleId) -> Self {
        Self {
            sat_calc_job,
            role_satisfiable_test: true,
            role_subsumption_test: false,
            role1: satisfiable_tested_role,
            role2: RoleId::NONE,
        }
    }

    pub fn new_subsumption(
        sat_calc_job: Cint64,
        subsumer_tested_role: RoleId,
        subsumed_tested_role: RoleId,
    ) -> Self {
        Self {
            sat_calc_job,
            role_satisfiable_test: false,
            role_subsumption_test: true,
            role1: subsumer_tested_role,
            role2: subsumed_tested_role,
        }
    }

    pub fn get_satisfiable_calculation_job(&self) -> Cint64 {
        self.sat_calc_job
    }

    pub fn is_role_satisfiable_test(&self) -> bool {
        self.role_satisfiable_test
    }

    pub fn is_role_subsumption_test(&self) -> bool {
        self.role_subsumption_test
    }

    pub fn get_satisfiable_tested_role(&self) -> RoleId {
        if self.role_satisfiable_test {
            self.role1
        } else {
            RoleId::NONE
        }
    }

    pub fn get_subsumer_tested_role(&self) -> RoleId {
        if self.role_subsumption_test {
            self.role1
        } else {
            RoleId::NONE
        }
    }

    pub fn get_subsumed_tested_role(&self) -> RoleId {
        if self.role_subsumption_test {
            self.role2
        } else {
            RoleId::NONE
        }
    }
}

/// Port of the classifier-facing fields on `CTestCalculatedCallbackEvent`.
#[derive(Debug, Clone)]
pub struct TestCalculatedCallbackEvent<W> {
    sat_calc_job: Cint64,
    classification_work_item: Option<W>,
    test_result_satisfiable: bool,
    calculation_error: bool,
    used_statistics_collection: Cint64,
}

impl<W> TestCalculatedCallbackEvent<W> {
    pub fn new(
        sat_calc_job: Cint64,
        classification_work_item: W,
        test_result_satisfiable: bool,
    ) -> Self {
        Self {
            sat_calc_job,
            classification_work_item: Some(classification_work_item),
            test_result_satisfiable,
            calculation_error: false,
            used_statistics_collection: INVALID,
        }
    }

    pub fn get_satisfiable_calculation_job(&self) -> Cint64 {
        self.sat_calc_job
    }

    pub fn get_classification_work_item(&self) -> Option<&W> {
        self.classification_work_item.as_ref()
    }

    pub fn get_test_result_satisfiable(&self) -> bool {
        self.test_result_satisfiable
    }

    pub fn has_calculation_error(&self) -> bool {
        self.calculation_error
    }

    pub fn set_calculation_error(&mut self, calculation_error: bool) -> &mut Self {
        self.calculation_error = calculation_error;
        self
    }

    pub fn get_used_statistics_collection(&self) -> Cint64 {
        self.used_statistics_collection
    }

    pub fn set_used_statistics_collection(&mut self, statistics: Cint64) -> &mut Self {
        self.used_statistics_collection = statistics;
        self
    }
}

/// Port of the individual-dependence adapter setup branches in
/// `COptimizedKPSetClassSubsumptionClassifierThread`.
#[derive(Debug, Clone)]
pub struct OptimizedKPSetClassSubsumptionClassifierThread {
    stat_satisfiable_tested_count: Cint64,
    stat_received_callback_count: Cint64,
    stat_interpreted_subsumption_calculation_count: Cint64,
    stat_ordered_subsumption_calculation_count: Cint64,
    stat_created_calculation_task_count: Cint64,
    stat_processed_subsumption_message_count: Cint64,
    stat_processed_possible_subsumption_init_message_count: Cint64,
    stat_processed_possible_subsumption_update_message_count: Cint64,
    stat_processed_pseudo_model_message_count: Cint64,
    conf_poss_subsum_calc_order_top_down: bool,
    conf_poss_subsum_calc_order_bottom_up: bool,
}

impl Default for OptimizedKPSetClassSubsumptionClassifierThread {
    fn default() -> Self {
        Self {
            stat_satisfiable_tested_count: 0,
            stat_received_callback_count: 0,
            stat_interpreted_subsumption_calculation_count: 0,
            stat_ordered_subsumption_calculation_count: 0,
            stat_created_calculation_task_count: 0,
            stat_processed_subsumption_message_count: 0,
            stat_processed_possible_subsumption_init_message_count: 0,
            stat_processed_possible_subsumption_update_message_count: 0,
            stat_processed_pseudo_model_message_count: 0,
            conf_poss_subsum_calc_order_top_down: true,
            conf_poss_subsum_calc_order_bottom_up: false,
        }
    }
}

impl OptimizedKPSetClassSubsumptionClassifierThread {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn get_processed_pseudo_model_message_count(&self) -> Cint64 {
        self.stat_processed_pseudo_model_message_count
    }

    pub fn get_satisfiable_tested_count(&self) -> Cint64 {
        self.stat_satisfiable_tested_count
    }

    pub fn get_received_callback_count(&self) -> Cint64 {
        self.stat_received_callback_count
    }

    pub fn get_interpreted_subsumption_calculation_count(&self) -> Cint64 {
        self.stat_interpreted_subsumption_calculation_count
    }

    pub fn get_ordered_subsumption_calculation_count(&self) -> Cint64 {
        self.stat_ordered_subsumption_calculation_count
    }

    pub fn get_created_calculation_task_count(&self) -> Cint64 {
        self.stat_created_calculation_task_count
    }

    pub fn set_possible_subsumption_calculation_order(
        &mut self,
        top_down: bool,
        bottom_up: bool,
    ) -> &mut Self {
        self.conf_poss_subsum_calc_order_top_down = top_down;
        self.conf_poss_subsum_calc_order_bottom_up = bottom_up;
        self
    }

    pub fn get_processed_subsumption_message_count(&self) -> Cint64 {
        self.stat_processed_subsumption_message_count
    }

    /// Port of the post-precheck work-item registration block in
    /// `calculateSatisfiable`.
    pub fn register_satisfiable_calculation_job(
        &mut self,
        opt_kpset_class_item: &mut OptimizedKPSetClassOntologyClassificationItem,
        next_sat_test_item_id: OptimizedKPSetClassTestingItemId,
        sat_calc_job: Cint64,
    ) -> Option<ClassClassificationComputationItem> {
        let concept = opt_kpset_class_item
            .get_concept_satisfiable_test_item_container()
            .get(next_sat_test_item_id.index())?
            .get_testing_concept();
        opt_kpset_class_item
            .get_concept_satisfiable_test_item_mut(next_sat_test_item_id)?
            .set_satisfiable_test_ordered(true);

        let work_item = ClassClassificationComputationItem::new_satisfiable(sat_calc_job, concept);
        opt_kpset_class_item.insert_work_item(sat_calc_job, work_item.clone());
        opt_kpset_class_item.inc_current_calculating_count(1);
        self.stat_created_calculation_task_count += 1;
        Some(work_item)
    }

    /// Port of the adjacent `setSatisfiableClassificationMessageAdapter(new
    /// CSatisfiableTaskClassificationMessageAdapter(..., EFEXTRACTALL))` call in
    /// `calculateSatisfiable`.
    pub fn register_satisfiable_calculation_job_with_message_adapter(
        &mut self,
        opt_kpset_class_item: &mut OptimizedKPSetClassOntologyClassificationItem,
        next_sat_test_item_id: OptimizedKPSetClassTestingItemId,
        sat_calc_job_handle: Cint64,
        sat_calc_job: &mut SatisfiableCalculationJob,
        testing_ontology: Cint64,
        classification_message_data_observer: Cint64,
        calc_context: &mut CalculationAlgorithmContext,
    ) -> Option<ClassClassificationComputationItem> {
        let work_item = self.register_satisfiable_calculation_job(
            opt_kpset_class_item,
            next_sat_test_item_id,
            sat_calc_job_handle,
        )?;
        let adapter = SatisfiableTaskClassificationMessageAdapter::new_with_handles(
            work_item.get_satisfiable_tested_concept(),
            testing_ontology,
            classification_message_data_observer,
            opt_kpset_class_item
                .get_concept_reference_linking_data_hash()
                .clone(),
            EFEXTRACTALL,
        );
        let adapter_id = calc_context.alloc_classification_message_adapter(adapter);
        sat_calc_job.set_satisfiable_classification_message_adapter(adapter_id);
        Some(work_item)
    }

    /// Port of the post-precheck work-item registration block in
    /// `calculateSubsumption`.
    pub fn register_subsumption_calculation_job(
        &mut self,
        opt_kpset_class_item: &mut OptimizedKPSetClassOntologyClassificationItem,
        subsumed_item_id: OptimizedKPSetClassTestingItemId,
        poss_subsumer_item_id: OptimizedKPSetClassTestingItemId,
        sat_calc_job: Cint64,
    ) -> Option<ClassClassificationComputationItem> {
        self.stat_ordered_subsumption_calculation_count += 1;
        let subsumed_concept = opt_kpset_class_item
            .get_concept_satisfiable_test_item_container()
            .get(subsumed_item_id.index())?
            .get_testing_concept();
        let subsumer_concept = opt_kpset_class_item
            .get_concept_satisfiable_test_item_container()
            .get(poss_subsumer_item_id.index())?
            .get_testing_concept();
        let work_item = ClassClassificationComputationItem::new_subsumption(
            sat_calc_job,
            subsumer_concept,
            subsumed_concept,
        );
        opt_kpset_class_item.insert_work_item(sat_calc_job, work_item.clone());
        opt_kpset_class_item.inc_current_calculating_count(1);
        opt_kpset_class_item.inc_calculated_possible_subsumer_count(1);
        self.stat_created_calculation_task_count += 1;
        Some(work_item)
    }

    /// Port of the adjacent `setSatisfiableClassificationMessageAdapter(new
    /// CSatisfiableTaskClassificationMessageAdapter(..., extFlags))` call in
    /// `calculateSubsumption`.
    pub fn register_subsumption_calculation_job_with_message_adapter(
        &mut self,
        opt_kpset_class_item: &mut OptimizedKPSetClassOntologyClassificationItem,
        subsumed_item_id: OptimizedKPSetClassTestingItemId,
        poss_subsumer_item_id: OptimizedKPSetClassTestingItemId,
        sat_calc_job_handle: Cint64,
        sat_calc_job: &mut SatisfiableCalculationJob,
        testing_ontology: Cint64,
        classification_message_data_observer: Cint64,
        calc_context: &mut CalculationAlgorithmContext,
    ) -> Option<ClassClassificationComputationItem> {
        let work_item = self.register_subsumption_calculation_job(
            opt_kpset_class_item,
            subsumed_item_id,
            poss_subsumer_item_id,
            sat_calc_job_handle,
        )?;
        let adapter = SatisfiableTaskClassificationMessageAdapter::new_with_handles(
            work_item.get_subsumed_tested_concept(),
            testing_ontology,
            classification_message_data_observer,
            opt_kpset_class_item
                .get_concept_reference_linking_data_hash()
                .clone(),
            EFEXTRACTSUBSUMERSOTHERNODES
                | EFEXTRACTPOSSIBLESUBSUMERSROOTNODE
                | EFEXTRACTPOSSIBLESUBSUMERSOTHERNODES
                | EFEXTRACTOTHERNODESMULTIPLEDEPENDENCY,
        );
        let adapter_id = calc_context.alloc_classification_message_adapter(adapter);
        sat_calc_job.set_satisfiable_classification_message_adapter(adapter_id);
        Some(work_item)
    }

    /// Port of the queue/result part of
    /// `COptimizedKPSetClassSubsumptionClassifierThread::interpreteSatisfiableResult`.
    ///
    /// The outer taxonomy mutation in the unsatisfiable branch is left to the
    /// taxonomy layer; the classifier item state, running counter, satisfiable
    /// list, successor predecessor counters, and next/next-candidate queues are
    /// updated exactly at this call point.
    pub fn interprete_satisfiable_result(
        &mut self,
        opt_kpset_class_item: &mut OptimizedKPSetClassOntologyClassificationItem,
        satisfiable_concept: ConceptId,
        is_satis: bool,
        concepts: &Arena<Concept>,
    ) -> bool {
        self.stat_satisfiable_tested_count += 1;
        opt_kpset_class_item.dec_running_satisfiable_tests_count(1);

        let sat_tested_item_id = opt_kpset_class_item.get_concept_satisfiable_test_item(
            satisfiable_concept,
            false,
            concepts,
        );
        if sat_tested_item_id.is_none() {
            return false;
        }

        let (subsuming_items, successor_items) = {
            let sat_tested_item = opt_kpset_class_item
                .get_concept_satisfiable_test_item_mut(sat_tested_item_id)
                .expect("satisfiable test item");
            sat_tested_item
                .set_satisfiable_tested(true)
                .set_satisfiable_tested_result(is_satis);
            (
                sat_tested_item.get_subsuming_concept_item_list().to_vec(),
                sat_tested_item.get_successor_item_list().to_vec(),
            )
        };

        if is_satis {
            opt_kpset_class_item.add_satisfiable_concept_item(sat_tested_item_id);
        }

        for succ_item_id in successor_items {
            let ready = {
                let succ_item = opt_kpset_class_item
                    .get_concept_satisfiable_test_item_mut(succ_item_id)
                    .expect("successor satisfiable test item");
                if !is_satis {
                    succ_item.set_result_unsatisfiable_derivated(true);
                } else {
                    for subsumer_item_id in &subsuming_items {
                        if succ_item_id != *subsumer_item_id {
                            succ_item.add_subsuming_concept_item(*subsumer_item_id);
                        }
                    }
                }
                succ_item.dec_unprocessed_predecessor_items(1);
                succ_item.has_only_processed_predecessor_items()
            };
            if ready {
                opt_kpset_class_item
                    .get_next_satisfiable_testing_item_list_mut()
                    .push(succ_item_id);
            } else {
                opt_kpset_class_item
                    .get_next_candidate_satisfiable_testing_item_set_mut()
                    .insert(succ_item_id);
            }
        }

        false
    }

    /// Compatibility wrapper for the W276 satisfiable-branch slice. The full
    /// callback dispatcher is `interprete_test_results`.
    pub fn interprete_test_results_satisfiable_branch(
        &mut self,
        opt_kpset_class_item: &mut OptimizedKPSetClassOntologyClassificationItem,
        test_result: &TestCalculatedCallbackEvent<ClassClassificationComputationItem>,
        concepts: &Arena<Concept>,
    ) -> bool {
        self.interprete_test_results(opt_kpset_class_item, test_result, concepts)
    }

    /// Port of the current in-memory result-dispatch body in
    /// `COptimizedKPSetClassSubsumptionClassifierThread::interpreteTestResults`.
    pub fn interprete_test_results(
        &mut self,
        opt_kpset_class_item: &mut OptimizedKPSetClassOntologyClassificationItem,
        test_result: &TestCalculatedCallbackEvent<ClassClassificationComputationItem>,
        concepts: &Arena<Concept>,
    ) -> bool {
        self.stat_received_callback_count += 1;

        let Some(work_item) = test_result.get_classification_work_item() else {
            return true;
        };

        opt_kpset_class_item.dec_current_calculating_count(1);
        if work_item.is_test_valid() {
            if test_result.has_calculation_error() {
                opt_kpset_class_item.set_taxonomy_construction_failed();
            } else if work_item.is_concept_satisfiable_test() {
                self.interprete_satisfiable_result(
                    opt_kpset_class_item,
                    work_item.get_satisfiable_tested_concept(),
                    test_result.get_test_result_satisfiable(),
                    concepts,
                );
            } else if work_item.is_concept_subsumption_test() {
                self.interprete_subsumption_result(
                    opt_kpset_class_item,
                    work_item.get_subsumed_tested_concept(),
                    work_item.get_subsumer_tested_concept(),
                    !test_result.get_test_result_satisfiable(),
                    concepts,
                );
            }
        }
        opt_kpset_class_item
            .remove_work_item_if_matching(test_result.get_satisfiable_calculation_job(), work_item);
        opt_kpset_class_item
            .reuse_calculation_statistics_collection(test_result.get_used_statistics_collection());

        true
    }

    /// Port of
    /// `COptimizedKPSetClassSubsumptionClassifierThread::interpreteSubsumptionResult`.
    pub fn interprete_subsumption_result(
        &mut self,
        opt_kpset_class_item: &mut OptimizedKPSetClassOntologyClassificationItem,
        subsumed_concept: ConceptId,
        subsumer_concept: ConceptId,
        is_subsumption: bool,
        concepts: &Arena<Concept>,
    ) -> bool {
        self.stat_interpreted_subsumption_calculation_count += 1;

        let candidate_concept = if Self::is_eq_concept(subsumer_concept, concepts) {
            opt_kpset_class_item
                .get_equivalent_concept_candidate_hash()
                .get(&subsumer_concept)
                .copied()
                .filter(|candidate| candidate.is_some())
                .unwrap_or(subsumer_concept)
        } else {
            subsumer_concept
        };

        opt_kpset_class_item.dec_running_possible_subsumption_tests_count(1);

        let subsumed_item_id = opt_kpset_class_item.get_concept_satisfiable_test_item(
            subsumed_concept,
            false,
            concepts,
        );
        let subsumer_item_id = opt_kpset_class_item.get_concept_satisfiable_test_item(
            subsumer_concept,
            false,
            concepts,
        );
        if subsumed_item_id.is_none() || subsumer_item_id.is_none() {
            return false;
        }

        let poss_subsum_map_exists = opt_kpset_class_item
            .get_concept_satisfiable_test_item_container()[subsumed_item_id.index()]
        .get_possible_subsumption_map_ref()
        .is_some();
        let poss_subsum_data_exists = opt_kpset_class_item
            .get_concept_satisfiable_test_item_container()[subsumed_item_id.index()]
        .get_possible_subsumption_map_ref()
        .and_then(|map| map.get(candidate_concept))
        .is_some();

        if is_subsumption {
            opt_kpset_class_item.inc_calculated_true_possible_subsumer_count(1);
            if poss_subsum_data_exists {
                opt_kpset_class_item
                    .get_concept_satisfiable_test_item_mut(subsumed_item_id)
                    .expect("subsumed item exists")
                    .get_possible_subsumption_map(false)
                    .expect("possible subsumption map exists")
                    .get_mut(candidate_concept)
                    .expect("possible subsumption data exists")
                    .set_subsumption_confirmed(true);
            }
            opt_kpset_class_item
                .get_concept_satisfiable_test_item_mut(subsumed_item_id)
                .expect("subsumed item exists")
                .add_subsuming_concept_item(subsumer_item_id)
                .add_up_propagation_item(subsumer_item_id);
            opt_kpset_class_item
                .get_concept_satisfiable_test_item_mut(subsumer_item_id)
                .expect("subsumer item exists")
                .add_down_propagation_item(subsumed_item_id);
            Self::propagate_down_subsumption(
                opt_kpset_class_item,
                subsumed_item_id,
                subsumer_item_id,
            );
        } else {
            opt_kpset_class_item.inc_calculated_false_possible_subsumer_count(1);
            if poss_subsum_data_exists {
                opt_kpset_class_item
                    .get_concept_satisfiable_test_item_mut(subsumed_item_id)
                    .expect("subsumed item exists")
                    .get_possible_subsumption_map(false)
                    .expect("possible subsumption map exists")
                    .get_mut(candidate_concept)
                    .expect("possible subsumption data exists")
                    .set_subsumption_invalid(true);
            }
        }

        let update_required = opt_kpset_class_item.get_concept_satisfiable_test_item_container()
            [subsumed_item_id.index()]
        .get_possible_subsumption_map_ref()
        .and_then(|map| map.get(candidate_concept))
        .map(|data| data.is_update_required())
        .unwrap_or(false);
        if update_required {
            Self::prune_possible_subsumptions(
                opt_kpset_class_item,
                subsumed_item_id,
                candidate_concept,
                concepts,
            );
        }

        if self.conf_poss_subsum_calc_order_top_down
            && opt_kpset_class_item
                .get_current_possible_subsumption_testing_item_set()
                .contains(&subsumed_item_id)
        {
            opt_kpset_class_item
                .get_current_possible_subsumption_testing_item_set_mut()
                .remove(&subsumed_item_id);
            if poss_subsum_map_exists {
                let has_remaining = opt_kpset_class_item
                    .get_concept_satisfiable_test_item_container()[subsumed_item_id.index()]
                .get_possible_subsumption_map_ref()
                .map(|map| map.has_remaining_possible_subsumptions())
                .unwrap_or(false);
                if has_remaining {
                    opt_kpset_class_item
                        .get_next_possible_subsumption_testing_item_list_mut()
                        .insert(0, subsumed_item_id);
                } else {
                    opt_kpset_class_item
                        .get_remaining_possible_subsumption_class_testing_set_mut()
                        .remove(&subsumed_item_id);
                }
            }
        }

        if self.conf_poss_subsum_calc_order_bottom_up
            && opt_kpset_class_item
                .get_current_possible_subsumption_testing_item_set()
                .contains(&subsumer_item_id)
        {
            opt_kpset_class_item
                .get_current_possible_subsumption_testing_item_set_mut()
                .remove(&subsumer_item_id);
            let has_remaining = opt_kpset_class_item.get_concept_satisfiable_test_item_container()
                [subsumer_item_id.index()]
            .has_remaining_possible_subsumed_items();
            if has_remaining {
                opt_kpset_class_item
                    .get_next_possible_subsumption_testing_item_list_mut()
                    .insert(0, subsumer_item_id);

                let up_items = opt_kpset_class_item.get_concept_satisfiable_test_item_container()
                    [subsumed_item_id.index()]
                .get_up_propagation_item_set()
                .iter()
                .copied()
                .collect::<Vec<_>>();
                let mut rem_list = opt_kpset_class_item
                    .get_concept_satisfiable_test_item_container()[subsumer_item_id.index()]
                .get_possible_subsumed_list()
                .map(|list| list.to_vec())
                .unwrap_or_default();
                let rem_set = opt_kpset_class_item.get_concept_satisfiable_test_item_container()
                    [subsumer_item_id.index()]
                .get_possible_subsumed_set_ref()
                .cloned()
                .unwrap_or_default();
                for up_item_id in up_items {
                    if rem_set.contains(&up_item_id) {
                        rem_list.insert(0, up_item_id);
                    }
                }
                opt_kpset_class_item
                    .get_concept_satisfiable_test_item_mut(subsumer_item_id)
                    .expect("subsumer item exists")
                    .set_possible_subsumed_list(rem_list);
            } else {
                opt_kpset_class_item
                    .get_remaining_possible_subsumption_class_testing_set_mut()
                    .remove(&subsumer_item_id);
            }
        }

        true
    }

    pub fn get_processed_possible_subsumption_init_message_count(&self) -> Cint64 {
        self.stat_processed_possible_subsumption_init_message_count
    }

    pub fn get_processed_possible_subsumption_update_message_count(&self) -> Cint64 {
        self.stat_processed_possible_subsumption_update_message_count
    }

    /// Port of the `TELLCLASSSUBSUMPTION` receive branch in
    /// `COptimizedKPSetClassSubsumptionClassifierThread`.
    pub fn process_class_subsumption_message(
        &mut self,
        opt_kpset_class_item: &mut OptimizedKPSetClassOntologyClassificationItem,
        subsum_message_data: &ClassificationClassSubsumptionMessageData,
        concepts: &Arena<Concept>,
    ) -> bool {
        self.stat_processed_subsumption_message_count += 1;
        let subsumed_concept = subsum_message_data.get_subsumed_concept();
        let subsumed_item_id = opt_kpset_class_item.get_concept_satisfiable_test_item(
            subsumed_concept,
            false,
            concepts,
        );
        if subsumed_item_id.is_none() {
            return false;
        }

        for subsumer_concept in subsum_message_data.get_class_subsumer_list().unwrap_or(&[]) {
            let subsumer_item_id = opt_kpset_class_item.get_concept_satisfiable_test_item(
                *subsumer_concept,
                false,
                concepts,
            );
            if subsumer_item_id.is_none() || subsumer_item_id == subsumed_item_id {
                continue;
            }

            let subsumed_item = opt_kpset_class_item
                .get_concept_satisfiable_test_item_mut(subsumed_item_id)
                .expect("subsumed item exists");
            subsumed_item.add_subsuming_concept_item(subsumer_item_id);
            if let Some(poss_subsum_map) = subsumed_item.get_possible_subsumption_map(false) {
                if let Some(poss_subsum_data) = poss_subsum_map.get_mut(*subsumer_concept) {
                    if !poss_subsum_data.is_subsumption_confirmed() {
                        poss_subsum_data.set_subsumption_confirmed(true);
                        if poss_subsum_data.is_update_required() {
                            let _ = Self::prune_possible_subsumptions(
                                opt_kpset_class_item,
                                subsumed_item_id,
                                *subsumer_concept,
                                concepts,
                            );
                        }
                    }
                }
            }
            let _ = Self::propagate_down_subsumption(
                opt_kpset_class_item,
                subsumed_item_id,
                subsumer_item_id,
            );
        }

        opt_kpset_class_item
            .get_concept_satisfiable_test_item_mut(subsumed_item_id)
            .expect("subsumed item exists")
            .set_result_satisfiable_derivated(true);
        true
    }

    /// Bounded port of the `TELLCLASSINITIALIZEPOSSIBLESUBSUM` receive branch.
    pub fn process_initialize_possible_class_subsumption_message(
        &mut self,
        opt_kpset_class_item: &mut OptimizedKPSetClassOntologyClassificationItem,
        poss_subsum_message_data: &ClassificationInitializePossibleClassSubsumptionMessageData,
        concepts: &Arena<Concept>,
    ) -> bool {
        self.stat_processed_possible_subsumption_init_message_count += 1;
        let subsumed_concept = poss_subsum_message_data.get_subsumed_concept();
        let subsumed_item_id = opt_kpset_class_item.get_concept_satisfiable_test_item(
            subsumed_concept,
            false,
            concepts,
        );
        if subsumed_item_id.is_none() {
            return false;
        }

        let poss_subsumer_list = poss_subsum_message_data.get_class_possible_subsumer_list();
        let valid_poss_subsumer_concepts: HashSet<ConceptId> = poss_subsumer_list
            .unwrap_or(&[])
            .iter()
            .filter(|data| data.is_possible_subsumer_valid())
            .map(|data| data.get_possible_subsumer_concept())
            .collect();
        let equiv_non_candidate_set_empty = opt_kpset_class_item
            .get_equivaltent_concept_non_candidate_set()
            .is_empty();
        let message_poss_list_empty = poss_subsumer_list
            .map(|list| list.is_empty())
            .unwrap_or(true);

        if equiv_non_candidate_set_empty && message_poss_list_empty {
            let unknown_concepts = opt_kpset_class_item
                .get_concept_satisfiable_test_item_mut(subsumed_item_id)
                .and_then(|item| item.get_possible_subsumption_map(false))
                .map(|poss_subsum_map| {
                    poss_subsum_map
                        .concepts()
                        .into_iter()
                        .filter(|concept| {
                            poss_subsum_map
                                .get(*concept)
                                .map(|data| data.is_subsumption_unknown())
                                .unwrap_or(false)
                        })
                        .collect::<Vec<_>>()
                })
                .unwrap_or_default();
            for unknown_concept in unknown_concepts {
                if let Some(data) = opt_kpset_class_item
                    .get_concept_satisfiable_test_item_mut(subsumed_item_id)
                    .and_then(|item| item.get_possible_subsumption_map(false))
                    .and_then(|map| map.get_mut(unknown_concept))
                {
                    data.set_subsumption_invalid(true);
                }
                let _ = Self::prune_possible_subsumptions(
                    opt_kpset_class_item,
                    subsumed_item_id,
                    unknown_concept,
                    concepts,
                );
            }
        } else {
            let map_was_empty = opt_kpset_class_item
                .get_concept_satisfiable_test_item_mut(subsumed_item_id)
                .and_then(|item| item.get_possible_subsumption_map(false))
                .map(|map| map.is_empty())
                .unwrap_or(true);
            if map_was_empty {
                let mut inserted_count = 0;
                for poss_subsum_concept in &valid_poss_subsumer_concepts {
                    if !Self::is_equivalent_candidate_key(
                        opt_kpset_class_item,
                        *poss_subsum_concept,
                        concepts,
                    ) {
                        inserted_count += Self::insert_possible_class_subsumer(
                            opt_kpset_class_item,
                            subsumed_item_id,
                            *poss_subsum_concept,
                            concepts,
                        );
                    }
                }

                if poss_subsum_message_data.has_eq_concepts_non_candidate_poss_subsumers() {
                    if let Some(eq_poss_subsumer_list) = poss_subsum_message_data
                        .get_class_eq_concept_non_candidate_possible_subsumer_list()
                    {
                        for eq_concept in eq_poss_subsumer_list {
                            inserted_count += Self::insert_possible_class_subsumer(
                                opt_kpset_class_item,
                                subsumed_item_id,
                                *eq_concept,
                                concepts,
                            );
                        }
                    }
                } else {
                    let eq_concepts = opt_kpset_class_item
                        .get_equivaltent_concept_non_candidate_set()
                        .iter()
                        .copied()
                        .collect::<Vec<_>>();
                    for eq_concept in eq_concepts {
                        inserted_count += Self::insert_possible_class_subsumer(
                            opt_kpset_class_item,
                            subsumed_item_id,
                            eq_concept,
                            concepts,
                        );
                    }
                }

                if inserted_count > 0 {
                    opt_kpset_class_item
                        .inc_remaining_possible_subsumption_tests_count(inserted_count)
                        .inc_possible_subsumer_count(inserted_count);
                }
                Self::prune_initialized_possible_subsumption_maps(
                    opt_kpset_class_item,
                    subsumed_item_id,
                    concepts,
                );
            } else {
                let to_invalidate = opt_kpset_class_item
                    .get_concept_satisfiable_test_item_mut(subsumed_item_id)
                    .and_then(|item| item.get_possible_subsumption_map(false))
                    .map(|poss_subsum_map| {
                        poss_subsum_map
                            .concepts()
                            .into_iter()
                            .filter(|concept| {
                                !valid_poss_subsumer_concepts.contains(concept)
                                    && !Self::is_eq_concept(*concept, concepts)
                                    && poss_subsum_map
                                        .get(*concept)
                                        .map(|data| !data.is_subsumption_invalided())
                                        .unwrap_or(false)
                            })
                            .collect::<Vec<_>>()
                    })
                    .unwrap_or_default();
                for invalid_concept in to_invalidate {
                    if let Some(data) = opt_kpset_class_item
                        .get_concept_satisfiable_test_item_mut(subsumed_item_id)
                        .and_then(|item| item.get_possible_subsumption_map(false))
                        .and_then(|map| map.get_mut(invalid_concept))
                    {
                        data.set_subsumption_invalid(true);
                    }
                    let _ = Self::prune_possible_subsumptions(
                        opt_kpset_class_item,
                        subsumed_item_id,
                        invalid_concept,
                        concepts,
                    );
                }
            }
        }
        opt_kpset_class_item
            .get_concept_satisfiable_test_item_mut(subsumed_item_id)
            .expect("subsumed item exists")
            .set_possible_subsumption_map_initialized(true);
        true
    }

    /// Bounded port of the `TELLCLASSUPDATEPOSSIBLESUBSUM` receive branch.
    pub fn process_update_possible_class_subsumption_message(
        &mut self,
        opt_kpset_class_item: &mut OptimizedKPSetClassOntologyClassificationItem,
        poss_subsum_message_data: &ClassificationUpdatePossibleClassSubsumptionMessageData,
        concepts: &Arena<Concept>,
    ) -> bool {
        self.stat_processed_possible_subsumption_update_message_count += 1;
        let subsumed_concept = poss_subsum_message_data.get_subsumed_concept();
        let subsumed_item_id = opt_kpset_class_item.get_concept_satisfiable_test_item(
            subsumed_concept,
            false,
            concepts,
        );
        if subsumed_item_id.is_none() {
            return false;
        }
        if let Some(poss_subsum_map) = opt_kpset_class_item
            .get_concept_satisfiable_test_item_mut(subsumed_item_id)
            .expect("subsumed item exists")
            .get_possible_subsumption_map(false)
        {
            let update_required_concepts = poss_subsum_map.update_required_concepts();
            for poss_subsum_concept in update_required_concepts {
                let _ = Self::prune_possible_subsumptions(
                    opt_kpset_class_item,
                    subsumed_item_id,
                    poss_subsum_concept,
                    concepts,
                );
            }
        }
        true
    }

    fn dec_remaining_possible_subsumption_testing_count(
        opt_kpset_class_item: &mut OptimizedKPSetClassOntologyClassificationItem,
        item_id: OptimizedKPSetClassTestingItemId,
        poss_subsum_concept: ConceptId,
        subsumption_confirmed: bool,
    ) {
        if subsumption_confirmed {
            opt_kpset_class_item.inc_true_possible_subsumer_count(1);
        } else {
            opt_kpset_class_item.inc_false_possible_subsumer_count(1);
        }
        opt_kpset_class_item.dec_remaining_possible_subsumption_tests_count(1);
        if let Some(poss_subsum_map) = opt_kpset_class_item
            .get_concept_satisfiable_test_item_mut(item_id)
            .and_then(|item| item.get_possible_subsumption_map(false))
        {
            if poss_subsum_map.contains(poss_subsum_concept) {
                poss_subsum_map.dec_remaining_possible_subsumption_count(1);
            }
        }
    }

    fn equivalent_candidate_concept(
        opt_kpset_class_item: &OptimizedKPSetClassOntologyClassificationItem,
        concept: ConceptId,
        concepts: &Arena<Concept>,
    ) -> Option<ConceptId> {
        if !Self::is_eq_concept(concept, concepts) {
            return None;
        }
        opt_kpset_class_item
            .get_equivalent_concept_candidate_hash()
            .get(&concept)
            .copied()
            .filter(|candidate| candidate.is_some())
    }

    fn is_eq_concept(concept: ConceptId, concepts: &Arena<Concept>) -> bool {
        concept.is_some()
            && concept.index() < concepts.len()
            && concepts.get(concept).get_operator_code() == CCEQ
    }

    fn is_equivalent_candidate_key(
        opt_kpset_class_item: &OptimizedKPSetClassOntologyClassificationItem,
        concept: ConceptId,
        concepts: &Arena<Concept>,
    ) -> bool {
        Self::is_eq_concept(concept, concepts)
            && opt_kpset_class_item
                .get_equivalent_concept_candidate_hash()
                .contains_key(&concept)
    }

    fn concept_tag(concepts: &Arena<Concept>, concept: ConceptId) -> Cint64 {
        if concept.is_some() && concept.index() < concepts.len() {
            concepts.get(concept).get_concept_tag()
        } else {
            INVALID
        }
    }

    fn sorted_possible_subsumption_concepts(
        opt_kpset_class_item: &OptimizedKPSetClassOntologyClassificationItem,
        item_id: OptimizedKPSetClassTestingItemId,
        concepts: &Arena<Concept>,
    ) -> Vec<ConceptId> {
        let mut poss_concepts = opt_kpset_class_item.get_concept_satisfiable_test_item_container()
            [item_id.index()]
        .get_possible_subsumption_map_ref()
        .map(|map| map.concepts())
        .unwrap_or_default();
        poss_concepts.sort_by_key(|concept| Self::concept_tag(concepts, *concept));
        poss_concepts
    }

    fn possible_subsumption_class_item(
        opt_kpset_class_item: &OptimizedKPSetClassOntologyClassificationItem,
        item_id: OptimizedKPSetClassTestingItemId,
        poss_subsum_concept: ConceptId,
    ) -> Option<OptimizedKPSetClassTestingItemId> {
        opt_kpset_class_item.get_concept_satisfiable_test_item_container()[item_id.index()]
            .get_possible_subsumption_map_ref()
            .and_then(|map| map.get(poss_subsum_concept))
            .map(|data| data.get_class_item())
    }

    fn invalidate_and_prune_possible_subsumption(
        opt_kpset_class_item: &mut OptimizedKPSetClassOntologyClassificationItem,
        item_id: OptimizedKPSetClassTestingItemId,
        poss_subsum_concept: ConceptId,
        concepts: &Arena<Concept>,
    ) -> bool {
        let Some(update_required) = opt_kpset_class_item
            .get_concept_satisfiable_test_item_mut(item_id)
            .and_then(|item| item.get_possible_subsumption_map(false))
            .and_then(|map| {
                map.get_mut(poss_subsum_concept).map(|data| {
                    if !data.is_subsumption_invalided() {
                        data.set_subsumption_invalid(true);
                    }
                    data.is_update_required()
                })
            })
        else {
            return false;
        };
        if update_required {
            Self::prune_possible_subsumptions(
                opt_kpset_class_item,
                item_id,
                poss_subsum_concept,
                concepts,
            )
        } else {
            false
        }
    }

    /// Port of the ancestor/descendant pruning block in
    /// `TELLCLASSINITIALIZEPOSSIBLESUBSUM` after a fresh possible map was filled.
    fn prune_initialized_possible_subsumption_maps(
        opt_kpset_class_item: &mut OptimizedKPSetClassOntologyClassificationItem,
        subsumed_item_id: OptimizedKPSetClassTestingItemId,
        concepts: &Arena<Concept>,
    ) {
        let poss_concepts = Self::sorted_possible_subsumption_concepts(
            opt_kpset_class_item,
            subsumed_item_id,
            concepts,
        );
        if poss_concepts.is_empty() {
            return;
        }

        for up_item_id in Self::propagation_parents(opt_kpset_class_item, subsumed_item_id) {
            let up_concepts = Self::sorted_possible_subsumption_concepts(
                opt_kpset_class_item,
                up_item_id,
                concepts,
            );
            let mut poss_index = 0;
            let mut up_index = 0;
            let mut invalidate_up = Vec::new();
            while poss_index < poss_concepts.len() && up_index < up_concepts.len() {
                let poss_tag = Self::concept_tag(concepts, poss_concepts[poss_index]);
                let up_tag = Self::concept_tag(concepts, up_concepts[up_index]);
                if poss_tag == up_tag {
                    poss_index += 1;
                    up_index += 1;
                } else if poss_tag < up_tag {
                    poss_index += 1;
                } else {
                    invalidate_up.push(up_concepts[up_index]);
                    up_index += 1;
                }
            }
            while up_index < up_concepts.len() {
                invalidate_up.push(up_concepts[up_index]);
                up_index += 1;
            }
            for up_concept in invalidate_up {
                let Some(up_class_item) = Self::possible_subsumption_class_item(
                    opt_kpset_class_item,
                    up_item_id,
                    up_concept,
                ) else {
                    continue;
                };
                let subsumed_item = &opt_kpset_class_item
                    .get_concept_satisfiable_test_item_container()[subsumed_item_id.index()];
                if !subsumed_item.has_subsumer_concept_item(up_class_item)
                    && subsumed_item_id != up_class_item
                {
                    let _ = Self::invalidate_and_prune_possible_subsumption(
                        opt_kpset_class_item,
                        up_item_id,
                        up_concept,
                        concepts,
                    );
                }
            }
        }

        for down_item_id in Self::propagation_children(opt_kpset_class_item, subsumed_item_id) {
            let down_has_map = opt_kpset_class_item.get_concept_satisfiable_test_item_container()
                [down_item_id.index()]
            .has_class_possible_subsumption_map();
            if down_has_map {
                let down_concepts = Self::sorted_possible_subsumption_concepts(
                    opt_kpset_class_item,
                    down_item_id,
                    concepts,
                );
                let mut poss_index = 0;
                let mut down_index = 0;
                let mut invalidate_subsumed = Vec::new();
                while poss_index < poss_concepts.len() && down_index < down_concepts.len() {
                    let poss_tag = Self::concept_tag(concepts, poss_concepts[poss_index]);
                    let down_tag = Self::concept_tag(concepts, down_concepts[down_index]);
                    if poss_tag == down_tag {
                        poss_index += 1;
                        down_index += 1;
                    } else if down_tag < poss_tag {
                        down_index += 1;
                    } else {
                        invalidate_subsumed.push(poss_concepts[poss_index]);
                        poss_index += 1;
                    }
                }
                while poss_index < poss_concepts.len() {
                    invalidate_subsumed.push(poss_concepts[poss_index]);
                    poss_index += 1;
                }
                for poss_concept in invalidate_subsumed {
                    let Some(poss_class_item) = Self::possible_subsumption_class_item(
                        opt_kpset_class_item,
                        subsumed_item_id,
                        poss_concept,
                    ) else {
                        continue;
                    };
                    let down_item = &opt_kpset_class_item
                        .get_concept_satisfiable_test_item_container()[down_item_id.index()];
                    if !down_item.has_subsumer_concept_item(poss_class_item)
                        && down_item_id != poss_class_item
                    {
                        let _ = Self::invalidate_and_prune_possible_subsumption(
                            opt_kpset_class_item,
                            subsumed_item_id,
                            poss_concept,
                            concepts,
                        );
                    }
                }
            } else if opt_kpset_class_item.get_concept_satisfiable_test_item_container()
                [down_item_id.index()]
            .is_possible_subsumption_map_initialized()
            {
                for poss_concept in &poss_concepts {
                    let Some(poss_class_item) = Self::possible_subsumption_class_item(
                        opt_kpset_class_item,
                        subsumed_item_id,
                        *poss_concept,
                    ) else {
                        continue;
                    };
                    let down_item = &opt_kpset_class_item
                        .get_concept_satisfiable_test_item_container()[down_item_id.index()];
                    if !down_item.has_subsumer_concept_item(poss_class_item)
                        && down_item_id != poss_class_item
                    {
                        let _ = Self::invalidate_and_prune_possible_subsumption(
                            opt_kpset_class_item,
                            subsumed_item_id,
                            *poss_concept,
                            concepts,
                        );
                    }
                }
            }
        }
    }

    fn propagation_children(
        opt_kpset_class_item: &OptimizedKPSetClassOntologyClassificationItem,
        item_id: OptimizedKPSetClassTestingItemId,
    ) -> Vec<OptimizedKPSetClassTestingItemId> {
        opt_kpset_class_item.get_concept_satisfiable_test_item_container()[item_id.index()]
            .get_down_propagation_item_set()
            .iter()
            .copied()
            .collect()
    }

    fn propagation_parents(
        opt_kpset_class_item: &OptimizedKPSetClassOntologyClassificationItem,
        item_id: OptimizedKPSetClassTestingItemId,
    ) -> Vec<OptimizedKPSetClassTestingItemId> {
        opt_kpset_class_item.get_concept_satisfiable_test_item_container()[item_id.index()]
            .get_up_propagation_item_set()
            .iter()
            .copied()
            .collect()
    }

    /// Port of `propagateDownSubsumption`.
    pub fn propagate_down_subsumption(
        opt_kpset_class_item: &mut OptimizedKPSetClassOntologyClassificationItem,
        item_id: OptimizedKPSetClassTestingItemId,
        subsumer_item_id: OptimizedKPSetClassTestingItemId,
    ) -> bool {
        let mut propagated = false;
        for down_item_id in Self::propagation_children(opt_kpset_class_item, item_id) {
            let should_add = down_item_id != subsumer_item_id
                && !opt_kpset_class_item.get_concept_satisfiable_test_item_container()
                    [down_item_id.index()]
                .has_subsumer_concept_item(subsumer_item_id);
            if should_add {
                opt_kpset_class_item
                    .get_concept_satisfiable_test_item_mut(down_item_id)
                    .expect("down-propagation item exists")
                    .add_subsuming_concept_item(subsumer_item_id);
                Self::propagate_down_subsumption(
                    opt_kpset_class_item,
                    down_item_id,
                    subsumer_item_id,
                );
                propagated = true;
            }
        }
        propagated
    }

    /// Port of `prunePossibleSubsumptions`.
    pub fn prune_possible_subsumptions(
        opt_kpset_class_item: &mut OptimizedKPSetClassOntologyClassificationItem,
        item_id: OptimizedKPSetClassTestingItemId,
        poss_subsum_concept: ConceptId,
        concepts: &Arena<Concept>,
    ) -> bool {
        let Some((confirmed, invalided, subsumer_item_id)) = opt_kpset_class_item
            .get_concept_satisfiable_test_item_mut(item_id)
            .and_then(|item| item.get_possible_subsumption_map(false))
            .and_then(|poss_subsum_map| {
                poss_subsum_map
                    .get_mut(poss_subsum_concept)
                    .and_then(|data| {
                        if data.is_update_required() {
                            data.set_subsumption_updated(true);
                            Some((
                                data.is_subsumption_confirmed(),
                                data.is_subsumption_invalided(),
                                data.get_class_item(),
                            ))
                        } else {
                            None
                        }
                    })
            })
        else {
            return false;
        };

        Self::dec_remaining_possible_subsumption_testing_count(
            opt_kpset_class_item,
            item_id,
            poss_subsum_concept,
            true,
        );

        if confirmed {
            let subsumer_concept = opt_kpset_class_item
                .get_concept_satisfiable_test_item_container()[subsumer_item_id.index()]
            .get_testing_concept();
            let down_items = Self::propagation_children(opt_kpset_class_item, item_id);
            for down_item_id in &down_items {
                Self::prune_down_subsumption(
                    opt_kpset_class_item,
                    *down_item_id,
                    subsumer_concept,
                    concepts,
                );
            }
            if let Some(candidate_concept) =
                Self::equivalent_candidate_concept(opt_kpset_class_item, subsumer_concept, concepts)
            {
                for down_item_id in down_items {
                    Self::prune_down_subsumption(
                        opt_kpset_class_item,
                        down_item_id,
                        candidate_concept,
                        concepts,
                    );
                }
            }
            true
        } else if invalided {
            let not_subsumer_concept = opt_kpset_class_item
                .get_concept_satisfiable_test_item_container()[subsumer_item_id.index()]
            .get_testing_concept();
            let up_items = Self::propagation_parents(opt_kpset_class_item, item_id);
            for up_item_id in &up_items {
                Self::prune_up_not_subsumption(
                    opt_kpset_class_item,
                    *up_item_id,
                    not_subsumer_concept,
                    concepts,
                );
            }
            if let Some(candidate_concept) = Self::equivalent_candidate_concept(
                opt_kpset_class_item,
                not_subsumer_concept,
                concepts,
            ) {
                for up_item_id in up_items {
                    Self::prune_up_not_subsumption(
                        opt_kpset_class_item,
                        up_item_id,
                        candidate_concept,
                        concepts,
                    );
                }
            }
            true
        } else {
            false
        }
    }

    /// Port of `pruneDownSubsumption`.
    pub fn prune_down_subsumption(
        opt_kpset_class_item: &mut OptimizedKPSetClassOntologyClassificationItem,
        item_id: OptimizedKPSetClassTestingItemId,
        subsumer_concept: ConceptId,
        _concepts: &Arena<Concept>,
    ) -> bool {
        let Some(should_recurse) = opt_kpset_class_item
            .get_concept_satisfiable_test_item_mut(item_id)
            .and_then(|item| item.get_possible_subsumption_map(false))
            .and_then(|poss_subsum_map| {
                poss_subsum_map.get_mut(subsumer_concept).and_then(|data| {
                    if !data.is_subsumption_confirmed() {
                        data.set_subsumption_confirmed(true);
                        data.set_subsumption_updated(true);
                        Some(true)
                    } else {
                        None
                    }
                })
            })
        else {
            return false;
        };

        if should_recurse {
            Self::dec_remaining_possible_subsumption_testing_count(
                opt_kpset_class_item,
                item_id,
                subsumer_concept,
                true,
            );
            for down_item_id in Self::propagation_children(opt_kpset_class_item, item_id) {
                Self::prune_down_subsumption(
                    opt_kpset_class_item,
                    down_item_id,
                    subsumer_concept,
                    _concepts,
                );
            }
            return true;
        }
        false
    }

    /// Port of `pruneUpNotSubsumption`.
    pub fn prune_up_not_subsumption(
        opt_kpset_class_item: &mut OptimizedKPSetClassOntologyClassificationItem,
        item_id: OptimizedKPSetClassTestingItemId,
        not_subsumer_concept: ConceptId,
        _concepts: &Arena<Concept>,
    ) -> bool {
        let Some(should_recurse) = opt_kpset_class_item
            .get_concept_satisfiable_test_item_mut(item_id)
            .and_then(|item| item.get_possible_subsumption_map(false))
            .and_then(|poss_subsum_map| {
                poss_subsum_map
                    .get_mut(not_subsumer_concept)
                    .and_then(|data| {
                        if !data.is_subsumption_invalided() {
                            data.set_subsumption_invalid(true);
                            data.set_subsumption_updated(true);
                            Some(true)
                        } else {
                            None
                        }
                    })
            })
        else {
            return false;
        };

        if should_recurse {
            Self::dec_remaining_possible_subsumption_testing_count(
                opt_kpset_class_item,
                item_id,
                not_subsumer_concept,
                false,
            );
            for up_item_id in Self::propagation_parents(opt_kpset_class_item, item_id) {
                Self::prune_up_not_subsumption(
                    opt_kpset_class_item,
                    up_item_id,
                    not_subsumer_concept,
                    _concepts,
                );
            }
            return true;
        }
        false
    }

    fn insert_possible_class_subsumer(
        opt_kpset_class_item: &mut OptimizedKPSetClassOntologyClassificationItem,
        subsumed_item_id: OptimizedKPSetClassTestingItemId,
        poss_subsum_concept: ConceptId,
        concepts: &Arena<Concept>,
    ) -> Cint64 {
        let poss_subsum_item_id = opt_kpset_class_item.get_concept_satisfiable_test_item(
            poss_subsum_concept,
            false,
            concepts,
        );
        if poss_subsum_item_id.is_none() || poss_subsum_item_id == subsumed_item_id {
            return 0;
        }
        if opt_kpset_class_item.get_concept_satisfiable_test_item_container()
            [subsumed_item_id.index()]
        .has_subsumer_concept_item(poss_subsum_item_id)
        {
            return 0;
        }
        let subsumed_item = opt_kpset_class_item
            .get_concept_satisfiable_test_item_mut(subsumed_item_id)
            .expect("subsumed item exists");
        let poss_subsum_map = subsumed_item
            .get_possible_subsumption_map(true)
            .expect("created possible-subsumption map");
        if poss_subsum_map.contains(poss_subsum_concept) {
            return 0;
        }
        poss_subsum_map.insert(
            poss_subsum_concept,
            OptimizedKPSetClassPossibleSubsumptionData::new(poss_subsum_item_id),
        );
        poss_subsum_map.inc_remaining_possible_subsumption_count(1);
        1
    }

    /// Port of the `TELLCLASSPSEUDOMODELIDENTIFIERS` receive branch in
    /// `COptimizedKPSetClassSubsumptionClassifierThread`.
    pub fn process_pseudo_model_identifier_message(
        &mut self,
        opt_kpset_class_item: &mut OptimizedKPSetClassOntologyClassificationItem,
        pm_message_data: &ClassificationPseudoModelIdentifierMessageData,
        concepts: &Arena<Concept>,
    ) -> bool {
        self.stat_processed_pseudo_model_message_count += 1;

        let pm_concept = pm_message_data.get_pseudo_model_concept();
        let pm_memory_pools = pm_message_data.get_pseudo_model_memory_pools();
        let pm_hash = pm_message_data.get_pseudo_model_hash().clone();

        let pm_item_id =
            opt_kpset_class_item.get_concept_satisfiable_test_item(pm_concept, false, concepts);
        let Some(pm_item) = opt_kpset_class_item.get_concept_satisfiable_test_item_mut(pm_item_id)
        else {
            return false;
        };

        pm_item
            .get_class_pseudo_model_mut()
            .set_pseudo_model_hash(Some(pm_hash));
        pm_item.set_class_pseudo_model_initalized(true);
        opt_kpset_class_item.add_memory_pools(pm_memory_pools);

        true
    }

    /// Port of the classification message linker dispatch loop for the currently
    /// typed KPSet class message payloads.
    pub fn process_classification_message_data_linker(
        &mut self,
        opt_kpset_class_item: &mut OptimizedKPSetClassOntologyClassificationItem,
        message_data_linker: &ClassificationMessageDataLinker,
        concepts: &Arena<Concept>,
    ) -> bool {
        let mut processed_any = false;
        for message_data in message_data_linker.iter() {
            match message_data {
                ClassificationMessageDataPayload::ClassSubsumption(subsum_message_data) => {
                    processed_any |= self.process_class_subsumption_message(
                        opt_kpset_class_item,
                        subsum_message_data,
                        concepts,
                    );
                }
                ClassificationMessageDataPayload::InitializePossibleClassSubsumption(
                    poss_subsum_message_data,
                ) => {
                    processed_any |= self.process_initialize_possible_class_subsumption_message(
                        opt_kpset_class_item,
                        poss_subsum_message_data,
                        concepts,
                    );
                }
                ClassificationMessageDataPayload::UpdatePossibleClassSubsumption(
                    poss_subsum_message_data,
                ) => {
                    processed_any |= self.process_update_possible_class_subsumption_message(
                        opt_kpset_class_item,
                        poss_subsum_message_data,
                        concepts,
                    );
                }
                ClassificationMessageDataPayload::PseudoModelIdentifier(pm_message_data) => {
                    processed_any |= self.process_pseudo_model_identifier_message(
                        opt_kpset_class_item,
                        pm_message_data,
                        concepts,
                    );
                }
                ClassificationMessageDataPayload::Header(_) => {}
            }
        }
        processed_any
    }

    /// Port of both KPSet class branches that allocate
    /// `CSatisfiableTaskIndividualDependenceTrackingAdapter` with the ontology
    /// item's collector and a testing item marker (`nextSatTestItem` or
    /// `subsumedItem` in C++).
    pub fn set_satisfiable_task_individual_dependence_tracking_adapter(
        opt_kpset_class_item: &OptimizedKPSetClassOntologyClassificationItem,
        marker_item: &OptimizedKPSetClassTestingItem,
        sat_calc_job: &mut SatisfiableCalculationJob,
        calc_context: &mut CalculationAlgorithmContext,
    ) {
        let collector = opt_kpset_class_item.get_individual_dependence_tracking_collector();
        if collector.is_some() {
            let adapter = calc_context.alloc_individual_dependence_tracking_adapter(
                SatisfiableTaskIndividualDependenceTrackingAdapter::new(
                    collector,
                    marker_item.individual_dependence_tracking_marker(),
                ),
            );
            sat_calc_job.set_satisfiable_task_individual_dependence_tracking_adapter(adapter);
        }
    }

    /// Port of `fastPseudoModelSubsumptionClassPrecheckTest`.
    pub fn fast_pseudo_model_subsumption_class_precheck_test(
        _opt_sub_class_item: &OptimizedKPSetClassOntologyClassificationItem,
        subsumed_item: &OptimizedKPSetClassTestingItem,
        subsumer_item: &OptimizedKPSetClassTestingItem,
        is_subsumption_flag: Option<&mut bool>,
    ) -> bool {
        if subsumed_item.is_class_pseudo_model_initalized()
            && subsumer_item.is_class_pseudo_model_initalized()
        {
            let Some(subsumed_pm_hash) = subsumed_item
                .get_class_pseudo_model()
                .get_pseudo_model_hash()
            else {
                return false;
            };
            let Some(subsumer_pm_hash) = subsumer_item
                .get_class_pseudo_model()
                .get_pseudo_model_hash()
            else {
                return false;
            };
            let Some(subsumed_pm_data) = subsumed_pm_hash.get_pseudo_model_data(0) else {
                return false;
            };
            let Some(subsumer_pm_data) = subsumer_pm_hash.get_pseudo_model_data(0) else {
                return false;
            };

            let is_subsum_possible = Self::is_pseudo_model_subsumer_possible(
                _opt_sub_class_item,
                subsumed_pm_data,
                subsumed_pm_hash,
                subsumer_pm_data,
                subsumer_pm_hash,
            );
            if !is_subsum_possible {
                if let Some(is_subsumption_flag) = is_subsumption_flag {
                    *is_subsumption_flag = false;
                }
                return true;
            }
        }
        false
    }

    /// Port of `isPseudoModelSubsumerPossible`.
    pub fn is_pseudo_model_subsumer_possible(
        _opt_sub_class_item: &OptimizedKPSetClassOntologyClassificationItem,
        subsumed_pm_data: &ClassificationClassPseudoModelData,
        subsumed_pm_hash: &ClassificationClassPseudoModelHash,
        subsumer_pm_data: &ClassificationClassPseudoModelData,
        subsumer_pm_hash: &ClassificationClassPseudoModelHash,
    ) -> bool {
        if subsumed_pm_data.has_valid_concept_map() && subsumer_pm_data.has_valid_concept_map() {
            let subsumed_con_map = subsumed_pm_data.get_pseudo_model_concept_map();
            let subsumer_con_map = subsumer_pm_data.get_pseudo_model_concept_map();
            if let (Some(subsumed_con_map), Some(subsumer_con_map)) =
                (subsumed_con_map, subsumer_con_map)
            {
                let subsumed_concepts: Vec<_> = subsumed_con_map.iter().collect();
                let subsumer_concepts: Vec<_> = subsumer_con_map.iter().collect();
                let mut it1 = 0;
                let mut it2 = 0;
                while it1 < subsumer_concepts.len() && it2 < subsumed_concepts.len() {
                    let (concept1, concept1_data) = subsumer_concepts[it1];
                    let (concept2, _) = subsumed_concepts[it2];
                    let con1_tag = concept1.raw;
                    let con2_tag = concept2.raw;
                    if con2_tag < con1_tag {
                        it2 += 1;
                    } else if con2_tag == con1_tag {
                        it1 += 1;
                        it2 += 1;
                    } else if con2_tag > con1_tag {
                        if concept1_data.is_deterministic() {
                            return false;
                        }
                        it1 += 1;
                    }
                }
                while it1 < subsumer_concepts.len() {
                    if subsumer_concepts[it1].1.is_deterministic() {
                        return false;
                    }
                    it1 += 1;
                }
            }
        }

        if subsumed_pm_data.has_valid_role_map() && subsumer_pm_data.has_valid_role_map() {
            let subsumed_role_map = subsumed_pm_data.get_pseudo_model_role_map();
            let subsumer_role_map = subsumer_pm_data.get_pseudo_model_role_map();
            if let (Some(subsumed_role_map), Some(subsumer_role_map)) =
                (subsumed_role_map, subsumer_role_map)
            {
                let subsumed_roles: Vec<_> = subsumed_role_map.iter().collect();
                let subsumer_roles: Vec<_> = subsumer_role_map.iter().collect();
                let mut it1 = 0;
                let mut it2 = 0;
                while it1 < subsumer_roles.len() && it2 < subsumed_roles.len() {
                    let (role1, role1_data) = subsumer_roles[it1];
                    let (role2, role2_data) = subsumed_roles[it2];
                    let role1_tag = role1.raw;
                    let role2_tag = role2.raw;
                    if role2_tag < role1_tag {
                        it2 += 1;
                    } else if role2_tag == role1_tag {
                        if !role1_data.is_possible_subsumer_of(role2_data) {
                            return false;
                        }
                        let succ1_id = role1_data.get_successor_model_id();
                        let succ2_id = role2_data.get_successor_model_id();
                        let succ1_model_data = subsumer_pm_hash.get_pseudo_model_data(succ1_id);
                        let succ2_model_data = subsumed_pm_hash.get_pseudo_model_data(succ2_id);
                        if let (Some(succ1_model_data), Some(succ2_model_data)) =
                            (succ1_model_data, succ2_model_data)
                        {
                            if !Self::is_pseudo_model_subsumer_possible(
                                _opt_sub_class_item,
                                succ2_model_data,
                                subsumed_pm_hash,
                                succ1_model_data,
                                subsumer_pm_hash,
                            ) {
                                return false;
                            }
                        }
                        it1 += 1;
                        it2 += 1;
                    } else if role2_tag > role1_tag {
                        if role1_data.is_deterministic() {
                            return false;
                        }
                        it1 += 1;
                    }
                }
                while it1 < subsumer_roles.len() {
                    if subsumer_roles[it1].1.is_deterministic() {
                        return false;
                    }
                    it1 += 1;
                }
            }
        }
        true
    }
}

/// Port of the individual-dependence adapter setup branches in
/// `COptimizedKPSetRoleSubsumptionClassifierThread`.
#[derive(Debug, Clone)]
pub struct OptimizedKPSetRoleSubsumptionClassifierThread {
    stat_satisfiable_tested_count: Cint64,
    stat_received_callback_count: Cint64,
    stat_interpreted_subsumption_calculation_count: Cint64,
    stat_ordered_subsumption_calculation_count: Cint64,
    stat_created_calculation_task_count: Cint64,
    conf_poss_subsum_calc_order_top_down: bool,
    conf_poss_subsum_calc_order_bottom_up: bool,
}

impl Default for OptimizedKPSetRoleSubsumptionClassifierThread {
    fn default() -> Self {
        Self {
            stat_satisfiable_tested_count: 0,
            stat_received_callback_count: 0,
            stat_interpreted_subsumption_calculation_count: 0,
            stat_ordered_subsumption_calculation_count: 0,
            stat_created_calculation_task_count: 0,
            conf_poss_subsum_calc_order_top_down: true,
            conf_poss_subsum_calc_order_bottom_up: false,
        }
    }
}

impl OptimizedKPSetRoleSubsumptionClassifierThread {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn get_satisfiable_tested_count(&self) -> Cint64 {
        self.stat_satisfiable_tested_count
    }

    pub fn get_received_callback_count(&self) -> Cint64 {
        self.stat_received_callback_count
    }

    pub fn get_interpreted_subsumption_calculation_count(&self) -> Cint64 {
        self.stat_interpreted_subsumption_calculation_count
    }

    pub fn get_ordered_subsumption_calculation_count(&self) -> Cint64 {
        self.stat_ordered_subsumption_calculation_count
    }

    pub fn get_created_calculation_task_count(&self) -> Cint64 {
        self.stat_created_calculation_task_count
    }

    pub fn set_possible_subsumption_calculation_order(
        &mut self,
        top_down: bool,
        bottom_up: bool,
    ) -> &mut Self {
        self.conf_poss_subsum_calc_order_top_down = top_down;
        self.conf_poss_subsum_calc_order_bottom_up = bottom_up;
        self
    }

    /// Port of the concrete allocation part of
    /// `createTemporaryRoleClassificationOntology`.
    ///
    /// The outer `CConcreteOntology` clone/configuration and complex-role
    /// automata preprocessor are scheduler/preprocess surfaces still outside this
    /// classifier slice; this method ports the temporary individuals/concepts and
    /// the item/hash field installation that `calculateSatisfiable` and
    /// `calculateSubsumption` consume.
    pub fn create_temporary_role_classification_ontology(
        &mut self,
        opt_kpset_role_item: &mut OptimizedKPSetRoleOntologyClassificationItem,
        ontology_arenas: &mut OntologyArenas,
        temporary_role_classification_ontology: Cint64,
    ) -> &mut Self {
        if opt_kpset_role_item.get_temporary_role_classification_ontology() != INVALID {
            return self;
        }

        let tmp_indi_prop =
            ontology_arenas.alloc_individual(Individual::new(ontology_arenas.individual_count()));
        ontology_arenas
            .individual_mut(tmp_indi_prop)
            .set_temporary_fake_individual(true);
        let tmp_indi_marker =
            ontology_arenas.alloc_individual(Individual::new(ontology_arenas.individual_count()));
        ontology_arenas
            .individual_mut(tmp_indi_marker)
            .set_temporary_fake_individual(true);

        opt_kpset_role_item
            .set_temporary_marker_individual(tmp_indi_marker)
            .set_temporary_propagation_individual(tmp_indi_prop);

        let mut all_prop_concept = Concept::new();
        all_prop_concept.set_operator_code(CCAND);
        let all_prop_concept = ontology_arenas.alloc_concept(all_prop_concept);
        let mut top_concept = Concept::new();
        top_concept.set_operator_code(CCTOP);
        let top_concept = ontology_arenas.alloc_concept(top_concept);
        let mut top_data_range_concept = Concept::new();
        top_data_range_concept.set_operator_code(CCTOP);
        let top_data_range_concept = ontology_arenas.alloc_concept(top_data_range_concept);

        let bottom_role_item = opt_kpset_role_item.get_bottom_role_satisfiable_test_item();
        let role_item_ids: Vec<OptimizedKPSetRoleTestingItemId> = (0..opt_kpset_role_item
            .get_role_satisfiable_test_item_list()
            .len())
            .map(|index| OptimizedKPSetRoleTestingItemId::new(index as Cint64))
            .collect();

        for role_item_id in role_item_ids {
            if role_item_id == bottom_role_item {
                continue;
            }
            let Some(role_item) =
                opt_kpset_role_item.get_role_satisfiable_test_item_mut(role_item_id)
            else {
                continue;
            };
            let role = role_item.get_testing_role();

            let mut marker_concept = Concept::new();
            marker_concept.set_operator_code(CCMARKER).set_role(role);
            let marker_concept = ontology_arenas.alloc_concept(marker_concept);

            let mut exist_concept = Concept::new();
            exist_concept
                .set_operator_code(CCVALUE)
                .set_role(role)
                .set_nominal_individual(tmp_indi_marker);
            let exist_concept = ontology_arenas.alloc_concept(exist_concept);

            let mut prop_concept = Concept::new();
            prop_concept
                .set_operator_code(CCALL)
                .set_role(role)
                .add_operand_linker(marker_concept, false)
                .inc_operand_count(1);
            let prop_concept = ontology_arenas.alloc_concept(prop_concept);

            ontology_arenas
                .concept_mut(all_prop_concept)
                .add_operand_linker(prop_concept, false)
                .inc_operand_count(1);

            role_item
                .set_temporary_marker_concept(marker_concept)
                .set_temporary_exist_concept(exist_concept)
                .set_temporary_propagation_concept(prop_concept);
            opt_kpset_role_item
                .get_marker_concept_instances_item_hash_mut()
                .insert(marker_concept, role_item_id);
        }

        opt_kpset_role_item
            .set_temporary_role_classification_ontology(temporary_role_classification_ontology)
            .set_temporary_all_propagation_concept(all_prop_concept)
            .set_temporary_top_concept(top_concept)
            .set_temporary_top_data_range_concept(top_data_range_concept);
        self
    }

    /// Port of the post-precheck work-item registration block in role
    /// `calculateSatisfiable`.
    pub fn register_satisfiable_calculation_job(
        &mut self,
        opt_kpset_role_item: &mut OptimizedKPSetRoleOntologyClassificationItem,
        next_sat_test_item_id: OptimizedKPSetRoleTestingItemId,
        sat_calc_job: Cint64,
    ) -> Option<PropertyClassificationComputationItem> {
        let role = opt_kpset_role_item
            .get_role_satisfiable_test_item_list()
            .get(next_sat_test_item_id.index())?
            .get_testing_role();
        opt_kpset_role_item
            .get_role_satisfiable_test_item_mut(next_sat_test_item_id)?
            .set_satisfiable_test_ordered(true);

        let work_item = PropertyClassificationComputationItem::new_satisfiable(sat_calc_job, role);
        opt_kpset_role_item.insert_computation_item(sat_calc_job, work_item.clone());
        opt_kpset_role_item.inc_current_calculating_count(1);
        self.stat_created_calculation_task_count += 1;
        Some(work_item)
    }

    /// Port of the adjacent
    /// `setSatisfiableClassificationRoleMarkedMessageAdapter(...)` call in role
    /// `calculateSatisfiable`.
    pub fn register_satisfiable_calculation_job_with_role_marked_adapter(
        &mut self,
        opt_kpset_role_item: &mut OptimizedKPSetRoleOntologyClassificationItem,
        next_sat_test_item_id: OptimizedKPSetRoleTestingItemId,
        sat_calc_job_handle: Cint64,
        sat_calc_job: &mut SatisfiableCalculationJob,
        propagation_individual: IndividualId,
        marker_individual: IndividualId,
        testing_ontology: Cint64,
        classification_message_data_observer: Cint64,
        calc_context: &mut CalculationAlgorithmContext,
    ) -> Option<PropertyClassificationComputationItem> {
        let work_item = self.register_satisfiable_calculation_job(
            opt_kpset_role_item,
            next_sat_test_item_id,
            sat_calc_job_handle,
        )?;
        let adapter = SatisfiableTaskClassificationRoleMarkedMessageAdapter::new(
            work_item.get_satisfiable_tested_role(),
            propagation_individual,
            marker_individual,
            testing_ontology,
            classification_message_data_observer,
        );
        let role_marked_message_adapter =
            calc_context.alloc_classification_role_marked_message_adapter(adapter);
        sat_calc_job.set_satisfiable_classification_role_marked_message_adapter(
            role_marked_message_adapter,
        );
        Some(work_item)
    }

    /// Port of the role `calculateSatisfiable` job-generator calls around the
    /// role-marked adapter installation.
    pub fn register_satisfiable_calculation_job_with_role_setup(
        &mut self,
        opt_kpset_role_item: &mut OptimizedKPSetRoleOntologyClassificationItem,
        next_sat_test_item_id: OptimizedKPSetRoleTestingItemId,
        sat_calc_job_handle: Cint64,
        sat_calc_job: &mut SatisfiableCalculationJob,
        testing_ontology: Cint64,
        classification_message_data_observer: Cint64,
        calc_context: &mut CalculationAlgorithmContext,
    ) -> Option<PropertyClassificationComputationItem> {
        let exist_concept = opt_kpset_role_item
            .get_role_satisfiable_test_item_list()
            .get(next_sat_test_item_id.index())?
            .get_temporary_exist_concept();
        let all_prop_concept = opt_kpset_role_item.get_temporary_all_propagation_concept();
        let propagation_individual = opt_kpset_role_item.get_temporary_propagation_individual();
        let marker_individual = opt_kpset_role_item.get_temporary_marker_individual();
        let top_concept = opt_kpset_role_item.get_temporary_role_setup_top_concept();

        let work_item = self.register_satisfiable_calculation_job_with_role_marked_adapter(
            opt_kpset_role_item,
            next_sat_test_item_id,
            sat_calc_job_handle,
            sat_calc_job,
            propagation_individual,
            marker_individual,
            testing_ontology,
            classification_message_data_observer,
            calc_context,
        )?;

        sat_calc_job
            .add_satisfiable_calculation_job_concept_assertion(
                exist_concept,
                false,
                propagation_individual,
            )
            .add_satisfiable_calculation_job_concept_assertion(
                all_prop_concept,
                false,
                propagation_individual,
            )
            .add_satisfiable_calculation_job_concept_assertion(
                top_concept,
                false,
                marker_individual,
            );

        Some(work_item)
    }

    /// Port of the post-precheck work-item registration block in role
    /// `calculateSubsumption`.
    pub fn register_subsumption_calculation_job(
        &mut self,
        opt_kpset_role_item: &mut OptimizedKPSetRoleOntologyClassificationItem,
        subsumed_item_id: OptimizedKPSetRoleTestingItemId,
        poss_subsumer_item_id: OptimizedKPSetRoleTestingItemId,
        sat_calc_job: Cint64,
    ) -> Option<PropertyClassificationComputationItem> {
        self.stat_ordered_subsumption_calculation_count += 1;
        let subsumed_role = opt_kpset_role_item
            .get_role_satisfiable_test_item_list()
            .get(subsumed_item_id.index())?
            .get_testing_role();
        let subsumer_role = opt_kpset_role_item
            .get_role_satisfiable_test_item_list()
            .get(poss_subsumer_item_id.index())?
            .get_testing_role();
        let work_item = PropertyClassificationComputationItem::new_subsumption(
            sat_calc_job,
            subsumer_role,
            subsumed_role,
        );
        opt_kpset_role_item.insert_computation_item(sat_calc_job, work_item.clone());
        opt_kpset_role_item.inc_current_calculating_count(1);
        opt_kpset_role_item.inc_calculated_possible_subsumer_count(1);
        self.stat_created_calculation_task_count += 1;
        Some(work_item)
    }

    /// Port of the role `calculateSubsumption` job-generator calls.
    pub fn register_subsumption_calculation_job_with_role_setup(
        &mut self,
        opt_kpset_role_item: &mut OptimizedKPSetRoleOntologyClassificationItem,
        subsumed_item_id: OptimizedKPSetRoleTestingItemId,
        poss_subsumer_item_id: OptimizedKPSetRoleTestingItemId,
        sat_calc_job_handle: Cint64,
        sat_calc_job: &mut SatisfiableCalculationJob,
    ) -> Option<PropertyClassificationComputationItem> {
        let subsumed_item = opt_kpset_role_item
            .get_role_satisfiable_test_item_list()
            .get(subsumed_item_id.index())?;
        let exist_concept = subsumed_item.get_temporary_exist_concept();
        let poss_subsumer_item = opt_kpset_role_item
            .get_role_satisfiable_test_item_list()
            .get(poss_subsumer_item_id.index())?;
        let propagation_concept = poss_subsumer_item.get_temporary_propagation_concept();
        let marker_concept = poss_subsumer_item.get_temporary_marker_concept();
        let propagation_individual = opt_kpset_role_item.get_temporary_propagation_individual();
        let marker_individual = opt_kpset_role_item.get_temporary_marker_individual();
        let top_concept = opt_kpset_role_item.get_temporary_role_setup_top_concept();

        let work_item = self.register_subsumption_calculation_job(
            opt_kpset_role_item,
            subsumed_item_id,
            poss_subsumer_item_id,
            sat_calc_job_handle,
        )?;

        sat_calc_job
            .add_satisfiable_calculation_job_concept_assertion(
                exist_concept,
                false,
                propagation_individual,
            )
            .add_satisfiable_calculation_job_concept_assertion(
                propagation_concept,
                false,
                propagation_individual,
            )
            .add_satisfiable_calculation_job_concept_assertion(
                marker_concept,
                true,
                marker_individual,
            )
            .add_satisfiable_calculation_job_concept_assertion(
                top_concept,
                false,
                marker_individual,
            );

        Some(work_item)
    }

    fn dec_remaining_possible_subsumption_testing_count(
        opt_kpset_role_item: &mut OptimizedKPSetRoleOntologyClassificationItem,
        item_id: OptimizedKPSetRoleTestingItemId,
        poss_subsum_role: RoleId,
        subsumption_confirmed: bool,
    ) {
        if subsumption_confirmed {
            opt_kpset_role_item.inc_true_possible_subsumer_count(1);
        } else {
            opt_kpset_role_item.inc_false_possible_subsumer_count(1);
        }
        opt_kpset_role_item.dec_remaining_possible_subsumption_tests_count(1);
        if let Some(poss_subsum_map) = opt_kpset_role_item
            .get_role_satisfiable_test_item_mut(item_id)
            .and_then(|item| item.get_possible_subsumption_map(false))
        {
            if poss_subsum_map.contains(poss_subsum_role) {
                poss_subsum_map.dec_remaining_possible_subsumption_count(1);
            }
        }
    }

    fn propagation_children(
        opt_kpset_role_item: &OptimizedKPSetRoleOntologyClassificationItem,
        item_id: OptimizedKPSetRoleTestingItemId,
    ) -> Vec<OptimizedKPSetRoleTestingItemId> {
        opt_kpset_role_item.get_role_satisfiable_test_item_list()[item_id.index()]
            .get_down_propagation_item_set()
            .iter()
            .copied()
            .collect()
    }

    fn propagation_parents(
        opt_kpset_role_item: &OptimizedKPSetRoleOntologyClassificationItem,
        item_id: OptimizedKPSetRoleTestingItemId,
    ) -> Vec<OptimizedKPSetRoleTestingItemId> {
        opt_kpset_role_item.get_role_satisfiable_test_item_list()[item_id.index()]
            .get_up_propagation_item_set()
            .iter()
            .copied()
            .collect()
    }

    /// Port of role `propagateDownSubsumption`.
    pub fn propagate_down_subsumption(
        opt_kpset_role_item: &mut OptimizedKPSetRoleOntologyClassificationItem,
        item_id: OptimizedKPSetRoleTestingItemId,
        subsumer_item_id: OptimizedKPSetRoleTestingItemId,
    ) -> bool {
        let mut propagated = false;
        for down_item_id in Self::propagation_children(opt_kpset_role_item, item_id) {
            let should_add = down_item_id != subsumer_item_id
                && !opt_kpset_role_item.get_role_satisfiable_test_item_list()[down_item_id.index()]
                    .has_subsumer_role_item(subsumer_item_id);
            if should_add {
                opt_kpset_role_item
                    .get_role_satisfiable_test_item_mut(down_item_id)
                    .expect("down-propagation role item exists")
                    .add_subsumer_role_item(subsumer_item_id);
                Self::propagate_down_subsumption(
                    opt_kpset_role_item,
                    down_item_id,
                    subsumer_item_id,
                );
                propagated = true;
            }
        }
        propagated
    }

    /// Port of role `prunePossibleSubsumptions`.
    pub fn prune_possible_subsumptions(
        opt_kpset_role_item: &mut OptimizedKPSetRoleOntologyClassificationItem,
        item_id: OptimizedKPSetRoleTestingItemId,
        poss_subsum_role: RoleId,
    ) -> bool {
        let Some((confirmed, invalided, subsumer_item_id)) = opt_kpset_role_item
            .get_role_satisfiable_test_item_mut(item_id)
            .and_then(|item| item.get_possible_subsumption_map(false))
            .and_then(|poss_subsum_map| {
                poss_subsum_map.get_mut(poss_subsum_role).and_then(|data| {
                    if data.is_update_required() {
                        data.set_subsumption_updated(true);
                        Some((
                            data.is_subsumption_confirmed(),
                            data.is_subsumption_invalided(),
                            data.get_testing_item(),
                        ))
                    } else {
                        None
                    }
                })
            })
        else {
            return false;
        };

        Self::dec_remaining_possible_subsumption_testing_count(
            opt_kpset_role_item,
            item_id,
            poss_subsum_role,
            true,
        );

        if confirmed {
            let subsumer_role = opt_kpset_role_item.get_role_satisfiable_test_item_list()
                [subsumer_item_id.index()]
            .get_testing_role();
            for down_item_id in Self::propagation_children(opt_kpset_role_item, item_id) {
                Self::prune_down_subsumption(opt_kpset_role_item, down_item_id, subsumer_role);
            }
            true
        } else if invalided {
            let not_subsumer_role = opt_kpset_role_item.get_role_satisfiable_test_item_list()
                [subsumer_item_id.index()]
            .get_testing_role();
            for up_item_id in Self::propagation_parents(opt_kpset_role_item, item_id) {
                Self::prune_up_not_subsumption(opt_kpset_role_item, up_item_id, not_subsumer_role);
            }
            true
        } else {
            false
        }
    }

    /// Port of role `pruneDownSubsumption`.
    pub fn prune_down_subsumption(
        opt_kpset_role_item: &mut OptimizedKPSetRoleOntologyClassificationItem,
        item_id: OptimizedKPSetRoleTestingItemId,
        subsumer_role: RoleId,
    ) -> bool {
        let Some(should_recurse) = opt_kpset_role_item
            .get_role_satisfiable_test_item_mut(item_id)
            .and_then(|item| item.get_possible_subsumption_map(false))
            .and_then(|poss_subsum_map| {
                poss_subsum_map.get_mut(subsumer_role).and_then(|data| {
                    if !data.is_subsumption_confirmed() {
                        data.set_subsumption_confirmed(true);
                        data.set_subsumption_updated(true);
                        Some(true)
                    } else {
                        None
                    }
                })
            })
        else {
            return false;
        };

        if should_recurse {
            Self::dec_remaining_possible_subsumption_testing_count(
                opt_kpset_role_item,
                item_id,
                subsumer_role,
                true,
            );
            for down_item_id in Self::propagation_children(opt_kpset_role_item, item_id) {
                Self::prune_down_subsumption(opt_kpset_role_item, down_item_id, subsumer_role);
            }
            return true;
        }
        false
    }

    /// Port of role `pruneUpNotSubsumption`.
    pub fn prune_up_not_subsumption(
        opt_kpset_role_item: &mut OptimizedKPSetRoleOntologyClassificationItem,
        item_id: OptimizedKPSetRoleTestingItemId,
        not_subsumer_role: RoleId,
    ) -> bool {
        let Some(should_recurse) = opt_kpset_role_item
            .get_role_satisfiable_test_item_mut(item_id)
            .and_then(|item| item.get_possible_subsumption_map(false))
            .and_then(|poss_subsum_map| {
                poss_subsum_map.get_mut(not_subsumer_role).and_then(|data| {
                    if !data.is_subsumption_invalided() {
                        data.set_subsumption_invalid(true);
                        data.set_subsumption_updated(true);
                        Some(true)
                    } else {
                        None
                    }
                })
            })
        else {
            return false;
        };

        if should_recurse {
            Self::dec_remaining_possible_subsumption_testing_count(
                opt_kpset_role_item,
                item_id,
                not_subsumer_role,
                false,
            );
            for up_item_id in Self::propagation_parents(opt_kpset_role_item, item_id) {
                Self::prune_up_not_subsumption(opt_kpset_role_item, up_item_id, not_subsumer_role);
            }
            return true;
        }
        false
    }

    /// Port of the queue/result part of
    /// `COptimizedKPSetRoleSubsumptionClassifierThread::interpreteSatisfiableResult`.
    ///
    /// The role-hierarchy mutation in the unsatisfiable branch remains with the
    /// not-yet-ported hierarchy layer; the item state, running counter,
    /// satisfiable-role list, successor flags, predecessor decrement, and
    /// next/next-candidate queues are updated at the upstream call point.
    pub fn interprete_satisfiable_result(
        &mut self,
        opt_kpset_role_item: &mut OptimizedKPSetRoleOntologyClassificationItem,
        satisfiable_role: RoleId,
        is_satis: bool,
    ) -> bool {
        self.stat_satisfiable_tested_count += 1;
        opt_kpset_role_item.dec_running_satisfiable_tests_count(1);

        let sat_tested_item_id =
            opt_kpset_role_item.get_role_satisfiable_test_item(satisfiable_role, false);
        if sat_tested_item_id.is_none() {
            return false;
        }

        let (subsumer_items, successor_items) = {
            let sat_tested_item = opt_kpset_role_item
                .get_role_satisfiable_test_item_mut(sat_tested_item_id)
                .expect("role satisfiable test item");
            sat_tested_item
                .set_satisfiable_tested(true)
                .set_satisfiable_tested_result(is_satis);
            (
                sat_tested_item.get_subsumer_role_item_list().to_vec(),
                sat_tested_item.get_successor_item_list().to_vec(),
            )
        };

        if is_satis {
            opt_kpset_role_item.add_satisfiable_role_item(sat_tested_item_id);
        }

        for succ_item_id in successor_items {
            let ready = {
                let succ_item = opt_kpset_role_item
                    .get_role_satisfiable_test_item_mut(succ_item_id)
                    .expect("successor role satisfiable test item");
                if !is_satis {
                    succ_item.set_result_unsatisfiable_derivated(true);
                } else {
                    for subsumer_item_id in &subsumer_items {
                        if succ_item_id != *subsumer_item_id {
                            succ_item.add_subsumer_role_item(*subsumer_item_id);
                        }
                    }
                }
                succ_item.dec_unprocessed_predecessor_items(1);
                succ_item.has_only_processed_predecessor_items()
            };
            if ready {
                opt_kpset_role_item
                    .get_next_satisfiable_testing_item_list_mut()
                    .push(succ_item_id);
            } else {
                opt_kpset_role_item
                    .get_next_candidate_satisfiable_testing_item_set_mut()
                    .insert(succ_item_id);
            }
        }

        false
    }

    /// Compatibility wrapper for the W276 satisfiable-branch slice. The full
    /// callback dispatcher is `interprete_test_results`.
    pub fn interprete_test_results_satisfiable_branch(
        &mut self,
        opt_kpset_role_item: &mut OptimizedKPSetRoleOntologyClassificationItem,
        test_result: &TestCalculatedCallbackEvent<PropertyClassificationComputationItem>,
    ) -> bool {
        self.interprete_test_results(opt_kpset_role_item, test_result)
    }

    /// Port of the current in-memory result-dispatch body in
    /// `COptimizedKPSetRoleSubsumptionClassifierThread::interpreteTestResults`.
    pub fn interprete_test_results(
        &mut self,
        opt_kpset_role_item: &mut OptimizedKPSetRoleOntologyClassificationItem,
        test_result: &TestCalculatedCallbackEvent<PropertyClassificationComputationItem>,
    ) -> bool {
        self.stat_received_callback_count += 1;

        let Some(work_item) = test_result.get_classification_work_item() else {
            return true;
        };

        opt_kpset_role_item.dec_current_calculating_count(1);
        if test_result.has_calculation_error() {
            opt_kpset_role_item.set_hierarchy_construction_failed();
        } else if work_item.is_role_satisfiable_test() {
            self.interprete_satisfiable_result(
                opt_kpset_role_item,
                work_item.get_satisfiable_tested_role(),
                test_result.get_test_result_satisfiable(),
            );
        } else if work_item.is_role_subsumption_test() {
            self.interprete_subsumption_result(
                opt_kpset_role_item,
                work_item.get_subsumed_tested_role(),
                work_item.get_subsumer_tested_role(),
                !test_result.get_test_result_satisfiable(),
            );
        }
        opt_kpset_role_item.remove_computation_item_if_matching(
            test_result.get_satisfiable_calculation_job(),
            work_item,
        );
        opt_kpset_role_item
            .reuse_calculation_statistics_collection(test_result.get_used_statistics_collection());

        true
    }

    /// Port of
    /// `COptimizedKPSetRoleSubsumptionClassifierThread::interpreteSubsumptionResult`.
    pub fn interprete_subsumption_result(
        &mut self,
        opt_kpset_role_item: &mut OptimizedKPSetRoleOntologyClassificationItem,
        subsumed_role: RoleId,
        subsumer_role: RoleId,
        is_subsumption: bool,
    ) -> bool {
        self.stat_interpreted_subsumption_calculation_count += 1;
        opt_kpset_role_item.dec_running_possible_subsumption_tests_count(1);

        let subsumed_item_id =
            opt_kpset_role_item.get_role_satisfiable_test_item(subsumed_role, false);
        let subsumer_item_id =
            opt_kpset_role_item.get_role_satisfiable_test_item(subsumer_role, false);
        if subsumed_item_id.is_none() || subsumer_item_id.is_none() {
            return false;
        }

        let poss_subsum_map_exists = opt_kpset_role_item.get_role_satisfiable_test_item_list()
            [subsumed_item_id.index()]
        .get_possible_subsumption_map_ref()
        .is_some();
        let poss_subsum_data_exists = opt_kpset_role_item.get_role_satisfiable_test_item_list()
            [subsumed_item_id.index()]
        .get_possible_subsumption_map_ref()
        .and_then(|map| map.get(subsumer_role))
        .is_some();

        if is_subsumption {
            opt_kpset_role_item.inc_calculated_true_possible_subsumer_count(1);
            if poss_subsum_data_exists {
                opt_kpset_role_item
                    .get_role_satisfiable_test_item_mut(subsumed_item_id)
                    .expect("subsumed role item exists")
                    .get_possible_subsumption_map(false)
                    .expect("possible role subsumption map exists")
                    .get_mut(subsumer_role)
                    .expect("possible role subsumption data exists")
                    .set_subsumption_confirmed(true);
            }
            opt_kpset_role_item
                .get_role_satisfiable_test_item_mut(subsumed_item_id)
                .expect("subsumed role item exists")
                .add_subsumer_role_item(subsumer_item_id)
                .add_up_propagation_item(subsumer_item_id);
            opt_kpset_role_item
                .get_role_satisfiable_test_item_mut(subsumer_item_id)
                .expect("subsumer role item exists")
                .add_down_propagation_item(subsumed_item_id);
            Self::propagate_down_subsumption(
                opt_kpset_role_item,
                subsumed_item_id,
                subsumer_item_id,
            );
        } else {
            opt_kpset_role_item.inc_calculated_false_possible_subsumer_count(1);
            if poss_subsum_data_exists {
                opt_kpset_role_item
                    .get_role_satisfiable_test_item_mut(subsumed_item_id)
                    .expect("subsumed role item exists")
                    .get_possible_subsumption_map(false)
                    .expect("possible role subsumption map exists")
                    .get_mut(subsumer_role)
                    .expect("possible role subsumption data exists")
                    .set_subsumption_invalid(true);
            }
        }

        let update_required = opt_kpset_role_item.get_role_satisfiable_test_item_list()
            [subsumed_item_id.index()]
        .get_possible_subsumption_map_ref()
        .and_then(|map| map.get(subsumer_role))
        .map(|data| data.is_update_required())
        .unwrap_or(false);
        if update_required {
            Self::prune_possible_subsumptions(opt_kpset_role_item, subsumed_item_id, subsumer_role);
        }

        if self.conf_poss_subsum_calc_order_top_down
            && opt_kpset_role_item
                .get_current_possible_subsumption_testing_item_set()
                .contains(&subsumed_item_id)
        {
            opt_kpset_role_item
                .get_current_possible_subsumption_testing_item_set_mut()
                .remove(&subsumed_item_id);
            if poss_subsum_map_exists {
                let has_remaining = opt_kpset_role_item.get_role_satisfiable_test_item_list()
                    [subsumed_item_id.index()]
                .get_possible_subsumption_map_ref()
                .map(|map| map.has_remaining_possible_subsumptions())
                .unwrap_or(false);
                if has_remaining {
                    opt_kpset_role_item
                        .get_next_possible_subsumption_testing_item_list_mut()
                        .insert(0, subsumed_item_id);
                } else {
                    opt_kpset_role_item
                        .get_remaining_possible_subsumption_testing_set_mut()
                        .remove(&subsumed_item_id);
                }
            }
        }

        if self.conf_poss_subsum_calc_order_bottom_up
            && opt_kpset_role_item
                .get_current_possible_subsumption_testing_item_set()
                .contains(&subsumer_item_id)
        {
            opt_kpset_role_item
                .get_current_possible_subsumption_testing_item_set_mut()
                .remove(&subsumer_item_id);
            let has_remaining = opt_kpset_role_item.get_role_satisfiable_test_item_list()
                [subsumer_item_id.index()]
            .has_remaining_possible_subsumed_items();
            if has_remaining {
                opt_kpset_role_item
                    .get_next_possible_subsumption_testing_item_list_mut()
                    .insert(0, subsumer_item_id);

                let up_items = opt_kpset_role_item.get_role_satisfiable_test_item_list()
                    [subsumed_item_id.index()]
                .get_up_propagation_item_set()
                .iter()
                .copied()
                .collect::<Vec<_>>();
                let mut rem_list = opt_kpset_role_item.get_role_satisfiable_test_item_list()
                    [subsumer_item_id.index()]
                .get_possible_subsumer_list()
                .map(|list| list.to_vec())
                .unwrap_or_default();
                let rem_set = opt_kpset_role_item.get_role_satisfiable_test_item_list()
                    [subsumer_item_id.index()]
                .get_possible_subsumer_set_ref()
                .cloned()
                .unwrap_or_default();
                for up_item_id in up_items {
                    if rem_set.contains(&up_item_id) {
                        rem_list.insert(0, up_item_id);
                    }
                }
                opt_kpset_role_item
                    .get_role_satisfiable_test_item_mut(subsumer_item_id)
                    .expect("subsumer role item exists")
                    .set_possible_subsumed_list(rem_list);
            } else {
                opt_kpset_role_item
                    .get_remaining_possible_subsumption_testing_set_mut()
                    .remove(&subsumer_item_id);
            }
        }

        true
    }

    /// Port of both KPSet role branches that allocate
    /// `CSatisfiableTaskIndividualDependenceTrackingAdapter` with only the
    /// ontology item's collector. The C++ constructor overload passes no marker.
    pub fn set_satisfiable_task_individual_dependence_tracking_adapter(
        opt_kpset_role_item: &OptimizedKPSetRoleOntologyClassificationItem,
        sat_calc_job: &mut SatisfiableCalculationJob,
        calc_context: &mut CalculationAlgorithmContext,
    ) {
        let collector = opt_kpset_role_item.get_individual_dependence_tracking_collector();
        if collector.is_some() {
            let adapter = calc_context.alloc_individual_dependence_tracking_adapter(
                SatisfiableTaskIndividualDependenceTrackingAdapter::new(
                    collector,
                    IndividualDependenceTrackingMarkerId::NONE,
                ),
            );
            sat_calc_job.set_satisfiable_task_individual_dependence_tracking_adapter(adapter);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::model::concept::Concept;
    use super::super::model::op::CCEQCAND;
    use super::super::task::adapters::IndividualDependenceTrackingCollector;
    use super::*;

    #[test]
    fn subclass_satisfiable_testing_item_carries_marker_facet() {
        let mut ctx = CalculationAlgorithmContext::new();
        let marker = ctx
            .alloc_individual_dependence_tracking_marker(IndividualDependenceTrackingMarker::new());
        let concept = ConceptId::new(11);
        let mut item = OptimizedSubClassSatisfiableTestingItem::new();

        item.init_satisfiable_testing_item(concept, marker);

        assert_eq!(item.get_satisfiable_concept(), concept);
        assert_eq!(item.individual_dependence_tracking_marker(), marker);
        assert!(!ctx
            .individual_dependence_tracking_marker(marker)
            .has_individual_dependence_tracked());
    }

    #[test]
    fn subclass_classifier_sets_job_individual_dependence_adapter_when_collector_exists() {
        let mut ctx = CalculationAlgorithmContext::new();
        let collector = ctx.alloc_individual_dependence_tracking_collector(
            IndividualDependenceTrackingCollector::new(),
        );
        let marker = ctx
            .alloc_individual_dependence_tracking_marker(IndividualDependenceTrackingMarker::new());
        let mut ont_item = OptimizedSubClassOntologyClassificationItem::new();
        ont_item.set_individual_dependence_tracking_collector(collector);
        let mut next_item = OptimizedSubClassSatisfiableTestingItem::new();
        next_item.init_satisfiable_testing_item(ConceptId::new(17), marker);
        let mut job = SatisfiableCalculationJob::new();

        OptimizedSubClassSubsumptionClassifierThread::set_satisfiable_task_individual_dependence_tracking_adapter(
            &ont_item,
            &next_item,
            &mut job,
            &mut ctx,
        );

        let adapter = job.get_satisfiable_task_individual_dependence_tracking_adapter();
        assert!(adapter.is_some());
        let adapter_ref = ctx.individual_dependence_tracking_adapter(adapter);
        assert_eq!(
            adapter_ref.get_individual_dependence_tracking_observer(),
            collector
        );
        assert_eq!(
            adapter_ref.get_individual_dependence_tracking_marker(),
            marker
        );
    }

    #[test]
    fn subclass_classifier_leaves_job_without_adapter_when_collector_missing() {
        let mut ctx = CalculationAlgorithmContext::new();
        let marker = ctx
            .alloc_individual_dependence_tracking_marker(IndividualDependenceTrackingMarker::new());
        let ont_item = OptimizedSubClassOntologyClassificationItem::new();
        let mut next_item = OptimizedSubClassSatisfiableTestingItem::new();
        next_item.init_satisfiable_testing_item(ConceptId::new(19), marker);
        let mut job = SatisfiableCalculationJob::new();

        OptimizedSubClassSubsumptionClassifierThread::set_satisfiable_task_individual_dependence_tracking_adapter(
            &ont_item,
            &next_item,
            &mut job,
            &mut ctx,
        );

        assert!(job
            .get_satisfiable_task_individual_dependence_tracking_adapter()
            .is_none());
    }

    #[test]
    fn kpset_class_testing_item_carries_marker_facet() {
        let mut ctx = CalculationAlgorithmContext::new();
        let marker = ctx
            .alloc_individual_dependence_tracking_marker(IndividualDependenceTrackingMarker::new());
        let concept = ConceptId::new(23);
        let mut item = OptimizedKPSetClassTestingItem::new();

        item.init_kpset_class_testing_item(concept, marker);

        assert_eq!(item.get_testing_concept(), concept);
        assert_eq!(item.individual_dependence_tracking_marker(), marker);
        assert!(!ctx
            .individual_dependence_tracking_marker(marker)
            .has_individual_dependence_tracked());
    }

    #[test]
    fn kpset_class_classifier_sets_job_individual_dependence_adapter_for_next_sat_item() {
        let mut ctx = CalculationAlgorithmContext::new();
        let collector = ctx.alloc_individual_dependence_tracking_collector(
            IndividualDependenceTrackingCollector::new(),
        );
        let marker = ctx
            .alloc_individual_dependence_tracking_marker(IndividualDependenceTrackingMarker::new());
        let mut ont_item = OptimizedKPSetClassOntologyClassificationItem::new();
        ont_item.set_individual_dependence_tracking_collector(collector);
        let mut next_item = OptimizedKPSetClassTestingItem::new();
        next_item.init_kpset_class_testing_item(ConceptId::new(29), marker);
        let mut job = SatisfiableCalculationJob::new();

        OptimizedKPSetClassSubsumptionClassifierThread::set_satisfiable_task_individual_dependence_tracking_adapter(
            &ont_item,
            &next_item,
            &mut job,
            &mut ctx,
        );

        let adapter = job.get_satisfiable_task_individual_dependence_tracking_adapter();
        assert!(adapter.is_some());
        let adapter_ref = ctx.individual_dependence_tracking_adapter(adapter);
        assert_eq!(
            adapter_ref.get_individual_dependence_tracking_observer(),
            collector
        );
        assert_eq!(
            adapter_ref.get_individual_dependence_tracking_marker(),
            marker
        );
    }

    #[test]
    fn kpset_class_classifier_sets_job_individual_dependence_adapter_for_subsumed_item() {
        let mut ctx = CalculationAlgorithmContext::new();
        let collector = ctx.alloc_individual_dependence_tracking_collector(
            IndividualDependenceTrackingCollector::new(),
        );
        let marker = ctx
            .alloc_individual_dependence_tracking_marker(IndividualDependenceTrackingMarker::new());
        let mut ont_item = OptimizedKPSetClassOntologyClassificationItem::new();
        ont_item.set_individual_dependence_tracking_collector(collector);
        let mut subsumed_item = OptimizedKPSetClassTestingItem::new();
        subsumed_item.init_kpset_class_testing_item(ConceptId::new(31), marker);
        let mut job = SatisfiableCalculationJob::new();

        OptimizedKPSetClassSubsumptionClassifierThread::set_satisfiable_task_individual_dependence_tracking_adapter(
            &ont_item,
            &subsumed_item,
            &mut job,
            &mut ctx,
        );

        let adapter = job.get_satisfiable_task_individual_dependence_tracking_adapter();
        assert!(adapter.is_some());
        let adapter_ref = ctx.individual_dependence_tracking_adapter(adapter);
        assert_eq!(
            adapter_ref.get_individual_dependence_tracking_observer(),
            collector
        );
        assert_eq!(
            adapter_ref.get_individual_dependence_tracking_marker(),
            marker
        );
    }

    #[test]
    fn kpset_class_classifier_leaves_job_without_adapter_when_collector_missing() {
        let mut ctx = CalculationAlgorithmContext::new();
        let marker = ctx
            .alloc_individual_dependence_tracking_marker(IndividualDependenceTrackingMarker::new());
        let ont_item = OptimizedKPSetClassOntologyClassificationItem::new();
        let mut next_item = OptimizedKPSetClassTestingItem::new();
        next_item.init_kpset_class_testing_item(ConceptId::new(37), marker);
        let mut job = SatisfiableCalculationJob::new();

        OptimizedKPSetClassSubsumptionClassifierThread::set_satisfiable_task_individual_dependence_tracking_adapter(
            &ont_item,
            &next_item,
            &mut job,
            &mut ctx,
        );

        assert!(job
            .get_satisfiable_task_individual_dependence_tracking_adapter()
            .is_none());
    }

    #[test]
    fn kpset_role_classifier_sets_observer_only_job_individual_dependence_adapter_for_sat_item() {
        let mut ctx = CalculationAlgorithmContext::new();
        let collector = ctx.alloc_individual_dependence_tracking_collector(
            IndividualDependenceTrackingCollector::new(),
        );
        let mut ont_item = OptimizedKPSetRoleOntologyClassificationItem::new();
        ont_item.set_individual_dependence_tracking_collector(collector);
        let mut job = SatisfiableCalculationJob::new();

        OptimizedKPSetRoleSubsumptionClassifierThread::set_satisfiable_task_individual_dependence_tracking_adapter(
            &ont_item,
            &mut job,
            &mut ctx,
        );

        let adapter = job.get_satisfiable_task_individual_dependence_tracking_adapter();
        assert!(adapter.is_some());
        let adapter_ref = ctx.individual_dependence_tracking_adapter(adapter);
        assert_eq!(
            adapter_ref.get_individual_dependence_tracking_observer(),
            collector
        );
        assert!(adapter_ref
            .get_individual_dependence_tracking_marker()
            .is_none());
    }

    #[test]
    fn kpset_role_classifier_sets_observer_only_job_individual_dependence_adapter_for_subsumption_item(
    ) {
        let mut ctx = CalculationAlgorithmContext::new();
        let collector = ctx.alloc_individual_dependence_tracking_collector(
            IndividualDependenceTrackingCollector::new(),
        );
        let mut ont_item = OptimizedKPSetRoleOntologyClassificationItem::new();
        ont_item.set_individual_dependence_tracking_collector(collector);
        let mut job = SatisfiableCalculationJob::new();

        OptimizedKPSetRoleSubsumptionClassifierThread::set_satisfiable_task_individual_dependence_tracking_adapter(
            &ont_item,
            &mut job,
            &mut ctx,
        );

        let adapter = job.get_satisfiable_task_individual_dependence_tracking_adapter();
        assert!(adapter.is_some());
        let adapter_ref = ctx.individual_dependence_tracking_adapter(adapter);
        assert_eq!(
            adapter_ref.get_individual_dependence_tracking_observer(),
            collector
        );
        assert!(adapter_ref
            .get_individual_dependence_tracking_marker()
            .is_none());
    }

    #[test]
    fn kpset_role_classifier_leaves_job_without_adapter_when_collector_missing() {
        let mut ctx = CalculationAlgorithmContext::new();
        let ont_item = OptimizedKPSetRoleOntologyClassificationItem::new();
        let mut job = SatisfiableCalculationJob::new();

        OptimizedKPSetRoleSubsumptionClassifierThread::set_satisfiable_task_individual_dependence_tracking_adapter(
            &ont_item,
            &mut job,
            &mut ctx,
        );

        assert!(job
            .get_satisfiable_task_individual_dependence_tracking_adapter()
            .is_none());
    }

    #[test]
    fn kpset_class_possible_subsumption_data_tracks_known_unknown_and_update_state() {
        let item = OptimizedKPSetClassTestingItemId::new(3);
        let other_item = OptimizedKPSetClassTestingItemId::new(5);
        let mut data = OptimizedKPSetClassPossibleSubsumptionData::new(item);

        assert_eq!(data.get_class_item(), item);
        assert!(data.is_subsumption_unknown());
        assert!(!data.is_subsumption_known());
        assert!(!data.is_update_required());

        data.set_subsumption_confirmed(true);
        assert!(data.is_subsumption_confirmed());
        assert!(data.is_subsumption_known());
        assert!(data.is_update_required());

        data.set_subsumption_updated(true)
            .set_class_item(other_item)
            .set_subsumption_invalid(true);
        assert!(data.is_subsumption_updated());
        assert!(!data.is_update_required());
        assert!(data.is_subsumption_invalided());
        assert_eq!(data.get_class_item(), other_item);
    }

    #[test]
    fn kpset_role_possible_subsumption_data_tracks_known_unknown_and_update_state() {
        let item = OptimizedKPSetRoleTestingItemId::new(7);
        let other_item = OptimizedKPSetRoleTestingItemId::new(11);
        let mut data = OptimizedKPSetRolePossibleSubsumptionData::new(item);

        assert_eq!(data.get_testing_item(), item);
        assert!(data.is_subsumption_unknown());
        assert!(!data.is_subsumption_known());
        assert!(!data.is_update_required());

        data.set_subsumption_invalid(true);
        assert!(data.is_subsumption_invalided());
        assert!(data.is_subsumption_known());
        assert!(data.is_update_required());

        data.set_subsumption_updated(true)
            .set_testing_item(other_item)
            .set_subsumption_confirmed(true);
        assert!(data.is_subsumption_updated());
        assert!(!data.is_update_required());
        assert!(data.is_subsumption_confirmed());
        assert_eq!(data.get_testing_item(), other_item);
    }

    #[test]
    fn kpset_class_possible_subsumption_map_tracks_count_update_and_sorted_iterator() {
        let mut map = OptimizedKPSetClassPossibleSubsumptionMap::new();
        map.set_remaining_possible_subsumption_count(2)
            .inc_remaining_possible_subsumption_count(3)
            .dec_remaining_possible_subsumption_count(1)
            .set_possible_subsumption_update_required(true);
        assert_eq!(map.get_remaining_possible_subsumption_count(), 4);
        assert!(map.has_remaining_possible_subsumptions());
        assert!(map.is_possible_subsumption_update_required());

        let concept_high = ConceptId::new(20);
        let concept_low = ConceptId::new(10);
        map.insert(
            concept_high,
            OptimizedKPSetClassPossibleSubsumptionData::new(OptimizedKPSetClassTestingItemId::new(
                1,
            )),
        );
        map.insert(
            concept_low,
            OptimizedKPSetClassPossibleSubsumptionData::new(OptimizedKPSetClassTestingItemId::new(
                2,
            )),
        );

        {
            let mut it = map.get_iterator();
            assert!(it.has_next());
            assert_eq!(it.get_subsumption_concept(), concept_low);
            assert!(!it.confirm_subsumption());
            assert!(it.confirm_subsumption());
            assert!(it.is_subsumption_confirmed());
            assert!(it.move_next());
            assert!(it.has_next());
            assert_eq!(it.get_subsumption_concept(), concept_high);
            assert!(!it.invalidate_subsumption());
            assert!(it.invalidate_subsumption());
            assert!(it.is_subsumption_invalided());
            assert!(it.move_next());
            assert!(!it.has_next());
        }

        assert!(map
            .get(concept_low)
            .expect("concept-low data")
            .is_subsumption_confirmed());
        assert!(map
            .get(concept_high)
            .expect("concept-high data")
            .is_subsumption_invalided());
    }

    #[test]
    fn kpset_role_possible_subsumption_map_tracks_count_update_and_sorted_iterator() {
        let mut map = OptimizedKPSetRolePossibleSubsumptionMap::new();
        map.set_remaining_possible_subsumption_count(1)
            .inc_remaining_possible_subsumption_count(2)
            .dec_remaining_possible_subsumption_count(3);
        assert_eq!(map.get_remaining_possible_subsumption_count(), 0);
        assert!(!map.has_remaining_possible_subsumptions());
        assert!(!map.is_possible_subsumption_update_required());

        let role_high = RoleId::new(17);
        let role_low = RoleId::new(9);
        map.insert(
            role_high,
            OptimizedKPSetRolePossibleSubsumptionData::new(OptimizedKPSetRoleTestingItemId::new(4)),
        );
        map.insert(
            role_low,
            OptimizedKPSetRolePossibleSubsumptionData::new(OptimizedKPSetRoleTestingItemId::new(6)),
        );

        {
            let mut it = map.get_iterator();
            assert!(it.has_next());
            assert_eq!(it.get_subsumption_role(), role_low);
            assert!(!it.invalidate_subsumption());
            assert!(it.invalidate_subsumption());
            assert!(it.is_subsumption_invalided());
            assert!(it.move_next());
            assert!(it.has_next());
            assert_eq!(it.get_subsumption_role(), role_high);
            assert!(!it.confirm_subsumption());
            assert!(it.confirm_subsumption());
            assert!(it.is_subsumption_confirmed());
            assert!(it.move_next());
            assert!(!it.has_next());
        }

        assert!(map
            .get(role_low)
            .expect("role-low data")
            .is_subsumption_invalided());
        assert!(map
            .get(role_high)
            .expect("role-high data")
            .is_subsumption_confirmed());
    }

    #[test]
    fn class_pseudo_model_deterministic_flags_match_konclude_defaults() {
        let mut flag = ClassificationClassPseudoModelDeterministicFlag::new();
        assert!(!flag.is_deterministic());
        assert!(flag.is_non_deterministic());
        assert!(flag.set_deterministic(true));
        assert!(flag.is_deterministic());
        assert!(!flag.is_non_deterministic());
        assert!(!flag.set_deterministic(true));

        let default_concept_data = ClassificationClassPseudoModelConceptData::new();
        assert!(default_concept_data.is_non_deterministic());
        let deterministic_concept_data =
            ClassificationClassPseudoModelConceptData::new_with_deterministic(true);
        assert!(deterministic_concept_data.is_deterministic());
    }

    #[test]
    fn class_pseudo_model_role_data_tracks_bounds_and_subsumer_test() {
        let mut subsumer = ClassificationClassPseudoModelRoleData::new();
        let mut subsumed = ClassificationClassPseudoModelRoleData::new();

        assert_eq!(subsumer.get_lower_at_least_bound(), 0);
        assert_eq!(subsumer.get_upper_at_least_bound(), 0);
        assert_eq!(subsumer.get_lower_at_most_bound(), 0);
        assert_eq!(subsumer.get_upper_at_most_bound(), 0);
        assert_eq!(subsumer.get_successor_model_id(), 0);
        assert!(subsumer.is_possible_subsumer_of(&subsumed));

        assert!(subsumer.set_deterministic(true));
        assert!(subsumer.set_lower_at_least_bound(4));
        assert!(!subsumer.set_lower_at_least_bound(4));
        subsumed.set_upper_at_least_bound(3);
        assert!(!subsumer.is_possible_subsumer_of(&subsumed));

        subsumed.set_upper_at_least_bound(5);
        subsumer.set_upper_at_most_bound(2);
        subsumed.set_lower_at_most_bound(3);
        assert!(!subsumer.is_possible_subsumer_of(&subsumed));

        subsumer.set_upper_at_most_bound(4);
        subsumer.set_successor_model_id(17);
        assert!(subsumer.is_possible_subsumer_of(&subsumed));
        assert_eq!(subsumer.get_successor_model_id(), 17);
    }

    #[test]
    fn class_pseudo_model_hash_creates_copies_and_ordered_maps() {
        let mut hash = ClassificationClassPseudoModelHash::new();
        assert_eq!(hash.get_count(), 0);
        assert!(hash.get_pseudo_model_data(0).is_none());

        {
            let data = hash
                .get_pseudo_model_data_mut(0, true)
                .expect("created pseudo-model data");
            data.set_valid_concept_map(true).set_valid_role_map(true);
            data.get_pseudo_model_concept_map_mut(true)
                .expect("concept map")
                .entry(ConceptId::new(7))
                .set_deterministic(true);
            data.get_pseudo_model_concept_map_mut(true)
                .expect("concept map")
                .insert(
                    ConceptId::new(3),
                    ClassificationClassPseudoModelConceptData::new_with_deterministic(false),
                );
            data.get_pseudo_model_role_map_mut(true)
                .expect("role map")
                .entry(RoleId::new(5))
                .set_successor_model_id(11);
        }

        assert_eq!(hash.get_count(), 1);
        let data = hash.get_pseudo_model_data(0).expect("pseudo-model data");
        assert!(data.has_valid_concept_map());
        assert!(data.has_valid_role_map());
        let concept_ids: Vec<_> = data
            .get_pseudo_model_concept_map()
            .expect("concept map")
            .iter()
            .map(|(concept, _)| concept)
            .collect();
        assert_eq!(concept_ids, vec![ConceptId::new(3), ConceptId::new(7)]);

        let mut copied_hash = ClassificationClassPseudoModelHash::new();
        copied_hash.init_pseudo_model_hash(Some(&hash));
        copied_hash
            .get_pseudo_model_data_mut(0, true)
            .expect("copied data")
            .get_pseudo_model_concept_map_mut(true)
            .expect("copied concept map")
            .entry(ConceptId::new(7))
            .set_deterministic(false);

        assert!(hash
            .get_pseudo_model_data(0)
            .expect("original data")
            .get_pseudo_model_concept_map()
            .expect("original concept map")
            .get(ConceptId::new(7))
            .expect("original concept data")
            .is_deterministic());

        copied_hash.init_pseudo_model_hash(None);
        assert_eq!(copied_hash.get_count(), 0);
    }

    fn kpset_class_item_with_pseudo_model_hash(
        hash: ClassificationClassPseudoModelHash,
    ) -> OptimizedKPSetClassTestingItem {
        let mut item = OptimizedKPSetClassTestingItem::new();
        item.get_class_pseudo_model_mut()
            .set_pseudo_model_hash(Some(hash));
        item.set_class_pseudo_model_initalized(true);
        item
    }

    #[test]
    fn class_pseudo_model_precheck_prunes_missing_deterministic_subsumer_concept() {
        let mut subsumed_hash = ClassificationClassPseudoModelHash::new();
        subsumed_hash
            .get_pseudo_model_data_mut(0, true)
            .expect("subsumed data")
            .set_valid_concept_map(true)
            .get_pseudo_model_concept_map_mut(true)
            .expect("subsumed concept map")
            .insert(
                ConceptId::new(3),
                ClassificationClassPseudoModelConceptData::new_with_deterministic(true),
            );
        let mut subsumer_hash = ClassificationClassPseudoModelHash::new();
        subsumer_hash
            .get_pseudo_model_data_mut(0, true)
            .expect("subsumer data")
            .set_valid_concept_map(true)
            .get_pseudo_model_concept_map_mut(true)
            .expect("subsumer concept map")
            .insert(
                ConceptId::new(5),
                ClassificationClassPseudoModelConceptData::new_with_deterministic(true),
            );
        let subsumed_item = kpset_class_item_with_pseudo_model_hash(subsumed_hash);
        let subsumer_item = kpset_class_item_with_pseudo_model_hash(subsumer_hash);
        let ont_item = OptimizedKPSetClassOntologyClassificationItem::new();
        let mut is_subsumption = true;

        assert!(OptimizedKPSetClassSubsumptionClassifierThread::fast_pseudo_model_subsumption_class_precheck_test(
            &ont_item,
            &subsumed_item,
            &subsumer_item,
            Some(&mut is_subsumption),
        ));
        assert!(!is_subsumption);
    }

    #[test]
    fn class_pseudo_model_precheck_allows_missing_nondeterministic_subsumer_concept() {
        let mut subsumed_hash = ClassificationClassPseudoModelHash::new();
        subsumed_hash
            .get_pseudo_model_data_mut(0, true)
            .expect("subsumed data")
            .set_valid_concept_map(true)
            .get_pseudo_model_concept_map_mut(true)
            .expect("subsumed concept map")
            .insert(
                ConceptId::new(3),
                ClassificationClassPseudoModelConceptData::new_with_deterministic(true),
            );
        let mut subsumer_hash = ClassificationClassPseudoModelHash::new();
        subsumer_hash
            .get_pseudo_model_data_mut(0, true)
            .expect("subsumer data")
            .set_valid_concept_map(true)
            .get_pseudo_model_concept_map_mut(true)
            .expect("subsumer concept map")
            .insert(
                ConceptId::new(5),
                ClassificationClassPseudoModelConceptData::new_with_deterministic(false),
            );
        let subsumed_item = kpset_class_item_with_pseudo_model_hash(subsumed_hash);
        let subsumer_item = kpset_class_item_with_pseudo_model_hash(subsumer_hash);
        let ont_item = OptimizedKPSetClassOntologyClassificationItem::new();
        let mut is_subsumption = true;

        assert!(!OptimizedKPSetClassSubsumptionClassifierThread::fast_pseudo_model_subsumption_class_precheck_test(
            &ont_item,
            &subsumed_item,
            &subsumer_item,
            Some(&mut is_subsumption),
        ));
        assert!(is_subsumption);
    }

    #[test]
    fn class_pseudo_model_precheck_recurses_over_role_successor_models() {
        let role = RoleId::new(7);
        let mut subsumed_hash = ClassificationClassPseudoModelHash::new();
        {
            let data = subsumed_hash
                .get_pseudo_model_data_mut(0, true)
                .expect("subsumed root data");
            data.set_valid_role_map(true);
            let role_data = data
                .get_pseudo_model_role_map_mut(true)
                .expect("subsumed role map")
                .entry(role);
            role_data.set_deterministic(true);
            role_data.set_successor_model_id(2);
        }
        subsumed_hash
            .get_pseudo_model_data_mut(2, true)
            .expect("subsumed successor data")
            .set_valid_concept_map(true)
            .get_pseudo_model_concept_map_mut(true)
            .expect("subsumed successor concept map")
            .insert(
                ConceptId::new(11),
                ClassificationClassPseudoModelConceptData::new_with_deterministic(true),
            );

        let mut subsumer_hash = ClassificationClassPseudoModelHash::new();
        {
            let data = subsumer_hash
                .get_pseudo_model_data_mut(0, true)
                .expect("subsumer root data");
            data.set_valid_role_map(true);
            let role_data = data
                .get_pseudo_model_role_map_mut(true)
                .expect("subsumer role map")
                .entry(role);
            role_data.set_deterministic(true);
            role_data.set_successor_model_id(1);
        }
        subsumer_hash
            .get_pseudo_model_data_mut(1, true)
            .expect("subsumer successor data")
            .set_valid_concept_map(true)
            .get_pseudo_model_concept_map_mut(true)
            .expect("subsumer successor concept map")
            .insert(
                ConceptId::new(13),
                ClassificationClassPseudoModelConceptData::new_with_deterministic(true),
            );

        let subsumed_item = kpset_class_item_with_pseudo_model_hash(subsumed_hash);
        let subsumer_item = kpset_class_item_with_pseudo_model_hash(subsumer_hash);
        let ont_item = OptimizedKPSetClassOntologyClassificationItem::new();
        let mut is_subsumption = true;

        assert!(OptimizedKPSetClassSubsumptionClassifierThread::fast_pseudo_model_subsumption_class_precheck_test(
            &ont_item,
            &subsumed_item,
            &subsumer_item,
            Some(&mut is_subsumption),
        ));
        assert!(!is_subsumption);
    }

    #[test]
    fn class_pseudo_model_precheck_is_inconclusive_without_initialized_models() {
        let subsumed_item = OptimizedKPSetClassTestingItem::new();
        let mut subsumer_hash = ClassificationClassPseudoModelHash::new();
        subsumer_hash
            .get_pseudo_model_data_mut(0, true)
            .expect("subsumer data")
            .set_valid_concept_map(true);
        let subsumer_item = kpset_class_item_with_pseudo_model_hash(subsumer_hash);
        let ont_item = OptimizedKPSetClassOntologyClassificationItem::new();
        let mut is_subsumption = true;

        assert!(!OptimizedKPSetClassSubsumptionClassifierThread::fast_pseudo_model_subsumption_class_precheck_test(
            &ont_item,
            &subsumed_item,
            &subsumer_item,
            Some(&mut is_subsumption),
        ));
        assert!(is_subsumption);
    }

    #[test]
    fn kpset_class_ontology_item_get_or_create_resolves_eqcand_and_tracks_queues() {
        let mut concepts = Arena::new();
        let base_concept = concepts.push(Concept::new());
        let mut eqcand = Concept::new();
        eqcand
            .set_operator_code(CCEQCAND)
            .add_operand_linker(base_concept, false);
        let eqcand_concept = concepts.push(eqcand);
        let mut item = OptimizedKPSetClassOntologyClassificationItem::new();

        assert!(item
            .get_concept_satisfiable_test_item(eqcand_concept, false, &concepts)
            .is_none());
        let test_item = item.get_concept_satisfiable_test_item(eqcand_concept, true, &concepts);
        assert!(test_item.is_some());
        assert_eq!(
            item.get_concept_satisfiable_test_item(base_concept, false, &concepts),
            test_item
        );
        assert_eq!(item.get_concept_satisfiable_test_item_container().len(), 1);
        assert_eq!(
            item.get_concept_satisfiable_test_item_hash()
                .get(&base_concept),
            Some(&test_item)
        );

        item.init_top_bottom_satisfiable_testing_items(test_item, test_item)
            .add_satisfiable_concept_item(test_item);
        item.get_next_satisfiable_testing_item_list_mut()
            .push(test_item);
        item.get_next_candidate_satisfiable_testing_item_set_mut()
            .insert(test_item);
        item.get_remaining_candidate_satisfiable_testing_item_set_mut()
            .insert(test_item);
        item.get_next_possible_subsumption_testing_item_list_mut()
            .push(test_item);
        item.get_current_possible_subsumption_testing_item_set_mut()
            .insert(test_item);
        item.get_remaining_possible_subsumption_class_testing_set_mut()
            .insert(test_item);

        assert_eq!(item.get_top_concept_satisfiable_test_item(), test_item);
        assert_eq!(item.get_bottom_concept_satisfiable_test_item(), test_item);
        assert_eq!(item.get_satisfiable_concept_item_list(), &[test_item]);
        assert_eq!(item.get_next_satisfiable_testing_item_list(), &[test_item]);
        assert!(item
            .get_next_candidate_satisfiable_testing_item_set()
            .contains(&test_item));
        assert!(item
            .get_remaining_candidate_satisfiable_testing_item_set()
            .contains(&test_item));
        assert_eq!(
            item.get_next_possible_subsumption_testing_item_list(),
            &[test_item]
        );
        assert!(item
            .get_current_possible_subsumption_testing_item_set()
            .contains(&test_item));
        assert_eq!(
            item.get_remaining_possible_subsumption_class_testing_count(),
            1
        );
    }

    #[test]
    fn classification_pseudo_model_identifier_message_tracks_type_and_payload() {
        let concept = ConceptId::new(41);
        let mut hash = ClassificationClassPseudoModelHash::new();
        hash.get_pseudo_model_data_mut(0, true)
            .expect("pseudo-model data")
            .set_valid_concept_map(true);

        let mut message = ClassificationPseudoModelIdentifierMessageData::new();
        message.init_classification_pseudo_model_identifier_message_data(concept, hash.clone(), 55);

        assert_eq!(
            message.get_classification_message_data_type(),
            ClassificationMessageDataType::TellClassPseudoModelIdentifiers
        );
        assert_eq!(message.get_pseudo_model_concept(), concept);
        assert_eq!(message.get_pseudo_model_memory_pools(), 55);
        assert_eq!(
            message.get_pseudo_model_hash().get_count(),
            hash.get_count()
        );
    }

    #[test]
    fn classification_class_subsumption_message_tracks_type_and_payload() {
        let subsumed = ConceptId::new(11);
        let subsumer_1 = ConceptId::new(13);
        let subsumer_2 = ConceptId::new(17);
        let mut message = ClassificationClassSubsumptionMessageData::new();
        message.init_classification_subsumption_message_data(
            subsumed,
            Some(vec![subsumer_1, subsumer_2]),
        );

        assert_eq!(
            message.get_classification_message_data_type(),
            ClassificationMessageDataType::TellClassSubsumption
        );
        assert_eq!(message.get_subsumed_concept(), subsumed);
        assert_eq!(
            message.get_class_subsumer_list(),
            Some([subsumer_1, subsumer_2].as_slice())
        );
    }

    #[test]
    fn classification_initialize_possible_subsumption_data_tracks_validity() {
        let concept = ConceptId::new(19);
        let mut data = ClassificationInitializePossibleClassSubsumptionData::new(concept);
        assert_eq!(data.get_possible_subsumer_concept(), concept);
        assert!(data.is_possible_subsumer_valid());

        data.set_possible_subsumer_invalid();
        assert!(!data.is_possible_subsumer_valid());

        data.init_classification_possible_subsumption_data(ConceptId::new(23));
        assert_eq!(data.get_possible_subsumer_concept(), ConceptId::new(23));
        assert!(data.is_possible_subsumer_valid());
    }

    #[test]
    fn classification_initialize_possible_class_subsumption_message_tracks_lists_and_eq_flag() {
        let subsumed = ConceptId::new(29);
        let poss = ClassificationInitializePossibleClassSubsumptionData::new(ConceptId::new(31));
        let mut message = ClassificationInitializePossibleClassSubsumptionMessageData::new();
        message.init_classification_possible_subsumption_message_data(
            subsumed,
            Some(vec![poss.clone()]),
            true,
            Some(vec![ConceptId::new(37)]),
        );

        assert_eq!(
            message.get_classification_message_data_type(),
            ClassificationMessageDataType::TellClassInitializePossibleSubsumption
        );
        assert_eq!(message.get_subsumed_concept(), subsumed);
        assert_eq!(
            message
                .get_class_possible_subsumer_list()
                .expect("possible list")[0]
                .get_possible_subsumer_concept(),
            poss.get_possible_subsumer_concept()
        );
        assert!(message.has_eq_concepts_non_candidate_poss_subsumers());
        assert_eq!(
            message.get_class_eq_concept_non_candidate_possible_subsumer_list(),
            Some([ConceptId::new(37)].as_slice())
        );
    }

    #[test]
    fn classification_update_possible_class_subsumption_message_tracks_type_and_subsumed() {
        let subsumed = ConceptId::new(41);
        let mut message = ClassificationUpdatePossibleClassSubsumptionMessageData::new();
        message.init_classification_possible_subsumption_message_data(subsumed);

        assert_eq!(
            message.get_classification_message_data_type(),
            ClassificationMessageDataType::TellClassUpdatePossibleSubsumption
        );
        assert_eq!(message.get_subsumed_concept(), subsumed);
    }

    #[test]
    fn classification_message_data_linker_preserves_konclude_append_order() {
        let mut tail = ClassificationMessageDataLinker::new();
        tail.prepend_message(ClassificationMessageDataPayload::Header(
            ClassificationMessageData::new(ClassificationMessageDataType::TellClassSubsumption),
        ));
        tail.prepend_message(ClassificationMessageDataPayload::Header(
            ClassificationMessageData::new(
                ClassificationMessageDataType::TellClassUpdatePossibleSubsumption,
            ),
        ));
        let head = ClassificationMessageDataLinker::from_message(
            ClassificationMessageDataPayload::Header(ClassificationMessageData::new(
                ClassificationMessageDataType::TellClassPseudoModelIdentifiers,
            )),
        );

        let combined = ClassificationMessageDataLinker::append_linker_as_head(head, tail);

        assert_eq!(
            combined.message_types(),
            vec![
                ClassificationMessageDataType::TellClassPseudoModelIdentifiers,
                ClassificationMessageDataType::TellClassUpdatePossibleSubsumption,
                ClassificationMessageDataType::TellClassSubsumption,
            ]
        );
    }

    #[test]
    fn classification_message_data_observer_records_delivered_linker() {
        let linker = ClassificationMessageDataLinker::from_message(
            ClassificationMessageDataPayload::Header(ClassificationMessageData::new(
                ClassificationMessageDataType::TellClassSubsumption,
            )),
        );
        let mut observer = RecordingClassificationMessageDataObserver::new();

        observer.tell_classification_message(17, linker, 33);

        assert_eq!(observer.get_told_messages().len(), 1);
        assert_eq!(observer.get_told_messages()[0].0, 17);
        assert_eq!(observer.get_told_messages()[0].2, 33);
        assert_eq!(
            observer.get_told_messages()[0].1.message_types(),
            vec![ClassificationMessageDataType::TellClassSubsumption]
        );
    }

    #[test]
    fn classification_message_delivery_uses_adapter_ontology_and_memory_pool() {
        let linker = ClassificationMessageDataLinker::from_message(
            ClassificationMessageDataPayload::Header(ClassificationMessageData::new(
                ClassificationMessageDataType::TellClassSubsumption,
            )),
        );
        let adapter = SatisfiableTaskClassificationMessageAdapter::new_with_handles(
            ConceptId::new(7),
            19,
            23,
            HashMap::new(),
            0,
        );
        let mut observer = RecordingClassificationMessageDataObserver::new();

        assert!(deliver_classification_message_data_to_observer(
            &adapter,
            Some(linker),
            29,
            Some(&mut observer),
        ));

        assert_eq!(observer.get_told_messages().len(), 1);
        assert_eq!(observer.get_told_messages()[0].0, 19);
        assert_eq!(observer.get_told_messages()[0].2, 29);
        assert_eq!(
            observer.get_told_messages()[0].1.message_types(),
            vec![ClassificationMessageDataType::TellClassSubsumption]
        );
    }

    #[test]
    fn classification_message_delivery_skips_null_observer_and_empty_linker() {
        let adapter_without_observer =
            SatisfiableTaskClassificationMessageAdapter::new_with_handles(
                ConceptId::new(7),
                19,
                INVALID,
                HashMap::new(),
                0,
            );
        let mut observer = RecordingClassificationMessageDataObserver::new();
        let linker = ClassificationMessageDataLinker::from_message(
            ClassificationMessageDataPayload::Header(ClassificationMessageData::new(
                ClassificationMessageDataType::TellClassSubsumption,
            )),
        );

        assert!(!deliver_classification_message_data_to_observer(
            &adapter_without_observer,
            Some(linker),
            29,
            Some(&mut observer),
        ));
        assert!(observer.get_told_messages().is_empty());

        let adapter = SatisfiableTaskClassificationMessageAdapter::new_with_handles(
            ConceptId::new(7),
            19,
            23,
            HashMap::new(),
            0,
        );
        assert!(!deliver_classification_message_data_to_observer(
            &adapter,
            None,
            29,
            Some(&mut observer),
        ));
        assert!(!deliver_classification_message_data_to_observer(
            &adapter,
            Some(ClassificationMessageDataLinker::new()),
            29,
            Some(&mut observer),
        ));
        let no_observer: Option<&mut RecordingClassificationMessageDataObserver> = None;
        let linker = ClassificationMessageDataLinker::from_message(
            ClassificationMessageDataPayload::Header(ClassificationMessageData::new(
                ClassificationMessageDataType::TellClassSubsumption,
            )),
        );
        assert!(!deliver_classification_message_data_to_observer(
            &adapter,
            Some(linker),
            29,
            no_observer,
        ));
        assert!(observer.get_told_messages().is_empty());
    }

    #[test]
    fn classification_message_delivery_resolves_registered_observer_handle() {
        let linker = ClassificationMessageDataLinker::from_message(
            ClassificationMessageDataPayload::Header(ClassificationMessageData::new(
                ClassificationMessageDataType::TellClassSubsumption,
            )),
        );
        let mut registry = ClassificationMessageDataObserverRegistry::new();
        let observer_handle =
            registry.alloc_observer(RecordingClassificationMessageDataObserver::new());
        let adapter = SatisfiableTaskClassificationMessageAdapter::new_with_handles(
            ConceptId::new(7),
            31,
            observer_handle,
            HashMap::new(),
            0,
        );

        assert!(deliver_classification_message_data_to_registered_observer(
            &adapter,
            Some(linker),
            37,
            Some(&mut registry),
        ));

        let observer = registry
            .get_observer(observer_handle)
            .expect("registered observer");
        assert_eq!(observer.get_told_messages().len(), 1);
        assert_eq!(observer.get_told_messages()[0].0, 31);
        assert_eq!(observer.get_told_messages()[0].2, 37);
        assert_eq!(
            observer.get_told_messages()[0].1.message_types(),
            vec![ClassificationMessageDataType::TellClassSubsumption]
        );
    }

    #[test]
    fn classification_message_delivery_rejects_missing_registered_observer_handle() {
        let linker = ClassificationMessageDataLinker::from_message(
            ClassificationMessageDataPayload::Header(ClassificationMessageData::new(
                ClassificationMessageDataType::TellClassSubsumption,
            )),
        );
        let mut registry = ClassificationMessageDataObserverRegistry::new();
        let observer_handle =
            registry.alloc_observer(RecordingClassificationMessageDataObserver::new());
        let stale_handle = observer_handle + 1;
        let adapter = SatisfiableTaskClassificationMessageAdapter::new_with_handles(
            ConceptId::new(7),
            31,
            stale_handle,
            HashMap::new(),
            0,
        );

        assert!(!deliver_classification_message_data_to_registered_observer(
            &adapter,
            Some(linker),
            37,
            Some(&mut registry),
        ));
        assert!(registry
            .get_observer(observer_handle)
            .expect("registered observer")
            .get_told_messages()
            .is_empty());

        let adapter_without_observer =
            SatisfiableTaskClassificationMessageAdapter::new_with_handles(
                ConceptId::new(7),
                31,
                INVALID,
                HashMap::new(),
                0,
            );
        let linker = ClassificationMessageDataLinker::from_message(
            ClassificationMessageDataPayload::Header(ClassificationMessageData::new(
                ClassificationMessageDataType::TellClassSubsumption,
            )),
        );
        assert!(!deliver_classification_message_data_to_registered_observer(
            &adapter_without_observer,
            Some(linker),
            37,
            Some(&mut registry),
        ));
    }

    #[test]
    fn classification_reference_linking_live_item_requires_more_information() {
        let mut concepts = Arena::new();
        let mut concept_process_datas = Arena::new();
        let mut concept_reference_linking_datas = Arena::new();
        let mut analyse_concept = Concept::new();
        let item_id = OptimizedKPSetClassTestingItemId::new(0);
        let mut ref_linking = ConceptSaturationReferenceLinkingData::new();
        ref_linking.set_classifier_reference_linking_data(item_id.raw);
        let ref_linking_id = concept_reference_linking_datas.push(ref_linking);
        let mut con_proc_data = ConceptProcessData::new();
        con_proc_data.set_concept_reference_linking(ref_linking_id);
        let con_proc_data_id = concept_process_datas.push(con_proc_data);
        analyse_concept.set_concept_data(con_proc_data_id.raw);
        let analyse_concept = concepts.push(analyse_concept);
        let adapter = SatisfiableTaskClassificationMessageAdapter::new(analyse_concept, 0);
        let testing_items = vec![OptimizedKPSetClassTestingItem::new()];

        assert!(is_more_classification_information_required_for_concept(
            analyse_concept,
            &concepts,
            &concept_process_datas,
            &concept_reference_linking_datas,
            &adapter,
            &testing_items,
        ));
    }

    #[test]
    fn classification_reference_linking_uses_invalidated_adapter_hash_fallback() {
        let mut concepts = Arena::new();
        let mut concept_process_datas = Arena::new();
        let concept_reference_linking_datas = Arena::new();
        let mut analyse_concept = Concept::new();
        let fallback_item_id = OptimizedKPSetClassTestingItemId::new(1);
        let mut con_proc_data = ConceptProcessData::new();
        con_proc_data.set_invalidated_reference_linking(true);
        let con_proc_data_id = concept_process_datas.push(con_proc_data);
        analyse_concept.set_concept_data(con_proc_data_id.raw);
        let analyse_concept = concepts.push(analyse_concept);
        let mut fallback_hash = HashMap::new();
        fallback_hash.insert(analyse_concept, fallback_item_id.raw);
        let adapter = SatisfiableTaskClassificationMessageAdapter::new_with_handles(
            analyse_concept,
            INVALID,
            INVALID,
            fallback_hash,
            0,
        );
        let mut completed_item = OptimizedKPSetClassTestingItem::new();
        completed_item.set_satisfiable_test_ordered(true);
        let testing_items = vec![completed_item, OptimizedKPSetClassTestingItem::new()];

        assert!(is_more_classification_information_required_for_concept(
            analyse_concept,
            &concepts,
            &concept_process_datas,
            &concept_reference_linking_datas,
            &adapter,
            &testing_items,
        ));
    }

    #[test]
    fn classification_reference_linking_rejects_completed_or_missing_items() {
        let mut concepts = Arena::new();
        let mut concept_process_datas = Arena::new();
        let mut concept_reference_linking_datas = Arena::new();
        let mut analyse_concept = Concept::new();
        let completed_item_id = OptimizedKPSetClassTestingItemId::new(0);
        let mut ref_linking = ConceptSaturationReferenceLinkingData::new();
        ref_linking.set_classifier_reference_linking_data(completed_item_id.raw);
        let ref_linking_id = concept_reference_linking_datas.push(ref_linking);
        let mut con_proc_data = ConceptProcessData::new();
        con_proc_data.set_concept_reference_linking(ref_linking_id);
        let con_proc_data_id = concept_process_datas.push(con_proc_data);
        analyse_concept.set_concept_data(con_proc_data_id.raw);
        let analyse_concept = concepts.push(analyse_concept);
        let adapter = SatisfiableTaskClassificationMessageAdapter::new(analyse_concept, 0);
        let mut completed_item = OptimizedKPSetClassTestingItem::new();
        completed_item.set_satisfiable_tested(true);
        let testing_items = vec![completed_item];

        assert!(!is_more_classification_information_required_for_concept(
            analyse_concept,
            &concepts,
            &concept_process_datas,
            &concept_reference_linking_datas,
            &adapter,
            &testing_items,
        ));

        assert!(!is_more_classification_information_required_for_concept(
            ConceptId::new(99),
            &concepts,
            &concept_process_datas,
            &concept_reference_linking_datas,
            &adapter,
            &testing_items,
        ));
    }

    #[test]
    fn kpset_class_thread_processes_pseudo_model_identifier_message() {
        let mut concepts = Arena::new();
        let concept = concepts.push(Concept::new());
        let mut ont_item = OptimizedKPSetClassOntologyClassificationItem::new();
        let item_id = ont_item.get_concept_satisfiable_test_item(concept, true, &concepts);

        let mut hash = ClassificationClassPseudoModelHash::new();
        hash.get_pseudo_model_data_mut(0, true)
            .expect("pseudo-model data")
            .set_valid_concept_map(true);

        let mut message = ClassificationPseudoModelIdentifierMessageData::new();
        message.init_classification_pseudo_model_identifier_message_data(concept, hash, 77);

        let mut thread = OptimizedKPSetClassSubsumptionClassifierThread::new();
        assert!(thread.process_pseudo_model_identifier_message(&mut ont_item, &message, &concepts));

        assert_eq!(thread.get_processed_pseudo_model_message_count(), 1);
        assert_eq!(ont_item.get_memory_pool_list(), &[77]);
        let item = &ont_item.get_concept_satisfiable_test_item_container()[item_id.index()];
        assert!(item.is_class_pseudo_model_initalized());
        assert_eq!(
            item.get_class_pseudo_model()
                .get_pseudo_model_hash()
                .expect("installed pseudo-model hash")
                .get_count(),
            1
        );
    }

    #[test]
    fn kpset_class_thread_pseudo_model_message_without_item_is_unconsumed() {
        let mut concepts = Arena::new();
        let concept = concepts.push(Concept::new());
        let mut ont_item = OptimizedKPSetClassOntologyClassificationItem::new();
        let mut message = ClassificationPseudoModelIdentifierMessageData::new();
        message.init_classification_pseudo_model_identifier_message_data(
            concept,
            ClassificationClassPseudoModelHash::new(),
            81,
        );

        let mut thread = OptimizedKPSetClassSubsumptionClassifierThread::new();
        assert!(!thread.process_pseudo_model_identifier_message(
            &mut ont_item,
            &message,
            &concepts
        ));

        assert_eq!(thread.get_processed_pseudo_model_message_count(), 1);
        assert!(ont_item.get_memory_pool_list().is_empty());
    }

    #[test]
    fn kpset_class_thread_processes_pseudo_model_message_linker() {
        let mut concepts = Arena::new();
        let concept = concepts.push(Concept::new());
        let mut ont_item = OptimizedKPSetClassOntologyClassificationItem::new();
        let item_id = ont_item.get_concept_satisfiable_test_item(concept, true, &concepts);

        let mut hash = ClassificationClassPseudoModelHash::new();
        hash.get_pseudo_model_data_mut(0, true)
            .expect("pseudo-model data")
            .set_valid_concept_map(true);
        let mut message = ClassificationPseudoModelIdentifierMessageData::new();
        message.init_classification_pseudo_model_identifier_message_data(concept, hash, 91);

        let mut message_linker = ClassificationMessageDataLinker::from_message(
            ClassificationMessageDataPayload::PseudoModelIdentifier(message),
        );
        message_linker.prepend_message(ClassificationMessageDataPayload::Header(
            ClassificationMessageData::new(ClassificationMessageDataType::TellClassSubsumption),
        ));

        let mut thread = OptimizedKPSetClassSubsumptionClassifierThread::new();
        assert!(thread.process_classification_message_data_linker(
            &mut ont_item,
            &message_linker,
            &concepts
        ));

        assert_eq!(thread.get_processed_pseudo_model_message_count(), 1);
        assert_eq!(ont_item.get_memory_pool_list(), &[91]);
        assert!(
            ont_item.get_concept_satisfiable_test_item_container()[item_id.index()]
                .is_class_pseudo_model_initalized()
        );
    }

    #[test]
    fn kpset_class_thread_registers_calculation_work_items() {
        let mut concepts = Arena::new();
        let sat_concept = concepts.push(Concept::new());
        let subsumed_concept = concepts.push(Concept::new());
        let subsumer_concept = concepts.push(Concept::new());
        let mut ont_item = OptimizedKPSetClassOntologyClassificationItem::new();
        let sat_item = ont_item.get_concept_satisfiable_test_item(sat_concept, true, &concepts);
        let subsumed_item =
            ont_item.get_concept_satisfiable_test_item(subsumed_concept, true, &concepts);
        let subsumer_item =
            ont_item.get_concept_satisfiable_test_item(subsumer_concept, true, &concepts);

        let mut thread = OptimizedKPSetClassSubsumptionClassifierThread::new();
        let sat_work = thread
            .register_satisfiable_calculation_job(&mut ont_item, sat_item, 301)
            .expect("registered satisfiable work item");
        assert!(sat_work.is_concept_satisfiable_test());
        assert_eq!(sat_work.get_satisfiable_tested_concept(), sat_concept);
        assert_eq!(ont_item.get_current_calculating_count(), 1);
        assert!(
            ont_item.get_concept_satisfiable_test_item_container()[sat_item.index()]
                .is_satisfiable_test_ordered()
        );
        assert_eq!(ont_item.get_work_item_hash().get(&301), Some(&sat_work));

        let subsum_work = thread
            .register_subsumption_calculation_job(&mut ont_item, subsumed_item, subsumer_item, 307)
            .expect("registered subsumption work item");
        assert!(subsum_work.is_concept_subsumption_test());
        assert_eq!(subsum_work.get_subsumed_tested_concept(), subsumed_concept);
        assert_eq!(subsum_work.get_subsumer_tested_concept(), subsumer_concept);
        assert_eq!(ont_item.get_current_calculating_count(), 2);
        assert_eq!(ont_item.get_calculated_possible_subsumer_count(), 1);
        assert_eq!(ont_item.get_work_item_hash().get(&307), Some(&subsum_work));
        assert_eq!(thread.get_created_calculation_task_count(), 2);
        assert_eq!(thread.get_ordered_subsumption_calculation_count(), 1);
    }

    #[test]
    fn kpset_class_thread_registers_satisfiable_job_message_adapter() {
        let mut concepts = Arena::new();
        let sat_concept = concepts.push(Concept::new());
        let ref_concept = concepts.push(Concept::new());
        let mut ont_item = OptimizedKPSetClassOntologyClassificationItem::new();
        ont_item
            .get_concept_reference_linking_data_hash_mut()
            .insert(ref_concept, 991);
        let sat_item = ont_item.get_concept_satisfiable_test_item(sat_concept, true, &concepts);
        let mut thread = OptimizedKPSetClassSubsumptionClassifierThread::new();
        let mut job = SatisfiableCalculationJob::new();
        let mut calc_context = CalculationAlgorithmContext::new();

        let work = thread
            .register_satisfiable_calculation_job_with_message_adapter(
                &mut ont_item,
                sat_item,
                501,
                &mut job,
                17,
                19,
                &mut calc_context,
            )
            .expect("registered class satisfiable work");

        assert!(work.is_concept_satisfiable_test());
        assert_eq!(work.get_satisfiable_tested_concept(), sat_concept);
        let adapter_id = job.get_satisfiable_classification_message_adapter();
        assert!(adapter_id.is_some());
        let adapter = calc_context.classification_message_adapter(adapter_id);
        assert_eq!(adapter.get_testing_concept(), sat_concept);
        assert_eq!(adapter.get_testing_ontology(), 17);
        assert_eq!(adapter.get_classification_message_data_observer(), 19);
        assert_eq!(adapter.get_extraction_flags(), EFEXTRACTALL);
        assert_eq!(
            adapter
                .get_concept_reference_linking_data_hash()
                .get(&ref_concept),
            Some(&991)
        );
        assert_eq!(ont_item.get_work_item_hash().get(&501), Some(&work));
    }

    #[test]
    fn kpset_class_thread_registers_subsumption_job_message_adapter() {
        let mut concepts = Arena::new();
        let subsumed_concept = concepts.push(Concept::new());
        let subsumer_concept = concepts.push(Concept::new());
        let ref_concept = concepts.push(Concept::new());
        let mut ont_item = OptimizedKPSetClassOntologyClassificationItem::new();
        ont_item
            .get_concept_reference_linking_data_hash_mut()
            .insert(ref_concept, 1003);
        let subsumed_item =
            ont_item.get_concept_satisfiable_test_item(subsumed_concept, true, &concepts);
        let subsumer_item =
            ont_item.get_concept_satisfiable_test_item(subsumer_concept, true, &concepts);
        let mut thread = OptimizedKPSetClassSubsumptionClassifierThread::new();
        let mut job = SatisfiableCalculationJob::new();
        let mut calc_context = CalculationAlgorithmContext::new();

        let work = thread
            .register_subsumption_calculation_job_with_message_adapter(
                &mut ont_item,
                subsumed_item,
                subsumer_item,
                503,
                &mut job,
                23,
                29,
                &mut calc_context,
            )
            .expect("registered class subsumption work");

        assert!(work.is_concept_subsumption_test());
        assert_eq!(work.get_subsumed_tested_concept(), subsumed_concept);
        assert_eq!(work.get_subsumer_tested_concept(), subsumer_concept);
        let adapter_id = job.get_satisfiable_classification_message_adapter();
        assert!(adapter_id.is_some());
        let adapter = calc_context.classification_message_adapter(adapter_id);
        assert_eq!(adapter.get_testing_concept(), subsumed_concept);
        assert_eq!(adapter.get_testing_ontology(), 23);
        assert_eq!(adapter.get_classification_message_data_observer(), 29);
        assert_eq!(
            adapter.get_extraction_flags(),
            EFEXTRACTSUBSUMERSOTHERNODES
                | EFEXTRACTPOSSIBLESUBSUMERSROOTNODE
                | EFEXTRACTPOSSIBLESUBSUMERSOTHERNODES
                | EFEXTRACTOTHERNODESMULTIPLEDEPENDENCY
        );
        assert_eq!(
            adapter
                .get_concept_reference_linking_data_hash()
                .get(&ref_concept),
            Some(&1003)
        );
        assert_eq!(ont_item.get_work_item_hash().get(&503), Some(&work));
        assert_eq!(thread.get_ordered_subsumption_calculation_count(), 1);
    }

    #[test]
    fn kpset_role_thread_registers_calculation_work_items() {
        let sat_role = RoleId::new(311);
        let subsumed_role = RoleId::new(313);
        let subsumer_role = RoleId::new(317);
        let mut ont_item = OptimizedKPSetRoleOntologyClassificationItem::new();
        let sat_item = ont_item.get_role_satisfiable_test_item(sat_role, true);
        let subsumed_item = ont_item.get_role_satisfiable_test_item(subsumed_role, true);
        let subsumer_item = ont_item.get_role_satisfiable_test_item(subsumer_role, true);

        let mut thread = OptimizedKPSetRoleSubsumptionClassifierThread::new();
        let sat_work = thread
            .register_satisfiable_calculation_job(&mut ont_item, sat_item, 401)
            .expect("registered role satisfiable work item");
        assert!(sat_work.is_role_satisfiable_test());
        assert_eq!(sat_work.get_satisfiable_tested_role(), sat_role);
        assert_eq!(ont_item.get_current_calculating_count(), 1);
        assert!(
            ont_item.get_role_satisfiable_test_item_list()[sat_item.index()]
                .is_satisfiable_test_ordered()
        );
        assert_eq!(
            ont_item.get_computation_item_hash().get(&401),
            Some(&sat_work)
        );

        let subsum_work = thread
            .register_subsumption_calculation_job(&mut ont_item, subsumed_item, subsumer_item, 409)
            .expect("registered role subsumption work item");
        assert!(subsum_work.is_role_subsumption_test());
        assert_eq!(subsum_work.get_subsumed_tested_role(), subsumed_role);
        assert_eq!(subsum_work.get_subsumer_tested_role(), subsumer_role);
        assert_eq!(ont_item.get_current_calculating_count(), 2);
        assert_eq!(ont_item.get_calculated_possible_subsumer_count(), 1);
        assert_eq!(
            ont_item.get_computation_item_hash().get(&409),
            Some(&subsum_work)
        );
        assert_eq!(thread.get_created_calculation_task_count(), 2);
        assert_eq!(thread.get_ordered_subsumption_calculation_count(), 1);
    }

    #[test]
    fn kpset_role_thread_registers_satisfiable_job_role_marked_adapter() {
        let sat_role = RoleId::new(421);
        let mut ont_item = OptimizedKPSetRoleOntologyClassificationItem::new();
        let sat_item = ont_item.get_role_satisfiable_test_item(sat_role, true);
        let mut thread = OptimizedKPSetRoleSubsumptionClassifierThread::new();
        let mut job = SatisfiableCalculationJob::new();
        let mut calc_context = CalculationAlgorithmContext::new();
        let propagation_individual = IndividualId::new(701);
        let marker_individual = IndividualId::new(703);

        let work = thread
            .register_satisfiable_calculation_job_with_role_marked_adapter(
                &mut ont_item,
                sat_item,
                521,
                &mut job,
                propagation_individual,
                marker_individual,
                31,
                37,
                &mut calc_context,
            )
            .expect("registered role satisfiable work");

        assert!(work.is_role_satisfiable_test());
        assert_eq!(work.get_satisfiable_tested_role(), sat_role);
        let role_adapter_id = job.get_satisfiable_classification_role_marked_message_adapter();
        assert!(role_adapter_id.is_some());
        let role_adapter = calc_context.classification_role_marked_message_adapter(role_adapter_id);
        assert_eq!(role_adapter.get_testing_role(), sat_role);
        assert_eq!(
            role_adapter.get_propagation_individual(),
            propagation_individual
        );
        assert_eq!(role_adapter.get_marker_individual(), marker_individual);
        assert_eq!(role_adapter.get_testing_ontology(), 31);
        assert_eq!(role_adapter.get_classification_message_data_observer(), 37);
        assert_eq!(ont_item.get_computation_item_hash().get(&521), Some(&work));
        assert_eq!(thread.get_created_calculation_task_count(), 1);
    }

    #[test]
    fn kpset_role_thread_registers_satisfiable_job_with_generator_assertions() {
        let sat_role = RoleId::new(431);
        let bottom_role = RoleId::new(433);
        let mut ont_item = OptimizedKPSetRoleOntologyClassificationItem::new();
        let sat_item = ont_item.get_role_satisfiable_test_item(sat_role, true);
        let bottom_item = ont_item.get_role_satisfiable_test_item(bottom_role, true);
        ont_item.set_bottom_role_satisfiable_test_item(bottom_item);
        let mut ontology_arenas = OntologyArenas::new();
        let mut thread = OptimizedKPSetRoleSubsumptionClassifierThread::new();
        thread.create_temporary_role_classification_ontology(
            &mut ont_item,
            &mut ontology_arenas,
            801,
        );

        let exist_concept = ont_item.get_role_satisfiable_test_item_list()[sat_item.index()]
            .get_temporary_exist_concept();
        let all_prop_concept = ont_item.get_temporary_all_propagation_concept();
        let top_concept = ont_item.get_temporary_top_concept();
        let propagation_individual = ont_item.get_temporary_propagation_individual();
        let marker_individual = ont_item.get_temporary_marker_individual();
        let mut job = SatisfiableCalculationJob::new();
        let mut calc_context = CalculationAlgorithmContext::new();

        let work = thread
            .register_satisfiable_calculation_job_with_role_setup(
                &mut ont_item,
                sat_item,
                531,
                &mut job,
                41,
                43,
                &mut calc_context,
            )
            .expect("registered role satisfiable job setup");

        assert!(work.is_role_satisfiable_test());
        assert_eq!(work.get_satisfiable_tested_role(), sat_role);
        let assertions = job.get_satisfiable_calculation_job_concept_assertions();
        assert_eq!(assertions.len(), 3);
        assert_eq!(assertions[0].get_concept(), exist_concept);
        assert!(!assertions[0].is_negated());
        assert_eq!(assertions[0].get_individual(), propagation_individual);
        assert_eq!(assertions[1].get_concept(), all_prop_concept);
        assert!(!assertions[1].is_negated());
        assert_eq!(assertions[1].get_individual(), propagation_individual);
        assert_eq!(assertions[2].get_concept(), top_concept);
        assert!(!assertions[2].is_negated());
        assert_eq!(assertions[2].get_individual(), marker_individual);

        let role_adapter_id = job.get_satisfiable_classification_role_marked_message_adapter();
        assert!(role_adapter_id.is_some());
        let role_adapter = calc_context.classification_role_marked_message_adapter(role_adapter_id);
        assert_eq!(role_adapter.get_testing_role(), sat_role);
        assert_eq!(
            role_adapter.get_propagation_individual(),
            propagation_individual
        );
        assert_eq!(role_adapter.get_marker_individual(), marker_individual);
        assert_eq!(role_adapter.get_testing_ontology(), 41);
        assert_eq!(role_adapter.get_classification_message_data_observer(), 43);
        assert_eq!(ont_item.get_computation_item_hash().get(&531), Some(&work));
        assert!(
            ont_item.get_role_satisfiable_test_item_list()[sat_item.index()]
                .is_satisfiable_test_ordered()
        );
    }

    #[test]
    fn kpset_role_thread_selects_top_data_range_for_data_role_setup() {
        let sat_role = RoleId::new(441);
        let mut ont_item = OptimizedKPSetRoleOntologyClassificationItem::new();
        ont_item.set_data_roles_classification(true);
        let sat_item = ont_item.get_role_satisfiable_test_item(sat_role, true);
        let mut ontology_arenas = OntologyArenas::new();
        let mut thread = OptimizedKPSetRoleSubsumptionClassifierThread::new();
        thread.create_temporary_role_classification_ontology(
            &mut ont_item,
            &mut ontology_arenas,
            811,
        );
        let top_object_concept = ont_item.get_temporary_top_concept();
        let top_data_concept = ont_item.get_temporary_top_data_range_concept();
        assert_ne!(top_object_concept, top_data_concept);

        let mut job = SatisfiableCalculationJob::new();
        let mut calc_context = CalculationAlgorithmContext::new();
        thread
            .register_satisfiable_calculation_job_with_role_setup(
                &mut ont_item,
                sat_item,
                541,
                &mut job,
                47,
                53,
                &mut calc_context,
            )
            .expect("registered data-role satisfiable job setup");

        let assertions = job.get_satisfiable_calculation_job_concept_assertions();
        assert_eq!(assertions.len(), 3);
        assert_eq!(assertions[2].get_concept(), top_data_concept);
        assert_ne!(assertions[2].get_concept(), top_object_concept);
        assert_eq!(
            assertions[2].get_individual(),
            ont_item.get_temporary_marker_individual()
        );
    }

    #[test]
    fn kpset_role_thread_registers_subsumption_job_with_generator_assertions() {
        let subsumed_role = RoleId::new(451);
        let poss_subsumer_role = RoleId::new(453);
        let bottom_role = RoleId::new(455);
        let mut ont_item = OptimizedKPSetRoleOntologyClassificationItem::new();
        let subsumed_item = ont_item.get_role_satisfiable_test_item(subsumed_role, true);
        let poss_subsumer_item = ont_item.get_role_satisfiable_test_item(poss_subsumer_role, true);
        let bottom_item = ont_item.get_role_satisfiable_test_item(bottom_role, true);
        ont_item.set_bottom_role_satisfiable_test_item(bottom_item);
        let mut ontology_arenas = OntologyArenas::new();
        let mut thread = OptimizedKPSetRoleSubsumptionClassifierThread::new();
        thread.create_temporary_role_classification_ontology(
            &mut ont_item,
            &mut ontology_arenas,
            821,
        );

        let subsumed_exist = ont_item.get_role_satisfiable_test_item_list()[subsumed_item.index()]
            .get_temporary_exist_concept();
        let poss_propagation = ont_item.get_role_satisfiable_test_item_list()
            [poss_subsumer_item.index()]
        .get_temporary_propagation_concept();
        let poss_marker = ont_item.get_role_satisfiable_test_item_list()
            [poss_subsumer_item.index()]
        .get_temporary_marker_concept();
        let top_concept = ont_item.get_temporary_top_concept();
        let propagation_individual = ont_item.get_temporary_propagation_individual();
        let marker_individual = ont_item.get_temporary_marker_individual();
        let mut job = SatisfiableCalculationJob::new();

        let work = thread
            .register_subsumption_calculation_job_with_role_setup(
                &mut ont_item,
                subsumed_item,
                poss_subsumer_item,
                551,
                &mut job,
            )
            .expect("registered role subsumption job setup");

        assert!(work.is_role_subsumption_test());
        assert_eq!(work.get_subsumed_tested_role(), subsumed_role);
        assert_eq!(work.get_subsumer_tested_role(), poss_subsumer_role);
        let assertions = job.get_satisfiable_calculation_job_concept_assertions();
        assert_eq!(assertions.len(), 4);
        assert_eq!(assertions[0].get_concept(), subsumed_exist);
        assert!(!assertions[0].is_negated());
        assert_eq!(assertions[0].get_individual(), propagation_individual);
        assert_eq!(assertions[1].get_concept(), poss_propagation);
        assert!(!assertions[1].is_negated());
        assert_eq!(assertions[1].get_individual(), propagation_individual);
        assert_eq!(assertions[2].get_concept(), poss_marker);
        assert!(assertions[2].is_negated());
        assert_eq!(assertions[2].get_individual(), marker_individual);
        assert_eq!(assertions[3].get_concept(), top_concept);
        assert!(!assertions[3].is_negated());
        assert_eq!(assertions[3].get_individual(), marker_individual);

        assert!(job
            .get_satisfiable_classification_role_marked_message_adapter()
            .is_none());
        assert_eq!(ont_item.get_current_calculating_count(), 1);
        assert_eq!(ont_item.get_calculated_possible_subsumer_count(), 1);
        assert_eq!(thread.get_created_calculation_task_count(), 1);
        assert_eq!(thread.get_ordered_subsumption_calculation_count(), 1);
        assert_eq!(ont_item.get_computation_item_hash().get(&551), Some(&work));
    }

    #[test]
    fn kpset_class_thread_interprets_satisfiable_result_and_schedules_successors() {
        let mut concepts = Arena::new();
        let tested_concept = concepts.push(Concept::new());
        let subsumer_concept = concepts.push(Concept::new());
        let ready_successor_concept = concepts.push(Concept::new());
        let pending_successor_concept = concepts.push(Concept::new());
        let mut ont_item = OptimizedKPSetClassOntologyClassificationItem::new();
        let tested_item =
            ont_item.get_concept_satisfiable_test_item(tested_concept, true, &concepts);
        let subsumer_item =
            ont_item.get_concept_satisfiable_test_item(subsumer_concept, true, &concepts);
        let ready_successor_item =
            ont_item.get_concept_satisfiable_test_item(ready_successor_concept, true, &concepts);
        let pending_successor_item =
            ont_item.get_concept_satisfiable_test_item(pending_successor_concept, true, &concepts);
        ont_item.inc_running_satisfiable_tests_count(1);
        {
            let tested = ont_item
                .get_concept_satisfiable_test_item_mut(tested_item)
                .expect("tested item");
            tested
                .add_subsuming_concept_item(subsumer_item)
                .add_subsuming_concept_item(ready_successor_item)
                .add_successor_satisfiable_test_item(ready_successor_item)
                .add_successor_satisfiable_test_item(pending_successor_item);
        }
        ont_item
            .get_concept_satisfiable_test_item_mut(ready_successor_item)
            .expect("ready successor")
            .set_unprocessed_predecessor_items(1);
        ont_item
            .get_concept_satisfiable_test_item_mut(pending_successor_item)
            .expect("pending successor")
            .set_unprocessed_predecessor_items(2);

        let mut thread = OptimizedKPSetClassSubsumptionClassifierThread::new();
        assert!(!thread.interprete_satisfiable_result(
            &mut ont_item,
            tested_concept,
            true,
            &concepts
        ));

        assert_eq!(thread.get_satisfiable_tested_count(), 1);
        assert_eq!(ont_item.get_running_satisfiable_tests_count(), 0);
        assert_eq!(ont_item.get_satisfiable_concept_item_list(), &[tested_item]);
        let tested = &ont_item.get_concept_satisfiable_test_item_container()[tested_item.index()];
        assert!(tested.is_satisfiable_tested());
        assert!(tested.get_satisfiable_tested_result());
        let ready =
            &ont_item.get_concept_satisfiable_test_item_container()[ready_successor_item.index()];
        assert_eq!(ready.get_unprocessed_predecessor_item_count(), 0);
        assert!(ready.has_subsumer_concept_item(subsumer_item));
        assert!(!ready.has_subsumer_concept_item(ready_successor_item));
        let pending =
            &ont_item.get_concept_satisfiable_test_item_container()[pending_successor_item.index()];
        assert_eq!(pending.get_unprocessed_predecessor_item_count(), 1);
        assert!(pending.has_subsumer_concept_item(subsumer_item));
        assert_eq!(
            ont_item.get_next_satisfiable_testing_item_list(),
            &[ready_successor_item]
        );
        assert!(ont_item
            .get_next_candidate_satisfiable_testing_item_set()
            .contains(&pending_successor_item));
    }

    #[test]
    fn kpset_class_thread_interprets_unsatisfiable_result_marks_successors() {
        let mut concepts = Arena::new();
        let tested_concept = concepts.push(Concept::new());
        let subsumer_concept = concepts.push(Concept::new());
        let successor_concept = concepts.push(Concept::new());
        let mut ont_item = OptimizedKPSetClassOntologyClassificationItem::new();
        let tested_item =
            ont_item.get_concept_satisfiable_test_item(tested_concept, true, &concepts);
        let subsumer_item =
            ont_item.get_concept_satisfiable_test_item(subsumer_concept, true, &concepts);
        let successor_item =
            ont_item.get_concept_satisfiable_test_item(successor_concept, true, &concepts);
        ont_item.inc_running_satisfiable_tests_count(1);
        ont_item
            .get_concept_satisfiable_test_item_mut(tested_item)
            .expect("tested item")
            .add_subsuming_concept_item(subsumer_item)
            .add_successor_satisfiable_test_item(successor_item);
        ont_item
            .get_concept_satisfiable_test_item_mut(successor_item)
            .expect("successor")
            .set_unprocessed_predecessor_items(1);

        let mut thread = OptimizedKPSetClassSubsumptionClassifierThread::new();
        assert!(!thread.interprete_satisfiable_result(
            &mut ont_item,
            tested_concept,
            false,
            &concepts
        ));

        assert_eq!(thread.get_satisfiable_tested_count(), 1);
        assert_eq!(ont_item.get_running_satisfiable_tests_count(), 0);
        assert!(ont_item.get_satisfiable_concept_item_list().is_empty());
        let tested = &ont_item.get_concept_satisfiable_test_item_container()[tested_item.index()];
        assert!(tested.is_satisfiable_tested());
        assert!(!tested.get_satisfiable_tested_result());
        let successor =
            &ont_item.get_concept_satisfiable_test_item_container()[successor_item.index()];
        assert!(successor.is_result_unsatisfiable_derivated());
        assert!(!successor.has_subsumer_concept_item(subsumer_item));
        assert_eq!(successor.get_unprocessed_predecessor_item_count(), 0);
        assert_eq!(
            ont_item.get_next_satisfiable_testing_item_list(),
            &[successor_item]
        );
    }

    #[test]
    fn kpset_role_thread_interprets_satisfiable_result_and_schedules_successors() {
        let tested_role = RoleId::new(101);
        let subsumer_role = RoleId::new(103);
        let ready_successor_role = RoleId::new(107);
        let pending_successor_role = RoleId::new(109);
        let mut ont_item = OptimizedKPSetRoleOntologyClassificationItem::new();
        let tested_item = ont_item.get_role_satisfiable_test_item(tested_role, true);
        let subsumer_item = ont_item.get_role_satisfiable_test_item(subsumer_role, true);
        let ready_successor_item =
            ont_item.get_role_satisfiable_test_item(ready_successor_role, true);
        let pending_successor_item =
            ont_item.get_role_satisfiable_test_item(pending_successor_role, true);
        ont_item.inc_running_satisfiable_tests_count(1);
        {
            let tested = ont_item
                .get_role_satisfiable_test_item_mut(tested_item)
                .expect("tested role item");
            tested
                .add_subsumer_role_item(subsumer_item)
                .add_subsumer_role_item(ready_successor_item)
                .add_successor_satisfiable_test_item(ready_successor_item)
                .add_successor_satisfiable_test_item(pending_successor_item);
        }
        ont_item
            .get_role_satisfiable_test_item_mut(ready_successor_item)
            .expect("ready successor")
            .set_unprocessed_predecessor_items(1);
        ont_item
            .get_role_satisfiable_test_item_mut(pending_successor_item)
            .expect("pending successor")
            .set_unprocessed_predecessor_items(2);

        let mut thread = OptimizedKPSetRoleSubsumptionClassifierThread::new();
        assert!(!thread.interprete_satisfiable_result(&mut ont_item, tested_role, true));

        assert_eq!(thread.get_satisfiable_tested_count(), 1);
        assert_eq!(ont_item.get_running_satisfiable_tests_count(), 0);
        assert_eq!(ont_item.get_satisfiable_role_item_list(), &[tested_item]);
        let tested = &ont_item.get_role_satisfiable_test_item_list()[tested_item.index()];
        assert!(tested.is_satisfiable_tested());
        assert!(tested.get_satisfiable_tested_result());
        let ready = &ont_item.get_role_satisfiable_test_item_list()[ready_successor_item.index()];
        assert_eq!(ready.get_unprocessed_predecessor_item_count(), 0);
        assert!(ready.has_subsumer_role_item(subsumer_item));
        assert!(!ready.has_subsumer_role_item(ready_successor_item));
        let pending =
            &ont_item.get_role_satisfiable_test_item_list()[pending_successor_item.index()];
        assert_eq!(pending.get_unprocessed_predecessor_item_count(), 1);
        assert!(pending.has_subsumer_role_item(subsumer_item));
        assert_eq!(
            ont_item.get_next_satisfiable_testing_item_list(),
            &[ready_successor_item]
        );
        assert!(ont_item
            .get_next_candidate_satisfiable_testing_item_set()
            .contains(&pending_successor_item));
    }

    #[test]
    fn kpset_role_thread_interprets_unsatisfiable_result_marks_successors() {
        let tested_role = RoleId::new(151);
        let subsumer_role = RoleId::new(157);
        let successor_role = RoleId::new(163);
        let mut ont_item = OptimizedKPSetRoleOntologyClassificationItem::new();
        let tested_item = ont_item.get_role_satisfiable_test_item(tested_role, true);
        let subsumer_item = ont_item.get_role_satisfiable_test_item(subsumer_role, true);
        let successor_item = ont_item.get_role_satisfiable_test_item(successor_role, true);
        ont_item.inc_running_satisfiable_tests_count(1);
        ont_item
            .get_role_satisfiable_test_item_mut(tested_item)
            .expect("tested role item")
            .add_subsumer_role_item(subsumer_item)
            .add_successor_satisfiable_test_item(successor_item);
        ont_item
            .get_role_satisfiable_test_item_mut(successor_item)
            .expect("successor role item")
            .set_unprocessed_predecessor_items(1);

        let mut thread = OptimizedKPSetRoleSubsumptionClassifierThread::new();
        assert!(!thread.interprete_satisfiable_result(&mut ont_item, tested_role, false));

        assert_eq!(thread.get_satisfiable_tested_count(), 1);
        assert_eq!(ont_item.get_running_satisfiable_tests_count(), 0);
        assert!(ont_item.get_satisfiable_role_item_list().is_empty());
        let tested = &ont_item.get_role_satisfiable_test_item_list()[tested_item.index()];
        assert!(tested.is_satisfiable_tested());
        assert!(!tested.get_satisfiable_tested_result());
        let successor = &ont_item.get_role_satisfiable_test_item_list()[successor_item.index()];
        assert!(successor.is_result_unsatisfiable_derivated());
        assert!(!successor.has_subsumer_role_item(subsumer_item));
        assert_eq!(successor.get_unprocessed_predecessor_item_count(), 0);
        assert_eq!(
            ont_item.get_next_satisfiable_testing_item_list(),
            &[successor_item]
        );
    }

    #[test]
    fn classifier_computation_items_and_callback_event_expose_konclude_fields() {
        let sat_job = 17;
        let class_sat =
            ClassClassificationComputationItem::new_satisfiable(sat_job, ConceptId::new(101));
        assert_eq!(class_sat.get_satisfiable_calculation_job(), sat_job);
        assert!(class_sat.is_test_valid());
        assert!(class_sat.is_concept_satisfiable_test());
        assert!(!class_sat.is_concept_subsumption_test());
        assert_eq!(
            class_sat.get_satisfiable_tested_concept(),
            ConceptId::new(101)
        );
        assert!(class_sat.get_subsumer_tested_concept().is_none());

        let mut class_sub = ClassClassificationComputationItem::new_subsumption(
            sat_job,
            ConceptId::new(103),
            ConceptId::new(107),
        );
        assert!(class_sub.is_concept_subsumption_test());
        assert_eq!(class_sub.get_subsumer_tested_concept(), ConceptId::new(103));
        assert_eq!(class_sub.get_subsumed_tested_concept(), ConceptId::new(107));
        class_sub.set_test_invalid();
        assert!(!class_sub.is_test_valid());

        let role_sub = PropertyClassificationComputationItem::new_subsumption(
            sat_job,
            RoleId::new(109),
            RoleId::new(113),
        );
        assert_eq!(role_sub.get_satisfiable_calculation_job(), sat_job);
        assert!(role_sub.is_role_subsumption_test());
        assert_eq!(role_sub.get_subsumer_tested_role(), RoleId::new(109));
        assert_eq!(role_sub.get_subsumed_tested_role(), RoleId::new(113));

        let mut event = TestCalculatedCallbackEvent::new(sat_job, class_sat, true);
        event.set_used_statistics_collection(31);
        assert_eq!(event.get_satisfiable_calculation_job(), sat_job);
        assert!(event.get_classification_work_item().is_some());
        assert!(event.get_test_result_satisfiable());
        assert!(!event.has_calculation_error());
        assert_eq!(event.get_used_statistics_collection(), 31);
    }

    #[test]
    fn kpset_class_thread_routes_satisfiable_callback_event() {
        let mut concepts = Arena::new();
        let tested_concept = concepts.push(Concept::new());
        let mut ont_item = OptimizedKPSetClassOntologyClassificationItem::new();
        let tested_item =
            ont_item.get_concept_satisfiable_test_item(tested_concept, true, &concepts);
        ont_item.inc_running_satisfiable_tests_count(1);
        ont_item.inc_current_calculating_count(1);

        let work_item = ClassClassificationComputationItem::new_satisfiable(41, tested_concept);
        let mut event = TestCalculatedCallbackEvent::new(41, work_item, true);
        event.set_used_statistics_collection(43);

        let mut thread = OptimizedKPSetClassSubsumptionClassifierThread::new();
        assert!(thread.interprete_test_results_satisfiable_branch(
            &mut ont_item,
            &event,
            &concepts
        ));

        assert_eq!(thread.get_received_callback_count(), 1);
        assert_eq!(thread.get_satisfiable_tested_count(), 1);
        assert_eq!(ont_item.get_current_calculating_count(), 0);
        assert_eq!(ont_item.get_running_satisfiable_tests_count(), 0);
        assert_eq!(ont_item.get_reused_statistics_collections(), &[43]);
        assert!(!ont_item.is_taxonomy_construction_failed());
        assert_eq!(ont_item.get_satisfiable_concept_item_list(), &[tested_item]);
    }

    #[test]
    fn kpset_class_thread_routes_error_callback_to_taxonomy_failure() {
        let mut concepts = Arena::new();
        let tested_concept = concepts.push(Concept::new());
        let mut ont_item = OptimizedKPSetClassOntologyClassificationItem::new();
        ont_item.get_concept_satisfiable_test_item(tested_concept, true, &concepts);
        ont_item.inc_running_satisfiable_tests_count(1);
        ont_item.inc_current_calculating_count(1);

        let work_item = ClassClassificationComputationItem::new_satisfiable(47, tested_concept);
        let mut event = TestCalculatedCallbackEvent::new(47, work_item, true);
        event
            .set_calculation_error(true)
            .set_used_statistics_collection(53);

        let mut thread = OptimizedKPSetClassSubsumptionClassifierThread::new();
        assert!(thread.interprete_test_results_satisfiable_branch(
            &mut ont_item,
            &event,
            &concepts
        ));

        assert_eq!(thread.get_received_callback_count(), 1);
        assert_eq!(thread.get_satisfiable_tested_count(), 0);
        assert_eq!(ont_item.get_current_calculating_count(), 0);
        assert_eq!(ont_item.get_running_satisfiable_tests_count(), 1);
        assert!(ont_item.is_taxonomy_construction_failed());
        assert_eq!(ont_item.get_reused_statistics_collections(), &[53]);
    }

    #[test]
    fn kpset_class_thread_interprets_true_subsumption_result() {
        let mut concepts = Arena::new();
        let subsumed_concept = concepts.push(Concept::new());
        let subsumer_concept = concepts.push(Concept::new());
        let mut ont_item = OptimizedKPSetClassOntologyClassificationItem::new();
        let subsumed_item =
            ont_item.get_concept_satisfiable_test_item(subsumed_concept, true, &concepts);
        let subsumer_item =
            ont_item.get_concept_satisfiable_test_item(subsumer_concept, true, &concepts);
        ont_item.inc_running_possible_subsumption_tests_count(1);
        ont_item.set_remaining_possible_subsumption_tests_count(1);
        ont_item
            .get_current_possible_subsumption_testing_item_set_mut()
            .insert(subsumed_item);
        ont_item
            .get_remaining_possible_subsumption_class_testing_set_mut()
            .insert(subsumed_item);
        {
            let poss_map = ont_item
                .get_concept_satisfiable_test_item_mut(subsumed_item)
                .expect("subsumed item")
                .get_possible_subsumption_map(true)
                .expect("possible map");
            poss_map.insert(
                subsumer_concept,
                OptimizedKPSetClassPossibleSubsumptionData::new(subsumer_item),
            );
            poss_map.inc_remaining_possible_subsumption_count(1);
        }

        let mut thread = OptimizedKPSetClassSubsumptionClassifierThread::new();
        assert!(thread.interprete_subsumption_result(
            &mut ont_item,
            subsumed_concept,
            subsumer_concept,
            true,
            &concepts
        ));

        assert_eq!(thread.get_interpreted_subsumption_calculation_count(), 1);
        assert_eq!(ont_item.get_running_possible_subsumption_tests_count(), 0);
        assert_eq!(ont_item.get_remaining_possible_subsumption_tests_count(), 0);
        assert_eq!(ont_item.get_calculated_true_possible_subsumer_count(), 1);
        assert_eq!(ont_item.get_true_possible_subsumer_count(), 1);
        assert!(!ont_item
            .get_current_possible_subsumption_testing_item_set()
            .contains(&subsumed_item));
        assert!(!ont_item
            .get_remaining_possible_subsumption_class_testing_set()
            .contains(&subsumed_item));

        let subsumed =
            &ont_item.get_concept_satisfiable_test_item_container()[subsumed_item.index()];
        assert!(subsumed.has_subsumer_concept_item(subsumer_item));
        assert!(subsumed
            .get_up_propagation_item_set()
            .contains(&subsumer_item));
        let data = subsumed
            .get_possible_subsumption_map_ref()
            .and_then(|map| map.get(subsumer_concept))
            .expect("possible data");
        assert!(data.is_subsumption_confirmed());
        assert!(data.is_subsumption_updated());
        let subsumer =
            &ont_item.get_concept_satisfiable_test_item_container()[subsumer_item.index()];
        assert!(subsumer
            .get_down_propagation_item_set()
            .contains(&subsumed_item));
    }

    #[test]
    fn kpset_class_thread_interprets_false_subsumption_result() {
        let mut concepts = Arena::new();
        let subsumed_concept = concepts.push(Concept::new());
        let subsumer_concept = concepts.push(Concept::new());
        let mut ont_item = OptimizedKPSetClassOntologyClassificationItem::new();
        let subsumed_item =
            ont_item.get_concept_satisfiable_test_item(subsumed_concept, true, &concepts);
        let subsumer_item =
            ont_item.get_concept_satisfiable_test_item(subsumer_concept, true, &concepts);
        ont_item.inc_running_possible_subsumption_tests_count(1);
        ont_item.set_remaining_possible_subsumption_tests_count(1);
        ont_item
            .get_current_possible_subsumption_testing_item_set_mut()
            .insert(subsumed_item);
        ont_item
            .get_remaining_possible_subsumption_class_testing_set_mut()
            .insert(subsumed_item);
        {
            let poss_map = ont_item
                .get_concept_satisfiable_test_item_mut(subsumed_item)
                .expect("subsumed item")
                .get_possible_subsumption_map(true)
                .expect("possible map");
            poss_map.insert(
                subsumer_concept,
                OptimizedKPSetClassPossibleSubsumptionData::new(subsumer_item),
            );
            poss_map.inc_remaining_possible_subsumption_count(1);
        }

        let mut thread = OptimizedKPSetClassSubsumptionClassifierThread::new();
        assert!(thread.interprete_subsumption_result(
            &mut ont_item,
            subsumed_concept,
            subsumer_concept,
            false,
            &concepts
        ));

        assert_eq!(thread.get_interpreted_subsumption_calculation_count(), 1);
        assert_eq!(ont_item.get_running_possible_subsumption_tests_count(), 0);
        assert_eq!(ont_item.get_remaining_possible_subsumption_tests_count(), 0);
        assert_eq!(ont_item.get_calculated_false_possible_subsumer_count(), 1);
        assert_eq!(ont_item.get_true_possible_subsumer_count(), 1);
        assert_eq!(ont_item.get_false_possible_subsumer_count(), 0);
        assert!(!ont_item
            .get_current_possible_subsumption_testing_item_set()
            .contains(&subsumed_item));
        assert!(!ont_item
            .get_remaining_possible_subsumption_class_testing_set()
            .contains(&subsumed_item));

        let subsumed =
            &ont_item.get_concept_satisfiable_test_item_container()[subsumed_item.index()];
        assert!(!subsumed.has_subsumer_concept_item(subsumer_item));
        assert!(!subsumed
            .get_up_propagation_item_set()
            .contains(&subsumer_item));
        let data = subsumed
            .get_possible_subsumption_map_ref()
            .and_then(|map| map.get(subsumer_concept))
            .expect("possible data");
        assert!(data.is_subsumption_invalided());
        assert!(data.is_subsumption_updated());
        let subsumer =
            &ont_item.get_concept_satisfiable_test_item_container()[subsumer_item.index()];
        assert!(!subsumer
            .get_down_propagation_item_set()
            .contains(&subsumed_item));
    }

    #[test]
    fn kpset_class_thread_routes_subsumption_callback_event() {
        let mut concepts = Arena::new();
        let subsumed_concept = concepts.push(Concept::new());
        let subsumer_concept = concepts.push(Concept::new());
        let mut ont_item = OptimizedKPSetClassOntologyClassificationItem::new();
        let subsumed_item =
            ont_item.get_concept_satisfiable_test_item(subsumed_concept, true, &concepts);
        let subsumer_item =
            ont_item.get_concept_satisfiable_test_item(subsumer_concept, true, &concepts);
        ont_item.inc_current_calculating_count(1);
        ont_item.inc_running_possible_subsumption_tests_count(1);
        ont_item.set_remaining_possible_subsumption_tests_count(1);
        ont_item
            .get_current_possible_subsumption_testing_item_set_mut()
            .insert(subsumed_item);
        ont_item
            .get_remaining_possible_subsumption_class_testing_set_mut()
            .insert(subsumed_item);
        {
            let poss_map = ont_item
                .get_concept_satisfiable_test_item_mut(subsumed_item)
                .expect("subsumed item")
                .get_possible_subsumption_map(true)
                .expect("possible map");
            poss_map.insert(
                subsumer_concept,
                OptimizedKPSetClassPossibleSubsumptionData::new(subsumer_item),
            );
            poss_map.inc_remaining_possible_subsumption_count(1);
        }

        let work_item = ClassClassificationComputationItem::new_subsumption(
            73,
            subsumer_concept,
            subsumed_concept,
        );
        ont_item.insert_work_item(73, work_item.clone());
        let mut event = TestCalculatedCallbackEvent::new(73, work_item, false);
        event.set_used_statistics_collection(79);

        let mut thread = OptimizedKPSetClassSubsumptionClassifierThread::new();
        assert!(thread.interprete_test_results(&mut ont_item, &event, &concepts));

        assert_eq!(thread.get_received_callback_count(), 1);
        assert_eq!(thread.get_interpreted_subsumption_calculation_count(), 1);
        assert_eq!(ont_item.get_current_calculating_count(), 0);
        assert_eq!(ont_item.get_running_possible_subsumption_tests_count(), 0);
        assert_eq!(ont_item.get_reused_statistics_collections(), &[79]);
        assert!(ont_item.get_work_item_hash().is_empty());
        assert!(
            ont_item.get_concept_satisfiable_test_item_container()[subsumed_item.index()]
                .has_subsumer_concept_item(subsumer_item)
        );
    }

    #[test]
    fn kpset_role_thread_routes_satisfiable_callback_event() {
        let tested_role = RoleId::new(181);
        let mut ont_item = OptimizedKPSetRoleOntologyClassificationItem::new();
        let tested_item = ont_item.get_role_satisfiable_test_item(tested_role, true);
        ont_item.inc_running_satisfiable_tests_count(1);
        ont_item.inc_current_calculating_count(1);

        let work_item = PropertyClassificationComputationItem::new_satisfiable(59, tested_role);
        let mut event = TestCalculatedCallbackEvent::new(59, work_item, true);
        event.set_used_statistics_collection(61);

        let mut thread = OptimizedKPSetRoleSubsumptionClassifierThread::new();
        assert!(thread.interprete_test_results_satisfiable_branch(&mut ont_item, &event));

        assert_eq!(thread.get_received_callback_count(), 1);
        assert_eq!(thread.get_satisfiable_tested_count(), 1);
        assert_eq!(ont_item.get_current_calculating_count(), 0);
        assert_eq!(ont_item.get_running_satisfiable_tests_count(), 0);
        assert_eq!(ont_item.get_reused_statistics_collections(), &[61]);
        assert!(!ont_item.is_hierarchy_construction_failed());
        assert_eq!(ont_item.get_satisfiable_role_item_list(), &[tested_item]);
    }

    #[test]
    fn kpset_role_thread_routes_error_callback_to_hierarchy_failure() {
        let tested_role = RoleId::new(191);
        let mut ont_item = OptimizedKPSetRoleOntologyClassificationItem::new();
        ont_item.get_role_satisfiable_test_item(tested_role, true);
        ont_item.inc_running_satisfiable_tests_count(1);
        ont_item.inc_current_calculating_count(1);

        let work_item = PropertyClassificationComputationItem::new_satisfiable(67, tested_role);
        let mut event = TestCalculatedCallbackEvent::new(67, work_item, true);
        event
            .set_calculation_error(true)
            .set_used_statistics_collection(71);

        let mut thread = OptimizedKPSetRoleSubsumptionClassifierThread::new();
        assert!(thread.interprete_test_results_satisfiable_branch(&mut ont_item, &event));

        assert_eq!(thread.get_received_callback_count(), 1);
        assert_eq!(thread.get_satisfiable_tested_count(), 0);
        assert_eq!(ont_item.get_current_calculating_count(), 0);
        assert_eq!(ont_item.get_running_satisfiable_tests_count(), 1);
        assert!(ont_item.is_hierarchy_construction_failed());
        assert_eq!(ont_item.get_reused_statistics_collections(), &[71]);
    }

    #[test]
    fn kpset_role_thread_interprets_true_subsumption_result() {
        let subsumed_role = RoleId::new(211);
        let subsumer_role = RoleId::new(223);
        let mut ont_item = OptimizedKPSetRoleOntologyClassificationItem::new();
        let subsumed_item = ont_item.get_role_satisfiable_test_item(subsumed_role, true);
        let subsumer_item = ont_item.get_role_satisfiable_test_item(subsumer_role, true);
        ont_item.inc_running_possible_subsumption_tests_count(1);
        ont_item.set_remaining_possible_subsumption_tests_count(1);
        ont_item
            .get_current_possible_subsumption_testing_item_set_mut()
            .insert(subsumed_item);
        ont_item
            .get_remaining_possible_subsumption_testing_set_mut()
            .insert(subsumed_item);
        {
            let poss_map = ont_item
                .get_role_satisfiable_test_item_mut(subsumed_item)
                .expect("subsumed role item")
                .get_possible_subsumption_map(true)
                .expect("possible role map");
            poss_map.insert(
                subsumer_role,
                OptimizedKPSetRolePossibleSubsumptionData::new(subsumer_item),
            );
            poss_map.inc_remaining_possible_subsumption_count(1);
        }

        let mut thread = OptimizedKPSetRoleSubsumptionClassifierThread::new();
        assert!(thread.interprete_subsumption_result(
            &mut ont_item,
            subsumed_role,
            subsumer_role,
            true
        ));

        assert_eq!(thread.get_interpreted_subsumption_calculation_count(), 1);
        assert_eq!(ont_item.get_running_possible_subsumption_tests_count(), 0);
        assert_eq!(ont_item.get_remaining_possible_subsumption_tests_count(), 0);
        assert_eq!(ont_item.get_calculated_true_possible_subsumer_count(), 1);
        assert_eq!(ont_item.get_true_possible_subsumer_count(), 1);
        assert!(!ont_item
            .get_current_possible_subsumption_testing_item_set()
            .contains(&subsumed_item));
        assert!(!ont_item
            .get_remaining_possible_subsumption_testing_set()
            .contains(&subsumed_item));

        let subsumed = &ont_item.get_role_satisfiable_test_item_list()[subsumed_item.index()];
        assert!(subsumed.has_subsumer_role_item(subsumer_item));
        assert!(subsumed
            .get_up_propagation_item_set()
            .contains(&subsumer_item));
        let data = subsumed
            .get_possible_subsumption_map_ref()
            .and_then(|map| map.get(subsumer_role))
            .expect("possible role data");
        assert!(data.is_subsumption_confirmed());
        assert!(data.is_subsumption_updated());
        let subsumer = &ont_item.get_role_satisfiable_test_item_list()[subsumer_item.index()];
        assert!(subsumer
            .get_down_propagation_item_set()
            .contains(&subsumed_item));
    }

    #[test]
    fn kpset_role_thread_interprets_false_subsumption_result() {
        let subsumed_role = RoleId::new(227);
        let subsumer_role = RoleId::new(229);
        let mut ont_item = OptimizedKPSetRoleOntologyClassificationItem::new();
        let subsumed_item = ont_item.get_role_satisfiable_test_item(subsumed_role, true);
        let subsumer_item = ont_item.get_role_satisfiable_test_item(subsumer_role, true);
        ont_item.inc_running_possible_subsumption_tests_count(1);
        ont_item.set_remaining_possible_subsumption_tests_count(1);
        ont_item
            .get_current_possible_subsumption_testing_item_set_mut()
            .insert(subsumed_item);
        ont_item
            .get_remaining_possible_subsumption_testing_set_mut()
            .insert(subsumed_item);
        {
            let poss_map = ont_item
                .get_role_satisfiable_test_item_mut(subsumed_item)
                .expect("subsumed role item")
                .get_possible_subsumption_map(true)
                .expect("possible role map");
            poss_map.insert(
                subsumer_role,
                OptimizedKPSetRolePossibleSubsumptionData::new(subsumer_item),
            );
            poss_map.inc_remaining_possible_subsumption_count(1);
        }

        let mut thread = OptimizedKPSetRoleSubsumptionClassifierThread::new();
        assert!(thread.interprete_subsumption_result(
            &mut ont_item,
            subsumed_role,
            subsumer_role,
            false
        ));

        assert_eq!(thread.get_interpreted_subsumption_calculation_count(), 1);
        assert_eq!(ont_item.get_running_possible_subsumption_tests_count(), 0);
        assert_eq!(ont_item.get_remaining_possible_subsumption_tests_count(), 0);
        assert_eq!(ont_item.get_calculated_false_possible_subsumer_count(), 1);
        assert_eq!(ont_item.get_true_possible_subsumer_count(), 1);
        assert_eq!(ont_item.get_false_possible_subsumer_count(), 0);
        assert!(!ont_item
            .get_current_possible_subsumption_testing_item_set()
            .contains(&subsumed_item));
        assert!(!ont_item
            .get_remaining_possible_subsumption_testing_set()
            .contains(&subsumed_item));

        let subsumed = &ont_item.get_role_satisfiable_test_item_list()[subsumed_item.index()];
        assert!(!subsumed.has_subsumer_role_item(subsumer_item));
        assert!(!subsumed
            .get_up_propagation_item_set()
            .contains(&subsumer_item));
        let data = subsumed
            .get_possible_subsumption_map_ref()
            .and_then(|map| map.get(subsumer_role))
            .expect("possible role data");
        assert!(data.is_subsumption_invalided());
        assert!(data.is_subsumption_updated());
        let subsumer = &ont_item.get_role_satisfiable_test_item_list()[subsumer_item.index()];
        assert!(!subsumer
            .get_down_propagation_item_set()
            .contains(&subsumed_item));
    }

    #[test]
    fn kpset_role_thread_routes_subsumption_callback_event() {
        let subsumed_role = RoleId::new(233);
        let subsumer_role = RoleId::new(239);
        let mut ont_item = OptimizedKPSetRoleOntologyClassificationItem::new();
        let subsumed_item = ont_item.get_role_satisfiable_test_item(subsumed_role, true);
        let subsumer_item = ont_item.get_role_satisfiable_test_item(subsumer_role, true);
        ont_item.inc_current_calculating_count(1);
        ont_item.inc_running_possible_subsumption_tests_count(1);
        ont_item.set_remaining_possible_subsumption_tests_count(1);
        ont_item
            .get_current_possible_subsumption_testing_item_set_mut()
            .insert(subsumed_item);
        ont_item
            .get_remaining_possible_subsumption_testing_set_mut()
            .insert(subsumed_item);
        {
            let poss_map = ont_item
                .get_role_satisfiable_test_item_mut(subsumed_item)
                .expect("subsumed role item")
                .get_possible_subsumption_map(true)
                .expect("possible role map");
            poss_map.insert(
                subsumer_role,
                OptimizedKPSetRolePossibleSubsumptionData::new(subsumer_item),
            );
            poss_map.inc_remaining_possible_subsumption_count(1);
        }

        let work_item = PropertyClassificationComputationItem::new_subsumption(
            83,
            subsumer_role,
            subsumed_role,
        );
        ont_item.insert_computation_item(83, work_item.clone());
        let mut event = TestCalculatedCallbackEvent::new(83, work_item, false);
        event.set_used_statistics_collection(89);

        let mut thread = OptimizedKPSetRoleSubsumptionClassifierThread::new();
        assert!(thread.interprete_test_results(&mut ont_item, &event));

        assert_eq!(thread.get_received_callback_count(), 1);
        assert_eq!(thread.get_interpreted_subsumption_calculation_count(), 1);
        assert_eq!(ont_item.get_current_calculating_count(), 0);
        assert_eq!(ont_item.get_running_possible_subsumption_tests_count(), 0);
        assert_eq!(ont_item.get_reused_statistics_collections(), &[89]);
        assert!(ont_item.get_computation_item_hash().is_empty());
        assert!(
            ont_item.get_role_satisfiable_test_item_list()[subsumed_item.index()]
                .has_subsumer_role_item(subsumer_item)
        );
    }

    #[test]
    fn kpset_class_thread_processes_class_subsumption_message_linker() {
        let mut concepts = Arena::new();
        let subsumed_concept = concepts.push(Concept::new());
        let subsumer_concept = concepts.push(Concept::new());
        let mut ont_item = OptimizedKPSetClassOntologyClassificationItem::new();
        let subsumed_item =
            ont_item.get_concept_satisfiable_test_item(subsumed_concept, true, &concepts);
        let subsumer_item =
            ont_item.get_concept_satisfiable_test_item(subsumer_concept, true, &concepts);
        ont_item
            .get_concept_satisfiable_test_item_mut(subsumed_item)
            .expect("subsumed item")
            .get_possible_subsumption_map(true)
            .expect("possible subsumption map")
            .insert(
                subsumer_concept,
                OptimizedKPSetClassPossibleSubsumptionData::new(subsumer_item),
            );

        let mut message = ClassificationClassSubsumptionMessageData::new();
        message.init_classification_subsumption_message_data(
            subsumed_concept,
            Some(vec![subsumer_concept]),
        );
        let linker = ClassificationMessageDataLinker::from_message(
            ClassificationMessageDataPayload::from_class_subsumption(message),
        );
        let mut thread = OptimizedKPSetClassSubsumptionClassifierThread::new();

        assert!(thread.process_classification_message_data_linker(
            &mut ont_item,
            &linker,
            &concepts
        ));

        assert_eq!(thread.get_processed_subsumption_message_count(), 1);
        let subsumed_item_ref =
            &ont_item.get_concept_satisfiable_test_item_container()[subsumed_item.index()];
        assert!(subsumed_item_ref.has_subsumer_concept_item(subsumer_item));
        assert_eq!(
            subsumed_item_ref.get_subsuming_concept_item_list(),
            &[subsumer_item]
        );
        assert!(subsumed_item_ref.is_result_satisfiable_derivated());
        let poss_subsum_data = subsumed_item_ref
            .get_possible_subsumption_map_ref()
            .expect("possible subsumption map")
            .get(subsumer_concept)
            .expect("possible subsumption data");
        assert!(poss_subsum_data.is_subsumption_confirmed());
    }

    #[test]
    fn kpset_class_thread_propagates_down_subsumption_recursively() {
        let mut concepts = Arena::new();
        let root_concept = concepts.push(Concept::new());
        let child_concept = concepts.push(Concept::new());
        let grandchild_concept = concepts.push(Concept::new());
        let subsumer_concept = concepts.push(Concept::new());
        let mut ont_item = OptimizedKPSetClassOntologyClassificationItem::new();
        let root_item = ont_item.get_concept_satisfiable_test_item(root_concept, true, &concepts);
        let child_item = ont_item.get_concept_satisfiable_test_item(child_concept, true, &concepts);
        let grandchild_item =
            ont_item.get_concept_satisfiable_test_item(grandchild_concept, true, &concepts);
        let subsumer_item =
            ont_item.get_concept_satisfiable_test_item(subsumer_concept, true, &concepts);

        ont_item
            .get_concept_satisfiable_test_item_mut(root_item)
            .expect("root item")
            .add_down_propagation_item(child_item);
        ont_item
            .get_concept_satisfiable_test_item_mut(child_item)
            .expect("child item")
            .add_down_propagation_item(grandchild_item);

        assert!(
            OptimizedKPSetClassSubsumptionClassifierThread::propagate_down_subsumption(
                &mut ont_item,
                root_item,
                subsumer_item,
            )
        );
        assert!(
            ont_item.get_concept_satisfiable_test_item_container()[child_item.index()]
                .has_subsumer_concept_item(subsumer_item)
        );
        assert!(
            ont_item.get_concept_satisfiable_test_item_container()[grandchild_item.index()]
                .has_subsumer_concept_item(subsumer_item)
        );
    }

    #[test]
    fn kpset_class_thread_prunes_confirmed_possible_subsumption_downward() {
        let mut concepts = Arena::new();
        let root_concept = concepts.push(Concept::new());
        let child_concept = concepts.push(Concept::new());
        let grandchild_concept = concepts.push(Concept::new());
        let subsumer_concept = concepts.push(Concept::new());
        let mut ont_item = OptimizedKPSetClassOntologyClassificationItem::new();
        let root_item = ont_item.get_concept_satisfiable_test_item(root_concept, true, &concepts);
        let child_item = ont_item.get_concept_satisfiable_test_item(child_concept, true, &concepts);
        let grandchild_item =
            ont_item.get_concept_satisfiable_test_item(grandchild_concept, true, &concepts);
        let subsumer_item =
            ont_item.get_concept_satisfiable_test_item(subsumer_concept, true, &concepts);

        ont_item
            .get_concept_satisfiable_test_item_mut(root_item)
            .expect("root item")
            .add_down_propagation_item(child_item);
        ont_item
            .get_concept_satisfiable_test_item_mut(child_item)
            .expect("child item")
            .add_down_propagation_item(grandchild_item);
        for item_id in [root_item, child_item, grandchild_item] {
            let mut data = OptimizedKPSetClassPossibleSubsumptionData::new(subsumer_item);
            if item_id == root_item {
                data.set_subsumption_confirmed(true);
            }
            let map = ont_item
                .get_concept_satisfiable_test_item_mut(item_id)
                .expect("test item")
                .get_possible_subsumption_map(true)
                .expect("possible map");
            map.insert(subsumer_concept, data);
            map.inc_remaining_possible_subsumption_count(1);
        }
        ont_item
            .inc_remaining_possible_subsumption_tests_count(3)
            .inc_possible_subsumer_count(3);

        assert!(
            OptimizedKPSetClassSubsumptionClassifierThread::prune_possible_subsumptions(
                &mut ont_item,
                root_item,
                subsumer_concept,
                &concepts,
            )
        );

        assert_eq!(ont_item.get_remaining_possible_subsumption_tests_count(), 0);
        assert_eq!(ont_item.get_true_possible_subsumer_count(), 3);
        for item_id in [root_item, child_item, grandchild_item] {
            let data = ont_item.get_concept_satisfiable_test_item_container()[item_id.index()]
                .get_possible_subsumption_map_ref()
                .expect("possible map")
                .get(subsumer_concept)
                .expect("possible data");
            assert!(data.is_subsumption_confirmed());
            assert!(data.is_subsumption_updated());
        }
    }

    #[test]
    fn kpset_class_thread_prunes_invalid_possible_subsumption_upward() {
        let mut concepts = Arena::new();
        let parent_concept = concepts.push(Concept::new());
        let middle_concept = concepts.push(Concept::new());
        let leaf_concept = concepts.push(Concept::new());
        let not_subsumer_concept = concepts.push(Concept::new());
        let mut ont_item = OptimizedKPSetClassOntologyClassificationItem::new();
        let parent_item =
            ont_item.get_concept_satisfiable_test_item(parent_concept, true, &concepts);
        let middle_item =
            ont_item.get_concept_satisfiable_test_item(middle_concept, true, &concepts);
        let leaf_item = ont_item.get_concept_satisfiable_test_item(leaf_concept, true, &concepts);
        let not_subsumer_item =
            ont_item.get_concept_satisfiable_test_item(not_subsumer_concept, true, &concepts);

        ont_item
            .get_concept_satisfiable_test_item_mut(leaf_item)
            .expect("leaf item")
            .add_up_propagation_item(middle_item);
        ont_item
            .get_concept_satisfiable_test_item_mut(middle_item)
            .expect("middle item")
            .add_up_propagation_item(parent_item);
        for item_id in [parent_item, middle_item, leaf_item] {
            let mut data = OptimizedKPSetClassPossibleSubsumptionData::new(not_subsumer_item);
            if item_id == leaf_item {
                data.set_subsumption_invalid(true);
            }
            let map = ont_item
                .get_concept_satisfiable_test_item_mut(item_id)
                .expect("test item")
                .get_possible_subsumption_map(true)
                .expect("possible map");
            map.insert(not_subsumer_concept, data);
            map.inc_remaining_possible_subsumption_count(1);
        }
        ont_item
            .inc_remaining_possible_subsumption_tests_count(3)
            .inc_possible_subsumer_count(3);

        assert!(
            OptimizedKPSetClassSubsumptionClassifierThread::prune_possible_subsumptions(
                &mut ont_item,
                leaf_item,
                not_subsumer_concept,
                &concepts,
            )
        );

        assert_eq!(ont_item.get_remaining_possible_subsumption_tests_count(), 0);
        assert_eq!(ont_item.get_true_possible_subsumer_count(), 1);
        assert_eq!(ont_item.get_false_possible_subsumer_count(), 2);
        for item_id in [parent_item, middle_item, leaf_item] {
            let data = ont_item.get_concept_satisfiable_test_item_container()[item_id.index()]
                .get_possible_subsumption_map_ref()
                .expect("possible map")
                .get(not_subsumer_concept)
                .expect("possible data");
            assert!(data.is_subsumption_invalided());
            assert!(data.is_subsumption_updated());
        }
    }

    #[test]
    fn kpset_class_thread_prunes_equivalent_candidate_downward() {
        let mut concepts = Arena::new();
        let root_concept = concepts.push(Concept::new());
        let child_concept = concepts.push(Concept::new());
        let mut eq_concept_data = Concept::new();
        eq_concept_data.set_operator_code(CCEQ);
        let eq_concept = concepts.push(eq_concept_data);
        let candidate_concept = concepts.push(Concept::new());
        let mut ont_item = OptimizedKPSetClassOntologyClassificationItem::new();
        let root_item = ont_item.get_concept_satisfiable_test_item(root_concept, true, &concepts);
        let child_item = ont_item.get_concept_satisfiable_test_item(child_concept, true, &concepts);
        let eq_item = ont_item.get_concept_satisfiable_test_item(eq_concept, true, &concepts);
        let candidate_item =
            ont_item.get_concept_satisfiable_test_item(candidate_concept, true, &concepts);

        ont_item
            .get_equivalent_concept_candidate_hash_mut()
            .insert(eq_concept, candidate_concept);
        ont_item
            .get_concept_satisfiable_test_item_mut(root_item)
            .expect("root item")
            .add_down_propagation_item(child_item);

        let mut root_data = OptimizedKPSetClassPossibleSubsumptionData::new(eq_item);
        root_data.set_subsumption_confirmed(true);
        let root_map = ont_item
            .get_concept_satisfiable_test_item_mut(root_item)
            .expect("root item")
            .get_possible_subsumption_map(true)
            .expect("root map");
        root_map.insert(eq_concept, root_data);
        root_map.inc_remaining_possible_subsumption_count(1);
        let child_map = ont_item
            .get_concept_satisfiable_test_item_mut(child_item)
            .expect("child item")
            .get_possible_subsumption_map(true)
            .expect("child map");
        child_map.insert(
            candidate_concept,
            OptimizedKPSetClassPossibleSubsumptionData::new(candidate_item),
        );
        child_map.inc_remaining_possible_subsumption_count(1);
        ont_item
            .inc_remaining_possible_subsumption_tests_count(2)
            .inc_possible_subsumer_count(2);

        assert!(
            OptimizedKPSetClassSubsumptionClassifierThread::prune_possible_subsumptions(
                &mut ont_item,
                root_item,
                eq_concept,
                &concepts,
            )
        );

        assert_eq!(ont_item.get_remaining_possible_subsumption_tests_count(), 0);
        assert_eq!(ont_item.get_true_possible_subsumer_count(), 2);
        let candidate_data = ont_item.get_concept_satisfiable_test_item_container()
            [child_item.index()]
        .get_possible_subsumption_map_ref()
        .expect("child map")
        .get(candidate_concept)
        .expect("candidate data");
        assert!(candidate_data.is_subsumption_confirmed());
        assert!(candidate_data.is_subsumption_updated());
    }

    #[test]
    fn kpset_class_thread_init_prunes_ancestor_map_missing_new_candidate() {
        let mut concepts = Arena::new();
        let parent_concept = concepts.push(Concept::new());
        let subsumed_concept = concepts.push(Concept::new());
        let retained_concept = concepts.push(Concept::new());
        let stale_parent_concept = concepts.push(Concept::new());
        let mut ont_item = OptimizedKPSetClassOntologyClassificationItem::new();
        let parent_item =
            ont_item.get_concept_satisfiable_test_item(parent_concept, true, &concepts);
        let subsumed_item =
            ont_item.get_concept_satisfiable_test_item(subsumed_concept, true, &concepts);
        let retained_item =
            ont_item.get_concept_satisfiable_test_item(retained_concept, true, &concepts);
        let stale_parent_item =
            ont_item.get_concept_satisfiable_test_item(stale_parent_concept, true, &concepts);
        ont_item
            .get_concept_satisfiable_test_item_mut(subsumed_item)
            .expect("subsumed item")
            .add_up_propagation_item(parent_item);
        let parent_map = ont_item
            .get_concept_satisfiable_test_item_mut(parent_item)
            .expect("parent item")
            .get_possible_subsumption_map(true)
            .expect("parent map");
        parent_map.insert(
            retained_concept,
            OptimizedKPSetClassPossibleSubsumptionData::new(retained_item),
        );
        parent_map.insert(
            stale_parent_concept,
            OptimizedKPSetClassPossibleSubsumptionData::new(stale_parent_item),
        );
        parent_map.inc_remaining_possible_subsumption_count(2);
        ont_item
            .inc_remaining_possible_subsumption_tests_count(2)
            .inc_possible_subsumer_count(2);

        let retained_data =
            ClassificationInitializePossibleClassSubsumptionData::new(retained_concept);
        let mut message = ClassificationInitializePossibleClassSubsumptionMessageData::new();
        message.init_classification_possible_subsumption_message_data(
            subsumed_concept,
            Some(vec![retained_data]),
            false,
            None,
        );
        let mut thread = OptimizedKPSetClassSubsumptionClassifierThread::new();

        assert!(
            thread.process_initialize_possible_class_subsumption_message(
                &mut ont_item,
                &message,
                &concepts,
            )
        );

        assert_eq!(ont_item.get_remaining_possible_subsumption_tests_count(), 2);
        assert_eq!(ont_item.get_true_possible_subsumer_count(), 1);
        let parent_map = ont_item.get_concept_satisfiable_test_item_container()
            [parent_item.index()]
        .get_possible_subsumption_map_ref()
        .expect("parent map");
        assert!(!parent_map
            .get(retained_concept)
            .expect("retained parent data")
            .is_subsumption_invalided());
        let stale_data = parent_map
            .get(stale_parent_concept)
            .expect("stale parent data");
        assert!(stale_data.is_subsumption_invalided());
        assert!(stale_data.is_subsumption_updated());
    }

    #[test]
    fn kpset_class_thread_init_prunes_descendant_missing_new_candidate() {
        let mut concepts = Arena::new();
        let subsumed_concept = concepts.push(Concept::new());
        let child_concept = concepts.push(Concept::new());
        let retained_concept = concepts.push(Concept::new());
        let stale_for_child_concept = concepts.push(Concept::new());
        let mut ont_item = OptimizedKPSetClassOntologyClassificationItem::new();
        let subsumed_item =
            ont_item.get_concept_satisfiable_test_item(subsumed_concept, true, &concepts);
        let child_item = ont_item.get_concept_satisfiable_test_item(child_concept, true, &concepts);
        let retained_item =
            ont_item.get_concept_satisfiable_test_item(retained_concept, true, &concepts);
        let stale_for_child_item =
            ont_item.get_concept_satisfiable_test_item(stale_for_child_concept, true, &concepts);
        ont_item
            .get_concept_satisfiable_test_item_mut(subsumed_item)
            .expect("subsumed item")
            .add_down_propagation_item(child_item);
        let child_map = ont_item
            .get_concept_satisfiable_test_item_mut(child_item)
            .expect("child item")
            .get_possible_subsumption_map(true)
            .expect("child map");
        child_map.insert(
            retained_concept,
            OptimizedKPSetClassPossibleSubsumptionData::new(retained_item),
        );
        child_map.inc_remaining_possible_subsumption_count(1);
        ont_item
            .inc_remaining_possible_subsumption_tests_count(1)
            .inc_possible_subsumer_count(1);

        let retained_data =
            ClassificationInitializePossibleClassSubsumptionData::new(retained_concept);
        let stale_data =
            ClassificationInitializePossibleClassSubsumptionData::new(stale_for_child_concept);
        let mut message = ClassificationInitializePossibleClassSubsumptionMessageData::new();
        message.init_classification_possible_subsumption_message_data(
            subsumed_concept,
            Some(vec![retained_data, stale_data]),
            false,
            None,
        );
        let mut thread = OptimizedKPSetClassSubsumptionClassifierThread::new();

        assert!(
            thread.process_initialize_possible_class_subsumption_message(
                &mut ont_item,
                &message,
                &concepts,
            )
        );

        assert_eq!(ont_item.get_remaining_possible_subsumption_tests_count(), 2);
        assert_eq!(ont_item.get_true_possible_subsumer_count(), 1);
        let subsumed_map = ont_item.get_concept_satisfiable_test_item_container()
            [subsumed_item.index()]
        .get_possible_subsumption_map_ref()
        .expect("subsumed map");
        assert!(!subsumed_map
            .get(retained_concept)
            .expect("retained data")
            .is_subsumption_invalided());
        let stale_data = subsumed_map
            .get(stale_for_child_concept)
            .expect("stale child data");
        assert!(stale_data.is_subsumption_invalided());
        assert!(stale_data.is_subsumption_updated());
        assert_eq!(stale_data.get_class_item(), stale_for_child_item);
    }

    #[test]
    fn kpset_class_thread_initializes_possible_class_subsumption_map_from_valid_entries() {
        let mut concepts = Arena::new();
        let subsumed_concept = concepts.push(Concept::new());
        let valid_concept = concepts.push(Concept::new());
        let invalid_concept = concepts.push(Concept::new());
        let eq_concept = concepts.push(Concept::new());
        let mut ont_item = OptimizedKPSetClassOntologyClassificationItem::new();
        let subsumed_item =
            ont_item.get_concept_satisfiable_test_item(subsumed_concept, true, &concepts);
        let valid_item = ont_item.get_concept_satisfiable_test_item(valid_concept, true, &concepts);
        let _invalid_item =
            ont_item.get_concept_satisfiable_test_item(invalid_concept, true, &concepts);
        let eq_item = ont_item.get_concept_satisfiable_test_item(eq_concept, true, &concepts);

        let valid_data = ClassificationInitializePossibleClassSubsumptionData::new(valid_concept);
        let mut invalid_data =
            ClassificationInitializePossibleClassSubsumptionData::new(invalid_concept);
        invalid_data.set_possible_subsumer_invalid();
        let mut message = ClassificationInitializePossibleClassSubsumptionMessageData::new();
        message.init_classification_possible_subsumption_message_data(
            subsumed_concept,
            Some(vec![valid_data, invalid_data]),
            true,
            Some(vec![eq_concept]),
        );
        let linker = ClassificationMessageDataLinker::from_message(
            ClassificationMessageDataPayload::from_initialize_possible_class_subsumption(message),
        );
        let mut thread = OptimizedKPSetClassSubsumptionClassifierThread::new();

        assert!(thread.process_classification_message_data_linker(
            &mut ont_item,
            &linker,
            &concepts
        ));

        assert_eq!(
            thread.get_processed_possible_subsumption_init_message_count(),
            1
        );
        assert_eq!(ont_item.get_remaining_possible_subsumption_tests_count(), 2);
        assert_eq!(ont_item.get_possible_subsumer_count(), 2);
        let subsumed_item_ref =
            &ont_item.get_concept_satisfiable_test_item_container()[subsumed_item.index()];
        assert!(subsumed_item_ref.is_possible_subsumption_map_initialized());
        let poss_map = subsumed_item_ref
            .get_possible_subsumption_map_ref()
            .expect("possible subsumption map");
        assert_eq!(poss_map.len(), 2);
        assert_eq!(poss_map.get_remaining_possible_subsumption_count(), 2);
        assert_eq!(
            poss_map
                .get(valid_concept)
                .expect("valid data")
                .get_class_item(),
            valid_item
        );
        assert!(poss_map.get(invalid_concept).is_none());
        assert_eq!(
            poss_map.get(eq_concept).expect("eq data").get_class_item(),
            eq_item
        );
    }

    #[test]
    fn kpset_class_thread_initialization_skips_eq_candidates_and_uses_non_candidate_set() {
        let mut concepts = Arena::new();
        let subsumed_concept = concepts.push(Concept::new());
        let mut eq_candidate_concept_data = Concept::new();
        eq_candidate_concept_data.set_operator_code(CCEQ);
        let eq_candidate_concept = concepts.push(eq_candidate_concept_data);
        let eq_candidate_target = concepts.push(Concept::new());
        let eq_non_candidate_concept = concepts.push(Concept::new());
        let mut ont_item = OptimizedKPSetClassOntologyClassificationItem::new();
        let subsumed_item =
            ont_item.get_concept_satisfiable_test_item(subsumed_concept, true, &concepts);
        let _eq_candidate_item =
            ont_item.get_concept_satisfiable_test_item(eq_candidate_concept, true, &concepts);
        let eq_non_candidate_item =
            ont_item.get_concept_satisfiable_test_item(eq_non_candidate_concept, true, &concepts);
        ont_item
            .get_equivalent_concept_candidate_hash_mut()
            .insert(eq_candidate_concept, eq_candidate_target);
        ont_item
            .get_equivaltent_concept_non_candidate_set_mut()
            .insert(eq_non_candidate_concept);

        let poss_data =
            ClassificationInitializePossibleClassSubsumptionData::new(eq_candidate_concept);
        let mut message = ClassificationInitializePossibleClassSubsumptionMessageData::new();
        message.init_classification_possible_subsumption_message_data(
            subsumed_concept,
            Some(vec![poss_data]),
            false,
            None,
        );
        let mut thread = OptimizedKPSetClassSubsumptionClassifierThread::new();

        assert!(
            thread.process_initialize_possible_class_subsumption_message(
                &mut ont_item,
                &message,
                &concepts,
            )
        );

        assert_eq!(ont_item.get_remaining_possible_subsumption_tests_count(), 1);
        assert_eq!(ont_item.get_possible_subsumer_count(), 1);
        let poss_map = ont_item.get_concept_satisfiable_test_item_container()
            [subsumed_item.index()]
        .get_possible_subsumption_map_ref()
        .expect("possible map");
        assert!(poss_map.get(eq_candidate_concept).is_none());
        assert_eq!(
            poss_map
                .get(eq_non_candidate_concept)
                .expect("non-candidate eq data")
                .get_class_item(),
            eq_non_candidate_item
        );
    }

    #[test]
    fn kpset_class_thread_empty_initialization_invalidates_unknown_possible_entries() {
        let mut concepts = Arena::new();
        let subsumed_concept = concepts.push(Concept::new());
        let poss_concept = concepts.push(Concept::new());
        let mut ont_item = OptimizedKPSetClassOntologyClassificationItem::new();
        let subsumed_item =
            ont_item.get_concept_satisfiable_test_item(subsumed_concept, true, &concepts);
        let poss_item = ont_item.get_concept_satisfiable_test_item(poss_concept, true, &concepts);
        let map = ont_item
            .get_concept_satisfiable_test_item_mut(subsumed_item)
            .expect("subsumed item")
            .get_possible_subsumption_map(true)
            .expect("possible map");
        map.insert(
            poss_concept,
            OptimizedKPSetClassPossibleSubsumptionData::new(poss_item),
        );
        map.inc_remaining_possible_subsumption_count(1);
        ont_item
            .inc_remaining_possible_subsumption_tests_count(1)
            .inc_possible_subsumer_count(1);

        let mut message = ClassificationInitializePossibleClassSubsumptionMessageData::new();
        message.init_classification_possible_subsumption_message_data(
            subsumed_concept,
            None,
            false,
            None,
        );
        let mut thread = OptimizedKPSetClassSubsumptionClassifierThread::new();

        assert!(
            thread.process_initialize_possible_class_subsumption_message(
                &mut ont_item,
                &message,
                &concepts,
            )
        );

        assert_eq!(ont_item.get_remaining_possible_subsumption_tests_count(), 0);
        assert_eq!(ont_item.get_true_possible_subsumer_count(), 1);
        let data = ont_item.get_concept_satisfiable_test_item_container()[subsumed_item.index()]
            .get_possible_subsumption_map_ref()
            .expect("possible map")
            .get(poss_concept)
            .expect("possible data");
        assert!(data.is_subsumption_invalided());
        assert!(data.is_subsumption_updated());
    }

    #[test]
    fn kpset_class_thread_existing_initialization_invalidates_stale_non_eq_entries() {
        let mut concepts = Arena::new();
        let subsumed_concept = concepts.push(Concept::new());
        let retained_concept = concepts.push(Concept::new());
        let stale_concept = concepts.push(Concept::new());
        let mut eq_concept_data = Concept::new();
        eq_concept_data.set_operator_code(CCEQ);
        let eq_concept = concepts.push(eq_concept_data);
        let mut ont_item = OptimizedKPSetClassOntologyClassificationItem::new();
        let subsumed_item =
            ont_item.get_concept_satisfiable_test_item(subsumed_concept, true, &concepts);
        let retained_item =
            ont_item.get_concept_satisfiable_test_item(retained_concept, true, &concepts);
        let stale_item = ont_item.get_concept_satisfiable_test_item(stale_concept, true, &concepts);
        let eq_item = ont_item.get_concept_satisfiable_test_item(eq_concept, true, &concepts);
        let map = ont_item
            .get_concept_satisfiable_test_item_mut(subsumed_item)
            .expect("subsumed item")
            .get_possible_subsumption_map(true)
            .expect("possible map");
        for (concept, item) in [
            (retained_concept, retained_item),
            (stale_concept, stale_item),
            (eq_concept, eq_item),
        ] {
            map.insert(
                concept,
                OptimizedKPSetClassPossibleSubsumptionData::new(item),
            );
            map.inc_remaining_possible_subsumption_count(1);
        }
        ont_item
            .inc_remaining_possible_subsumption_tests_count(3)
            .inc_possible_subsumer_count(3);
        let retained_data =
            ClassificationInitializePossibleClassSubsumptionData::new(retained_concept);
        let mut message = ClassificationInitializePossibleClassSubsumptionMessageData::new();
        message.init_classification_possible_subsumption_message_data(
            subsumed_concept,
            Some(vec![retained_data]),
            false,
            None,
        );
        let mut thread = OptimizedKPSetClassSubsumptionClassifierThread::new();

        assert!(
            thread.process_initialize_possible_class_subsumption_message(
                &mut ont_item,
                &message,
                &concepts,
            )
        );

        assert_eq!(ont_item.get_remaining_possible_subsumption_tests_count(), 2);
        let poss_map = ont_item.get_concept_satisfiable_test_item_container()
            [subsumed_item.index()]
        .get_possible_subsumption_map_ref()
        .expect("possible map");
        assert!(!poss_map
            .get(retained_concept)
            .expect("retained data")
            .is_subsumption_invalided());
        let stale_data = poss_map.get(stale_concept).expect("stale data");
        assert!(stale_data.is_subsumption_invalided());
        assert!(stale_data.is_subsumption_updated());
        assert!(!poss_map
            .get(eq_concept)
            .expect("eq data")
            .is_subsumption_invalided());
    }

    #[test]
    fn kpset_class_thread_dispatches_all_typed_class_messages() {
        let mut concepts = Arena::new();
        let subsumed_concept = concepts.push(Concept::new());
        let subsumer_concept = concepts.push(Concept::new());
        let poss_concept = concepts.push(Concept::new());
        let pm_concept = concepts.push(Concept::new());
        let mut ont_item = OptimizedKPSetClassOntologyClassificationItem::new();
        let subsumed_item =
            ont_item.get_concept_satisfiable_test_item(subsumed_concept, true, &concepts);
        let _subsumer_item =
            ont_item.get_concept_satisfiable_test_item(subsumer_concept, true, &concepts);
        let _poss_item = ont_item.get_concept_satisfiable_test_item(poss_concept, true, &concepts);
        let pm_item = ont_item.get_concept_satisfiable_test_item(pm_concept, true, &concepts);

        let mut class_message = ClassificationClassSubsumptionMessageData::new();
        class_message.init_classification_subsumption_message_data(
            subsumed_concept,
            Some(vec![subsumer_concept]),
        );
        let poss_data = ClassificationInitializePossibleClassSubsumptionData::new(poss_concept);
        let mut init_message = ClassificationInitializePossibleClassSubsumptionMessageData::new();
        init_message.init_classification_possible_subsumption_message_data(
            subsumed_concept,
            Some(vec![poss_data]),
            false,
            None,
        );
        let mut update_message = ClassificationUpdatePossibleClassSubsumptionMessageData::new();
        update_message.init_classification_possible_subsumption_message_data(subsumed_concept);
        let mut pm_hash = ClassificationClassPseudoModelHash::new();
        pm_hash
            .get_pseudo_model_data_mut(0, true)
            .expect("pseudo-model data")
            .set_valid_concept_map(true);
        let mut pm_message = ClassificationPseudoModelIdentifierMessageData::new();
        pm_message
            .init_classification_pseudo_model_identifier_message_data(pm_concept, pm_hash, 92);

        let mut linker = ClassificationMessageDataLinker::from_message(
            ClassificationMessageDataPayload::from_pseudo_model_identifier(pm_message),
        );
        linker.prepend_message(
            ClassificationMessageDataPayload::from_update_possible_class_subsumption(
                update_message,
            ),
        );
        linker.prepend_message(
            ClassificationMessageDataPayload::from_initialize_possible_class_subsumption(
                init_message,
            ),
        );
        linker.prepend_message(ClassificationMessageDataPayload::from_class_subsumption(
            class_message,
        ));
        let mut thread = OptimizedKPSetClassSubsumptionClassifierThread::new();

        assert!(thread.process_classification_message_data_linker(
            &mut ont_item,
            &linker,
            &concepts
        ));

        assert_eq!(thread.get_processed_subsumption_message_count(), 1);
        assert_eq!(
            thread.get_processed_possible_subsumption_init_message_count(),
            1
        );
        assert_eq!(
            thread.get_processed_possible_subsumption_update_message_count(),
            1
        );
        assert_eq!(thread.get_processed_pseudo_model_message_count(), 1);
        assert!(
            ont_item.get_concept_satisfiable_test_item_container()[subsumed_item.index()]
                .is_result_satisfiable_derivated()
        );
        assert!(
            ont_item.get_concept_satisfiable_test_item_container()[pm_item.index()]
                .is_class_pseudo_model_initalized()
        );
    }

    #[test]
    fn kpset_role_ontology_item_get_or_create_and_tracks_queues() {
        let role = RoleId::new(31);
        let mut item = OptimizedKPSetRoleOntologyClassificationItem::new();

        assert!(item.get_role_satisfiable_test_item(role, false).is_none());
        let test_item = item.get_role_satisfiable_test_item(role, true);
        assert!(test_item.is_some());
        assert_eq!(item.get_role_satisfiable_test_item(role, false), test_item);
        assert_eq!(item.get_role_satisfiable_test_item_list().len(), 1);
        assert_eq!(
            item.get_role_satisfiable_test_item_list()[test_item.index()].get_testing_role(),
            role
        );
        assert_eq!(
            item.get_role_satisfiable_test_item_hash().get(&role),
            Some(&test_item)
        );

        item.set_top_role_satisfiable_test_item(test_item)
            .set_bottom_role_satisfiable_test_item(test_item)
            .add_satisfiable_role_item(test_item);
        item.get_next_satisfiable_testing_item_list_mut()
            .push(test_item);
        item.get_next_candidate_satisfiable_testing_item_set_mut()
            .insert(test_item);
        item.get_remaining_candidate_satisfiable_testing_item_set_mut()
            .insert(test_item);
        item.get_next_possible_subsumption_testing_item_list_mut()
            .push(test_item);
        item.get_current_possible_subsumption_testing_item_set_mut()
            .insert(test_item);
        item.get_remaining_possible_subsumption_testing_set_mut()
            .insert(test_item);

        assert_eq!(item.get_top_role_satisfiable_test_item(), test_item);
        assert_eq!(item.get_bottom_role_satisfiable_test_item(), test_item);
        assert_eq!(item.get_satisfiable_role_item_list(), &[test_item]);
        assert_eq!(item.get_next_satisfiable_testing_item_list(), &[test_item]);
        assert!(item
            .get_next_candidate_satisfiable_testing_item_set()
            .contains(&test_item));
        assert!(item
            .get_remaining_candidate_satisfiable_testing_item_set()
            .contains(&test_item));
        assert_eq!(
            item.get_next_possible_subsumption_testing_item_list(),
            &[test_item]
        );
        assert!(item
            .get_current_possible_subsumption_testing_item_set()
            .contains(&test_item));
        assert_eq!(item.get_remaining_possible_subsumption_testing_count(), 1);
    }

    #[test]
    fn kpset_class_ontology_item_tracks_counters_and_phase_flags() {
        let mut item = OptimizedKPSetClassOntologyClassificationItem::new();
        assert!(item.has_all_satisfiable_tests_completed());
        assert!(!item.has_remaining_satisfiable_tests());

        item.inc_remaining_satisfiable_tests_count(5)
            .inc_running_satisfiable_tests_count(2)
            .dec_remaining_satisfiable_tests_count(3)
            .dec_running_satisfiable_tests_count(1)
            .set_satisfiable_testing_phase_finished(true)
            .set_possible_subsumption_testing_phase_finished(true)
            .set_remaining_possible_subsumption_tests_count(4)
            .inc_remaining_possible_subsumption_tests_count(3)
            .dec_remaining_possible_subsumption_tests_count(2)
            .inc_running_possible_subsumption_tests_count(6)
            .dec_running_possible_subsumption_tests_count(1);

        assert_eq!(item.get_remaining_satisfiable_tests_count(), 2);
        assert_eq!(item.get_running_satisfiable_tests_count(), 1);
        assert!(!item.has_all_satisfiable_tests_completed());
        assert!(item.has_remaining_satisfiable_tests());
        assert!(item.has_satisfiable_testing_phase_finished());
        assert!(item.has_possible_subsumption_testing_phase_finished());
        assert_eq!(item.get_remaining_possible_subsumption_tests_count(), 5);
        assert!(item.has_remaining_possible_subsumption_tests());

        item.set_calculated_possible_subsumer_count(10)
            .set_calculated_true_possible_subsumer_count(4)
            .set_calculated_false_possible_subsumer_count(6)
            .inc_calculated_possible_subsumer_count(1)
            .inc_calculated_true_possible_subsumer_count(2)
            .inc_calculated_false_possible_subsumer_count(3)
            .set_possible_subsumer_count(20)
            .set_true_possible_subsumer_count(8)
            .set_false_possible_subsumer_count(12)
            .inc_possible_subsumer_count(1)
            .inc_true_possible_subsumer_count(2)
            .inc_false_possible_subsumer_count(3);

        assert_eq!(item.get_calculated_possible_subsumer_count(), 11);
        assert_eq!(item.get_calculated_true_possible_subsumer_count(), 6);
        assert_eq!(item.get_calculated_false_possible_subsumer_count(), 9);
        assert_eq!(item.get_possible_subsumer_count(), 21);
        assert_eq!(item.get_true_possible_subsumer_count(), 10);
        assert_eq!(item.get_false_possible_subsumer_count(), 15);
    }

    #[test]
    fn kpset_role_ontology_item_tracks_counters_and_phase_flags() {
        let mut item = OptimizedKPSetRoleOntologyClassificationItem::new();
        assert!(item.has_all_satisfiable_tests_completed());
        assert!(!item.has_remaining_satisfiable_tests());

        item.inc_remaining_satisfiable_tests_count(6)
            .inc_running_satisfiable_tests_count(3)
            .dec_remaining_satisfiable_tests_count(2)
            .dec_running_satisfiable_tests_count(1)
            .set_satisfiable_testing_phase_finished(true)
            .set_possible_subsumption_testing_phase_finished(true)
            .set_remaining_possible_subsumption_tests_count(5)
            .inc_remaining_possible_subsumption_tests_count(4)
            .dec_remaining_possible_subsumption_tests_count(3)
            .inc_running_possible_subsumption_tests_count(7)
            .dec_running_possible_subsumption_tests_count(2);

        assert_eq!(item.get_remaining_satisfiable_tests_count(), 4);
        assert_eq!(item.get_running_satisfiable_tests_count(), 2);
        assert!(!item.has_all_satisfiable_tests_completed());
        assert!(item.has_remaining_satisfiable_tests());
        assert!(item.has_satisfiable_testing_phase_finished());
        assert!(item.has_possible_subsumption_testing_phase_finished());
        assert_eq!(item.get_remaining_possible_subsumption_tests_count(), 6);
        assert!(item.has_remaining_possible_subsumption_tests());

        item.set_calculated_possible_subsumer_count(30)
            .set_calculated_true_possible_subsumer_count(14)
            .set_calculated_false_possible_subsumer_count(16)
            .inc_calculated_possible_subsumer_count(1)
            .inc_calculated_true_possible_subsumer_count(2)
            .inc_calculated_false_possible_subsumer_count(3)
            .set_possible_subsumer_count(40)
            .set_true_possible_subsumer_count(18)
            .set_false_possible_subsumer_count(22)
            .inc_possible_subsumer_count(1)
            .inc_true_possible_subsumer_count(2)
            .inc_false_possible_subsumer_count(3);

        assert_eq!(item.get_calculated_possible_subsumer_count(), 31);
        assert_eq!(item.get_calculated_true_possible_subsumer_count(), 16);
        assert_eq!(item.get_calculated_false_possible_subsumer_count(), 19);
        assert_eq!(item.get_possible_subsumer_count(), 41);
        assert_eq!(item.get_true_possible_subsumer_count(), 20);
        assert_eq!(item.get_false_possible_subsumer_count(), 25);
    }

    #[test]
    fn kpset_class_testing_item_tracks_passive_classification_state() {
        let marker = IndividualDependenceTrackingMarkerId::new(71);
        let mut item = OptimizedKPSetClassTestingItem::new();
        item.init_kpset_class_testing_item(ConceptId::new(73), marker);
        let other = OptimizedKPSetClassTestingItemId::new(2);

        assert_eq!(item.get_testing_concept(), ConceptId::new(73));
        assert_eq!(item.individual_dependence_tracking_marker(), marker);
        assert!(item.has_only_processed_predecessor_items());
        assert!(item.is_more_concept_classification_information_required());

        item.set_satisfiable_concept_hierarchy_node(101)
            .set_unprocessed_predecessor_items(3)
            .inc_unprocessed_predecessor_items(2)
            .dec_unprocessed_predecessor_items(1)
            .add_successor_satisfiable_test_item(other)
            .add_subsuming_concept_item(other)
            .add_subsuming_concept_item(other)
            .set_satisfiable_test_ordered(true)
            .set_satisfiable_tested(true)
            .set_satisfiable_tested_result(true)
            .set_result_unsatisfiable_derivated(true)
            .set_result_satisfiable_derivated(true)
            .set_equivalent_item(true)
            .set_predecessor_item(true)
            .set_possible_subsumption_map_initialized(true)
            .set_propagation_connected(true)
            .set_class_pseudo_model_initalized(true)
            .add_up_propagation_item(other)
            .add_down_propagation_item(other)
            .set_possible_subsumed_list(vec![other])
            .set_fast_satisfiability_tested_saturation_cache_entry(17)
            .set_successfully_fast_satisfiability_tested(true);
        item.get_possible_subsumption_map(true)
            .expect("class possible-subsumption map")
            .set_remaining_possible_subsumption_count(1);
        item.get_possible_subsumed_set(true)
            .expect("class possible-subsumed set")
            .insert(other);

        assert_eq!(item.get_satisfiable_concept_hierarchy_node(), 101);
        assert_eq!(item.get_unprocessed_predecessor_item_count(), 4);
        assert_eq!(item.get_successor_item_list(), &[other]);
        assert_eq!(item.get_subsuming_concept_item_count(), 1);
        assert_eq!(item.get_subsuming_concept_item_list(), &[other]);
        assert!(item.has_subsumer_concept_item(other));
        assert!(item.is_satisfiable_test_ordered());
        assert!(item.is_satisfiable_tested());
        assert!(item.get_satisfiable_tested_result());
        assert!(item.is_result_unsatisfiable_derivated());
        assert!(item.is_result_satisfiable_derivated());
        assert!(item.is_equivalent_item());
        assert!(item.is_predecessor_item());
        assert!(!item.is_more_concept_classification_information_required());
        assert!(item.has_class_possible_subsumption_map());
        assert!(item.is_possible_subsumption_map_initialized());
        assert!(item.is_propagation_connected());
        assert!(item.is_class_pseudo_model_initalized());
        assert!(item.get_up_propagation_item_set().contains(&other));
        assert!(item.get_down_propagation_item_set().contains(&other));
        assert_eq!(item.get_possible_subsumed_list(), Some(&[other][..]));
        assert!(item.has_remaining_possible_subsumed_items());
        assert_eq!(
            item.get_fast_satisfiability_tested_saturation_cache_entry(),
            17
        );
        assert!(item.has_successfully_fast_satisfiability_tested());
    }

    #[test]
    fn kpset_class_testing_item_exposes_embedded_pseudo_model_without_reinit_clear() {
        let marker = IndividualDependenceTrackingMarkerId::new(91);
        let mut item = OptimizedKPSetClassTestingItem::new();
        let mut hash = ClassificationClassPseudoModelHash::new();
        hash.get_pseudo_model_data_mut(0, true)
            .expect("pseudo-model data")
            .set_valid_concept_map(true);

        item.get_class_pseudo_model_mut()
            .set_pseudo_model_hash(Some(hash));
        item.set_class_pseudo_model_initalized(true);
        item.init_kpset_class_testing_item(ConceptId::new(93), marker);

        assert!(!item.is_class_pseudo_model_initalized());
        assert_eq!(
            item.get_class_pseudo_model()
                .get_pseudo_model_hash()
                .expect("embedded pseudo-model hash")
                .get_count(),
            1
        );
    }

    #[test]
    fn kpset_role_testing_item_tracks_passive_classification_state() {
        let mut item = OptimizedKPSetRoleTestingItem::new();
        item.init_satisfiable_testing_item(RoleId::new(79));
        let other = OptimizedKPSetRoleTestingItemId::new(3);

        assert_eq!(item.get_testing_role(), RoleId::new(79));
        assert!(item.has_only_processed_predecessor_items());
        assert!(item.is_more_concept_classification_information_required());

        item.set_temporary_marker_concept(ConceptId::new(81))
            .set_temporary_propagation_concept(ConceptId::new(83))
            .set_temporary_exist_concept(ConceptId::new(85))
            .set_satisfiable_role_hierarchy_node(103)
            .set_unprocessed_predecessor_items(4)
            .inc_unprocessed_predecessor_items(2)
            .dec_unprocessed_predecessor_items(1)
            .add_successor_satisfiable_test_item(other)
            .add_subsumer_role_item(other)
            .add_subsumer_role_item(other)
            .set_satisfiable_test_ordered(true)
            .set_satisfiable_tested(true)
            .set_satisfiable_tested_result(true)
            .set_result_unsatisfiable_derivated(true)
            .set_result_satisfiable_derivated(true)
            .set_equivalent_item(true)
            .set_predecessor_item(true)
            .set_possible_subsumption_map_initialized(true)
            .set_propagation_connected(true)
            .add_up_propagation_item(other)
            .add_down_propagation_item(other)
            .set_possible_subsumed_list(vec![other]);
        item.get_possible_subsumption_map(true)
            .expect("role possible-subsumption map")
            .set_remaining_possible_subsumption_count(1);
        item.get_possible_subsumer_set(true)
            .expect("role possible-subsumer set")
            .insert(other);

        assert_eq!(item.get_temporary_marker_concept(), ConceptId::new(81));
        assert_eq!(item.get_temporary_propagation_concept(), ConceptId::new(83));
        assert_eq!(item.get_temporary_exist_concept(), ConceptId::new(85));
        assert_eq!(item.get_satisfiable_role_hierarchy_node(), 103);
        assert_eq!(item.get_unprocessed_predecessor_item_count(), 5);
        assert_eq!(item.get_successor_item_list(), &[other]);
        assert_eq!(item.get_subsumer_role_item_count(), 1);
        assert_eq!(item.get_subsumer_role_item_list(), &[other]);
        assert!(item.has_subsumer_role_item(other));
        assert!(item.is_satisfiable_test_ordered());
        assert!(item.is_satisfiable_tested());
        assert!(item.get_satisfiable_tested_result());
        assert!(item.is_result_unsatisfiable_derivated());
        assert!(item.is_result_satisfiable_derivated());
        assert!(item.is_equivalent_item());
        assert!(item.is_predecessor_item());
        assert!(!item.is_more_concept_classification_information_required());
        assert!(item.has_property_possible_subsumption_map());
        assert!(item.is_possible_subsumption_map_initialized());
        assert!(item.is_propagation_connected());
        assert!(item.get_up_propagation_item_set().contains(&other));
        assert!(item.get_down_propagation_item_set().contains(&other));
        assert_eq!(item.get_possible_subsumer_list(), Some(&[other][..]));
        assert!(item.has_remaining_possible_subsumed_items());
    }

    #[test]
    fn kpset_role_ontology_item_tracks_temporary_role_classification_storage() {
        let mut item = OptimizedKPSetRoleOntologyClassificationItem::new();
        let marker_concept = ConceptId::new(91);
        let role_item = OptimizedKPSetRoleTestingItemId::new(5);

        assert_eq!(item.get_temporary_role_classification_ontology(), INVALID);
        assert!(!item.is_data_roles_classification());
        assert!(item.get_temporary_top_concept().is_none());
        assert!(item.get_temporary_top_data_range_concept().is_none());
        assert!(item.get_temporary_role_setup_top_concept().is_none());
        assert!(item.get_marker_concept_instances_item_hash().is_empty());
        assert!(item.get_temporary_all_propagation_concept().is_none());
        assert!(item.get_temporary_propagation_individual().is_none());
        assert!(item.get_temporary_marker_individual().is_none());

        item.set_temporary_role_classification_ontology(101)
            .set_temporary_all_propagation_concept(ConceptId::new(93))
            .set_temporary_top_concept(ConceptId::new(95))
            .set_temporary_top_data_range_concept(ConceptId::new(96))
            .set_temporary_propagation_individual(IndividualId::new(97))
            .set_temporary_marker_individual(IndividualId::new(99));
        item.get_marker_concept_instances_item_hash_mut()
            .insert(marker_concept, role_item);

        assert_eq!(item.get_temporary_role_classification_ontology(), 101);
        assert_eq!(
            item.get_marker_concept_instances_item_hash()
                .get(&marker_concept),
            Some(&role_item)
        );
        assert_eq!(
            item.get_temporary_all_propagation_concept(),
            ConceptId::new(93)
        );
        assert_eq!(item.get_temporary_top_concept(), ConceptId::new(95));
        assert_eq!(
            item.get_temporary_top_data_range_concept(),
            ConceptId::new(96)
        );
        assert_eq!(
            item.get_temporary_role_setup_top_concept(),
            ConceptId::new(95)
        );
        item.set_data_roles_classification(true);
        assert!(item.is_data_roles_classification());
        assert_eq!(
            item.get_temporary_role_setup_top_concept(),
            ConceptId::new(96)
        );
        assert_eq!(
            item.get_temporary_propagation_individual(),
            IndividualId::new(97)
        );
        assert_eq!(
            item.get_temporary_marker_individual(),
            IndividualId::new(99)
        );
    }

    #[test]
    fn kpset_role_thread_creates_temporary_role_classification_ontology_payload() {
        let role_a = RoleId::new(11);
        let role_b = RoleId::new(13);
        let bottom_role = RoleId::new(17);
        let mut ont_item = OptimizedKPSetRoleOntologyClassificationItem::new();
        let item_a = ont_item.get_role_satisfiable_test_item(role_a, true);
        let item_b = ont_item.get_role_satisfiable_test_item(role_b, true);
        let bottom_item = ont_item.get_role_satisfiable_test_item(bottom_role, true);
        ont_item.set_bottom_role_satisfiable_test_item(bottom_item);

        let mut ontology_arenas = OntologyArenas::new();
        let mut thread = OptimizedKPSetRoleSubsumptionClassifierThread::new();
        thread.create_temporary_role_classification_ontology(
            &mut ont_item,
            &mut ontology_arenas,
            701,
        );

        assert_eq!(ont_item.get_temporary_role_classification_ontology(), 701);
        let propagation_individual = ont_item.get_temporary_propagation_individual();
        let marker_individual = ont_item.get_temporary_marker_individual();
        assert!(ontology_arenas
            .individual(propagation_individual)
            .is_temporary_individual());
        assert!(ontology_arenas
            .individual(propagation_individual)
            .is_fake_individual());
        assert!(ontology_arenas
            .individual(marker_individual)
            .is_temporary_individual());
        assert!(ontology_arenas
            .individual(marker_individual)
            .is_fake_individual());

        let all_prop = ont_item.get_temporary_all_propagation_concept();
        let all_prop_concept = ontology_arenas.concept(all_prop);
        assert_eq!(all_prop_concept.get_operator_code(), CCAND);
        assert_eq!(all_prop_concept.get_operand_count(), 2);

        let role_a_item = &ont_item.get_role_satisfiable_test_item_list()[item_a.index()];
        let marker_a = role_a_item.get_temporary_marker_concept();
        let prop_a = role_a_item.get_temporary_propagation_concept();
        let exist_a = role_a_item.get_temporary_exist_concept();
        assert_eq!(
            ont_item
                .get_marker_concept_instances_item_hash()
                .get(&marker_a),
            Some(&item_a)
        );
        assert!(all_prop_concept
            .get_operand_list()
            .iter()
            .any(|operand| operand.target == prop_a && !operand.negated));

        let marker_a_concept = ontology_arenas.concept(marker_a);
        assert_eq!(marker_a_concept.get_operator_code(), CCMARKER);
        assert_eq!(marker_a_concept.get_role(), role_a);

        let prop_a_concept = ontology_arenas.concept(prop_a);
        assert_eq!(prop_a_concept.get_operator_code(), CCALL);
        assert_eq!(prop_a_concept.get_role(), role_a);
        assert_eq!(prop_a_concept.get_operand_count(), 1);
        assert_eq!(prop_a_concept.get_operand_list()[0].target, marker_a);
        assert!(!prop_a_concept.get_operand_list()[0].negated);

        let exist_a_concept = ontology_arenas.concept(exist_a);
        assert_eq!(exist_a_concept.get_operator_code(), CCVALUE);
        assert_eq!(exist_a_concept.get_role(), role_a);
        assert_eq!(exist_a_concept.get_nominal_individual(), marker_individual);

        let role_b_item = &ont_item.get_role_satisfiable_test_item_list()[item_b.index()];
        assert_eq!(
            ontology_arenas
                .concept(role_b_item.get_temporary_marker_concept())
                .get_role(),
            role_b
        );
        assert!(ont_item
            .get_role_satisfiable_test_item_list()
            .get(bottom_item.index())
            .expect("bottom item")
            .get_temporary_marker_concept()
            .is_none());

        thread.create_temporary_role_classification_ontology(
            &mut ont_item,
            &mut ontology_arenas,
            999,
        );
        assert_eq!(ont_item.get_temporary_role_classification_ontology(), 701);
        assert_eq!(ont_item.get_temporary_all_propagation_concept(), all_prop);
    }

    #[test]
    fn kpset_class_testing_item_sorts_subsuming_items_by_descending_subsumer_count() {
        let mut items = vec![
            OptimizedKPSetClassTestingItem::new(),
            OptimizedKPSetClassTestingItem::new(),
            OptimizedKPSetClassTestingItem::new(),
            OptimizedKPSetClassTestingItem::new(),
        ];
        let item_1 = OptimizedKPSetClassTestingItemId::new(1);
        let item_2 = OptimizedKPSetClassTestingItemId::new(2);
        let item_3 = OptimizedKPSetClassTestingItemId::new(3);
        items[1]
            .add_subsuming_concept_item(OptimizedKPSetClassTestingItemId::new(10))
            .add_subsuming_concept_item(OptimizedKPSetClassTestingItemId::new(11));
        items[3].add_subsuming_concept_item(OptimizedKPSetClassTestingItemId::new(12));
        let mut item = OptimizedKPSetClassTestingItem::new();
        item.add_subsuming_concept_item(item_2)
            .add_subsuming_concept_item(item_3)
            .add_subsuming_concept_item(item_1);

        let sorted = item.sort_subsuming_concept_item_list(&items);

        assert_eq!(sorted, &[item_1, item_3, item_2]);
    }

    #[test]
    fn kpset_role_testing_item_sorts_subsuming_items_by_descending_subsumer_count() {
        let mut items = vec![
            OptimizedKPSetRoleTestingItem::new(),
            OptimizedKPSetRoleTestingItem::new(),
            OptimizedKPSetRoleTestingItem::new(),
            OptimizedKPSetRoleTestingItem::new(),
        ];
        let item_1 = OptimizedKPSetRoleTestingItemId::new(1);
        let item_2 = OptimizedKPSetRoleTestingItemId::new(2);
        let item_3 = OptimizedKPSetRoleTestingItemId::new(3);
        items[2]
            .add_subsumer_role_item(OptimizedKPSetRoleTestingItemId::new(10))
            .add_subsumer_role_item(OptimizedKPSetRoleTestingItemId::new(11))
            .add_subsumer_role_item(OptimizedKPSetRoleTestingItemId::new(12));
        items[1].add_subsumer_role_item(OptimizedKPSetRoleTestingItemId::new(13));
        let mut item = OptimizedKPSetRoleTestingItem::new();
        item.add_subsumer_role_item(item_1)
            .add_subsumer_role_item(item_3)
            .add_subsumer_role_item(item_2);

        let sorted = item.sort_subsuming_concept_item_list(&items);

        assert_eq!(sorted, &[item_2, item_1, item_3]);
    }

    #[test]
    fn kpset_class_tell_concept_supsumption_adds_live_reference_linking_item() {
        let mut concepts = Arena::new();
        let mut concept_process_datas = Arena::new();
        let mut concept_reference_linking_datas = Arena::new();
        let subsumer_item = OptimizedKPSetClassTestingItemId::new(7);

        let mut con_ref_linking = ConceptSaturationReferenceLinkingData::new();
        con_ref_linking.set_classifier_reference_linking_data(subsumer_item.raw);
        let con_ref_linking_id = concept_reference_linking_datas.push(con_ref_linking);

        let mut con_pro_data = ConceptProcessData::new();
        con_pro_data.set_concept_reference_linking(con_ref_linking_id);
        let con_pro_data_id = concept_process_datas.push(con_pro_data);

        let mut subsumer_concept = Concept::new();
        subsumer_concept.set_concept_data(con_pro_data_id.raw);
        let subsumer_concept_id = concepts.push(subsumer_concept);

        let mut item = OptimizedKPSetClassTestingItem::new();
        item.tell_concept_supsumption(
            ConceptId::NONE,
            subsumer_concept_id,
            &concepts,
            &concept_process_datas,
            &concept_reference_linking_datas,
            None,
        );

        assert!(item.has_subsumer_concept_item(subsumer_item));
        assert_eq!(item.get_subsuming_concept_item_list(), &[subsumer_item]);
    }

    #[test]
    fn kpset_class_tell_concept_supsumption_uses_invalidated_fallback_hash() {
        let mut concepts = Arena::new();
        let mut concept_process_datas = Arena::new();
        let concept_reference_linking_datas = Arena::new();
        let fallback_item = OptimizedKPSetClassTestingItemId::new(11);

        let mut con_pro_data = ConceptProcessData::new();
        con_pro_data.set_invalidated_reference_linking(true);
        let con_pro_data_id = concept_process_datas.push(con_pro_data);

        let mut subsumer_concept = Concept::new();
        subsumer_concept.set_concept_data(con_pro_data_id.raw);
        let subsumer_concept_id = concepts.push(subsumer_concept);
        let mut fallback_hash = HashMap::new();
        fallback_hash.insert(subsumer_concept_id, fallback_item.raw);

        let mut item = OptimizedKPSetClassTestingItem::new();
        item.tell_concept_supsumption(
            ConceptId::NONE,
            subsumer_concept_id,
            &concepts,
            &concept_process_datas,
            &concept_reference_linking_datas,
            Some(&fallback_hash),
        );

        assert!(item.has_subsumer_concept_item(fallback_item));
        assert_eq!(item.get_subsuming_concept_item_list(), &[fallback_item]);
    }

    #[test]
    fn kpset_role_tell_concept_supsumption_adds_live_reference_linking_item() {
        let mut concepts = Arena::new();
        let mut concept_process_datas = Arena::new();
        let mut concept_reference_linking_datas = Arena::new();
        let subsumer_item = OptimizedKPSetRoleTestingItemId::new(13);

        let mut con_ref_linking = ConceptSaturationReferenceLinkingData::new();
        con_ref_linking.set_classifier_reference_linking_data(subsumer_item.raw);
        let con_ref_linking_id = concept_reference_linking_datas.push(con_ref_linking);

        let mut con_pro_data = ConceptProcessData::new();
        con_pro_data.set_concept_reference_linking(con_ref_linking_id);
        let con_pro_data_id = concept_process_datas.push(con_pro_data);

        let mut subsumer_concept = Concept::new();
        subsumer_concept.set_concept_data(con_pro_data_id.raw);
        let subsumer_concept_id = concepts.push(subsumer_concept);

        let mut item = OptimizedKPSetRoleTestingItem::new();
        item.tell_concept_supsumption(
            ConceptId::NONE,
            subsumer_concept_id,
            &concepts,
            &concept_process_datas,
            &concept_reference_linking_datas,
        );

        assert!(item.has_subsumer_role_item(subsumer_item));
        assert_eq!(item.get_subsumer_role_item_list(), &[subsumer_item]);
    }

    #[test]
    fn kpset_tell_concept_supsumption_skips_top_subsumer_concept() {
        let mut concepts = Arena::new();
        let mut concept_process_datas = Arena::new();
        let mut concept_reference_linking_datas = Arena::new();
        let subsumer_item = OptimizedKPSetClassTestingItemId::new(17);

        let mut con_ref_linking = ConceptSaturationReferenceLinkingData::new();
        con_ref_linking.set_classifier_reference_linking_data(subsumer_item.raw);
        let con_ref_linking_id = concept_reference_linking_datas.push(con_ref_linking);

        let mut con_pro_data = ConceptProcessData::new();
        con_pro_data.set_concept_reference_linking(con_ref_linking_id);
        let con_pro_data_id = concept_process_datas.push(con_pro_data);

        let mut top_concept = Concept::new();
        top_concept
            .set_operator_code(CCTOP)
            .set_concept_data(con_pro_data_id.raw);
        let top_concept_id = concepts.push(top_concept);

        let mut item = OptimizedKPSetClassTestingItem::new();
        item.tell_concept_supsumption(
            ConceptId::NONE,
            top_concept_id,
            &concepts,
            &concept_process_datas,
            &concept_reference_linking_datas,
            None,
        );

        assert!(!item.has_subsumer_concept_item(subsumer_item));
        assert!(item.get_subsuming_concept_item_list().is_empty());
    }
}
