//! `generator` — narrow ports from Konclude `Source/Reasoner/Generator/`.
//!
//! The full generator layer builds calculation tasks from query jobs. This wave
//! ports the individual-dependence adapter transfer seam that classifier/realizer
//! jobs use before the completion algorithm's tracking path can observe it.

#![allow(dead_code)]

use std::collections::HashSet;

use super::model::ontology::OntologyArenas;
use super::model::substrate::NegLink;
use super::process::context::ProcessContext;
use super::process::databox::{
    ProcessingDataBox, ProcessingDataBoxConceptAssertion, ProcessingDataBoxIndividualTarget,
};
use super::process::node::{IndividualProcessNode, IndividualType};
use super::process::stubs::ProcessContextId;
use super::process::TrackPointId;
use super::task::calculation_job::{
    SatisfiableCalculationJob, SatisfiableCalculationJobIndividualTarget,
};
use super::task::satisfiable_task::SatisfiableCalculationTask;

/// Port of the currently live individual-dependence slice of
/// `CSatisfiableCalculationTaskFromCalculationJobGenerator`.
#[derive(Debug, Default, Clone)]
pub struct SatisfiableCalculationTaskFromCalculationJobGenerator;

impl SatisfiableCalculationTaskFromCalculationJobGenerator {
    /// Port of the constructor.
    pub fn new() -> Self {
        Self
    }

    /// Port of the adapter copy in
    /// `createSatisfiableCalculationTaskExtension` / `createSatisfiableCalculationTask`:
    ///
    /// ```text
    /// satCalcTask->setSatisfiableTaskIndividualDependenceTrackingAdapter(
    ///     satCalcJob->getSatisfiableTaskIndividualDependenceTrackingAdapter());
    /// if (satCalcTask->getSatisfiableTaskIndividualDependenceTrackingAdapter()) {
    ///     dataBox->setIndividualDependenceTrackingRequired(true);
    /// }
    /// ```
    pub fn transfer_individual_dependence_tracking_adapter(
        &self,
        sat_calc_job: &SatisfiableCalculationJob,
        sat_calc_task: &mut SatisfiableCalculationTask,
        data_box: &mut ProcessingDataBox,
    ) -> &Self {
        let adapter = sat_calc_job.get_satisfiable_task_individual_dependence_tracking_adapter();
        sat_calc_task.set_satisfiable_task_individual_dependence_tracking_adapter(adapter);
        if sat_calc_task
            .get_satisfiable_task_individual_dependence_tracking_adapter()
            .is_some()
        {
            data_box.set_individual_dependence_tracking_required(true);
        }
        self
    }

    /// Port of the classification adapter copy in
    /// `CSatisfiableCalculationTaskFromCalculationJobGenerator`.
    pub fn transfer_classification_message_adapters(
        &self,
        sat_calc_job: &SatisfiableCalculationJob,
        sat_calc_task: &mut SatisfiableCalculationTask,
    ) -> &Self {
        sat_calc_task.set_classification_message_adapter(
            sat_calc_job.get_satisfiable_classification_message_adapter(),
        );
        sat_calc_task.set_satisfiable_classification_role_marked_message_adapter(
            sat_calc_job.get_satisfiable_classification_role_marked_message_adapter(),
        );
        self
    }

    /// Port-side transfer of the calculation constructs created by
    /// `CSatisfiableCalculationJobGenerator`.
    pub fn transfer_concept_assertions(
        &self,
        sat_calc_job: &SatisfiableCalculationJob,
        sat_calc_task: &mut SatisfiableCalculationTask,
    ) -> &Self {
        sat_calc_task.set_satisfiable_calculation_job_concept_assertions(
            sat_calc_job
                .get_satisfiable_calculation_job_concept_assertions()
                .to_vec(),
        );
        self
    }

    /// Port-side materialization step for the generator block that iterates
    /// `CSatisfiableCalculationConstruct` entries and initializes databox/process
    /// state for their concept assertions.
    pub fn materialize_concept_assertions_to_processing_data_box(
        &self,
        sat_calc_task: &SatisfiableCalculationTask,
        data_box: &mut ProcessingDataBox,
    ) -> &Self {
        let assertions: Vec<ProcessingDataBoxConceptAssertion> = sat_calc_task
            .get_satisfiable_calculation_job_concept_assertions()
            .iter()
            .map(|assertion| {
                let target = match assertion.get_individual_target() {
                    SatisfiableCalculationJobIndividualTarget::Individual(individual) => {
                        ProcessingDataBoxIndividualTarget::Individual(individual)
                    }
                    SatisfiableCalculationJobIndividualTarget::FixedIndividualId(individual_id) => {
                        ProcessingDataBoxIndividualTarget::FixedIndividualId(individual_id)
                    }
                    SatisfiableCalculationJobIndividualTarget::RelativeNewNodeId(
                        relative_new_node_id,
                    ) => ProcessingDataBoxIndividualTarget::RelativeNewNodeId(relative_new_node_id),
                };
                ProcessingDataBoxConceptAssertion::new_for_target(
                    assertion.get_concept(),
                    assertion.is_negated(),
                    target,
                )
            })
            .collect();
        data_box.set_multiple_construction_individual_nodes(assertions.len() > 1);
        data_box.set_initializing_concept_assertions(assertions);
        self
    }

    /// Port of the named-individual branch of
    /// `createSatisfiableCalculationTaskExtension` that expands
    /// `CSatisfiableCalculationConstruct` concept linkers into
    /// `CIndividualProcessNode::mInitializingConceptLinkerIt`.
    pub fn expand_databox_initializing_concepts_to_process_nodes(
        &self,
        ontology: &OntologyArenas,
        process_context: &mut ProcessContext,
        data_box: &mut ProcessingDataBox,
        independent_base_dep_track_point: TrackPointId,
        base_task: bool,
    ) -> &Self {
        let staged_assertions = data_box.initializing_concept_assertions().to_vec();
        let base_individual_node_id = data_box.next_individual_node_id(false).max(
            data_box
                .individual_process_node_vector()
                .get_item_max_index()
                + 1,
        );
        let mut first_possible_individual_node_id = base_individual_node_id;
        let mut localized_base_task_nodes = HashSet::new();
        for assertion in staged_assertions {
            let (mut individual_node_id, nominal_individual) =
                match assertion.get_individual_target() {
                    ProcessingDataBoxIndividualTarget::Individual(individual) => {
                        let individual_id = ontology.individual(individual).get_individual_id();
                        (-individual_id, individual)
                    }
                    ProcessingDataBoxIndividualTarget::FixedIndividualId(individual_id) => {
                        (individual_id, super::model::IndividualId::NONE)
                    }
                    ProcessingDataBoxIndividualTarget::RelativeNewNodeId(relative_new_node_id) => (
                        base_individual_node_id + relative_new_node_id,
                        super::model::IndividualId::NONE,
                    ),
                };
            first_possible_individual_node_id =
                first_possible_individual_node_id.max(individual_node_id + 1);
            let mut ref_node = data_box
                .individual_process_node_vector()
                .get_data(individual_node_id);
            if base_task
                && ref_node.is_some()
                && !localized_base_task_nodes.contains(&individual_node_id)
            {
                let mut merged_ref_node = ref_node;
                while merged_ref_node.is_some()
                    && process_context
                        .node(merged_ref_node)
                        .has_merged_into_individual_node_id()
                {
                    let corr_individual_node_id = process_context
                        .node(merged_ref_node)
                        .merged_into_individual_node_id();
                    let corr_ref_node = data_box
                        .individual_process_node_vector()
                        .get_data(corr_individual_node_id);
                    if corr_ref_node.is_none() {
                        break;
                    }
                    individual_node_id = corr_individual_node_id;
                    merged_ref_node = corr_ref_node;
                }
                ref_node = merged_ref_node;
            }
            let node = if ref_node.is_some()
                && (!base_task || localized_base_task_nodes.contains(&individual_node_id))
            {
                ref_node
            } else {
                let mut local_indi = IndividualProcessNode::new(ProcessContextId::NONE);
                local_indi.set_dependency_track_point(independent_base_dep_track_point);
                if base_task && ref_node.is_some() {
                    let prev_node = ref_node;
                    local_indi.init_individual_process_node(
                        prev_node,
                        process_context.node_mut(prev_node),
                    );
                    local_indi
                        .clear_processing_queued()
                        .clear_processing_restriction_flags(
                            IndividualProcessNode::PRF_CACHEDCOMPUTEDTYPESADDED,
                        );
                }
                local_indi.set_individual_node_id(individual_node_id);
                if ref_node.is_none() && nominal_individual.is_some() {
                    let individual = ontology.individual(nominal_individual);
                    local_indi
                        .set_nominal_individual(nominal_individual)
                        .set_individual_type(IndividualType::Nominal)
                        .set_assertion_concept_assertions(
                            individual.get_assertion_concept_linker().to_vec(),
                        )
                        .set_assertion_data_assertions(
                            individual.get_assertion_data_linker().to_vec(),
                        )
                        .set_assertion_role_assertions(
                            individual.get_assertion_role_linker().to_vec(),
                        )
                        .set_reverse_assertion_role_assertions(
                            individual.get_reverse_assertion_role_linker().to_vec(),
                        );
                } else if nominal_individual.is_some() && local_indi.nominal_individual().is_none()
                {
                    local_indi
                        .set_nominal_individual(nominal_individual)
                        .set_individual_type(IndividualType::Nominal);
                }
                if nominal_individual.is_none() || base_task {
                    local_indi.add_processing_restriction_flags(
                        IndividualProcessNode::PRF_INVALIDBLOCKINGORCACHING,
                    );
                }
                local_indi.set_initializing_concept_linker(Vec::new());
                let node = process_context.alloc_node(local_indi);
                data_box
                    .individual_process_node_vector_mut()
                    .set_local_data(individual_node_id, node);
                if base_task {
                    localized_base_task_nodes.insert(individual_node_id);
                }
                let queue =
                    data_box.get_individual_immediately_processing_queue(process_context, true);
                process_context
                    .indi_unsorted_proc_queue_mut(queue)
                    .insert_indiviudal_process_node(node);
                if data_box.constructed_individual_node().is_none() {
                    data_box.set_constructed_individual_node(node);
                }
                node
            };

            if nominal_individual.is_some() {
                process_context
                    .node_mut(node)
                    .set_nominal_individual_triples_assertions(true);
            }
            process_context
                .node_mut(node)
                .add_initializing_concept_linker(vec![NegLink {
                    target: assertion.get_concept(),
                    negated: assertion.is_negated(),
                }]);
        }
        data_box.set_first_possible_individual_node_id(first_possible_individual_node_id);
        self
    }

    /// Port of
    /// `CSatisfiableCalculationTaskFromCalculationJobGenerator::createIndividualNominalNodeForCalculationTask`.
    pub fn create_individual_nominal_node_for_calculation_task(
        &self,
        ontology: &OntologyArenas,
        process_context: &mut ProcessContext,
        data_box: &mut ProcessingDataBox,
        individual: super::model::IndividualId,
        individual_index: super::model::Cint64,
        independent_base_dep_track_point: TrackPointId,
    ) -> bool {
        let individual_node_id = -individual_index;
        if data_box
            .individual_process_node_vector()
            .get_data(individual_node_id)
            .is_some()
        {
            return false;
        }

        let mut indi_node = IndividualProcessNode::new(ProcessContextId::NONE);
        indi_node.set_dependency_track_point(independent_base_dep_track_point);
        if individual.is_some() {
            let individual_data = ontology.individual(individual);
            indi_node
                .set_assertion_concept_assertions(
                    individual_data.get_assertion_concept_linker().to_vec(),
                )
                .set_assertion_data_assertions(individual_data.get_assertion_data_linker().to_vec())
                .set_assertion_role_assertions(individual_data.get_assertion_role_linker().to_vec())
                .set_reverse_assertion_role_assertions(
                    individual_data.get_reverse_assertion_role_linker().to_vec(),
                );
        }
        indi_node
            .set_nominal_individual(individual)
            .set_individual_node_id(individual_node_id)
            .set_individual_type(IndividualType::Nominal);

        let node = process_context.alloc_node(indi_node);
        // KONCLUDE-PORT-NOTE[unclear]: upstream generator line 541 writes
        // `setLocalData(i, indiNode)` although the helper guards with
        // `getData(-i)` and all nominal-node consumers use `-individualID`.
        // The port stores under the semantic individual-node id `-i`, matching
        // the sibling completion-algorithm branch and the vector lookup guard.
        data_box
            .individual_process_node_vector_mut()
            .set_local_data(individual_node_id, node);
        let queue = data_box.get_individual_immediately_processing_queue(process_context, true);
        process_context
            .indi_unsorted_proc_queue_mut(queue)
            .insert_indiviudal_process_node(node);
        true
    }

    /// Port of the `recreateNodesForIndividuals` block in
    /// `createSatisfiableCalculationTaskExtension`.
    pub fn recreate_ontology_nominal_nodes_for_calculation_task(
        &self,
        ontology: &OntologyArenas,
        process_context: &mut ProcessContext,
        data_box: &mut ProcessingDataBox,
        independent_base_dep_track_point: TrackPointId,
    ) -> &Self {
        let max_triples_indexed_indi_id = ontology.get_max_triples_indexed_individual_id();
        let mut max_abox_indi_id = 0;
        let indi_count = ontology.individual_count();
        for i in 0..indi_count {
            let individual = ontology.individual_data(i);
            if individual.is_some() && ontology.is_active_individual(individual) {
                self.create_individual_nominal_node_for_calculation_task(
                    ontology,
                    process_context,
                    data_box,
                    individual,
                    i,
                    independent_base_dep_track_point,
                );
            } else if i <= max_triples_indexed_indi_id {
                self.create_individual_nominal_node_for_calculation_task(
                    ontology,
                    process_context,
                    data_box,
                    individual,
                    i,
                    independent_base_dep_track_point,
                );
            }
            max_abox_indi_id = max_abox_indi_id.max(i);
        }
        for idx in (max_abox_indi_id + 1)..=max_triples_indexed_indi_id {
            self.create_individual_nominal_node_for_calculation_task(
                ontology,
                process_context,
                data_box,
                super::model::IndividualId::NONE,
                idx,
                independent_base_dep_track_point,
            );
        }
        self
    }
}

#[cfg(test)]
mod tests {
    use super::super::model::substrate::Id;
    use super::super::task::adapters::SatisfiableTaskIndividualDependenceTrackingAdapter;
    use super::*;

    #[test]
    fn generator_transfers_individual_dependence_adapter_and_requires_tracking() {
        let adapter = Id::<SatisfiableTaskIndividualDependenceTrackingAdapter>::new(5);
        let mut job = SatisfiableCalculationJob::new();
        job.set_satisfiable_task_individual_dependence_tracking_adapter(adapter);
        let mut task = SatisfiableCalculationTask::new();
        let mut data_box = ProcessingDataBox::new();

        SatisfiableCalculationTaskFromCalculationJobGenerator::new()
            .transfer_individual_dependence_tracking_adapter(&job, &mut task, &mut data_box);

        assert_eq!(
            task.get_satisfiable_task_individual_dependence_tracking_adapter(),
            adapter
        );
        assert!(data_box.is_individual_dependence_tracking_required());
    }

    #[test]
    fn generator_leaves_tracking_unrequired_without_adapter() {
        let job = SatisfiableCalculationJob::new();
        let mut task = SatisfiableCalculationTask::new();
        let mut data_box = ProcessingDataBox::new();

        SatisfiableCalculationTaskFromCalculationJobGenerator::new()
            .transfer_individual_dependence_tracking_adapter(&job, &mut task, &mut data_box);

        assert!(task
            .get_satisfiable_task_individual_dependence_tracking_adapter()
            .is_none());
        assert!(!data_box.is_individual_dependence_tracking_required());
    }

    #[test]
    fn generator_transfers_classification_message_adapters() {
        use super::super::task::adapters::{
            SatisfiableTaskClassificationMessageAdapter,
            SatisfiableTaskClassificationRoleMarkedMessageAdapter,
        };

        let class_adapter = Id::<SatisfiableTaskClassificationMessageAdapter>::new(11);
        let role_adapter = Id::<SatisfiableTaskClassificationRoleMarkedMessageAdapter>::new(13);
        let mut job = SatisfiableCalculationJob::new();
        job.set_satisfiable_classification_message_adapter(class_adapter)
            .set_satisfiable_classification_role_marked_message_adapter(role_adapter);
        let mut task = SatisfiableCalculationTask::new();

        SatisfiableCalculationTaskFromCalculationJobGenerator::new()
            .transfer_classification_message_adapters(&job, &mut task);

        assert_eq!(task.get_classification_message_adapter(), class_adapter);
        assert_eq!(
            task.get_satisfiable_classification_role_marked_message_adapter(),
            role_adapter
        );
    }

    #[test]
    fn generator_transfers_ordered_concept_assertions() {
        use super::super::model::{ConceptId, IndividualId};

        let concept_a = ConceptId::new(17);
        let concept_b = ConceptId::new(19);
        let individual_a = IndividualId::new(23);
        let individual_b = IndividualId::new(29);
        let mut job = SatisfiableCalculationJob::new();
        job.add_satisfiable_calculation_job_concept_assertion(concept_a, false, individual_a)
            .add_satisfiable_calculation_job_concept_assertion(concept_b, true, individual_b);
        let mut task = SatisfiableCalculationTask::new();

        SatisfiableCalculationTaskFromCalculationJobGenerator::new()
            .transfer_concept_assertions(&job, &mut task);

        let assertions = task.get_satisfiable_calculation_job_concept_assertions();
        assert_eq!(assertions.len(), 2);
        assert_eq!(assertions[0].get_concept(), concept_a);
        assert!(!assertions[0].is_negated());
        assert_eq!(assertions[0].get_individual(), individual_a);
        assert_eq!(assertions[1].get_concept(), concept_b);
        assert!(assertions[1].is_negated());
        assert_eq!(assertions[1].get_individual(), individual_b);
    }

    #[test]
    fn generator_materializes_concept_assertions_to_processing_data_box() {
        use super::super::model::{ConceptId, IndividualId};

        let concept_a = ConceptId::new(31);
        let concept_b = ConceptId::new(37);
        let concept_c = ConceptId::new(39);
        let individual_a = IndividualId::new(41);
        let mut job = SatisfiableCalculationJob::new();
        job.add_satisfiable_calculation_job_concept_assertion(concept_a, false, individual_a)
            .add_satisfiable_calculation_job_concept_assertion_for_fixed_individual_id(
                concept_b, true, 43,
            )
            .add_satisfiable_calculation_job_concept_assertion_for_relative_new_node_id(
                concept_c, false, 2,
            );
        let mut task = SatisfiableCalculationTask::new();
        let mut data_box = ProcessingDataBox::new();
        assert!(!data_box.has_multiple_construction_individual_nodes());
        data_box.add_initializing_concept_assertion(
            ConceptId::new(47),
            false,
            IndividualId::new(53),
        );

        SatisfiableCalculationTaskFromCalculationJobGenerator::new()
            .transfer_concept_assertions(&job, &mut task)
            .materialize_concept_assertions_to_processing_data_box(&task, &mut data_box);

        let assertions = data_box.initializing_concept_assertions();
        assert_eq!(assertions.len(), 3);
        assert!(data_box.has_multiple_construction_individual_nodes());
        assert_eq!(assertions[0].get_concept(), concept_a);
        assert!(!assertions[0].is_negated());
        assert_eq!(assertions[0].get_individual(), individual_a);
        assert_eq!(
            assertions[0].get_individual_target(),
            ProcessingDataBoxIndividualTarget::Individual(individual_a)
        );
        assert_eq!(assertions[1].get_concept(), concept_b);
        assert!(assertions[1].is_negated());
        assert_eq!(
            assertions[1].get_individual_target(),
            ProcessingDataBoxIndividualTarget::FixedIndividualId(43)
        );
        assert_eq!(assertions[2].get_concept(), concept_c);
        assert!(!assertions[2].is_negated());
        assert_eq!(
            assertions[2].get_individual_target(),
            ProcessingDataBoxIndividualTarget::RelativeNewNodeId(2)
        );

        let mut single_job = SatisfiableCalculationJob::new();
        single_job.add_satisfiable_calculation_job_concept_assertion(
            concept_a,
            false,
            individual_a,
        );
        let mut single_task = SatisfiableCalculationTask::new();
        let mut single_data_box = ProcessingDataBox::new();
        SatisfiableCalculationTaskFromCalculationJobGenerator::new()
            .transfer_concept_assertions(&single_job, &mut single_task)
            .materialize_concept_assertions_to_processing_data_box(
                &single_task,
                &mut single_data_box,
            );
        assert!(!single_data_box.has_multiple_construction_individual_nodes());
    }

    #[test]
    fn generator_expands_databox_initializing_concepts_to_nominal_process_nodes() {
        use super::super::model::individual::{
            ConceptAssertion, DataAssertion, Individual, ReverseRoleAssertion, RoleAssertion,
        };
        use super::super::model::{ConceptId, RoleId};

        let mut ontology = OntologyArenas::new();
        let mut individual = Individual::new(5);
        let asserted_concept = ConceptId::new(59);
        let asserted_role = RoleId::new(11);
        individual
            .add_assertion_concept_linker(ConceptAssertion {
                target: asserted_concept,
                negated: true,
            })
            .add_assertion_data_linker(DataAssertion {
                role: RoleId::new(13),
                data_literal: 17,
            })
            .add_assertion_role_linker(RoleAssertion {
                role: asserted_role,
                individual: super::super::model::IndividualId::new(19),
            })
            .add_reverse_assertion_role_linker(ReverseRoleAssertion {
                individual: super::super::model::IndividualId::new(23),
                role: asserted_role,
                role_assertion: 29,
            });
        let individual_a = ontology.alloc_individual(individual);
        let individual_b = ontology.alloc_individual(Individual::new(7));
        let concept_a = ConceptId::new(61);
        let concept_b = ConceptId::new(67);
        let concept_c = ConceptId::new(71);
        let dep_track_point = TrackPointId::new(101);
        let mut data_box = ProcessingDataBox::new();
        let mut process_context = ProcessContext::new();

        data_box
            .add_initializing_concept_assertion(concept_a, false, individual_a)
            .add_initializing_concept_assertion(concept_b, true, individual_a)
            .add_initializing_concept_assertion(concept_c, false, individual_b);

        SatisfiableCalculationTaskFromCalculationJobGenerator::new()
            .expand_databox_initializing_concepts_to_process_nodes(
                &ontology,
                &mut process_context,
                &mut data_box,
                dep_track_point,
                false,
            );

        let node_a = data_box.individual_process_node_vector().get_data(-5);
        let node_b = data_box.individual_process_node_vector().get_data(-7);
        assert!(node_a.is_some());
        assert!(node_b.is_some());
        assert_eq!(data_box.constructed_individual_node(), node_a);

        let node_a_ref = process_context.node(node_a);
        assert_eq!(node_a_ref.individual_node_id(), -5);
        assert_eq!(node_a_ref.nominal_individual(), individual_a);
        assert_eq!(node_a_ref.individual_type(), IndividualType::Nominal);
        assert!(node_a_ref.has_nominal_individual_triples_assertions());
        assert_eq!(node_a_ref.dependency_track_point(), dep_track_point);
        assert_eq!(
            node_a_ref.assertion_concept_assertions(),
            &[ConceptAssertion {
                target: asserted_concept,
                negated: true,
            }]
        );
        assert_eq!(node_a_ref.assertion_data_assertions().len(), 1);
        assert_eq!(
            node_a_ref.assertion_role_assertions(),
            &[RoleAssertion {
                role: asserted_role,
                individual: super::super::model::IndividualId::new(19),
            }]
        );
        assert_eq!(node_a_ref.reverse_assertion_role_assertions().len(), 1);
        assert!(!node_a_ref.has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_INVALIDBLOCKINGORCACHING
        ));
        assert_eq!(
            node_a_ref.initializing_concept_linker(),
            &[
                NegLink {
                    target: concept_b,
                    negated: true,
                },
                NegLink {
                    target: concept_a,
                    negated: false,
                },
            ]
        );
        assert_eq!(
            node_a_ref.process_initializing_concept_linker(),
            node_a_ref.initializing_concept_linker()
        );

        let node_b_ref = process_context.node(node_b);
        assert_eq!(node_b_ref.individual_node_id(), -7);
        assert_eq!(node_b_ref.nominal_individual(), individual_b);
        assert_eq!(
            node_b_ref.initializing_concept_linker(),
            &[NegLink {
                target: concept_c,
                negated: false,
            }]
        );
        let queue =
            data_box.get_individual_immediately_processing_queue(&mut process_context, false);
        assert_eq!(
            process_context
                .indi_unsorted_proc_queue_mut(queue)
                .get_next_process_individual_node(),
            node_b
        );
    }

    #[test]
    fn generator_expands_fixed_and_relative_targets_and_updates_next_node_id() {
        use super::super::model::ConceptId;
        use super::super::process::NodeId;

        let ontology = OntologyArenas::new();
        let concept_fixed = ConceptId::new(73);
        let concept_relative_a = ConceptId::new(79);
        let concept_relative_b = ConceptId::new(83);
        let dep_track_point = TrackPointId::new(303);
        let mut data_box = ProcessingDataBox::new();
        let mut process_context = ProcessContext::new();
        data_box.set_first_possible_individual_node_id(10);

        data_box
            .add_initializing_concept_assertion_for_fixed_individual_id(concept_fixed, false, 25)
            .add_initializing_concept_assertion_for_relative_new_node_id(
                concept_relative_a,
                true,
                0,
            )
            .add_initializing_concept_assertion_for_relative_new_node_id(
                concept_relative_b,
                false,
                2,
            );

        SatisfiableCalculationTaskFromCalculationJobGenerator::new()
            .expand_databox_initializing_concepts_to_process_nodes(
                &ontology,
                &mut process_context,
                &mut data_box,
                dep_track_point,
                false,
            );

        let fixed_node = data_box.individual_process_node_vector().get_data(25);
        let rel_a_node = data_box.individual_process_node_vector().get_data(10);
        let rel_b_node = data_box.individual_process_node_vector().get_data(12);
        assert!(fixed_node.is_some());
        assert!(rel_a_node.is_some());
        assert!(rel_b_node.is_some());
        assert_eq!(data_box.constructed_individual_node(), fixed_node);
        assert_eq!(data_box.next_individual_node_id(false), 26);
        assert_eq!(
            data_box.individual_process_node_vector().get_data(11),
            NodeId::NONE
        );

        let fixed = process_context.node(fixed_node);
        assert_eq!(fixed.individual_node_id(), 25);
        assert_eq!(fixed.individual_type(), IndividualType::Blockable);
        assert_eq!(fixed.dependency_track_point(), dep_track_point);
        assert!(fixed.nominal_individual().is_none());
        assert!(fixed.has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_INVALIDBLOCKINGORCACHING
        ));
        assert_eq!(
            fixed.initializing_concept_linker(),
            &[NegLink {
                target: concept_fixed,
                negated: false,
            }]
        );

        let rel_a = process_context.node(rel_a_node);
        assert_eq!(rel_a.individual_node_id(), 10);
        assert_eq!(rel_a.individual_type(), IndividualType::Blockable);
        assert_eq!(rel_a.dependency_track_point(), dep_track_point);
        assert!(rel_a.has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_INVALIDBLOCKINGORCACHING
        ));
        assert_eq!(
            rel_a.initializing_concept_linker(),
            &[NegLink {
                target: concept_relative_a,
                negated: true,
            }]
        );

        let rel_b = process_context.node(rel_b_node);
        assert_eq!(rel_b.individual_node_id(), 12);
        assert_eq!(rel_b.individual_type(), IndividualType::Blockable);
        assert_eq!(rel_b.dependency_track_point(), dep_track_point);
        assert!(rel_b.has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_INVALIDBLOCKINGORCACHING
        ));
        assert_eq!(
            rel_b.initializing_concept_linker(),
            &[NegLink {
                target: concept_relative_b,
                negated: false,
            }]
        );
        let queue =
            data_box.get_individual_immediately_processing_queue(&mut process_context, false);
        assert_eq!(
            process_context
                .indi_unsorted_proc_queue_mut(queue)
                .get_next_process_individual_node(),
            rel_b_node
        );
    }

    #[test]
    fn generator_base_task_localizes_existing_ref_node_and_clears_queue_cached_flag() {
        use super::super::model::ConceptId;

        let ontology = OntologyArenas::new();
        let concept_a = ConceptId::new(89);
        let concept_b = ConceptId::new(97);
        let existing_concept = ConceptId::new(101);
        let dep_track_point = TrackPointId::new(307);
        let mut data_box = ProcessingDataBox::new();
        let mut process_context = ProcessContext::new();

        let mut ref_node = IndividualProcessNode::new(ProcessContextId::NONE);
        ref_node
            .set_individual_node_id(33)
            .set_processing_queued(true)
            .set_immediately_processing_queued(true)
            .set_regular_depth_processing_queued(true)
            .add_initializing_concept_linker(vec![NegLink {
                target: existing_concept,
                negated: false,
            }]);
        ref_node.add_processing_restriction_flags(
            IndividualProcessNode::PRF_CACHEDCOMPUTEDTYPESADDED
                | IndividualProcessNode::PRF_DIRECTBLOCKED,
        );
        let ref_node_id = process_context.alloc_node(ref_node);
        data_box
            .individual_process_node_vector_mut()
            .set_local_data(33, ref_node_id);

        data_box
            .add_initializing_concept_assertion_for_fixed_individual_id(concept_a, false, 33)
            .add_initializing_concept_assertion_for_fixed_individual_id(concept_b, true, 33);

        SatisfiableCalculationTaskFromCalculationJobGenerator::new()
            .expand_databox_initializing_concepts_to_process_nodes(
                &ontology,
                &mut process_context,
                &mut data_box,
                dep_track_point,
                true,
            );

        let localized_node = data_box.individual_process_node_vector().get_data(33);
        assert!(localized_node.is_some());
        assert_ne!(localized_node, ref_node_id);
        assert!(process_context.node(ref_node_id).is_relocalized());

        let localized = process_context.node(localized_node);
        assert_eq!(localized.individual_node_id(), 33);
        assert!(!localized.is_processing_queued());
        assert!(!localized.is_immediately_processing_queued());
        assert!(!localized.is_regular_depth_processing_queued());
        assert!(!localized.has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_CACHEDCOMPUTEDTYPESADDED
        ));
        assert!(localized
            .has_partial_processing_restriction_flags(IndividualProcessNode::PRF_DIRECTBLOCKED));
        assert!(localized.has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_INVALIDBLOCKINGORCACHING
        ));
        assert_eq!(
            localized.initializing_concept_linker(),
            &[
                NegLink {
                    target: concept_b,
                    negated: true,
                },
                NegLink {
                    target: concept_a,
                    negated: false,
                },
            ]
        );

        let queue =
            data_box.get_individual_immediately_processing_queue(&mut process_context, false);
        assert_eq!(
            process_context
                .indi_unsorted_proc_queue_mut(queue)
                .get_next_process_individual_node(),
            localized_node
        );
        assert_eq!(data_box.constructed_individual_node(), localized_node);
    }

    #[test]
    fn generator_recreates_active_and_triples_indexed_nominal_nodes() {
        use super::super::model::individual::{ConceptAssertion, Individual};
        use super::super::model::ConceptId;

        let mut ontology = OntologyArenas::new();
        let concept_a = ConceptId::new(113);
        let individual_0 = ontology.alloc_individual(Individual::new(0));
        let mut individual = Individual::new(1);
        individual.add_assertion_concept_linker(ConceptAssertion {
            target: concept_a,
            negated: false,
        });
        let individual_1 = ontology.alloc_individual(individual);
        let individual_2 = ontology.alloc_individual(Individual::new(2));
        assert_eq!(individual_0.raw, 0);
        assert_eq!(individual_1.raw, 1);
        assert_eq!(individual_2.raw, 2);
        ontology
            .set_max_triples_indexed_individual_id(1)
            .insert_active_individual(individual_2);

        let dep_track_point = TrackPointId::new(401);
        let mut data_box = ProcessingDataBox::new();
        let mut process_context = ProcessContext::new();

        SatisfiableCalculationTaskFromCalculationJobGenerator::new()
            .recreate_ontology_nominal_nodes_for_calculation_task(
                &ontology,
                &mut process_context,
                &mut data_box,
                dep_track_point,
            );

        let node_0 = data_box.individual_process_node_vector().get_data(0);
        let node_1 = data_box.individual_process_node_vector().get_data(-1);
        let node_2 = data_box.individual_process_node_vector().get_data(-2);
        assert!(node_0.is_some());
        assert!(node_1.is_some());
        assert!(node_2.is_some());

        let node_1_ref = process_context.node(node_1);
        assert_eq!(node_1_ref.individual_node_id(), -1);
        assert_eq!(node_1_ref.individual_type(), IndividualType::Nominal);
        assert_eq!(node_1_ref.nominal_individual(), individual_1);
        assert_eq!(node_1_ref.dependency_track_point(), dep_track_point);
        assert_eq!(
            node_1_ref.assertion_concept_assertions(),
            &[ConceptAssertion {
                target: concept_a,
                negated: false,
            }]
        );

        let node_2_ref = process_context.node(node_2);
        assert_eq!(node_2_ref.individual_node_id(), -2);
        assert_eq!(node_2_ref.nominal_individual(), individual_2);
        assert_eq!(node_2_ref.individual_type(), IndividualType::Nominal);

        let queue =
            data_box.get_individual_immediately_processing_queue(&mut process_context, false);
        assert_eq!(
            process_context
                .indi_unsorted_proc_queue_mut(queue)
                .get_next_process_individual_node(),
            node_2
        );
    }
}
