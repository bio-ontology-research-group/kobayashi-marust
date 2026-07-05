//! `task::calculation_job` — minimal `CSatisfiableCalculationJob` holder surface.
//!
//! Ports the currently live Query-layer job fields that feed the kernel task
//! generator. The full Konclude class also owns query data, calculation
//! constructs, configuration, statistics, and the remaining adapter bag; those
//! stay deferred until their generator call sites become live.

#![allow(dead_code)]

use super::super::model::substrate::{Cint64, Id};
use super::super::model::{ConceptId, IndividualId};
use super::adapters::{
    SatisfiableTaskClassificationMessageAdapter,
    SatisfiableTaskClassificationRoleMarkedMessageAdapter,
    SatisfiableTaskIndividualDependenceTrackingAdapter,
};

/// Port-side target of one `CSatisfiableCalculationConstruct`.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum SatisfiableCalculationJobIndividualTarget {
    /// `satCalcConstruct->getIndividual()`.
    Individual(IndividualId),
    /// `satCalcConstruct->getIndividualID()` with no materialized individual.
    FixedIndividualId(Cint64),
    /// `baseIndiID + satCalcConstruct->getRelativeNewNodeID()`.
    RelativeNewNodeId(Cint64),
}

/// Port-side record of one `CSatisfiableCalculationJobGenerator`
/// concept construct.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct SatisfiableCalculationJobConceptAssertion {
    concept: ConceptId,
    negated: bool,
    target: SatisfiableCalculationJobIndividualTarget,
}

impl SatisfiableCalculationJobConceptAssertion {
    pub fn new(concept: ConceptId, negated: bool, individual: IndividualId) -> Self {
        Self::new_for_target(
            concept,
            negated,
            SatisfiableCalculationJobIndividualTarget::Individual(individual),
        )
    }

    pub fn new_for_fixed_individual_id(
        concept: ConceptId,
        negated: bool,
        individual_id: Cint64,
    ) -> Self {
        Self::new_for_target(
            concept,
            negated,
            SatisfiableCalculationJobIndividualTarget::FixedIndividualId(individual_id),
        )
    }

    pub fn new_for_relative_new_node_id(
        concept: ConceptId,
        negated: bool,
        relative_new_node_id: Cint64,
    ) -> Self {
        Self::new_for_target(
            concept,
            negated,
            SatisfiableCalculationJobIndividualTarget::RelativeNewNodeId(relative_new_node_id),
        )
    }

    pub fn new_for_target(
        concept: ConceptId,
        negated: bool,
        target: SatisfiableCalculationJobIndividualTarget,
    ) -> Self {
        Self {
            concept,
            negated,
            target,
        }
    }

    pub fn get_concept(&self) -> ConceptId {
        self.concept
    }

    pub fn is_negated(&self) -> bool {
        self.negated
    }

    pub fn get_individual(&self) -> IndividualId {
        match self.target {
            SatisfiableCalculationJobIndividualTarget::Individual(individual) => individual,
            SatisfiableCalculationJobIndividualTarget::FixedIndividualId(_)
            | SatisfiableCalculationJobIndividualTarget::RelativeNewNodeId(_) => IndividualId::NONE,
        }
    }

    pub fn get_individual_target(&self) -> SatisfiableCalculationJobIndividualTarget {
        self.target
    }
}

/// Port of the currently live part of
/// `Reasoner/Query/CSatisfiableCalculationJob`.
#[derive(Debug, Clone)]
pub struct SatisfiableCalculationJob {
    /// Ordered concept assertions accumulated by
    /// `CSatisfiableCalculationJobGenerator`.
    concept_assertions: Vec<SatisfiableCalculationJobConceptAssertion>,
    /// `CSatisfiableTaskClassificationMessageAdapter* mClassMessAdapter`.
    class_mess_adapter: Id<SatisfiableTaskClassificationMessageAdapter>,
    /// `CSatisfiableTaskClassificationRoleMarkedMessageAdapter* mClassRoleMarkedMessageAdapter`.
    class_role_marked_message_adapter: Id<SatisfiableTaskClassificationRoleMarkedMessageAdapter>,
    /// `CSatisfiableTaskIndividualDependenceTrackingAdapter* mSatIndDepTrackAdapter`.
    sat_ind_dep_track_adapter: Id<SatisfiableTaskIndividualDependenceTrackingAdapter>,
}

impl Default for SatisfiableCalculationJob {
    fn default() -> Self {
        Self::new()
    }
}

impl SatisfiableCalculationJob {
    /// Port of the constructor's relevant default
    /// (`mSatIndDepTrackAdapter = nullptr`).
    pub fn new() -> Self {
        Self {
            concept_assertions: Vec::new(),
            class_mess_adapter: Id::NONE,
            class_role_marked_message_adapter: Id::NONE,
            sat_ind_dep_track_adapter: Id::NONE,
        }
    }

    /// Port-side append for one generator concept assertion.
    pub fn add_satisfiable_calculation_job_concept_assertion(
        &mut self,
        concept: ConceptId,
        negated: bool,
        individual: IndividualId,
    ) -> &mut Self {
        self.concept_assertions
            .push(SatisfiableCalculationJobConceptAssertion::new(
                concept, negated, individual,
            ));
        self
    }

    pub fn add_satisfiable_calculation_job_concept_assertion_for_fixed_individual_id(
        &mut self,
        concept: ConceptId,
        negated: bool,
        individual_id: Cint64,
    ) -> &mut Self {
        self.concept_assertions.push(
            SatisfiableCalculationJobConceptAssertion::new_for_fixed_individual_id(
                concept,
                negated,
                individual_id,
            ),
        );
        self
    }

    pub fn add_satisfiable_calculation_job_concept_assertion_for_relative_new_node_id(
        &mut self,
        concept: ConceptId,
        negated: bool,
        relative_new_node_id: Cint64,
    ) -> &mut Self {
        self.concept_assertions.push(
            SatisfiableCalculationJobConceptAssertion::new_for_relative_new_node_id(
                concept,
                negated,
                relative_new_node_id,
            ),
        );
        self
    }

    /// Ordered assertions installed by the calculation-job generator calls.
    pub fn get_satisfiable_calculation_job_concept_assertions(
        &self,
    ) -> &[SatisfiableCalculationJobConceptAssertion] {
        &self.concept_assertions
    }

    /// Port of `setSatisfiableClassificationMessageAdapter`.
    pub fn set_satisfiable_classification_message_adapter(
        &mut self,
        class_mess_adapter: Id<SatisfiableTaskClassificationMessageAdapter>,
    ) -> &mut Self {
        self.class_mess_adapter = class_mess_adapter;
        self
    }

    /// Port of `getSatisfiableClassificationMessageAdapter`.
    pub fn get_satisfiable_classification_message_adapter(
        &self,
    ) -> Id<SatisfiableTaskClassificationMessageAdapter> {
        self.class_mess_adapter
    }

    /// Port of `setSatisfiableClassificationRoleMarkedMessageAdapter`.
    pub fn set_satisfiable_classification_role_marked_message_adapter(
        &mut self,
        class_role_marked_message_adapter: Id<
            SatisfiableTaskClassificationRoleMarkedMessageAdapter,
        >,
    ) -> &mut Self {
        self.class_role_marked_message_adapter = class_role_marked_message_adapter;
        self
    }

    /// Port of `getSatisfiableClassificationRoleMarkedMessageAdapter`.
    pub fn get_satisfiable_classification_role_marked_message_adapter(
        &self,
    ) -> Id<SatisfiableTaskClassificationRoleMarkedMessageAdapter> {
        self.class_role_marked_message_adapter
    }

    /// Port of `setSatisfiableTaskIndividualDependenceTrackingAdapter`.
    pub fn set_satisfiable_task_individual_dependence_tracking_adapter(
        &mut self,
        ind_dep_track_adaptor: Id<SatisfiableTaskIndividualDependenceTrackingAdapter>,
    ) -> &mut Self {
        self.sat_ind_dep_track_adapter = ind_dep_track_adaptor;
        self
    }

    /// Port of `getSatisfiableTaskIndividualDependenceTrackingAdapter`.
    pub fn get_satisfiable_task_individual_dependence_tracking_adapter(
        &self,
    ) -> Id<SatisfiableTaskIndividualDependenceTrackingAdapter> {
        self.sat_ind_dep_track_adapter
    }
}

#[cfg(test)]
mod tests {
    use super::super::super::model::substrate::Id;
    use super::*;

    #[test]
    fn satisfiable_calculation_job_stores_individual_dependence_adapter() {
        let mut job = SatisfiableCalculationJob::new();
        assert!(job
            .get_satisfiable_task_individual_dependence_tracking_adapter()
            .is_none());

        let adapter = Id::<SatisfiableTaskIndividualDependenceTrackingAdapter>::new(7);
        job.set_satisfiable_task_individual_dependence_tracking_adapter(adapter);
        assert_eq!(
            job.get_satisfiable_task_individual_dependence_tracking_adapter(),
            adapter
        );
    }

    #[test]
    fn satisfiable_calculation_job_stores_ordered_concept_assertions() {
        let mut job = SatisfiableCalculationJob::new();
        assert!(job
            .get_satisfiable_calculation_job_concept_assertions()
            .is_empty());

        let concept_a = ConceptId::new(3);
        let concept_b = ConceptId::new(5);
        let individual_a = IndividualId::new(7);
        let individual_b = IndividualId::new(11);
        job.add_satisfiable_calculation_job_concept_assertion(concept_a, false, individual_a)
            .add_satisfiable_calculation_job_concept_assertion(concept_b, true, individual_b);

        let assertions = job.get_satisfiable_calculation_job_concept_assertions();
        assert_eq!(assertions.len(), 2);
        assert_eq!(assertions[0].get_concept(), concept_a);
        assert!(!assertions[0].is_negated());
        assert_eq!(assertions[0].get_individual(), individual_a);
        assert_eq!(assertions[1].get_concept(), concept_b);
        assert!(assertions[1].is_negated());
        assert_eq!(assertions[1].get_individual(), individual_b);
    }

    #[test]
    fn satisfiable_calculation_job_stores_classification_message_adapters() {
        use super::super::adapters::{
            SatisfiableTaskClassificationMessageAdapter,
            SatisfiableTaskClassificationRoleMarkedMessageAdapter,
        };

        let mut job = SatisfiableCalculationJob::new();
        assert!(job
            .get_satisfiable_classification_message_adapter()
            .is_none());
        assert!(job
            .get_satisfiable_classification_role_marked_message_adapter()
            .is_none());

        let class_adapter = Id::<SatisfiableTaskClassificationMessageAdapter>::new(3);
        let role_adapter = Id::<SatisfiableTaskClassificationRoleMarkedMessageAdapter>::new(5);
        job.set_satisfiable_classification_message_adapter(class_adapter)
            .set_satisfiable_classification_role_marked_message_adapter(role_adapter);

        assert_eq!(
            job.get_satisfiable_classification_message_adapter(),
            class_adapter
        );
        assert_eq!(
            job.get_satisfiable_classification_role_marked_message_adapter(),
            role_adapter
        );
    }
}
