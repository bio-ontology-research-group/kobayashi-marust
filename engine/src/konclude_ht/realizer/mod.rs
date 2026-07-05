//! `realizer` — narrow ports from Konclude `Source/Reasoner/Realizer/`.
//!
//! This module starts at the individual-dependence adapter call sites. The full
//! realizer contains realization schedulers, instance maps, and result queues;
//! this wave ports only the tracking-required flag, per-individual collector
//! field, and job-adapter setup branches they use.

#![allow(dead_code)]

use super::completion::context::CalculationAlgorithmContext;
use super::model::substrate::Id;
use super::model::IndividualId;
use super::task::adapters::{
    IndividualDependenceTrackingCollector, IndividualDependenceTrackingCollectorId,
    IndividualDependenceTrackingMarkerId, SatisfiableTaskIndividualDependenceTrackingAdapter,
};
use super::task::calculation_job::SatisfiableCalculationJob;

/// Opaque id target for `COntologyRealizingDynamicRequirmentProcessingData*`.
#[derive(Debug, Clone)]
pub struct OntologyRealizingDynamicRequirmentProcessingData;

pub type OntologyRealizingDynamicRequirmentProcessingDataId =
    Id<OntologyRealizingDynamicRequirmentProcessingData>;

/// Opaque id target for `COptimizedKPSetConceptInstancesItem*`.
#[derive(Debug, Clone)]
pub struct OptimizedKPSetConceptInstancesItem;

pub type OptimizedKPSetConceptInstancesItemId = Id<OptimizedKPSetConceptInstancesItem>;

/// Opaque id target for `COptimizedKPSetRoleInstancesItem*`.
#[derive(Debug, Clone)]
pub struct OptimizedKPSetRoleInstancesItem;

pub type OptimizedKPSetRoleInstancesItemId = Id<OptimizedKPSetRoleInstancesItem>;

/// Opaque id target for
/// `CSatisfiableTaskRealizationPossibleInstancesMergingAdapter*`.
#[derive(Debug, Clone)]
pub struct SatisfiableTaskRealizationPossibleInstancesMergingAdapter;

pub type SatisfiableTaskRealizationPossibleInstancesMergingAdapterId =
    Id<SatisfiableTaskRealizationPossibleInstancesMergingAdapter>;

/// Port of the individual-dependence tracking-required flag on
/// `COptimizedRepresentativeKPSetOntologyRealizingItem`.
#[derive(Debug, Clone)]
pub struct OptimizedRepresentativeKPSetOntologyRealizingItem {
    /// `bool mIndiDepTrackReq`.
    individual_dependence_tracking_required: bool,
}

pub type OptimizedRepresentativeKPSetOntologyRealizingItemId =
    Id<OptimizedRepresentativeKPSetOntologyRealizingItem>;

impl Default for OptimizedRepresentativeKPSetOntologyRealizingItem {
    fn default() -> Self {
        Self::new()
    }
}

impl OptimizedRepresentativeKPSetOntologyRealizingItem {
    /// Constructor-side shell; `initRequirementConfigRealizingItem` installs the
    /// configuration-derived flag in C++.
    pub fn new() -> Self {
        Self {
            individual_dependence_tracking_required: false,
        }
    }

    /// Port of the individual-dependence part of
    /// `initRequirementConfigRealizingItem`.
    pub fn init_requirement_config_realizing_item(
        &mut self,
        individual_dependence_tracking_required: bool,
    ) -> &mut Self {
        self.individual_dependence_tracking_required = individual_dependence_tracking_required;
        self
    }

    /// Port of `requiresIndividualDependenceTracking`.
    pub fn requires_individual_dependence_tracking(&self) -> bool {
        self.individual_dependence_tracking_required
    }

    /// Port of `setIndividualDependenceTrackingRequired`.
    pub fn set_individual_dependence_tracking_required(
        &mut self,
        individual_dependence_tracking_required: bool,
    ) -> &mut Self {
        self.individual_dependence_tracking_required = individual_dependence_tracking_required;
        self
    }
}

/// Minimal port of `COptimizedKPSetIndividualItem` fields needed at the
/// individual-dependence adapter call sites.
#[derive(Debug, Clone)]
pub struct OptimizedKPSetIndividualItem {
    /// `cint64 mIndividualId`; retained for the init/getter surface.
    individual_id: i64,
    /// `CIndividual* mIndividual`.
    individual: IndividualId,
    /// `CIndividualDependenceTrackingCollector* mIndiDepTrackingCollector`.
    individual_dependence_tracking_collector: IndividualDependenceTrackingCollectorId,
}

pub type OptimizedKPSetIndividualItemId = Id<OptimizedKPSetIndividualItem>;

impl Default for OptimizedKPSetIndividualItem {
    fn default() -> Self {
        Self::new()
    }
}

impl OptimizedKPSetIndividualItem {
    /// Constructor-side shell; `initInstantiatedItem` fills the item in C++.
    pub fn new() -> Self {
        Self {
            individual_id: 0,
            individual: IndividualId::NONE,
            individual_dependence_tracking_collector: IndividualDependenceTrackingCollectorId::NONE,
        }
    }

    /// Port of the currently live part of `initInstantiatedItem`.
    pub fn init_instantiated_item(
        &mut self,
        individual_id: i64,
        individual: IndividualId,
    ) -> &mut Self {
        self.individual = individual;
        self.individual_id = individual_id;
        self.individual_dependence_tracking_collector =
            IndividualDependenceTrackingCollectorId::NONE;
        self
    }

    /// Port of `getIndividualId`.
    pub fn get_individual_id(&self) -> i64 {
        self.individual_id
    }

    /// Port of `getIndividual`.
    pub fn get_individual(&self) -> IndividualId {
        self.individual
    }

    /// Port of `getIndividualDependenceTrackingCollector`.
    pub fn get_individual_dependence_tracking_collector(
        &self,
    ) -> IndividualDependenceTrackingCollectorId {
        self.individual_dependence_tracking_collector
    }

    /// Port of `setIndividualDependenceTrackingCollector`.
    pub fn set_individual_dependence_tracking_collector(
        &mut self,
        collector: IndividualDependenceTrackingCollectorId,
    ) -> &mut Self {
        self.individual_dependence_tracking_collector = collector;
        self
    }
}

/// Port of `COptimizedKPSetIndividualItemPair`.
pub type OptimizedKPSetIndividualItemPair = (
    OptimizedKPSetIndividualItemId,
    OptimizedKPSetIndividualItemId,
);

/// Port of `CRealizingTestingItem::REALIZINGTESTINGTYPE`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RealizingTestingType {
    IndividualConceptInstanceTesting,
    IndividualPairRoleInstanceTesting,
    IndividualSameTesting,
    IndividualRoleCandidatePropagationTesting,
    IndividualRoleCandidateConfirmationTesting,
    IndividualsConsistencyTesting,
}

/// Port of the common `CRealizingTestingItem` base payload.
#[derive(Debug, Clone)]
pub struct RealizingTestingItem {
    /// `COntologyRealizingItem* mOntologyPreproItem`.
    ontology_realizing_item: OptimizedRepresentativeKPSetOntologyRealizingItemId,
    /// `QList<COntologyRealizingDynamicRequirmentProcessingData*> mProcDataList`.
    processing_data_list: Vec<OntologyRealizingDynamicRequirmentProcessingDataId>,
}

impl RealizingTestingItem {
    /// Port of `CRealizingTestingItem` constructor.
    pub fn new(
        ontology_realizing_item: OptimizedRepresentativeKPSetOntologyRealizingItemId,
        proc_data: OntologyRealizingDynamicRequirmentProcessingDataId,
    ) -> Self {
        let mut item = Self {
            ontology_realizing_item,
            processing_data_list: Vec::new(),
        };
        item.add_processing_data(proc_data);
        item
    }

    /// Port of `getOntologyRealizingItem`.
    pub fn get_ontology_realizing_item(
        &self,
    ) -> OptimizedRepresentativeKPSetOntologyRealizingItemId {
        self.ontology_realizing_item
    }

    /// Port of `setOntologyRealizingItem`.
    pub fn set_ontology_realizing_item(
        &mut self,
        ontology_realizing_item: OptimizedRepresentativeKPSetOntologyRealizingItemId,
    ) -> &mut Self {
        self.ontology_realizing_item = ontology_realizing_item;
        self
    }

    /// Port of `getProcessingDataList`.
    pub fn get_processing_data_list(
        &self,
    ) -> &[OntologyRealizingDynamicRequirmentProcessingDataId] {
        &self.processing_data_list
    }

    /// Port of `addProcessingData`.
    pub fn add_processing_data(
        &mut self,
        proc_data: OntologyRealizingDynamicRequirmentProcessingDataId,
    ) -> &mut Self {
        if proc_data.is_some() {
            self.processing_data_list.push(proc_data);
        }
        self
    }
}

/// Port of `CIndividualConceptInstanceTestingItem`.
#[derive(Debug, Clone)]
pub struct IndividualConceptInstanceTestingItem {
    base: RealizingTestingItem,
    instances_item: OptimizedKPSetConceptInstancesItemId,
    instantiated_item: OptimizedKPSetIndividualItemId,
    possible_instance_merging_data_adapter:
        SatisfiableTaskRealizationPossibleInstancesMergingAdapterId,
}

impl IndividualConceptInstanceTestingItem {
    /// Port of `CIndividualConceptInstanceTestingItem` constructor.
    pub fn new(
        prepro_item: OptimizedRepresentativeKPSetOntologyRealizingItemId,
        instances_item: OptimizedKPSetConceptInstancesItemId,
        instantiated_item: OptimizedKPSetIndividualItemId,
        proc_data: OntologyRealizingDynamicRequirmentProcessingDataId,
        possible_instance_merging_data_adapter:
            SatisfiableTaskRealizationPossibleInstancesMergingAdapterId,
    ) -> Self {
        Self {
            base: RealizingTestingItem::new(prepro_item, proc_data),
            instances_item,
            instantiated_item,
            possible_instance_merging_data_adapter,
        }
    }

    /// Port of `getRealizingTestingType`.
    pub fn get_realizing_testing_type(&self) -> RealizingTestingType {
        RealizingTestingType::IndividualConceptInstanceTesting
    }

    pub fn base(&self) -> &RealizingTestingItem {
        &self.base
    }

    /// Port of `getInstancesItem`.
    pub fn get_instances_item(&self) -> OptimizedKPSetConceptInstancesItemId {
        self.instances_item
    }

    /// Port of `getInstantiatedItem`.
    pub fn get_instantiated_item(&self) -> OptimizedKPSetIndividualItemId {
        self.instantiated_item
    }

    /// Port of `getPossibleInstanceMergingDataAdapter`.
    pub fn get_possible_instance_merging_data_adapter(
        &self,
    ) -> SatisfiableTaskRealizationPossibleInstancesMergingAdapterId {
        self.possible_instance_merging_data_adapter
    }
}

/// Port of `CIndividualPairRoleInstanceTestingItem`.
#[derive(Debug, Clone)]
pub struct IndividualPairRoleInstanceTestingItem {
    base: RealizingTestingItem,
    instances_item: OptimizedKPSetRoleInstancesItemId,
    individual_item_pair: OptimizedKPSetIndividualItemPair,
}

impl IndividualPairRoleInstanceTestingItem {
    /// Port of `CIndividualPairRoleInstanceTestingItem` constructor.
    pub fn new(
        prepro_item: OptimizedRepresentativeKPSetOntologyRealizingItemId,
        instances_item: OptimizedKPSetRoleInstancesItemId,
        individual_item_pair: OptimizedKPSetIndividualItemPair,
        proc_data: OntologyRealizingDynamicRequirmentProcessingDataId,
    ) -> Self {
        Self {
            base: RealizingTestingItem::new(prepro_item, proc_data),
            instances_item,
            individual_item_pair,
        }
    }

    /// Port of `getRealizingTestingType`.
    pub fn get_realizing_testing_type(&self) -> RealizingTestingType {
        RealizingTestingType::IndividualPairRoleInstanceTesting
    }

    pub fn base(&self) -> &RealizingTestingItem {
        &self.base
    }

    /// Port of `getInstancesItem`.
    pub fn get_instances_item(&self) -> OptimizedKPSetRoleInstancesItemId {
        self.instances_item
    }

    /// Port of `getIndividualItemPair`.
    pub fn get_individual_item_pair(&self) -> OptimizedKPSetIndividualItemPair {
        self.individual_item_pair
    }
}

/// Port of `CIndividualSameTestingItem`.
#[derive(Debug, Clone)]
pub struct IndividualSameTestingItem {
    base: RealizingTestingItem,
    instantiated_item1: OptimizedKPSetIndividualItemId,
    instantiated_item2: OptimizedKPSetIndividualItemId,
}

impl IndividualSameTestingItem {
    /// Port of `CIndividualSameTestingItem` constructor.
    pub fn new(
        prepro_item: OptimizedRepresentativeKPSetOntologyRealizingItemId,
        instantiated_item1: OptimizedKPSetIndividualItemId,
        instantiated_item2: OptimizedKPSetIndividualItemId,
        proc_data: OntologyRealizingDynamicRequirmentProcessingDataId,
    ) -> Self {
        Self {
            base: RealizingTestingItem::new(prepro_item, proc_data),
            instantiated_item1,
            instantiated_item2,
        }
    }

    /// Port of `getRealizingTestingType`.
    pub fn get_realizing_testing_type(&self) -> RealizingTestingType {
        RealizingTestingType::IndividualSameTesting
    }

    pub fn base(&self) -> &RealizingTestingItem {
        &self.base
    }

    /// Port of `getInstantiatedItem1`.
    pub fn get_instantiated_item1(&self) -> OptimizedKPSetIndividualItemId {
        self.instantiated_item1
    }

    /// Port of `getInstantiatedItem2`.
    pub fn get_instantiated_item2(&self) -> OptimizedKPSetIndividualItemId {
        self.instantiated_item2
    }
}

/// Port of the individual-dependence adapter setup branches in
/// `COptimizedRepresentativeKPSetOntologyRealizingThread`.
#[derive(Debug, Default, Clone)]
pub struct OptimizedRepresentativeKPSetOntologyRealizingThread;

impl OptimizedRepresentativeKPSetOntologyRealizingThread {
    /// Port of the realization branches that lazily install an
    /// `CIndividualDependenceTrackingCollector` on the individual item when the
    /// ontology realizing item requires tracking.
    pub fn ensure_individual_dependence_tracking_collector(
        req_conf_pre_comp_item: &OptimizedRepresentativeKPSetOntologyRealizingItem,
        individual_item: &mut OptimizedKPSetIndividualItem,
        calc_context: &mut CalculationAlgorithmContext,
    ) {
        if req_conf_pre_comp_item.requires_individual_dependence_tracking()
            && individual_item
                .get_individual_dependence_tracking_collector()
                .is_none()
        {
            let collector = calc_context.alloc_individual_dependence_tracking_collector(
                IndividualDependenceTrackingCollector::new(),
            );
            individual_item.set_individual_dependence_tracking_collector(collector);
        }
    }

    /// Port of the observer-only adapter allocation used by possible concept
    /// instance, role instance, and same-individual realization tests.
    pub fn set_satisfiable_task_individual_dependence_tracking_adapter(
        individual_item: &OptimizedKPSetIndividualItem,
        sat_calc_job: &mut SatisfiableCalculationJob,
        calc_context: &mut CalculationAlgorithmContext,
    ) {
        let collector = individual_item.get_individual_dependence_tracking_collector();
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

    /// Port of the combined pattern used before processing a realization
    /// satisfiability job.
    pub fn prepare_individual_dependence_tracking_adapter(
        req_conf_pre_comp_item: &OptimizedRepresentativeKPSetOntologyRealizingItem,
        individual_item: &mut OptimizedKPSetIndividualItem,
        sat_calc_job: &mut SatisfiableCalculationJob,
        calc_context: &mut CalculationAlgorithmContext,
    ) {
        Self::ensure_individual_dependence_tracking_collector(
            req_conf_pre_comp_item,
            individual_item,
            calc_context,
        );
        Self::set_satisfiable_task_individual_dependence_tracking_adapter(
            individual_item,
            sat_calc_job,
            calc_context,
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_observer_only_adapter(
        ctx: &CalculationAlgorithmContext,
        job: &SatisfiableCalculationJob,
        collector: IndividualDependenceTrackingCollectorId,
    ) {
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
    fn realizing_item_carries_individual_dependence_tracking_required_flag() {
        let mut item = OptimizedRepresentativeKPSetOntologyRealizingItem::new();

        assert!(!item.requires_individual_dependence_tracking());
        item.init_requirement_config_realizing_item(true);
        assert!(item.requires_individual_dependence_tracking());
        item.set_individual_dependence_tracking_required(false);
        assert!(!item.requires_individual_dependence_tracking());
    }

    #[test]
    fn kpset_individual_item_carries_collector_facet() {
        let mut ctx = CalculationAlgorithmContext::new();
        let collector = ctx.alloc_individual_dependence_tracking_collector(
            IndividualDependenceTrackingCollector::new(),
        );
        let mut item = OptimizedKPSetIndividualItem::new();
        item.init_instantiated_item(17, IndividualId::new(3));

        assert_eq!(item.get_individual_id(), 17);
        assert_eq!(item.get_individual(), IndividualId::new(3));
        assert!(item
            .get_individual_dependence_tracking_collector()
            .is_none());

        item.set_individual_dependence_tracking_collector(collector);
        assert_eq!(
            item.get_individual_dependence_tracking_collector(),
            collector
        );
    }

    #[test]
    fn realizer_possible_concept_instance_test_installs_observer_only_adapter() {
        let mut ctx = CalculationAlgorithmContext::new();
        let mut req_item = OptimizedRepresentativeKPSetOntologyRealizingItem::new();
        req_item.set_individual_dependence_tracking_required(true);
        let mut individual_item = OptimizedKPSetIndividualItem::new();
        individual_item.init_instantiated_item(23, IndividualId::new(5));
        let mut job = SatisfiableCalculationJob::new();

        OptimizedRepresentativeKPSetOntologyRealizingThread::prepare_individual_dependence_tracking_adapter(
            &req_item,
            &mut individual_item,
            &mut job,
            &mut ctx,
        );

        let collector = individual_item.get_individual_dependence_tracking_collector();
        assert!(collector.is_some());
        assert_observer_only_adapter(&ctx, &job, collector);
    }

    #[test]
    fn realizer_role_instance_pair_test_reuses_existing_observer_only_adapter_collector() {
        let mut ctx = CalculationAlgorithmContext::new();
        let collector = ctx.alloc_individual_dependence_tracking_collector(
            IndividualDependenceTrackingCollector::new(),
        );
        let mut req_item = OptimizedRepresentativeKPSetOntologyRealizingItem::new();
        req_item.set_individual_dependence_tracking_required(true);
        let mut individual_item = OptimizedKPSetIndividualItem::new();
        individual_item
            .init_instantiated_item(29, IndividualId::new(7))
            .set_individual_dependence_tracking_collector(collector);
        let mut job = SatisfiableCalculationJob::new();

        OptimizedRepresentativeKPSetOntologyRealizingThread::prepare_individual_dependence_tracking_adapter(
            &req_item,
            &mut individual_item,
            &mut job,
            &mut ctx,
        );

        assert_eq!(
            individual_item.get_individual_dependence_tracking_collector(),
            collector
        );
        assert_observer_only_adapter(&ctx, &job, collector);
    }

    #[test]
    fn realizer_same_individual_test_attaches_preexisting_collector_even_when_flag_disabled() {
        let mut ctx = CalculationAlgorithmContext::new();
        let collector = ctx.alloc_individual_dependence_tracking_collector(
            IndividualDependenceTrackingCollector::new(),
        );
        let req_item = OptimizedRepresentativeKPSetOntologyRealizingItem::new();
        let mut individual_item = OptimizedKPSetIndividualItem::new();
        individual_item
            .init_instantiated_item(31, IndividualId::new(11))
            .set_individual_dependence_tracking_collector(collector);
        let mut job = SatisfiableCalculationJob::new();

        OptimizedRepresentativeKPSetOntologyRealizingThread::prepare_individual_dependence_tracking_adapter(
            &req_item,
            &mut individual_item,
            &mut job,
            &mut ctx,
        );

        assert_observer_only_adapter(&ctx, &job, collector);
    }

    #[test]
    fn realizer_leaves_job_without_adapter_when_tracking_not_required_and_no_collector_exists() {
        let mut ctx = CalculationAlgorithmContext::new();
        let req_item = OptimizedRepresentativeKPSetOntologyRealizingItem::new();
        let mut individual_item = OptimizedKPSetIndividualItem::new();
        individual_item.init_instantiated_item(37, IndividualId::new(13));
        let mut job = SatisfiableCalculationJob::new();

        OptimizedRepresentativeKPSetOntologyRealizingThread::prepare_individual_dependence_tracking_adapter(
            &req_item,
            &mut individual_item,
            &mut job,
            &mut ctx,
        );

        assert!(individual_item
            .get_individual_dependence_tracking_collector()
            .is_none());
        assert!(job
            .get_satisfiable_task_individual_dependence_tracking_adapter()
            .is_none());
    }

    #[test]
    fn realizing_testing_item_base_stores_ontology_item_and_non_null_processing_data() {
        let ontology_item = OptimizedRepresentativeKPSetOntologyRealizingItemId::new(2);
        let proc_data = OntologyRealizingDynamicRequirmentProcessingDataId::new(5);
        let mut item = RealizingTestingItem::new(
            ontology_item,
            OntologyRealizingDynamicRequirmentProcessingDataId::NONE,
        );

        assert_eq!(item.get_ontology_realizing_item(), ontology_item);
        assert!(item.get_processing_data_list().is_empty());

        item.add_processing_data(proc_data);
        assert_eq!(item.get_processing_data_list(), &[proc_data]);

        let other_ontology_item = OptimizedRepresentativeKPSetOntologyRealizingItemId::new(3);
        item.set_ontology_realizing_item(other_ontology_item);
        assert_eq!(item.get_ontology_realizing_item(), other_ontology_item);
    }

    #[test]
    fn concept_instance_testing_item_carries_type_and_constructor_fields() {
        let prepro_item = OptimizedRepresentativeKPSetOntologyRealizingItemId::new(11);
        let instances_item = OptimizedKPSetConceptInstancesItemId::new(13);
        let instantiated_item = OptimizedKPSetIndividualItemId::new(17);
        let proc_data = OntologyRealizingDynamicRequirmentProcessingDataId::new(19);
        let merging_adapter = SatisfiableTaskRealizationPossibleInstancesMergingAdapterId::new(23);

        let item = IndividualConceptInstanceTestingItem::new(
            prepro_item,
            instances_item,
            instantiated_item,
            proc_data,
            merging_adapter,
        );

        assert_eq!(
            item.get_realizing_testing_type(),
            RealizingTestingType::IndividualConceptInstanceTesting
        );
        assert_eq!(item.base().get_ontology_realizing_item(), prepro_item);
        assert_eq!(item.base().get_processing_data_list(), &[proc_data]);
        assert_eq!(item.get_instances_item(), instances_item);
        assert_eq!(item.get_instantiated_item(), instantiated_item);
        assert_eq!(
            item.get_possible_instance_merging_data_adapter(),
            merging_adapter
        );
    }

    #[test]
    fn pair_role_instance_testing_item_carries_type_and_constructor_fields() {
        let prepro_item = OptimizedRepresentativeKPSetOntologyRealizingItemId::new(29);
        let instances_item = OptimizedKPSetRoleInstancesItemId::new(31);
        let individual_item_pair = (
            OptimizedKPSetIndividualItemId::new(37),
            OptimizedKPSetIndividualItemId::new(41),
        );
        let proc_data = OntologyRealizingDynamicRequirmentProcessingDataId::new(43);

        let item = IndividualPairRoleInstanceTestingItem::new(
            prepro_item,
            instances_item,
            individual_item_pair,
            proc_data,
        );

        assert_eq!(
            item.get_realizing_testing_type(),
            RealizingTestingType::IndividualPairRoleInstanceTesting
        );
        assert_eq!(item.base().get_ontology_realizing_item(), prepro_item);
        assert_eq!(item.base().get_processing_data_list(), &[proc_data]);
        assert_eq!(item.get_instances_item(), instances_item);
        assert_eq!(item.get_individual_item_pair(), individual_item_pair);
    }

    #[test]
    fn same_individual_testing_item_carries_type_and_constructor_fields() {
        let prepro_item = OptimizedRepresentativeKPSetOntologyRealizingItemId::new(47);
        let instantiated_item1 = OptimizedKPSetIndividualItemId::new(53);
        let instantiated_item2 = OptimizedKPSetIndividualItemId::new(59);
        let proc_data = OntologyRealizingDynamicRequirmentProcessingDataId::new(61);

        let item = IndividualSameTestingItem::new(
            prepro_item,
            instantiated_item1,
            instantiated_item2,
            proc_data,
        );

        assert_eq!(
            item.get_realizing_testing_type(),
            RealizingTestingType::IndividualSameTesting
        );
        assert_eq!(item.base().get_ontology_realizing_item(), prepro_item);
        assert_eq!(item.base().get_processing_data_list(), &[proc_data]);
        assert_eq!(item.get_instantiated_item1(), instantiated_item1);
        assert_eq!(item.get_instantiated_item2(), instantiated_item2);
    }
}
