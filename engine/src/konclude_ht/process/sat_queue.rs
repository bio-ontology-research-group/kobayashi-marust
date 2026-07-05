//! `process::sat_queue` — saturation processing queues.
//!
//! This file ports `CSaturationIndividualNodeProcessingQueue`,
//! `CCriticalIndividualNodeProcessingQueue`,
//! `CCriticalIndividualNodeConceptTestSet`, and
//! `CSaturationSuccessorExtensionIndividualNodeProcessingQueue`,
//! `CCriticalSaturationConceptQueue`, and
//! `CCriticalSaturationConceptTypeQueues`.

#![allow(dead_code)]

use std::collections::{BTreeMap, HashSet};

use super::super::model::substrate::{Id, INVALID};
use super::super::model::{Cint64, ConceptId};
use super::super::saturation::satellites::ConceptSaturationProcessLinkerId;
use super::SatNodeId;

/// `CSaturationIndividualNodeProcessingQueue*`.
pub type SaturationIndividualNodeProcessingQueueId = Id<SaturationIndividualNodeProcessingQueue>;

/// `CCriticalIndividualNodeProcessingQueue*`.
pub type CriticalIndividualNodeProcessingQueueId = Id<CriticalIndividualNodeProcessingQueue>;

/// `CCriticalIndividualNodeConceptTestSet*`.
pub type CriticalIndividualNodeConceptTestSetId = Id<CriticalIndividualNodeConceptTestSet>;

/// `CSaturationSuccessorExtensionIndividualNodeProcessingQueue*`.
pub type SaturationSuccessorExtensionIndividualNodeProcessingQueueId =
    Id<SaturationSuccessorExtensionIndividualNodeProcessingQueue>;

/// `CCriticalSaturationConceptQueue*`.
pub type CriticalSaturationConceptQueueId = Id<CriticalSaturationConceptQueue>;

/// `CCriticalSaturationConceptTypeQueues*`.
pub type CriticalSaturationConceptTypeQueuesId = Id<CriticalSaturationConceptTypeQueues>;

/// Port of `CCriticalSaturationConceptTypeQueues::CRITICALSATURATIONCONCEPTQUEUETYPE`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CriticalSaturationConceptQueueType {
    Forall,
    Atmost,
    Disjunction,
    EqCandidate,
    Value,
    Nominal,
}

impl CriticalSaturationConceptQueueType {
    pub const CONCEPT_TYPE_COUNT: usize = 6;

    /// Port of the enum's integer indexing.
    pub fn as_index(self) -> usize {
        match self {
            Self::Forall => 0,
            Self::Atmost => 1,
            Self::Disjunction => 2,
            Self::EqCandidate => 3,
            Self::Value => 4,
            Self::Nominal => 5,
        }
    }
}

/// Port of `CSaturationIndividualNodeProcessingQueue`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SaturationIndividualNodeProcessingQueue {
    /// `mPriorityIndiDesMap`, keyed by `-individual->getIndividualID()`.
    pub priority_indi_des_map: BTreeMap<Cint64, SatNodeId>,
    /// `mProcessContext` opaque back handle.
    pub process_context: Cint64,
}

impl Default for SaturationIndividualNodeProcessingQueue {
    fn default() -> Self {
        Self::new(INVALID)
    }
}

impl SaturationIndividualNodeProcessingQueue {
    /// Port of the constructor.
    pub fn new(process_context: Cint64) -> Self {
        Self {
            priority_indi_des_map: BTreeMap::new(),
            process_context,
        }
    }

    /// Port of `initProcessingQueue`.
    pub fn init_processing_queue(
        &mut self,
        processing_queue: Option<&SaturationIndividualNodeProcessingQueue>,
    ) -> &mut Self {
        if let Some(queue) = processing_queue {
            self.priority_indi_des_map = queue.priority_indi_des_map.clone();
        } else {
            self.priority_indi_des_map.clear();
        }
        self
    }

    /// Port of `takeNextProcessIndividual`.
    pub fn take_next_process_individual(&mut self) -> SatNodeId {
        self.priority_indi_des_map
            .pop_first()
            .map_or(SatNodeId::NONE, |(_, node)| node)
    }

    /// Port of `getNextProcessIndividual`.
    pub fn get_next_process_individual(&self) -> SatNodeId {
        self.priority_indi_des_map
            .first_key_value()
            .map_or(SatNodeId::NONE, |(_, node)| *node)
    }

    /// Port of `insertProcessIndiviudal`.
    pub fn insert_process_individual(
        &mut self,
        individual: SatNodeId,
        individual_id: Cint64,
    ) -> &mut Self {
        self.priority_indi_des_map
            .insert(-individual_id, individual);
        self
    }

    /// Port of `isEmpty`.
    pub fn is_empty(&self) -> bool {
        self.priority_indi_des_map.is_empty()
    }

    /// Port of `getQueuedIndividualCount`.
    pub fn get_queued_individual_count(&self) -> Cint64 {
        self.priority_indi_des_map.len() as Cint64
    }

    /// Port of `hasQueuedIndividuals`.
    pub fn has_queued_individuals(&self) -> bool {
        !self.priority_indi_des_map.is_empty()
    }

    /// Port of `isIndividualQueued`.
    pub fn is_individual_queued(&self, individual_id: Cint64) -> bool {
        self.priority_indi_des_map.contains_key(&-individual_id)
    }
}

/// Port of `CCriticalIndividualNodeProcessingQueue`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CriticalIndividualNodeProcessingQueue {
    pub base: SaturationIndividualNodeProcessingQueue,
}

impl CriticalIndividualNodeProcessingQueue {
    /// Port of the constructor.
    pub fn new(process_context: Cint64) -> Self {
        Self {
            base: SaturationIndividualNodeProcessingQueue::new(process_context),
        }
    }

    /// Port of `initProcessingQueue`.
    pub fn init_processing_queue(
        &mut self,
        processing_queue: Option<&CriticalIndividualNodeProcessingQueue>,
    ) -> &mut Self {
        self.base
            .init_processing_queue(processing_queue.map(|queue| &queue.base));
        self
    }

    /// Port of inherited `takeNextProcessIndividual`.
    pub fn take_next_process_individual(&mut self) -> SatNodeId {
        self.base.take_next_process_individual()
    }

    /// Port of inherited `getNextProcessIndividual`.
    pub fn get_next_process_individual(&self) -> SatNodeId {
        self.base.get_next_process_individual()
    }

    /// Port of inherited `insertProcessIndiviudal`.
    pub fn insert_process_individual(
        &mut self,
        individual: SatNodeId,
        individual_id: Cint64,
    ) -> &mut Self {
        self.base
            .insert_process_individual(individual, individual_id);
        self
    }

    /// Port of inherited `isEmpty`.
    pub fn is_empty(&self) -> bool {
        self.base.is_empty()
    }

    /// Port of inherited `getQueuedIndividualCount`.
    pub fn get_queued_individual_count(&self) -> Cint64 {
        self.base.get_queued_individual_count()
    }

    /// Port of inherited `hasQueuedIndividuals`.
    pub fn has_queued_individuals(&self) -> bool {
        self.base.has_queued_individuals()
    }

    /// Port of inherited `isIndividualQueued`.
    pub fn is_individual_queued(&self, individual_id: Cint64) -> bool {
        self.base.is_individual_queued(individual_id)
    }
}

/// Port of `CCriticalIndividualNodeConceptTestSet`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CriticalIndividualNodeConceptTestSet {
    /// `mIndiConceptTestedSet`.
    pub indi_concept_tested_set: HashSet<(SatNodeId, ConceptId)>,
    /// `mProcessContext` opaque back handle.
    pub process_context: Cint64,
}

impl Default for CriticalIndividualNodeConceptTestSet {
    fn default() -> Self {
        Self::new(INVALID)
    }
}

impl CriticalIndividualNodeConceptTestSet {
    /// Port of the constructor.
    pub fn new(process_context: Cint64) -> Self {
        Self {
            indi_concept_tested_set: HashSet::new(),
            process_context,
        }
    }

    /// Port of `initIndividualNodeConceptTestSet`.
    pub fn init_individual_node_concept_test_set(
        &mut self,
        processing_queue: Option<&CriticalIndividualNodeConceptTestSet>,
    ) -> &mut Self {
        if let Some(queue) = processing_queue {
            self.indi_concept_tested_set = queue.indi_concept_tested_set.clone();
        } else {
            self.indi_concept_tested_set.clear();
        }
        self
    }

    /// Port of `isConceptTestedForIndividual(CConcept*, ...)`.
    pub fn is_concept_tested_for_individual(
        &self,
        concept: ConceptId,
        individual: SatNodeId,
    ) -> bool {
        self.indi_concept_tested_set
            .contains(&(individual, concept))
    }

    /// Port of `insertConceptTestedForIndividual(CConcept*, ...)`.
    pub fn insert_concept_tested_for_individual(
        &mut self,
        concept: ConceptId,
        individual: SatNodeId,
    ) -> &mut Self {
        self.indi_concept_tested_set.insert((individual, concept));
        self
    }

    // The `CConceptSaturationDescriptor*` overloads bottom out in
    // `criticalConDes->getConcept()`. The descriptor remains opaque in this
    // wave, so only the direct `CConcept*` pair operations are live here.
}

/// Port of `CCriticalSaturationConceptQueue`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CriticalSaturationConceptQueue {
    /// `mContext` opaque back handle.
    pub process_context: Cint64,
    /// `mCriticalConDesLinker`.
    pub critical_con_des_linker: ConceptSaturationProcessLinkerId,
}

impl Default for CriticalSaturationConceptQueue {
    fn default() -> Self {
        Self::new(INVALID)
    }
}

impl CriticalSaturationConceptQueue {
    /// Port of the constructor.
    pub fn new(process_context: Cint64) -> Self {
        Self {
            process_context,
            critical_con_des_linker: ConceptSaturationProcessLinkerId::NONE,
        }
    }

    /// Port of `initCriticalSaturationConceptQueue`.
    pub fn init_critical_saturation_concept_queue(&mut self, _indi_node: SatNodeId) -> &mut Self {
        self.critical_con_des_linker = ConceptSaturationProcessLinkerId::NONE;
        self
    }

    /// Port of `hasCriticalConceptDescriptorLinker`.
    pub fn has_critical_concept_descriptor_linker(&self) -> bool {
        self.critical_con_des_linker.is_some()
    }

    /// Port of `getCriticalConceptDescriptorLinker`.
    pub fn get_critical_concept_descriptor_linker(&self) -> ConceptSaturationProcessLinkerId {
        self.critical_con_des_linker
    }
}

/// Port of `CCriticalSaturationConceptTypeQueues`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CriticalSaturationConceptTypeQueues {
    /// `mContext` opaque back handle.
    pub process_context: Cint64,
    /// `mIndiNode`.
    pub indi_node: SatNodeId,
    /// `mQueueVec`.
    pub queue_vec:
        [CriticalSaturationConceptQueueId; CriticalSaturationConceptQueueType::CONCEPT_TYPE_COUNT],
    /// `mQueued`.
    pub queued: bool,
}

impl Default for CriticalSaturationConceptTypeQueues {
    fn default() -> Self {
        Self::new(INVALID)
    }
}

impl CriticalSaturationConceptTypeQueues {
    /// Port of the constructor.
    pub fn new(process_context: Cint64) -> Self {
        Self {
            process_context,
            indi_node: SatNodeId::NONE,
            queue_vec: [CriticalSaturationConceptQueueId::NONE;
                CriticalSaturationConceptQueueType::CONCEPT_TYPE_COUNT],
            queued: false,
        }
    }

    /// Port of `initCriticalSaturationConceptQueues`.
    pub fn init_critical_saturation_concept_queues(&mut self, indi_node: SatNodeId) -> &mut Self {
        self.indi_node = indi_node;
        self.queued = false;
        self.queue_vec = [CriticalSaturationConceptQueueId::NONE;
            CriticalSaturationConceptQueueType::CONCEPT_TYPE_COUNT];
        self
    }

    /// Port of `hasCriticalSaturationConceptsQueued`.
    pub fn has_critical_saturation_concepts_queued<F>(&self, mut queue_has_linker: F) -> bool
    where
        F: FnMut(CriticalSaturationConceptQueueId) -> bool,
    {
        self.queue_vec
            .iter()
            .copied()
            .any(|queue| queue.is_some() && queue_has_linker(queue))
    }

    /// Port of the non-allocating part of `getCriticalSaturationConceptQueue`.
    pub fn get_critical_saturation_concept_queue_id(
        &self,
        queue_type: CriticalSaturationConceptQueueType,
    ) -> CriticalSaturationConceptQueueId {
        self.queue_vec[queue_type.as_index()]
    }

    /// Port of `isProcessNodeQueued`.
    pub fn is_process_node_queued(&self) -> bool {
        self.queued
    }

    /// Port of `setProcessNodeQueued`.
    pub fn set_process_node_queued(&mut self, queued: bool) -> &mut Self {
        self.queued = queued;
        self
    }
}

/// Port of `CSaturationSuccessorExtensionIndividualNodeProcessingQueue`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SaturationSuccessorExtensionIndividualNodeProcessingQueue {
    /// `mPriorityIndiDesMap`, keyed by `-individual->getIndividualID()`.
    pub priority_indi_des_map: BTreeMap<Cint64, SatNodeId>,
    /// `mCurrentIndividual`.
    pub current_individual: SatNodeId,
    /// `mProcessContext` opaque back handle.
    pub process_context: Cint64,
}

impl Default for SaturationSuccessorExtensionIndividualNodeProcessingQueue {
    fn default() -> Self {
        Self::new(INVALID)
    }
}

impl SaturationSuccessorExtensionIndividualNodeProcessingQueue {
    /// Port of the constructor.
    pub fn new(process_context: Cint64) -> Self {
        Self {
            priority_indi_des_map: BTreeMap::new(),
            current_individual: SatNodeId::NONE,
            process_context,
        }
    }

    /// Port of `initProcessingQueue`.
    pub fn init_processing_queue(
        &mut self,
        processing_queue: Option<&SaturationSuccessorExtensionIndividualNodeProcessingQueue>,
    ) -> &mut Self {
        if let Some(queue) = processing_queue {
            self.priority_indi_des_map = queue.priority_indi_des_map.clone();
            self.current_individual = queue.current_individual;
        } else {
            self.priority_indi_des_map.clear();
            self.current_individual = SatNodeId::NONE;
        }
        self
    }

    /// Port of `takeNextToCurrentProcessIndividual`.
    pub fn take_next_to_current_process_individual(&mut self) -> SatNodeId {
        if self.current_individual.is_none() {
            let next_node = self
                .priority_indi_des_map
                .pop_first()
                .map_or(SatNodeId::NONE, |(_, node)| node);
            self.current_individual = next_node;
        }
        self.current_individual
    }

    /// Port of `insertProcessIndiviudal`.
    pub fn insert_process_individual(
        &mut self,
        individual: SatNodeId,
        individual_id: Cint64,
    ) -> &mut Self {
        if self.current_individual.is_some() && self.current_individual == individual {
            return self;
        }
        self.priority_indi_des_map
            .insert(-individual_id, individual);
        self
    }

    /// Port of `isEmpty`.
    pub fn is_empty(&self) -> bool {
        self.current_individual.is_none() && self.priority_indi_des_map.is_empty()
    }

    /// Port of `getQueuedIndividualCount`.
    pub fn get_queued_individual_count(&self) -> Cint64 {
        let mut count = self.priority_indi_des_map.len() as Cint64;
        if self.current_individual.is_some() {
            count += 1;
        }
        count
    }

    /// Port of `hasQueuedIndividuals`.
    pub fn has_queued_individuals(&self) -> bool {
        self.current_individual.is_some() || !self.priority_indi_des_map.is_empty()
    }

    /// Port of `isIndividualQueued`.
    pub fn is_individual_queued(&self, individual: SatNodeId, individual_id: Cint64) -> bool {
        if self.current_individual.is_some() && self.current_individual == individual {
            return true;
        }
        self.priority_indi_des_map.contains_key(&-individual_id)
    }

    /// Port of `getCurrentProcessIndividual`.
    pub fn get_current_process_individual(&self) -> SatNodeId {
        self.current_individual
    }

    /// Port of `clearCurrentProcessIndividual`.
    pub fn clear_current_process_individual(&mut self) -> &mut Self {
        self.current_individual = SatNodeId::NONE;
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn saturation_individual_node_queue_orders_by_negative_individual_id() {
        let mut queue = SaturationIndividualNodeProcessingQueue::new(INVALID);
        let n7 = SatNodeId::new(7);
        let n3 = SatNodeId::new(3);
        let n11 = SatNodeId::new(11);

        queue
            .insert_process_individual(n7, 7)
            .insert_process_individual(n3, 3)
            .insert_process_individual(n11, 11);

        assert_eq!(queue.get_queued_individual_count(), 3);
        assert_eq!(queue.get_next_process_individual(), n11);
        assert_eq!(queue.take_next_process_individual(), n11);
        assert_eq!(queue.take_next_process_individual(), n7);
        assert_eq!(queue.take_next_process_individual(), n3);
        assert_eq!(queue.take_next_process_individual(), SatNodeId::NONE);
        assert!(queue.is_empty());
    }

    #[test]
    fn critical_individual_node_queue_copies_base_state() {
        let mut source = CriticalIndividualNodeProcessingQueue::new(INVALID);
        source
            .insert_process_individual(SatNodeId::new(1), 1)
            .insert_process_individual(SatNodeId::new(4), 4);

        let mut target = CriticalIndividualNodeProcessingQueue::new(INVALID);
        target.init_processing_queue(Some(&source));

        assert_eq!(target.get_queued_individual_count(), 2);
        assert!(target.is_individual_queued(4));
        assert_eq!(target.take_next_process_individual(), SatNodeId::new(4));
        assert_eq!(source.get_queued_individual_count(), 2);
    }

    #[test]
    fn critical_individual_node_concept_test_set_copies_and_tests_pairs() {
        let mut source = CriticalIndividualNodeConceptTestSet::new(INVALID);
        let node = SatNodeId::new(5);
        let concept = ConceptId::new(7);

        assert!(!source.is_concept_tested_for_individual(concept, node));
        source.insert_concept_tested_for_individual(concept, node);
        assert!(source.is_concept_tested_for_individual(concept, node));
        assert!(!source.is_concept_tested_for_individual(ConceptId::new(8), node));

        let mut target = CriticalIndividualNodeConceptTestSet::new(INVALID);
        target.init_individual_node_concept_test_set(Some(&source));
        assert!(target.is_concept_tested_for_individual(concept, node));
        assert_eq!(source.indi_concept_tested_set.len(), 1);

        target.init_individual_node_concept_test_set(None);
        assert!(!target.is_concept_tested_for_individual(concept, node));
    }

    #[test]
    fn saturation_successor_extension_queue_orders_by_negative_individual_id() {
        let mut queue = SaturationSuccessorExtensionIndividualNodeProcessingQueue::new(INVALID);
        let n7 = SatNodeId::new(7);
        let n3 = SatNodeId::new(3);
        let n11 = SatNodeId::new(11);

        queue
            .insert_process_individual(n7, 7)
            .insert_process_individual(n3, 3)
            .insert_process_individual(n11, 11);

        assert_eq!(queue.get_queued_individual_count(), 3);
        assert_eq!(queue.take_next_to_current_process_individual(), n11);
        assert_eq!(queue.take_next_to_current_process_individual(), n11);
        queue.clear_current_process_individual();
        assert_eq!(queue.take_next_to_current_process_individual(), n7);
        queue.clear_current_process_individual();
        assert_eq!(queue.take_next_to_current_process_individual(), n3);
        queue.clear_current_process_individual();
        assert_eq!(
            queue.take_next_to_current_process_individual(),
            SatNodeId::NONE
        );
        assert!(queue.is_empty());
    }

    #[test]
    fn saturation_successor_extension_queue_copies_current_and_pending_state() {
        let mut source = SaturationSuccessorExtensionIndividualNodeProcessingQueue::new(INVALID);
        let current = SatNodeId::new(4);
        let pending = SatNodeId::new(5);
        source
            .insert_process_individual(current, 4)
            .insert_process_individual(pending, 5);
        assert_eq!(source.take_next_to_current_process_individual(), pending);

        let mut target = SaturationSuccessorExtensionIndividualNodeProcessingQueue::new(INVALID);
        target.init_processing_queue(Some(&source));

        assert_eq!(target.get_current_process_individual(), pending);
        assert!(target.is_individual_queued(pending, 5));
        assert!(target.is_individual_queued(current, 4));
        source.clear_current_process_individual();
        assert_eq!(target.get_current_process_individual(), pending);
    }

    #[test]
    fn critical_saturation_concept_queue_prepends_and_takes_head() {
        let mut ctx = super::super::context::ProcessContext::new();
        let first = ctx.alloc_con_sat_proc_linker(Default::default());
        let second = ctx.alloc_con_sat_proc_linker(Default::default());
        let queue =
            ctx.alloc_critical_sat_concept_queue(CriticalSaturationConceptQueue::new(INVALID));
        ctx.critical_sat_concept_queue_mut(queue)
            .init_critical_saturation_concept_queue(SatNodeId::new(1));

        assert!(!ctx
            .critical_sat_concept_queue(queue)
            .has_critical_concept_descriptor_linker());
        ctx.critical_sat_concept_queue_add_critical_concept_descriptor_linker(queue, first);
        ctx.critical_sat_concept_queue_add_critical_concept_descriptor_linker(queue, second);

        assert_eq!(
            ctx.critical_sat_concept_queue(queue)
                .get_critical_concept_descriptor_linker(),
            second
        );
        assert_eq!(
            ctx.critical_sat_concept_queue_take_next_critical_concept_descriptor(queue),
            second
        );
        assert_eq!(
            ctx.con_sat_proc_linker(second).get_next(),
            ConceptSaturationProcessLinkerId::NONE
        );
        assert_eq!(
            ctx.critical_sat_concept_queue(queue)
                .get_critical_concept_descriptor_linker(),
            first
        );
        assert_eq!(
            ctx.critical_sat_concept_queue_take_next_critical_concept_descriptor(queue),
            first
        );
        assert_eq!(
            ctx.critical_sat_concept_queue_take_next_critical_concept_descriptor(queue),
            ConceptSaturationProcessLinkerId::NONE
        );
    }

    #[test]
    fn critical_saturation_type_queues_create_per_type_and_scan_has() {
        let mut ctx = super::super::context::ProcessContext::new();
        let node = SatNodeId::new(11);
        let type_queues = ctx.alloc_critical_sat_concept_type_queues(
            CriticalSaturationConceptTypeQueues::new(INVALID),
        );
        ctx.critical_sat_concept_type_queues_mut(type_queues)
            .init_critical_saturation_concept_queues(node);

        assert!(!ctx
            .critical_sat_concept_type_queues_has_critical_saturation_concepts_queued(type_queues));
        assert_eq!(
            ctx.critical_sat_concept_type_queues_get_critical_saturation_concept_queue(
                type_queues,
                CriticalSaturationConceptQueueType::Forall,
                false
            ),
            CriticalSaturationConceptQueueId::NONE
        );

        let forall = ctx.critical_sat_concept_type_queues_get_critical_saturation_concept_queue(
            type_queues,
            CriticalSaturationConceptQueueType::Forall,
            true,
        );
        let value = ctx.critical_sat_concept_type_queues_get_critical_saturation_concept_queue(
            type_queues,
            CriticalSaturationConceptQueueType::Value,
            true,
        );
        assert_ne!(forall, value);
        assert_eq!(
            ctx.critical_sat_concept_type_queues(type_queues).queue_vec
                [CriticalSaturationConceptQueueType::Forall.as_index()],
            forall
        );

        let linker = ctx.alloc_con_sat_proc_linker(Default::default());
        ctx.critical_sat_concept_queue_add_critical_concept_descriptor_linker(value, linker);
        assert!(ctx
            .critical_sat_concept_type_queues_has_critical_saturation_concepts_queued(type_queues));
    }

    #[test]
    fn critical_saturation_type_queues_init_clears_queues_and_queued_flag() {
        let mut queues = CriticalSaturationConceptTypeQueues::new(INVALID);
        queues.queue_vec[CriticalSaturationConceptQueueType::Nominal.as_index()] =
            CriticalSaturationConceptQueueId::new(3);
        queues.set_process_node_queued(true);

        queues.init_critical_saturation_concept_queues(SatNodeId::new(9));

        assert_eq!(queues.indi_node, SatNodeId::new(9));
        assert!(!queues.is_process_node_queued());
        assert_eq!(
            queues.get_critical_saturation_concept_queue_id(
                CriticalSaturationConceptQueueType::Nominal
            ),
            CriticalSaturationConceptQueueId::NONE
        );
    }
}
