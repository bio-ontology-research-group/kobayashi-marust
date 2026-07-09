//! `completion::selftest` — the W5 behavioural milestone: the FIRST time the
//! ported Konclude hypertableau completion engine RUNS on a trivial input and
//! produces a consistency verdict.
//!
//! Until W5 the kernel only COMPILED (W1–W8.1). These `#[cfg(test)]` checks drive
//! the live machinery end-to-end on a hand-built two-concept TBox, bypassing the
//! Task / scheduler adapter (which is still `W3-DEFER`) with a thin test entry that
//! constructs the per-thread context directly — exactly the "thin test entry that
//! bypasses the task adapter and calls the drive loop directly on a constructed
//! context" the W5 task describes.
//!
//! What runs (the live path, no `todo!` reached):
//!   * `OntologyArenas` is hand-built (one `CConcept` A with a concept tag);
//!   * a root `CIndividualProcessNode` is allocated, given an individual id, and
//!     registered in the databox `CIndividualProcessNodeVector` (the minimal
//!     `initializeCompletionGraph` / `buildCompletionGraph` seed);
//!   * `addConceptToIndividual` (the buildCompletionGraph "add the test concepts"
//!     step) materialises the node's concept-processing queue + reapply concept
//!     label set (the W3b/W8.1 context-threaded lazy getters), allocates a
//!     `CConceptDescriptor`, and inserts it into the label set via the faithful
//!     `insertConceptGetClash`;
//!   * a clash (A and ¬A on one node) is DETECTED by the polarity compare and
//!     RAISED as the pending clash signal (the `completion/clash.rs` stand-in for
//!     `throw CCalculationClashProcessingException`).
//!
//! The VERDICT is read off the per-task pending signal, exactly as `handleTask`'s
//! catch does: no pending signal ⇒ CONSISTENT (no clash); a pending `Clash` ⇒
//! INCONSISTENT. (The full saturation drive loop — `take_next_process_individual`
//! → `individual_node_initializing` → rule drain — is still gated behind the
//! `individualNodeInitializing` `todo!`; the clash-at-initialization verdict is the
//! W5 milestone.)
//!
//! The concept-processing-queue INSERT primitive (the `CConceptProcessDescriptor`
//! allocation + `CConceptProcessingQueue::insertConceptProcessDescriptor`) — gap
//! (a) of the W5 task — is exercised directly in `concept_queue_insert_primitive`.

#![cfg(test)]

use std::collections::{HashMap, HashSet};

use super::super::cache::context::CacheContext;
use super::super::cache::satnode::{
    AssociatedConceptExpansion, AssociatedConceptExpansionKind,
    SaturationNodeAssociatedConceptLinker, SaturationNodeAssociatedDependentNominalSet,
    SaturationNodeAssociatedExpansionCache,
    SaturationNodeAssociatedExpansionCacheExpansionWriteData,
    SaturationNodeAssociatedExpansionCacheUnsatisfiabilityWriteData,
    SaturationNodeAssociatedExpansionCacheWriteDataRecord,
    SaturationNodeAssociatedExpansionCacheWriter, SaturationNodeCacheUpdater,
};
use super::super::cache::unsat::OccurrenceUnsatisfiableCache;
use super::super::cache::value::{CacheValue, CacheValueIdentifier};
use super::super::model::concept::Concept;
use super::super::model::concept_process::{
    ConceptProcessData, ConceptSaturationReferenceLinkingData, SaturationConceptReferenceLinking,
};
use super::super::model::individual::Individual;
use super::super::model::substrate::{Id, NegLink, INVALID};
use super::super::model::{ConceptId, RoleId};
use super::super::process::analized_concept_expansion::{
    AnalizedConceptExpansionLinker, IndividualNodeAnalizedConceptExpansionData,
};
use super::super::process::backend_control::BackendNeighbourExpansionControllingData;
use super::super::process::backend_sync::IndividualNodeBackendCacheSynchronisationData;
use super::super::process::blocking_hash::{
    BlockingIndividualNodeCandidateHash, BlockingIndividualNodeLinkedCandidateHash,
    ReusingIndividualNodeConceptExpansionData, ReusingReviewData, SignatureBlockingReviewSet,
};
use super::super::process::databox::ProcessingDataBox;
use super::super::process::dependency::{
    DepKind, DepNodeBase, DependencyLink, DependencyNode, DependencyTrackPoint, NonDetData,
};
use super::super::process::descriptor::{
    ClashDescriptor, ClashDescriptorKind, ConceptDescriptor, ConceptProcessDescriptor,
    ConceptProcessPriority,
};
use super::super::process::edge::IndividualLinkEdge;
use super::super::process::marker_hash::MarkerIndividualNodeHash;
use super::super::process::node::{
    IndividualProcessNode, IndividualProcessNodePriority, IndividualType,
};
use super::super::process::queues::{
    ConceptProcessingQueue, IndividualConceptBatchProcessingQueue,
    IndividualCustomPriorityProcessingQueue, IndividualProcessNodeDescriptor,
    IndividualReactivationProcessingQueue,
};
use super::super::process::reapply_sat::BlockingAlternativeSignatureBlockingCandidateData;
use super::super::process::referred_tracking::ReferredIndividualTrackingVector;
use super::super::process::rs1::ReapplyQueueIterator;
use super::super::process::sat_block::IndividualNodeSaturationBlockingData;
use super::super::process::sat_node::{
    IndividualSaturationProcessNode, IndividualSaturationProcessNodeStatusFlags,
};
use super::super::process::sat_ref::ExtendedConceptReferenceLinkingData;
use super::super::process::satellites::{
    AdditionalDesDepMapRef, AdditionalMapSlot, ConceptDescriptorDependencyReapplyData,
    LabelSetMapAlias, ReapplyConceptLabelSet,
};
use super::super::process::varbind::VarBindingPathId;
use super::super::process::{
    BranchNodeId, ClashDescId, ConDescId, ConProcDescId, DepLinkId, DependencyId, LabelSetId,
    NodeId, RestrictionSpecId, SatNodeId, TrackPointId,
};
use super::super::saturation::algorithm::SaturationTaskHandleAlgorithm;
use super::super::task::adapters::{
    IndividualDependenceTrackingCollector, IndividualDependenceTrackingMarker,
    SatisfiableTaskClassificationMessageAdapter,
    SatisfiableTaskIncrementalConsistencyTestingAdapter,
    SatisfiableTaskIndividualDependenceTrackingAdapter, EFEXTRACTSUBSUMERSROOTNODE,
};
use super::super::task::satisfiable_task::SatisfiableCalculationTask as RealSatisfiableCalculationTask;
use super::super::task::task_data::TaskData;
use super::algorithm::{CompletionTaskHandleAlgorithm, IndiNodeQueueType};
use super::clash::CalcSignal;
use super::computed_cons_handler::ComputedConsequencesCacheHandler;
use super::context::CalculationAlgorithmContextBase;
use super::sat_node_exp_handler::SaturationNodeExpansionCacheHandler;
use super::strategy::{ConceptProcessingPriorityStrategy, TaskProcessingPriorityStrategy};
use super::stubs::SatisfiableCalculationTask;
use super::u30::{TrackedClashedDependencyLine, TrackedClashedDescriptorHasher};
use super::unsat_handler::UnsatisfiableCacheHandler;

/// The thin test harness: a constructed per-thread context, the completion
/// algorithm, the hand-built concept A and a seeded root individual node.
struct SelfTestEnv {
    algo: CompletionTaskHandleAlgorithm,
    ctx: CalculationAlgorithmContextBase,
    concept_a: ConceptId,
    top_concept: ConceptId,
    top_data_range_concept: ConceptId,
    root: NodeId,
}

/// Port-faithful analogue of `initializeCompletionGraph` + `buildCompletionGraph`'s
/// root-node creation: build the context, a one-concept TBox, and a root nominal
/// node registered in the node vector.
fn build_env() -> SelfTestEnv {
    let algo = CompletionTaskHandleAlgorithm::new();
    let mut ctx = CalculationAlgorithmContextBase::new();
    ctx.base.used_concept_priority_strategy =
        Some(ConceptProcessingPriorityStrategy::new_concrete_operator());

    // --- hand-build the static terminology: one named concept A ---
    let concept_a = {
        let mut c = Concept::new();
        // CConcept::setConceptTag — the value `insertConceptGetClash` keys the label
        // set by (so A and ¬A collide on the same key and the polarity compare runs).
        c.set_concept_tag(100);
        ctx.ontology_arenas_mut().alloc_concept(c)
    };

    // --- the ontology TOP concept (CCTOP) — `create_new_individual` seeds every
    //     fresh successor node with it, so it must resolve to a real concept. ---
    let top = {
        let mut c = Concept::new();
        c.set_concept_tag(1);
        c.set_operator_code(super::super::model::op::CCTOP);
        ctx.ontology_arenas_mut().alloc_concept(c)
    };
    ctx.processing_data_box_mut().ontology_top_concept = top;
    let top_data_range = {
        let mut c = Concept::new();
        c.set_concept_tag(2);
        c.set_operator_code(super::super::model::op::CCDATATYPE);
        ctx.ontology_arenas_mut().alloc_concept(c)
    };
    ctx.processing_data_box_mut()
        .ontology_top_data_range_concept = top_data_range;

    // --- minimal completion-graph init: the root individual node ---
    // new CIndividualProcessNode(processContext) — no process-context arena handle
    // is needed here, so `Id::NONE` (the node-resolution keystone uses the same).
    let root = ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    // setIndividualNodeID(0) — the (anonymous) root individual id.
    ctx.process_context_mut()
        .node_mut(root)
        .set_individual_node_id(0);
    // indiProcNodeVec->setLocalData(indiID, root) — register it so the resolvers see it.
    ctx.processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(0, root);

    SelfTestEnv {
        algo,
        ctx,
        concept_a,
        top_concept: top,
        top_data_range_concept: top_data_range,
        root,
    }
}

#[test]
fn referred_individual_tracking_vector_records_referred_and_extended_individuals() {
    let mut vec = ReferredIndividualTrackingVector::new();
    vec.init_referred_individual_tracking_vector(20, 5);

    vec.set_individual_referred(-3);
    vec.set_individual_referred_and_extended(-2);

    let referred = vec.get_referred_individual_tracking_data(2).unwrap();
    assert!(referred.is_referred());
    assert!(!referred.is_extended());

    let extended = vec.get_referred_individual_tracking_data(3).unwrap();
    assert!(extended.is_referred());
    assert!(extended.is_extended());
    assert_eq!(vec.get_dependence_size(), 2);
}

#[test]
fn referred_individual_tracking_vector_copies_merges_and_tests_affected_sets() {
    let mut base = ReferredIndividualTrackingVector::new();
    base.init_referred_individual_tracking_vector(20, 5);
    base.set_individual_referred(-3);

    let mut other = ReferredIndividualTrackingVector::new();
    other.init_referred_individual_tracking_vector(20, 5);
    other.set_individual_referred_and_extended(-2);

    let copied = other.get_copied_individual_dependency_tracking();
    base.merge_gathered_tracked_individual_dependences(&copied);

    assert_eq!(base.get_individual_track_count(), 20);
    assert_eq!(base.get_individual_track_offset(), 5);
    assert_eq!(base.get_dependence_size(), 2);
    assert!(base
        .get_referred_individual_tracking_data(3)
        .unwrap()
        .is_extended());

    let indirectly_changed = HashSet::from([2]);
    let changed_compatible = HashSet::from([7]);
    assert!(!base.are_individuals_affected(&indirectly_changed, &changed_compatible));

    let indirectly_changed = HashSet::from([3]);
    assert!(base.are_individuals_affected(&indirectly_changed, &changed_compatible));
}

#[test]
fn individual_dependence_tracking_collector_keeps_first_installed_vector() {
    let mut env = build_env();
    let first = env
        .ctx
        .process_context_mut()
        .alloc_referred_individual_tracking_vector({
            let mut vec = ReferredIndividualTrackingVector::new();
            vec.init_referred_individual_tracking_vector(4, 2);
            vec
        });
    let second = env
        .ctx
        .process_context_mut()
        .alloc_referred_individual_tracking_vector({
            let mut vec = ReferredIndividualTrackingVector::new();
            vec.init_referred_individual_tracking_vector(8, 4);
            vec
        });

    let mut collector = IndividualDependenceTrackingCollector::new();
    assert!(collector
        .get_extending_individual_dependence_tracking()
        .is_none());
    assert_eq!(
        collector.install_individual_dependence_tracking(first),
        first
    );
    assert_eq!(
        collector.get_extending_individual_dependence_tracking(),
        first
    );
    assert_eq!(
        collector.install_individual_dependence_tracking(second),
        first
    );
    assert_eq!(
        collector.get_extending_individual_dependence_tracking(),
        first
    );
}

#[test]
fn individual_dependence_tracking_adapter_preserves_observer_and_marker_handles() {
    let mut ctx = CalculationAlgorithmContextBase::new();
    let observer = ctx.base.alloc_individual_dependence_tracking_collector(
        IndividualDependenceTrackingCollector::new(),
    );
    let next_observer = ctx.base.alloc_individual_dependence_tracking_collector(
        IndividualDependenceTrackingCollector::new(),
    );
    let marker = ctx
        .base
        .alloc_individual_dependence_tracking_marker(IndividualDependenceTrackingMarker::new());
    let next_marker = ctx
        .base
        .alloc_individual_dependence_tracking_marker(IndividualDependenceTrackingMarker::new());

    let mut adapter = SatisfiableTaskIndividualDependenceTrackingAdapter::new(observer, marker);
    assert_eq!(
        adapter.get_individual_dependence_tracking_observer(),
        observer
    );
    assert_eq!(adapter.get_individual_dependence_tracking_marker(), marker);

    adapter
        .set_individual_dependence_tracking_observer(next_observer)
        .set_individual_dependence_tracking_marker(next_marker);
    assert_eq!(
        adapter.get_individual_dependence_tracking_observer(),
        next_observer
    );
    assert_eq!(
        adapter.get_individual_dependence_tracking_marker(),
        next_marker
    );
}

#[test]
fn individual_dependence_tracking_adapter_resolves_through_task_context_arena() {
    let mut ctx = CalculationAlgorithmContextBase::new();
    let observer = ctx.base.alloc_individual_dependence_tracking_collector(
        IndividualDependenceTrackingCollector::new(),
    );
    let marker = ctx
        .base
        .alloc_individual_dependence_tracking_marker(IndividualDependenceTrackingMarker::new());
    let adapter = ctx.base.alloc_individual_dependence_tracking_adapter(
        SatisfiableTaskIndividualDependenceTrackingAdapter::new(observer, marker),
    );
    let mut task = RealSatisfiableCalculationTask::new();
    task.set_satisfiable_task_individual_dependence_tracking_adapter(adapter);
    let task_id = ctx.base.alloc_sat_calc_task(task);

    let resolved_adapter_id = ctx
        .base
        .satisfiable_task_individual_dependence_tracking_adapter(task_id);
    assert_eq!(resolved_adapter_id, adapter);
    assert_eq!(
        ctx.base
            .individual_dependence_tracking_adapter(resolved_adapter_id)
            .get_individual_dependence_tracking_observer(),
        observer
    );
    assert_eq!(
        ctx.base
            .individual_dependence_tracking_adapter(resolved_adapter_id)
            .get_individual_dependence_tracking_marker(),
        marker
    );
}

#[test]
fn track_individual_dependence_marks_existing_referred_tracking_vector() {
    let mut env = build_env();
    let track_vec = env
        .ctx
        .process_context_mut()
        .alloc_referred_individual_tracking_vector({
            let mut vec = ReferredIndividualTrackingVector::new();
            vec.init_referred_individual_tracking_vector(20, 5);
            vec
        });
    env.ctx
        .processing_data_box_mut()
        .set_individual_dependence_tracking_required(true)
        .set_referred_individual_tracking_vector(track_vec);

    assert!(env
        .algo
        .track_individual_referred_dependence(3, &mut env.ctx));
    assert!(env
        .ctx
        .process_context()
        .referred_individual_tracking_vector(track_vec)
        .get_referred_individual_tracking_data(2)
        .unwrap()
        .is_referred());

    assert!(env
        .algo
        .track_individual_extended_dependence(2, &mut env.ctx));
    let extended = env
        .ctx
        .process_context()
        .referred_individual_tracking_vector(track_vec)
        .get_referred_individual_tracking_data(3)
        .unwrap();
    assert!(extended.is_referred());
    assert!(extended.is_extended());
}

#[test]
fn track_individual_dependence_respects_required_flag_and_missing_vector() {
    let mut env = build_env();
    assert!(!env
        .algo
        .track_individual_referred_dependence(3, &mut env.ctx));

    env.ctx
        .processing_data_box_mut()
        .set_individual_dependence_tracking_required(true);
    assert!(!env
        .algo
        .track_individual_referred_dependence(3, &mut env.ctx));
}

#[test]
fn track_individual_dependence_lazily_installs_vector_from_observer() {
    let mut env = build_env();
    for id in 0..5 {
        env.ctx
            .ontology_arenas_mut()
            .alloc_individual(Individual::new(id));
    }
    let observer = env.ctx.base.alloc_individual_dependence_tracking_collector(
        IndividualDependenceTrackingCollector::new(),
    );
    let adapter = env.ctx.base.alloc_individual_dependence_tracking_adapter(
        SatisfiableTaskIndividualDependenceTrackingAdapter::new(observer, Id::NONE),
    );
    let mut task = SatisfiableCalculationTask::new();
    task.set_satisfiable_task_individual_dependence_tracking_adapter(adapter);
    let task_id = env.ctx.base.alloc_sat_calc_task(task);
    env.ctx.base.used_sat_calc_task = task_id;
    env.ctx
        .processing_data_box_mut()
        .set_individual_dependence_tracking_required(true);

    assert!(env
        .algo
        .track_individual_referred_dependence(8, &mut env.ctx));

    let track_vec = env
        .ctx
        .processing_data_box()
        .referred_individual_tracking_vector();
    assert!(track_vec.is_some());
    assert_eq!(
        env.ctx
            .base
            .individual_dependence_tracking_collector(observer)
            .get_extending_individual_dependence_tracking(),
        track_vec
    );
    let track_vec_ref = env
        .ctx
        .process_context()
        .referred_individual_tracking_vector(track_vec);
    assert_eq!(track_vec_ref.get_individual_track_count(), 5);
    assert_eq!(track_vec_ref.get_individual_track_offset(), 5);
    assert_eq!(track_vec_ref.get_dependence_size(), 1);
}

#[test]
fn track_individual_dependence_marks_classifier_marker_when_lazy_tracking_starts() {
    let mut env = build_env();
    for id in 0..5 {
        env.ctx
            .ontology_arenas_mut()
            .alloc_individual(Individual::new(id));
    }
    let observer = env.ctx.base.alloc_individual_dependence_tracking_collector(
        IndividualDependenceTrackingCollector::new(),
    );
    let marker = env
        .ctx
        .base
        .alloc_individual_dependence_tracking_marker(IndividualDependenceTrackingMarker::new());
    let adapter = env.ctx.base.alloc_individual_dependence_tracking_adapter(
        SatisfiableTaskIndividualDependenceTrackingAdapter::new(observer, marker),
    );
    let mut task = SatisfiableCalculationTask::new();
    task.set_satisfiable_task_individual_dependence_tracking_adapter(adapter);
    let task_id = env.ctx.base.alloc_sat_calc_task(task);
    env.ctx.base.used_sat_calc_task = task_id;
    env.ctx
        .processing_data_box_mut()
        .set_individual_dependence_tracking_required(true);

    assert!(!env
        .ctx
        .base
        .individual_dependence_tracking_marker(marker)
        .has_individual_dependence_tracked());
    assert!(env
        .algo
        .track_individual_referred_dependence(8, &mut env.ctx));
    assert!(env
        .ctx
        .base
        .individual_dependence_tracking_marker(marker)
        .has_individual_dependence_tracked());
}

#[test]
fn track_individual_dependence_reuses_existing_observer_vector() {
    let mut env = build_env();
    for id in 0..5 {
        env.ctx
            .ontology_arenas_mut()
            .alloc_individual(Individual::new(id));
    }
    let existing_vec = env
        .ctx
        .process_context_mut()
        .alloc_referred_individual_tracking_vector({
            let mut vec = ReferredIndividualTrackingVector::new();
            vec.init_referred_individual_tracking_vector(20, 5);
            vec
        });
    let observer = env.ctx.base.alloc_individual_dependence_tracking_collector(
        IndividualDependenceTrackingCollector::new(),
    );
    env.ctx
        .base
        .individual_dependence_tracking_collector_mut(observer)
        .install_individual_dependence_tracking(existing_vec);
    let adapter = env.ctx.base.alloc_individual_dependence_tracking_adapter(
        SatisfiableTaskIndividualDependenceTrackingAdapter::new(observer, Id::NONE),
    );
    let mut task = SatisfiableCalculationTask::new();
    task.set_satisfiable_task_individual_dependence_tracking_adapter(adapter);
    let task_id = env.ctx.base.alloc_sat_calc_task(task);
    env.ctx.base.used_sat_calc_task = task_id;
    env.ctx
        .processing_data_box_mut()
        .set_individual_dependence_tracking_required(true);

    assert!(env
        .algo
        .track_individual_referred_dependence(3, &mut env.ctx));

    assert_eq!(
        env.ctx
            .processing_data_box()
            .referred_individual_tracking_vector(),
        existing_vec
    );
    assert_eq!(
        env.ctx
            .process_context()
            .referred_individual_tracking_vector(existing_vec)
            .get_dependence_size(),
        1
    );
}

#[test]
fn track_individual_dependence_sizes_to_deterministic_graph_when_larger_than_abox() {
    let mut env = build_env();
    for id in 0..2 {
        env.ctx
            .ontology_arenas_mut()
            .alloc_individual(Individual::new(id));
    }
    let mut cached_data_box = ProcessingDataBox::new();
    cached_data_box
        .individual_process_node_vector_mut()
        .set_local_data(6, NodeId::NONE);
    let mut cached_task = SatisfiableCalculationTask::new();
    cached_task.set_processing_data_box_state(cached_data_box);
    let cached_task_id = env.ctx.base.alloc_sat_calc_task(cached_task);
    let current_cons_data = env
        .ctx
        .base
        .alloc_task_data(TaskData::new_consistence(cached_task_id, Id::NONE));
    env.ctx
        .processing_data_box_mut()
        .set_consistence_model_data(current_cons_data);

    let observer = env.ctx.base.alloc_individual_dependence_tracking_collector(
        IndividualDependenceTrackingCollector::new(),
    );
    let adapter = env.ctx.base.alloc_individual_dependence_tracking_adapter(
        SatisfiableTaskIndividualDependenceTrackingAdapter::new(observer, Id::NONE),
    );
    let mut task = SatisfiableCalculationTask::new();
    task.set_satisfiable_task_individual_dependence_tracking_adapter(adapter);
    let task_id = env.ctx.base.alloc_sat_calc_task(task);
    env.ctx.base.used_sat_calc_task = task_id;
    env.ctx
        .processing_data_box_mut()
        .set_individual_dependence_tracking_required(true);

    assert!(env
        .algo
        .track_individual_referred_dependence(2, &mut env.ctx));

    let track_vec = env
        .ctx
        .processing_data_box()
        .referred_individual_tracking_vector();
    let track_vec_ref = env
        .ctx
        .process_context()
        .referred_individual_tracking_vector(track_vec);
    assert_eq!(track_vec_ref.get_individual_track_count(), 7);
    assert_eq!(track_vec_ref.get_individual_track_offset(), 2);
    assert_eq!(track_vec_ref.get_dependence_size(), 1);
}

/// sat: a root labelled with a single atomic concept A → COMPLETE (no clash).
#[test]
fn sat_single_atomic_concept_is_consistent() {
    let mut env = build_env();
    let mut root = env.root;

    // addConceptToIndividual(A, false, root, baseDepTrackPoint, false, true, ctx)
    env.algo.add_concept_to_individual(
        env.concept_a,
        false,
        &mut root,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );

    // VERDICT: no pending clash/stop signal ⇒ the node is consistent so far.
    assert!(
        !env.ctx.has_pending_signal(),
        "single atomic concept must not clash (expected COMPLETE)"
    );
    assert_eq!(env.ctx.pending_signal(), CalcSignal::Continue);
}

/// clash: a root labelled with A and ¬A → CLASH (the contradiction fires).
#[test]
fn clash_a_and_not_a_is_inconsistent() {
    let mut env = build_env();
    let mut root = env.root;

    // addConceptToIndividual(A, false, …) — positive A.
    env.algo.add_concept_to_individual(
        env.concept_a,
        false,
        &mut root,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );
    assert!(
        !env.ctx.has_pending_signal(),
        "first (positive) concept must not clash"
    );

    // addConceptToIndividual(A, true, …) — negative ¬A on the SAME node ⇒ clash.
    env.algo.add_concept_to_individual(
        env.concept_a,
        true,
        &mut root,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );

    // VERDICT: a pending Clash signal ⇒ the node (and hence the test) is inconsistent.
    assert!(
        env.ctx.has_pending_signal(),
        "A and ¬A on one node must clash (expected CLASH)"
    );
    match env.ctx.pending_signal() {
        CalcSignal::Clash(_) => {}
        other => panic!("expected a Clash signal, got {:?}", other),
    }
}

#[test]
fn add_concept_to_individual_updates_concept_occurrence_statistics() {
    let mut env = build_env();
    env.algo.conf_occurrence_statistics_collecting = true;
    env.algo.opt_collect_occurrence_statistics = true;
    let mut root = env.root;

    env.algo.add_concept_to_individual(
        env.concept_a,
        false,
        &mut root,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );

    let stats = env
        .ctx
        .occurrence_statistics_cache_handler_mut()
        .accummulated_concept_data_occurrence_statistics(100);
    assert_eq!(stats.get_deterministic_instance_occurrences_count(), 0);
    assert_eq!(stats.get_non_deterministic_instance_occurrences_count(), 1);
    assert_eq!(stats.get_individual_instance_occurrences_count(), 0);
    assert_eq!(stats.get_existential_instance_occurrences_count(), 1);
}

#[test]
fn add_concept_to_individual_occurrence_statistics_skip_contained_descriptor() {
    let mut env = build_env();
    env.algo.conf_occurrence_statistics_collecting = true;
    env.algo.opt_collect_occurrence_statistics = true;
    let mut root = env.root;

    for _ in 0..2 {
        env.algo.add_concept_to_individual(
            env.concept_a,
            false,
            &mut root,
            TrackPointId::NONE,
            false,
            true,
            &mut env.ctx,
        );
    }

    let stats = env
        .ctx
        .occurrence_statistics_cache_handler_mut()
        .accummulated_concept_data_occurrence_statistics(100);
    assert_eq!(
        stats.get_non_deterministic_instance_occurrences_count(),
        1,
        "Konclude only updates concept occurrence stats for newly inserted labels"
    );
    assert_eq!(stats.get_existential_instance_occurrences_count(), 1);
}

#[test]
fn add_concept_to_individual_occurrence_statistics_do_not_update_rejected_clash() {
    let mut env = build_env();
    env.algo.conf_occurrence_statistics_collecting = true;
    env.algo.opt_collect_occurrence_statistics = true;
    let mut root = env.root;

    env.algo.add_concept_to_individual(
        env.concept_a,
        false,
        &mut root,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );
    env.algo.add_concept_to_individual(
        env.concept_a,
        true,
        &mut root,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );

    match env.ctx.pending_signal() {
        CalcSignal::Clash(_) => {}
        other => panic!("expected a Clash signal, got {:?}", other),
    }
    let stats = env
        .ctx
        .occurrence_statistics_cache_handler_mut()
        .accummulated_concept_data_occurrence_statistics(100);
    assert_eq!(stats.get_non_deterministic_instance_occurrences_count(), 1);
    assert_eq!(stats.get_existential_instance_occurrences_count(), 1);
}

fn marker_concept(env: &mut SelfTestEnv, tag: i64) -> ConceptId {
    let mut c = Concept::new();
    c.set_concept_tag(tag);
    c.set_operator_code(super::super::model::op::CCMARKER);
    env.ctx.ontology_arenas_mut().alloc_concept(c)
}

fn processable_or_concept(env: &mut SelfTestEnv, tag: i64) -> ConceptId {
    let mut c = Concept::new();
    c.set_concept_tag(tag);
    c.set_operator_code(super::super::model::op::CCOR);
    env.ctx.ontology_arenas_mut().alloc_concept(c)
}

fn operator_concept_process_descriptor(
    env: &mut SelfTestEnv,
    concept_tag: i64,
    operator_code: i64,
    priority: f64,
) -> (ConceptId, ConDescId, ConProcDescId) {
    let mut concept = Concept::new();
    concept.set_concept_tag(concept_tag);
    concept.set_operator_code(operator_code);
    let concept = env.ctx.ontology_arenas_mut().alloc_concept(concept);
    let mut con_des = ConceptDescriptor::new();
    con_des.concept = concept;
    let con_des = env.ctx.process_context_mut().alloc_con_desc(con_des);
    let mut con_pro_des = ConceptProcessDescriptor::new();
    con_pro_des.concept_des = con_des;
    con_pro_des.priority = ConceptProcessPriority::new(priority);
    let con_pro_des = env
        .ctx
        .process_context_mut()
        .alloc_con_proc_desc(con_pro_des);
    (concept, con_des, con_pro_des)
}

fn marker_entries(env: &SelfTestEnv, marker: ConceptId) -> Vec<(NodeId, bool)> {
    let marker_hash = env.ctx.processing_data_box().use_marker_indi_node_hash;
    if marker_hash.is_none() {
        return Vec::new();
    }
    MarkerIndividualNodeHash::get_marker_individual_node_linker(
        env.ctx.process_context(),
        marker_hash,
        marker,
    )
}

fn deterministic_track_point(env: &mut SelfTestEnv) -> TrackPointId {
    let tp = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(Id::NONE));
    env.ctx
        .processing_data_box_mut()
        .set_maximum_deterministic_branch_tag(0);
    tp
}

fn real_dependency_track_point(
    env: &mut SelfTestEnv,
    individual_node: NodeId,
    concept_descriptor: ConDescId,
    kind: DepKind,
    dependency_processing_tag: i64,
    branching_tag: i64,
) -> TrackPointId {
    let base = DepNodeBase {
        process_tag: dependency_processing_tag,
        concept_descriptor,
        individual_node,
        kind,
        dep_track_point: TrackPointId::NONE,
        additional_after: Id::NONE,
        selected_var_bind_path: VarBindingPathId::NONE,
        resolve_var_bind_path_map: None,
        resolve_rep_prop_map: None,
        base_assertion_role: Id::NONE,
        base_assertion_individual: Id::NONE,
    };
    let dep_node = match kind {
        DepKind::IndependentBase => DependencyNode::IndependentBase { base },
        kind if kind.is_non_deterministic() => DependencyNode::NonDeterministic {
            base,
            nd: NonDetData {
                branch_track_points: TrackPointId::NONE,
                clash_track_point: TrackPointId::NONE,
                dependency_clashes: ClashDescId::NONE,
                branch_node: BranchNodeId::NONE,
                branch_tag: branching_tag,
                closing_track_point: TrackPointId::NONE,
                closed_track_point: TrackPointId::NONE,
            },
        },
        _ => DependencyNode::Deterministic { base },
    };
    let dep_node = env.ctx.process_context_mut().alloc_dep_node(dep_node);
    let mut tp = DependencyTrackPoint::new(dep_node);
    tp.process_tag = branching_tag;
    env.ctx.process_context_mut().alloc_track_point(tp)
}

fn dependency_track_point_with_previous(
    env: &mut SelfTestEnv,
    individual_node: NodeId,
    concept_descriptor: ConDescId,
    kind: DepKind,
    dependency_processing_tag: i64,
    branching_tag: i64,
    previous_track_point: TrackPointId,
    additional_track_points: &[TrackPointId],
) -> TrackPointId {
    let mut additional_after = Id::NONE;
    for add_tp in additional_track_points.iter().rev() {
        let link = env
            .ctx
            .process_context_mut()
            .alloc_dep_link(DependencyLink::new());
        env.ctx
            .process_context_mut()
            .dep_link_mut(link)
            .init_dependency(*add_tp);
        env.ctx.process_context_mut().dep_link_mut(link).next = additional_after;
        additional_after = link;
    }

    let base = DepNodeBase {
        process_tag: dependency_processing_tag,
        concept_descriptor,
        individual_node,
        kind,
        dep_track_point: previous_track_point,
        additional_after,
        selected_var_bind_path: VarBindingPathId::NONE,
        resolve_var_bind_path_map: None,
        resolve_rep_prop_map: None,
        base_assertion_role: Id::NONE,
        base_assertion_individual: Id::NONE,
    };
    let dep_node = if kind.is_non_deterministic() {
        DependencyNode::NonDeterministic {
            base,
            nd: NonDetData {
                branch_track_points: TrackPointId::NONE,
                clash_track_point: TrackPointId::NONE,
                dependency_clashes: ClashDescId::NONE,
                branch_node: BranchNodeId::NONE,
                branch_tag: branching_tag,
                closing_track_point: TrackPointId::NONE,
                closed_track_point: TrackPointId::NONE,
            },
        }
    } else {
        DependencyNode::Deterministic { base }
    };
    let dep_node = env.ctx.process_context_mut().alloc_dep_node(dep_node);
    let mut tp = DependencyTrackPoint::new(dep_node);
    tp.process_tag = branching_tag;
    env.ctx.process_context_mut().alloc_track_point(tp)
}

fn clash_descriptor_for_track_point(
    env: &mut SelfTestEnv,
    dep_track_point: TrackPointId,
) -> ClashDescId {
    let mut clash = ClashDescriptor::new();
    clash.init_clashed_dependency_descriptor(dep_track_point);
    env.ctx.process_context_mut().alloc_clash_desc(clash)
}

fn attach_saturation_unsat_reference(
    env: &mut SelfTestEnv,
    concept: ConceptId,
    negated: bool,
    clashed: bool,
) -> SatNodeId {
    let sat_node = env
        .ctx
        .process_context_mut()
        .alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));
    if clashed {
        env.ctx
            .process_context_mut()
            .sat_node_mut(sat_node)
            .indirect_status_flags
            .add_flags_code(IndividualSaturationProcessNodeStatusFlags::INDSATFLAGCLASHED);
    }

    let mut sat_ref = SaturationConceptReferenceLinking::new();
    sat_ref.set_individual_process_node_for_concept(sat_node);
    let sat_ref = env
        .ctx
        .ontology_arenas_mut()
        .alloc_saturation_concept_reference_linking(sat_ref);

    let mut con_sat_ref = ConceptSaturationReferenceLinkingData::new();
    con_sat_ref.set_saturation_reference_linking_data(sat_ref, negated);
    let con_sat_ref = env
        .ctx
        .ontology_arenas_mut()
        .alloc_concept_saturation_reference_linking_data(con_sat_ref);

    let mut con_proc_data = ConceptProcessData::new();
    con_proc_data.set_concept_reference_linking(con_sat_ref);
    let con_proc_data = env
        .ctx
        .ontology_arenas_mut()
        .alloc_concept_process_data(con_proc_data);

    env.ctx
        .ontology_arenas_mut()
        .concept_mut(concept)
        .set_concept_data(con_proc_data.raw);
    sat_node
}

#[test]
fn create_clashed_concept_descriptor_prepends_payload() {
    let mut env = build_env();
    let mut root = env.root;
    let tp1 = deterministic_track_point(&mut env);
    let tp2 = deterministic_track_point(&mut env);

    let mut con_des1 = ConceptDescriptor::new();
    con_des1.concept = env.concept_a;
    con_des1.negated = false;
    con_des1.set_dependency_track_point(tp1);
    let con_des1 = env.ctx.process_context_mut().alloc_con_desc(con_des1);

    let mut con_des2 = ConceptDescriptor::new();
    con_des2.concept = env.top_concept;
    con_des2.negated = true;
    con_des2.set_dependency_track_point(tp2);
    let con_des2 = env.ctx.process_context_mut().alloc_con_desc(con_des2);

    let first = env.algo.create_clashed_concept_descriptor(
        Id::NONE,
        &mut root,
        con_des1,
        tp1,
        &mut env.ctx,
    );
    let second =
        env.algo
            .create_clashed_concept_descriptor(first, &mut root, con_des2, tp2, &mut env.ctx);

    let first_desc = env.ctx.process_context().clash_desc(first);
    assert_eq!(first_desc.get_next(), Id::NONE);
    assert_eq!(first_desc.get_dependency_track_point(), tp1);
    assert_eq!(first_desc.get_concept_descriptor(), con_des1);
    assert_eq!(first_desc.get_appropriated_individual(), root);
    assert_eq!(first_desc.get_appropriated_individual_id(), 0);

    let second_desc = env.ctx.process_context().clash_desc(second);
    assert_eq!(second_desc.get_next(), first);
    assert_eq!(second_desc.get_dependency_track_point(), tp2);
    assert_eq!(
        second_desc.kind,
        ClashDescriptorKind::Concept {
            concept_descriptor: con_des2,
            individual_node: root,
        }
    );
}

#[test]
fn create_clashed_individual_node_descriptor_walks_adding_sorted_label_chain() {
    let mut env = build_env();
    let mut root = env.root;
    let tp1 = deterministic_track_point(&mut env);
    let tp2 = deterministic_track_point(&mut env);

    let mut con_des1 = ConceptDescriptor::new();
    con_des1.concept = env.concept_a;
    con_des1.negated = false;
    con_des1.set_dependency_track_point(tp1);
    let con_des1 = env.ctx.process_context_mut().alloc_con_desc(con_des1);

    let mut con_des2 = ConceptDescriptor::new();
    con_des2.concept = env.top_concept;
    con_des2.negated = true;
    con_des2.set_dependency_track_point(tp2);
    con_des2.set_next(con_des1);
    let con_des2 = env.ctx.process_context_mut().alloc_con_desc(con_des2);

    let mut label_set = ReapplyConceptLabelSet::new(INVALID);
    label_set.concept_des_linker = con_des2;
    label_set.concept_count = 2;
    let label_set = env.ctx.process_context_mut().alloc_label_set(label_set);
    env.ctx
        .process_context_mut()
        .node_mut(root)
        .set_reapply_concept_label_set(label_set);

    let clashes =
        env.algo
            .create_clashed_individual_node_descriptor(Id::NONE, &mut root, &mut env.ctx);

    let first_clash = env.ctx.process_context().clash_desc(clashes);
    assert_eq!(first_clash.get_concept_descriptor(), con_des1);
    assert_eq!(first_clash.get_dependency_track_point(), tp1);
    assert_eq!(first_clash.get_appropriated_individual(), root);

    let second = first_clash.get_next();
    let second_clash = env.ctx.process_context().clash_desc(second);
    assert_eq!(second_clash.get_concept_descriptor(), con_des2);
    assert_eq!(second_clash.get_dependency_track_point(), tp2);
    assert_eq!(second_clash.get_appropriated_individual(), root);
    assert_eq!(second_clash.get_next(), Id::NONE);
}

#[test]
fn create_clashed_individual_link_descriptor_prepends_payload() {
    let mut env = build_env();
    let mut root = env.root;
    let concept_tp = deterministic_track_point(&mut env);
    let link_tp = deterministic_track_point(&mut env);

    let mut con_des = ConceptDescriptor::new();
    con_des.concept = env.concept_a;
    con_des.set_dependency_track_point(concept_tp);
    let con_des = env.ctx.process_context_mut().alloc_con_desc(con_des);
    let first = env.algo.create_clashed_concept_descriptor(
        Id::NONE,
        &mut root,
        con_des,
        concept_tp,
        &mut env.ctx,
    );

    let mut edge = super::super::process::edge::IndividualLinkEdge::new();
    edge.set_dependency_track_point(link_tp);
    let edge = env.ctx.process_context_mut().alloc_edge(edge);

    let second =
        env.algo
            .create_clashed_individual_link_descriptor(first, edge, link_tp, &mut env.ctx);

    let second_desc = env.ctx.process_context().clash_desc(second);
    assert_eq!(second_desc.get_next(), first);
    assert_eq!(second_desc.get_dependency_track_point(), link_tp);
    assert_eq!(second_desc.get_individual_link_edge(), edge);
    assert_eq!(
        second_desc.kind,
        ClashDescriptorKind::IndividualLink { link_edge: edge }
    );

    let first_desc = env.ctx.process_context().clash_desc(first);
    assert_eq!(first_desc.get_next(), Id::NONE);
    assert_eq!(first_desc.get_concept_descriptor(), con_des);
}

#[test]
fn create_individual_merge_causing_descriptors_collects_link_and_label_clashes() {
    let mut env = build_env();
    let mut root = env.root;
    let concept_a_tp = deterministic_track_point(&mut env);
    let top_tp = deterministic_track_point(&mut env);
    let link_tp = deterministic_track_point(&mut env);
    let concept_a = env.concept_a;
    let top_concept = env.top_concept;

    let con_a = concept_descriptor_with_dependency(&mut env, concept_a, false, concept_a_tp);
    let con_top = concept_descriptor_with_dependency(&mut env, top_concept, false, top_tp);
    let label_set = label_set_from_descriptors(&mut env, &[con_a, con_top]);
    env.ctx
        .process_context_mut()
        .node_mut(root)
        .set_reapply_concept_label_set(label_set);

    let mut edge = super::super::process::edge::IndividualLinkEdge::new();
    edge.set_dependency_track_point(link_tp);
    let edge = env.ctx.process_context_mut().alloc_edge(edge);

    let clashes = env.algo.create_individual_merge_causing_descriptors(
        Id::NONE,
        &mut root,
        edge,
        &[
            NegLink {
                target: concept_a,
                negated: false,
            },
            NegLink {
                target: top_concept,
                negated: false,
            },
        ],
        &mut env.ctx,
    );

    let top_clash = env.ctx.process_context().clash_desc(clashes);
    assert_eq!(top_clash.get_concept_descriptor(), con_top);
    assert_eq!(top_clash.get_dependency_track_point(), top_tp);

    let a_clash = env.ctx.process_context().clash_desc(top_clash.get_next());
    assert_eq!(a_clash.get_concept_descriptor(), con_a);
    assert_eq!(a_clash.get_dependency_track_point(), concept_a_tp);

    let link_clash = env.ctx.process_context().clash_desc(a_clash.get_next());
    assert_eq!(link_clash.get_individual_link_edge(), edge);
    assert_eq!(link_clash.get_dependency_track_point(), link_tp);
    assert_eq!(link_clash.get_next(), Id::NONE);
}

#[test]
fn create_clashed_individual_distinct_descriptor_prepends_payload() {
    let mut env = build_env();
    let mut root = env.root;
    let concept_tp = deterministic_track_point(&mut env);
    let distinct_tp = deterministic_track_point(&mut env);

    let mut con_des = ConceptDescriptor::new();
    con_des.concept = env.concept_a;
    con_des.set_dependency_track_point(concept_tp);
    let con_des = env.ctx.process_context_mut().alloc_con_desc(con_des);
    let first = env.algo.create_clashed_concept_descriptor(
        Id::NONE,
        &mut root,
        con_des,
        concept_tp,
        &mut env.ctx,
    );

    let mut distinct_edge = super::super::process::edge::DistinctEdge::new();
    distinct_edge.init_distinct_edge(root, root, distinct_tp);
    let distinct_edge = env
        .ctx
        .process_context_mut()
        .alloc_distinct_edge(distinct_edge);

    let second = env.algo.create_clashed_individual_distinct_descriptor(
        first,
        distinct_edge,
        distinct_tp,
        &mut env.ctx,
    );

    let second_desc = env.ctx.process_context().clash_desc(second);
    assert_eq!(second_desc.get_next(), first);
    assert_eq!(second_desc.get_dependency_track_point(), distinct_tp);
    assert_eq!(second_desc.get_distinct_edge(), distinct_edge);
    assert_eq!(
        second_desc.kind,
        ClashDescriptorKind::IndividualDistinct { distinct_edge }
    );

    let first_desc = env.ctx.process_context().clash_desc(first);
    assert_eq!(first_desc.get_next(), Id::NONE);
    assert_eq!(first_desc.get_concept_descriptor(), con_des);
}

#[test]
fn create_clashed_negation_disjoint_descriptor_prepends_payload() {
    use super::super::model::role::Role;

    let mut env = build_env();
    let mut root = env.root;
    let concept_tp = deterministic_track_point(&mut env);
    let disjoint_tp = deterministic_track_point(&mut env);

    let mut con_des = ConceptDescriptor::new();
    con_des.concept = env.concept_a;
    con_des.set_dependency_track_point(concept_tp);
    let con_des = env.ctx.process_context_mut().alloc_con_desc(con_des);
    let first = env.algo.create_clashed_concept_descriptor(
        Id::NONE,
        &mut root,
        con_des,
        concept_tp,
        &mut env.ctx,
    );

    let role_s = {
        let mut r = Role::new();
        r.set_role_tag(172);
        env.ctx.ontology_arenas_mut().alloc_role(r)
    };
    let mut disjoint_edge = super::super::process::edge::DisjointEdge::new();
    disjoint_edge.init_negation_disjoint_edge(root, root, role_s, disjoint_tp);
    let disjoint_edge = env
        .ctx
        .process_context_mut()
        .alloc_disjoint_edge(disjoint_edge);

    let second = env.algo.create_clashed_negation_disjoint_descriptor(
        first,
        disjoint_edge,
        disjoint_tp,
        &mut env.ctx,
    );

    let second_desc = env.ctx.process_context().clash_desc(second);
    assert_eq!(second_desc.get_next(), first);
    assert_eq!(second_desc.get_dependency_track_point(), disjoint_tp);
    assert_eq!(second_desc.get_negation_disjoint_link_edge(), disjoint_edge);
    assert_eq!(
        second_desc.kind,
        ClashDescriptorKind::NegationDisjointLink { disjoint_edge }
    );

    let first_desc = env.ctx.process_context().clash_desc(first);
    assert_eq!(first_desc.get_next(), Id::NONE);
    assert_eq!(first_desc.get_concept_descriptor(), con_des);
}

#[test]
fn create_tracked_clashes_descriptor_from_concept_clash_payload() {
    let mut env = build_env();
    let mut root = env.root;

    let mut con_des = ConceptDescriptor::new();
    con_des.concept = env.concept_a;
    let con_des = env.ctx.process_context_mut().alloc_con_desc(con_des);
    let tp = real_dependency_track_point(&mut env, root, con_des, DepKind::IndependentBase, 31, 7);
    env.ctx
        .process_context_mut()
        .con_desc_mut(con_des)
        .set_dependency_track_point(tp);

    let clash =
        env.algo
            .create_clashed_concept_descriptor(Id::NONE, &mut root, con_des, tp, &mut env.ctx);
    let tracked = env
        .algo
        .create_tracked_clashes_descriptor(clash, &mut env.ctx, INVALID, false);

    let tracked_desc = env.ctx.process_context().clash_desc(tracked);
    assert_eq!(tracked_desc.get_next_descriptor(), Id::NONE);
    assert_eq!(tracked_desc.get_dependency_track_point(), tp);
    assert_eq!(tracked_desc.get_concept_descriptor(), con_des);
    assert_eq!(tracked_desc.get_appropriated_individual(), root);
    assert_eq!(tracked_desc.get_appropriated_individual_id(), 0);
    assert_eq!(tracked_desc.get_appropriated_individual_level(), 0);
    assert_eq!(tracked_desc.get_processing_tag(), 31);
    assert_eq!(tracked_desc.get_branching_level_tag(), 7);
    assert!(tracked_desc.is_pointing_to_deterministic_dependency_node());
    assert!(tracked_desc.is_pointing_to_independent_dependency_node());
    assert!(!tracked_desc.is_appropriated_individual_nominal());
    assert!(!tracked_desc.is_tracking_error());
    assert_eq!(
        tracked_desc.kind,
        ClashDescriptorKind::Tracked {
            individual_node: root,
            individual_node_id: 0,
            individual_node_level: 0,
            branching_level_tag: 7,
            processing_tag: 31,
            deterministic: true,
            nominal_individual: false,
            error: false,
            independent: true,
            concept_descriptor: con_des,
            var_bind_path: VarBindingPathId::NONE,
        }
    );
}

#[test]
fn add_indi_node_signature_of_unsatisfiable_clashed_descriptors_inserts_label_signature() {
    let mut env = build_env();
    let signature = 4242;
    let mut label_set = ReapplyConceptLabelSet::new(0);
    label_set.get_concept_signature().signature_value = signature;
    let label_set = env.ctx.process_context_mut().alloc_label_set(label_set);
    env.ctx
        .process_context_mut()
        .node_mut(env.root)
        .set_reapply_concept_label_set(label_set);

    let mut tracked = ClashDescriptor::new();
    tracked.init_tracked_clashed_descriptor(
        env.root,
        0,
        0,
        false,
        ConDescId::NONE,
        VarBindingPathId::NONE,
        TrackPointId::NONE,
        true,
        false,
        11,
        0,
        false,
    );
    let tracked = env.ctx.process_context_mut().alloc_clash_desc(tracked);

    assert!(env
        .algo
        .add_indi_node_signature_of_unsatisfiable_clashed_descriptors(tracked, &mut env.ctx));
    assert!(env.algo.unsat_caching_signature_set.contains(&signature));
}

#[test]
fn create_tracked_clashes_descriptors_prepends_each_converted_clash() {
    let mut env = build_env();
    let mut root = env.root;

    let mut con_des1 = ConceptDescriptor::new();
    con_des1.concept = env.concept_a;
    let con_des1 = env.ctx.process_context_mut().alloc_con_desc(con_des1);
    let tp1 =
        real_dependency_track_point(&mut env, root, con_des1, DepKind::IndependentBase, 32, 8);
    env.ctx
        .process_context_mut()
        .con_desc_mut(con_des1)
        .set_dependency_track_point(tp1);

    let mut con_des2 = ConceptDescriptor::new();
    con_des2.concept = env.top_concept;
    let con_des2 = env.ctx.process_context_mut().alloc_con_desc(con_des2);
    let tp2 =
        real_dependency_track_point(&mut env, root, con_des2, DepKind::IndependentBase, 33, 9);
    env.ctx
        .process_context_mut()
        .con_desc_mut(con_des2)
        .set_dependency_track_point(tp2);

    let first = env.algo.create_clashed_concept_descriptor(
        Id::NONE,
        &mut root,
        con_des1,
        tp1,
        &mut env.ctx,
    );
    let second =
        env.algo
            .create_clashed_concept_descriptor(first, &mut root, con_des2, tp2, &mut env.ctx);

    let tracked_head =
        env.algo
            .create_tracked_clashes_descriptors(second, &mut env.ctx, INVALID, false);
    let tracked_first = env.ctx.process_context().clash_desc(tracked_head);
    assert_eq!(tracked_first.get_concept_descriptor(), con_des1);
    assert_eq!(tracked_first.get_dependency_track_point(), tp1);

    let tracked_second_id = tracked_first.get_next_descriptor();
    let tracked_second = env.ctx.process_context().clash_desc(tracked_second_id);
    assert_eq!(tracked_second.get_concept_descriptor(), con_des2);
    assert_eq!(tracked_second.get_dependency_track_point(), tp2);
    assert_eq!(tracked_second.get_next_descriptor(), Id::NONE);
}

#[test]
fn create_tracked_clashes_descriptor_copies_independent_concept_descriptor() {
    let mut env = build_env();
    let mut root = env.root;

    let mut con_des = ConceptDescriptor::new();
    con_des.concept = env.concept_a;
    con_des.negated = true;
    let con_des = env.ctx.process_context_mut().alloc_con_desc(con_des);
    let tp = real_dependency_track_point(&mut env, root, con_des, DepKind::IndependentBase, 34, 10);
    env.ctx
        .process_context_mut()
        .con_desc_mut(con_des)
        .set_dependency_track_point(tp);

    let clash =
        env.algo
            .create_clashed_concept_descriptor(Id::NONE, &mut root, con_des, tp, &mut env.ctx);
    let tracked = env
        .algo
        .create_tracked_clashes_descriptor(clash, &mut env.ctx, INVALID, false);
    let copied = env
        .algo
        .create_tracked_clashes_descriptor(tracked, &mut env.ctx, INVALID, true);

    let copied_con_des = env
        .ctx
        .process_context()
        .clash_desc(copied)
        .get_concept_descriptor();
    assert_ne!(copied_con_des, con_des);
    let copied_con_desc = env.ctx.process_context().con_desc(copied_con_des);
    assert_eq!(copied_con_desc.get_concept(), env.concept_a);
    assert!(copied_con_desc.is_negated());
    assert_eq!(copied_con_desc.get_dependency_track_point(), tp);

    let copied_desc = env.ctx.process_context().clash_desc(copied);
    assert_eq!(copied_desc.get_appropriated_individual(), root);
    assert_eq!(copied_desc.get_dependency_track_point(), tp);
    assert!(copied_desc.is_pointing_to_independent_dependency_node());
    assert_eq!(copied_desc.get_next_descriptor(), Id::NONE);
}

fn tracked_concept_clash(
    env: &mut SelfTestEnv,
    individual_node: NodeId,
    concept: ConceptId,
    negated: bool,
    kind: DepKind,
    dependency_processing_tag: i64,
    branching_tag: i64,
) -> ClashDescId {
    let mut con_des = ConceptDescriptor::new();
    con_des.concept = concept;
    con_des.negated = negated;
    let con_des = env.ctx.process_context_mut().alloc_con_desc(con_des);
    let tp = real_dependency_track_point(
        env,
        individual_node,
        con_des,
        kind,
        dependency_processing_tag,
        branching_tag,
    );
    env.ctx
        .process_context_mut()
        .con_desc_mut(con_des)
        .set_dependency_track_point(tp);

    let mut clash_node = individual_node;
    let clash = env.algo.create_clashed_concept_descriptor(
        Id::NONE,
        &mut clash_node,
        con_des,
        tp,
        &mut env.ctx,
    );
    env.algo
        .create_tracked_clashes_descriptor(clash, &mut env.ctx, INVALID, false)
}

fn test_node_at_depth(env: &mut SelfTestEnv, individual_id: i64, depth: i64) -> NodeId {
    let node = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(node)
        .set_individual_node_id(individual_id)
        .set_individual_ancestor_depth(depth);
    node
}

fn register_test_node(env: &mut SelfTestEnv, node: NodeId) {
    let individual_id = env.ctx.process_context().node(node).individual_node_id();
    env.ctx
        .processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(individual_id, node);
}

fn install_test_successor_link(
    env: &mut SelfTestEnv,
    source: NodeId,
    destination: NodeId,
    tag: i64,
) {
    let role = {
        let mut role = super::super::model::role::Role::new();
        role.set_role_tag(tag);
        env.ctx.ontology_arenas_mut().alloc_role(role)
    };
    let edge = {
        let mut edge = super::super::process::edge::IndividualLinkEdge::new();
        edge.set_source_individual(source);
        edge.set_destination_individual(destination);
        edge.set_link_role(role);
        env.ctx.process_context_mut().alloc_edge(edge)
    };
    let mut reapply_it = super::super::process::rs1::ReapplyQueueIterator::empty();
    env.ctx
        .process_context_mut()
        .node_install_individual_link(source, edge, &mut reapply_it);
}

fn install_test_ancestor_link(env: &mut SelfTestEnv, ancestor: NodeId, child: NodeId, tag: i64) {
    let role = {
        let mut role = super::super::model::role::Role::new();
        role.set_role_tag(tag);
        env.ctx.ontology_arenas_mut().alloc_role(role)
    };
    let edge = {
        let mut edge = super::super::process::edge::IndividualLinkEdge::new();
        edge.set_source_individual(ancestor);
        edge.set_destination_individual(child);
        edge.set_link_role(role);
        env.ctx.process_context_mut().alloc_edge(edge)
    };
    env.ctx
        .process_context_mut()
        .node_mut(child)
        .set_ancestor_link(edge);
}

fn add_test_connection_successor(env: &mut SelfTestEnv, node: NodeId, connected: NodeId) {
    let connected_id = env
        .ctx
        .process_context()
        .node(connected)
        .individual_node_id();
    let conn_set = env
        .ctx
        .process_context_mut()
        .node_connection_successor_set(node);
    env.ctx
        .process_context_mut()
        .conn_succ_set_mut(conn_set)
        .insert_connection_successor(connected_id);
}

#[test]
fn unit03_propagate_processing_restriction_to_ancestor_marks_direct_ancestor() {
    let mut env = build_env();
    let root = env.root;
    let child = test_node_at_depth(&mut env, 65, 1);
    install_test_ancestor_link(&mut env, root, child, 265);

    env.algo
        .propagate_adding_processing_restriction_to_ancestor(
            child,
            IndividualProcessNode::PRF_BLOCKINGRETESTDUEANCESTORMODIFIED,
            false,
            IndividualProcessNode::PRF_PURGEDBLOCKED,
            &mut env.ctx,
        );

    assert!(env
        .ctx
        .process_context()
        .node(root)
        .has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_BLOCKINGRETESTDUEANCESTORMODIFIED
        ));
}

#[test]
fn unit03_propagate_processing_restriction_to_ancestor_recurses_until_stop_flag() {
    let mut env = build_env();
    let root = env.root;
    let mid = test_node_at_depth(&mut env, 66, 1);
    let leaf = test_node_at_depth(&mut env, 67, 2);
    install_test_ancestor_link(&mut env, root, mid, 266);
    install_test_ancestor_link(&mut env, mid, leaf, 267);
    env.ctx
        .process_context_mut()
        .node_mut(root)
        .add_processing_restriction_flags(IndividualProcessNode::PRF_PURGEDBLOCKED);

    env.algo
        .propagate_adding_processing_restriction_to_ancestor(
            leaf,
            IndividualProcessNode::PRF_BLOCKINGRETESTDUEANCESTORMODIFIED,
            true,
            IndividualProcessNode::PRF_PURGEDBLOCKED,
            &mut env.ctx,
        );

    assert!(env
        .ctx
        .process_context()
        .node(mid)
        .has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_BLOCKINGRETESTDUEANCESTORMODIFIED
        ));
    assert!(!env
        .ctx
        .process_context()
        .node(root)
        .has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_BLOCKINGRETESTDUEANCESTORMODIFIED
        ));
}

#[test]
fn unit21_reactivate_indirect_satisfiable_cached_successors_marks_and_queues_deeper_successor() {
    let mut env = build_env();
    env.algo.conf_depth_orientated_processing = true;
    env.algo.opt_det_exp_preporcessing = false;
    let root = env.root;
    env.ctx
        .process_context_mut()
        .node_mut(root)
        .set_individual_ancestor_depth(1);

    let deeper = test_node_at_depth(&mut env, 61, 2);
    register_test_node(&mut env, deeper);
    env.ctx
        .process_context_mut()
        .node_mut(deeper)
        .add_processing_restriction_flags(IndividualProcessNode::PRF_ANCESTORSATISFIABLECACHED);
    install_test_successor_link(&mut env, root, deeper, 261);

    let same_depth = test_node_at_depth(&mut env, 62, 1);
    register_test_node(&mut env, same_depth);
    env.ctx
        .process_context_mut()
        .node_mut(same_depth)
        .add_processing_restriction_flags(IndividualProcessNode::PRF_ANCESTORSATISFIABLECACHED);
    install_test_successor_link(&mut env, root, same_depth, 262);

    env.algo
        .reactivate_indirect_satisfiable_cached_successors(root, false, &mut env.ctx);

    assert!(env
        .ctx
        .process_context()
        .node(deeper)
        .has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_ANCESTORSATISFIABLECACHEDABOLISHED
        ));
    assert!(!env
        .ctx
        .process_context()
        .node(same_depth)
        .has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_ANCESTORSATISFIABLECACHEDABOLISHED
        ));
    let q = env.ctx.get_individual_depth_first_processing_queue(false);
    assert!(q.is_some());
    assert_eq!(
        env.ctx
            .process_context_mut()
            .indi_unsorted_proc_queue_mut(q)
            .take_next_process_individual_node(),
        deeper
    );
}

#[test]
fn unit21_reactivate_indirect_saturation_cached_successors_marks_and_queues_deeper_successor() {
    let mut env = build_env();
    env.algo.conf_depth_orientated_processing = true;
    env.algo.opt_det_exp_preporcessing = false;
    let root = env.root;
    env.ctx
        .process_context_mut()
        .node_mut(root)
        .set_individual_ancestor_depth(1);

    let deeper = test_node_at_depth(&mut env, 63, 2);
    register_test_node(&mut env, deeper);
    env.ctx
        .process_context_mut()
        .node_mut(deeper)
        .add_processing_restriction_flags(
            IndividualProcessNode::PRF_ANCESTORSATURATIONBLOCKINGCACHED,
        );
    install_test_successor_link(&mut env, root, deeper, 263);

    let already_abolished = test_node_at_depth(&mut env, 64, 2);
    register_test_node(&mut env, already_abolished);
    env.ctx
        .process_context_mut()
        .node_mut(already_abolished)
        .add_processing_restriction_flags(
            IndividualProcessNode::PRF_ANCESTORSATURATIONBLOCKINGCACHED
                | IndividualProcessNode::PRF_ANCESTORSATURATIONBLOCKINGCACHEDABOLISHED,
        );
    install_test_successor_link(&mut env, root, already_abolished, 264);

    env.algo
        .reactivate_indirect_saturation_cached_successors(root, false, &mut env.ctx);

    assert!(env
        .ctx
        .process_context()
        .node(deeper)
        .has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_ANCESTORSATURATIONBLOCKINGCACHEDABOLISHED
        ));
    let q = env.ctx.get_individual_depth_first_processing_queue(false);
    assert!(q.is_some());
    assert_eq!(
        env.ctx
            .process_context_mut()
            .indi_unsorted_proc_queue_mut(q)
            .take_next_process_individual_node(),
        deeper
    );
    assert!(env
        .ctx
        .process_context()
        .indi_unsorted_proc_queue(q)
        .is_empty());
}

#[test]
fn unit04_search_reactivate_drains_processing_blocked_linker() {
    let mut env = build_env();
    env.algo.conf_depth_orientated_processing = true;
    env.algo.opt_det_exp_preporcessing = false;
    let root = env.root;

    let blocked_first = test_node_at_depth(&mut env, 265, 1);
    let blocked_second = test_node_at_depth(&mut env, 266, 1);
    env.ctx
        .process_context_mut()
        .node_mut(root)
        .add_processing_blocked_individuals_linker(vec![blocked_first, blocked_second]);

    env.algo
        .search_reactivate_individuals_processed_propagated(root, &mut env.ctx);

    assert!(env
        .ctx
        .process_context()
        .node(blocked_first)
        .has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_BLOCKINGRETESTDUEPROCESSINGCOMPLETED,
        ));
    assert!(env
        .ctx
        .process_context()
        .node(blocked_second)
        .has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_BLOCKINGRETESTDUEPROCESSINGCOMPLETED,
        ));
    assert!(env
        .ctx
        .process_context()
        .node(root)
        .get_processing_blocked_individuals_linker()
        .is_empty());

    let q = env.ctx.get_individual_depth_first_processing_queue(false);
    assert!(q.is_some());
    let first_queued = env
        .ctx
        .process_context_mut()
        .indi_unsorted_proc_queue_mut(q)
        .take_next_process_individual_node();
    let second_queued = env
        .ctx
        .process_context_mut()
        .indi_unsorted_proc_queue_mut(q)
        .take_next_process_individual_node();
    let mut queued = [first_queued, second_queued];
    queued.sort_by_key(|id| id.index());
    let mut expected = [blocked_first, blocked_second];
    expected.sort_by_key(|id| id.index());
    assert_eq!(queued, expected);
    assert!(env
        .ctx
        .process_context()
        .indi_unsorted_proc_queue(q)
        .is_empty());
}

#[test]
fn unit04_search_reactivate_marks_successor_ancestor_all_processed() {
    let mut env = build_env();
    env.algo.conf_depth_orientated_processing = true;
    env.algo.opt_det_exp_preporcessing = false;
    let root = env.root;

    let successor = test_node_at_depth(&mut env, 267, 1);
    register_test_node(&mut env, successor);
    install_test_successor_link(&mut env, root, successor, 267);
    add_test_connection_successor(&mut env, successor, root);

    env.algo
        .search_reactivate_individuals_processed_propagated(root, &mut env.ctx);

    assert!(
        env.ctx
            .process_context()
            .node(successor)
            .has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_ANCESTORALLPROCESSED,
            )
    );
    assert!(env
        .ctx
        .get_individual_depth_first_processing_queue(false)
        .is_none());
}

#[test]
fn unit04_search_reactivate_requeues_processing_blocked_successor() {
    let mut env = build_env();
    env.algo.conf_depth_orientated_processing = true;
    env.algo.opt_det_exp_preporcessing = false;
    let root = env.root;

    let successor = test_node_at_depth(&mut env, 268, 1);
    register_test_node(&mut env, successor);
    env.ctx
        .process_context_mut()
        .node_mut(successor)
        .add_processing_restriction_flags(IndividualProcessNode::PRF_PROCESSINGBLOCKED);
    install_test_successor_link(&mut env, root, successor, 268);
    add_test_connection_successor(&mut env, successor, root);

    env.algo
        .search_reactivate_individuals_processed_propagated(root, &mut env.ctx);

    assert!(env
        .ctx
        .process_context()
        .node(successor)
        .has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_ANCESTORALLPROCESSED
                | IndividualProcessNode::PRF_BLOCKINGRETESTDUEPROCESSINGCOMPLETED,
        ));
    let q = env.ctx.get_individual_depth_first_processing_queue(false);
    assert!(q.is_some());
    assert_eq!(
        env.ctx
            .process_context_mut()
            .indi_unsorted_proc_queue_mut(q)
            .take_next_process_individual_node(),
        successor
    );
    assert!(env
        .ctx
        .process_context()
        .indi_unsorted_proc_queue(q)
        .is_empty());
}

#[test]
fn unit04_search_reactivate_recurses_completed_successor() {
    let mut env = build_env();
    env.algo.conf_depth_orientated_processing = true;
    env.algo.opt_det_exp_preporcessing = false;
    let root = env.root;

    let successor = test_node_at_depth(&mut env, 269, 1);
    register_test_node(&mut env, successor);
    env.ctx
        .process_context_mut()
        .node_mut(successor)
        .add_processing_restriction_flags(IndividualProcessNode::PRF_PROCESSINGCOMPLETED);
    install_test_successor_link(&mut env, root, successor, 269);
    add_test_connection_successor(&mut env, successor, root);

    let blocked = test_node_at_depth(&mut env, 270, 2);
    env.ctx
        .process_context_mut()
        .node_mut(successor)
        .add_processing_blocked_individuals_linker(vec![blocked]);

    env.algo
        .search_reactivate_individuals_processed_propagated(root, &mut env.ctx);

    assert!(
        env.ctx
            .process_context()
            .node(successor)
            .has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_ANCESTORALLPROCESSED,
            )
    );
    assert!(env
        .ctx
        .process_context()
        .node(blocked)
        .has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_BLOCKINGRETESTDUEPROCESSINGCOMPLETED,
        ));
    assert!(env
        .ctx
        .process_context()
        .node(successor)
        .get_processing_blocked_individuals_linker()
        .is_empty());

    let q = env.ctx.get_individual_depth_first_processing_queue(false);
    assert!(q.is_some());
    assert_eq!(
        env.ctx
            .process_context_mut()
            .indi_unsorted_proc_queue_mut(q)
            .take_next_process_individual_node(),
        blocked
    );
    assert!(env
        .ctx
        .process_context()
        .indi_unsorted_proc_queue(q)
        .is_empty());
}

#[test]
fn unit04_propagate_unprocessed_clears_completed_and_recurses_missing_ancestor_flag() {
    let mut env = build_env();
    let root = env.root;

    env.ctx
        .process_context_mut()
        .node_mut(root)
        .add_processing_restriction_flags(
            IndividualProcessNode::PRF_PROCESSINGCOMPLETED
                | IndividualProcessNode::PRF_ANCESTORALLPROCESSED,
        );

    let successor = test_node_at_depth(&mut env, 271, 1);
    register_test_node(&mut env, successor);
    env.ctx
        .process_context_mut()
        .node_mut(successor)
        .add_processing_restriction_flags(
            IndividualProcessNode::PRF_PROCESSINGCOMPLETED
                | IndividualProcessNode::PRF_CONSNODEPREPARATIONINDINODE,
        );
    install_test_successor_link(&mut env, root, successor, 271);

    env.algo
        .propagate_individual_unprocessed_cons(root, false, &mut env.ctx);

    assert!(!env
        .ctx
        .process_context()
        .node(root)
        .has_partial_processing_restriction_flags(IndividualProcessNode::PRF_PROCESSINGCOMPLETED,));
    assert!(
        env.ctx
            .process_context()
            .node(root)
            .has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_ANCESTORALLPROCESSED,
            )
    );
    assert!(!env
        .ctx
        .process_context()
        .node(successor)
        .has_partial_processing_restriction_flags(IndividualProcessNode::PRF_PROCESSINGCOMPLETED,));
}

#[test]
fn unit04_propagate_unprocessed_skips_successor_that_already_has_ancestor_flag() {
    let mut env = build_env();
    let root = env.root;

    env.ctx
        .process_context_mut()
        .node_mut(root)
        .add_processing_restriction_flags(
            IndividualProcessNode::PRF_PROCESSINGCOMPLETED
                | IndividualProcessNode::PRF_ANCESTORALLPROCESSED,
        );

    let successor = test_node_at_depth(&mut env, 272, 1);
    register_test_node(&mut env, successor);
    env.ctx
        .process_context_mut()
        .node_mut(successor)
        .add_processing_restriction_flags(
            IndividualProcessNode::PRF_PROCESSINGCOMPLETED
                | IndividualProcessNode::PRF_ANCESTORALLPROCESSED
                | IndividualProcessNode::PRF_CONSNODEPREPARATIONINDINODE,
        );
    install_test_successor_link(&mut env, root, successor, 272);

    env.algo
        .propagate_individual_unprocessed_cons(root, false, &mut env.ctx);

    assert!(!env
        .ctx
        .process_context()
        .node(root)
        .has_partial_processing_restriction_flags(IndividualProcessNode::PRF_PROCESSINGCOMPLETED,));
    assert!(env
        .ctx
        .process_context()
        .node(successor)
        .has_partial_processing_restriction_flags(IndividualProcessNode::PRF_PROCESSINGCOMPLETED,));
}

#[test]
fn unit04_propagate_unprocessed_requires_cons_preparation_flag() {
    let mut env = build_env();
    let root = env.root;

    env.ctx
        .process_context_mut()
        .node_mut(root)
        .add_processing_restriction_flags(IndividualProcessNode::PRF_PROCESSINGCOMPLETED);

    env.algo
        .propagate_individual_unprocessed_cons(root, true, &mut env.ctx);
    assert!(env
        .ctx
        .process_context()
        .node(root)
        .has_partial_processing_restriction_flags(IndividualProcessNode::PRF_PROCESSINGCOMPLETED,));

    env.ctx
        .process_context_mut()
        .node_mut(root)
        .add_processing_restriction_flags(IndividualProcessNode::PRF_CONSNODEPREPARATIONINDINODE);
    env.algo
        .propagate_individual_unprocessed_cons(root, true, &mut env.ctx);
    assert!(!env
        .ctx
        .process_context()
        .node(root)
        .has_partial_processing_restriction_flags(IndividualProcessNode::PRF_PROCESSINGCOMPLETED,));
}

#[test]
fn unit04_add_concept_skip_and_processing_inserts_label_and_queue_descriptor() {
    let mut env = build_env();
    let root = env.root;
    let dep = deterministic_track_point(&mut env);
    let concept = processable_or_concept(&mut env, 2710);

    env.algo.add_concept_to_individual_skip_and_processing(
        concept,
        false,
        root,
        dep,
        false,
        true,
        false,
        &mut env.ctx,
    );

    assert_eq!(env.algo.stat_con_des_insertion_count, 1);
    assert_eq!(env.algo.stat_con_des_contained_count, 0);

    let label_set = env
        .ctx
        .process_context()
        .node(root)
        .use_reapply_con_label_set;
    let mut stored_dep = TrackPointId::NONE;
    let mut descriptor = ConDescId::NONE;
    let found = env
        .ctx
        .process_context()
        .label_set(label_set)
        .get_concept_descriptor_in_context(
            env.ctx.process_context(),
            env.ctx.ontology_arenas(),
            concept,
            &mut descriptor,
            &mut stored_dep,
        );
    assert!(found);
    assert!(descriptor.is_some());
    assert_eq!(stored_dep, dep);

    let queue = env
        .ctx
        .process_context_mut()
        .node_concept_processing_queue(root, false);
    assert_eq!(
        env.ctx
            .process_context()
            .concept_proc_queue(queue)
            .get_descriptor_count(),
        1
    );
}

#[test]
fn unit04_add_concept_skip_and_processing_marks_label_modification_when_requested() {
    let mut env = build_env();
    let root = env.root;
    let dep = deterministic_track_point(&mut env);
    let concept = processable_or_concept(&mut env, 2711);

    env.algo.add_concept_to_individual_skip_and_processing(
        concept,
        false,
        root,
        dep,
        false,
        true,
        true,
        &mut env.ctx,
    );

    let current_tag = env
        .ctx
        .process_context()
        .used_process_tagger()
        .get_current_concept_label_set_modification_tag();
    let label_set = env
        .ctx
        .process_context()
        .node(root)
        .use_reapply_con_label_set;
    assert_eq!(current_tag, 1);
    assert_eq!(
        env.ctx
            .process_context()
            .label_set(label_set)
            .get_concept_label_set_modification_tag(),
        current_tag
    );
}

#[test]
fn unit04_add_concept_skip_and_processing_counts_contained_duplicates() {
    let mut env = build_env();
    let root = env.root;
    let dep = deterministic_track_point(&mut env);
    let concept = processable_or_concept(&mut env, 2712);

    env.algo.add_concept_to_individual_skip_and_processing(
        concept,
        false,
        root,
        dep,
        false,
        true,
        false,
        &mut env.ctx,
    );
    env.algo.add_concept_to_individual_skip_and_processing(
        concept,
        false,
        root,
        dep,
        false,
        true,
        false,
        &mut env.ctx,
    );

    assert_eq!(env.algo.stat_con_des_insertion_count, 1);
    assert_eq!(env.algo.stat_con_des_contained_count, 1);
    let queue = env
        .ctx
        .process_context_mut()
        .node_concept_processing_queue(root, false);
    assert_eq!(
        env.ctx
            .process_context()
            .concept_proc_queue(queue)
            .get_descriptor_count(),
        1
    );
    assert!(
        env.ctx
            .processing_data_box()
            .remaining_concept_descriptor()
            .len()
            > 0
    );
}

#[test]
fn unit04_insert_concept_process_descriptor_routes_propagation_to_batch_queue() {
    let mut env = build_env();
    let root = env.root;
    let (concept, _, con_pro_des) = operator_concept_process_descriptor(
        &mut env,
        2720,
        super::super::model::op::CCPBINDVARIABLE,
        4.0,
    );
    let concept_queue = env
        .ctx
        .process_context_mut()
        .node_concept_processing_queue(root, true);

    env.algo
        .insert_concept_process_descriptor_to_processing_queue(
            con_pro_des,
            concept_queue,
            root,
            &mut env.ctx,
        );

    assert!(env
        .ctx
        .process_context()
        .concept_proc_queue(concept_queue)
        .is_empty());
    let batch_queue = env
        .ctx
        .get_variable_binding_concept_batch_processing_queue(false);
    assert!(batch_queue.is_some());
    assert_eq!(
        env.ctx
            .take_next_variable_binding_concept_batch_process_individual(batch_queue),
        Some((concept, root, con_pro_des))
    );
}

#[test]
fn unit04_insert_concept_process_descriptor_binding_routes_all_and_to_binding_count_queue() {
    let mut env = build_env();
    let root = env.root;
    let (_, _, con_pro_des) = operator_concept_process_descriptor(
        &mut env,
        2721,
        super::super::model::op::CCPBINDALL,
        4.0,
    );
    let concept_queue = env
        .ctx
        .process_context_mut()
        .node_concept_processing_queue(root, true);

    env.algo
        .insert_concept_process_descriptor_to_processing_queue_binding(
            con_pro_des,
            concept_queue,
            7,
            root,
            &mut env.ctx,
        );

    assert!(env
        .ctx
        .process_context()
        .concept_proc_queue(concept_queue)
        .is_empty());
    let batch_queue = env
        .ctx
        .get_variable_binding_concept_batch_processing_queue(false);
    assert!(batch_queue.is_some());
    assert_eq!(
        env.ctx
            .take_next_variable_binding_concept_batch_process_individual(batch_queue),
        Some((ConceptId::NONE, root, con_pro_des))
    );
}

#[test]
fn unit04_add_concept_to_processing_queue_reinsert_restores_default_priority_descriptor() {
    let mut env = build_env();
    let root = env.root;
    let (_, _, con_pro_des) =
        operator_concept_process_descriptor(&mut env, 2722, super::super::model::op::CCOR, 4.0);
    let concept_queue = env
        .ctx
        .process_context_mut()
        .node_concept_processing_queue(root, true);
    ConceptProcessingQueue::insert_concept_process_descriptor(
        concept_queue,
        con_pro_des,
        env.ctx.process_context_mut(),
    );
    assert_eq!(
        ConceptProcessingQueue::take_next_concept_descriptor_process(
            concept_queue,
            env.ctx.process_context_mut(),
        ),
        con_pro_des
    );
    assert!(env
        .ctx
        .process_context()
        .concept_proc_queue(concept_queue)
        .is_empty());

    env.algo.add_concept_to_processing_queue_reinsert(
        con_pro_des,
        concept_queue,
        root,
        &mut env.ctx,
    );

    assert_eq!(
        env.ctx
            .process_context()
            .concept_proc_queue(concept_queue)
            .get_descriptor_count(),
        1
    );
    assert_eq!(
        ConceptProcessingQueue::take_next_concept_descriptor_process(
            concept_queue,
            env.ctx.process_context_mut(),
        ),
        con_pro_des
    );
}

#[test]
fn unit04_add_concept_to_processing_queue_reinsert_restores_sorted_priority_descriptor() {
    let mut env = build_env();
    let root = env.root;
    let (_, _, con_pro_des) =
        operator_concept_process_descriptor(&mut env, 2723, super::super::model::op::CCOR, 4.5);
    let concept_queue = env
        .ctx
        .process_context_mut()
        .node_concept_processing_queue(root, true);
    ConceptProcessingQueue::insert_concept_process_descriptor(
        concept_queue,
        con_pro_des,
        env.ctx.process_context_mut(),
    );
    assert_eq!(
        ConceptProcessingQueue::take_next_concept_descriptor_process(
            concept_queue,
            env.ctx.process_context_mut(),
        ),
        con_pro_des
    );

    env.algo.add_concept_to_processing_queue_reinsert(
        con_pro_des,
        concept_queue,
        root,
        &mut env.ctx,
    );

    assert_eq!(
        ConceptProcessingQueue::take_next_concept_descriptor_process(
            concept_queue,
            env.ctx.process_context_mut(),
        ),
        con_pro_des
    );
    assert!(env
        .ctx
        .process_context()
        .concept_proc_queue(concept_queue)
        .is_empty());
}

#[test]
fn unit04_add_individual_depth_oriented_sets_processing_queue_flag() {
    let mut env = build_env();
    env.algo.conf_depth_orientated_processing = true;
    env.algo.opt_det_exp_preporcessing = false;
    let root = env.root;

    assert!(env
        .algo
        .add_individual_to_processing_queue(root, &mut env.ctx));

    assert!(env.ctx.process_context().node(root).is_processing_queued());
    let q = env.ctx.get_individual_depth_first_processing_queue(false);
    assert!(q.is_some());
    assert_eq!(
        env.ctx
            .process_context_mut()
            .indi_unsorted_proc_queue_mut(q)
            .take_next_process_individual_node(),
        root
    );
}

#[test]
fn unit04_add_individual_depth_oriented_suppresses_duplicate_processing_queue_insert() {
    let mut env = build_env();
    env.algo.conf_depth_orientated_processing = true;
    env.algo.opt_det_exp_preporcessing = false;
    let root = env.root;
    env.ctx
        .process_context_mut()
        .node_mut(root)
        .set_processing_queued(true);

    assert!(!env
        .algo
        .add_individual_to_processing_queue(root, &mut env.ctx));
    assert!(env
        .ctx
        .get_individual_depth_first_processing_queue(false)
        .is_none());
}

#[test]
fn unit04_add_individual_depth_oriented_uses_deterministic_preprocessing_queue() {
    let mut env = build_env();
    env.algo.conf_depth_orientated_processing = true;
    env.algo.opt_det_exp_preporcessing = true;
    let root = env.root;

    assert!(env
        .algo
        .add_individual_to_processing_queue(root, &mut env.ctx));

    let det_q = env
        .ctx
        .get_individual_depth_first_deterministic_expansion_processing_queue(false);
    assert!(det_q.is_some());
    assert_eq!(
        env.ctx
            .process_context_mut()
            .indi_unsorted_proc_queue_mut(det_q)
            .take_next_process_individual_node(),
        root
    );
    assert!(env
        .ctx
        .get_individual_depth_first_processing_queue(false)
        .is_none());
}

#[test]
fn unit04_add_individual_depth_oriented_low_priority_uses_regular_depth_queue() {
    let mut env = build_env();
    env.algo.conf_depth_orientated_processing = true;
    env.algo.opt_det_exp_preporcessing = true;
    let root = env.root;
    let (_, _, con_pro_des) =
        operator_concept_process_descriptor(&mut env, 2724, super::super::model::op::CCOR, 3.0);
    let concept_queue = env
        .ctx
        .process_context_mut()
        .node_concept_processing_queue(root, true);
    ConceptProcessingQueue::insert_concept_process_descriptor(
        concept_queue,
        con_pro_des,
        env.ctx.process_context_mut(),
    );

    assert!(env
        .algo
        .add_individual_to_processing_queue(root, &mut env.ctx));

    assert!(env
        .ctx
        .get_individual_depth_first_deterministic_expansion_processing_queue(false)
        .is_none());
    let q = env.ctx.get_individual_depth_first_processing_queue(false);
    assert!(q.is_some());
    assert_eq!(
        env.ctx
            .process_context_mut()
            .indi_unsorted_proc_queue_mut(q)
            .take_next_process_individual_node(),
        root
    );
}

#[test]
fn unit04_add_individual_non_depth_direct_blocked_without_retest_skips_queue() {
    let mut env = build_env();
    env.algo.conf_depth_orientated_processing = false;
    env.algo.conf_late_blocking_resolving = true;
    let root = env.root;
    env.ctx
        .process_context_mut()
        .node_mut(root)
        .add_processing_restriction_flags(IndividualProcessNode::PRF_DIRECTBLOCKED);

    assert!(!env
        .algo
        .add_individual_to_processing_queue(root, &mut env.ctx));
    assert!(env
        .ctx
        .get_blocked_reactivation_processing_queue(false)
        .is_none());
    assert!(env
        .ctx
        .get_individual_depth_processing_queue(false)
        .is_none());
}

#[test]
fn unit04_add_individual_non_depth_late_retest_queues_blocked_reactivation_once() {
    let mut env = build_env();
    env.algo.conf_depth_orientated_processing = false;
    env.algo.conf_late_blocking_resolving = true;
    let root = env.root;
    env.ctx
        .process_context_mut()
        .node_mut(root)
        .add_processing_restriction_flags(
            IndividualProcessNode::PRF_DIRECTBLOCKED
                | IndividualProcessNode::PRF_BLOCKINGRETESTDUEDIRECTMODIFIED,
        );

    assert!(env
        .algo
        .add_individual_to_processing_queue(root, &mut env.ctx));
    assert!(env
        .ctx
        .process_context()
        .node(root)
        .is_blocked_reactivation_processing_queued());
    let q = env.ctx.get_blocked_reactivation_processing_queue(false);
    assert!(q.is_some());
    assert_eq!(
        env.ctx.process_context_mut().indi_depth_queue_take_next(q),
        root
    );
    assert!(!env
        .algo
        .add_individual_to_processing_queue(root, &mut env.ctx));
}

#[test]
fn unit04_add_individual_non_depth_retest_without_late_resolving_uses_regular_depth_queue() {
    let mut env = build_env();
    env.algo.conf_depth_orientated_processing = false;
    env.algo.conf_late_blocking_resolving = false;
    let root = env.root;
    env.ctx
        .process_context_mut()
        .node_mut(root)
        .add_processing_restriction_flags(
            IndividualProcessNode::PRF_INDIRECTBLOCKED
                | IndividualProcessNode::PRF_BLOCKINGRETESTDUEINDIRECTBLOCKERLOSS,
        );
    env.ctx
        .process_context_mut()
        .node_mut(root)
        .set_immediately_processing_queued(true);

    assert!(env
        .algo
        .add_individual_to_processing_queue(root, &mut env.ctx));
    assert!(env
        .ctx
        .process_context()
        .node(root)
        .is_regular_depth_processing_queued());
    let q = env.ctx.get_individual_depth_processing_queue(false);
    assert!(q.is_some());
    assert_eq!(
        env.ctx.process_context_mut().indi_depth_queue_take_next(q),
        root
    );
    assert!(!env
        .algo
        .add_individual_to_processing_queue(root, &mut env.ctx));
}

#[test]
fn unit04_add_individual_non_depth_delayed_nominal_queue_blocks_insert() {
    let mut env = build_env();
    env.algo.conf_depth_orientated_processing = false;
    let root = env.root;
    env.ctx
        .process_context_mut()
        .node_mut(root)
        .set_delayed_nominal_processing_queued(true);

    assert!(!env
        .algo
        .add_individual_to_processing_queue(root, &mut env.ctx));
    assert!(env
        .ctx
        .get_individual_immediately_processing_queue(false)
        .is_none());
}

#[test]
fn unit04_processing_concepts_no_queue_enqueues_immediate() {
    let mut env = build_env();
    let root = env.root;
    env.algo.conf_current_individual_queuing = true;

    assert!(env
        .algo
        .add_individual_to_processing_queue_based_on_processing_concepts(root, &mut env.ctx));

    assert!(env
        .ctx
        .process_context()
        .node(root)
        .is_immediately_processing_queued());
    let q = env.ctx.get_individual_immediately_processing_queue(false);
    assert!(q.is_some());
    assert_eq!(
        env.ctx
            .process_context_mut()
            .indi_unsorted_proc_queue_mut(q)
            .take_next_process_individual_node(),
        root
    );
}

#[test]
fn unit04_processing_concepts_immediate_queue_deduplicates_flagged_node() {
    let mut env = build_env();
    let root = env.root;
    env.algo.conf_current_individual_queuing = true;
    env.ctx
        .process_context_mut()
        .node_mut(root)
        .set_immediately_processing_queued(true);

    assert!(!env
        .algo
        .add_individual_to_processing_queue_based_on_processing_concepts(root, &mut env.ctx));
    assert!(env
        .ctx
        .get_individual_immediately_processing_queue(false)
        .is_none());
}

#[test]
fn unit04_processing_concepts_current_node_no_current_queueing_skips_queue_insert() {
    let mut env = build_env();
    let root = env.root;
    env.algo.conf_current_individual_queuing = false;
    env.ctx.base.set_current_individual_node(root);

    assert!(env
        .algo
        .add_individual_to_processing_queue_based_on_processing_concepts(root, &mut env.ctx));
    assert!(!env
        .ctx
        .process_context()
        .node(root)
        .is_immediately_processing_queued());
    assert!(env
        .ctx
        .get_individual_immediately_processing_queue(false)
        .is_none());
}

#[test]
fn unit21_test_all_successors_processed_accepts_empty_successor_tree() {
    let mut env = build_env();
    let root = test_node_at_depth(&mut env, 70, 1);
    let child = test_node_at_depth(&mut env, 71, 2);
    let grandchild = test_node_at_depth(&mut env, 72, 3);
    register_test_node(&mut env, root);
    register_test_node(&mut env, child);
    register_test_node(&mut env, grandchild);
    install_test_successor_link(&mut env, root, child, 270);
    install_test_successor_link(&mut env, child, grandchild, 271);

    let mut processed = HashSet::new();
    assert!(env
        .algo
        .test_all_successors_processed_and_write_satisfiable_cache(
            root,
            &mut processed,
            Id::new(1),
            &mut env.ctx,
        ));
    assert!(processed.contains(&root));
    assert!(processed.contains(&child));
    assert!(processed.contains(&grandchild));
}

#[test]
fn unit21_test_all_successors_processed_rejects_pending_successor_queue() {
    let mut env = build_env();
    let root = test_node_at_depth(&mut env, 73, 1);
    let child = test_node_at_depth(&mut env, 74, 2);
    register_test_node(&mut env, root);
    register_test_node(&mut env, child);
    install_test_successor_link(&mut env, root, child, 272);

    let queue = env
        .ctx
        .process_context_mut()
        .node_concept_processing_queue(child, true);
    let con_desc = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    let mut cpd_val = ConceptProcessDescriptor::new();
    cpd_val.concept_des = con_desc;
    let cpd = env.ctx.process_context_mut().alloc_con_proc_desc(cpd_val);
    ConceptProcessingQueue::insert_concept_process_descriptor(
        queue,
        cpd,
        env.ctx.process_context_mut(),
    );

    let mut processed = HashSet::new();
    assert!(!env
        .algo
        .test_all_successors_processed_and_write_satisfiable_cache(
            root,
            &mut processed,
            Id::new(1),
            &mut env.ctx,
        ));
    assert!(processed.contains(&root));
    assert!(!processed.contains(&child));
}

#[test]
fn unit21_write_unsat_branch_satisfiable_cache_accepts_processed_tree() {
    let mut env = build_env();
    let root = test_node_at_depth(&mut env, 75, 1);
    let child = test_node_at_depth(&mut env, 76, 2);
    register_test_node(&mut env, root);
    register_test_node(&mut env, child);
    install_test_successor_link(&mut env, root, child, 273);
    env.ctx.base.used_sat_exp_cache_handler = Id::new(1);
    env.algo.conf_unsat_branch_satisfiable_caching = true;
    env.algo.conf_sat_exp_cache_writing = true;

    assert!(env
        .algo
        .write_satisfiable_cached_individual_nodes_of_unsatisfiable_branch(&mut env.ctx));
}

#[test]
fn unit21_write_unsat_branch_satisfiable_cache_rejects_pending_queue_tree() {
    let mut env = build_env();
    let root = test_node_at_depth(&mut env, 77, 1);
    let child = test_node_at_depth(&mut env, 78, 2);
    register_test_node(&mut env, root);
    register_test_node(&mut env, child);
    install_test_successor_link(&mut env, root, child, 274);

    let queue = env
        .ctx
        .process_context_mut()
        .node_concept_processing_queue(child, true);
    let con_desc = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    let mut cpd_val = ConceptProcessDescriptor::new();
    cpd_val.concept_des = con_desc;
    let cpd = env.ctx.process_context_mut().alloc_con_proc_desc(cpd_val);
    ConceptProcessingQueue::insert_concept_process_descriptor(
        queue,
        cpd,
        env.ctx.process_context_mut(),
    );

    env.ctx.base.used_sat_exp_cache_handler = Id::new(1);
    env.algo.conf_unsat_branch_satisfiable_caching = true;
    env.algo.conf_sat_exp_cache_writing = true;

    assert!(!env
        .algo
        .write_satisfiable_cached_individual_nodes_of_unsatisfiable_branch(&mut env.ctx));
}

#[test]
fn unit21_absorbed_generating_reapply_prepends_drains_and_clears() {
    let mut env = build_env();
    let root = env.root;
    let top_concept = env.top_concept;
    let first =
        concept_descriptor_with_dependency(&mut env, top_concept, false, TrackPointId::NONE);
    let second =
        concept_descriptor_with_dependency(&mut env, top_concept, false, TrackPointId::NONE);

    env.algo.add_satisfiable_cached_absorbed_generating_concept(
        first,
        root,
        TrackPointId::NONE,
        &mut env.ctx,
    );
    env.algo.add_satisfiable_cached_absorbed_generating_concept(
        second,
        root,
        TrackPointId::NONE,
        &mut env.ctx,
    );

    let head = env
        .ctx
        .process_context()
        .node(root)
        .satisfiable_cached_absorbed_generating_linker();
    assert_eq!(
        env.ctx
            .process_context()
            .reapply_con_desc(head)
            .get_concept_descriptor(),
        second
    );
    let next = env.ctx.process_context().reapply_con_desc(head).get_next();
    assert_eq!(
        env.ctx
            .process_context()
            .reapply_con_desc(next)
            .get_concept_descriptor(),
        first
    );

    assert!(env
        .algo
        .reapply_satisfiable_cached_absorbed_generating_concepts(root, &mut env.ctx));
    assert!(env
        .ctx
        .process_context()
        .node(root)
        .satisfiable_cached_absorbed_generating_linker()
        .is_none());

    let queue = env
        .ctx
        .process_context_mut()
        .node_concept_processing_queue(root, false);
    let queued_a = ConceptProcessingQueue::take_next_concept_descriptor_process(
        queue,
        env.ctx.process_context_mut(),
    );
    let queued_b = ConceptProcessingQueue::take_next_concept_descriptor_process(
        queue,
        env.ctx.process_context_mut(),
    );
    let queued = [
        env.ctx
            .process_context()
            .con_proc_desc(queued_a)
            .get_concept_descriptor(),
        env.ctx
            .process_context()
            .con_proc_desc(queued_b)
            .get_concept_descriptor(),
    ];
    assert!(queued.contains(&first));
    assert!(queued.contains(&second));
}

#[test]
fn unit21_absorbed_disjunction_reapply_drains_restricted_chain() {
    let mut env = build_env();
    let root = env.root;
    let top_concept = env.top_concept;
    let descriptor =
        concept_descriptor_with_dependency(&mut env, top_concept, false, TrackPointId::NONE);

    env.algo
        .add_satisfiable_cached_absorbed_disjunction_concept(
            descriptor,
            root,
            RestrictionSpecId::NONE,
            TrackPointId::NONE,
            &mut env.ctx,
        );

    assert!(env
        .algo
        .reapply_satisfiable_cached_absorbed_disjunction_concepts(root, &mut env.ctx));
    assert!(env
        .ctx
        .process_context()
        .node(root)
        .satisfiable_cached_absorbed_disjunctions_linker()
        .is_none());

    let queue = env
        .ctx
        .process_context_mut()
        .node_concept_processing_queue(root, false);
    let queued = ConceptProcessingQueue::take_next_concept_descriptor_process(
        queue,
        env.ctx.process_context_mut(),
    );
    let queued = env.ctx.process_context().con_proc_desc(queued);
    assert_eq!(queued.get_concept_descriptor(), descriptor);
    assert_eq!(queued.get_processing_restriction_specification(), Id::NONE);
}

fn errored_tracked_concept_clash(env: &mut SelfTestEnv, individual_node: NodeId) -> ClashDescId {
    let mut con_des = ConceptDescriptor::new();
    con_des.concept = env.concept_a;
    let con_des = env.ctx.process_context_mut().alloc_con_desc(con_des);
    let mut clash_node = individual_node;
    let clash = env.algo.create_clashed_concept_descriptor(
        Id::NONE,
        &mut clash_node,
        con_des,
        TrackPointId::NONE,
        &mut env.ctx,
    );
    env.algo
        .create_tracked_clashes_descriptor(clash, &mut env.ctx, INVALID, false)
}

fn tracked_chain_tags(env: &SelfTestEnv, mut head: ClashDescId) -> Vec<i64> {
    let mut tags = Vec::new();
    while head.is_some() {
        let con_des = env
            .ctx
            .process_context()
            .clash_desc(head)
            .get_concept_descriptor();
        tags.push(
            env.ctx
                .process_context()
                .con_desc(con_des)
                .get_concept_tag(env.ctx.ontology_arenas()),
        );
        head = env
            .ctx
            .process_context()
            .clash_desc(head)
            .get_next_descriptor();
    }
    tags
}

fn install_unsat_cache_handler(env: &mut SelfTestEnv) {
    let mut cache_context = CacheContext::new();
    let cache = cache_context.alloc_unsat_cache(OccurrenceUnsatisfiableCache::new(3, "", 0));
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
    env.ctx.install_used_unsatisfiable_cache_handler(
        UnsatisfiableCacheHandler::new(reader, writer),
        cache_context,
    );
}

fn make_constructed_nominal_root_with_single_init(
    env: &mut SelfTestEnv,
    concept: ConceptId,
    negated: bool,
) -> super::super::model::IndividualId {
    let individual = env
        .ctx
        .ontology_arenas_mut()
        .alloc_individual(Individual::new(7));
    env.ctx
        .process_context_mut()
        .node_mut(env.root)
        .set_individual_type(IndividualType::Nominal)
        .set_nominal_individual(individual)
        .set_initializing_concept_linker(vec![NegLink {
            target: concept,
            negated,
        }]);
    env.ctx
        .processing_data_box_mut()
        .set_constructed_individual_node(env.root)
        .set_multiple_construction_individual_nodes(false);
    individual
}

fn attach_previous_processing_data_box(
    env: &mut SelfTestEnv,
    previous_data_box: ProcessingDataBox,
) {
    let mut previous_task = SatisfiableCalculationTask::new();
    previous_task.set_processing_data_box_state(previous_data_box);
    let previous_task_id = env.ctx.base.alloc_sat_calc_task(previous_task);
    let previous_task_data = env
        .ctx
        .base
        .alloc_task_data(TaskData::new_consistence(previous_task_id, Id::NONE));
    let mut adapter = SatisfiableTaskIncrementalConsistencyTestingAdapter::new(0, 0, 0, 0);
    adapter.set_previous_consistence_data(previous_task_data);
    let adapter_id = env.ctx.base.alloc_inc_cons_testing_adapter(adapter);
    let mut current_task = SatisfiableCalculationTask::new();
    current_task.set_satisfiable_task_incremental_consistency_testing_adapter(adapter_id);
    let current_task_id = env.ctx.base.alloc_sat_calc_task(current_task);
    env.ctx.base.used_sat_calc_task = current_task_id;
}

fn atom_concept_with_tag(env: &mut SelfTestEnv, tag: i64) -> ConceptId {
    let mut c = Concept::new();
    c.set_concept_tag(tag);
    c.set_operator_code(super::super::model::op::CCATOM);
    env.ctx.ontology_arenas_mut().alloc_concept(c)
}

fn concept_descriptor_with_dependency(
    env: &mut SelfTestEnv,
    concept: ConceptId,
    negated: bool,
    dep_track_point: TrackPointId,
) -> ConDescId {
    let con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    env.ctx.process_context_mut().con_desc_mut(con_des).concept = concept;
    env.ctx.process_context_mut().con_desc_mut(con_des).negated = negated;
    env.ctx
        .process_context_mut()
        .con_desc_mut(con_des)
        .set_dependency_track_point(dep_track_point);
    con_des
}

fn label_set_from_descriptors(env: &mut SelfTestEnv, descriptors: &[ConDescId]) -> LabelSetId {
    let mut set = ReapplyConceptLabelSet::new(INVALID);
    for con_des in descriptors {
        let concept = env.ctx.process_context().con_desc(*con_des).get_concept();
        let negated = env.ctx.process_context().con_desc(*con_des).is_negated();
        let tag = env
            .ctx
            .process_context()
            .con_desc(*con_des)
            .get_concept_tag(env.ctx.ontology_arenas());
        set.concept_des_dep_map.insert(
            tag,
            ConceptDescriptorDependencyReapplyData {
                concept_descriptor: *con_des,
                pos_neg_reapply_queue: Default::default(),
            },
        );
        set.concept_count += 1;
        set.concept_signature
            .add_concept_signature(concept, tag, negated);
    }
    for con_des in descriptors.iter().rev() {
        env.ctx.process_context_mut().con_desc_mut(*con_des).next = set.concept_des_linker;
        set.concept_des_linker = *con_des;
    }
    env.ctx.process_context_mut().alloc_label_set(set)
}

#[test]
fn root_unsatisfiability_write_caches_writes_testing_concept_to_unsat_cache() {
    let mut env = build_env();
    env.algo.conf_tested_concept_write_unsat_caching = true;
    install_unsat_cache_handler(&mut env);

    let mut con_desc = ConceptDescriptor::new();
    con_desc.concept = env.concept_a;
    let con_desc = env.ctx.process_context_mut().alloc_con_desc(con_desc);
    let concept_process_data = env
        .ctx
        .ontology_arenas_mut()
        .alloc_concept_process_data(ConceptProcessData::new());
    env.ctx
        .ontology_arenas_mut()
        .concept_mut(env.concept_a)
        .set_concept_data(concept_process_data.raw);

    let mut label_set = ReapplyConceptLabelSet::new(0);
    label_set.concept_des_linker = con_desc;
    label_set.concept_count = 1;
    let label_set = env.ctx.process_context_mut().alloc_label_set(label_set);
    env.ctx
        .process_context_mut()
        .node_mut(env.root)
        .set_reapply_concept_label_set(label_set);

    let concept_tag = env
        .ctx
        .process_context()
        .con_desc(con_desc)
        .get_concept_tag(env.ctx.ontology_arenas());
    env.ctx
        .process_context_mut()
        .label_set_mut(label_set)
        .concept_des_dep_map
        .insert(
            concept_tag,
            ConceptDescriptorDependencyReapplyData {
                concept_descriptor: con_desc,
                ..Default::default()
            },
        );

    let adapter = env.ctx.base.alloc_classification_message_adapter(
        SatisfiableTaskClassificationMessageAdapter::new(env.concept_a, EFEXTRACTSUBSUMERSROOTNODE),
    );
    let mut task = SatisfiableCalculationTask::new();
    task.set_classification_message_adapter(adapter);
    let task = env.ctx.base.alloc_sat_calc_task(task);

    assert!(!env
        .algo
        .root_unsatisfiability_write_caches(task, &mut env.ctx));

    let mut handler_state = env
        .ctx
        .take_used_unsatisfiable_cache_handler()
        .expect("installed unsat-cache handler must be restored");
    handler_state
        .handler
        .conf_concept_data_unsatisfiable_precheck = false;
    let mut clash = ClashDescId::NONE;
    assert!(handler_state
        .handler
        .is_individual_node_unsatisfiable_cached(
            env.root,
            &mut clash,
            &mut env.ctx,
            &mut handler_state.cache_context,
        ));
    env.ctx
        .restore_used_unsatisfiable_cache_handler(handler_state);
    assert_eq!(
        env.ctx
            .process_context()
            .clash_desc(clash)
            .get_concept_descriptor(),
        con_desc
    );
}

#[test]
fn saturation_node_expansion_handler_queues_unsat_concept_write_data() {
    let mut env = build_env();
    let concept_a = env.concept_a;
    let sat_node = attach_saturation_unsat_reference(&mut env, concept_a, false, false);
    let mut handler = SaturationNodeExpansionCacheHandler::default();

    assert!(handler.cache_unsatisfiable_concept(concept_a, &mut env.ctx));
    assert_eq!(handler.pending_cache_message_count(), 1);
    match &handler.write_data[0] {
        SaturationNodeAssociatedExpansionCacheWriteDataRecord::Unsat(write_data) => {
            assert_eq!(
                write_data.get_unsatisfiable_saturation_individual_node(),
                sat_node
            );
        }
        SaturationNodeAssociatedExpansionCacheWriteDataRecord::Expand(_) => {
            panic!("cacheUnsatisfiableConcept must queue an UNSAT write-data record")
        }
    }
}

#[test]
fn saturation_node_expansion_handler_skips_already_clashed_concept() {
    let mut env = build_env();
    let concept_a = env.concept_a;
    attach_saturation_unsat_reference(&mut env, concept_a, false, true);
    let mut handler = SaturationNodeExpansionCacheHandler::default();

    assert!(!handler.cache_unsatisfiable_concept(concept_a, &mut env.ctx));
    assert!(handler.write_data.is_empty());
}

fn build_saturation_node_expansion_cache_handler(
) -> (CacheContext, SaturationNodeExpansionCacheHandler) {
    let mut cache_context = CacheContext::default();
    let cache =
        cache_context.alloc_sat_expansion_cache(SaturationNodeAssociatedExpansionCache::new());
    let writer = SaturationNodeAssociatedExpansionCacheWriter::new(cache);
    (
        cache_context,
        SaturationNodeExpansionCacheHandler::new(Id::NONE, writer),
    )
}

fn attach_saturation_blocking_data(
    env: &mut SelfTestEnv,
    node: NodeId,
    sat_node: SatNodeId,
    last_confirmed: ConDescId,
    concept_count: i64,
    signature: i64,
) {
    let mut sat_ref_data = ExtendedConceptReferenceLinkingData::new();
    sat_ref_data.init_concept_saturation_testing_item(env.concept_a, false, Id::NONE);
    let sat_ref_data = env
        .ctx
        .process_context_mut()
        .alloc_extended_con_ref_linking_data(sat_ref_data);
    env.ctx
        .process_context_mut()
        .sat_node_mut(sat_node)
        .init_individual_saturation_process_node(INVALID, sat_ref_data, Id::NONE)
        .set_completed(true);
    let mut label_set = ReapplyConceptLabelSet::new(0);
    label_set.concept_count = concept_count;
    label_set.get_concept_signature().signature_value = signature;
    let label_set = env.ctx.process_context_mut().alloc_label_set(label_set);
    env.ctx
        .process_context_mut()
        .node_mut(node)
        .set_reapply_concept_label_set(label_set);

    let mut sat_block_data = IndividualNodeSaturationBlockingData::new();
    sat_block_data.init_saturation_blocking_data(concept_count, last_confirmed, sat_node);
    let sat_block_data = env
        .ctx
        .process_context_mut()
        .alloc_indi_sat_block_data(sat_block_data);
    env.ctx
        .process_context_mut()
        .node_mut(node)
        .set_individual_saturation_blocking_data(sat_block_data);
}

#[test]
fn root_unsatisfiability_write_caches_queues_saturation_unsat_concept() {
    let mut env = build_env();
    env.algo
        .conf_saturation_concept_unsatisfiability_saturated_cache_writing = true;
    let concept_a = env.concept_a;
    let sat_node = attach_saturation_unsat_reference(&mut env, concept_a, false, false);
    env.ctx
        .install_used_saturation_node_expansion_cache_handler(
            SaturationNodeExpansionCacheHandler::default(),
            CacheContext::default(),
        );

    let adapter = env.ctx.base.alloc_classification_message_adapter(
        SatisfiableTaskClassificationMessageAdapter::new(concept_a, EFEXTRACTSUBSUMERSROOTNODE),
    );
    let mut task = SatisfiableCalculationTask::new();
    task.set_classification_message_adapter(adapter);
    let task = env.ctx.base.alloc_sat_calc_task(task);

    assert!(!env
        .algo
        .root_unsatisfiability_write_caches(task, &mut env.ctx));

    let handler_state = env
        .ctx
        .take_used_saturation_node_expansion_cache_handler()
        .expect("installed saturation-node expansion handler must be restored");
    assert_eq!(handler_state.handler.pending_cache_message_count(), 1);
    match &handler_state.handler.write_data[0] {
        SaturationNodeAssociatedExpansionCacheWriteDataRecord::Unsat(write_data) => {
            assert_eq!(
                write_data.get_unsatisfiable_saturation_individual_node(),
                sat_node
            );
        }
        SaturationNodeAssociatedExpansionCacheWriteDataRecord::Expand(_) => {
            panic!("root unsat saturation branch must queue an UNSAT write-data record")
        }
    }
    env.ctx
        .restore_used_saturation_node_expansion_cache_handler(handler_state);
}

#[test]
fn algorithm_commit_cache_messages_installs_queued_saturation_unsat_write_data() {
    let mut env = build_env();
    env.algo
        .conf_saturation_concept_unsatisfiability_saturated_cache_writing = true;
    let concept_a = env.concept_a;
    let sat_node = attach_saturation_unsat_reference(&mut env, concept_a, false, false);
    let (cache_context, handler) = build_saturation_node_expansion_cache_handler();
    env.ctx
        .install_used_saturation_node_expansion_cache_handler(handler, cache_context);

    let adapter = env.ctx.base.alloc_classification_message_adapter(
        SatisfiableTaskClassificationMessageAdapter::new(concept_a, EFEXTRACTSUBSUMERSROOTNODE),
    );
    let mut task = SatisfiableCalculationTask::new();
    task.set_classification_message_adapter(adapter);
    let task = env.ctx.base.alloc_sat_calc_task(task);

    assert!(!env
        .algo
        .root_unsatisfiability_write_caches(task, &mut env.ctx));

    env.algo.commit_cache_messages(&mut env.ctx);

    let node = env.ctx.process_context().sat_node(sat_node);
    assert!(node.direct_status_flags.has_clashed_flag());
    assert!(node.indirect_status_flags.has_clashed_flag());
    let handler_state = env
        .ctx
        .take_used_saturation_node_expansion_cache_handler()
        .expect("installed saturation-node expansion handler must be restored");
    assert!(handler_state.handler.write_data.is_empty());
    env.ctx
        .restore_used_saturation_node_expansion_cache_handler(handler_state);
}

#[test]
fn saturation_node_expansion_handler_commit_installs_unsat_write_data() {
    let mut env = build_env();
    let concept_a = env.concept_a;
    let sat_node = attach_saturation_unsat_reference(&mut env, concept_a, false, false);
    let (mut cache_context, mut handler) = build_saturation_node_expansion_cache_handler();

    assert!(handler.cache_unsatisfiable_concept(concept_a, &mut env.ctx));
    assert!(handler.commit_cache_messages(&mut env.ctx, &mut cache_context));
    assert!(handler.write_data.is_empty());

    let node = env.ctx.process_context().sat_node(sat_node);
    assert!(node.direct_status_flags.has_clashed_flag());
    assert!(node.indirect_status_flags.has_clashed_flag());
    let updater = cache_context
        .sat_expansion_cache(handler.sat_cache_writer.cache)
        .saturation_node_cache_update;
    assert!(updater.is_some());
    assert_eq!(
        cache_context
            .sat_node_cache_updater(updater)
            .direct_updated_status_indi_node_count,
        1
    );
    assert_eq!(
        cache_context
            .sat_node_cache_updater(updater)
            .indirect_updated_status_indi_node_count,
        1
    );
}

#[test]
fn individual_node_saturation_blocking_data_stores_last_confirmed_and_node() {
    let mut env = build_env();
    let sat_node = env
        .ctx
        .process_context_mut()
        .alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));
    let con_desc = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    let mut sat_block_data = IndividualNodeSaturationBlockingData::new();
    sat_block_data.init_saturation_blocking_data(3, con_desc, sat_node);

    assert_eq!(sat_block_data.get_saturation_blocked_concept_count(), 3);
    assert_eq!(
        sat_block_data.get_last_confirmed_concept_descriptior(),
        con_desc
    );
    assert_eq!(sat_block_data.get_saturation_individual_node(), sat_node);
    sat_block_data.set_saturation_blocked_concept_count(4);
    assert_eq!(sat_block_data.get_saturation_blocked_concept_count(), 4);
}

#[test]
fn saturation_node_expansion_handler_cacheability_accepts_completed_uncached_node() {
    let mut env = build_env();
    let sat_node = env
        .ctx
        .process_context_mut()
        .alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));
    let root = env.root;
    attach_saturation_blocking_data(&mut env, root, sat_node, ConDescId::NONE, 2, 101);
    let (cache_context, handler) = build_saturation_node_expansion_cache_handler();

    let data = handler
        .test_node_caching_possible(env.root, &env.ctx, &cache_context)
        .expect("completed saturation node with label set and sat-block data is cacheable");
    assert!(!data.only_if_completely_deterministic);
    assert!(!data.only_all_nondeterministic);
    assert!(data.cache_entry.is_none());
}

#[test]
fn saturation_node_expansion_handler_cacheability_rejects_complete_deterministic_cache_entry() {
    let mut env = build_env();
    let sat_node = env
        .ctx
        .process_context_mut()
        .alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));
    let root = env.root;
    attach_saturation_blocking_data(&mut env, root, sat_node, ConDescId::NONE, 2, 101);
    let (mut cache_context, handler) = build_saturation_node_expansion_cache_handler();
    let cache = handler.sat_cache_writer.cache;
    let entry = cache_context.get_sat_expansion_cache_entry_for_node(
        cache,
        sat_node,
        env.ctx.process_context_mut(),
        true,
    );
    let mut det_expansion =
        AssociatedConceptExpansion::new(AssociatedConceptExpansionKind::Deterministic, INVALID);
    det_expansion.init_deterministic_concept_expansion();
    det_expansion
        .set_non_deterministic_expansion_required(false)
        .set_concept_set_signature(101);
    let det_expansion = cache_context.alloc_associated_concept_expansion(det_expansion);
    cache_context
        .sat_expansion_cache_entry_mut(entry)
        .set_deterministic_concept_expansion(det_expansion);

    assert!(handler
        .test_node_caching_possible(env.root, &env.ctx, &cache_context)
        .is_none());
}

#[test]
fn saturation_node_expansion_handler_cacheability_requires_deterministic_on_matching_signature() {
    let mut env = build_env();
    let sat_node = env
        .ctx
        .process_context_mut()
        .alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));
    let root = env.root;
    attach_saturation_blocking_data(&mut env, root, sat_node, ConDescId::NONE, 2, 202);
    let (mut cache_context, handler) = build_saturation_node_expansion_cache_handler();
    let cache = handler.sat_cache_writer.cache;
    let entry = cache_context.get_sat_expansion_cache_entry_for_node(
        cache,
        sat_node,
        env.ctx.process_context_mut(),
        true,
    );
    let mut det_expansion =
        AssociatedConceptExpansion::new(AssociatedConceptExpansionKind::Deterministic, INVALID);
    det_expansion.init_deterministic_concept_expansion();
    det_expansion
        .set_non_deterministic_expansion_required(true)
        .set_concept_set_signature(202);
    let det_expansion = cache_context.alloc_associated_concept_expansion(det_expansion);
    cache_context
        .sat_expansion_cache_entry_mut(entry)
        .set_deterministic_concept_expansion(det_expansion);

    let data = handler
        .test_node_caching_possible(env.root, &env.ctx, &cache_context)
        .expect("matching det expansion that still requires nondet remains cacheable");
    assert!(data.only_if_completely_deterministic);
    assert_eq!(data.cache_entry, entry);
}

#[test]
fn successor_connected_nominal_set_localizes_and_preserves_parent_set() {
    let mut env = build_env();
    let root = env.root;
    let root_set = env
        .ctx
        .process_context_mut()
        .node_successor_nominal_connection_set(root);
    assert!(env
        .ctx
        .process_context_mut()
        .node_add_successor_connection_to_nominal(root, 7));
    assert!(!env
        .ctx
        .process_context_mut()
        .node_add_successor_connection_to_nominal(root, 7));

    let child = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    {
        let child_ref = env.ctx.process_context_mut().node_mut(child);
        child_ref.use_nominal_connection_set = root_set;
        child_ref.loc_nominal_connection_set = Id::NONE;
    }
    let child_set = env
        .ctx
        .process_context_mut()
        .node_successor_nominal_connection_set(child);
    assert_ne!(child_set, root_set);
    assert!(env
        .ctx
        .process_context()
        .nominal_conn_set(child_set)
        .has_successor_connected_nominal(7));

    assert!(env
        .ctx
        .process_context_mut()
        .node_add_successor_connection_to_nominal(child, 8));
    assert!(!env
        .ctx
        .process_context()
        .nominal_conn_set(root_set)
        .has_successor_connected_nominal(8));
}

#[test]
fn blocking_follow_set_localizes_and_preserves_parent_set() {
    let mut env = build_env();
    let root = env.root;
    let root_set = env
        .ctx
        .process_context_mut()
        .node_blocking_follow_set(root, true);
    assert!(env
        .ctx
        .process_context_mut()
        .node_add_blocking_follower(root, 17));
    assert!(!env
        .ctx
        .process_context_mut()
        .node_add_blocking_follower(root, 17));

    let child = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    {
        let child_ref = env.ctx.process_context_mut().node_mut(child);
        child_ref.prev_sig_block_follow_set = root_set;
        child_ref.use_sig_block_follow_set = root_set;
        child_ref.sig_block_follow_set = Id::NONE;
    }
    let child_set = env
        .ctx
        .process_context_mut()
        .node_blocking_follow_set(child, true);
    assert_ne!(child_set, root_set);
    assert!(env
        .ctx
        .process_context()
        .blocking_follow_set(child_set)
        .contains(17));

    assert!(env
        .ctx
        .process_context_mut()
        .node_add_blocking_follower(child, 18));
    assert!(!env
        .ctx
        .process_context()
        .blocking_follow_set(root_set)
        .contains(18));
}

#[test]
fn nominal_connection_flag_propagation_visits_blocking_followers() {
    let mut env = build_env();
    let root = env.root;
    let follower = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(follower)
        .set_individual_node_id(93);
    env.ctx
        .processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(93, follower);
    env.ctx
        .process_context_mut()
        .node_add_blocking_follower(root, 93);

    env.algo
        .propagate_individual_node_nominal_connection_flags_to_ancestors(
            root,
            IndividualProcessNode::PRF_SUCCESSORNOMINALCONNECTION,
            &mut env.ctx,
        );

    assert!(env
        .ctx
        .process_context()
        .node(follower)
        .has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_SUCCESSORNOMINALCONNECTION,
        ));
}

#[test]
fn nominal_connection_flag_propagation_visits_successor_backward_dependencies() {
    let mut env = build_env();
    let root = env.root;
    let succ = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(succ)
        .set_individual_node_id(95);
    env.ctx
        .process_context_mut()
        .node_mut(root)
        .add_successor_individual_node_backward_dependency_linker(succ);

    let mut edge = IndividualLinkEdge::new();
    edge.init_individual_link_edge(root, root, succ, RoleId::new(95), TrackPointId::NONE);
    let edge = env.ctx.process_context_mut().alloc_edge(edge);
    let mut reapply_it = ReapplyQueueIterator::default();
    env.ctx
        .process_context_mut()
        .node_install_individual_link(root, edge, &mut reapply_it);

    env.algo
        .propagate_individual_node_nominal_connection_flags_to_ancestors(
            root,
            IndividualProcessNode::PRF_SUCCESSORNOMINALCONNECTION,
            &mut env.ctx,
        );

    assert!(env
        .ctx
        .process_context()
        .node(succ)
        .has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_SUCCESSORNOMINALCONNECTION,
        ));
}

#[test]
fn connected_nominal_propagation_visits_blocking_followers() {
    let mut env = build_env();
    let root = env.root;
    let follower = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(follower)
        .set_individual_node_id(94);
    env.ctx
        .processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(94, follower);
    env.ctx
        .process_context_mut()
        .node_add_blocking_follower(root, 94);

    env.algo
        .propagate_individual_node_connected_nominal_to_ancestors(root, -94, &mut env.ctx);

    assert!(env
        .ctx
        .process_context()
        .node_has_successor_connection_to_nominal(follower, -94));
}

#[test]
fn connected_nominal_propagation_visits_successor_backward_dependencies() {
    let mut env = build_env();
    let root = env.root;
    let succ = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(succ)
        .set_individual_node_id(96);
    env.ctx
        .process_context_mut()
        .node_mut(root)
        .add_successor_individual_node_backward_dependency_linker(succ);

    let mut edge = IndividualLinkEdge::new();
    edge.init_individual_link_edge(root, root, succ, RoleId::new(96), TrackPointId::NONE);
    let edge = env.ctx.process_context_mut().alloc_edge(edge);
    let mut reapply_it = ReapplyQueueIterator::default();
    env.ctx
        .process_context_mut()
        .node_install_individual_link(root, edge, &mut reapply_it);

    env.algo
        .propagate_individual_node_connected_nominal_to_ancestors(root, -96, &mut env.ctx);

    assert!(env
        .ctx
        .process_context()
        .node_has_successor_connection_to_nominal(succ, -96));
}

#[test]
fn label_subset_ignore_nominals_direct_lookup_ignores_nominals_and_reports_clash() {
    use super::super::model::op;

    fn concept_with_op(env: &mut SelfTestEnv, tag: i64, op_code: i64) -> ConceptId {
        let mut concept = Concept::new();
        concept.set_concept_tag(tag);
        concept.set_operator_code(op_code);
        env.ctx.ontology_arenas_mut().alloc_concept(concept)
    }

    fn descriptor(env: &mut SelfTestEnv, concept: ConceptId, negated: bool) -> ConDescId {
        let mut con_des = ConceptDescriptor::new();
        con_des.concept = concept;
        con_des.negated = negated;
        env.ctx.process_context_mut().alloc_con_desc(con_des)
    }

    fn label_set(env: &mut SelfTestEnv, descriptors: &[ConDescId]) -> LabelSetId {
        let mut set = ReapplyConceptLabelSet::new(INVALID);
        for &con_des in descriptors {
            set.insert_concept_get_clash_in_context(
                env.ctx.process_context(),
                env.ctx.ontology_arenas(),
                con_des,
                TrackPointId::NONE,
                None,
                None,
                None,
            );
        }
        env.ctx.process_context_mut().alloc_label_set(set)
    }

    let mut env = build_env();
    env.algo.map_comparison_direct_lookup_factor = 1;
    let atom_a = concept_with_op(&mut env, 2110, op::CCATOM);
    let atom_b = concept_with_op(&mut env, 2111, op::CCATOM);
    let atom_c = concept_with_op(&mut env, 2112, op::CCATOM);
    let nominal = concept_with_op(&mut env, 2113, op::CCNOMINAL);

    let atom_a_pos = descriptor(&mut env, atom_a, false);
    let atom_a_neg = descriptor(&mut env, atom_a, true);
    let atom_b_pos = descriptor(&mut env, atom_b, false);
    let atom_c_pos = descriptor(&mut env, atom_c, false);
    let nominal_pos = descriptor(&mut env, nominal, false);

    let sub_with_missing_nominal = label_set(&mut env, &[atom_a_pos, nominal_pos]);
    let super_with_extra_atoms = label_set(&mut env, &[atom_a_pos, atom_b_pos, atom_c_pos]);
    let mut clash = false;
    assert!(env.algo.is_label_concept_sub_set_ignore_nominals(
        sub_with_missing_nominal,
        super_with_extra_atoms,
        Some(&mut clash),
        &mut env.ctx,
    ));
    assert!(!clash);

    let sub_atom = label_set(&mut env, &[atom_a_pos]);
    let super_atom_negated = label_set(&mut env, &[atom_a_neg, atom_b_pos, atom_c_pos]);
    assert!(!env.algo.is_label_concept_sub_set_ignore_nominals(
        sub_atom,
        super_atom_negated,
        Some(&mut clash),
        &mut env.ctx,
    ));
    assert!(clash);
}

#[test]
fn label_subset_ignore_nominals_merge_walk_ignores_nominals_and_rejects_missing_atoms() {
    use super::super::model::op;

    fn concept_with_op(env: &mut SelfTestEnv, tag: i64, op_code: i64) -> ConceptId {
        let mut concept = Concept::new();
        concept.set_concept_tag(tag);
        concept.set_operator_code(op_code);
        env.ctx.ontology_arenas_mut().alloc_concept(concept)
    }

    fn descriptor(env: &mut SelfTestEnv, concept: ConceptId) -> ConDescId {
        let mut con_des = ConceptDescriptor::new();
        con_des.concept = concept;
        env.ctx.process_context_mut().alloc_con_desc(con_des)
    }

    fn label_set(env: &mut SelfTestEnv, descriptors: &[ConDescId]) -> LabelSetId {
        let mut set = ReapplyConceptLabelSet::new(INVALID);
        for &con_des in descriptors {
            set.insert_concept_get_clash_in_context(
                env.ctx.process_context(),
                env.ctx.ontology_arenas(),
                con_des,
                TrackPointId::NONE,
                None,
                None,
                None,
            );
        }
        env.ctx.process_context_mut().alloc_label_set(set)
    }

    let mut env = build_env();
    let atom_a = concept_with_op(&mut env, 2120, op::CCATOM);
    let atom_b = concept_with_op(&mut env, 2121, op::CCATOM);
    let nominal = concept_with_op(&mut env, 2122, op::CCNOMINAL);

    let atom_a_pos = descriptor(&mut env, atom_a);
    let atom_b_pos = descriptor(&mut env, atom_b);
    let nominal_pos = descriptor(&mut env, nominal);

    let super_atom = label_set(&mut env, &[atom_a_pos]);
    let sub_with_missing_nominal = label_set(&mut env, &[atom_a_pos, nominal_pos]);
    let mut clash = false;
    assert!(env.algo.is_label_concept_sub_set_ignore_nominals(
        sub_with_missing_nominal,
        super_atom,
        Some(&mut clash),
        &mut env.ctx,
    ));
    assert!(!clash);

    let sub_with_missing_atom = label_set(&mut env, &[atom_a_pos, atom_b_pos]);
    assert!(!env.algo.is_label_concept_sub_set_ignore_nominals(
        sub_with_missing_atom,
        super_atom,
        Some(&mut clash),
        &mut env.ctx,
    ));
    assert!(!clash);
}

#[test]
fn label_clash_set_direct_lookup_reports_clash_and_subset_miss() {
    use super::super::model::op;

    fn concept_with_op(env: &mut SelfTestEnv, tag: i64, op_code: i64) -> ConceptId {
        let mut concept = Concept::new();
        concept.set_concept_tag(tag);
        concept.set_operator_code(op_code);
        env.ctx.ontology_arenas_mut().alloc_concept(concept)
    }

    fn descriptor(env: &mut SelfTestEnv, concept: ConceptId, negated: bool) -> ConDescId {
        let mut con_des = ConceptDescriptor::new();
        con_des.concept = concept;
        con_des.negated = negated;
        env.ctx.process_context_mut().alloc_con_desc(con_des)
    }

    fn label_set(env: &mut SelfTestEnv, descriptors: &[ConDescId]) -> LabelSetId {
        let mut set = ReapplyConceptLabelSet::new(INVALID);
        for &con_des in descriptors {
            set.insert_concept_get_clash_in_context(
                env.ctx.process_context(),
                env.ctx.ontology_arenas(),
                con_des,
                TrackPointId::NONE,
                None,
                None,
                None,
            );
        }
        env.ctx.process_context_mut().alloc_label_set(set)
    }

    let mut env = build_env();
    env.algo.map_comparison_direct_lookup_factor = 1;
    let atom_a = concept_with_op(&mut env, 2130, op::CCATOM);
    let atom_b = concept_with_op(&mut env, 2131, op::CCATOM);
    let atom_c = concept_with_op(&mut env, 2132, op::CCATOM);
    let atom_d = concept_with_op(&mut env, 2133, op::CCATOM);

    let atom_a_pos = descriptor(&mut env, atom_a, false);
    let atom_a_neg = descriptor(&mut env, atom_a, true);
    let atom_b_pos = descriptor(&mut env, atom_b, false);
    let atom_c_pos = descriptor(&mut env, atom_c, false);
    let atom_d_pos = descriptor(&mut env, atom_d, false);

    let sub_clash = label_set(&mut env, &[atom_a_pos]);
    let super_clash = label_set(&mut env, &[atom_a_neg, atom_b_pos, atom_c_pos]);
    let mut sub_set = true;
    assert!(env.algo.is_label_concept_clash_set_label_sets(
        sub_clash,
        super_clash,
        Some(&mut sub_set),
        false,
        &mut env.ctx,
    ));
    assert!(sub_set);

    let sub_missing = label_set(&mut env, &[atom_d_pos]);
    assert!(!env.algo.is_label_concept_clash_set_label_sets(
        sub_missing,
        super_clash,
        Some(&mut sub_set),
        false,
        &mut env.ctx,
    ));
    assert!(!sub_set);
}

#[test]
fn label_clash_set_merge_walk_ignores_nominal_subset_miss_and_reports_clash() {
    use super::super::model::op;

    fn concept_with_op(env: &mut SelfTestEnv, tag: i64, op_code: i64) -> ConceptId {
        let mut concept = Concept::new();
        concept.set_concept_tag(tag);
        concept.set_operator_code(op_code);
        env.ctx.ontology_arenas_mut().alloc_concept(concept)
    }

    fn descriptor(env: &mut SelfTestEnv, concept: ConceptId, negated: bool) -> ConDescId {
        let mut con_des = ConceptDescriptor::new();
        con_des.concept = concept;
        con_des.negated = negated;
        env.ctx.process_context_mut().alloc_con_desc(con_des)
    }

    fn label_set(env: &mut SelfTestEnv, descriptors: &[ConDescId]) -> LabelSetId {
        let mut set = ReapplyConceptLabelSet::new(INVALID);
        for &con_des in descriptors {
            set.insert_concept_get_clash_in_context(
                env.ctx.process_context(),
                env.ctx.ontology_arenas(),
                con_des,
                TrackPointId::NONE,
                None,
                None,
                None,
            );
        }
        env.ctx.process_context_mut().alloc_label_set(set)
    }

    let mut env = build_env();
    let atom_a = concept_with_op(&mut env, 2140, op::CCATOM);
    let nominal = concept_with_op(&mut env, 2141, op::CCNOMINAL);
    let atom_b = concept_with_op(&mut env, 2142, op::CCATOM);
    let atom_c = concept_with_op(&mut env, 2143, op::CCATOM);

    let atom_a_pos = descriptor(&mut env, atom_a, false);
    let atom_a_neg = descriptor(&mut env, atom_a, true);
    let atom_b_pos = descriptor(&mut env, atom_b, false);
    let atom_c_pos = descriptor(&mut env, atom_c, false);
    let nominal_pos = descriptor(&mut env, nominal, false);

    let super_atom = label_set(&mut env, &[atom_a_pos, atom_b_pos]);
    let sub_missing_nominal = label_set(&mut env, &[atom_a_pos, nominal_pos]);
    let mut sub_set = false;
    assert!(!env.algo.is_label_concept_clash_set_label_sets(
        sub_missing_nominal,
        super_atom,
        Some(&mut sub_set),
        true,
        &mut env.ctx,
    ));
    assert!(sub_set);

    let sub_missing_atom = label_set(&mut env, &[atom_a_pos, atom_c_pos]);
    assert!(!env.algo.is_label_concept_clash_set_label_sets(
        sub_missing_atom,
        super_atom,
        Some(&mut sub_set),
        true,
        &mut env.ctx,
    ));
    assert!(!sub_set);

    let sub_clash = label_set(&mut env, &[atom_a_pos]);
    let super_clash = label_set(&mut env, &[atom_a_neg]);
    assert!(env.algo.is_label_concept_clash_set_label_sets(
        sub_clash,
        super_clash,
        Some(&mut sub_set),
        true,
        &mut env.ctx,
    ));
}

#[test]
fn directly_changed_search_visits_blocking_followers() {
    let mut env = build_env();
    let root = env.root;
    let follower = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(follower)
        .set_individual_node_id(95);
    env.ctx
        .processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(95, follower);
    env.ctx
        .process_context_mut()
        .node_mut(root)
        .add_processing_restriction_flags(IndividualProcessNode::PRF_SUCCESSORNOMINALCONNECTION);
    env.ctx
        .process_context_mut()
        .node_add_blocking_follower(root, 95);
    let inc = env
        .ctx
        .process_context_mut()
        .node_incremental_expansion_data(follower, true);
    env.ctx
        .process_context_mut()
        .inc_exp_data_mut(inc)
        .set_directly_changed(true);

    assert_eq!(
        env.algo
            .search_directly_changed_neighbour_node_connection(root, &mut env.ctx),
        follower
    );
}

#[test]
fn directly_changed_propagation_establishes_connection_on_blocking_follower() {
    let mut env = build_env();
    let root = env.root;
    let follower = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(follower)
        .set_individual_node_id(96);
    env.ctx
        .processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(96, follower);
    env.ctx
        .process_context_mut()
        .node_mut(root)
        .add_processing_restriction_flags(IndividualProcessNode::PRF_SUCCESSORNOMINALCONNECTION);
    env.ctx
        .process_context_mut()
        .node_add_blocking_follower(root, 96);
    let root_inc = env
        .ctx
        .process_context_mut()
        .node_incremental_expansion_data(root, true);
    env.ctx
        .process_context_mut()
        .inc_exp_data_mut(root_inc)
        .set_directly_changed(true);

    assert!(env
        .algo
        .propagate_directly_changed_neighbour_node_connection(root, false, &mut env.ctx));

    let follower_inc = env
        .ctx
        .process_context()
        .node_incremental_expansion_data_existing(follower);
    assert!(follower_inc.is_some());
    assert_eq!(
        env.ctx
            .process_context()
            .inc_exp_data(follower_inc)
            .get_directly_changed_neighbour_connection_node(),
        root
    );
}

#[test]
fn directly_changed_clear_removes_neighbour_connection() {
    let mut env = build_env();
    let root = env.root;
    env.ctx
        .process_context_mut()
        .node_mut(root)
        .set_individual_type(IndividualType::Nominal);
    let neighbour = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(neighbour)
        .set_individual_node_id(97);
    env.ctx
        .processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(97, neighbour);

    let neighbour_inc = env
        .ctx
        .process_context_mut()
        .node_incremental_expansion_data(neighbour, true);
    env.ctx
        .process_context_mut()
        .inc_exp_data_mut(neighbour_inc)
        .set_directly_changed(true);
    assert!(env.algo.establish_directly_changed_neighbour_connection(
        root,
        neighbour,
        false,
        &mut env.ctx,
    ));

    assert!(env
        .algo
        .clear_directly_changed_neighbour_connection(root, true, &mut env.ctx));

    let root_inc = env
        .ctx
        .process_context()
        .node_incremental_expansion_data_existing(root);
    assert_eq!(
        env.ctx
            .process_context()
            .inc_exp_data(root_inc)
            .get_directly_changed_neighbour_connection_node(),
        NodeId::NONE
    );
    assert!(env
        .ctx
        .process_context()
        .node(root)
        .is_incremental_compatibility_checking_queued());
    let queue = env.ctx.get_incremental_compatibility_checking_queue(false);
    assert_eq!(
        env.ctx
            .process_context_mut()
            .indi_depth_queue_take_next(queue),
        root
    );
}

#[test]
fn propagated_directly_changed_clear_drains_registered_nodes() {
    let mut env = build_env();
    let root = env.root;
    let first = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(first)
        .set_individual_node_id(98);
    env.ctx
        .processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(98, first);
    let second = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(second)
        .set_individual_node_id(99);
    env.ctx
        .processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(99, second);

    let root_inc = env
        .ctx
        .process_context_mut()
        .node_incremental_expansion_data(root, true);
    env.ctx
        .process_context_mut()
        .inc_exp_data_mut(root_inc)
        .set_directly_changed(true);
    assert!(env.algo.establish_directly_changed_neighbour_connection(
        first,
        root,
        false,
        &mut env.ctx,
    ));
    assert!(env.algo.establish_directly_changed_neighbour_connection(
        second,
        first,
        false,
        &mut env.ctx,
    ));

    assert!(!env
        .algo
        .clear_propagated_directly_changed_neighbour_connection(root, false, &mut env.ctx));

    for node in [first, second] {
        let inc = env
            .ctx
            .process_context()
            .node_incremental_expansion_data_existing(node);
        assert_eq!(
            env.ctx
                .process_context()
                .inc_exp_data(inc)
                .get_directly_changed_neighbour_connection_node(),
            NodeId::NONE
        );
    }
    assert!(!env
        .ctx
        .process_context()
        .inc_exp_data(root_inc)
        .has_neighbour_propagated_directly_changed());
}

#[test]
fn debug_incremental_expansion_string_reports_live_status() {
    let mut env = build_env();
    let root = env.root;
    let neighbour = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(neighbour)
        .set_individual_node_id(101);
    let inc = env
        .ctx
        .process_context_mut()
        .node_incremental_expansion_data(root, true);
    env.ctx
        .process_context_mut()
        .inc_exp_data_mut(inc)
        .set_previous_completion_graph_compatible(true)
        .set_directly_changed_neighbour_connection_node(neighbour)
        .set_directly_changed(true)
        .set_expansion_priority(7.5);

    assert_eq!(
        env.algo
            .generate_debug_incremental_expansion_string(root, &mut env.ctx),
        "Incremental-Expansion-Status: compatible, directly-changed-connection, directly-changed-node\r\n Directly-Changed-Connection-Neighbour: 101\r\n Expansion-Priority: 7.5"
    );
}

#[test]
fn compatibility_update_rechecks_equal_previous_label_and_clears_propagated() {
    use super::super::model::op;

    fn concept_with_tag(env: &mut SelfTestEnv, tag: i64) -> ConceptId {
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op::CCATOM);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    }

    fn one_concept_label_set(env: &mut SelfTestEnv, concept: ConceptId, tag: i64) -> LabelSetId {
        let con_des = env
            .ctx
            .process_context_mut()
            .alloc_con_desc(ConceptDescriptor::new());
        env.ctx.process_context_mut().con_desc_mut(con_des).concept = concept;
        let mut set = ReapplyConceptLabelSet::new(INVALID);
        set.concept_des_dep_map.insert(
            tag,
            ConceptDescriptorDependencyReapplyData {
                concept_descriptor: con_des,
                pos_neg_reapply_queue: Default::default(),
            },
        );
        set.concept_des_linker = con_des;
        set.concept_count = 1;
        set.concept_signature
            .add_concept_signature(concept, tag, false);
        env.ctx.process_context_mut().alloc_label_set(set)
    }

    let mut env = build_env();
    let root = env.root;
    let prev = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    let propagated = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(propagated)
        .set_individual_node_id(105);
    let concept = concept_with_tag(&mut env, 1005);
    let root_set = one_concept_label_set(&mut env, concept, 1005);
    let prev_set = one_concept_label_set(&mut env, concept, 1005);
    env.ctx
        .process_context_mut()
        .node_mut(root)
        .use_reapply_con_label_set = root_set;
    env.ctx
        .process_context_mut()
        .node_mut(prev)
        .use_reapply_con_label_set = prev_set;

    let root_inc = env
        .ctx
        .process_context_mut()
        .node_incremental_expansion_data(root, true);
    env.ctx
        .process_context_mut()
        .inc_exp_data_mut(root_inc)
        .set_previous_completion_graph_correspondence_individual_node(prev)
        .set_previous_completion_graph_correspondence_individual_node_loaded(true)
        .add_neighbour_propagated_directly_changed(propagated);
    let propagated_inc = env
        .ctx
        .process_context_mut()
        .node_incremental_expansion_data(propagated, true);
    env.ctx
        .process_context_mut()
        .inc_exp_data_mut(propagated_inc)
        .set_directly_changed_neighbour_connection_node(root);

    assert!(env
        .algo
        .check_compatibility_update_directly_changed_propagation(root, &mut env.ctx));
    assert!(env
        .ctx
        .process_context()
        .inc_exp_data(root_inc)
        .is_previous_completion_graph_compatible());
    assert_eq!(
        env.ctx
            .process_context()
            .inc_exp_data(propagated_inc)
            .get_directly_changed_neighbour_connection_node(),
        NodeId::NONE
    );
    assert_eq!(
        env.ctx
            .process_context()
            .inc_exp_data(root_inc)
            .get_last_compatible_checked_concept_descriptor(),
        env.ctx
            .process_context()
            .label_set(root_set)
            .get_adding_sorted_concept_description_linker()
    );
}

#[test]
fn compatibility_update_loads_previous_correspondence_from_previous_task_data() {
    use super::super::model::op;

    fn concept_with_tag(env: &mut SelfTestEnv, tag: i64) -> ConceptId {
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op::CCATOM);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    }

    fn one_concept_label_set(env: &mut SelfTestEnv, concept: ConceptId, tag: i64) -> LabelSetId {
        let con_des = env
            .ctx
            .process_context_mut()
            .alloc_con_desc(ConceptDescriptor::new());
        env.ctx.process_context_mut().con_desc_mut(con_des).concept = concept;
        let mut set = ReapplyConceptLabelSet::new(INVALID);
        set.concept_des_dep_map.insert(
            tag,
            ConceptDescriptorDependencyReapplyData {
                concept_descriptor: con_des,
                pos_neg_reapply_queue: Default::default(),
            },
        );
        set.concept_des_linker = con_des;
        set.concept_count = 1;
        set.concept_signature
            .add_concept_signature(concept, tag, false);
        env.ctx.process_context_mut().alloc_label_set(set)
    }

    let mut env = build_env();
    let root = env.root;
    let prev = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    let concept = concept_with_tag(&mut env, 1010);
    let root_set = one_concept_label_set(&mut env, concept, 1010);
    let prev_set = one_concept_label_set(&mut env, concept, 1010);
    env.ctx
        .process_context_mut()
        .node_mut(root)
        .use_reapply_con_label_set = root_set;
    env.ctx
        .process_context_mut()
        .node_mut(prev)
        .use_reapply_con_label_set = prev_set;

    let mut previous_data_box = super::super::process::databox::ProcessingDataBox::new();
    previous_data_box
        .individual_process_node_vector_mut()
        .set_local_data(
            env.ctx.process_context().node(root).individual_node_id(),
            prev,
        );
    let mut previous_task = SatisfiableCalculationTask::new();
    previous_task.set_processing_data_box_state(previous_data_box);
    let previous_task_id = env.ctx.base.alloc_sat_calc_task(previous_task);
    let previous_task_data = env
        .ctx
        .base
        .alloc_task_data(TaskData::new_consistence(previous_task_id, Id::NONE));
    let mut adapter = SatisfiableTaskIncrementalConsistencyTestingAdapter::new(0, 0, 0, 0);
    adapter.set_previous_consistence_data(previous_task_data);
    let adapter_id = env.ctx.base.alloc_inc_cons_testing_adapter(adapter);
    let mut current_task = SatisfiableCalculationTask::new();
    current_task.set_satisfiable_task_incremental_consistency_testing_adapter(adapter_id);
    let current_task_id = env.ctx.base.alloc_sat_calc_task(current_task);
    env.ctx.base.used_sat_calc_task = current_task_id;

    let root_inc = env
        .ctx
        .process_context_mut()
        .node_incremental_expansion_data(root, true);
    assert!(!env
        .ctx
        .process_context()
        .inc_exp_data(root_inc)
        .is_previous_completion_graph_correspondence_individual_node_loaded());

    assert!(env
        .algo
        .check_compatibility_update_directly_changed_propagation(root, &mut env.ctx));

    let inc = env.ctx.process_context().inc_exp_data(root_inc);
    assert!(inc.is_previous_completion_graph_correspondence_individual_node_loaded());
    assert_eq!(
        inc.get_previous_completion_graph_correspondence_individual_node(),
        prev
    );
    assert!(inc.is_previous_completion_graph_compatible());
}

#[test]
fn initialize_incremental_individual_expansion_collects_missing_previous_nominals() {
    let mut env = build_env();
    let root = env.root;
    let root_id = env.ctx.process_context().node(root).individual_node_id();
    env.ctx
        .process_context_mut()
        .node_mut(root)
        .add_processing_restriction_flags(IndividualProcessNode::PRF_SUCCESSORNOMINALCONNECTION);

    let missing_individual = env
        .ctx
        .ontology_arenas_mut()
        .alloc_individual(Individual::new(31));
    let missing_prev = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(missing_prev)
        .set_individual_node_id(-31)
        .set_individual_type(IndividualType::Nominal)
        .set_nominal_individual(missing_individual);

    let already_present_individual = env
        .ctx
        .ontology_arenas_mut()
        .alloc_individual(Individual::new(32));
    let already_present_prev = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(already_present_prev)
        .set_individual_node_id(-32)
        .set_individual_type(IndividualType::Nominal)
        .set_nominal_individual(already_present_individual);
    let already_present_current = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(already_present_current)
        .set_individual_node_id(-32);
    env.ctx
        .processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(-32, already_present_current);

    let conn_set = env
        .ctx
        .process_context_mut()
        .node_connection_successor_set(root);
    env.ctx
        .process_context_mut()
        .conn_succ_set_mut(conn_set)
        .insert_connection_successor(-31)
        .insert_connection_successor(-32);

    let root_inc = env
        .ctx
        .process_context_mut()
        .node_incremental_expansion_data(root, true);

    let mut previous_data_box = ProcessingDataBox::new();
    previous_data_box
        .individual_process_node_vector_mut()
        .set_local_data(root_id, root)
        .set_local_data(-31, missing_prev)
        .set_local_data(-32, already_present_prev);
    attach_previous_processing_data_box(&mut env, previous_data_box);

    assert!(env
        .algo
        .initialize_incremental_individual_expansion(root, &mut env.ctx));

    let inc = env.ctx.process_context().inc_exp_data(root_inc);
    assert!(inc.is_incremetnal_expansion_list_initialized());
    assert_eq!(
        inc.get_next_incremental_expansion_individual(),
        missing_individual
    );
    assert!(env
        .ctx
        .process_context()
        .node(root)
        .is_incremental_expansion_queued());
}

#[test]
fn are_all_dependent_facts_unchanged_accepts_unchanged_nominal_chain() {
    let mut env = build_env();
    let root = env.root;
    let previous_nominal = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(previous_nominal)
        .set_individual_node_id(-71)
        .set_individual_type(IndividualType::Nominal);

    let concept = atom_concept_with_tag(&mut env, 710);
    let con_des = concept_descriptor_with_dependency(&mut env, concept, false, Id::NONE);
    let base_tp = real_dependency_track_point(
        &mut env,
        Id::NONE,
        con_des,
        DepKind::IndependentBase,
        710,
        0,
    );
    let some_tp = dependency_track_point_with_previous(
        &mut env,
        previous_nominal,
        con_des,
        DepKind::Some,
        711,
        0,
        base_tp,
        &[],
    );

    let mut rem = 15;
    assert!(env.algo.are_all_dependent_facts_unchanged(
        root,
        Id::NONE,
        some_tp,
        INVALID,
        &mut rem,
        &mut env.ctx,
    ));
}

#[test]
fn are_all_dependent_facts_unchanged_rejects_current_graph_association() {
    let mut env = build_env();
    let root = env.root;
    let previous_nominal = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(previous_nominal)
        .set_individual_node_id(-72)
        .set_individual_type(IndividualType::Nominal);
    env.ctx
        .processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(-72, previous_nominal);

    let concept = atom_concept_with_tag(&mut env, 720);
    let con_des = concept_descriptor_with_dependency(&mut env, concept, false, Id::NONE);
    let base_tp = real_dependency_track_point(
        &mut env,
        Id::NONE,
        con_des,
        DepKind::IndependentBase,
        720,
        0,
    );
    let some_tp = dependency_track_point_with_previous(
        &mut env,
        previous_nominal,
        con_des,
        DepKind::Some,
        721,
        0,
        base_tp,
        &[],
    );

    let mut rem = 15;
    assert!(!env.algo.are_all_dependent_facts_unchanged(
        root,
        Id::NONE,
        some_tp,
        INVALID,
        &mut rem,
        &mut env.ctx,
    ));
}

#[test]
fn initialize_incremental_individual_expansion_replays_missing_previous_concept() {
    let mut env = build_env();
    let root = env.root;
    let previous_node = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(previous_node)
        .set_individual_node_id(-73)
        .set_individual_type(IndividualType::Nominal);

    let current_concept = atom_concept_with_tag(&mut env, 800);
    let replay_concept = atom_concept_with_tag(&mut env, 700);
    let current_des =
        concept_descriptor_with_dependency(&mut env, current_concept, false, Id::NONE);
    let current_set = label_set_from_descriptors(&mut env, &[current_des]);
    env.ctx
        .process_context_mut()
        .node_mut(root)
        .use_reapply_con_label_set = current_set;

    let replay_des = concept_descriptor_with_dependency(&mut env, replay_concept, false, Id::NONE);
    let previous_current_des =
        concept_descriptor_with_dependency(&mut env, current_concept, false, Id::NONE);
    let base_tp = real_dependency_track_point(
        &mut env,
        Id::NONE,
        replay_des,
        DepKind::IndependentBase,
        700,
        0,
    );
    let replay_tp = dependency_track_point_with_previous(
        &mut env,
        previous_node,
        replay_des,
        DepKind::Some,
        701,
        0,
        base_tp,
        &[],
    );
    env.ctx
        .process_context_mut()
        .con_desc_mut(replay_des)
        .set_dependency_track_point(replay_tp);
    let previous_set = label_set_from_descriptors(&mut env, &[replay_des, previous_current_des]);
    env.ctx
        .process_context_mut()
        .node_mut(previous_node)
        .use_reapply_con_label_set = previous_set;

    let root_inc = env
        .ctx
        .process_context_mut()
        .node_incremental_expansion_data(root, true);
    env.ctx
        .process_context_mut()
        .inc_exp_data_mut(root_inc)
        .set_previous_completion_graph_correspondence_individual_node(previous_node)
        .set_previous_completion_graph_correspondence_individual_node_loaded(true);

    let mut previous_data_box = ProcessingDataBox::new();
    previous_data_box
        .individual_process_node_vector_mut()
        .set_local_data(
            env.ctx.process_context().node(root).individual_node_id(),
            previous_node,
        );
    attach_previous_processing_data_box(&mut env, previous_data_box);

    assert!(env
        .algo
        .initialize_incremental_individual_expansion(root, &mut env.ctx));

    let mut replayed = ConDescId::NONE;
    let mut dep = TrackPointId::NONE;
    assert!(env
        .ctx
        .process_context()
        .label_set(
            env.ctx
                .process_context()
                .node(root)
                .use_reapply_con_label_set
        )
        .get_concept_descriptor_by_tag(700, &mut replayed, &mut dep));
    assert_eq!(
        env.ctx.process_context().con_desc(replayed).get_concept(),
        replay_concept
    );
    assert_eq!(
        env.ctx
            .process_context()
            .con_desc(replayed)
            .get_dependency_track_point(),
        replay_tp
    );
}

#[test]
fn get_next_incremental_expansion_individual_skips_current_graph_nominals() {
    let mut env = build_env();
    let root = env.root;
    let present_individual = env
        .ctx
        .ontology_arenas_mut()
        .alloc_individual(Individual::new(41));
    let missing_individual = env
        .ctx
        .ontology_arenas_mut()
        .alloc_individual(Individual::new(42));
    let present_node = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(present_node)
        .set_individual_node_id(-41);
    env.ctx
        .processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(-41, present_node);

    let root_inc = env
        .ctx
        .process_context_mut()
        .node_incremental_expansion_data(root, true);
    env.ctx
        .process_context_mut()
        .inc_exp_data_mut(root_inc)
        .get_incremental_expansion_list(true)
        .unwrap()
        .extend([present_individual, missing_individual]);
    env.ctx
        .process_context_mut()
        .inc_exp_data_mut(root_inc)
        .set_incremetnal_expansion_list_initialized(true);

    assert_eq!(
        env.algo
            .get_next_incremental_expansion_individual(root, &mut env.ctx),
        missing_individual
    );
    assert_eq!(
        env.ctx
            .process_context()
            .inc_exp_data(root_inc)
            .get_next_incremental_expansion_individual(),
        Id::NONE
    );
}

#[test]
fn add_individual_to_incremental_expansion_queue_inserts_initializing_queue() {
    let mut env = build_env();
    let root = env.root;

    assert!(env
        .algo
        .add_individual_to_incremental_expansion_queue(root, &mut env.ctx));
    assert!(env
        .ctx
        .process_context()
        .node(root)
        .is_incremental_expansion_queued());
    let queue = env
        .ctx
        .get_incremental_expansion_initializing_processing_queue(false);
    assert_eq!(
        env.ctx
            .process_context_mut()
            .indi_depth_queue_take_next(queue),
        root
    );
}

#[test]
fn individual_custom_priority_processing_queue_orders_and_copies_entries() {
    let mut env = build_env();
    let first = env.root;
    let second = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    let third = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));

    let mut queue = IndividualCustomPriorityProcessingQueue::new();
    queue
        .insert_indiviudal(3.0, first)
        .insert_indiviudal(1.0, second)
        .insert_indiviudal(1.0, third);

    assert_eq!(queue.get_queued_individual_count(), 3);
    assert_eq!(queue.get_next_process_individual(), second);

    let mut copied = IndividualCustomPriorityProcessingQueue::new();
    copied.init_processing_queue(Some(&queue));
    assert_eq!(copied.take_next_process_individual(), second);
    assert_eq!(copied.take_next_process_individual(), third);
    assert_eq!(copied.take_next_process_individual(), first);
    assert!(copied.is_empty());

    assert_eq!(queue.take_next_process_individual(), second);
    assert_eq!(queue.get_queued_individual_count(), 2);
}

fn batch_queue_concept_descriptor(
    env: &mut SelfTestEnv,
    concept_tag: i64,
    priority: f64,
    restricted: bool,
) -> (ConceptId, ConProcDescId) {
    let mut concept = Concept::new();
    concept.set_concept_tag(concept_tag);
    let concept = env.ctx.ontology_arenas_mut().alloc_concept(concept);
    let mut con_des = ConceptDescriptor::new();
    con_des.concept = concept;
    let con_des = env.ctx.process_context_mut().alloc_con_desc(con_des);
    let mut con_pro_des = ConceptProcessDescriptor::new();
    con_pro_des.concept_des = con_des;
    con_pro_des.priority = ConceptProcessPriority::new(priority);
    if restricted {
        con_pro_des.proc_spec = Id::new(7);
    }
    let con_pro_des = env
        .ctx
        .process_context_mut()
        .alloc_con_proc_desc(con_pro_des);
    (concept, con_pro_des)
}

#[test]
fn individual_concept_batch_processing_queue_orders_by_depth_and_id() {
    let mut env = build_env();
    let shallow = env.root;
    env.ctx
        .process_context_mut()
        .node_mut(shallow)
        .set_individual_node_id(5)
        .set_individual_ancestor_depth(1);
    let deep = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(deep)
        .set_individual_node_id(2)
        .set_individual_ancestor_depth(3);
    let lower_id = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(lower_id)
        .set_individual_node_id(1)
        .set_individual_ancestor_depth(1);

    let (concept, shallow_des) = batch_queue_concept_descriptor(&mut env, 9001, 4.0, false);
    let (_, deep_des) = batch_queue_concept_descriptor(&mut env, 9001, 4.0, false);
    let (_, lower_des) = batch_queue_concept_descriptor(&mut env, 9001, 4.0, false);

    let queue = env
        .ctx
        .process_context_mut()
        .alloc_indi_concept_batch_proc_queue(IndividualConceptBatchProcessingQueue::new());
    {
        let base = &mut env.ctx.base;
        base.used_process_context
            .indi_concept_batch_queue_insert_indiviudal_for_concept(
                queue,
                &base.ontology_arenas,
                concept,
                deep,
                deep_des,
            );
        base.used_process_context
            .indi_concept_batch_queue_insert_indiviudal_for_concept(
                queue,
                &base.ontology_arenas,
                concept,
                shallow,
                shallow_des,
            );
        base.used_process_context
            .indi_concept_batch_queue_insert_indiviudal_for_concept(
                queue,
                &base.ontology_arenas,
                concept,
                lower_id,
                lower_des,
            );
    }

    assert_eq!(
        env.ctx
            .take_next_variable_binding_concept_batch_process_individual(queue),
        Some((concept, lower_id, lower_des))
    );
    assert_eq!(
        env.ctx
            .take_next_variable_binding_concept_batch_process_individual(queue),
        Some((concept, shallow, shallow_des))
    );
    assert_eq!(
        env.ctx
            .take_next_variable_binding_concept_batch_process_individual(queue),
        Some((concept, deep, deep_des))
    );
    assert!(env
        .ctx
        .process_context()
        .indi_concept_batch_proc_queue(queue)
        .is_empty());
}

#[test]
fn take_next_process_individual_drains_variable_binding_concept_batch_queue() {
    let mut env = build_env();
    let root = env.root;
    env.ctx
        .process_context_mut()
        .node_mut(root)
        .set_individual_node_id(17)
        .set_individual_ancestor_depth(2);
    let (concept, con_pro_des) = batch_queue_concept_descriptor(&mut env, 9011, 4.0, false);
    let queue = env
        .ctx
        .get_variable_binding_concept_batch_processing_queue(true);
    {
        let base = &mut env.ctx.base;
        base.used_process_context
            .indi_concept_batch_queue_insert_indiviudal_for_concept(
                queue,
                &base.ontology_arenas,
                concept,
                root,
                con_pro_des,
            );
    }

    let next = env.algo.take_next_process_individual(&mut env.ctx);

    assert_eq!(next, root);
    assert_eq!(
        env.algo.indi_node_from_queue_type,
        IndiNodeQueueType::Inqt_VarBindBatchQue
    );
    let con_queue = env
        .ctx
        .process_context_mut()
        .node_concept_processing_queue(root, false);
    assert!(con_queue.is_some());
    assert_eq!(
        ConceptProcessingQueue::take_next_concept_descriptor_process(
            con_queue,
            env.ctx.process_context_mut()
        ),
        con_pro_des
    );
    assert!(env
        .ctx
        .process_context()
        .indi_concept_batch_proc_queue(queue)
        .is_empty());
}

#[test]
fn take_next_process_individual_sorts_nominal_non_deterministic_nodes() {
    let mut env = build_env();
    let high = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(high)
        .set_individual_node_id(30);
    let low = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(low)
        .set_individual_node_id(10);
    let mid = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(mid)
        .set_individual_node_id(20);

    env.ctx
        .processing_data_box_mut()
        .set_sorted_nominal_non_deterministic_processing_node_linker(vec![mid, high, low])
        .set_nominal_non_deterministic_processing_nodes_sorted(false);

    let next = env.algo.take_next_process_individual(&mut env.ctx);

    assert_eq!(next, low);
    assert_eq!(
        env.algo.indi_node_from_queue_type,
        IndiNodeQueueType::Inqt_Nominal
    );
    assert!(env
        .ctx
        .processing_data_box()
        .has_nominal_non_deterministic_processing_nodes_sorted());
    let remaining_ids: Vec<_> = env
        .ctx
        .processing_data_box()
        .sorted_nominal_non_deterministic_processing_node_linker()
        .iter()
        .map(|node| env.ctx.process_context().node(*node).individual_node_id())
        .collect();
    assert_eq!(remaining_ids, vec![20, 30]);
}

#[test]
fn individual_reactivation_processing_queue_orders_copies_and_overwrites_force() {
    let mut env = build_env();
    let shallow = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(shallow)
        .set_individual_node_id(20)
        .set_individual_ancestor_depth(1);
    let early = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(early)
        .set_individual_node_id(7)
        .set_individual_ancestor_depth(0);
    let deep = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(deep)
        .set_individual_node_id(5)
        .set_individual_ancestor_depth(2);

    let queue = env
        .ctx
        .process_context_mut()
        .alloc_indi_reactivation_proc_queue(IndividualReactivationProcessingQueue::new());
    assert!(env
        .ctx
        .process_context_mut()
        .indi_reactivation_queue_insert(queue, shallow, false));
    assert!(env
        .ctx
        .process_context_mut()
        .indi_reactivation_queue_insert(queue, early, true));
    assert!(env
        .ctx
        .process_context_mut()
        .indi_reactivation_queue_insert(queue, deep, false));
    assert!(!env
        .ctx
        .process_context_mut()
        .indi_reactivation_queue_insert(queue, early, false));
    assert_eq!(
        env.ctx
            .process_context()
            .indi_reactivation_proc_queue(queue)
            .get_next_reactivation_individual(),
        Some((early, false))
    );

    let mut copied = IndividualReactivationProcessingQueue::new();
    copied.init_processing_queue(Some(
        env.ctx
            .process_context()
            .indi_reactivation_proc_queue(queue),
    ));
    assert_eq!(
        copied.take_next_reactivation_individual(),
        Some((early, false))
    );
    assert_eq!(
        copied.take_next_reactivation_individual(),
        Some((shallow, false))
    );
    assert_eq!(
        copied.take_next_reactivation_individual(),
        Some((deep, false))
    );
    assert!(copied.is_empty());

    assert_eq!(
        env.ctx
            .process_context_mut()
            .indi_reactivation_proc_queue_mut(queue)
            .take_next_reactivation_individual(),
        Some((early, false))
    );
    assert_eq!(
        env.ctx
            .process_context()
            .indi_reactivation_proc_queue(queue)
            .get_queued_individual_count(),
        2
    );
}

#[test]
fn take_next_process_individual_drains_early_reactivation_queue_with_force() {
    let mut env = build_env();
    let root = env.root;
    env.ctx
        .process_context_mut()
        .node_mut(root)
        .set_individual_node_id(41)
        .set_individual_ancestor_depth(1)
        .add_processing_restriction_flags(IndividualProcessNode::PRF_COMPLETIONGRAPHCACHED);
    let queue = env.ctx.early_individual_reactivation_processing_queue(true);
    assert!(env
        .ctx
        .process_context_mut()
        .indi_reactivation_queue_insert(queue, root, true));

    let next = env.algo.take_next_process_individual(&mut env.ctx);

    assert_eq!(next, root);
    assert_eq!(
        env.algo.indi_node_from_queue_type,
        IndiNodeQueueType::Inqt_CompCachedReact
    );
    assert!(!env
        .ctx
        .process_context()
        .node(root)
        .has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_COMPLETIONGRAPHCACHED,
        ));
    assert!(env
        .ctx
        .process_context()
        .node(root)
        .has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_COMPLETIONGRAPHCACHINGINVALIDATED,
        ));
    assert!(env
        .ctx
        .process_context()
        .indi_reactivation_proc_queue(queue)
        .is_empty());
}

#[test]
fn take_next_process_individual_drains_late_reactivation_queue_without_force() {
    let mut env = build_env();
    let root = env.root;
    env.ctx
        .process_context_mut()
        .node_mut(root)
        .set_individual_node_id(42)
        .set_individual_ancestor_depth(1)
        .add_processing_restriction_flags(IndividualProcessNode::PRF_COMPLETIONGRAPHCACHED);
    let queue = env.ctx.late_individual_reactivation_processing_queue(true);
    assert!(env
        .ctx
        .process_context_mut()
        .indi_reactivation_queue_insert(queue, root, false));

    let next = env.algo.take_next_process_individual(&mut env.ctx);

    assert_eq!(next, root);
    assert_eq!(
        env.algo.indi_node_from_queue_type,
        IndiNodeQueueType::Inqt_CompCachedReact
    );
    assert!(env
        .ctx
        .process_context()
        .node(root)
        .has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_COMPLETIONGRAPHCACHED,
        ));
    assert!(!env
        .ctx
        .process_context()
        .node(root)
        .has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_COMPLETIONGRAPHCACHINGINVALIDATED,
        ));
    assert!(env
        .ctx
        .process_context()
        .indi_reactivation_proc_queue(queue)
        .is_empty());
}

#[test]
fn clear_completion_graph_caching_reapplies_absorbed_cached_concepts() {
    let mut env = build_env();
    let root = env.root;
    let top_concept = env.top_concept;
    let disjunction =
        concept_descriptor_with_dependency(&mut env, top_concept, false, TrackPointId::NONE);
    let generating =
        concept_descriptor_with_dependency(&mut env, top_concept, false, TrackPointId::NONE);
    env.ctx
        .process_context_mut()
        .node_mut(root)
        .add_processing_restriction_flags(IndividualProcessNode::PRF_COMPLETIONGRAPHCACHED);
    env.algo
        .add_satisfiable_cached_absorbed_disjunction_concept(
            disjunction,
            root,
            RestrictionSpecId::NONE,
            TrackPointId::NONE,
            &mut env.ctx,
        );
    env.algo.add_satisfiable_cached_absorbed_generating_concept(
        generating,
        root,
        TrackPointId::NONE,
        &mut env.ctx,
    );

    env.algo.clear_completion_graph_caching(root, &mut env.ctx);

    let node = env.ctx.process_context().node(root);
    assert!(!node.has_partial_processing_restriction_flags(
        IndividualProcessNode::PRF_COMPLETIONGRAPHCACHED
    ));
    assert!(node.has_partial_processing_restriction_flags(
        IndividualProcessNode::PRF_COMPLETIONGRAPHCACHINGINVALIDATED
    ));
    assert!(node
        .satisfiable_cached_absorbed_disjunctions_linker()
        .is_none());
    assert!(node
        .satisfiable_cached_absorbed_generating_linker()
        .is_none());

    let queue = env
        .ctx
        .process_context_mut()
        .node_concept_processing_queue(root, false);
    let queued_a = ConceptProcessingQueue::take_next_concept_descriptor_process(
        queue,
        env.ctx.process_context_mut(),
    );
    let queued_b = ConceptProcessingQueue::take_next_concept_descriptor_process(
        queue,
        env.ctx.process_context_mut(),
    );
    let queued = [
        env.ctx
            .process_context()
            .con_proc_desc(queued_a)
            .get_concept_descriptor(),
        env.ctx
            .process_context()
            .con_proc_desc(queued_b)
            .get_concept_descriptor(),
    ];
    assert!(queued.contains(&disjunction));
    assert!(queued.contains(&generating));
}

#[test]
fn individual_processing_queue_orders_copies_and_resets_hash_priority() {
    let mut env = build_env();
    let slow = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(slow)
        .set_individual_node_id(51);
    let fast = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(fast)
        .set_individual_node_id(52);
    let slow_pri = IndividualProcessNodePriority {
        priority_con: 3.0,
        priority_ind: 5.0,
        strict_order: true,
    };
    let fast_pri = IndividualProcessNodePriority {
        priority_con: 9.0,
        priority_ind: 1.0,
        strict_order: true,
    };
    let slow_desc = env
        .ctx
        .process_context_mut()
        .alloc_indi_proc_node_desc(IndividualProcessNodeDescriptor::new(slow, slow_pri));
    let fast_desc = env
        .ctx
        .process_context_mut()
        .alloc_indi_proc_node_desc(IndividualProcessNodeDescriptor::new(fast, fast_pri));
    let queue = env.ctx.individual_processing_queue(true);
    env.ctx
        .process_context_mut()
        .indi_processing_queue_insert_descriptor(queue, slow_desc);
    env.ctx
        .process_context_mut()
        .indi_processing_queue_insert_descriptor(queue, fast_desc);

    assert!(env
        .ctx
        .process_context_mut()
        .indi_processing_queue_is_individual_queued(queue, fast));
    let copied = env
        .ctx
        .process_context_mut()
        .alloc_individual_processing_queue_from_prev(queue);
    assert_eq!(
        env.ctx
            .process_context_mut()
            .indi_processing_queue_take_next_descriptor(copied),
        fast_desc
    );
    assert_eq!(
        env.ctx
            .process_context_mut()
            .indi_processing_queue_take_next_descriptor(copied),
        slow_desc
    );
    assert!(env.ctx.process_context().indi_proc_queue(copied).is_empty());

    let taken = env
        .ctx
        .process_context_mut()
        .indi_processing_queue_take_next_descriptor(queue);
    assert_eq!(taken, fast_desc);
    assert!(!env
        .ctx
        .process_context_mut()
        .indi_processing_queue_is_individual_queued(queue, fast));
}

#[test]
fn take_next_process_individual_drains_individual_processing_queue() {
    let mut env = build_env();
    let root = env.root;
    env.ctx
        .process_context_mut()
        .node_mut(root)
        .set_individual_node_id(61);
    let priority = IndividualProcessNodePriority {
        priority_con: 4.0,
        priority_ind: 2.0,
        strict_order: true,
    };
    let desc = env
        .ctx
        .process_context_mut()
        .alloc_indi_proc_node_desc(IndividualProcessNodeDescriptor::new(root, priority));
    let queue = env.ctx.individual_processing_queue(true);
    env.ctx
        .process_context_mut()
        .indi_processing_queue_insert_descriptor(queue, desc);
    env.algo.min_concept_processing_priority_level = 17.0;

    let next = env.algo.take_next_process_individual(&mut env.ctx);

    assert_eq!(next, root);
    assert_eq!(
        env.algo.indi_node_from_queue_type,
        IndiNodeQueueType::Inqt_Outdated
    );
    assert_eq!(env.algo.min_concept_processing_priority_level, 0.0);
    assert!(env.ctx.process_context().indi_proc_queue(queue).is_empty());
}

#[test]
fn unit20_blocked_successor_propagation_and_reactivation_iterate_real_successors() {
    use super::super::process::edge::IndividualLinkEdge;
    use super::super::process::rs1::ReapplyQueueIterator;

    let mut env = build_env();
    let root = env.root;
    env.ctx
        .process_context_mut()
        .node_mut(root)
        .set_individual_node_id(70)
        .set_individual_ancestor_depth(0);

    let child = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::default());
    env.ctx
        .process_context_mut()
        .node_mut(child)
        .set_individual_node_id(71)
        .set_individual_ancestor_depth(1);

    let role = {
        let mut role = super::super::model::role::Role::new();
        role.set_role_tag(710);
        env.ctx.ontology_arenas_mut().alloc_role(role)
    };
    let edge = {
        let mut edge = IndividualLinkEdge::new();
        edge.set_source_individual(root)
            .set_destination_individual(child)
            .set_link_role(role);
        env.ctx.process_context_mut().alloc_edge(edge)
    };
    let mut reapply_it = ReapplyQueueIterator::empty();
    env.ctx
        .process_context_mut()
        .node_install_individual_link(root, edge, &mut reapply_it);

    env.algo
        .propagate_adding_blocked_processing_restriction_to_successors(
            root,
            IndividualProcessNode::PRF_INDIRECTBLOCKED,
            false,
            IndividualProcessNode::PRF_INDIRECTBLOCKED,
            &mut env.ctx,
        );
    assert!(env
        .ctx
        .process_context()
        .node(child)
        .has_partial_processing_restriction_flags(IndividualProcessNode::PRF_INDIRECTBLOCKED));

    env.algo
        .reactivate_indirect_blocked_successors(root, false, &mut env.ctx);
    assert!(env
        .ctx
        .process_context()
        .node(child)
        .has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_BLOCKINGRETESTDUEINDIRECTBLOCKERLOSS,
        ));
}

#[test]
fn unit20_add_blocking_core_concept_uses_process_data_and_label_set() {
    let mut env = build_env();
    env.algo.conf_save_core_blocking_concepts_candidates = true;

    let mut con_desc = ConceptDescriptor::new();
    con_desc.concept = env.concept_a;
    con_desc.negated = true;
    let con_desc = env.ctx.process_context_mut().alloc_con_desc(con_desc);

    let label_set = env
        .ctx
        .process_context_mut()
        .alloc_label_set(ReapplyConceptLabelSet::new(0));

    let mut con_proc_data = ConceptProcessData::new();
    con_proc_data.set_core_blocking_concept(true, true);
    let con_proc_data = env
        .ctx
        .ontology_arenas_mut()
        .alloc_concept_process_data(con_proc_data);
    env.ctx
        .ontology_arenas_mut()
        .concept_mut(env.concept_a)
        .set_concept_data(con_proc_data.raw);

    assert!(env
        .algo
        .add_blocking_core_concept(con_desc, env.root, label_set, &mut env.ctx,));
    let core_linker = env
        .ctx
        .process_context()
        .label_set(label_set)
        .get_core_concept_descriptor_linker();
    assert_eq!(
        env.ctx
            .process_context()
            .core_con_desc(core_linker)
            .get_concept_desciptor(),
        con_desc
    );

    let linked_hash = env
        .ctx
        .blocking_individual_node_linked_candidate_hash(false);
    let linked_data =
        BlockingIndividualNodeLinkedCandidateHash::get_blocking_individual_candidate_data_for_concept_descriptor(
            env.ctx.process_context_mut(),
            linked_hash,
            con_desc,
            false,
        );
    assert!(linked_data.is_some());
    assert_eq!(
        env.ctx
            .process_context()
            .blocking_indi_node_linked_cand_data(linked_data)
            .get_candidate_count(),
        1
    );
    let linker = env
        .ctx
        .process_context()
        .blocking_indi_node_linked_cand_data(linked_data)
        .get_blocking_candidates_individual_node_linker();
    assert_eq!(
        env.ctx
            .process_context()
            .blocking_indi_node_linker(linker)
            .get_candidate_individual_node(),
        env.root
    );
}

#[test]
fn unit20_linked_candidate_search_scans_core_descriptor_chain_for_min_bucket() {
    let mut env = build_env();
    let root = env.root;

    let concept_b = {
        let mut c = Concept::new();
        c.set_concept_tag(101);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };

    let mut con_desc_a = ConceptDescriptor::new();
    con_desc_a.concept = env.concept_a;
    let con_desc_a = env.ctx.process_context_mut().alloc_con_desc(con_desc_a);
    let mut con_desc_b = ConceptDescriptor::new();
    con_desc_b.concept = concept_b;
    let con_desc_b = env.ctx.process_context_mut().alloc_con_desc(con_desc_b);

    let label_set = env
        .ctx
        .process_context_mut()
        .alloc_label_set(ReapplyConceptLabelSet::new(0));
    env.ctx
        .process_context_mut()
        .label_set_add_core_concept_descriptor(label_set, con_desc_a);
    let core_b = env
        .ctx
        .process_context_mut()
        .label_set_add_core_concept_descriptor(label_set, con_desc_b);
    env.ctx
        .process_context_mut()
        .node_mut(root)
        .set_reapply_concept_label_set(label_set);

    let linked_hash = env.ctx.blocking_individual_node_linked_candidate_hash(true);
    let data_a =
        BlockingIndividualNodeLinkedCandidateHash::get_blocking_individual_candidate_data_for_concept_descriptor(
            env.ctx.process_context_mut(),
            linked_hash,
            con_desc_a,
            true,
        );
    env.ctx
        .process_context_mut()
        .blocking_indi_node_linked_cand_data_mut(data_a)
        .set_candidate_count(3);
    let data_b =
        BlockingIndividualNodeLinkedCandidateHash::get_blocking_individual_candidate_data_for_concept_descriptor(
            env.ctx.process_context_mut(),
            linked_hash,
            con_desc_b,
            true,
        );
    env.ctx
        .process_context_mut()
        .blocking_indi_node_linked_cand_data_mut(data_b)
        .set_candidate_count(1);

    let blocker = env
        .algo
        .get_anywhere_blocking_individual_node_linked_canidate_hashed(root, Id::NONE, &mut env.ctx);
    assert!(blocker.is_none());

    let block_data = env
        .ctx
        .process_context()
        .node(root)
        .individual_block_data(false);
    assert_eq!(
        env.ctx
            .process_context()
            .blocking_test_data(block_data)
            .get_last_added_core_concept_descriptor(),
        core_b
    );
    assert_eq!(
        env.ctx
            .process_context()
            .blocking_test_data(block_data)
            .get_last_core_blocking_candidate_concept_descriptor(),
        con_desc_b
    );
    assert_eq!(
        env.ctx
            .process_context()
            .blocking_test_data(block_data)
            .get_last_core_blocking_candidate_concept_node_difference(),
        3
    );
}

#[test]
fn signature_blocking_review_set_orders_non_subset_then_subset_and_copies() {
    let mut set = SignatureBlockingReviewSet::new();
    set.get_review_data(true).insert(3, 30).insert(1, 10);
    set.get_review_data(false).insert(2, 20).insert(1, 11);
    set.get_review_data(false).remove(11);

    let mut copied = SignatureBlockingReviewSet::new();
    copied.init_signature_blocking_review_set(Some(&set));

    assert_eq!(set.take_next_review_individual(), Some((20, true)));
    assert_eq!(set.take_next_review_individual(), Some((10, false)));
    assert_eq!(set.take_next_review_individual(), Some((30, false)));
    assert!(set.is_empty());

    assert_eq!(copied.take_next_review_individual(), Some((20, true)));
    assert_eq!(copied.take_next_review_individual(), Some((10, false)));
    assert_eq!(copied.take_next_review_individual(), Some((30, false)));
    assert!(copied.is_empty());
}

#[test]
fn reusing_review_data_preserves_upstream_has_next_and_drains_depth_order() {
    let mut data = ReusingReviewData::new();
    assert!(data.is_empty());
    assert!(data.has_next_individual_id());

    data.insert(3, 30).insert(1, 10).insert(1, 11);
    data.remove(11);

    assert!(!data.is_empty());
    assert!(data.contains(10));
    assert!(!data.contains(11));
    assert!(!data.has_next_individual_id());

    let mut copied = ReusingReviewData::new();
    copied.init_review_data(Some(&data));

    assert_eq!(data.take_next_individual_id(), 10);
    assert_eq!(data.take_next_individual_id(), 30);
    assert!(data.is_empty());
    assert!(data.has_next_individual_id());

    assert_eq!(copied.take_next_individual_id(), 10);
    assert_eq!(copied.take_next_individual_id(), 30);
    assert!(copied.is_empty());
}

#[test]
fn reusing_review_data_getter_allocates_and_copies_previous_data() {
    let mut env = build_env();
    assert!(env.ctx.reusing_review_data(false).is_none());

    let first = env.ctx.reusing_review_data(true);
    env.ctx
        .process_context_mut()
        .reusing_review_data_mut(first)
        .insert(4, 40);
    env.ctx
        .processing_data_box_mut()
        .clear_reusing_review_data()
        .prev_reusing_review_set = first;

    let second = env.ctx.reusing_review_data(true);
    assert_ne!(second, first);
    assert!(env
        .ctx
        .process_context()
        .reusing_review_data(second)
        .contains(40));
}

#[test]
fn reusing_individual_node_concept_expansion_data_copies_base_and_reuse_fields() {
    let mut env = build_env();
    let tp = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(Id::NONE));
    let mut con_desc = ConceptDescriptor::new();
    con_desc.concept = env.concept_a;
    con_desc.negated = false;
    con_desc.dep_track_point = TrackPointId::NONE;
    let desc = env.ctx.process_context_mut().alloc_con_desc(con_desc);

    let mut data = ReusingIndividualNodeConceptExpansionData::new();
    data.set_blocker_individual_node(env.root)
        .set_concept_set_still_subset(false)
        .set_reusing_tried_count(2)
        .inc_reusing_tried_count(3)
        .set_reusing_failed_count(1)
        .inc_reusing_failed_count(4)
        .add_reusing_failed_signature_and_individual(77, 9)
        .set_reuse_concepts_dependency_track_point(tp)
        .set_last_non_deterministic_expansion_linker(vec![desc]);

    let mut copied = ReusingIndividualNodeConceptExpansionData::new();
    copied.init_reusing_expansion_data(Some(&data));

    assert_eq!(copied.get_blocker_individual_node(), env.root);
    assert!(!copied.is_concept_set_still_subset());
    assert_eq!(copied.get_reusing_tried_count(), 5);
    assert_eq!(copied.get_reusing_failed_count(), 5);
    assert_eq!(copied.get_reuse_concepts_dependency_track_point(), tp);
    assert_eq!(
        copied.get_last_non_deterministic_expansion_linker(),
        &[desc]
    );
    assert!(!copied.reused_individuals.contains(&9));
    assert!(!copied.reused_concept_set_signatures.contains(&77));
}

fn unit18_registered_candidate_node(env: &mut SelfTestEnv, indi_id: i64) -> NodeId {
    let node = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(node)
        .set_individual_node_id(indi_id);
    env.ctx
        .processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(indi_id, node);
    node
}

fn unit18_signature_candidates(env: &SelfTestEnv, signature: i64) -> Vec<i64> {
    let hash = env
        .ctx
        .processing_data_box()
        .use_signature_blocking_candidate_hash;
    if hash.is_none() {
        return Vec::new();
    }
    let mut it = env
        .ctx
        .process_context()
        .sig_block_cand_hash(hash)
        .get_blocking_candidates_iterator(signature);
    let mut candidates = Vec::new();
    while it.has_next() {
        candidates.push(it.next(true));
    }
    candidates
}

fn unit18_descriptor_for_concept(
    env: &mut SelfTestEnv,
    concept: ConceptId,
    negated: bool,
    dep: TrackPointId,
) -> ConDescId {
    let con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(con_des);
        d.concept = concept;
        d.negated = negated;
        d.dep_track_point = dep;
    }
    con_des
}

fn unit18_alloc_analyzed_linker(
    env: &mut SelfTestEnv,
    exp_con_des: ConDescId,
    dependencies: Vec<ConDescId>,
) -> super::super::process::analized_concept_expansion::AnalizedConceptExpansionLinkerId {
    let mut linker = AnalizedConceptExpansionLinker::new();
    linker.init_analized_concept_expansion(dependencies, exp_con_des);
    env.ctx
        .process_context_mut()
        .alloc_analized_con_exp_linker(linker)
}

fn unit18_node_label_contains(
    env: &SelfTestEnv,
    node: NodeId,
    concept: ConceptId,
    negated: bool,
) -> bool {
    let label_set = env
        .ctx
        .process_context()
        .node(node)
        .use_reapply_con_label_set;
    label_set.is_some()
        && env
            .ctx
            .process_context()
            .label_set(label_set)
            .contains_concept_in_context(
                env.ctx.process_context(),
                env.ctx.ontology_arenas(),
                concept,
                negated,
            )
}

#[test]
fn unit18_add_reusing_blocker_following_uses_real_blocker_node() {
    let mut env = build_env();
    let blocker = env.root;
    let blocked = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(blocked)
        .set_individual_node_id(41);
    let mut data = ReusingIndividualNodeConceptExpansionData::new();
    data.set_blocker_individual_node(blocker);
    let data_id = env
        .ctx
        .process_context_mut()
        .alloc_reusing_con_exp_data(data);
    env.ctx
        .process_context_mut()
        .node_mut(blocked)
        .set_reusing_individual_node_concept_expansion_data(data_id);

    assert!(env
        .algo
        .add_reusing_blocker_following(blocked, &mut env.ctx));

    assert_eq!(
        env.ctx
            .process_context()
            .node(blocked)
            .following_individual_node(),
        blocker
    );
    assert_eq!(
        env.ctx.process_context().node_blocking_followers(blocker),
        vec![41]
    );
}

#[test]
fn unit18_remove_reusing_blocker_following_uses_real_blocker_node() {
    let mut env = build_env();
    let blocker = env.root;
    let blocked = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(blocked)
        .set_individual_node_id(43);
    let mut data = ReusingIndividualNodeConceptExpansionData::new();
    data.set_blocker_individual_node(blocker);
    let data_id = env
        .ctx
        .process_context_mut()
        .alloc_reusing_con_exp_data(data);
    env.ctx
        .process_context_mut()
        .node_mut(blocked)
        .set_reusing_individual_node_concept_expansion_data(data_id)
        .set_following_individual_node(blocker);
    env.ctx
        .process_context_mut()
        .node_add_blocking_follower(blocker, 43);

    assert!(env
        .algo
        .remove_reusing_blocker_following(blocked, &mut env.ctx));

    assert!(env
        .ctx
        .process_context()
        .node(blocked)
        .following_individual_node()
        .is_none());
    assert!(env
        .ctx
        .process_context()
        .node_blocking_followers(blocker)
        .is_empty());
}

#[test]
fn unit18_rebuild_signature_blocking_candidate_hash_filters_invalid_and_installs_fresh_hash() {
    let mut env = build_env();
    let valid_a = unit18_registered_candidate_node(&mut env, 101);
    let invalid = unit18_registered_candidate_node(&mut env, 102);
    let valid_b = unit18_registered_candidate_node(&mut env, 103);
    env.ctx
        .process_context_mut()
        .node_mut(invalid)
        .add_processing_restriction_flags(
            IndividualProcessNode::PRF_INVALIDATEBLOCKERFLAGSCOMPINATION,
        );

    let old_hash = env.ctx.signature_blocking_candidate_hash(true);
    env.ctx
        .process_context_mut()
        .sig_block_cand_hash_mut(old_hash)
        .insert_signature_blocking_candidates(991, vec![101, 102, 103]);

    env.algo
        .rebuild_signature_blocking_candidate_hash(&mut env.ctx);

    let new_hash = env.ctx.signature_blocking_candidate_hash(false);
    assert_ne!(new_hash, old_hash);
    assert_eq!(
        env.ctx
            .processing_data_box()
            .use_signature_blocking_candidate_hash,
        new_hash
    );
    assert_eq!(unit18_signature_candidates(&env, 991), vec![103, 101]);
    assert_eq!(
        env.ctx
            .process_context()
            .sig_block_cand_hash(new_hash)
            .get_blocking_candidates_count(991),
        2
    );
    assert_eq!(
        env.ctx.process_context().node(valid_a).individual_node_id(),
        101
    );
    assert_eq!(
        env.ctx.process_context().node(valid_b).individual_node_id(),
        103
    );
}

#[test]
fn unit18_rebuild_signature_blocking_candidate_hash_drops_all_invalid_bucket() {
    let mut env = build_env();
    let invalid_a = unit18_registered_candidate_node(&mut env, 111);
    let invalid_b = unit18_registered_candidate_node(&mut env, 112);
    for invalid in [invalid_a, invalid_b] {
        env.ctx
            .process_context_mut()
            .node_mut(invalid)
            .add_processing_restriction_flags(
                IndividualProcessNode::PRF_INVALIDATEBLOCKERFLAGSCOMPINATION,
            );
    }

    let old_hash = env.ctx.signature_blocking_candidate_hash(true);
    env.ctx
        .process_context_mut()
        .sig_block_cand_hash_mut(old_hash)
        .insert_signature_blocking_candidates(992, vec![111, 112]);

    env.algo
        .rebuild_signature_blocking_candidate_hash(&mut env.ctx);

    let new_hash = env.ctx.signature_blocking_candidate_hash(false);
    assert_ne!(new_hash, old_hash);
    assert!(unit18_signature_candidates(&env, 992).is_empty());
    assert_eq!(
        env.ctx
            .process_context()
            .sig_block_cand_hash(new_hash)
            .get_blocking_candidates_count(992),
        0
    );
}

#[test]
fn unit18_test_alternative_blocked_uses_signature_candidate_data() {
    let mut env = build_env();
    env.algo.conf_signature_mirroring_blocking = true;
    let blocking = env.root;
    let blocker = unit18_registered_candidate_node(&mut env, 121);

    let mut blocking_mut = blocking;
    env.algo.add_concept_to_individual(
        env.concept_a,
        false,
        &mut blocking_mut,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );
    let mut blocker_mut = blocker;
    env.algo.add_concept_to_individual(
        env.concept_a,
        false,
        &mut blocker_mut,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );

    let analyzed = env
        .ctx
        .process_context_mut()
        .alloc_analized_con_exp_data(Default::default());
    {
        let blocker_node = env.ctx.process_context_mut().node_mut(blocker);
        blocker_node.sig_block_ind_expl_data = analyzed;
        blocker_node.use_sig_block_ind_expl_data = analyzed;
    }

    let mut alt = BlockingAlternativeSignatureBlockingCandidateData::new();
    alt.init_signature_blocking_candidate_data(blocker, 2, 1, 3);
    let alt_id = env.ctx.process_context_mut().alloc_blocking_alt_data(alt);

    assert!(env
        .algo
        .test_alternative_blocked(blocking, alt_id, &mut env.ctx));

    let sig_data = env
        .ctx
        .process_context()
        .node(blocking)
        .signature_blocking_individual_node_concept_expansion_data(false);
    assert!(env
        .ctx
        .process_context()
        .node(blocking)
        .has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_SIGNATUREBLOCKINGCACHED
        ));
    assert_eq!(
        env.ctx
            .process_context()
            .sig_block_con_exp_data(sig_data)
            .get_blocker_individual_node(),
        blocker
    );
    assert_eq!(
        env.ctx.process_context().node_blocking_followers(blocker),
        vec![0]
    );
}

#[test]
fn unit18_establish_signature_blocking_rejects_invalid_analyzed_blocker() {
    let mut env = build_env();
    let blocking = env.root;
    let blocker = unit18_registered_candidate_node(&mut env, 131);
    let mut data = IndividualNodeAnalizedConceptExpansionData::default();
    data.set_invalid_blocker(true);
    let analyzed = env
        .ctx
        .process_context_mut()
        .alloc_analized_con_exp_data(data);
    {
        let blocker_node = env.ctx.process_context_mut().node_mut(blocker);
        blocker_node.sig_block_ind_expl_data = analyzed;
        blocker_node.use_sig_block_ind_expl_data = analyzed;
    }

    assert!(!env.algo.establish_individual_node_signature_blocking(
        blocking,
        blocker,
        &mut env.ctx
    ));
    assert!(env
        .ctx
        .process_context()
        .node(blocking)
        .is_invalid_signature_blocking());
}

#[test]
fn unit18_update_signature_blocking_expansion_skips_missing_dependency_descriptor() {
    let mut env = build_env();
    env.algo.conf_build_dependencies = true;
    let blocking = env.root;
    let blocker = unit18_registered_candidate_node(&mut env, 141);
    let dep_concept = marker_concept(&mut env, 6141);
    let exp_concept = marker_concept(&mut env, 6142);
    let dep_exp_con_des =
        unit18_descriptor_for_concept(&mut env, dep_concept, false, TrackPointId::NONE);
    let exp_con_des =
        unit18_descriptor_for_concept(&mut env, exp_concept, false, TrackPointId::NONE);
    let linker = unit18_alloc_analyzed_linker(&mut env, exp_con_des, vec![dep_exp_con_des]);
    let mut data = IndividualNodeAnalizedConceptExpansionData::default();
    data.add_analized_concept_expansion_linker(env.ctx.process_context_mut(), linker);
    data.set_last_concept_count(1);
    let analyzed = env
        .ctx
        .process_context_mut()
        .alloc_analized_con_exp_data(data);
    let sig_data = env
        .algo
        .get_or_create_signature_blocking_concept_expansion_data(blocking, &mut env.ctx);

    assert!(env.algo.update_signature_blocking_concept_expansion(
        blocking,
        sig_data,
        blocker,
        analyzed,
        &mut env.ctx,
    ));

    assert!(!unit18_node_label_contains(
        &env,
        blocking,
        exp_concept,
        false
    ));
    assert_eq!(
        env.ctx
            .process_context()
            .sig_block_con_exp_data(sig_data)
            .get_last_updated_concept_expansion_count(),
        1
    );
}

#[test]
fn unit18_update_signature_blocking_expansion_adds_missing_expansion_with_dependencies() {
    let mut env = build_env();
    env.algo.conf_build_dependencies = true;
    let blocking = env.root;
    let blocker = unit18_registered_candidate_node(&mut env, 142);
    let dep = deterministic_track_point(&mut env);
    let dep_concept = marker_concept(&mut env, 6143);
    let exp_concept = marker_concept(&mut env, 6144);

    env.algo.add_concept_to_individual_skip_and_processing(
        dep_concept,
        false,
        blocking,
        dep,
        false,
        true,
        false,
        &mut env.ctx,
    );
    let dep_exp_con_des =
        unit18_descriptor_for_concept(&mut env, dep_concept, false, TrackPointId::NONE);
    let exp_con_des =
        unit18_descriptor_for_concept(&mut env, exp_concept, false, TrackPointId::NONE);
    let linker = unit18_alloc_analyzed_linker(&mut env, exp_con_des, vec![dep_exp_con_des]);
    let mut data = IndividualNodeAnalizedConceptExpansionData::default();
    data.add_analized_concept_expansion_linker(env.ctx.process_context_mut(), linker);
    data.set_last_concept_count(1);
    let analyzed = env
        .ctx
        .process_context_mut()
        .alloc_analized_con_exp_data(data);
    let sig_data = env
        .algo
        .get_or_create_signature_blocking_concept_expansion_data(blocking, &mut env.ctx);

    assert!(env.algo.update_signature_blocking_concept_expansion(
        blocking,
        sig_data,
        blocker,
        analyzed,
        &mut env.ctx,
    ));

    assert!(unit18_node_label_contains(
        &env,
        blocking,
        exp_concept,
        false
    ));
    assert_eq!(
        env.ctx
            .process_context()
            .sig_block_con_exp_data(sig_data)
            .get_last_updated_concept_expansion_count(),
        1
    );
    assert_eq!(
        env.ctx
            .process_context()
            .sig_block_con_exp_data(sig_data)
            .get_last_updated_concept_count(),
        1
    );
}

#[test]
fn unit18_update_signature_blocking_expansion_threads_connection_dependencies() {
    let mut env = build_env();
    env.algo.conf_build_dependencies = true;
    let blocking = env.root;
    let blocker = unit18_registered_candidate_node(&mut env, 143);
    let dep1 = deterministic_track_point(&mut env);
    let dep2 = deterministic_track_point(&mut env);
    let dep_concept1 = marker_concept(&mut env, 6145);
    let dep_concept2 = marker_concept(&mut env, 6146);
    let exp_concept = marker_concept(&mut env, 6147);

    env.algo.add_concept_to_individual_skip_and_processing(
        dep_concept1,
        false,
        blocking,
        dep1,
        false,
        true,
        false,
        &mut env.ctx,
    );
    env.algo.add_concept_to_individual_skip_and_processing(
        dep_concept2,
        false,
        blocking,
        dep2,
        false,
        true,
        false,
        &mut env.ctx,
    );

    let dep_exp_con_des1 =
        unit18_descriptor_for_concept(&mut env, dep_concept1, false, TrackPointId::NONE);
    let dep_exp_con_des2 =
        unit18_descriptor_for_concept(&mut env, dep_concept2, false, TrackPointId::NONE);
    let exp_con_des =
        unit18_descriptor_for_concept(&mut env, exp_concept, false, TrackPointId::NONE);
    let linker = unit18_alloc_analyzed_linker(
        &mut env,
        exp_con_des,
        vec![dep_exp_con_des1, dep_exp_con_des2],
    );
    let mut data = IndividualNodeAnalizedConceptExpansionData::default();
    data.add_analized_concept_expansion_linker(env.ctx.process_context_mut(), linker);
    data.set_last_concept_count(2);
    let analyzed = env
        .ctx
        .process_context_mut()
        .alloc_analized_con_exp_data(data);
    let sig_data = env
        .algo
        .get_or_create_signature_blocking_concept_expansion_data(blocking, &mut env.ctx);

    assert!(env.algo.update_signature_blocking_concept_expansion(
        blocking,
        sig_data,
        blocker,
        analyzed,
        &mut env.ctx,
    ));

    let label_set = env
        .ctx
        .process_context()
        .node(blocking)
        .use_reapply_con_label_set;
    let mut added_con_des = ConDescId::NONE;
    let mut added_dep_track_point = TrackPointId::NONE;
    assert!(env
        .ctx
        .process_context()
        .label_set(label_set)
        .get_concept_descriptor_in_context(
            env.ctx.process_context(),
            env.ctx.ontology_arenas(),
            exp_concept,
            &mut added_con_des,
            &mut added_dep_track_point,
        ));
    assert!(added_con_des.is_some());
    assert!(added_dep_track_point.is_some());

    let expanded_dep = env
        .ctx
        .process_context()
        .track_point(added_dep_track_point)
        .dependency_node();
    let (first_conn_tp, extra_conn_link) = match env.ctx.process_context().dep_node(expanded_dep) {
        DependencyNode::Deterministic { base } => {
            assert_eq!(base.kind, DepKind::Expanded);
            assert_eq!(base.concept_descriptor, ConDescId::NONE);
            (base.dep_track_point, base.additional_after)
        }
        other => panic!("expected expanded deterministic dependency, got {:?}", other),
    };
    assert!(first_conn_tp.is_some());
    assert!(extra_conn_link.is_some());

    let first_conn_dep = env
        .ctx
        .process_context()
        .track_point(first_conn_tp)
        .dependency_node();
    match env.ctx.process_context().dep_node(first_conn_dep) {
        DependencyNode::Deterministic { base } => {
            assert_eq!(base.kind, DepKind::Connection);
            assert_eq!(base.dep_track_point, dep1);
            assert_eq!(
                env.ctx
                    .process_context()
                    .con_desc(base.concept_descriptor)
                    .get_concept(),
                dep_concept1
            );
        }
        other => panic!("expected first connection dependency, got {:?}", other),
    }

    let extra_link = env.ctx.process_context().dep_link(extra_conn_link);
    assert_eq!(extra_link.next, DepLinkId::NONE);
    let second_conn_dep = env
        .ctx
        .process_context()
        .track_point(extra_link.dep_track_point)
        .dependency_node();
    match env.ctx.process_context().dep_node(second_conn_dep) {
        DependencyNode::Deterministic { base } => {
            assert_eq!(base.kind, DepKind::Connection);
            assert_eq!(base.dep_track_point, dep2);
            assert_eq!(
                env.ctx
                    .process_context()
                    .con_desc(base.concept_descriptor)
                    .get_concept(),
                dep_concept2
            );
        }
        other => panic!("expected second connection dependency, got {:?}", other),
    }
}

#[test]
fn backend_neighbour_expansion_controlling_data_copies_modes_counts_and_linkers() {
    let mut env = build_env();
    let tp = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(Id::NONE));
    let root = env.root;

    let mut data = BackendNeighbourExpansionControllingData::new();
    data.inc_expanded_neighbour_link_count(3)
        .set_reuse_modes_dependency_node(Id::NONE)
        .set_reuse_continuing_dependency_track_point(tp)
        .set_fixed_reuse_expansion_mode(true)
        .set_prioritized_reuse_expansion_mode(false)
        .set_last_backend_expanded_ensuring_existing_individual_links_linker(vec![root])
        .add_cut_backend_neighbour_expansion_individual_linker(vec![root])
        .add_cut_backend_neighbour_expansion_individual_linker(vec![NodeId::NONE])
        .set_last_cut_backend_neighbour_expansion_ensuring_existing_individual_links_linker(vec![
            root,
        ]);

    assert!(data.has_expansion_reusing_mode());
    assert_eq!(
        data.get_cut_backend_neighbour_expansion_individual_linker(),
        &[NodeId::NONE, root]
    );

    let mut copied = BackendNeighbourExpansionControllingData::new();
    copied.init_expansion_controlling_data(Some(&data));

    assert_eq!(copied.get_expanded_neighbour_link_count(), 3);
    assert_eq!(copied.get_reuse_continuing_dependency_track_point(), tp);
    assert!(copied.is_fixed_reuse_expansion_mode());
    assert!(!copied.is_prioritized_reuse_expansion_mode());
    assert_eq!(
        copied.get_last_backend_expanded_ensuring_existing_individual_links_linker(),
        &[root]
    );
    assert_eq!(
        copied.get_cut_backend_neighbour_expansion_individual_linker(),
        &[NodeId::NONE, root]
    );
    assert_eq!(
        copied.get_last_cut_backend_neighbour_expansion_ensuring_existing_individual_links_linker(),
        &[root]
    );
}

#[test]
fn backend_neighbour_expansion_controlling_getter_allocates_and_copies() {
    let mut env = build_env();
    assert!(env
        .ctx
        .backend_neighbour_expansion_controlling_data(false)
        .is_none());

    let first = env.ctx.backend_neighbour_expansion_controlling_data(true);
    env.ctx
        .process_context_mut()
        .backend_neighbour_expansion_controlling_data_mut(first)
        .inc_expanded_neighbour_link_count(5)
        .set_prioritized_reuse_expansion_mode(true)
        .set_last_backend_expanded_ensuring_existing_individual_links_linker(vec![env.root]);

    env.ctx
        .processing_data_box_mut()
        .loc_backend_neighbour_expansion_controlling_data = Id::NONE;
    let second = env.ctx.backend_neighbour_expansion_controlling_data(true);

    assert_ne!(second, first);
    let copied = env
        .ctx
        .process_context()
        .backend_neighbour_expansion_controlling_data(second);
    assert_eq!(copied.get_expanded_neighbour_link_count(), 5);
    assert!(copied.is_prioritized_reuse_expansion_mode());
    assert_eq!(
        copied.get_last_backend_expanded_ensuring_existing_individual_links_linker(),
        &[env.root]
    );
}

#[test]
fn prepare_backend_expansion_reuse_branching_creates_modes_dependency_and_prioritized_mode() {
    let mut env = build_env();
    env.algo.conf_build_dependencies = true;

    assert!(env
        .algo
        .prepare_backend_expansion_reuse_branching(&mut env.ctx));

    let exp_cont_data = env.ctx.backend_neighbour_expansion_controlling_data(false);
    assert!(exp_cont_data.is_some());
    let data = env
        .ctx
        .process_context()
        .backend_neighbour_expansion_controlling_data(exp_cont_data);
    let dep_node = data.get_reuse_modes_dependency_node();
    assert!(dep_node.is_some());
    assert!(data.is_prioritized_reuse_expansion_mode());
    assert!(!data.is_fixed_reuse_expansion_mode());
    assert_eq!(
        env.ctx.process_context().dep_node(dep_node).kind(),
        DepKind::ReuseBackendExpansionModes
    );
}

#[test]
fn prepare_backend_expansion_reuse_branching_returns_false_when_modes_dependency_exists() {
    let mut env = build_env();
    env.algo.conf_build_dependencies = true;

    assert!(env
        .algo
        .prepare_backend_expansion_reuse_branching(&mut env.ctx));
    let exp_cont_data = env.ctx.backend_neighbour_expansion_controlling_data(false);
    let first_dep = env
        .ctx
        .process_context()
        .backend_neighbour_expansion_controlling_data(exp_cont_data)
        .get_reuse_modes_dependency_node();

    assert!(!env
        .algo
        .prepare_backend_expansion_reuse_branching(&mut env.ctx));

    let second_dep = env
        .ctx
        .process_context()
        .backend_neighbour_expansion_controlling_data(exp_cont_data)
        .get_reuse_modes_dependency_node();
    assert_eq!(second_dep, first_dep);
}

#[test]
fn prepare_backend_expansion_reuse_branching_without_dependency_building_localizes_modes() {
    let mut env = build_env();
    env.algo.conf_build_dependencies = false;

    assert!(env
        .algo
        .prepare_backend_expansion_reuse_branching(&mut env.ctx));

    let exp_cont_data = env.ctx.backend_neighbour_expansion_controlling_data(false);
    assert!(exp_cont_data.is_some());
    let data = env
        .ctx
        .process_context()
        .backend_neighbour_expansion_controlling_data(exp_cont_data);
    assert!(data.get_reuse_modes_dependency_node().is_none());
    assert!(data.is_prioritized_reuse_expansion_mode());
}

#[test]
fn prepare_backend_individual_fixed_reuse_expansion_without_reuse_modes_dependency_returns_false() {
    let mut env = build_env();
    let mut root = env.root;

    assert!(!env
        .algo
        .prepare_backend_individual_fixed_reuse_expansion(&mut root, &mut env.ctx));
    assert_eq!(root, env.root);
    assert!(!env
        .ctx
        .process_context()
        .node(root)
        .has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_BACKENDEXPANSIONREUSINGINDIVIDUAL
        ));
}

#[test]
fn prepare_backend_individual_fixed_reuse_expansion_marks_reusing_individual() {
    let mut env = build_env();
    let mut root = env.root;
    let mode_tp = real_dependency_track_point(
        &mut env,
        root,
        Id::NONE,
        DepKind::ReuseBackendExpansionModes,
        250,
        250,
    );
    let mode_dep = env
        .ctx
        .process_context()
        .track_point(mode_tp)
        .dependency_node();
    let continuing_tp = deterministic_track_point(&mut env);
    let exp_cont_data = env.ctx.backend_neighbour_expansion_controlling_data(true);
    env.ctx
        .process_context_mut()
        .backend_neighbour_expansion_controlling_data_mut(exp_cont_data)
        .set_reuse_modes_dependency_node(mode_dep)
        .set_reuse_continuing_dependency_track_point(continuing_tp);

    assert!(env
        .algo
        .prepare_backend_individual_fixed_reuse_expansion(&mut root, &mut env.ctx));

    assert_eq!(root, env.root);
    assert!(env
        .ctx
        .process_context()
        .node(root)
        .has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_BACKENDEXPANSIONREUSINGINDIVIDUAL
        ));
}

#[test]
fn prepare_backend_individual_prioritized_reuse_expansion_without_reuse_modes_dependency_returns_false(
) {
    let mut env = build_env();
    let mut root = env.root;

    assert!(!env
        .algo
        .prepare_backend_individual_prioritized_reuse_expansion(&mut root, &mut env.ctx));
    assert_eq!(root, env.root);
    assert!(env
        .ctx
        .get_backend_individual_reuse_expansion_queue(false)
        .is_none());
    assert!(env
        .ctx
        .get_backend_indirect_compatibility_expansion_queue(false)
        .is_none());
}

#[test]
fn prepare_backend_individual_prioritized_reuse_expansion_wires_branch_alternatives() {
    let mut env = build_env();
    env.algo.conf_build_dependencies = true;
    env.algo.conf_build_all_branching_nodes = true;
    let mut root = env.root;
    let mode_tp = real_dependency_track_point(
        &mut env,
        root,
        Id::NONE,
        DepKind::ReuseBackendExpansionModes,
        251,
        251,
    );
    let mode_dep = env
        .ctx
        .process_context()
        .track_point(mode_tp)
        .dependency_node();
    let continuing_tp = deterministic_track_point(&mut env);
    let exp_cont_data = env.ctx.backend_neighbour_expansion_controlling_data(true);
    env.ctx
        .process_context_mut()
        .backend_neighbour_expansion_controlling_data_mut(exp_cont_data)
        .set_reuse_modes_dependency_node(mode_dep)
        .set_reuse_continuing_dependency_track_point(continuing_tp);

    assert!(env
        .algo
        .prepare_backend_individual_prioritized_reuse_expansion(&mut root, &mut env.ctx));

    assert_eq!(root, env.root);
    let node = env.ctx.process_context().node(root);
    assert!(node.has_partial_processing_restriction_flags(
        IndividualProcessNode::PRF_BACKENDEXPANSIONREUSINGINDIVIDUAL
    ));
    assert!(node.has_partial_processing_restriction_flags(
        IndividualProcessNode::PRF_BACKENDEXPANSIONREUSEDISCARDED
    ));

    let sync = node.individual_backend_cache_synchronisation_data(false);
    assert!(sync.is_some());
    assert!(env
        .ctx
        .process_context()
        .backend_sync_data(sync)
        .get_backend_expansion_reuse_dependency_track_point()
        .is_some());

    let reuse_queue = env.ctx.get_backend_individual_reuse_expansion_queue(false);
    assert!(reuse_queue.is_some());
    let queued_reuse = env
        .ctx
        .process_context_mut()
        .indi_unsorted_proc_queue_mut(reuse_queue)
        .take_next_process_individual_node();
    assert_eq!(queued_reuse, root);

    let indirect_queue = env
        .ctx
        .get_backend_indirect_compatibility_expansion_queue(false);
    assert!(indirect_queue.is_some());
    let queued_indirect = env
        .ctx
        .process_context_mut()
        .indi_unsorted_proc_queue_mut(indirect_queue)
        .take_next_process_individual_node();
    assert_eq!(queued_indirect, root);
}

#[test]
fn take_next_process_individual_drains_fixed_backend_reuse_queue() {
    let mut env = build_env();
    env.algo.opt_backend_expansion_reuse = true;
    let root = env.root;
    let exp_cont_data = env.ctx.backend_neighbour_expansion_controlling_data(true);
    env.ctx
        .process_context_mut()
        .backend_neighbour_expansion_controlling_data_mut(exp_cont_data)
        .set_fixed_reuse_expansion_mode(true);
    let q = env.ctx.get_backend_individual_reuse_expansion_queue(true);
    env.ctx
        .process_context_mut()
        .indi_unsorted_proc_queue_mut(q)
        .insert_indiviudal_process_node(root);

    let next = env.algo.take_next_process_individual(&mut env.ctx);

    assert_eq!(next, root);
    assert_eq!(
        env.algo.indi_node_from_queue_type,
        IndiNodeQueueType::Inqt_BackendExpansionReuse
    );
    assert!(env
        .ctx
        .process_context()
        .indi_unsorted_proc_queue(q)
        .is_empty());
}

#[test]
fn take_next_process_individual_drains_prioritized_backend_reuse_queue() {
    let mut env = build_env();
    env.algo.opt_backend_expansion_reuse = true;
    let root = env.root;
    let exp_cont_data = env.ctx.backend_neighbour_expansion_controlling_data(true);
    env.ctx
        .process_context_mut()
        .backend_neighbour_expansion_controlling_data_mut(exp_cont_data)
        .set_prioritized_reuse_expansion_mode(true);
    let q = env.ctx.get_backend_individual_reuse_expansion_queue(true);
    env.ctx
        .process_context_mut()
        .indi_unsorted_proc_queue_mut(q)
        .insert_indiviudal_process_node(root);

    let next = env.algo.take_next_process_individual(&mut env.ctx);

    assert_eq!(next, root);
    assert_eq!(
        env.algo.indi_node_from_queue_type,
        IndiNodeQueueType::Inqt_BackendExpansionReuse
    );
    assert!(env
        .ctx
        .process_context()
        .indi_unsorted_proc_queue(q)
        .is_empty());
}

#[test]
fn add_individual_to_backend_reuse_expansion_queue_sets_flag_and_inserts_once() {
    let mut env = build_env();
    let root = env.root;

    assert!(env
        .algo
        .add_individual_to_backend_reuse_expansion_queue(root, &mut env.ctx));
    assert!(env
        .ctx
        .process_context()
        .node(root)
        .is_backend_reuse_expansion_queued());
    let q = env.ctx.get_backend_individual_reuse_expansion_queue(false);
    assert!(q.is_some());
    assert!(!env
        .ctx
        .process_context()
        .indi_unsorted_proc_queue(q)
        .is_empty());

    assert!(!env
        .algo
        .add_individual_to_backend_reuse_expansion_queue(root, &mut env.ctx));

    let queued = env
        .ctx
        .process_context_mut()
        .indi_unsorted_proc_queue_mut(q)
        .take_next_process_individual_node();
    assert_eq!(queued, root);
    assert!(env
        .ctx
        .process_context()
        .indi_unsorted_proc_queue(q)
        .is_empty());
}

#[test]
fn add_individual_to_backend_indirect_compatibility_expansion_queue_sets_flag_and_inserts_once() {
    let mut env = build_env();
    let root = env.root;

    assert!(env
        .algo
        .add_individual_to_backend_indirect_compatibility_expansion_queue(root, &mut env.ctx));
    assert!(env
        .ctx
        .process_context()
        .node(root)
        .is_backend_indirect_compatibility_expansion_queued());
    let q = env
        .ctx
        .get_backend_indirect_compatibility_expansion_queue(false);
    assert!(q.is_some());
    assert!(!env
        .ctx
        .process_context()
        .indi_unsorted_proc_queue(q)
        .is_empty());

    assert!(!env
        .algo
        .add_individual_to_backend_indirect_compatibility_expansion_queue(root, &mut env.ctx));

    let queued = env
        .ctx
        .process_context_mut()
        .indi_unsorted_proc_queue_mut(q)
        .take_next_process_individual_node();
    assert_eq!(queued, root);
    assert!(env
        .ctx
        .process_context()
        .indi_unsorted_proc_queue(q)
        .is_empty());
}

#[test]
fn add_individual_to_backend_synchronisation_retest_queue_sets_flag_and_inserts_once() {
    let mut env = build_env();
    let root = env.root;

    assert!(env
        .algo
        .add_individual_to_backend_synchronisation_retest_queue(root, &mut env.ctx));
    assert!(env
        .ctx
        .process_context()
        .node(root)
        .is_backend_synchron_retest_processing_queued());
    let q = env
        .ctx
        .get_backend_cache_synchronization_processing_queue(false);
    assert!(q.is_some());
    assert!(!env
        .ctx
        .process_context()
        .indi_unsorted_proc_queue(q)
        .is_empty());

    assert!(!env
        .algo
        .add_individual_to_backend_synchronisation_retest_queue(root, &mut env.ctx));

    let queued = env
        .ctx
        .process_context_mut()
        .indi_unsorted_proc_queue_mut(q)
        .take_next_process_individual_node();
    assert_eq!(queued, root);
    assert!(env
        .ctx
        .process_context()
        .indi_unsorted_proc_queue(q)
        .is_empty());
}

fn seed_backend_sync_data(
    env: &mut SelfTestEnv,
    node: NodeId,
) -> super::super::process::stubs::BackendSyncDataId {
    let mut data = IndividualNodeBackendCacheSynchronisationData::new();
    data.set_associtaion_data(Id::new(0));
    let sync = env.ctx.process_context_mut().alloc_backend_sync_data(data);
    env.ctx
        .process_context_mut()
        .node_mut(node)
        .set_individual_backend_cache_synchronisation_data(sync);
    sync
}

#[test]
fn unit17_visit_relevant_backend_sync_individuals_visits_base_and_merged_nodes() {
    let mut env = build_env();
    let root = env.root;
    let merged = test_node_at_depth(&mut env, 54, 1);
    let root_sync = seed_backend_sync_data(&mut env, root);
    let _merged_sync = seed_backend_sync_data(&mut env, merged);
    env.ctx
        .process_context_mut()
        .backend_sync_data_mut(root_sync)
        .merged_individual_node_linker = vec![merged];

    let mut visited = Vec::new();
    assert!(env
        .algo
        .visit_individuals_relevant_backend_synchronisation_data_individuals(
            root,
            false,
            &mut |base, node, _tp| {
                visited.push((base, node));
                true
            },
            &mut env.ctx,
        ));

    assert_eq!(visited, vec![(root, root), (root, merged)]);
}

#[test]
fn unit17_visit_relevant_backend_sync_individuals_honours_visitor_stop() {
    let mut env = build_env();
    let root = env.root;
    let merged = test_node_at_depth(&mut env, 55, 1);
    let root_sync = seed_backend_sync_data(&mut env, root);
    let _merged_sync = seed_backend_sync_data(&mut env, merged);
    env.ctx
        .process_context_mut()
        .backend_sync_data_mut(root_sync)
        .merged_individual_node_linker = vec![merged];

    let mut visited = Vec::new();
    assert!(env
        .algo
        .visit_individuals_relevant_backend_synchronisation_data_individuals(
            root,
            false,
            &mut |base, node, _tp| {
                visited.push((base, node));
                false
            },
            &mut env.ctx,
        ));

    assert_eq!(visited, vec![(root, root)]);
}

#[test]
fn unit20_blocking_candidate_iterator_uses_descriptor_concept_tag() {
    let mut env = build_env();
    env.algo.conf_anywhere_blocking_lazy_exact_hashing = true;

    let init_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(7777);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let mut init_desc = ConceptDescriptor::new();
    init_desc.concept = init_concept;
    let init_desc = env.ctx.process_context_mut().alloc_con_desc(init_desc);
    assert_ne!(
        init_desc.raw,
        env.ctx
            .ontology_arenas()
            .concept(init_concept)
            .get_concept_tag()
    );

    let candidate = env.ctx.process_context_mut().alloc_node({
        let mut node = IndividualProcessNode::new(Id::NONE);
        node.set_individual_node_id(1);
        node
    });
    let testing = env.ctx.process_context_mut().alloc_node({
        let mut node = IndividualProcessNode::new(Id::NONE);
        node.set_individual_node_id(2);
        node.set_individual_initialization_concept(init_desc);
        node
    });
    env.ctx
        .processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(1, candidate)
        .set_local_data(2, testing);

    let mut label_set_obj = ReapplyConceptLabelSet::new(0);
    label_set_obj.insert_concept_get_clash_in_context(
        env.ctx.process_context(),
        env.ctx.ontology_arenas(),
        init_desc,
        TrackPointId::NONE,
        None,
        None,
        None,
    );
    let label_set = env.ctx.process_context_mut().alloc_label_set(label_set_obj);
    assert!(env
        .ctx
        .process_context()
        .label_set(label_set)
        .contains_concept_descriptor_in_context(
            env.ctx.process_context(),
            env.ctx.ontology_arenas(),
            init_desc,
        ));
    env.ctx
        .process_context_mut()
        .node_mut(candidate)
        .set_reapply_concept_label_set(label_set);

    let mut iterator = env
        .algo
        .get_blocking_individual_node_candidate_iterator(testing, &mut env.ctx);
    let hash = env.ctx.blocking_individual_node_candidate_hash(false);
    let data =
        BlockingIndividualNodeCandidateHash::get_blocking_individual_candidate_data_for_concept_descriptor(
            env.ctx.process_context_mut(),
            hash,
            init_desc,
            false,
        );
    assert!(env
        .ctx
        .process_context()
        .blocking_indi_node_cand_data(data)
        .get_blocking_candidates_individual_node_iterator(2)
        .has_individual_candidate(1));
    assert_eq!(iterator.next_individual_candidate(true), Some(candidate));
}

#[test]
fn unit20_backend_cardinality_criticality_reads_sync_gate_and_cursor_snapshot() {
    let mut env = build_env();
    let root = env.root;
    let merged = test_node_at_depth(&mut env, 51, 1);
    let sync = seed_backend_sync_data(&mut env, root);
    env.ctx
        .process_context_mut()
        .backend_sync_data_mut(sync)
        .merged_individual_node_linker = vec![merged];

    assert!(!env
        .algo
        .test_individual_node_backend_cache_expansion_blocking_critical_cardinality(
            root,
            &mut env.ctx,
        ));

    let sync_data = env.ctx.process_context().backend_sync_data(sync);
    assert_eq!(
        sync_data.get_last_critical_neighbours_tested_merged_node_linker(),
        &[merged]
    );

    env.ctx
        .process_context_mut()
        .backend_sync_data_mut(sync)
        .set_critical_cardinality_expansion_blocking(true);
    assert!(env
        .algo
        .test_individual_node_backend_cache_expansion_blocking_critical_cardinality(
            root,
            &mut env.ctx,
        ));
}

#[test]
fn unit20_backend_neighbour_criticality_reads_and_writes_sync_state() {
    let mut env = build_env();
    let root = env.root;
    let merged = test_node_at_depth(&mut env, 52, 1);
    let sync = seed_backend_sync_data(&mut env, root);
    env.ctx
        .process_context_mut()
        .backend_sync_data_mut(sync)
        .merged_individual_node_linker = vec![merged];

    assert!(env
        .algo
        .test_individual_node_backend_cache_neighbour_expansion_blocking_critical(
            root,
            &mut env.ctx,
        ));

    let sync_data = env.ctx.process_context().backend_sync_data(sync);
    assert_eq!(
        sync_data.get_last_critical_neighbours_tested_merged_node_linker(),
        &[merged]
    );
    assert!(sync_data.is_critical_neighbour_expansion_blocking());

    env.ctx
        .process_context_mut()
        .backend_sync_data_mut(sync)
        .set_critical_neighbour_expansion_blocking(false)
        .merged_individual_node_linker
        .clear();
    assert!(!env
        .algo
        .test_individual_node_backend_cache_neighbour_expansion_blocking_critical(
            root,
            &mut env.ctx,
        ));
}

#[test]
fn unit20_backend_neighbour_criticality_walks_label_chain_and_advances_cursor() {
    use super::super::model::op;

    let mut env = build_env();
    let root = env.root;
    let role = {
        let mut role = super::super::model::role::Role::new();
        role.set_role_tag(6204);
        env.ctx.ontology_arenas_mut().alloc_role(role)
    };
    let critical_concept = {
        let mut concept = Concept::new();
        concept.set_concept_tag(6205);
        concept.set_operator_code(op::CCSOME);
        concept.set_role(role);
        env.ctx.ontology_arenas_mut().alloc_concept(concept)
    };
    let tail_concept = atom_concept_with_tag(&mut env, 6206);

    let mut tail_desc = ConceptDescriptor::new();
    tail_desc.concept = tail_concept;
    let tail_desc = env.ctx.process_context_mut().alloc_con_desc(tail_desc);

    let mut critical_desc = ConceptDescriptor::new();
    critical_desc.concept = critical_concept;
    critical_desc.negated = true;
    critical_desc.set_next(tail_desc);
    let critical_desc = env.ctx.process_context_mut().alloc_con_desc(critical_desc);

    let mut label_set = ReapplyConceptLabelSet::new(INVALID);
    label_set.concept_des_linker = critical_desc;
    label_set.concept_count = 2;
    let label_set = env.ctx.process_context_mut().alloc_label_set(label_set);
    env.ctx
        .process_context_mut()
        .node_mut(root)
        .set_reapply_concept_label_set(label_set);

    let sync = seed_backend_sync_data(&mut env, root);
    env.ctx
        .process_context_mut()
        .backend_sync_data_mut(sync)
        .set_backend_cache_synchron(false);

    assert!(env
        .algo
        .test_individual_node_backend_cache_neighbour_expansion_blocking_critical(
            root,
            &mut env.ctx,
        ));

    let sync_data = env.ctx.process_context().backend_sync_data(sync);
    assert!(sync_data.is_critical_neighbour_expansion_blocking());
    assert_eq!(
        sync_data.get_last_critical_neighbour_expansion_tested_concept_descriptor(),
        tail_desc
    );
}

#[test]
fn unit25_validate_backend_synchronisation_continued_updates_live_sync_cursors() {
    let mut env = build_env();
    let root = env.root;
    let concept = atom_concept_with_tag(&mut env, 6201);
    let mut con_desc = ConceptDescriptor::new();
    con_desc.concept = concept;
    let con_desc = env.ctx.process_context_mut().alloc_con_desc(con_desc);
    let mut label_set = ReapplyConceptLabelSet::new(INVALID);
    label_set.concept_des_linker = con_desc;
    let label_set = env.ctx.process_context_mut().alloc_label_set(label_set);
    env.ctx
        .process_context_mut()
        .node_mut(root)
        .set_reapply_concept_label_set(label_set);

    let sync = seed_backend_sync_data(&mut env, root);
    env.ctx
        .process_context_mut()
        .backend_sync_data_mut(sync)
        .set_backend_cache_synchron(true);

    assert!(env.algo.validate_backend_synchronisation_continued(
        root,
        sync,
        ConceptId::NONE,
        false,
        &mut env.ctx,
    ));

    let sync_data = env.ctx.process_context().backend_sync_data(sync);
    assert!(sync_data.is_backend_cache_synchron());
    assert_eq!(
        sync_data.get_last_synchronization_tested_concept_descriptor(),
        con_desc
    );
    assert_eq!(sync_data.get_last_synched_concept_descriptor(), con_desc);
}

#[test]
fn unit25_validate_backend_synchronisation_continued_clears_unsynced_state_on_missing_inputs() {
    let mut env = build_env();
    let root = env.root;
    let sync = seed_backend_sync_data(&mut env, root);
    env.ctx
        .process_context_mut()
        .backend_sync_data_mut(sync)
        .set_backend_cache_synchron(true)
        .set_associtaion_data(Id::NONE);

    assert!(!env.algo.validate_backend_synchronisation_continued(
        root,
        sync,
        ConceptId::NONE,
        false,
        &mut env.ctx,
    ));
    assert!(!env
        .ctx
        .process_context()
        .backend_sync_data(sync)
        .is_backend_cache_synchron());

    let absent_sync = super::super::process::stubs::BackendSyncDataId::NONE;
    assert!(!env.algo.validate_backend_synchronisation_continued(
        root,
        absent_sync,
        ConceptId::NONE,
        false,
        &mut env.ctx,
    ));
}

#[test]
fn unit25_backend_cache_concepts_synchronization_updates_live_sync_cursors() {
    let mut env = build_env();
    let root = env.root;
    let merged = test_node_at_depth(&mut env, 53, 1);
    let concept = atom_concept_with_tag(&mut env, 6202);
    let mut con_desc = ConceptDescriptor::new();
    con_desc.concept = concept;
    let con_desc = env.ctx.process_context_mut().alloc_con_desc(con_desc);
    let mut label_set = ReapplyConceptLabelSet::new(INVALID);
    label_set.concept_des_linker = con_desc;
    let label_set = env.ctx.process_context_mut().alloc_label_set(label_set);
    env.ctx
        .process_context_mut()
        .node_mut(root)
        .set_reapply_concept_label_set(label_set);

    let sync = seed_backend_sync_data(&mut env, root);
    env.ctx
        .process_context_mut()
        .backend_sync_data_mut(sync)
        .set_backend_cache_synchron(true)
        .merged_individual_node_linker = vec![merged];

    assert!(env
        .algo
        .test_individual_node_backend_cache_concepts_synchronization(root, &mut env.ctx));

    let sync_data = env.ctx.process_context().backend_sync_data(sync);
    assert!(sync_data.is_backend_cache_synchron());
    assert_eq!(
        sync_data.get_last_synchronized_concepts_tested_merged_node_linker(),
        &[merged]
    );
    assert_eq!(
        sync_data.get_last_synchronization_tested_concept_descriptor(),
        con_desc
    );
    assert_eq!(sync_data.get_last_synched_concept_descriptor(), con_desc);
}

#[test]
fn unit25_backend_cache_concepts_synchronization_clears_unsynced_state_on_missing_assoc() {
    let mut env = build_env();
    let root = env.root;
    let sync = seed_backend_sync_data(&mut env, root);
    env.ctx
        .process_context_mut()
        .backend_sync_data_mut(sync)
        .set_backend_cache_synchron(true)
        .set_associtaion_data(Id::NONE);

    assert!(!env
        .algo
        .test_individual_node_backend_cache_concepts_synchronization(root, &mut env.ctx));
    assert!(!env
        .ctx
        .process_context()
        .backend_sync_data(sync)
        .is_backend_cache_synchron());
}

#[test]
fn add_individual_to_backend_direct_influence_expansion_queue_sets_flag_and_inserts_once() {
    let mut env = build_env();
    let root = env.root;

    assert!(env
        .algo
        .add_individual_to_backend_direct_influence_expansion_queue(root, &mut env.ctx));
    assert!(env
        .ctx
        .process_context()
        .node(root)
        .is_backend_direct_influence_expansion_queued());
    let q = env.ctx.get_backend_direct_influence_expansion_queue(false);
    assert!(q.is_some());
    assert!(!env
        .ctx
        .process_context()
        .indi_unsorted_proc_queue(q)
        .is_empty());

    assert!(!env
        .algo
        .add_individual_to_backend_direct_influence_expansion_queue(root, &mut env.ctx));

    let queued = env
        .ctx
        .process_context_mut()
        .indi_unsorted_proc_queue_mut(q)
        .take_next_process_individual_node();
    assert_eq!(queued, root);
    assert!(env
        .ctx
        .process_context()
        .indi_unsorted_proc_queue(q)
        .is_empty());
}

#[test]
fn add_individual_to_backend_neighbour_expansion_queue_sets_flag_and_inserts_once() {
    let mut env = build_env();
    let root = env.root;

    assert!(env
        .algo
        .add_individual_to_backend_neighbour_expansion_queue(root, &mut env.ctx));
    assert!(env
        .ctx
        .process_context()
        .node(root)
        .is_backend_neighbour_expansion_queued());
    let q = env
        .ctx
        .get_backend_individual_neighbour_expansion_queue(false);
    assert!(q.is_some());
    assert!(!env
        .ctx
        .process_context()
        .indi_rotation_proc_queue(q)
        .is_empty());

    assert!(!env
        .algo
        .add_individual_to_backend_neighbour_expansion_queue(root, &mut env.ctx));

    let queued = env
        .ctx
        .process_context_mut()
        .indi_rotation_proc_queue_mut(q)
        .take_next_process_individual_node();
    assert_eq!(queued, root);
    assert!(env
        .ctx
        .process_context()
        .indi_rotation_proc_queue(q)
        .is_empty());
}

#[test]
fn add_individual_to_blocking_update_review_processing_queue_inserts_depth_queue() {
    let mut env = build_env();
    let root = env.root;
    env.ctx
        .process_context_mut()
        .node_mut(root)
        .set_individual_ancestor_depth(3);

    assert!(env
        .algo
        .add_individual_to_blocking_update_review_processing_queue(root, &mut env.ctx));
    let q = env.ctx.get_blocking_update_review_processing_queue(false);
    assert!(q.is_some());
    assert!(!env
        .ctx
        .process_context()
        .indi_depth_proc_queue(q)
        .is_empty());

    let queued = env.ctx.process_context_mut().indi_depth_queue_take_next(q);
    assert_eq!(queued, root);
    assert!(env
        .ctx
        .process_context()
        .indi_depth_proc_queue(q)
        .is_empty());
}

#[test]
fn get_applied_and_rule_count_returns_counter_field() {
    let mut env = build_env();
    env.algo.applied_and_rule_count = 17;

    assert_eq!(env.algo.get_applied_and_rule_count(), 17);
    assert_eq!(
        env.algo.get_applied_and_rule_count(),
        env.algo.applied_and_rule_count()
    );
}

#[test]
fn rule_count_getters_return_counter_fields() {
    let mut env = build_env();
    env.algo.applied_and_rule_count = 11;
    env.algo.applied_or_rule_count = 12;
    env.algo.applied_some_rule_count = 13;
    env.algo.applied_atleast_rule_count = 14;
    env.algo.applied_all_rule_count = 15;
    env.algo.applied_atmost_rule_count = 16;
    env.algo.applied_total_rule_count = 17;

    assert_eq!(env.algo.get_applied_and_rule_count(), 11);
    assert_eq!(env.algo.get_applied_or_rule_count(), 12);
    assert_eq!(env.algo.get_applied_some_rule_count(), 13);
    assert_eq!(env.algo.get_applied_atleast_rule_count(), 14);
    assert_eq!(env.algo.get_applied_all_rule_count(), 15);
    assert_eq!(env.algo.get_applied_atmost_rule_count(), 16);
    assert_eq!(env.algo.get_applied_total_rule_count(), 17);
}

#[test]
fn take_next_process_individual_preserves_reusing_review_upstream_has_next_gate() {
    let mut env = build_env();
    let q = env.ctx.reusing_review_data(true);
    env.ctx
        .process_context_mut()
        .reusing_review_data_mut(q)
        .insert(1, 0);

    let next = env.algo.take_next_process_individual(&mut env.ctx);

    assert!(next.is_none());
    assert!(env.ctx.process_context().reusing_review_data(q).contains(0));
}

#[test]
fn take_next_process_individual_drains_signature_blocking_review_set() {
    let mut env = build_env();
    let root = env.root;
    env.ctx
        .process_context_mut()
        .node_mut(root)
        .set_individual_ancestor_depth(2);
    let set = env.ctx.signature_blocking_review_set(true);
    env.ctx
        .process_context_mut()
        .signature_blocking_review_set_mut(set)
        .get_review_data(false)
        .insert(2, 0);

    let next = env.algo.take_next_process_individual(&mut env.ctx);

    assert_eq!(next, root);
    assert!(env
        .ctx
        .process_context()
        .signature_blocking_review_set(set)
        .is_empty());
    let sig_block_data = env
        .ctx
        .process_context()
        .node(root)
        .signature_blocking_individual_node_concept_expansion_data(false);
    assert!(sig_block_data.is_some());
    assert!(env
        .ctx
        .process_context()
        .sig_block_con_exp_data(sig_block_data)
        .is_identic_concept_set_required());
    assert_eq!(
        env.ctx
            .process_context()
            .node(root)
            .last_search_blocker_candidate_count(),
        0
    );
}

#[test]
fn add_individual_to_incremental_expansion_queue_inserts_priority_queue() {
    let mut env = build_env();
    let root = env.root;
    let exp_individual = env
        .ctx
        .ontology_arenas_mut()
        .alloc_individual(Individual::new(43));

    let root_inc = env
        .ctx
        .process_context_mut()
        .node_incremental_expansion_data(root, true);
    env.ctx
        .process_context_mut()
        .inc_exp_data_mut(root_inc)
        .get_incremental_expansion_list(true)
        .unwrap()
        .push(exp_individual);
    env.ctx
        .process_context_mut()
        .inc_exp_data_mut(root_inc)
        .set_expansion_priority(6.0)
        .set_incremetnal_expansion_list_initialized(true);

    assert!(env
        .algo
        .add_individual_to_incremental_expansion_queue(root, &mut env.ctx));
    assert!(!env
        .algo
        .add_individual_to_incremental_expansion_queue(root, &mut env.ctx));

    let queue = env.ctx.get_incremental_expansion_processing_queue(false);
    assert_eq!(
        env.ctx
            .process_context()
            .indi_custom_priority_proc_queue(queue)
            .get_next_process_individual(),
        root
    );
    assert_eq!(
        env.ctx
            .process_context()
            .indi_custom_priority_proc_queue(queue)
            .get_queued_individual_count(),
        1
    );
    assert_eq!(
        env.ctx
            .process_context_mut()
            .indi_custom_priority_queue_take_next(queue),
        root
    );
    assert!(env
        .ctx
        .process_context()
        .indi_custom_priority_proc_queue(queue)
        .is_empty());
}

#[test]
fn take_next_process_individual_drains_incremental_expansion_priority_queue() {
    let mut env = build_env();
    env.algo.opt_incremental_compatible_expansion = true;
    env.ctx
        .processing_data_box_mut()
        .set_incremental_expansion_id(88);
    let root = env.root;
    let exp_individual = env
        .ctx
        .ontology_arenas_mut()
        .alloc_individual(Individual::new(44));

    let root_inc = env
        .ctx
        .process_context_mut()
        .node_incremental_expansion_data(root, true);
    env.ctx
        .process_context_mut()
        .inc_exp_data_mut(root_inc)
        .set_directly_changed(true)
        .get_incremental_expansion_list(true)
        .unwrap()
        .push(exp_individual);
    env.ctx
        .process_context_mut()
        .inc_exp_data_mut(root_inc)
        .set_incremetnal_expansion_list_initialized(true);
    assert!(env
        .algo
        .add_individual_to_incremental_expansion_queue(root, &mut env.ctx));

    let expanded = env.algo.take_next_process_individual(&mut env.ctx);

    assert!(expanded.is_some());
    assert_eq!(
        env.ctx
            .process_context()
            .node(expanded)
            .individual_node_id(),
        -44
    );
    assert_eq!(
        env.ctx
            .processing_data_box()
            .individual_process_node_vector()
            .get_data(-44),
        expanded
    );
    assert!(!env
        .ctx
        .process_context()
        .node(root)
        .is_incremental_expansion_queued());
}

#[test]
fn incremental_node_expansion_materializes_missing_nominal_node() {
    let mut env = build_env();
    env.algo.opt_incremental_compatible_expansion = true;
    env.ctx
        .processing_data_box_mut()
        .set_incremental_expansion_id(77);
    let root = env.root;
    let exp_individual = env
        .ctx
        .ontology_arenas_mut()
        .alloc_individual(Individual::new(42));

    let root_inc = env
        .ctx
        .process_context_mut()
        .node_incremental_expansion_data(root, true);
    env.ctx
        .process_context_mut()
        .inc_exp_data_mut(root_inc)
        .get_incremental_expansion_list(true)
        .unwrap()
        .push(exp_individual);
    env.ctx
        .process_context_mut()
        .inc_exp_data_mut(root_inc)
        .set_incremetnal_expansion_list_initialized(true);

    let expanded = env.algo.incremental_node_expansion(root, &mut env.ctx);

    assert!(expanded.is_some());
    let node = env.ctx.process_context().node(expanded);
    assert_eq!(node.individual_node_id(), -42);
    assert!(node.is_nominal_individual_node());
    assert_eq!(node.nominal_individual(), exp_individual);
    assert!(node.has_nominal_individual_triples_assertions());
    assert!(node.has_processing_restriction_flags(IndividualProcessNode::PRF_INCREMENTALEXPANDING));
    assert_eq!(node.incremental_expansion_id(), 77);
    assert_eq!(
        env.ctx
            .processing_data_box()
            .individual_process_node_vector()
            .get_data(-42),
        expanded
    );
    assert!(env
        .ctx
        .process_context()
        .node_incremental_expansion_data_existing(expanded)
        .is_some());
}

#[test]
fn compatibility_update_queues_directly_changed_incompatible_node() {
    use super::super::model::op;

    fn concept_with_tag(env: &mut SelfTestEnv, tag: i64) -> ConceptId {
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op::CCATOM);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    }

    fn one_concept_label_set(env: &mut SelfTestEnv, concept: ConceptId, tag: i64) -> LabelSetId {
        let con_des = env
            .ctx
            .process_context_mut()
            .alloc_con_desc(ConceptDescriptor::new());
        env.ctx.process_context_mut().con_desc_mut(con_des).concept = concept;
        let mut set = ReapplyConceptLabelSet::new(INVALID);
        set.concept_des_dep_map.insert(
            tag,
            ConceptDescriptorDependencyReapplyData {
                concept_descriptor: con_des,
                pos_neg_reapply_queue: Default::default(),
            },
        );
        set.concept_des_linker = con_des;
        set.concept_count = 1;
        set.concept_signature
            .add_concept_signature(concept, tag, false);
        env.ctx.process_context_mut().alloc_label_set(set)
    }

    let mut env = build_env();
    let root = env.root;
    let prev = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    let current_concept = concept_with_tag(&mut env, 1006);
    let previous_concept = concept_with_tag(&mut env, 1007);
    let root_set = one_concept_label_set(&mut env, current_concept, 1006);
    let prev_set = one_concept_label_set(&mut env, previous_concept, 1007);
    env.ctx
        .process_context_mut()
        .node_mut(root)
        .use_reapply_con_label_set = root_set;
    env.ctx
        .process_context_mut()
        .node_mut(prev)
        .use_reapply_con_label_set = prev_set;
    let root_inc = env
        .ctx
        .process_context_mut()
        .node_incremental_expansion_data(root, true);
    env.ctx
        .process_context_mut()
        .inc_exp_data_mut(root_inc)
        .set_previous_completion_graph_correspondence_individual_node(prev)
        .set_previous_completion_graph_correspondence_individual_node_loaded(true)
        .set_directly_changed(true);

    assert!(!env
        .algo
        .check_compatibility_update_directly_changed_propagation(root, &mut env.ctx));
    assert!(env
        .ctx
        .process_context()
        .node(root)
        .is_incremental_expansion_queued());
    assert!(!env
        .ctx
        .process_context()
        .inc_exp_data(root_inc)
        .is_previous_completion_graph_compatible());
}

#[test]
fn compatibility_update_establishes_found_directly_changed_neighbour() {
    use super::super::model::op;

    fn concept_with_tag(env: &mut SelfTestEnv, tag: i64) -> ConceptId {
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op::CCATOM);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    }

    fn one_concept_label_set(env: &mut SelfTestEnv, concept: ConceptId, tag: i64) -> LabelSetId {
        let con_des = env
            .ctx
            .process_context_mut()
            .alloc_con_desc(ConceptDescriptor::new());
        env.ctx.process_context_mut().con_desc_mut(con_des).concept = concept;
        let mut set = ReapplyConceptLabelSet::new(INVALID);
        set.concept_des_dep_map.insert(
            tag,
            ConceptDescriptorDependencyReapplyData {
                concept_descriptor: con_des,
                pos_neg_reapply_queue: Default::default(),
            },
        );
        set.concept_des_linker = con_des;
        set.concept_count = 1;
        set.concept_signature
            .add_concept_signature(concept, tag, false);
        env.ctx.process_context_mut().alloc_label_set(set)
    }

    let mut env = build_env();
    let root = env.root;
    let prev = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    let neighbour = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(neighbour)
        .set_individual_node_id(106);
    env.ctx
        .processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(106, neighbour);
    let current_concept = concept_with_tag(&mut env, 1008);
    let previous_concept = concept_with_tag(&mut env, 1009);
    let root_set = one_concept_label_set(&mut env, current_concept, 1008);
    let prev_set = one_concept_label_set(&mut env, previous_concept, 1009);
    env.ctx
        .process_context_mut()
        .node_mut(root)
        .use_reapply_con_label_set = root_set;
    env.ctx
        .process_context_mut()
        .node_mut(prev)
        .use_reapply_con_label_set = prev_set;

    let root_inc = env
        .ctx
        .process_context_mut()
        .node_incremental_expansion_data(root, true);
    env.ctx
        .process_context_mut()
        .inc_exp_data_mut(root_inc)
        .set_previous_completion_graph_correspondence_individual_node(prev)
        .set_previous_completion_graph_correspondence_individual_node_loaded(true);
    let neigh_inc = env
        .ctx
        .process_context_mut()
        .node_incremental_expansion_data(neighbour, true);
    env.ctx
        .process_context_mut()
        .inc_exp_data_mut(neigh_inc)
        .set_directly_changed(true);
    let conn_set = env
        .ctx
        .process_context_mut()
        .node_connection_successor_set(root);
    env.ctx
        .process_context_mut()
        .conn_succ_set_mut(conn_set)
        .insert_connection_successor(106);

    assert!(!env
        .algo
        .check_compatibility_update_directly_changed_propagation(root, &mut env.ctx));
    assert_eq!(
        env.ctx
            .process_context()
            .inc_exp_data(root_inc)
            .get_directly_changed_neighbour_connection_node(),
        neighbour
    );
    assert!(env
        .ctx
        .process_context()
        .inc_exp_data(neigh_inc)
        .has_neighbour_propagated_directly_changed());
}

#[test]
fn compatible_variable_propagation_bindings_collect_matching_concepts() {
    use super::super::model::individual::Variable;
    use super::super::model::VariableId;
    use super::super::process::binding_hash::ConceptVariableBindingPathSetHash;
    use super::super::process::varbind::{
        VariableBinding, VariableBindingDescriptor, VariableBindingPath,
        VariableBindingPathDescriptor, VariableBindingPathSet,
    };

    fn concept_with_tag(env: &mut SelfTestEnv, tag: i64) -> ConceptId {
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    }

    fn concept_descriptor(env: &mut SelfTestEnv, concept: ConceptId) -> ConDescId {
        let con_des = env
            .ctx
            .process_context_mut()
            .alloc_con_desc(ConceptDescriptor::new());
        env.ctx.process_context_mut().con_desc_mut(con_des).concept = concept;
        con_des
    }

    fn variable_path(
        env: &mut SelfTestEnv,
        prop_id: i64,
        bindings: &[(VariableId, NodeId)],
    ) -> VarBindingPathId {
        let mut head = Id::NONE;
        let mut last = Id::NONE;
        for &(variable, node) in bindings {
            let mut binding = VariableBinding::new();
            binding.init_variable_binding(TrackPointId::NONE, node, variable);
            let binding = env.ctx.process_context_mut().alloc_var_binding(binding);
            let mut binding_des = VariableBindingDescriptor::new();
            binding_des.init_variable_binding_descriptor(binding);
            let binding_des = env
                .ctx
                .process_context_mut()
                .alloc_var_binding_des(binding_des);
            if last.is_some() {
                env.ctx
                    .process_context_mut()
                    .var_binding_des_mut(last)
                    .set_next(binding_des);
            } else {
                head = binding_des;
            }
            last = binding_des;
        }
        let mut path = VariableBindingPath::new();
        path.init_variable_binding_path(prop_id, head);
        env.ctx.process_context_mut().alloc_vbpath(path)
    }

    fn add_concept_path(
        env: &mut SelfTestEnv,
        node: NodeId,
        concept: ConceptId,
        path: VarBindingPathId,
    ) {
        let con_des = concept_descriptor(env, concept);
        let path_hash = env
            .ctx
            .process_context_mut()
            .node_concept_variable_binding_path_set_hash(node);
        let tag = env.ctx.ontology_arenas().concept(concept).get_concept_tag();
        let path_set = ConceptVariableBindingPathSetHash::get_variable_binding_path_set(
            env.ctx.process_context_mut(),
            path_hash,
            tag,
            true,
        );
        env.ctx
            .process_context_mut()
            .vbpath_set_mut(path_set)
            .set_concept_descriptor(con_des);
        let mut path_des = VariableBindingPathDescriptor::new();
        path_des.init_variable_binding_path_descriptor(path, TrackPointId::NONE);
        let path_des = env.ctx.process_context_mut().alloc_vbpath_des(path_des);
        VariableBindingPathSet::add_variable_binding_path(
            env.ctx.process_context_mut(),
            path_set,
            path_des,
        );
    }

    let mut env = build_env();
    let root = env.root;
    let other = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(other)
        .set_individual_node_id(102);
    let variable = env
        .ctx
        .ontology_arenas_mut()
        .alloc_variable(Variable::new());
    let compatible_concept = concept_with_tag(&mut env, 801);
    let incompatible_concept = concept_with_tag(&mut env, 802);
    let query_path = variable_path(&mut env, 9001, &[(variable, root)]);
    let compatible_path = variable_path(&mut env, 9002, &[(variable, root)]);
    let incompatible_path = variable_path(&mut env, 9003, &[(variable, other)]);
    add_concept_path(&mut env, root, compatible_concept, compatible_path);
    add_concept_path(&mut env, root, incompatible_concept, incompatible_path);

    let mut root_ref = root;
    let concepts = env
        .algo
        .get_concepts_for_compatible_variable_propagation_bindings(
            &mut root_ref,
            query_path,
            &mut env.ctx,
        );

    assert_eq!(concepts, vec![compatible_concept]);
}

#[test]
fn variable_propagation_binding_collection_reads_live_path_hash() {
    use super::super::model::individual::Variable;
    use super::super::model::VariableId;
    use super::super::process::binding_hash::ConceptVariableBindingPathSetHash;
    use super::super::process::varbind::{
        VariableBinding, VariableBindingDescriptor, VariableBindingPath,
        VariableBindingPathDescriptor, VariableBindingPathSet,
    };

    fn concept_with_tag(env: &mut SelfTestEnv, tag: i64) -> ConceptId {
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    }

    fn variable_path(
        env: &mut SelfTestEnv,
        prop_id: i64,
        variable: VariableId,
        node: NodeId,
    ) -> VarBindingPathId {
        let mut binding = VariableBinding::new();
        binding.init_variable_binding(TrackPointId::NONE, node, variable);
        let binding = env.ctx.process_context_mut().alloc_var_binding(binding);
        let mut binding_des = VariableBindingDescriptor::new();
        binding_des.init_variable_binding_descriptor(binding);
        let binding_des = env
            .ctx
            .process_context_mut()
            .alloc_var_binding_des(binding_des);
        let mut path = VariableBindingPath::new();
        path.init_variable_binding_path(prop_id, binding_des);
        env.ctx.process_context_mut().alloc_vbpath(path)
    }

    fn add_path(env: &mut SelfTestEnv, node: NodeId, concept: ConceptId, path: VarBindingPathId) {
        let con_des = env
            .ctx
            .process_context_mut()
            .alloc_con_desc(ConceptDescriptor::new());
        env.ctx.process_context_mut().con_desc_mut(con_des).concept = concept;
        let hash = env
            .ctx
            .process_context_mut()
            .node_concept_variable_binding_path_set_hash(node);
        let tag = env.ctx.ontology_arenas().concept(concept).get_concept_tag();
        let set = ConceptVariableBindingPathSetHash::get_variable_binding_path_set(
            env.ctx.process_context_mut(),
            hash,
            tag,
            true,
        );
        env.ctx
            .process_context_mut()
            .vbpath_set_mut(set)
            .set_concept_descriptor(con_des);
        let mut path_des = VariableBindingPathDescriptor::new();
        path_des.init_variable_binding_path_descriptor(path, TrackPointId::NONE);
        let path_des = env.ctx.process_context_mut().alloc_vbpath_des(path_des);
        VariableBindingPathSet::add_variable_binding_path(
            env.ctx.process_context_mut(),
            set,
            path_des,
        );
    }

    let mut env = build_env();
    let root = env.root;
    let variable = env
        .ctx
        .ontology_arenas_mut()
        .alloc_variable(Variable::new());
    let concept_b = concept_with_tag(&mut env, 804);
    let first_path = variable_path(&mut env, 9010, variable, root);
    let replacement_path = variable_path(&mut env, 9010, variable, root);
    let second_path = variable_path(&mut env, 9011, variable, root);
    add_path(&mut env, root, concept_b, replacement_path);
    add_path(&mut env, root, concept_b, second_path);

    let mut root_ref = root;
    let mut collected = vec![(9010, first_path)];
    assert!(env
        .algo
        .collect_individual_node_variable_propagation_bindings(
            &mut root_ref,
            &mut collected,
            &mut env.ctx,
        ));
    collected.sort_by_key(|(prop_id, _)| *prop_id);

    assert_eq!(collected.len(), 2);
    assert_eq!(collected[0], (9010, replacement_path));
    assert_eq!(collected[1], (9011, second_path));
}

#[test]
fn compatible_concept_set_signature_accepts_shifted_suffix_match() {
    use super::super::process::satellites::CondensedReapplyQueue;

    fn concept_with_tag(env: &mut SelfTestEnv, tag: i64) -> ConceptId {
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    }

    fn descriptor(env: &mut SelfTestEnv, concept: ConceptId) -> ConDescId {
        let con_des = env
            .ctx
            .process_context_mut()
            .alloc_con_desc(ConceptDescriptor::new());
        env.ctx.process_context_mut().con_desc_mut(con_des).concept = concept;
        con_des
    }

    fn label_set(env: &mut SelfTestEnv, descs: &[ConDescId]) -> LabelSetId {
        for pair in descs.windows(2) {
            env.ctx
                .process_context_mut()
                .con_desc_mut(pair[0])
                .set_next(pair[1]);
        }
        if let Some(&last) = descs.last() {
            env.ctx
                .process_context_mut()
                .con_desc_mut(last)
                .set_next(ConDescId::NONE);
        }
        let mut set = ReapplyConceptLabelSet::new(INVALID);
        set.concept_des_linker = descs.first().copied().unwrap_or(ConDescId::NONE);
        set.concept_count = descs.len() as i64;
        for &des in descs {
            let concept = env.ctx.process_context().con_desc(des).get_concept();
            let tag = env.ctx.ontology_arenas().concept(concept).get_concept_tag();
            set.concept_des_dep_map.insert(
                tag,
                ConceptDescriptorDependencyReapplyData {
                    concept_descriptor: des,
                    pos_neg_reapply_queue: CondensedReapplyQueue::new(),
                },
            );
        }
        env.ctx.process_context_mut().alloc_label_set(set)
    }

    let mut env = build_env();
    let mut blocking = env.root;
    let compatible = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    let concept_a = concept_with_tag(&mut env, 811);
    let concept_b = concept_with_tag(&mut env, 812);
    let concept_c = concept_with_tag(&mut env, 813);
    let a = descriptor(&mut env, concept_a);
    let b = descriptor(&mut env, concept_b);
    let c = descriptor(&mut env, concept_c);
    let sub_set = label_set(&mut env, &[b, c]);
    let super_set = label_set(&mut env, &[a, b, c]);
    env.ctx
        .process_context_mut()
        .node_mut(compatible)
        .set_reapply_concept_label_set(super_set);

    assert!(env.algo.has_compatible_concept_set_signature(
        &mut blocking,
        sub_set,
        compatible,
        &mut env.ctx,
    ));
}

#[test]
fn compatible_concept_set_signature_rejects_critical_concept() {
    use super::super::model::op;
    use super::super::process::satellites::CondensedReapplyQueue;

    fn critical_concept(env: &mut SelfTestEnv) -> ConceptId {
        let mut c = Concept::new();
        c.set_concept_tag(814);
        c.set_operator_code(op::CCATMOST);
        c.set_parameter(2);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    }

    fn descriptor(env: &mut SelfTestEnv, concept: ConceptId) -> ConDescId {
        let con_des = env
            .ctx
            .process_context_mut()
            .alloc_con_desc(ConceptDescriptor::new());
        env.ctx.process_context_mut().con_desc_mut(con_des).concept = concept;
        con_des
    }

    fn singleton_label_set(env: &mut SelfTestEnv, des: ConDescId) -> LabelSetId {
        let concept = env.ctx.process_context().con_desc(des).get_concept();
        let tag = env.ctx.ontology_arenas().concept(concept).get_concept_tag();
        let mut set = ReapplyConceptLabelSet::new(INVALID);
        set.concept_des_linker = des;
        set.concept_count = 1;
        set.concept_des_dep_map.insert(
            tag,
            ConceptDescriptorDependencyReapplyData {
                concept_descriptor: des,
                pos_neg_reapply_queue: CondensedReapplyQueue::new(),
            },
        );
        env.ctx.process_context_mut().alloc_label_set(set)
    }

    let mut env = build_env();
    let mut blocking = env.root;
    let compatible = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    let critical = critical_concept(&mut env);
    let des = descriptor(&mut env, critical);
    let sub_set = singleton_label_set(&mut env, des);
    let super_set = singleton_label_set(&mut env, des);
    env.ctx
        .process_context_mut()
        .node_mut(compatible)
        .set_reapply_concept_label_set(super_set);

    assert!(!env.algo.has_compatible_concept_set_signature(
        &mut blocking,
        sub_set,
        compatible,
        &mut env.ctx,
    ));
    assert!(env
        .ctx
        .process_context()
        .node(blocking)
        .is_invalid_signature_blocking());
}

#[test]
fn label_concept_subset_direct_lookup_reports_missing_descriptor() {
    use super::super::process::satellites::CondensedReapplyQueue;

    fn concept_with_tag(env: &mut SelfTestEnv, tag: i64) -> ConceptId {
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    }

    fn descriptor(env: &mut SelfTestEnv, concept: ConceptId) -> ConDescId {
        let con_des = env
            .ctx
            .process_context_mut()
            .alloc_con_desc(ConceptDescriptor::new());
        env.ctx.process_context_mut().con_desc_mut(con_des).concept = concept;
        con_des
    }

    fn label_set(env: &mut SelfTestEnv, descs: &[ConDescId]) -> LabelSetId {
        let mut set = ReapplyConceptLabelSet::new(INVALID);
        set.concept_count = descs.len() as i64;
        for &des in descs {
            let concept = env.ctx.process_context().con_desc(des).get_concept();
            let tag = env.ctx.ontology_arenas().concept(concept).get_concept_tag();
            set.concept_des_dep_map.insert(
                tag,
                ConceptDescriptorDependencyReapplyData {
                    concept_descriptor: des,
                    pos_neg_reapply_queue: CondensedReapplyQueue::new(),
                },
            );
        }
        env.ctx.process_context_mut().alloc_label_set(set)
    }

    let mut env = build_env();
    let missing_concept = concept_with_tag(&mut env, 821);
    let missing = descriptor(&mut env, missing_concept);
    let sub_set = label_set(&mut env, &[missing]);
    let mut super_descs = Vec::new();
    for tag in 830..841 {
        let concept = concept_with_tag(&mut env, tag);
        super_descs.push(descriptor(&mut env, concept));
    }
    let super_set = label_set(&mut env, &super_descs);
    let mut first_not_entailed = ConDescId::NONE;
    let mut equal = true;

    assert!(!env.algo.is_label_concept_sub_set(
        sub_set,
        super_set,
        Some(&mut first_not_entailed),
        Some(&mut equal),
        &mut env.ctx,
    ));
    assert_eq!(first_not_entailed, missing);
    assert!(!equal);
}

#[test]
fn label_concept_subset_sorted_merge_accepts_contained_subset() {
    use super::super::process::satellites::CondensedReapplyQueue;

    fn concept_with_tag(env: &mut SelfTestEnv, tag: i64) -> ConceptId {
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    }

    fn descriptor(env: &mut SelfTestEnv, concept: ConceptId) -> ConDescId {
        let con_des = env
            .ctx
            .process_context_mut()
            .alloc_con_desc(ConceptDescriptor::new());
        env.ctx.process_context_mut().con_desc_mut(con_des).concept = concept;
        con_des
    }

    fn label_set(env: &mut SelfTestEnv, descs: &[ConDescId]) -> LabelSetId {
        let mut set = ReapplyConceptLabelSet::new(INVALID);
        set.concept_count = descs.len() as i64;
        for &des in descs {
            let concept = env.ctx.process_context().con_desc(des).get_concept();
            let tag = env.ctx.ontology_arenas().concept(concept).get_concept_tag();
            set.concept_des_dep_map.insert(
                tag,
                ConceptDescriptorDependencyReapplyData {
                    concept_descriptor: des,
                    pos_neg_reapply_queue: CondensedReapplyQueue::new(),
                },
            );
        }
        env.ctx.process_context_mut().alloc_label_set(set)
    }

    let mut env = build_env();
    let a_concept = concept_with_tag(&mut env, 850);
    let b_concept = concept_with_tag(&mut env, 851);
    let c_concept = concept_with_tag(&mut env, 852);
    let a = descriptor(&mut env, a_concept);
    let b = descriptor(&mut env, b_concept);
    let c = descriptor(&mut env, c_concept);
    let sub_set = label_set(&mut env, &[b, c]);
    let super_set = label_set(&mut env, &[a, b, c]);
    let mut first_not_entailed = ConDescId::NONE;
    let mut equal = true;

    assert!(env.algo.is_label_concept_sub_set(
        sub_set,
        super_set,
        Some(&mut first_not_entailed),
        Some(&mut equal),
        &mut env.ctx,
    ));
    assert_eq!(first_not_entailed, ConDescId::NONE);
    assert!(!equal);
}

#[test]
fn compatible_concept_set_reuse_rejects_non_subset_without_invalidating() {
    use super::super::process::satellites::CondensedReapplyQueue;

    fn concept_with_tag(env: &mut SelfTestEnv, tag: i64) -> ConceptId {
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    }

    fn descriptor(env: &mut SelfTestEnv, concept: ConceptId) -> ConDescId {
        let con_des = env
            .ctx
            .process_context_mut()
            .alloc_con_desc(ConceptDescriptor::new());
        env.ctx.process_context_mut().con_desc_mut(con_des).concept = concept;
        con_des
    }

    fn label_set(env: &mut SelfTestEnv, descs: &[ConDescId]) -> LabelSetId {
        for pair in descs.windows(2) {
            env.ctx
                .process_context_mut()
                .con_desc_mut(pair[0])
                .set_next(pair[1]);
        }
        let mut set = ReapplyConceptLabelSet::new(INVALID);
        set.concept_des_linker = descs.first().copied().unwrap_or(ConDescId::NONE);
        set.concept_count = descs.len() as i64;
        for &des in descs {
            let concept = env.ctx.process_context().con_desc(des).get_concept();
            let tag = env.ctx.ontology_arenas().concept(concept).get_concept_tag();
            set.concept_des_dep_map.insert(
                tag,
                ConceptDescriptorDependencyReapplyData {
                    concept_descriptor: des,
                    pos_neg_reapply_queue: CondensedReapplyQueue::new(),
                },
            );
        }
        env.ctx.process_context_mut().alloc_label_set(set)
    }

    let mut env = build_env();
    let indi = env.root;
    let reuse = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    let missing_concept = concept_with_tag(&mut env, 861);
    let present_concept = concept_with_tag(&mut env, 862);
    let missing = descriptor(&mut env, missing_concept);
    let present = descriptor(&mut env, present_concept);
    let sub_set = label_set(&mut env, &[missing]);
    let super_set = label_set(&mut env, &[present]);
    env.ctx
        .process_context_mut()
        .node_mut(reuse)
        .set_reapply_concept_label_set(super_set);

    assert!(!env
        .algo
        .has_compatible_concept_set_reuse(indi, sub_set, reuse, &mut env.ctx,));
    assert!(!env
        .ctx
        .process_context()
        .node(indi)
        .is_invalid_signature_blocking());
}

#[test]
fn compatible_concept_set_reuse_rejects_signature_critical_super_descriptor() {
    use super::super::model::op;
    use super::super::process::satellites::CondensedReapplyQueue;

    fn critical_concept(env: &mut SelfTestEnv) -> ConceptId {
        let mut c = Concept::new();
        c.set_concept_tag(863);
        c.set_operator_code(op::CCATMOST);
        c.set_parameter(2);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    }

    fn descriptor(env: &mut SelfTestEnv, concept: ConceptId) -> ConDescId {
        let con_des = env
            .ctx
            .process_context_mut()
            .alloc_con_desc(ConceptDescriptor::new());
        env.ctx.process_context_mut().con_desc_mut(con_des).concept = concept;
        con_des
    }

    fn label_set(env: &mut SelfTestEnv, descs: &[ConDescId]) -> LabelSetId {
        for pair in descs.windows(2) {
            env.ctx
                .process_context_mut()
                .con_desc_mut(pair[0])
                .set_next(pair[1]);
        }
        let mut set = ReapplyConceptLabelSet::new(INVALID);
        set.concept_des_linker = descs.first().copied().unwrap_or(ConDescId::NONE);
        set.concept_count = descs.len() as i64;
        for &des in descs {
            let concept = env.ctx.process_context().con_desc(des).get_concept();
            let tag = env.ctx.ontology_arenas().concept(concept).get_concept_tag();
            set.concept_des_dep_map.insert(
                tag,
                ConceptDescriptorDependencyReapplyData {
                    concept_descriptor: des,
                    pos_neg_reapply_queue: CondensedReapplyQueue::new(),
                },
            );
        }
        env.ctx.process_context_mut().alloc_label_set(set)
    }

    let mut env = build_env();
    let indi = env.root;
    let reuse = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    let critical = critical_concept(&mut env);
    let critical_des = descriptor(&mut env, critical);
    let sub_set = label_set(&mut env, &[critical_des]);
    let super_set = label_set(&mut env, &[critical_des]);
    env.ctx
        .process_context_mut()
        .node_mut(reuse)
        .set_reapply_concept_label_set(super_set);

    assert!(!env
        .algo
        .has_compatible_concept_set_reuse(indi, sub_set, reuse, &mut env.ctx,));
    assert!(env
        .ctx
        .process_context()
        .node(indi)
        .is_invalid_signature_blocking());
}

#[test]
fn concept_set_signature_matches_konclude_formula() {
    use super::super::process::satellites::ConceptSetSignature;

    let mut env = build_env();
    let mut c1 = Concept::new();
    c1.set_concept_tag(871);
    let c1 = env.ctx.ontology_arenas_mut().alloc_concept(c1);
    let mut c2 = Concept::new();
    c2.set_concept_tag(872);
    let c2 = env.ctx.ontology_arenas_mut().alloc_concept(c2);

    let mut sig = ConceptSetSignature::default();
    sig.add_concept_signature(c1, 871, false)
        .add_concept_signature(c2, 872, true);

    let con_sig1 = 871_i64;
    let con_sig2 = i64::MAX.wrapping_sub(872);
    let value1 = 0_i64.wrapping_add(con_sig1).wrapping_add(con_sig2);
    let value2 = 1_i64.wrapping_mul(con_sig1).wrapping_mul(con_sig2);
    let value3 = 0_i64.wrapping_add(c1.raw).wrapping_add(c2.raw);
    assert_eq!(sig.get_signature_value(), value1 ^ value2 ^ value3);

    let mut same = ConceptSetSignature::default();
    same.add_concept_signature(c1, 871, false)
        .add_concept_signature(c2, 872, true);
    assert!(sig.is_signature_equivalent(&same));
}

#[test]
fn label_set_resolved_insert_updates_signature_once() {
    let mut env = build_env();
    let mut concept = Concept::new();
    concept.set_concept_tag(873);
    let concept = env.ctx.ontology_arenas_mut().alloc_concept(concept);
    let con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    env.ctx.process_context_mut().con_desc_mut(con_des).concept = concept;
    let mut label_set = ReapplyConceptLabelSet::new(INVALID);

    let contained = label_set.insert_concept_get_clash_resolved(
        con_des,
        concept,
        873,
        false,
        &|_| false,
        None,
        None,
    );
    assert!(!contained);
    let first_signature = label_set.get_concept_signature_value();
    assert_ne!(first_signature, 0);

    let contained = label_set.insert_concept_get_clash_resolved(
        con_des,
        concept,
        873,
        false,
        &|_| false,
        None,
        None,
    );
    assert!(contained);
    assert_eq!(label_set.get_concept_signature_value(), first_signature);
}

#[test]
fn label_set_shared_main_alias_reads_previous_main_map() {
    fn concept_with_tag(env: &mut SelfTestEnv, tag: i64) -> ConceptId {
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    }

    fn descriptor(env: &mut SelfTestEnv, concept: ConceptId) -> ConDescId {
        let con_des = env
            .ctx
            .process_context_mut()
            .alloc_con_desc(ConceptDescriptor::new());
        env.ctx.process_context_mut().con_desc_mut(con_des).concept = concept;
        con_des
    }

    let mut env = build_env();
    let mut prev = ReapplyConceptLabelSet::new(INVALID);
    let mut first_des = ConDescId::NONE;
    for tag in 900..951 {
        let concept = concept_with_tag(&mut env, tag);
        let des = descriptor(&mut env, concept);
        if first_des.is_none() {
            first_des = des;
        }
        prev.concept_des_dep_map.insert(
            tag,
            ConceptDescriptorDependencyReapplyData {
                concept_descriptor: des,
                pos_neg_reapply_queue: Default::default(),
            },
        );
    }
    prev.concept_count = 51;
    let prev_id = env.ctx.process_context_mut().alloc_label_set(prev);
    let taken = std::mem::replace(
        env.ctx.process_context_mut().label_set_mut(prev_id),
        ReapplyConceptLabelSet::new(INVALID),
    );
    let mut child = ReapplyConceptLabelSet::new(INVALID);
    child.init_concept_label_set(Some((prev_id, &taken)));
    *env.ctx.process_context_mut().label_set_mut(prev_id) = taken;
    let child_id = env.ctx.process_context_mut().alloc_label_set(child);

    assert_eq!(
        env.ctx
            .process_context()
            .label_set_additional_size(child_id),
        51
    );
    assert_eq!(
        env.ctx
            .process_context()
            .label_set_additional_get_cloned(child_id, 900)
            .expect("shared main entry")
            .concept_descriptor,
        first_des
    );
}

#[test]
fn label_set_iterator_snapshots_shared_additional_alias() {
    fn concept_with_tag(env: &mut SelfTestEnv, tag: i64) -> ConceptId {
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    }

    fn descriptor(env: &mut SelfTestEnv, concept: ConceptId) -> ConDescId {
        let con_des = env
            .ctx
            .process_context_mut()
            .alloc_con_desc(ConceptDescriptor::new());
        env.ctx.process_context_mut().con_desc_mut(con_des).concept = concept;
        con_des
    }

    let mut env = build_env();
    let concept = concept_with_tag(&mut env, 960);
    let des = descriptor(&mut env, concept);
    let mut owned = HashMap::new();
    owned.insert(
        960,
        ConceptDescriptorDependencyReapplyData {
            concept_descriptor: des,
            pos_neg_reapply_queue: Default::default(),
        },
    );
    let mut prev = ReapplyConceptLabelSet::new(INVALID);
    prev.additional_concept_des_dep_map = AdditionalDesDepMapRef::Owned(owned);
    prev.concept_count = 1;
    let prev_id = env.ctx.process_context_mut().alloc_label_set(prev);
    let taken = std::mem::replace(
        env.ctx.process_context_mut().label_set_mut(prev_id),
        ReapplyConceptLabelSet::new(INVALID),
    );
    let mut child = ReapplyConceptLabelSet::new(INVALID);
    child.init_concept_label_set(Some((prev_id, &taken)));
    *env.ctx.process_context_mut().label_set_mut(prev_id) = taken;
    let child_id = env.ctx.process_context_mut().alloc_label_set(child);

    assert!(matches!(
        env.ctx
            .process_context()
            .label_set(child_id)
            .additional_concept_des_dep_map,
        AdditionalDesDepMapRef::Shared(LabelSetMapAlias {
            label_set,
            which: AdditionalMapSlot::Additional,
        }) if label_set == prev_id
    ));
    let mut it = env
        .ctx
        .process_context()
        .label_set_concept_label_set_iterator(child_id, true, false, false);
    assert!(it.has_value());
    assert_eq!(it.get_concept_descriptor(), des);
    it.move_next(env.ctx.process_context());
    assert!(!it.has_value());
}

#[test]
fn label_set_equal_set_reads_shared_additional_alias() {
    fn concept_with_tag(env: &mut SelfTestEnv, tag: i64) -> ConceptId {
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    }

    fn descriptor(env: &mut SelfTestEnv, concept: ConceptId) -> ConDescId {
        let con_des = env
            .ctx
            .process_context_mut()
            .alloc_con_desc(ConceptDescriptor::new());
        env.ctx.process_context_mut().con_desc_mut(con_des).concept = concept;
        con_des
    }

    let mut env = build_env();
    let concept = concept_with_tag(&mut env, 965);
    let shared_des = descriptor(&mut env, concept);
    let mut prev_owned = HashMap::new();
    prev_owned.insert(
        965,
        ConceptDescriptorDependencyReapplyData {
            concept_descriptor: shared_des,
            pos_neg_reapply_queue: Default::default(),
        },
    );
    let mut prev = ReapplyConceptLabelSet::new(INVALID);
    prev.additional_concept_des_dep_map = AdditionalDesDepMapRef::Owned(prev_owned);
    prev.concept_count = 1;
    prev.concept_signature
        .add_concept_signature(concept, 965, false);
    let prev_id = env.ctx.process_context_mut().alloc_label_set(prev);
    let taken = std::mem::replace(
        env.ctx.process_context_mut().label_set_mut(prev_id),
        ReapplyConceptLabelSet::new(INVALID),
    );
    let mut child = ReapplyConceptLabelSet::new(INVALID);
    child.init_concept_label_set(Some((prev_id, &taken)));
    *env.ctx.process_context_mut().label_set_mut(prev_id) = taken;
    let child_id = env.ctx.process_context_mut().alloc_label_set(child);

    let other_des = descriptor(&mut env, concept);
    let mut other_owned = HashMap::new();
    other_owned.insert(
        965,
        ConceptDescriptorDependencyReapplyData {
            concept_descriptor: other_des,
            pos_neg_reapply_queue: Default::default(),
        },
    );
    let mut other = ReapplyConceptLabelSet::new(INVALID);
    other.additional_concept_des_dep_map = AdditionalDesDepMapRef::Owned(other_owned);
    other.concept_count = 1;
    other
        .concept_signature
        .add_concept_signature(concept, 965, false);
    let other_id = env.ctx.process_context_mut().alloc_label_set(other);

    assert!(env
        .algo
        .is_label_concept_equal_set(child_id, other_id, &mut env.ctx));
}

#[test]
fn label_set_equal_set_rejects_lockstep_concept_mismatch() {
    fn concept_with_tag(env: &mut SelfTestEnv, tag: i64) -> ConceptId {
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    }

    fn descriptor(env: &mut SelfTestEnv, concept: ConceptId) -> ConDescId {
        let con_des = env
            .ctx
            .process_context_mut()
            .alloc_con_desc(ConceptDescriptor::new());
        env.ctx.process_context_mut().con_desc_mut(con_des).concept = concept;
        con_des
    }

    fn one_entry_set(con_tag: i64, con_des: ConDescId) -> ReapplyConceptLabelSet {
        let mut set = ReapplyConceptLabelSet::new(INVALID);
        set.concept_des_dep_map.insert(
            con_tag,
            ConceptDescriptorDependencyReapplyData {
                concept_descriptor: con_des,
                pos_neg_reapply_queue: Default::default(),
            },
        );
        set.concept_count = 1;
        set
    }

    let mut env = build_env();
    let concept1 = concept_with_tag(&mut env, 970);
    let concept2 = concept_with_tag(&mut env, 971);
    let set1_id = {
        let des = descriptor(&mut env, concept1);
        env.ctx
            .process_context_mut()
            .alloc_label_set(one_entry_set(970, des))
    };
    let set2_id = {
        let des = descriptor(&mut env, concept2);
        env.ctx
            .process_context_mut()
            .alloc_label_set(one_entry_set(971, des))
    };

    assert!(!env
        .algo
        .is_label_concept_equal_set(set1_id, set2_id, &mut env.ctx));
}

#[test]
fn pairwise_label_concept_equal_set_rejects_first_pair_mismatch() {
    fn concept_with_tag(env: &mut SelfTestEnv, tag: i64) -> ConceptId {
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    }

    fn descriptor(env: &mut SelfTestEnv, concept: ConceptId) -> ConDescId {
        let con_des = env
            .ctx
            .process_context_mut()
            .alloc_con_desc(ConceptDescriptor::new());
        env.ctx.process_context_mut().con_desc_mut(con_des).concept = concept;
        con_des
    }

    fn one_entry_set(con_tag: i64, con_des: ConDescId) -> ReapplyConceptLabelSet {
        let mut set = ReapplyConceptLabelSet::new(INVALID);
        set.concept_des_dep_map.insert(
            con_tag,
            ConceptDescriptorDependencyReapplyData {
                concept_descriptor: con_des,
                pos_neg_reapply_queue: Default::default(),
            },
        );
        set.concept_count = 1;
        set
    }

    let mut env = build_env();
    let concept1 = concept_with_tag(&mut env, 980);
    let concept2 = concept_with_tag(&mut env, 981);
    let set1_id = {
        let des = descriptor(&mut env, concept1);
        env.ctx
            .process_context_mut()
            .alloc_label_set(one_entry_set(980, des))
    };
    let set1_pair_id = {
        let des = descriptor(&mut env, concept2);
        env.ctx
            .process_context_mut()
            .alloc_label_set(one_entry_set(981, des))
    };
    let empty2_id = env
        .ctx
        .process_context_mut()
        .alloc_label_set(ReapplyConceptLabelSet::new(INVALID));
    let empty2_pair_id = env
        .ctx
        .process_context_mut()
        .alloc_label_set(ReapplyConceptLabelSet::new(INVALID));

    assert!(!env.algo.is_pairwise_label_concept_equal_set(
        set1_id,
        set1_pair_id,
        empty2_id,
        empty2_pair_id,
        &mut env.ctx
    ));
}

#[test]
fn pairwise_label_concept_equal_set_rejects_second_pair_mismatch() {
    fn concept_with_tag(env: &mut SelfTestEnv, tag: i64) -> ConceptId {
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    }

    fn descriptor(env: &mut SelfTestEnv, concept: ConceptId) -> ConDescId {
        let con_des = env
            .ctx
            .process_context_mut()
            .alloc_con_desc(ConceptDescriptor::new());
        env.ctx.process_context_mut().con_desc_mut(con_des).concept = concept;
        con_des
    }

    fn one_entry_set(con_tag: i64, con_des: ConDescId) -> ReapplyConceptLabelSet {
        let mut set = ReapplyConceptLabelSet::new(INVALID);
        set.concept_des_dep_map.insert(
            con_tag,
            ConceptDescriptorDependencyReapplyData {
                concept_descriptor: con_des,
                pos_neg_reapply_queue: Default::default(),
            },
        );
        set.concept_count = 1;
        set
    }

    let mut env = build_env();
    let empty1_id = env
        .ctx
        .process_context_mut()
        .alloc_label_set(ReapplyConceptLabelSet::new(INVALID));
    let empty1_pair_id = env
        .ctx
        .process_context_mut()
        .alloc_label_set(ReapplyConceptLabelSet::new(INVALID));
    let concept1 = concept_with_tag(&mut env, 982);
    let concept2 = concept_with_tag(&mut env, 983);
    let set2_id = {
        let des = descriptor(&mut env, concept1);
        env.ctx
            .process_context_mut()
            .alloc_label_set(one_entry_set(982, des))
    };
    let set2_pair_id = {
        let des = descriptor(&mut env, concept2);
        env.ctx
            .process_context_mut()
            .alloc_label_set(one_entry_set(983, des))
    };

    assert!(!env.algo.is_pairwise_label_concept_equal_set(
        empty1_id,
        empty1_pair_id,
        set2_id,
        set2_pair_id,
        &mut env.ctx
    ));
}

#[test]
fn nominal_clash_only_equal_set_ignores_extra_nominal() {
    use super::super::model::op;

    fn concept_with_tag(env: &mut SelfTestEnv, tag: i64, op_code: i64) -> ConceptId {
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op_code);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    }

    fn descriptor(env: &mut SelfTestEnv, concept: ConceptId, negated: bool) -> ConDescId {
        let con_des = env
            .ctx
            .process_context_mut()
            .alloc_con_desc(ConceptDescriptor::new());
        let desc = env.ctx.process_context_mut().con_desc_mut(con_des);
        desc.concept = concept;
        desc.negated = negated;
        con_des
    }

    fn insert(set: &mut ReapplyConceptLabelSet, tag: i64, con_des: ConDescId) {
        set.concept_des_dep_map.insert(
            tag,
            ConceptDescriptorDependencyReapplyData {
                concept_descriptor: con_des,
                pos_neg_reapply_queue: Default::default(),
            },
        );
        set.concept_count += 1;
    }

    let mut env = build_env();
    let atom = concept_with_tag(&mut env, 990, op::CCATOM);
    let nominal = concept_with_tag(&mut env, 991, op::CCNOMINAL);

    let mut set1 = ReapplyConceptLabelSet::new(INVALID);
    insert(&mut set1, 990, descriptor(&mut env, atom, false));
    insert(&mut set1, 991, descriptor(&mut env, nominal, false));
    let set1_id = env.ctx.process_context_mut().alloc_label_set(set1);

    let mut set2 = ReapplyConceptLabelSet::new(INVALID);
    insert(&mut set2, 990, descriptor(&mut env, atom, false));
    let set2_id = env.ctx.process_context_mut().alloc_label_set(set2);

    let mut clash = true;
    assert!(env
        .algo
        .is_label_concept_equal_set_consider_nominals_for_clash_only(
            set1_id,
            set2_id,
            Some(&mut clash),
            &mut env.ctx
        ));
    assert!(!clash);
}

#[test]
fn nominal_clash_only_equal_set_rejects_non_nominal_mismatch() {
    use super::super::model::op;

    fn concept_with_tag(env: &mut SelfTestEnv, tag: i64, op_code: i64) -> ConceptId {
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op_code);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    }

    fn descriptor(env: &mut SelfTestEnv, concept: ConceptId, negated: bool) -> ConDescId {
        let con_des = env
            .ctx
            .process_context_mut()
            .alloc_con_desc(ConceptDescriptor::new());
        let desc = env.ctx.process_context_mut().con_desc_mut(con_des);
        desc.concept = concept;
        desc.negated = negated;
        con_des
    }

    fn one_entry_set(tag: i64, con_des: ConDescId) -> ReapplyConceptLabelSet {
        let mut set = ReapplyConceptLabelSet::new(INVALID);
        set.concept_des_dep_map.insert(
            tag,
            ConceptDescriptorDependencyReapplyData {
                concept_descriptor: con_des,
                pos_neg_reapply_queue: Default::default(),
            },
        );
        set.concept_count = 1;
        set
    }

    let mut env = build_env();
    let concept1 = concept_with_tag(&mut env, 992, op::CCATOM);
    let concept2 = concept_with_tag(&mut env, 993, op::CCATOM);
    let set1_id = {
        let des = descriptor(&mut env, concept1, false);
        env.ctx
            .process_context_mut()
            .alloc_label_set(one_entry_set(992, des))
    };
    let set2_id = {
        let des = descriptor(&mut env, concept2, false);
        env.ctx
            .process_context_mut()
            .alloc_label_set(one_entry_set(993, des))
    };

    let mut clash = true;
    assert!(!env
        .algo
        .is_label_concept_equal_set_consider_nominals_for_clash_only(
            set1_id,
            set2_id,
            Some(&mut clash),
            &mut env.ctx
        ));
    assert!(!clash);
}

#[test]
fn nominal_clash_only_equal_set_reports_non_nominal_polarity_clash() {
    use super::super::model::op;

    fn concept_with_tag(env: &mut SelfTestEnv, tag: i64, op_code: i64) -> ConceptId {
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op_code);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    }

    fn descriptor(env: &mut SelfTestEnv, concept: ConceptId, negated: bool) -> ConDescId {
        let con_des = env
            .ctx
            .process_context_mut()
            .alloc_con_desc(ConceptDescriptor::new());
        let desc = env.ctx.process_context_mut().con_desc_mut(con_des);
        desc.concept = concept;
        desc.negated = negated;
        con_des
    }

    fn one_entry_set(tag: i64, con_des: ConDescId) -> ReapplyConceptLabelSet {
        let mut set = ReapplyConceptLabelSet::new(INVALID);
        set.concept_des_dep_map.insert(
            tag,
            ConceptDescriptorDependencyReapplyData {
                concept_descriptor: con_des,
                pos_neg_reapply_queue: Default::default(),
            },
        );
        set.concept_count = 1;
        set
    }

    let mut env = build_env();
    let concept = concept_with_tag(&mut env, 995, op::CCATOM);
    let set1_id = {
        let des = descriptor(&mut env, concept, false);
        env.ctx
            .process_context_mut()
            .alloc_label_set(one_entry_set(995, des))
    };
    let set2_id = {
        let des = descriptor(&mut env, concept, true);
        env.ctx
            .process_context_mut()
            .alloc_label_set(one_entry_set(995, des))
    };

    let mut clash = false;
    assert!(!env
        .algo
        .is_label_concept_equal_set_consider_nominals_for_clash_only(
            set1_id,
            set2_id,
            Some(&mut clash),
            &mut env.ctx
        ));
    assert!(clash);
}

#[test]
fn nominal_clash_only_equal_set_reports_opposite_nominal_clash() {
    use super::super::model::op;

    fn concept_with_tag(env: &mut SelfTestEnv, tag: i64, op_code: i64) -> ConceptId {
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op_code);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    }

    fn descriptor(env: &mut SelfTestEnv, concept: ConceptId, negated: bool) -> ConDescId {
        let con_des = env
            .ctx
            .process_context_mut()
            .alloc_con_desc(ConceptDescriptor::new());
        let desc = env.ctx.process_context_mut().con_desc_mut(con_des);
        desc.concept = concept;
        desc.negated = negated;
        con_des
    }

    fn one_entry_set(tag: i64, con_des: ConDescId) -> ReapplyConceptLabelSet {
        let mut set = ReapplyConceptLabelSet::new(INVALID);
        set.concept_des_dep_map.insert(
            tag,
            ConceptDescriptorDependencyReapplyData {
                concept_descriptor: con_des,
                pos_neg_reapply_queue: Default::default(),
            },
        );
        set.concept_count = 1;
        set
    }

    let mut env = build_env();
    let nominal = concept_with_tag(&mut env, 994, op::CCNOMINAL);
    let set1_id = {
        let des = descriptor(&mut env, nominal, false);
        env.ctx
            .process_context_mut()
            .alloc_label_set(one_entry_set(994, des))
    };
    let set2_id = {
        let des = descriptor(&mut env, nominal, true);
        env.ctx
            .process_context_mut()
            .alloc_label_set(one_entry_set(994, des))
    };

    let mut clash = false;
    assert!(!env
        .algo
        .is_label_concept_equal_set_consider_nominals_for_clash_only(
            set1_id,
            set2_id,
            Some(&mut clash),
            &mut env.ctx
        ));
    assert!(clash);
}

#[test]
fn nominal_clash_only_equal_set_advances_different_nominals_together() {
    use super::super::model::op;

    fn concept_with_tag(env: &mut SelfTestEnv, tag: i64, op_code: i64) -> ConceptId {
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op_code);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    }

    fn descriptor(env: &mut SelfTestEnv, concept: ConceptId, negated: bool) -> ConDescId {
        let con_des = env
            .ctx
            .process_context_mut()
            .alloc_con_desc(ConceptDescriptor::new());
        let desc = env.ctx.process_context_mut().con_desc_mut(con_des);
        desc.concept = concept;
        desc.negated = negated;
        con_des
    }

    fn insert(set: &mut ReapplyConceptLabelSet, tag: i64, con_des: ConDescId) {
        set.concept_des_dep_map.insert(
            tag,
            ConceptDescriptorDependencyReapplyData {
                concept_descriptor: con_des,
                pos_neg_reapply_queue: Default::default(),
            },
        );
        set.concept_count += 1;
    }

    let mut env = build_env();
    let nominal_a = concept_with_tag(&mut env, 996, op::CCNOMINAL);
    let nominal_b = concept_with_tag(&mut env, 997, op::CCNOMINAL);

    let mut set1 = ReapplyConceptLabelSet::new(INVALID);
    insert(&mut set1, 996, descriptor(&mut env, nominal_a, false));
    insert(&mut set1, 997, descriptor(&mut env, nominal_b, false));
    let set1_id = env.ctx.process_context_mut().alloc_label_set(set1);

    let mut set2 = ReapplyConceptLabelSet::new(INVALID);
    insert(&mut set2, 997, descriptor(&mut env, nominal_b, true));
    let set2_id = env.ctx.process_context_mut().alloc_label_set(set2);

    let mut clash = false;
    assert!(env
        .algo
        .is_label_concept_equal_set_consider_nominals_for_clash_only(
            set1_id,
            set2_id,
            Some(&mut clash),
            &mut env.ctx
        ));
    assert!(!clash);
}

#[test]
fn generate_debug_dependent_nominals_string_iterates_successor_nominal_set() {
    let mut env = build_env();
    let root = env.root;
    env.ctx
        .process_context_mut()
        .node_add_successor_connection_to_nominal(root, -9);
    env.ctx
        .process_context_mut()
        .node_add_successor_connection_to_nominal(root, -4);

    let mut nominal_ids = env
        .algo
        .generate_debug_dependent_nominals_string(root, &mut env.ctx)
        .split(", ")
        .map(|part| part.parse::<i64>().expect("dependent nominal id"))
        .collect::<Vec<_>>();
    nominal_ids.sort_unstable();
    assert_eq!(nominal_ids, vec![-9, -4]);
}

#[test]
fn nominal_connection_status_propagation_copies_exact_successor_nominals() {
    let mut env = build_env();
    env.algo.conf_exact_nominal_dependency_tracking = true;
    let target = env.root;
    let source = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(source)
        .set_individual_node_id(91)
        .add_processing_restriction_flags(IndividualProcessNode::PRF_SUCCESSORNOMINALCONNECTION);
    env.ctx
        .process_context_mut()
        .node_add_successor_connection_to_nominal(source, -91);
    env.ctx
        .process_context_mut()
        .node_add_successor_connection_to_nominal(source, -92);

    env.algo
        .propagate_individual_node_nominal_connection_status_to_ancestors(
            target,
            source,
            &mut env.ctx,
        );

    let mut target_nominals = env
        .ctx
        .process_context()
        .node_successor_connected_nominals(target);
    target_nominals.sort_unstable();
    assert_eq!(target_nominals, vec![-92, -91]);
    assert!(env
        .ctx
        .process_context()
        .node(target)
        .has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_SUCCESSORNOMINALCONNECTION,
        ));
}

#[test]
fn nominal_caching_loss_reactivation_drains_registered_nodes_to_queue() {
    let mut env = build_env();
    let root = env.root;
    let waiting = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    let nominal = attach_successor_nominal_connection(
        &mut env,
        root,
        17,
        IndividualProcessNode::PRF_COMPLETIONGRAPHCACHED,
    );
    let data = env
        .ctx
        .process_context_mut()
        .node_nominal_caching_loss_reactivation_data(nominal, true);
    env.ctx
        .process_context_mut()
        .nominal_caching_loss_reactivation_data_mut(data)
        .add_reactivation_individual_node(root)
        .add_reactivation_individual_node(waiting);

    assert!(env
        .algo
        .reactivate_individual_nodes_due_to_nominal_caching_loss(nominal, &mut env.ctx));

    let queue = env
        .ctx
        .get_nominal_caching_loss_reactivation_processing_queue(true);
    assert_eq!(
        env.ctx
            .process_context()
            .indi_unsorted_proc_queue(queue)
            .linker,
        vec![waiting, root]
    );
    assert!(env
        .ctx
        .process_context()
        .nominal_caching_loss_reactivation_data(data)
        .has_reactivated());
    assert!(env
        .ctx
        .process_context()
        .nominal_caching_loss_reactivation_data(data)
        .get_reactivation_individual_node_linker()
        .is_empty());
}

#[test]
fn install_saturation_caching_reactivation_records_cached_dependent_nominal() {
    let mut env = build_env();
    let root = env.root;
    let nominal = attach_successor_nominal_connection(
        &mut env,
        root,
        18,
        IndividualProcessNode::PRF_COMPLETIONGRAPHCACHED,
    );
    let mut cache_context = CacheContext::new();
    let mut dependent_nominals = SaturationNodeAssociatedDependentNominalSet::new();
    dependent_nominals.insert(-18);
    let dependent_nominals = cache_context.alloc_dependent_nominal_set(dependent_nominals);

    assert!(env.algo.install_saturation_caching_reactivation(
        root,
        dependent_nominals,
        &cache_context,
        &mut env.ctx,
    ));

    assert!(env
        .ctx
        .process_context()
        .node(nominal)
        .is_caching_loss_node_reactivation_installed());
    let data = env
        .ctx
        .process_context_mut()
        .node_nominal_caching_loss_reactivation_data(nominal, false);
    assert_eq!(
        env.ctx
            .process_context()
            .nominal_caching_loss_reactivation_data(data)
            .get_reactivation_individual_node_linker(),
        &[root]
    );
}

#[test]
fn install_saturation_caching_reactivation_queues_when_nominal_cache_lost() {
    let mut env = build_env();
    let root = env.root;
    let nominal = attach_successor_nominal_connection(
        &mut env,
        root,
        19,
        IndividualProcessNode::PRF_COMPLETIONGRAPHCACHINGINVALID,
    );
    let mut cache_context = CacheContext::new();
    let mut dependent_nominals = SaturationNodeAssociatedDependentNominalSet::new();
    dependent_nominals.insert(-19);
    let dependent_nominals = cache_context.alloc_dependent_nominal_set(dependent_nominals);

    assert!(env.algo.install_saturation_caching_reactivation(
        root,
        dependent_nominals,
        &cache_context,
        &mut env.ctx,
    ));

    assert!(env
        .ctx
        .process_context()
        .node(nominal)
        .is_caching_loss_node_reactivation_installed());
    let queue = env
        .ctx
        .get_nominal_caching_loss_reactivation_processing_queue(true);
    assert_eq!(
        env.ctx
            .process_context()
            .indi_unsorted_proc_queue(queue)
            .linker,
        vec![root]
    );
}

#[test]
fn try_install_saturation_caching_reactivation_rejects_invalid_successor_nominal() {
    let mut env = build_env();
    let root = env.root;
    attach_successor_nominal_connection(
        &mut env,
        root,
        20,
        IndividualProcessNode::PRF_COMPLETIONGRAPHCACHINGINVALID,
    );
    let nominal_set = env
        .ctx
        .process_context_mut()
        .node_successor_nominal_connection_set(root);
    env.ctx
        .process_context_mut()
        .node_add_successor_connection_to_nominal(root, -20);

    assert!(!env
        .algo
        .try_install_saturation_caching_reactivation(root, nominal_set, &mut env.ctx,));
}

fn install_matching_saturation_expansion_with_dependent_nominal(
    env: &mut SelfTestEnv,
    root: NodeId,
    sat_node: SatNodeId,
    nominal_id: i64,
    signature: i64,
) -> (CacheContext, SaturationNodeExpansionCacheHandler, NodeId) {
    attach_saturation_blocking_data(env, root, sat_node, ConDescId::NONE, 2, signature);
    let nominal = attach_successor_nominal_connection(
        env,
        root,
        nominal_id,
        IndividualProcessNode::PRF_COMPLETIONGRAPHCACHED,
    );
    env.ctx.base.max_completion_graph_cached_indi_node_id = nominal_id;

    let concept_a = env.concept_a;
    let sat_desc = descriptor_with_dependency(env, concept_a, DepKind::And, 24);
    let extra = marker_concept(env, signature * 10 + 1);
    let extra_desc = descriptor_with_dependency(env, extra, DepKind::And, 24);
    env.ctx
        .process_context_mut()
        .con_desc_mut(sat_desc)
        .set_next(extra_desc);
    install_saturation_cache_label_chain(env, root, sat_desc, sat_desc, 2, signature);

    let (mut cache_context, handler) = build_saturation_node_expansion_cache_handler();
    let linker_a = make_associated_concept_linker(
        &mut cache_context,
        CacheValue::new_value(
            100,
            concept_a.raw,
            CacheValueIdentifier::CacheValTagAndConcept,
        ),
    );
    let linker_b = make_associated_concept_linker(
        &mut cache_context,
        CacheValue::new_value(
            signature * 10 + 1,
            extra.raw,
            CacheValueIdentifier::CacheValTagAndConcept,
        ),
    );
    let mut dependent_nominals = SaturationNodeAssociatedDependentNominalSet::new();
    dependent_nominals.insert(-nominal_id);
    let dependent_nominals = cache_context.alloc_dependent_nominal_set(dependent_nominals);
    let mut write_data = SaturationNodeAssociatedExpansionCacheExpansionWriteData::new();
    write_data
        .init_expansion_write_data(sat_node, vec![linker_a, linker_b])
        .set_dependent_nominal_set(dependent_nominals)
        .set_tight_at_most_restriction(false)
        .set_concept_set_signature(signature)
        .set_total_concept_count(2);
    assert!(cache_context.install_sat_expansion_expand_write_data(
        handler.sat_cache_writer.cache,
        &[write_data],
        env.ctx.process_context_mut(),
        INVALID,
    ));

    (cache_context, handler, nominal)
}

#[test]
fn saturation_node_expansion_handler_reads_matching_expansion_with_dependent_nominal() {
    let mut env = build_env();
    let root = env.root;
    let sat_node = env
        .ctx
        .process_context_mut()
        .alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));
    let (cache_context, handler, _nominal) =
        install_matching_saturation_expansion_with_dependent_nominal(
            &mut env, root, sat_node, 21, 515,
        );

    let (cached, expansion) = handler.is_node_satisfiable_cached(root, &env.ctx, &cache_context);

    assert!(cached);
    assert!(expansion.is_some());
    let dep_set = cache_context
        .associated_concept_expansion(expansion)
        .dependent_nominal_set;
    assert_eq!(
        cache_context.dependent_nominal_set(dep_set).nominal_set,
        vec![-21]
    );
}

#[test]
fn detect_saturation_cached_retest_installs_dependent_nominal_reactivation() {
    let mut env = build_env();
    env.algo.conf_saturation_expansion_cache_reading = true;
    env.algo.conf_saturation_caching_with_nominals = true;
    let root = env.root;
    let sat_node = env
        .ctx
        .process_context_mut()
        .alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));
    let (cache_context, handler, nominal) =
        install_matching_saturation_expansion_with_dependent_nominal(
            &mut env, root, sat_node, 22, 516,
        );
    env.ctx
        .install_used_saturation_node_expansion_cache_handler(handler, cache_context);
    env.ctx
        .process_context_mut()
        .node_mut(root)
        .add_processing_restriction_flags(
            IndividualProcessNode::PRF_SATURATIONBLOCKINGCACHEDRETESTDUETOMODIFICATION,
        );

    assert!(env
        .algo
        .detect_individual_node_saturation_cached(root, &mut env.ctx));

    assert!(env
        .ctx
        .process_context()
        .node(root)
        .has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_SATURATIONBLOCKINGCACHED
                | IndividualProcessNode::PRF_SATURATIONSUCCESSORCREATIONBLOCKINGCACHED,
        ));
    assert!(env
        .ctx
        .process_context()
        .node(nominal)
        .is_caching_loss_node_reactivation_installed());
    let data = env
        .ctx
        .process_context_mut()
        .node_nominal_caching_loss_reactivation_data(nominal, false);
    assert_eq!(
        env.ctx
            .process_context()
            .nominal_caching_loss_reactivation_data(data)
            .get_reactivation_individual_node_linker(),
        &[root]
    );
}

#[test]
fn saturation_successor_connected_nominal_update_fans_out_once() {
    use super::super::model::role::Role;

    let mut env = build_env();
    let mut sat_algo = SaturationTaskHandleAlgorithm::new();
    let root = env
        .ctx
        .process_context_mut()
        .alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));
    let copy_dep = env
        .ctx
        .process_context_mut()
        .alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));
    let backward_source = env
        .ctx
        .process_context_mut()
        .alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));
    let non_inverse_source = env
        .ctx
        .process_context_mut()
        .alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));

    env.ctx
        .process_context_mut()
        .sat_node_mut(root)
        .depending_indi_node_linker
        .push(NegLink {
            target: copy_dep,
            negated: true,
        });
    env.ctx
        .process_context_mut()
        .sat_node_mut(root)
        .non_inverse_connected_indi_node_linker
        .push(non_inverse_source);
    let role = {
        let mut role = Role::new();
        role.set_role_tag(4401);
        env.ctx.ontology_arenas_mut().alloc_role(role)
    };
    env.ctx
        .process_context_mut()
        .sat_node_add_backward_propagation_link(root, role, backward_source);

    sat_algo.update_adding_successor_connected_nominal(root, 42, &mut env.ctx);

    for node in [root, copy_dep, backward_source, non_inverse_source] {
        assert!(env
            .ctx
            .process_context_mut()
            .sat_node_has_successor_connected_nominal(node, 42));
    }
    assert_eq!(sat_algo.successor_connected_nominal_updated_count, 4);

    sat_algo.update_adding_successor_connected_nominal(root, 42, &mut env.ctx);
    assert_eq!(
        sat_algo.successor_connected_nominal_updated_count, 4,
        "membership must stop duplicate successor-connected nominal propagation"
    );
}

#[test]
fn saturation_extended_debug_writer_creates_file_with_generated_tail() {
    let mut env = build_env();
    let mut sat_algo = SaturationTaskHandleAlgorithm::new();
    let path = format!(
        "/tmp/kobayashi-marust-saturation-debug-{}-{}.txt",
        std::process::id(),
        1
    );
    let _ = std::fs::remove_file(&path);

    let returned =
        sat_algo.write_generated_extended_debug_indi_model_string_list(&path, &mut env.ctx, 0, -1);

    let written = std::fs::read_to_string(&path).expect("debug writer should create output file");
    assert_eq!(written, returned);
    assert_eq!(returned, sat_algo.debug_indi_model_string);

    let _ = std::fs::remove_file(&path);
}

#[test]
fn extended_debug_collects_backend_cut_individual_node_ids() {
    let mut env = build_env();
    let mut algo = CompletionTaskHandleAlgorithm::new();
    let root = env.root;
    env.ctx
        .process_context_mut()
        .node_mut(root)
        .set_individual_node_id(31);
    let cut_successor = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(cut_successor)
        .set_individual_node_id(42);

    let exp_cont_data = env.ctx.backend_neighbour_expansion_controlling_data(true);
    env.ctx
        .process_context_mut()
        .backend_neighbour_expansion_controlling_data_mut(exp_cont_data)
        .add_cut_backend_neighbour_expansion_individual_linker(vec![root])
        .add_cut_backend_neighbour_expansion_individual_linker(vec![cut_successor]);

    let cut_ids = algo.collect_backend_neighbour_expansion_cut_individual_ids(&mut env.ctx);

    assert_eq!(cut_ids.len(), 2);
    assert!(cut_ids.contains(&31));
    assert!(cut_ids.contains(&42));
}

#[test]
fn saturation_successor_connected_nominal_set_overload_iterates_all_nominals() {
    let mut env = build_env();
    let mut sat_algo = SaturationTaskHandleAlgorithm::new();
    let target = env
        .ctx
        .process_context_mut()
        .alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));
    let source = env
        .ctx
        .process_context_mut()
        .alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));
    env.ctx
        .process_context_mut()
        .sat_node_add_successor_connected_nominal(source, 70);
    env.ctx
        .process_context_mut()
        .sat_node_add_successor_connected_nominal(source, 71);
    let source_set = env
        .ctx
        .process_context_mut()
        .sat_node_successor_connected_nominal_set_existing(source);

    sat_algo.update_adding_successor_connected_nominal_set(target, source_set, &mut env.ctx);

    let mut nominals = env
        .ctx
        .process_context_mut()
        .sat_node_successor_connected_nominals(target);
    nominals.sort_unstable();
    assert_eq!(nominals, vec![70, 71]);
    assert_eq!(sat_algo.successor_connected_nominal_updated_count, 2);
}

fn attach_successor_nominal_connection(
    env: &mut SelfTestEnv,
    source: NodeId,
    nominal_id: i64,
    flags: i64,
) -> NodeId {
    let nominal_node = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(nominal_node)
        .set_individual_node_id(nominal_id)
        .add_processing_restriction_flags(flags);
    env.ctx
        .processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(nominal_id, nominal_node);
    env.ctx
        .process_context_mut()
        .node_add_successor_connection_to_nominal(source, nominal_id);
    nominal_node
}

fn descriptor_with_dependency(
    env: &mut SelfTestEnv,
    concept: ConceptId,
    kind: DepKind,
    branch_tag: i64,
) -> ConDescId {
    let mut descriptor = ConceptDescriptor::new();
    descriptor.concept = concept;
    let descriptor = env.ctx.process_context_mut().alloc_con_desc(descriptor);
    let dep_track_point =
        real_dependency_track_point(env, env.root, descriptor, kind, branch_tag, branch_tag);
    env.ctx
        .process_context_mut()
        .con_desc_mut(descriptor)
        .set_dependency_track_point(dep_track_point);
    descriptor
}

fn install_saturation_cache_label_chain(
    env: &mut SelfTestEnv,
    node: NodeId,
    head: ConDescId,
    saturation_descriptor: ConDescId,
    concept_count: i64,
    signature: i64,
) {
    let label_set = env
        .ctx
        .process_context()
        .node(node)
        .use_reapply_con_label_set;
    env.ctx
        .process_context_mut()
        .label_set_mut(label_set)
        .concept_des_linker = head;
    env.ctx
        .process_context_mut()
        .label_set_mut(label_set)
        .concept_count = concept_count;
    env.ctx
        .process_context_mut()
        .label_set_mut(label_set)
        .get_concept_signature()
        .signature_value = signature;

    let saturation_tag = env
        .ctx
        .process_context()
        .con_desc(saturation_descriptor)
        .get_concept_tag(env.ctx.ontology_arenas());
    env.ctx
        .process_context_mut()
        .label_set_mut(label_set)
        .concept_des_dep_map
        .insert(
            saturation_tag,
            ConceptDescriptorDependencyReapplyData {
                concept_descriptor: saturation_descriptor,
                ..Default::default()
            },
        );
}

#[test]
fn saturation_node_expansion_handler_try_queues_deterministic_expansion() {
    let mut env = build_env();
    let sat_node = env
        .ctx
        .process_context_mut()
        .alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));
    let root = env.root;
    attach_saturation_blocking_data(&mut env, root, sat_node, ConDescId::NONE, 2, 303);

    let concept_a = env.concept_a;
    let sat_desc = descriptor_with_dependency(&mut env, concept_a, DepKind::And, 17);
    let extra = marker_concept(&mut env, 3031);
    let extra_desc = descriptor_with_dependency(&mut env, extra, DepKind::And, 17);
    env.ctx
        .process_context_mut()
        .con_desc_mut(sat_desc)
        .set_next(extra_desc);
    install_saturation_cache_label_chain(&mut env, root, sat_desc, sat_desc, 2, 303);

    let (mut cache_context, mut handler) = build_saturation_node_expansion_cache_handler();
    assert!(handler.try_node_satisfiable_caching(root, &mut env.ctx, &mut cache_context));
    assert_eq!(handler.pending_cache_message_count(), 1);
    match &handler.write_data[0] {
        SaturationNodeAssociatedExpansionCacheWriteDataRecord::Expand(write_data) => {
            assert!(write_data.is_deterministic_expansion());
            assert_eq!(write_data.get_expansion_concept_linker().len(), 2);
            assert_eq!(write_data.get_concept_set_signature(), 303);
            assert_eq!(write_data.get_total_concept_count(), 2);
            let first_linker = write_data.get_expansion_concept_linker()[0];
            let cache_value = cache_context
                .associated_concept_linker(first_linker)
                .get_cache_value();
            assert_eq!(
                cache_value.get_cache_value_identifier(),
                CacheValueIdentifier::CacheValTagAndConcept as i64
            );
            assert!(
                cache_value.get_tag() == 100 || cache_value.get_tag() == 3031,
                "producer cache value must carry the concept tag"
            );
        }
        SaturationNodeAssociatedExpansionCacheWriteDataRecord::Unsat(_) => {
            panic!("tryNodeSatisfiableCaching must queue expansion write data")
        }
    }
}

#[test]
fn saturation_node_expansion_handler_try_copies_successor_nominals_to_dependent_set() {
    let mut env = build_env();
    let sat_node = env
        .ctx
        .process_context_mut()
        .alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));
    let root = env.root;
    attach_saturation_blocking_data(&mut env, root, sat_node, ConDescId::NONE, 2, 313);
    attach_successor_nominal_connection(
        &mut env,
        root,
        7,
        IndividualProcessNode::PRF_SYNCHRONIZEDBACKEND,
    );

    let concept_a = env.concept_a;
    let sat_desc = descriptor_with_dependency(&mut env, concept_a, DepKind::And, 18);
    let extra = marker_concept(&mut env, 3131);
    let extra_desc = descriptor_with_dependency(&mut env, extra, DepKind::And, 18);
    env.ctx
        .process_context_mut()
        .con_desc_mut(sat_desc)
        .set_next(extra_desc);
    install_saturation_cache_label_chain(&mut env, root, sat_desc, sat_desc, 2, 313);

    let (mut cache_context, mut handler) = build_saturation_node_expansion_cache_handler();
    assert!(handler.try_node_satisfiable_caching(root, &mut env.ctx, &mut cache_context));
    assert_eq!(handler.pending_cache_message_count(), 1);
    let write_data = match &handler.write_data[0] {
        SaturationNodeAssociatedExpansionCacheWriteDataRecord::Expand(write_data) => write_data,
        SaturationNodeAssociatedExpansionCacheWriteDataRecord::Unsat(_) => {
            panic!("tryNodeSatisfiableCaching must queue expansion write data")
        }
    };
    let dep_set = write_data.get_dependent_nominal_set();
    assert!(dep_set.is_some());
    assert_eq!(
        cache_context.dependent_nominal_set(dep_set).nominal_set,
        vec![-7]
    );
}

#[test]
fn saturation_node_expansion_handler_try_splits_nondeterministic_prefix() {
    let mut env = build_env();
    let sat_node = env
        .ctx
        .process_context_mut()
        .alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));
    let root = env.root;
    attach_saturation_blocking_data(&mut env, root, sat_node, ConDescId::NONE, 3, 404);

    let concept_a = env.concept_a;
    let sat_desc = descriptor_with_dependency(&mut env, concept_a, DepKind::And, 23);
    let nondet_concept = marker_concept(&mut env, 4041);
    let nondet_desc =
        descriptor_with_dependency(&mut env, nondet_concept, DepKind::IndependentBase, 23);
    let det_concept = marker_concept(&mut env, 4042);
    let det_desc = descriptor_with_dependency(&mut env, det_concept, DepKind::And, 23);
    env.ctx
        .process_context_mut()
        .con_desc_mut(sat_desc)
        .set_next(nondet_desc);
    env.ctx
        .process_context_mut()
        .con_desc_mut(nondet_desc)
        .set_next(det_desc);
    install_saturation_cache_label_chain(&mut env, root, sat_desc, sat_desc, 3, 404);

    let (mut cache_context, mut handler) = build_saturation_node_expansion_cache_handler();
    assert!(handler.try_node_satisfiable_caching(root, &mut env.ctx, &mut cache_context));
    assert_eq!(handler.pending_cache_message_count(), 2);

    let det_write = match &handler.write_data[0] {
        SaturationNodeAssociatedExpansionCacheWriteDataRecord::Expand(write_data) => write_data,
        SaturationNodeAssociatedExpansionCacheWriteDataRecord::Unsat(_) => {
            panic!("latest queued record must be deterministic expansion")
        }
    };
    assert!(det_write.is_deterministic_expansion());
    assert_eq!(det_write.get_expansion_concept_linker().len(), 1);

    let nondet_write = match &handler.write_data[1] {
        SaturationNodeAssociatedExpansionCacheWriteDataRecord::Expand(write_data) => write_data,
        SaturationNodeAssociatedExpansionCacheWriteDataRecord::Unsat(_) => {
            panic!("first queued record must be nondeterministic expansion")
        }
    };
    assert!(!nondet_write.is_deterministic_expansion());
    assert_eq!(nondet_write.get_expansion_concept_linker().len(), 2);
    assert_eq!(nondet_write.get_concept_set_signature(), 404);
    assert_eq!(nondet_write.get_total_concept_count(), 3);
}

fn make_associated_concept_linker(
    cache_context: &mut CacheContext,
    cache_value: CacheValue,
) -> Id<SaturationNodeAssociatedConceptLinker> {
    let mut linker = SaturationNodeAssociatedConceptLinker::new();
    linker.init_concept_linker(cache_value);
    cache_context.alloc_associated_concept_linker(linker)
}

fn test_cache_value(value: i64) -> CacheValue {
    CacheValue::new_raw(value, 0, 0)
}

#[test]
fn unit21_cache_satisfiable_individual_nodes_queues_saturation_expansion() {
    let mut env = build_env();
    let sat_node = env
        .ctx
        .process_context_mut()
        .alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));
    let node = test_node_at_depth(&mut env, 68, 1);
    register_test_node(&mut env, node);
    attach_saturation_blocking_data(&mut env, node, sat_node, ConDescId::NONE, 2, 680);

    let concept_a = env.concept_a;
    let sat_desc = descriptor_with_dependency(&mut env, concept_a, DepKind::And, 68);
    let extra = marker_concept(&mut env, 6801);
    let extra_desc = descriptor_with_dependency(&mut env, extra, DepKind::And, 68);
    env.ctx
        .process_context_mut()
        .con_desc_mut(sat_desc)
        .set_next(extra_desc);
    install_saturation_cache_label_chain(&mut env, node, sat_desc, sat_desc, 2, 680);

    let (cache_context, handler) = build_saturation_node_expansion_cache_handler();
    env.ctx
        .install_used_saturation_node_expansion_cache_handler(handler, cache_context);
    env.algo
        .conf_saturation_satisfiabilitiy_expansion_cache_writing = true;

    assert!(env.algo.cache_satisfiable_individual_nodes(&mut env.ctx));

    let handler_state = env
        .ctx
        .take_used_saturation_node_expansion_cache_handler()
        .expect("installed saturation-node expansion handler must be restored");
    assert_eq!(handler_state.handler.pending_cache_message_count(), 1);
    match &handler_state.handler.write_data[0] {
        SaturationNodeAssociatedExpansionCacheWriteDataRecord::Expand(write_data) => {
            assert_eq!(write_data.get_concept_set_signature(), 680);
            assert_eq!(write_data.get_total_concept_count(), 2);
        }
        SaturationNodeAssociatedExpansionCacheWriteDataRecord::Unsat(_) => {
            panic!("cacheSatisfiableIndividualNodes must queue expansion write data")
        }
    }
    env.ctx
        .restore_used_saturation_node_expansion_cache_handler(handler_state);
}

#[test]
fn unit21_cache_satisfiable_individual_nodes_respects_saturation_flag_gate() {
    let mut env = build_env();
    let sat_node = env
        .ctx
        .process_context_mut()
        .alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));
    let node = test_node_at_depth(&mut env, 69, 1);
    register_test_node(&mut env, node);
    attach_saturation_blocking_data(&mut env, node, sat_node, ConDescId::NONE, 1, 690);
    env.ctx
        .process_context_mut()
        .node_mut(node)
        .add_processing_restriction_flags(IndividualProcessNode::PRF_SUCCESSORNEWNOMINALCONNECTION);

    let concept_a = env.concept_a;
    let sat_desc = descriptor_with_dependency(&mut env, concept_a, DepKind::And, 69);
    install_saturation_cache_label_chain(&mut env, node, sat_desc, sat_desc, 1, 690);

    let (cache_context, handler) = build_saturation_node_expansion_cache_handler();
    env.ctx
        .install_used_saturation_node_expansion_cache_handler(handler, cache_context);
    env.algo
        .conf_saturation_satisfiabilitiy_expansion_cache_writing = true;

    assert!(!env.algo.cache_satisfiable_individual_nodes(&mut env.ctx));

    let handler_state = env
        .ctx
        .take_used_saturation_node_expansion_cache_handler()
        .expect("installed saturation-node expansion handler must be restored");
    assert_eq!(handler_state.handler.pending_cache_message_count(), 0);
    env.ctx
        .restore_used_saturation_node_expansion_cache_handler(handler_state);
}

#[test]
fn saturation_node_expansion_handler_commit_installs_queued_expansion_write_data() {
    let mut env = build_env();
    let sat_node = env
        .ctx
        .process_context_mut()
        .alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));
    let (mut cache_context, mut handler) = build_saturation_node_expansion_cache_handler();
    let linker = make_associated_concept_linker(&mut cache_context, test_cache_value(61));
    let mut write_data = SaturationNodeAssociatedExpansionCacheExpansionWriteData::new();
    write_data
        .init_expansion_write_data(sat_node, vec![linker])
        .set_concept_set_signature(77)
        .set_total_concept_count(1);

    assert!(handler.queue_expansion_write_data(write_data, &mut env.ctx));
    assert_eq!(handler.pending_cache_message_count(), 1);
    assert!(handler.commit_cache_messages(&mut env.ctx, &mut cache_context));
    assert!(handler.write_data.is_empty());

    let entry = Id::new(
        env.ctx
            .process_context()
            .sat_node(sat_node)
            .get_cache_expansion_data()
            .raw,
    );
    let det = cache_context
        .sat_expansion_cache_entry(entry)
        .get_deterministic_concept_expansion();
    let expansion = cache_context.associated_concept_expansion(det);
    assert!(expansion.has_concept_expansion_linker(test_cache_value(61)));
    assert_eq!(expansion.get_concept_set_signature(), 77);
    assert_eq!(expansion.get_total_concept_count(), 1);
}

#[test]
fn saturation_node_expansion_handler_commit_drains_mixed_write_data_chain() {
    let mut env = build_env();
    let concept_a = env.concept_a;
    let unsat_node = attach_saturation_unsat_reference(&mut env, concept_a, false, false);
    let expansion_node = env
        .ctx
        .process_context_mut()
        .alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));
    let (mut cache_context, mut handler) = build_saturation_node_expansion_cache_handler();
    let linker = make_associated_concept_linker(&mut cache_context, test_cache_value(67));
    let mut expansion_write = SaturationNodeAssociatedExpansionCacheExpansionWriteData::new();
    expansion_write
        .init_expansion_write_data(expansion_node, vec![linker])
        .set_concept_set_signature(88)
        .set_total_concept_count(1);

    assert!(handler.cache_unsatisfiable_concept(concept_a, &mut env.ctx));
    assert!(handler.queue_expansion_write_data(expansion_write, &mut env.ctx));
    assert_eq!(handler.pending_cache_message_count(), 2);
    assert!(handler.commit_cache_messages(&mut env.ctx, &mut cache_context));
    assert!(handler.write_data.is_empty());

    let unsat = env.ctx.process_context().sat_node(unsat_node);
    assert!(unsat.direct_status_flags.has_clashed_flag());
    assert!(unsat.indirect_status_flags.has_clashed_flag());

    let entry = Id::new(
        env.ctx
            .process_context()
            .sat_node(expansion_node)
            .get_cache_expansion_data()
            .raw,
    );
    let det = cache_context
        .sat_expansion_cache_entry(entry)
        .get_deterministic_concept_expansion();
    let expansion = cache_context.associated_concept_expansion(det);
    assert!(expansion.has_concept_expansion_linker(test_cache_value(67)));
    assert_eq!(expansion.get_concept_set_signature(), 88);
}

#[test]
fn saturation_node_expansion_cache_installs_deterministic_expansion_write_data() {
    let mut env = build_env();
    let sat_node = env
        .ctx
        .process_context_mut()
        .alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));
    let (mut cache_context, handler) = build_saturation_node_expansion_cache_handler();
    let cache = handler.sat_cache_writer.cache;
    let linker_a = make_associated_concept_linker(&mut cache_context, test_cache_value(17));
    let linker_b = make_associated_concept_linker(&mut cache_context, test_cache_value(23));
    let mut dependent_nominals = SaturationNodeAssociatedDependentNominalSet::new();
    dependent_nominals.insert(5).insert(7);
    let dependent_nominals = cache_context.alloc_dependent_nominal_set(dependent_nominals);
    let mut write_data = SaturationNodeAssociatedExpansionCacheExpansionWriteData::new();
    write_data
        .init_expansion_write_data(sat_node, vec![linker_a, linker_b])
        .set_dependent_nominal_set(dependent_nominals)
        .set_tight_at_most_restriction(true)
        .set_requires_nondeterministic_expansion(true)
        .set_concept_set_signature(99)
        .set_total_concept_count(2);

    assert!(cache_context.install_sat_expansion_expand_write_data(
        cache,
        &[write_data],
        env.ctx.process_context_mut(),
        INVALID,
    ));

    let entry = Id::new(
        env.ctx
            .process_context()
            .sat_node(sat_node)
            .get_cache_expansion_data()
            .raw,
    );
    let det = cache_context
        .sat_expansion_cache_entry(entry)
        .get_deterministic_concept_expansion();
    let expansion = cache_context.associated_concept_expansion(det);
    assert_eq!(
        expansion.kind,
        AssociatedConceptExpansionKind::Deterministic
    );
    assert!(expansion.requires_non_deterministic_expansion());
    assert!(expansion.get_has_tight_at_most_restriction());
    assert_eq!(expansion.get_concept_set_signature(), 99);
    assert_eq!(expansion.get_total_concept_count(), 2);
    assert_eq!(expansion.get_concept_expansion_count(), 2);
    assert!(expansion.has_concept_expansion_linker(test_cache_value(17)));
    assert!(expansion.has_concept_expansion_linker(test_cache_value(23)));
    let dep_set = cache_context.dependent_nominal_set(expansion.dependent_nominal_set);
    assert_eq!(dep_set.nominal_set, vec![5, 7]);
}

#[test]
fn saturation_node_expansion_cache_installs_nondeterministic_expansion_write_data() {
    let mut env = build_env();
    let sat_node = env
        .ctx
        .process_context_mut()
        .alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));
    let (mut cache_context, handler) = build_saturation_node_expansion_cache_handler();
    let cache = handler.sat_cache_writer.cache;
    cache_context
        .sat_expansion_cache_mut(cache)
        .conf_allowed_non_det_expansion_count = 1;
    let linker = make_associated_concept_linker(&mut cache_context, test_cache_value(31));
    let mut write_data = SaturationNodeAssociatedExpansionCacheExpansionWriteData::new();
    write_data
        .init_expansion_write_data(sat_node, vec![linker])
        .set_deterministic_expansion(false)
        .set_concept_set_signature(44)
        .set_total_concept_count(1);

    assert!(cache_context.install_sat_expansion_expand_write_data(
        cache,
        &[write_data],
        env.ctx.process_context_mut(),
        INVALID,
    ));

    let entry = Id::new(
        env.ctx
            .process_context()
            .sat_node(sat_node)
            .get_cache_expansion_data()
            .raw,
    );
    let entry_ref = cache_context.sat_expansion_cache_entry(entry);
    assert_eq!(
        entry_ref.get_remaining_allowed_nondeterministic_expansion_count(),
        0
    );
    assert_eq!(
        entry_ref
            .get_nondeterministic_concept_expansion_linker()
            .len(),
        1
    );
    let nondet = entry_ref.get_nondeterministic_concept_expansion_linker()[0];
    let expansion = cache_context.associated_concept_expansion(nondet);
    assert_eq!(
        expansion.kind,
        AssociatedConceptExpansionKind::Nondeterministic
    );
    assert_eq!(expansion.get_concept_expansion_count(), 1);
    assert!(expansion.has_concept_expansion_linker(test_cache_value(31)));
    assert_eq!(expansion.get_concept_set_signature(), 44);
}

#[test]
fn saturation_node_expansion_cache_extends_deterministic_expansion_with_new_values() {
    let mut env = build_env();
    let sat_node = env
        .ctx
        .process_context_mut()
        .alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));
    let (mut cache_context, handler) = build_saturation_node_expansion_cache_handler();
    let cache = handler.sat_cache_writer.cache;
    let linker_a = make_associated_concept_linker(&mut cache_context, test_cache_value(41));
    let mut first_write = SaturationNodeAssociatedExpansionCacheExpansionWriteData::new();
    first_write
        .init_expansion_write_data(sat_node, vec![linker_a])
        .set_concept_set_signature(1)
        .set_total_concept_count(1);
    cache_context.install_sat_expansion_expand_write_data(
        cache,
        &[first_write],
        env.ctx.process_context_mut(),
        INVALID,
    );

    let linker_a_again = make_associated_concept_linker(&mut cache_context, test_cache_value(41));
    let linker_b = make_associated_concept_linker(&mut cache_context, test_cache_value(43));
    let mut second_write = SaturationNodeAssociatedExpansionCacheExpansionWriteData::new();
    second_write
        .init_expansion_write_data(sat_node, vec![linker_a_again, linker_b])
        .set_requires_nondeterministic_expansion(false)
        .set_concept_set_signature(2)
        .set_total_concept_count(2);
    cache_context.install_sat_expansion_expand_write_data(
        cache,
        &[second_write],
        env.ctx.process_context_mut(),
        INVALID,
    );

    let entry = Id::new(
        env.ctx
            .process_context()
            .sat_node(sat_node)
            .get_cache_expansion_data()
            .raw,
    );
    let det = cache_context
        .sat_expansion_cache_entry(entry)
        .get_deterministic_concept_expansion();
    let expansion = cache_context.associated_concept_expansion(det);
    assert!(expansion.has_concept_expansion_linker(test_cache_value(43)));
    assert!(!expansion.has_concept_expansion_linker(test_cache_value(41)));
    assert_eq!(expansion.get_concept_expansion_count(), 1);
    assert_eq!(expansion.get_concept_set_signature(), 2);
}

#[test]
fn saturation_node_expansion_cache_typed_write_data_dispatches_unsat_and_expand() {
    let mut env = build_env();
    let unsat_node = env
        .ctx
        .process_context_mut()
        .alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));
    let expansion_node = env
        .ctx
        .process_context_mut()
        .alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));
    let (mut cache_context, handler) = build_saturation_node_expansion_cache_handler();
    let cache = handler.sat_cache_writer.cache;

    let mut unsat_write = SaturationNodeAssociatedExpansionCacheUnsatisfiabilityWriteData::new();
    unsat_write.init_unsatisfiability_write_data(unsat_node);
    let linker = make_associated_concept_linker(&mut cache_context, test_cache_value(53));
    let mut expansion_write = SaturationNodeAssociatedExpansionCacheExpansionWriteData::new();
    expansion_write
        .init_expansion_write_data(expansion_node, vec![linker])
        .set_concept_set_signature(12)
        .set_total_concept_count(1);

    assert!(cache_context.write_sat_expansion_cache_data(
        cache,
        vec![
            SaturationNodeAssociatedExpansionCacheWriteDataRecord::Unsat(unsat_write),
            SaturationNodeAssociatedExpansionCacheWriteDataRecord::Expand(expansion_write),
        ],
        env.ctx.process_context_mut(),
        INVALID,
    ));

    let unsat = env.ctx.process_context().sat_node(unsat_node);
    assert!(unsat.direct_status_flags.has_clashed_flag());
    assert!(unsat.indirect_status_flags.has_clashed_flag());
    let entry = Id::new(
        env.ctx
            .process_context()
            .sat_node(expansion_node)
            .get_cache_expansion_data()
            .raw,
    );
    let det = cache_context
        .sat_expansion_cache_entry(entry)
        .get_deterministic_concept_expansion();
    let expansion = cache_context.associated_concept_expansion(det);
    assert!(expansion.has_concept_expansion_linker(test_cache_value(53)));
    assert_eq!(expansion.get_concept_set_signature(), 12);
}

#[test]
fn saturation_node_cache_updater_propagates_unsat_to_direct_and_indirect_flags() {
    let mut env = build_env();
    let sat_node = env
        .ctx
        .process_context_mut()
        .alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));
    let mut updater = SaturationNodeCacheUpdater::new(INVALID);

    updater.propagate_unsatisfibility(sat_node, env.ctx.process_context_mut(), INVALID);

    let node = env.ctx.process_context().sat_node(sat_node);
    assert!(node.direct_status_flags.has_clashed_flag());
    assert!(node.indirect_status_flags.has_clashed_flag());
    assert_eq!(updater.direct_updated_status_indi_node_count, 1);
    assert_eq!(updater.indirect_updated_status_indi_node_count, 1);
}

#[test]
fn saturation_node_cache_updater_propagates_copy_depending_flags() {
    let mut env = build_env();
    let root = env
        .ctx
        .process_context_mut()
        .alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));
    let dependent = env
        .ctx
        .process_context_mut()
        .alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));
    env.ctx
        .process_context_mut()
        .sat_node_mut(root)
        .add_copy_depending_individual_node_linker(NegLink {
            target: dependent,
            negated: false,
        });
    let mut updater = SaturationNodeCacheUpdater::new(INVALID);

    updater.propagate_unsatisfibility(root, env.ctx.process_context_mut(), INVALID);

    let root_node = env.ctx.process_context().sat_node(root);
    assert!(root_node.direct_status_flags.has_clashed_flag());
    assert!(root_node.indirect_status_flags.has_clashed_flag());
    let dependent_node = env.ctx.process_context().sat_node(dependent);
    assert!(dependent_node.direct_status_flags.has_clashed_flag());
    assert!(dependent_node.indirect_status_flags.has_clashed_flag());
    assert_eq!(updater.direct_updated_status_indi_node_count, 2);
    assert_eq!(updater.indirect_updated_status_indi_node_count, 2);
}

#[test]
fn saturation_node_cache_updater_propagates_non_inverse_indirect_flags() {
    let mut env = build_env();
    let root = env
        .ctx
        .process_context_mut()
        .alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));
    let source = env
        .ctx
        .process_context_mut()
        .alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));
    env.ctx
        .process_context_mut()
        .sat_node_mut(root)
        .add_non_inverse_connected_individual_node_linker(source);
    let mut updater = SaturationNodeCacheUpdater::new(INVALID);

    updater.propagate_unsatisfibility(root, env.ctx.process_context_mut(), INVALID);

    let root_node = env.ctx.process_context().sat_node(root);
    assert!(root_node.direct_status_flags.has_clashed_flag());
    assert!(root_node.indirect_status_flags.has_clashed_flag());
    let source_node = env.ctx.process_context().sat_node(source);
    assert!(!source_node.direct_status_flags.has_clashed_flag());
    assert!(source_node.indirect_status_flags.has_clashed_flag());
    assert_eq!(updater.direct_updated_status_indi_node_count, 1);
    assert_eq!(updater.indirect_updated_status_indi_node_count, 2);
}

#[test]
fn saturation_node_cache_updater_propagates_role_backward_indirect_flags() {
    use super::super::model::role::Role;

    let mut env = build_env();
    let role = env.ctx.ontology_arenas_mut().alloc_role(Role::new());
    let root = env
        .ctx
        .process_context_mut()
        .alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));
    let source = env
        .ctx
        .process_context_mut()
        .alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));
    env.ctx
        .process_context_mut()
        .sat_node_add_backward_propagation_link(root, role, source);
    let mut updater = SaturationNodeCacheUpdater::new(INVALID);

    updater.propagate_unsatisfibility(root, env.ctx.process_context_mut(), INVALID);

    let root_node = env.ctx.process_context().sat_node(root);
    assert!(root_node.direct_status_flags.has_clashed_flag());
    assert!(root_node.indirect_status_flags.has_clashed_flag());
    let source_node = env.ctx.process_context().sat_node(source);
    assert!(!source_node.direct_status_flags.has_clashed_flag());
    assert!(source_node.indirect_status_flags.has_clashed_flag());
    assert_eq!(updater.direct_updated_status_indi_node_count, 1);
    assert_eq!(updater.indirect_updated_status_indi_node_count, 2);
}

#[test]
fn computed_consequences_handler_commits_type_write_data_when_cacheable() {
    let mut env = build_env();
    let concept_a = env.concept_a;
    env.ctx
        .ontology_arenas_mut()
        .concept_mut(concept_a)
        .set_terminology(1);
    let individual = env
        .ctx
        .ontology_arenas_mut()
        .alloc_individual(Individual::new(13));
    let mut handler = ComputedConsequencesCacheHandler::default();
    handler.allow_type_concept_cache(individual, concept_a, true);

    assert!(handler.try_cache_type_concept(individual, concept_a, true, &mut env.ctx));
    assert!(handler.write_data.is_empty());
    assert_eq!(handler.committed_type_write_data.len(), 1);
    assert_eq!(
        handler.committed_type_write_data[0].get_individual(),
        individual
    );
    assert_eq!(
        handler.committed_type_write_data[0].get_concept(),
        concept_a
    );
    assert!(handler.committed_type_write_data[0].get_negation());
}

#[test]
fn root_unsatisfiability_write_caches_commits_computed_consequence_for_nominal_root() {
    let mut env = build_env();
    let concept_a = env.concept_a;
    env.algo.conf_cache_computed_consequences = true;
    env.ctx
        .ontology_arenas_mut()
        .concept_mut(concept_a)
        .set_terminology(1);
    let individual = make_constructed_nominal_root_with_single_init(&mut env, concept_a, false);

    let mut handler = ComputedConsequencesCacheHandler::default();
    handler.allow_type_concept_cache(individual, concept_a, true);
    env.ctx
        .install_used_computed_consequences_cache_handler(handler);

    let task = env
        .ctx
        .base
        .alloc_sat_calc_task(SatisfiableCalculationTask::new());

    assert!(!env
        .algo
        .root_unsatisfiability_write_caches(task, &mut env.ctx));

    let handler_state = env
        .ctx
        .take_used_computed_consequences_cache_handler()
        .expect("installed computed-consequences handler must be restored");
    assert_eq!(handler_state.handler.committed_type_write_data.len(), 1);
    assert_eq!(
        handler_state.handler.committed_type_write_data[0].get_individual(),
        individual
    );
    assert_eq!(
        handler_state.handler.committed_type_write_data[0].get_concept(),
        concept_a
    );
    assert!(handler_state.handler.committed_type_write_data[0].get_negation());
    env.ctx
        .restore_used_computed_consequences_cache_handler(handler_state);
}

#[test]
fn tracked_clashed_descriptor_hasher_matches_konclude_identity() {
    let mut env = build_env();
    let root = env.root;
    let concept_a = env.concept_a;
    let tracked = tracked_concept_clash(&mut env, root, concept_a, false, DepKind::And, 41, 12);
    let copied = env
        .algo
        .create_tracked_clashes_descriptor(tracked, &mut env.ctx, INVALID, true);
    let negated = tracked_concept_clash(&mut env, root, concept_a, true, DepKind::And, 41, 12);

    let tracked_hash = TrackedClashedDescriptorHasher::new(tracked, &env.ctx);
    let copied_hash = TrackedClashedDescriptorHasher::new(copied, &env.ctx);
    let negated_hash = TrackedClashedDescriptorHasher::new(negated, &env.ctx);

    assert_eq!(tracked_hash, copied_hash);
    assert_eq!(
        tracked_hash.get_descriptor_hash_value(),
        copied_hash.get_descriptor_hash_value()
    );
    assert_ne!(tracked_hash, negated_hash);
}

#[test]
fn tracked_clashed_dependency_line_sorts_deduplicates_and_takes_by_priority() {
    let mut env = build_env();
    let root = env.root;
    let concept_a = env.concept_a;
    let top_concept = env.top_concept;
    let top_data_range_concept = env.top_data_range_concept;
    let previous_level_node = test_node_at_depth(&mut env, 77, 2);
    let mut line = TrackedClashedDependencyLine::new();
    line.init_tracked_clashed_dependency_line(false, 0, 44);

    let level = tracked_concept_clash(&mut env, root, concept_a, false, DepKind::And, 51, 40);
    let level_branching =
        tracked_concept_clash(&mut env, root, top_concept, false, DepKind::And, 52, 44);
    let previous = tracked_concept_clash(
        &mut env,
        previous_level_node,
        concept_a,
        true,
        DepKind::And,
        53,
        40,
    );
    let previous_non_det = tracked_concept_clash(
        &mut env,
        previous_level_node,
        top_concept,
        true,
        DepKind::Merge,
        54,
        40,
    );
    let previous_non_det_branching = tracked_concept_clash(
        &mut env,
        previous_level_node,
        top_data_range_concept,
        false,
        DepKind::Merge,
        55,
        44,
    );
    let independent = tracked_concept_clash(
        &mut env,
        root,
        top_data_range_concept,
        true,
        DepKind::IndependentBase,
        56,
        41,
    );

    for clash in [
        level,
        level_branching,
        previous,
        previous_non_det,
        previous_non_det_branching,
        independent,
    ] {
        line.sort_in_tracked_clashed_descriptors(clash, false, &mut env.ctx);
    }

    let duplicate = env
        .algo
        .create_tracked_clashes_descriptor(level, &mut env.ctx, INVALID, true);
    line.sort_in_tracked_clashed_descriptors(duplicate, false, &mut env.ctx);
    assert_eq!(line.get_tracked_clashed_descriptor_set().len(), 6);
    assert_eq!(
        line.take_next_free_tracked_clashed_descriptor(&mut env.ctx),
        duplicate
    );
    assert_eq!(
        env.ctx
            .process_context()
            .clash_desc(duplicate)
            .get_next_descriptor(),
        Id::NONE
    );

    assert!(line.has_more_tracked_clashed_list());
    assert_eq!(line.take_next_tracked_clashed_list(), level);
    assert_eq!(line.take_next_tracked_clashed_list(), level_branching);
    assert_eq!(line.take_next_tracked_clashed_list(), previous);
    assert_eq!(line.take_next_tracked_clashed_list(), previous_non_det);
    assert_eq!(
        line.take_next_tracked_clashed_list(),
        previous_non_det_branching
    );
    assert_eq!(line.take_next_tracked_clashed_list(), independent);
    assert_eq!(line.take_next_tracked_clashed_list(), Id::NONE);
    assert!(!line.has_more_tracked_clashed_list());
}

#[test]
fn tracked_clashed_dependency_line_moves_current_level_buckets_by_resorting() {
    let mut env = build_env();
    let root = env.root;
    let concept_a = env.concept_a;
    let top_concept = env.top_concept;
    let mut line = TrackedClashedDependencyLine::new();
    line.init_tracked_clashed_dependency_line(false, 0, 70);

    let level = tracked_concept_clash(&mut env, root, concept_a, false, DepKind::And, 61, 69);
    let level_branching =
        tracked_concept_clash(&mut env, root, top_concept, false, DepKind::And, 62, 70);
    line.sort_in_tracked_clashed_descriptors(level, false, &mut env.ctx);
    line.sort_in_tracked_clashed_descriptors(level_branching, false, &mut env.ctx);

    line.move_to_next_individual_node_level(-1, &mut env.ctx);

    assert!(!line.has_level_tracked_clashed_descriptors());
    assert!(!line.has_level_tracked_branching_clashed_descriptors());
    let moved_head = line.get_pervious_level_tracked_clashed_descriptors();
    assert_eq!(moved_head, level_branching);
    assert_eq!(
        env.ctx
            .process_context()
            .clash_desc(moved_head)
            .get_next_descriptor(),
        level
    );
}

#[test]
fn get_free_tracked_clashed_descriptor_reuses_free_list_or_allocates() {
    let mut env = build_env();
    let root = env.root;
    let concept_a = env.concept_a;
    let mut line = TrackedClashedDependencyLine::new();

    let fresh = env
        .algo
        .get_free_tracked_clashed_descriptor(&mut line, &mut env.ctx);
    assert!(fresh.is_some());
    assert_eq!(
        env.ctx
            .process_context()
            .clash_desc(fresh)
            .get_next_descriptor(),
        Id::NONE
    );
    assert_eq!(
        env.ctx.process_context().clash_desc(fresh).kind,
        ClashDescriptorKind::Dependency
    );

    let reusable = tracked_concept_clash(&mut env, root, concept_a, false, DepKind::And, 71, 70);
    line.add_free_tracked_clashed_descriptor(reusable, &mut env.ctx);

    assert_eq!(
        env.algo
            .get_free_tracked_clashed_descriptor(&mut line, &mut env.ctx),
        reusable
    );
    assert_eq!(
        env.ctx
            .process_context()
            .clash_desc(reusable)
            .get_next_descriptor(),
        Id::NONE
    );

    let second_fresh = env
        .algo
        .get_free_tracked_clashed_descriptor(&mut line, &mut env.ctx);
    assert!(second_fresh.is_some());
    assert_ne!(second_fresh, reusable);
}

#[test]
fn mark_relevance_for_tracked_clashed_descriptors_marks_each_dependency_track_point() {
    let mut env = build_env();
    let root = env.root;
    let concept_a = env.concept_a;
    let top_concept = env.top_concept;
    let first = tracked_concept_clash(&mut env, root, concept_a, false, DepKind::And, 103, 103);
    let second = tracked_concept_clash(&mut env, root, top_concept, false, DepKind::And, 104, 103);
    env.ctx
        .process_context_mut()
        .clash_desc_mut(first)
        .set_next(second);
    let first_tp = env
        .ctx
        .process_context()
        .clash_desc(first)
        .get_dependency_track_point();
    let second_tp = env
        .ctx
        .process_context()
        .clash_desc(second)
        .get_dependency_track_point();

    assert!(!env
        .ctx
        .process_context()
        .track_point(first_tp)
        .is_dependency_relevant());
    assert!(!env
        .ctx
        .process_context()
        .track_point(second_tp)
        .is_dependency_relevant());

    env.algo
        .mark_relevance_for_tracked_clashed_descriptors(first, &mut env.ctx);

    assert!(env
        .ctx
        .process_context()
        .track_point(first_tp)
        .is_dependency_relevant());
    assert!(env
        .ctx
        .process_context()
        .track_point(second_tp)
        .is_dependency_relevant());
}

#[test]
fn backtrack_from_tracking_line_step_caches_independent_only_and_stops() {
    let mut env = build_env();
    let root = env.root;
    let concept_a = env.concept_a;
    let independent = tracked_concept_clash(
        &mut env,
        root,
        concept_a,
        false,
        DepKind::IndependentBase,
        106,
        106,
    );
    let mut line = TrackedClashedDependencyLine::new();
    line.init_tracked_clashed_dependency_line(false, 0, 106);
    line.sort_in_tracked_clashed_descriptors(independent, false, &mut env.ctx);

    assert!(!env
        .algo
        .backtrack_from_tracking_line_step(&mut line, &mut env.ctx));
    assert_eq!(line.take_next_tracked_clashed_list(), independent);
    assert_eq!(line.take_next_tracked_clashed_list(), Id::NONE);
}

#[test]
fn backtrack_from_tracking_line_step_frees_previous_level_deterministic_descriptor() {
    let mut env = build_env();
    let previous_node = test_node_at_depth(&mut env, 91, 2);
    let concept_a = env.concept_a;
    let mut con_des = ConceptDescriptor::new();
    con_des.concept = concept_a;
    let con_des = env.ctx.process_context_mut().alloc_con_desc(con_des);
    let base_tp = real_dependency_track_point(
        &mut env,
        previous_node,
        con_des,
        DepKind::IndependentBase,
        106,
        106,
    );
    let tp = dependency_track_point_with_previous(
        &mut env,
        previous_node,
        con_des,
        DepKind::And,
        107,
        107,
        base_tp,
        &[],
    );
    env.ctx
        .process_context_mut()
        .con_desc_mut(con_des)
        .set_dependency_track_point(tp);
    let mut clash_node = previous_node;
    let clash = env.algo.create_clashed_concept_descriptor(
        Id::NONE,
        &mut clash_node,
        con_des,
        tp,
        &mut env.ctx,
    );
    let previous = env
        .algo
        .create_tracked_clashes_descriptor(clash, &mut env.ctx, INVALID, false);
    let mut line = TrackedClashedDependencyLine::new();
    line.init_tracked_clashed_dependency_line(false, 0, 107);
    line.sort_in_tracked_clashed_descriptors(previous, false, &mut env.ctx);
    assert!(line.has_pervious_level_tracked_clashed_descriptors());

    assert!(!env
        .algo
        .backtrack_from_tracking_line_step(&mut line, &mut env.ctx));
    let restored = line.take_next_tracked_clashed_list();
    assert_ne!(restored, Id::NONE);
    assert_eq!(
        env.ctx
            .process_context()
            .clash_desc(restored)
            .get_dependency_track_point(),
        base_tp
    );
    assert_eq!(
        line.take_next_free_tracked_clashed_descriptor(&mut env.ctx),
        previous
    );
}

#[test]
fn get_backtracked_deterministic_clashed_descriptors_replays_previous_track_point() {
    let mut env = build_env();
    let node = test_node_at_depth(&mut env, 92, 3);
    let concept_a = env.concept_a;
    let mut con_des = ConceptDescriptor::new();
    con_des.concept = concept_a;
    let con_des = env.ctx.process_context_mut().alloc_con_desc(con_des);
    let base_tp =
        real_dependency_track_point(&mut env, node, con_des, DepKind::IndependentBase, 108, 108);
    let tp = dependency_track_point_with_previous(
        &mut env,
        node,
        con_des,
        DepKind::And,
        109,
        109,
        base_tp,
        &[],
    );
    env.ctx
        .process_context_mut()
        .con_desc_mut(con_des)
        .set_dependency_track_point(tp);
    let mut clash_node = node;
    let clash = env.algo.create_clashed_concept_descriptor(
        Id::NONE,
        &mut clash_node,
        con_des,
        tp,
        &mut env.ctx,
    );
    let tracked = env
        .algo
        .create_tracked_clashes_descriptor(clash, &mut env.ctx, INVALID, false);
    let mut line = TrackedClashedDependencyLine::new();
    line.init_tracked_clashed_dependency_line(false, 0, 109);
    let mut min_level = i64::MAX;

    let replayed = env.algo.get_backtracked_deterministic_clashed_descriptors(
        tracked,
        &mut line,
        Some(&mut min_level),
        &mut env.ctx,
    );

    let replayed_desc = env.ctx.process_context().clash_desc(replayed);
    assert_eq!(replayed_desc.get_dependency_track_point(), base_tp);
    assert_eq!(replayed_desc.get_concept_descriptor(), con_des);
    assert_eq!(replayed_desc.get_appropriated_individual(), node);
    assert_eq!(replayed_desc.get_next_descriptor(), Id::NONE);
    assert_eq!(min_level, 3);
}

#[test]
fn get_backtracked_deterministic_clashed_descriptors_includes_additional_dependencies() {
    let mut env = build_env();
    let node = test_node_at_depth(&mut env, 93, 5);
    let additional_node = test_node_at_depth(&mut env, 94, 1);
    let concept_a = env.concept_a;
    let mut con_des = ConceptDescriptor::new();
    con_des.concept = concept_a;
    let con_des = env.ctx.process_context_mut().alloc_con_desc(con_des);
    let base_tp =
        real_dependency_track_point(&mut env, node, con_des, DepKind::IndependentBase, 110, 110);
    let mut add_con_des = ConceptDescriptor::new();
    add_con_des.concept = concept_a;
    let add_con_des = env.ctx.process_context_mut().alloc_con_desc(add_con_des);
    let add_tp = real_dependency_track_point(
        &mut env,
        additional_node,
        add_con_des,
        DepKind::IndependentBase,
        111,
        111,
    );
    let tp = dependency_track_point_with_previous(
        &mut env,
        node,
        con_des,
        DepKind::And,
        112,
        112,
        base_tp,
        &[add_tp],
    );
    env.ctx
        .process_context_mut()
        .con_desc_mut(con_des)
        .set_dependency_track_point(tp);
    let mut clash_node = node;
    let clash = env.algo.create_clashed_concept_descriptor(
        Id::NONE,
        &mut clash_node,
        con_des,
        tp,
        &mut env.ctx,
    );
    let tracked = env
        .algo
        .create_tracked_clashes_descriptor(clash, &mut env.ctx, INVALID, false);
    let mut line = TrackedClashedDependencyLine::new();
    line.init_tracked_clashed_dependency_line(false, 0, 112);
    let mut min_level = i64::MAX;

    let head = env.algo.get_backtracked_deterministic_clashed_descriptors(
        tracked,
        &mut line,
        Some(&mut min_level),
        &mut env.ctx,
    );
    let head_desc = env.ctx.process_context().clash_desc(head);
    let tail = head_desc.get_next_descriptor();
    let tail_desc = env.ctx.process_context().clash_desc(tail);

    assert_eq!(head_desc.get_dependency_track_point(), add_tp);
    assert_eq!(head_desc.get_concept_descriptor(), Id::NONE);
    assert_eq!(head_desc.get_appropriated_individual(), additional_node);
    assert_eq!(tail_desc.get_dependency_track_point(), base_tp);
    assert_eq!(tail_desc.get_concept_descriptor(), con_des);
    assert_eq!(tail_desc.get_next_descriptor(), Id::NONE);
    assert_eq!(min_level, 1);
    assert_eq!(
        line.take_next_free_tracked_clashed_descriptor(&mut env.ctx),
        Id::NONE
    );
}

#[test]
fn get_backtracked_deterministic_clashed_descriptors_before_processing_tag_replays_after_tag() {
    let mut env = build_env();
    let node = test_node_at_depth(&mut env, 96, 4);
    let concept_a = env.concept_a;
    let mut con_des = ConceptDescriptor::new();
    con_des.concept = concept_a;
    let con_des = env.ctx.process_context_mut().alloc_con_desc(con_des);
    let base_tp =
        real_dependency_track_point(&mut env, node, con_des, DepKind::IndependentBase, 120, 120);
    let tp = dependency_track_point_with_previous(
        &mut env,
        node,
        con_des,
        DepKind::And,
        130,
        130,
        base_tp,
        &[],
    );
    env.ctx
        .process_context_mut()
        .con_desc_mut(con_des)
        .set_dependency_track_point(tp);
    let mut clash_node = node;
    let clash = env.algo.create_clashed_concept_descriptor(
        Id::NONE,
        &mut clash_node,
        con_des,
        tp,
        &mut env.ctx,
    );
    let tracked = env
        .algo
        .create_tracked_clashes_descriptor(clash, &mut env.ctx, INVALID, false);
    let mut line = TrackedClashedDependencyLine::new();
    line.init_tracked_clashed_dependency_line(false, 0, 130);

    let head = env
        .algo
        .get_backtracked_deterministic_clashed_descriptors_before_processing_tag(
            tracked,
            125,
            &mut line,
            &mut env.ctx,
        );

    let head_desc = env.ctx.process_context().clash_desc(head);
    assert_ne!(head, tracked);
    assert_eq!(head_desc.get_dependency_track_point(), base_tp);
    assert_eq!(head_desc.get_concept_descriptor(), con_des);
    assert_eq!(head_desc.get_appropriated_individual(), node);
    assert_eq!(head_desc.get_next_descriptor(), Id::NONE);
    assert_eq!(
        line.take_next_free_tracked_clashed_descriptor(&mut env.ctx),
        tracked
    );
}

#[test]
fn get_backtracked_deterministic_clashed_descriptors_before_processing_tag_frees_duplicate_replay()
{
    let mut env = build_env();
    let node = test_node_at_depth(&mut env, 97, 4);
    let concept_a = env.concept_a;
    let mut con_des = ConceptDescriptor::new();
    con_des.concept = concept_a;
    let con_des = env.ctx.process_context_mut().alloc_con_desc(con_des);
    let base_tp =
        real_dependency_track_point(&mut env, node, con_des, DepKind::IndependentBase, 140, 140);
    let tp = dependency_track_point_with_previous(
        &mut env,
        node,
        con_des,
        DepKind::And,
        150,
        150,
        base_tp,
        &[],
    );
    env.ctx
        .process_context_mut()
        .con_desc_mut(con_des)
        .set_dependency_track_point(tp);

    let mut clash_node = node;
    let clash = env.algo.create_clashed_concept_descriptor(
        Id::NONE,
        &mut clash_node,
        con_des,
        tp,
        &mut env.ctx,
    );
    let tracked = env
        .algo
        .create_tracked_clashes_descriptor(clash, &mut env.ctx, INVALID, false);
    let mut duplicate_node = node;
    let duplicate_clash = env.algo.create_clashed_concept_descriptor(
        Id::NONE,
        &mut duplicate_node,
        con_des,
        base_tp,
        &mut env.ctx,
    );
    let duplicate =
        env.algo
            .create_tracked_clashes_descriptor(duplicate_clash, &mut env.ctx, INVALID, false);
    let mut line = TrackedClashedDependencyLine::new();
    line.init_tracked_clashed_dependency_line(false, 0, 150);
    assert!(line.insert_tracked_clashed_descriptor_hasher(duplicate, &env.ctx));

    let head = env
        .algo
        .get_backtracked_deterministic_clashed_descriptors_before_processing_tag(
            tracked,
            145,
            &mut line,
            &mut env.ctx,
        );

    assert_eq!(head, Id::NONE);
    assert_eq!(
        line.take_next_free_tracked_clashed_descriptor(&mut env.ctx),
        tracked
    );
    let replay = line.take_next_free_tracked_clashed_descriptor(&mut env.ctx);
    assert_ne!(replay, Id::NONE);
    assert_ne!(replay, duplicate);
    assert_eq!(
        env.ctx
            .process_context()
            .clash_desc(replay)
            .get_dependency_track_point(),
        base_tp
    );
    assert_eq!(
        line.take_next_free_tracked_clashed_descriptor(&mut env.ctx),
        Id::NONE
    );
}

#[test]
fn backtrack_non_deterministic_branching_clashed_descriptor_marks_branch_with_open_sibling() {
    let mut env = build_env();
    let node = test_node_at_depth(&mut env, 98, 4);
    let concept_a = env.concept_a;
    let mut con_des = ConceptDescriptor::new();
    con_des.concept = concept_a;
    let con_des = env.ctx.process_context_mut().alloc_con_desc(con_des);
    let base_tp =
        real_dependency_track_point(&mut env, node, con_des, DepKind::IndependentBase, 200, 200);

    let base = DepNodeBase {
        process_tag: 210,
        concept_descriptor: ConDescId::NONE,
        individual_node: node,
        kind: DepKind::Or,
        dep_track_point: base_tp,
        additional_after: Id::NONE,
        selected_var_bind_path: VarBindingPathId::NONE,
        resolve_var_bind_path_map: None,
        resolve_rep_prop_map: None,
        base_assertion_role: Id::NONE,
        base_assertion_individual: Id::NONE,
    };
    let non_det_dep =
        env.ctx
            .process_context_mut()
            .alloc_dep_node(DependencyNode::NonDeterministic {
                base,
                nd: NonDetData {
                    branch_track_points: TrackPointId::NONE,
                    clash_track_point: TrackPointId::NONE,
                    dependency_clashes: ClashDescId::NONE,
                    branch_node: BranchNodeId::NONE,
                    branch_tag: 210,
                    closing_track_point: TrackPointId::NONE,
                    closed_track_point: TrackPointId::NONE,
                },
            });
    let mut branch_tp1 = DependencyTrackPoint::new(non_det_dep);
    branch_tp1.process_tag = 210;
    let branch_tp1 = env.ctx.process_context_mut().alloc_track_point(branch_tp1);
    let mut branch_tp2 = DependencyTrackPoint::new(non_det_dep);
    branch_tp2.process_tag = 211;
    let branch_tp2 = env.ctx.process_context_mut().alloc_track_point(branch_tp2);
    env.ctx
        .process_context_mut()
        .track_point_mut(branch_tp1)
        .next = branch_tp2;
    if let DependencyNode::NonDeterministic { nd, .. } =
        env.ctx.process_context_mut().dep_node_mut(non_det_dep)
    {
        nd.branch_track_points = branch_tp1;
    }

    let current_branch_clash = clash_descriptor_for_track_point(&mut env, branch_tp1);
    let tracked_current = env.algo.create_tracked_clashes_descriptor(
        current_branch_clash,
        &mut env.ctx,
        INVALID,
        false,
    );
    let before = tracked_concept_clash(&mut env, node, concept_a, false, DepKind::And, 205, 205);
    let mut line = TrackedClashedDependencyLine::new();
    line.init_tracked_clashed_dependency_line(false, 0, 210);
    line.sort_in_tracked_clashed_descriptors(before, false, &mut env.ctx);
    let mut involved = HashSet::new();
    involved.insert(990);
    line.set_involved_individual_tracking_set(Some(involved));

    assert!(!env
        .algo
        .backtrack_non_deterministic_branching_clashed_descriptor(
            tracked_current,
            &mut line,
            &mut env.ctx,
        ));

    let branch = env.ctx.process_context().track_point(branch_tp1);
    assert!(branch.is_clashed_or_irelevant_branch());
    assert_eq!(branch.get_involved_individual_ids_linker(), &[990]);
    let copied = branch.get_clashes();
    assert_ne!(copied, Id::NONE);
    assert_ne!(copied, before);
    assert_eq!(
        env.ctx
            .process_context()
            .clash_desc(copied)
            .get_dependency_track_point(),
        env.ctx
            .process_context()
            .clash_desc(before)
            .get_dependency_track_point()
    );
    assert!(!env
        .ctx
        .process_context()
        .track_point(branch_tp2)
        .is_clashed_or_irelevant_branch());
}

#[test]
fn backtrack_non_deterministic_branching_clashed_descriptor_reinitializes_when_last_branch_closed()
{
    let mut env = build_env();
    let node = test_node_at_depth(&mut env, 99, 4);
    let concept_a = env.concept_a;
    let mut con_des = ConceptDescriptor::new();
    con_des.concept = concept_a;
    let con_des = env.ctx.process_context_mut().alloc_con_desc(con_des);
    let base_tp =
        real_dependency_track_point(&mut env, node, con_des, DepKind::IndependentBase, 220, 220);

    let base = DepNodeBase {
        process_tag: 230,
        concept_descriptor: ConDescId::NONE,
        individual_node: node,
        kind: DepKind::Or,
        dep_track_point: base_tp,
        additional_after: Id::NONE,
        selected_var_bind_path: VarBindingPathId::NONE,
        resolve_var_bind_path_map: None,
        resolve_rep_prop_map: None,
        base_assertion_role: Id::NONE,
        base_assertion_individual: Id::NONE,
    };
    let non_det_dep =
        env.ctx
            .process_context_mut()
            .alloc_dep_node(DependencyNode::NonDeterministic {
                base,
                nd: NonDetData {
                    branch_track_points: TrackPointId::NONE,
                    clash_track_point: TrackPointId::NONE,
                    dependency_clashes: ClashDescId::NONE,
                    branch_node: BranchNodeId::NONE,
                    branch_tag: 230,
                    closing_track_point: TrackPointId::NONE,
                    closed_track_point: TrackPointId::NONE,
                },
            });
    let mut branch_tp = DependencyTrackPoint::new(non_det_dep);
    branch_tp.process_tag = 230;
    let branch_tp = env.ctx.process_context_mut().alloc_track_point(branch_tp);
    if let DependencyNode::NonDeterministic { nd, .. } =
        env.ctx.process_context_mut().dep_node_mut(non_det_dep)
    {
        nd.branch_track_points = branch_tp;
    }

    let current_branch_clash = clash_descriptor_for_track_point(&mut env, branch_tp);
    let tracked_current = env.algo.create_tracked_clashes_descriptor(
        current_branch_clash,
        &mut env.ctx,
        INVALID,
        false,
    );
    let before = tracked_concept_clash(&mut env, node, concept_a, false, DepKind::And, 225, 225);
    let mut line = TrackedClashedDependencyLine::new();
    line.init_tracked_clashed_dependency_line(false, 0, 230);
    line.sort_in_tracked_clashed_descriptors(before, false, &mut env.ctx);

    assert!(env
        .algo
        .backtrack_non_deterministic_branching_clashed_descriptor(
            tracked_current,
            &mut line,
            &mut env.ctx,
        ));

    assert!(env
        .ctx
        .process_context()
        .track_point(branch_tp)
        .is_clashed_or_irelevant_branch());
    assert_eq!(env.algo.relevant_non_deterministic_decision_count, 1);
    assert!(line.has_more_tracked_clashed_list());
    let reinitialized = line.take_next_tracked_clashed_list();
    assert_ne!(reinitialized, Id::NONE);
}

#[test]
fn clashed_backtracking_drives_non_deterministic_branch_core() {
    let mut env = build_env();
    env.algo.conf_dependency_backjumping = true;
    let node = test_node_at_depth(&mut env, 100, 4);
    let concept_a = env.concept_a;
    let mut con_des = ConceptDescriptor::new();
    con_des.concept = concept_a;
    let con_des = env.ctx.process_context_mut().alloc_con_desc(con_des);
    let base_tp =
        real_dependency_track_point(&mut env, node, con_des, DepKind::IndependentBase, 240, 240);

    let base = DepNodeBase {
        process_tag: 250,
        concept_descriptor: ConDescId::NONE,
        individual_node: node,
        kind: DepKind::Or,
        dep_track_point: base_tp,
        additional_after: Id::NONE,
        selected_var_bind_path: VarBindingPathId::NONE,
        resolve_var_bind_path_map: None,
        resolve_rep_prop_map: None,
        base_assertion_role: Id::NONE,
        base_assertion_individual: Id::NONE,
    };
    let non_det_dep =
        env.ctx
            .process_context_mut()
            .alloc_dep_node(DependencyNode::NonDeterministic {
                base,
                nd: NonDetData {
                    branch_track_points: TrackPointId::NONE,
                    clash_track_point: TrackPointId::NONE,
                    dependency_clashes: ClashDescId::NONE,
                    branch_node: BranchNodeId::NONE,
                    branch_tag: 250,
                    closing_track_point: TrackPointId::NONE,
                    closed_track_point: TrackPointId::NONE,
                },
            });
    let mut branch_tp = DependencyTrackPoint::new(non_det_dep);
    branch_tp.process_tag = 250;
    let branch_tp = env.ctx.process_context_mut().alloc_track_point(branch_tp);
    if let DependencyNode::NonDeterministic { nd, .. } =
        env.ctx.process_context_mut().dep_node_mut(non_det_dep)
    {
        nd.branch_track_points = branch_tp;
    }

    let branch_clash = clash_descriptor_for_track_point(&mut env, branch_tp);

    env.algo.clashed_backtracking(branch_clash, &mut env.ctx);

    assert_eq!(
        env.ctx.processing_data_box().clashed_descriptor_linker(),
        branch_clash
    );
    assert!(env
        .ctx
        .process_context()
        .track_point(branch_tp)
        .is_clashed_or_irelevant_branch());
    assert_eq!(env.algo.relevant_non_deterministic_decision_count, 1);
}

#[test]
fn nondeterministic_track_point_branch_allocates_new_branch() {
    let mut env = build_env();
    env.algo.conf_build_dependencies = true;

    let dep_node = env.ctx.process_context_mut().alloc_or_dependency_node();
    if let DependencyNode::Or { nd, .. } = env.ctx.process_context_mut().dep_node_mut(dep_node) {
        nd.branch_tag = 4;
    }

    let track_point = env
        .algo
        .create_non_deterministic_dependency_track_point_branch(dep_node, true, &mut env.ctx);
    let branch_node = env.ctx.branch_tree_node();

    assert!(track_point.is_some());
    assert!(branch_node.is_some());
    assert_eq!(env.ctx.base.used_branch_tree_node(), branch_node);
    assert_eq!(
        env.ctx
            .process_context()
            .dep_node(dep_node)
            .branch_track_points(),
        track_point
    );
    assert_eq!(
        env.ctx
            .process_context()
            .branch_node(branch_node)
            .dependency_track_point(),
        track_point
    );
    assert_eq!(
        env.ctx
            .process_context()
            .branch_node(branch_node)
            .get_branching_level(),
        1
    );
    let tp = env.ctx.process_context().track_point(track_point);
    assert_eq!(tp.dependency_node(), dep_node);
    assert_eq!(tp.get_branch_node(), branch_node);
    assert_eq!(tp.get_branching_tag(), 4);
}

#[test]
fn nondeterministic_track_point_branch_reuses_used_branch() {
    let mut env = build_env();
    env.algo.conf_build_dependencies = true;

    let used_branch = env
        .ctx
        .process_context_mut()
        .alloc_branch_child_node(BranchNodeId::NONE, INVALID);
    env.ctx.base.used_branch_tree_node = used_branch;

    let dep_node = env
        .ctx
        .process_context_mut()
        .alloc_non_deterministic_dependency_node(DepKind::AtMost);
    if let DependencyNode::NonDeterministic { nd, .. } =
        env.ctx.process_context_mut().dep_node_mut(dep_node)
    {
        nd.branch_tag = 12;
    }

    let track_point = env
        .algo
        .create_non_deterministic_dependency_track_point_branch(dep_node, false, &mut env.ctx);

    assert!(track_point.is_some());
    assert_eq!(env.ctx.branch_tree_node(), BranchNodeId::NONE);
    assert_eq!(env.ctx.base.used_branch_tree_node(), used_branch);
    assert_eq!(
        env.ctx
            .process_context()
            .branch_node(used_branch)
            .dependency_track_point(),
        track_point
    );
    assert_eq!(
        env.ctx
            .process_context()
            .branch_node(used_branch)
            .get_branching_level(),
        1
    );
    let tp = env.ctx.process_context().track_point(track_point);
    assert_eq!(tp.get_branch_node(), used_branch);
    assert_eq!(tp.get_branching_tag(), 12);
}

#[test]
fn create_dataassertion_dependency_disabled_returns_null_and_leaves_out_track_point() {
    let mut env = build_env();
    env.algo.conf_build_dependencies = false;
    let mut process_indi = env.root;
    let mut value_dep_track_point = TrackPointId::NONE;
    let prev_dep_track_point = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
    env.ctx
        .process_context_mut()
        .track_point_mut(prev_dep_track_point)
        .add_maximum_branching_tag_candidate(31);
    env.ctx
        .process_context_mut()
        .track_point_mut(prev_dep_track_point)
        .add_maximum_branching_tag_candidate(23);
    env.ctx
        .process_context_mut()
        .track_point_mut(prev_dep_track_point)
        .add_maximum_branching_tag_candidate(19);
    env.ctx
        .process_context_mut()
        .track_point_mut(prev_dep_track_point)
        .add_maximum_branching_tag_candidate(13);

    let dep_node = env.algo.create_dataassertion_dependency(
        &mut value_dep_track_point,
        &mut process_indi,
        prev_dep_track_point,
        &mut env.ctx,
    );

    assert_eq!(dep_node, DependencyId::NONE);
    assert_eq!(value_dep_track_point, TrackPointId::NONE);
    assert_eq!(process_indi, env.root);
}

#[test]
fn create_dataassertion_dependency_allocates_factory_node_and_continue_track_point() {
    let mut env = build_env();
    env.algo.conf_build_dependencies = true;
    let mut process_indi = env.root;
    let mut value_dep_track_point = TrackPointId::NONE;
    let prev_dep_track_point = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
    env.ctx
        .process_context_mut()
        .track_point_mut(prev_dep_track_point)
        .add_maximum_branching_tag_candidate(11);

    let dep_node = env.algo.create_dataassertion_dependency(
        &mut value_dep_track_point,
        &mut process_indi,
        prev_dep_track_point,
        &mut env.ctx,
    );

    assert!(dep_node.is_some());
    assert!(value_dep_track_point.is_some());
    assert_eq!(process_indi, env.root);
    assert_eq!(
        env.ctx
            .process_context()
            .track_point(value_dep_track_point)
            .dependency_node(),
        dep_node
    );

    match env.ctx.process_context().dep_node(dep_node) {
        DependencyNode::DetLink { base, prev } => {
            assert_eq!(base.kind, DepKind::DataAssertion);
            assert_eq!(base.individual_node, env.root);
            assert_eq!(base.concept_descriptor, ConDescId::NONE);
            assert_eq!(base.dep_track_point, prev_dep_track_point);
            assert_eq!(base.process_tag, 11);
            assert_eq!(
                env.ctx.process_context().dep_link(*prev).dep_track_point,
                TrackPointId::NONE
            );
        }
        other => panic!("expected DATAASSERTION DetLink dependency, got {:?}", other),
    }
    assert_eq!(
        env.ctx
            .process_context()
            .track_point(value_dep_track_point)
            .get_branching_tag(),
        11
    );
}

#[test]
fn create_merged_concept_dependency_preserves_guard() {
    let mut env = build_env();
    let mut process_indi = env.root;
    let mut continue_dep_track_point = TrackPointId::NONE;
    let merge_prev_dep_track_point = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
    let concept_prev_dep_track_point = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
    let con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());

    env.algo.conf_build_dependencies = false;
    let dep_node = env.algo.create_merged_concept_dependency(
        &mut continue_dep_track_point,
        &mut process_indi,
        con_des,
        merge_prev_dep_track_point,
        concept_prev_dep_track_point,
        &mut env.ctx,
    );

    assert_eq!(dep_node, DependencyId::NONE);
    assert_eq!(continue_dep_track_point, TrackPointId::NONE);
    assert_eq!(process_indi, env.root);
}

#[test]
fn create_merged_concept_dependency_allocates_det_link_factory_shape() {
    let mut env = build_env();
    let mut process_indi = env.root;
    let mut continue_dep_track_point = TrackPointId::NONE;
    let merge_prev_dep_track_point = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
    env.ctx
        .process_context_mut()
        .track_point_mut(merge_prev_dep_track_point)
        .add_maximum_branching_tag_candidate(17);
    let concept_prev_dep_track_point = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
    env.ctx
        .process_context_mut()
        .track_point_mut(concept_prev_dep_track_point)
        .add_maximum_branching_tag_candidate(23);
    let mut con_desc = ConceptDescriptor::new();
    con_desc.concept = env.concept_a;
    con_desc.negated = false;
    let con_des = env.ctx.process_context_mut().alloc_con_desc(con_desc);

    env.algo.conf_build_dependencies = true;
    let dep_node = env.algo.create_merged_concept_dependency(
        &mut continue_dep_track_point,
        &mut process_indi,
        con_des,
        merge_prev_dep_track_point,
        concept_prev_dep_track_point,
        &mut env.ctx,
    );

    assert!(dep_node.is_some());
    assert!(continue_dep_track_point.is_some());
    assert_eq!(process_indi, env.root);
    assert_eq!(
        env.ctx
            .process_context()
            .track_point(continue_dep_track_point)
            .dependency_node(),
        dep_node
    );

    match env.ctx.process_context().dep_node(dep_node) {
        DependencyNode::DetLink { base, prev } => {
            assert_eq!(base.kind, DepKind::MergedConcept);
            assert_eq!(base.individual_node, NodeId::NONE);
            assert_eq!(base.concept_descriptor, con_des);
            assert_eq!(base.dep_track_point, concept_prev_dep_track_point);
            assert_eq!(base.process_tag, 23);
            assert_eq!(
                env.ctx.process_context().dep_link(*prev).dep_track_point,
                merge_prev_dep_track_point
            );
        }
        other => panic!("expected MERGEDCONCEPT DetLink dependency, got {:?}", other),
    }
    assert_eq!(
        env.ctx
            .process_context()
            .track_point(continue_dep_track_point)
            .get_branching_tag(),
        23
    );
}

#[test]
fn create_atmost_dependency_allocates_factory_shaped_non_det_node() {
    let mut env = build_env();
    env.algo.conf_build_dependencies = true;
    let mut process_indi = env.root;
    let con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    let prev_dep_track_point = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
    env.ctx
        .process_context_mut()
        .track_point_mut(prev_dep_track_point)
        .add_maximum_branching_tag_candidate(13);
    let used_branch = env
        .ctx
        .process_context_mut()
        .alloc_branch_child_node(BranchNodeId::NONE, INVALID);
    env.ctx.base.used_branch_tree_node = used_branch;

    let dep_node = env.algo.create_atmost_dependency(
        &mut process_indi,
        con_des,
        prev_dep_track_point,
        &mut env.ctx,
    );

    assert!(dep_node.is_some());
    assert_eq!(process_indi, env.root);
    match env.ctx.process_context().dep_node(dep_node) {
        DependencyNode::NonDeterministic { base, nd } => {
            assert_eq!(base.kind, DepKind::AtMost);
            assert_eq!(base.individual_node, env.root);
            assert_eq!(base.concept_descriptor, con_des);
            assert_eq!(base.dep_track_point, prev_dep_track_point);
            assert_eq!(nd.branch_track_points, nd.clash_track_point);
            assert_eq!(nd.branch_node, used_branch);
            assert_eq!(nd.branch_tag, 13);
            assert_eq!(nd.closed_track_point, TrackPointId::NONE);
            assert_eq!(nd.closing_track_point, TrackPointId::NONE);
            assert_eq!(nd.dependency_clashes, ClashDescId::NONE);
            assert!(env
                .ctx
                .process_context()
                .track_point(nd.clash_track_point)
                .is_clashed_or_irelevant_branch());
            assert_eq!(
                env.ctx
                    .process_context()
                    .track_point(nd.clash_track_point)
                    .get_branching_tag(),
                13
            );
        }
        other => panic!(
            "expected ATMOST non-deterministic dependency, got {:?}",
            other
        ),
    }
}

#[test]
fn create_qualify_dependency_preserves_guard_and_allocates_factory_shaped_non_det_node() {
    let mut env = build_env();
    let mut process_indi = env.root;
    let con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    let prev_dep_track_point = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
    env.ctx
        .process_context_mut()
        .track_point_mut(prev_dep_track_point)
        .add_maximum_branching_tag_candidate(17);
    let used_branch = env
        .ctx
        .process_context_mut()
        .alloc_branch_child_node(BranchNodeId::NONE, INVALID);
    env.ctx.base.used_branch_tree_node = used_branch;

    env.algo.conf_build_dependencies = false;
    let disabled_dep = env.algo.create_qualify_dependency(
        &mut process_indi,
        con_des,
        prev_dep_track_point,
        &mut env.ctx,
    );
    assert_eq!(disabled_dep, DependencyId::NONE);
    assert_eq!(process_indi, env.root);

    env.algo.conf_build_dependencies = true;
    let dep_node = env.algo.create_qualify_dependency(
        &mut process_indi,
        con_des,
        prev_dep_track_point,
        &mut env.ctx,
    );

    assert!(dep_node.is_some());
    assert_eq!(process_indi, env.root);
    match env.ctx.process_context().dep_node(dep_node) {
        DependencyNode::NonDeterministic { base, nd } => {
            assert_eq!(base.kind, DepKind::Qualify);
            assert_eq!(base.individual_node, env.root);
            assert_eq!(base.concept_descriptor, con_des);
            assert_eq!(base.dep_track_point, prev_dep_track_point);
            assert_eq!(nd.branch_track_points, nd.clash_track_point);
            assert_eq!(nd.branch_node, used_branch);
            assert_eq!(nd.branch_tag, 17);
            assert_eq!(nd.closed_track_point, TrackPointId::NONE);
            assert_eq!(nd.closing_track_point, TrackPointId::NONE);
            assert_eq!(nd.dependency_clashes, ClashDescId::NONE);
            assert!(env
                .ctx
                .process_context()
                .track_point(nd.clash_track_point)
                .is_clashed_or_irelevant_branch());
            assert_eq!(
                env.ctx
                    .process_context()
                    .track_point(nd.clash_track_point)
                    .get_branching_tag(),
                17
            );
        }
        other => panic!(
            "expected QUALIFY non-deterministic dependency, got {:?}",
            other
        ),
    }
}

fn assert_factory_shaped_non_det_dependency(
    env: &SelfTestEnv,
    dep_node: DependencyId,
    expected_kind: DepKind,
    expected_indi: NodeId,
    expected_con_des: ConDescId,
    expected_prev_dep_track_point: TrackPointId,
    expected_branch: BranchNodeId,
    expected_branch_tag: i64,
) {
    assert!(dep_node.is_some());
    match env.ctx.process_context().dep_node(dep_node) {
        DependencyNode::NonDeterministic { base, nd } => {
            assert_eq!(base.kind, expected_kind);
            assert_eq!(base.individual_node, expected_indi);
            assert_eq!(base.concept_descriptor, expected_con_des);
            assert_eq!(base.dep_track_point, expected_prev_dep_track_point);
            assert_eq!(nd.branch_track_points, nd.clash_track_point);
            assert_eq!(nd.branch_node, expected_branch);
            assert_eq!(nd.branch_tag, expected_branch_tag);
            assert_eq!(nd.closed_track_point, TrackPointId::NONE);
            assert_eq!(nd.closing_track_point, TrackPointId::NONE);
            assert_eq!(nd.dependency_clashes, ClashDescId::NONE);
            assert!(env
                .ctx
                .process_context()
                .track_point(nd.clash_track_point)
                .is_clashed_or_irelevant_branch());
            assert_eq!(
                env.ctx
                    .process_context()
                    .track_point(nd.clash_track_point)
                    .dependency_node(),
                dep_node
            );
            assert_eq!(
                env.ctx
                    .process_context()
                    .track_point(nd.clash_track_point)
                    .get_branching_tag(),
                expected_branch_tag
            );
        }
        other => panic!(
            "expected {:?} non-deterministic dependency, got {:?}",
            expected_kind, other
        ),
    }
}

#[test]
fn create_reuse_dependency_wrappers_allocate_factory_shaped_non_det_nodes() {
    let mut env = build_env();
    env.algo.conf_build_dependencies = true;
    let mut process_indi = env.root;
    let con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    let prev_dep_track_point = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
    env.ctx
        .process_context_mut()
        .track_point_mut(prev_dep_track_point)
        .add_maximum_branching_tag_candidate(19);
    let used_branch = env
        .ctx
        .process_context_mut()
        .alloc_branch_child_node(BranchNodeId::NONE, INVALID);
    env.ctx.base.used_branch_tree_node = used_branch;

    let reuse_individual_dep = env.algo.create_reuse_individual_dependency(
        process_indi,
        con_des,
        prev_dep_track_point,
        &mut env.ctx,
    );
    assert_factory_shaped_non_det_dependency(
        &env,
        reuse_individual_dep,
        DepKind::ReuseIndividual,
        env.root,
        con_des,
        prev_dep_track_point,
        used_branch,
        19,
    );

    let reuse_completion_graph_dep = env.algo.create_reuse_completion_graph_dependency(
        &mut process_indi,
        con_des,
        prev_dep_track_point,
        &mut env.ctx,
    );
    assert_eq!(process_indi, env.root);
    assert_factory_shaped_non_det_dependency(
        &env,
        reuse_completion_graph_dep,
        DepKind::ReuseCompletionGraph,
        env.root,
        con_des,
        prev_dep_track_point,
        used_branch,
        19,
    );

    let reuse_concepts_dep = env.algo.create_reuse_concepts_dependency(
        process_indi,
        con_des,
        prev_dep_track_point,
        &mut env.ctx,
    );
    assert_factory_shaped_non_det_dependency(
        &env,
        reuse_concepts_dep,
        DepKind::ReuseConcepts,
        env.root,
        con_des,
        prev_dep_track_point,
        used_branch,
        19,
    );
}

#[test]
fn create_reuse_dependency_wrappers_preserve_build_dependencies_guard() {
    let mut env = build_env();
    env.algo.conf_build_dependencies = false;
    let mut process_indi = env.root;
    let con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    let prev_dep_track_point = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));

    assert_eq!(
        env.algo.create_reuse_individual_dependency(
            process_indi,
            con_des,
            prev_dep_track_point,
            &mut env.ctx,
        ),
        DependencyId::NONE
    );
    assert_eq!(
        env.algo.create_reuse_completion_graph_dependency(
            &mut process_indi,
            con_des,
            prev_dep_track_point,
            &mut env.ctx,
        ),
        DependencyId::NONE
    );
    assert_eq!(process_indi, env.root);
    assert_eq!(
        env.algo.create_reuse_concepts_dependency(
            process_indi,
            con_des,
            prev_dep_track_point,
            &mut env.ctx,
        ),
        DependencyId::NONE
    );
}

fn make_dependency_link(
    env: &mut SelfTestEnv,
    dep_track_point: TrackPointId,
    next: DepLinkId,
) -> DepLinkId {
    let link = env
        .ctx
        .process_context_mut()
        .alloc_dep_link(DependencyLink::new());
    let dep_link = env.ctx.process_context_mut().dep_link_mut(link);
    dep_link.init_dependency(dep_track_point);
    dep_link.next = next;
    link
}

fn assert_factory_shaped_deterministic_dependency(
    env: &SelfTestEnv,
    dep_node: DependencyId,
    continue_track_point: TrackPointId,
    expected_kind: DepKind,
    expected_con_des: ConDescId,
    expected_prev_dep_track_point: TrackPointId,
    expected_additional_after: DepLinkId,
) {
    assert!(dep_node.is_some());
    assert!(continue_track_point.is_some());
    assert_eq!(
        env.ctx
            .process_context()
            .track_point(continue_track_point)
            .dependency_node(),
        dep_node
    );
    match env.ctx.process_context().dep_node(dep_node) {
        DependencyNode::Deterministic { base } => {
            assert_eq!(base.kind, expected_kind);
            assert_eq!(base.individual_node, NodeId::NONE);
            assert_eq!(base.concept_descriptor, expected_con_des);
            assert_eq!(base.dep_track_point, expected_prev_dep_track_point);
            assert_eq!(base.additional_after, expected_additional_after);
        }
        other => panic!(
            "expected {:?} deterministic dependency, got {:?}",
            expected_kind, other
        ),
    }
}

fn assert_process_shaped_deterministic_dependency(
    env: &SelfTestEnv,
    dep_node: DependencyId,
    expected_kind: DepKind,
    expected_indi: NodeId,
    expected_con_des: ConDescId,
    expected_prev_dep_track_point: TrackPointId,
) {
    assert!(dep_node.is_some());
    match env.ctx.process_context().dep_node(dep_node) {
        DependencyNode::Deterministic { base } => {
            assert_eq!(base.kind, expected_kind);
            assert_eq!(base.individual_node, expected_indi);
            assert_eq!(base.concept_descriptor, expected_con_des);
            assert_eq!(base.dep_track_point, expected_prev_dep_track_point);
            assert_eq!(base.additional_after, DepLinkId::NONE);
        }
        other => panic!(
            "expected {:?} process-shaped deterministic dependency, got {:?}",
            expected_kind, other
        ),
    }
}

fn assert_factory_shaped_det_link_dependency(
    env: &SelfTestEnv,
    dep_node: DependencyId,
    continue_track_point: TrackPointId,
    expected_kind: DepKind,
    expected_indi: NodeId,
    expected_con_des: ConDescId,
    expected_prev_dep_track_point: TrackPointId,
    expected_link_dep_track_point: TrackPointId,
) {
    assert!(dep_node.is_some());
    assert!(continue_track_point.is_some());
    assert_eq!(
        env.ctx
            .process_context()
            .track_point(continue_track_point)
            .dependency_node(),
        dep_node
    );
    match env.ctx.process_context().dep_node(dep_node) {
        DependencyNode::DetLink { base, prev } => {
            assert_eq!(base.kind, expected_kind);
            assert_eq!(base.individual_node, expected_indi);
            assert_eq!(base.concept_descriptor, expected_con_des);
            assert_eq!(base.dep_track_point, expected_prev_dep_track_point);
            assert_eq!(
                env.ctx.process_context().dep_link(*prev).dep_track_point,
                expected_link_dep_track_point
            );
        }
        other => panic!(
            "expected {:?} DetLink dependency, got {:?}",
            expected_kind, other
        ),
    }
}

#[test]
fn create_oronly_implication_expanded_dependencies_preserve_factory_shapes() {
    let mut env = build_env();
    env.algo.conf_build_dependencies = true;
    let mut process_indi = env.root;
    let con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    let prev_dep_track_point = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
    let additional_tp = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
    let prev_other_dependencies = make_dependency_link(&mut env, additional_tp, DepLinkId::NONE);

    let mut or_continue = TrackPointId::NONE;
    let or_dep = env.algo.create_oronly_option_dependency(
        &mut or_continue,
        &mut process_indi,
        con_des,
        prev_dep_track_point,
        prev_other_dependencies,
        &mut env.ctx,
    );
    assert_eq!(process_indi, env.root);
    assert_factory_shaped_deterministic_dependency(
        &env,
        or_dep,
        or_continue,
        DepKind::OrOnlyOption,
        con_des,
        prev_dep_track_point,
        prev_other_dependencies,
    );

    let mut impl_continue = TrackPointId::NONE;
    let impl_dep = env.algo.create_implication_dependency(
        &mut impl_continue,
        &mut process_indi,
        con_des,
        prev_dep_track_point,
        prev_other_dependencies,
        &mut env.ctx,
    );
    assert_eq!(process_indi, env.root);
    assert_factory_shaped_deterministic_dependency(
        &env,
        impl_dep,
        impl_continue,
        DepKind::Implication,
        con_des,
        prev_dep_track_point,
        prev_other_dependencies,
    );

    let mut expanded_continue = TrackPointId::NONE;
    let expanded_dep = env.algo.create_expanded_dependency(
        &mut expanded_continue,
        &mut process_indi,
        prev_dep_track_point,
        prev_other_dependencies,
        &mut env.ctx,
    );
    assert_eq!(process_indi, env.root);
    assert_factory_shaped_deterministic_dependency(
        &env,
        expanded_dep,
        expanded_continue,
        DepKind::Expanded,
        ConDescId::NONE,
        prev_dep_track_point,
        prev_other_dependencies,
    );
    assert_eq!(
        env.ctx
            .process_context()
            .dep_link(prev_other_dependencies)
            .dep_track_point,
        additional_tp
    );
}

#[test]
fn create_oronly_implication_expanded_dependencies_preserve_build_dependencies_guard() {
    let mut env = build_env();
    env.algo.conf_build_dependencies = false;
    let mut process_indi = env.root;
    let con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    let prev_dep_track_point = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
    let additional_tp = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
    let prev_other_dependencies = make_dependency_link(&mut env, additional_tp, DepLinkId::NONE);

    let mut or_continue = TrackPointId::NONE;
    assert_eq!(
        env.algo.create_oronly_option_dependency(
            &mut or_continue,
            &mut process_indi,
            con_des,
            prev_dep_track_point,
            prev_other_dependencies,
            &mut env.ctx,
        ),
        DependencyId::NONE
    );
    assert_eq!(or_continue, TrackPointId::NONE);
    assert_eq!(process_indi, env.root);

    let mut impl_continue = TrackPointId::NONE;
    assert_eq!(
        env.algo.create_implication_dependency(
            &mut impl_continue,
            &mut process_indi,
            con_des,
            prev_dep_track_point,
            prev_other_dependencies,
            &mut env.ctx,
        ),
        DependencyId::NONE
    );
    assert_eq!(impl_continue, TrackPointId::NONE);
    assert_eq!(process_indi, env.root);

    let mut expanded_continue = TrackPointId::NONE;
    assert_eq!(
        env.algo.create_expanded_dependency(
            &mut expanded_continue,
            &mut process_indi,
            prev_dep_track_point,
            prev_other_dependencies,
            &mut env.ctx,
        ),
        DependencyId::NONE
    );
    assert_eq!(expanded_continue, TrackPointId::NONE);
    assert_eq!(process_indi, env.root);
}

#[test]
fn create_varbind_and_propagate_dependency_wrappers_preserve_factory_shapes() {
    let mut env = build_env();
    env.algo.conf_build_dependencies = true;
    let mut process_indi = env.root;
    let con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    let prev_dep_track_point = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
    let link_dep_track_point = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
    let additional_tp = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
    let prev_other_dependencies = make_dependency_link(&mut env, additional_tp, DepLinkId::NONE);

    let prop_var_conn_dep = env.algo.create_propagate_variable_connection_dependency(
        process_indi,
        con_des,
        prev_dep_track_point,
        &mut env.ctx,
    );
    assert_process_shaped_deterministic_dependency(
        &env,
        prop_var_conn_dep,
        DepKind::PropagateVariableConnection,
        env.root,
        con_des,
        prev_dep_track_point,
    );

    let mut varbind_impl_continue = TrackPointId::NONE;
    let varbind_impl_dep = env.algo.create_varbind_propagate_implication_dependency(
        &mut varbind_impl_continue,
        &mut process_indi,
        con_des,
        prev_dep_track_point,
        prev_other_dependencies,
        &mut env.ctx,
    );
    assert_factory_shaped_deterministic_dependency(
        &env,
        varbind_impl_dep,
        varbind_impl_continue,
        DepKind::VarBindPropagateImplication,
        con_des,
        prev_dep_track_point,
        prev_other_dependencies,
    );

    let mut varbind_all_continue = TrackPointId::NONE;
    let varbind_all_dep = env.algo.create_varbind_propagate_all_dependency(
        &mut varbind_all_continue,
        &mut process_indi,
        con_des,
        prev_dep_track_point,
        link_dep_track_point,
        &mut env.ctx,
    );
    assert_factory_shaped_det_link_dependency(
        &env,
        varbind_all_dep,
        varbind_all_continue,
        DepKind::VarBindPropagateAll,
        env.root,
        con_des,
        prev_dep_track_point,
        link_dep_track_point,
    );

    let mut varbind_and_continue = TrackPointId::NONE;
    let varbind_and_dep = env.algo.create_varbind_propagate_and_dependency(
        &mut varbind_and_continue,
        &mut process_indi,
        con_des,
        prev_dep_track_point,
        &mut env.ctx,
    );
    assert_factory_shaped_deterministic_dependency(
        &env,
        varbind_and_dep,
        varbind_and_continue,
        DepKind::VarBindPropagateAnd,
        con_des,
        prev_dep_track_point,
        DepLinkId::NONE,
    );

    let mut prop_var_binding_continue = TrackPointId::NONE;
    let prop_var_binding_dep = env.algo.create_propagate_variable_binding_dependency(
        &mut prop_var_binding_continue,
        &mut process_indi,
        con_des,
        prev_dep_track_point,
        prev_other_dependencies,
        &mut env.ctx,
    );
    assert_factory_shaped_deterministic_dependency(
        &env,
        prop_var_binding_dep,
        prop_var_binding_continue,
        DepKind::PropagateVariableBinding,
        con_des,
        prev_dep_track_point,
        prev_other_dependencies,
    );

    let mut prop_var_binding_succ_continue = TrackPointId::NONE;
    let prop_var_binding_succ_dep = env
        .algo
        .create_propagate_variable_bindings_successor_dependency(
            &mut prop_var_binding_succ_continue,
            &mut process_indi,
            con_des,
            prev_dep_track_point,
            link_dep_track_point,
            &mut env.ctx,
        );
    assert_factory_shaped_det_link_dependency(
        &env,
        prop_var_binding_succ_dep,
        prop_var_binding_succ_continue,
        DepKind::PropagateVariableBindingSuccessor,
        env.root,
        con_des,
        prev_dep_track_point,
        link_dep_track_point,
    );

    let mut varbind_variable_continue = TrackPointId::NONE;
    let varbind_variable_dep = env.algo.create_varbind_variable_dependency(
        &mut varbind_variable_continue,
        &mut process_indi,
        con_des,
        prev_dep_track_point,
        &mut env.ctx,
    );
    assert_factory_shaped_deterministic_dependency(
        &env,
        varbind_variable_dep,
        varbind_variable_continue,
        DepKind::VarBindVariable,
        con_des,
        prev_dep_track_point,
        DepLinkId::NONE,
    );

    let mut varbind_join_continue = TrackPointId::NONE;
    let varbind_join_dep = env.algo.create_varbind_propagate_join_dependency(
        &mut varbind_join_continue,
        &mut process_indi,
        con_des,
        prev_dep_track_point,
        link_dep_track_point,
        &mut env.ctx,
    );
    assert_factory_shaped_det_link_dependency(
        &env,
        varbind_join_dep,
        varbind_join_continue,
        DepKind::VarBindPropagateJoin,
        NodeId::NONE,
        con_des,
        prev_dep_track_point,
        link_dep_track_point,
    );

    let mut bind_ground_continue = TrackPointId::NONE;
    let bind_ground_dep = env.algo.create_bind_propagate_grounding_dependency(
        &mut bind_ground_continue,
        &mut process_indi,
        con_des,
        prev_dep_track_point,
        prev_other_dependencies,
        &mut env.ctx,
    );
    assert_factory_shaped_deterministic_dependency(
        &env,
        bind_ground_dep,
        bind_ground_continue,
        DepKind::BindPropagateGrounding,
        con_des,
        prev_dep_track_point,
        prev_other_dependencies,
    );

    let conn_away_dep = env.algo.create_propagate_connection_away_dependency(
        process_indi,
        con_des,
        prev_dep_track_point,
        &mut env.ctx,
    );
    assert_process_shaped_deterministic_dependency(
        &env,
        conn_away_dep,
        DepKind::PropagateConnectionAway,
        env.root,
        con_des,
        prev_dep_track_point,
    );

    let conn_dep = env.algo.create_propagate_connection_dependency(
        process_indi,
        con_des,
        prev_dep_track_point,
        &mut env.ctx,
    );
    assert_process_shaped_deterministic_dependency(
        &env,
        conn_dep,
        DepKind::PropagateConnection,
        env.root,
        con_des,
        prev_dep_track_point,
    );
    assert_eq!(process_indi, env.root);
}

#[test]
fn create_varbind_and_propagate_dependency_wrappers_preserve_build_dependencies_guard() {
    let mut env = build_env();
    env.algo.conf_build_dependencies = false;
    let mut process_indi = env.root;
    let con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    let prev_dep_track_point = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
    let link_dep_track_point = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
    let additional_tp = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
    let prev_other_dependencies = make_dependency_link(&mut env, additional_tp, DepLinkId::NONE);

    assert_eq!(
        env.algo.create_propagate_variable_connection_dependency(
            process_indi,
            con_des,
            prev_dep_track_point,
            &mut env.ctx,
        ),
        DependencyId::NONE
    );

    let mut cont = TrackPointId::NONE;
    assert_eq!(
        env.algo.create_varbind_propagate_implication_dependency(
            &mut cont,
            &mut process_indi,
            con_des,
            prev_dep_track_point,
            prev_other_dependencies,
            &mut env.ctx,
        ),
        DependencyId::NONE
    );
    assert_eq!(cont, TrackPointId::NONE);

    assert_eq!(
        env.algo.create_varbind_propagate_all_dependency(
            &mut cont,
            &mut process_indi,
            con_des,
            prev_dep_track_point,
            link_dep_track_point,
            &mut env.ctx,
        ),
        DependencyId::NONE
    );
    assert_eq!(cont, TrackPointId::NONE);

    assert_eq!(
        env.algo.create_varbind_propagate_and_dependency(
            &mut cont,
            &mut process_indi,
            con_des,
            prev_dep_track_point,
            &mut env.ctx,
        ),
        DependencyId::NONE
    );
    assert_eq!(cont, TrackPointId::NONE);

    assert_eq!(
        env.algo.create_propagate_variable_binding_dependency(
            &mut cont,
            &mut process_indi,
            con_des,
            prev_dep_track_point,
            prev_other_dependencies,
            &mut env.ctx,
        ),
        DependencyId::NONE
    );
    assert_eq!(cont, TrackPointId::NONE);

    assert_eq!(
        env.algo
            .create_propagate_variable_bindings_successor_dependency(
                &mut cont,
                &mut process_indi,
                con_des,
                prev_dep_track_point,
                link_dep_track_point,
                &mut env.ctx,
            ),
        DependencyId::NONE
    );
    assert_eq!(cont, TrackPointId::NONE);

    assert_eq!(
        env.algo.create_varbind_variable_dependency(
            &mut cont,
            &mut process_indi,
            con_des,
            prev_dep_track_point,
            &mut env.ctx,
        ),
        DependencyId::NONE
    );
    assert_eq!(cont, TrackPointId::NONE);

    assert_eq!(
        env.algo.create_varbind_propagate_join_dependency(
            &mut cont,
            &mut process_indi,
            con_des,
            prev_dep_track_point,
            link_dep_track_point,
            &mut env.ctx,
        ),
        DependencyId::NONE
    );
    assert_eq!(cont, TrackPointId::NONE);

    assert_eq!(
        env.algo.create_bind_propagate_grounding_dependency(
            &mut cont,
            &mut process_indi,
            con_des,
            prev_dep_track_point,
            prev_other_dependencies,
            &mut env.ctx,
        ),
        DependencyId::NONE
    );
    assert_eq!(cont, TrackPointId::NONE);

    assert_eq!(
        env.algo.create_propagate_connection_away_dependency(
            process_indi,
            con_des,
            prev_dep_track_point,
            &mut env.ctx,
        ),
        DependencyId::NONE
    );
    assert_eq!(
        env.algo.create_propagate_connection_dependency(
            process_indi,
            con_des,
            prev_dep_track_point,
            &mut env.ctx,
        ),
        DependencyId::NONE
    );
    assert_eq!(process_indi, env.root);
}

#[test]
fn create_bind_propagate_and_nominal_dependencies_preserve_factory_shapes() {
    let mut env = build_env();
    env.algo.conf_build_dependencies = true;
    let mut process_indi = env.root;
    let con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    let prev_dep_track_point = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
    let link_dep_track_point = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
    let trigger_dep_track_point = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
    let nominal_dep_track_point = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
    let additional_tp = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
    let prev_other_dependencies = make_dependency_link(&mut env, additional_tp, DepLinkId::NONE);

    let mut cycle_continue = TrackPointId::NONE;
    let cycle_dep = env.algo.create_bind_propagate_cycle_dependency(
        &mut cycle_continue,
        &mut process_indi,
        con_des,
        prev_dep_track_point,
        trigger_dep_track_point,
        &mut env.ctx,
    );
    assert_factory_shaped_det_link_dependency(
        &env,
        cycle_dep,
        cycle_continue,
        DepKind::BindPropagateCycle,
        NodeId::NONE,
        con_des,
        prev_dep_track_point,
        trigger_dep_track_point,
    );

    let mut bind_all_continue = TrackPointId::NONE;
    let bind_all_dep = env.algo.create_bind_propagate_all_dependency(
        &mut bind_all_continue,
        &mut process_indi,
        con_des,
        prev_dep_track_point,
        link_dep_track_point,
        &mut env.ctx,
    );
    assert_factory_shaped_det_link_dependency(
        &env,
        bind_all_dep,
        bind_all_continue,
        DepKind::BindPropagateAll,
        env.root,
        con_des,
        prev_dep_track_point,
        link_dep_track_point,
    );

    let mut prop_binding_succ_continue = TrackPointId::NONE;
    let prop_binding_succ_dep = env.algo.create_propagate_bindings_successor_dependency(
        &mut prop_binding_succ_continue,
        &mut process_indi,
        con_des,
        prev_dep_track_point,
        link_dep_track_point,
        &mut env.ctx,
    );
    assert_factory_shaped_det_link_dependency(
        &env,
        prop_binding_succ_dep,
        prop_binding_succ_continue,
        DepKind::PropagateBindingSuccessor,
        env.root,
        con_des,
        prev_dep_track_point,
        link_dep_track_point,
    );

    let mut bind_impl_continue = TrackPointId::NONE;
    let bind_impl_dep = env.algo.create_bind_propagate_implication_dependency(
        &mut bind_impl_continue,
        &mut process_indi,
        con_des,
        prev_dep_track_point,
        prev_other_dependencies,
        &mut env.ctx,
    );
    assert_factory_shaped_deterministic_dependency(
        &env,
        bind_impl_dep,
        bind_impl_continue,
        DepKind::BindPropagateImplication,
        con_des,
        prev_dep_track_point,
        prev_other_dependencies,
    );

    let mut bind_and_continue = TrackPointId::NONE;
    let bind_and_dep = env.algo.create_bind_propagate_and_dependency(
        &mut bind_and_continue,
        &mut process_indi,
        con_des,
        prev_dep_track_point,
        &mut env.ctx,
    );
    assert_factory_shaped_deterministic_dependency(
        &env,
        bind_and_dep,
        bind_and_continue,
        DepKind::BindPropagateAnd,
        con_des,
        prev_dep_track_point,
        DepLinkId::NONE,
    );

    let mut prop_binding_continue = TrackPointId::NONE;
    let prop_binding_dep = env.algo.create_propagate_binding_dependency(
        &mut prop_binding_continue,
        &mut process_indi,
        con_des,
        prev_dep_track_point,
        prev_other_dependencies,
        &mut env.ctx,
    );
    assert_factory_shaped_deterministic_dependency(
        &env,
        prop_binding_dep,
        prop_binding_continue,
        DepKind::PropagateBinding,
        con_des,
        prev_dep_track_point,
        prev_other_dependencies,
    );

    let mut bind_variable_continue = TrackPointId::NONE;
    let bind_variable_dep = env.algo.create_bind_variable_dependency(
        &mut bind_variable_continue,
        &mut process_indi,
        con_des,
        prev_dep_track_point,
        &mut env.ctx,
    );
    assert_factory_shaped_deterministic_dependency(
        &env,
        bind_variable_dep,
        bind_variable_continue,
        DepKind::BindVariable,
        con_des,
        prev_dep_track_point,
        DepLinkId::NONE,
    );

    let mut nominal_continue = TrackPointId::NONE;
    let nominal_dep = env.algo.create_nominal_dependency(
        &mut nominal_continue,
        &mut process_indi,
        con_des,
        prev_dep_track_point,
        nominal_dep_track_point,
        &mut env.ctx,
    );
    assert_factory_shaped_det_link_dependency(
        &env,
        nominal_dep,
        nominal_continue,
        DepKind::Nominal,
        env.root,
        con_des,
        prev_dep_track_point,
        nominal_dep_track_point,
    );
    assert_eq!(process_indi, env.root);
}

#[test]
fn create_bind_propagate_and_nominal_dependencies_preserve_build_dependencies_guard() {
    let mut env = build_env();
    env.algo.conf_build_dependencies = false;
    let mut process_indi = env.root;
    let con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    let prev_dep_track_point = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
    let link_dep_track_point = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
    let trigger_dep_track_point = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
    let nominal_dep_track_point = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
    let additional_tp = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
    let prev_other_dependencies = make_dependency_link(&mut env, additional_tp, DepLinkId::NONE);
    let mut cont = TrackPointId::NONE;

    assert_eq!(
        env.algo.create_bind_propagate_cycle_dependency(
            &mut cont,
            &mut process_indi,
            con_des,
            prev_dep_track_point,
            trigger_dep_track_point,
            &mut env.ctx,
        ),
        DependencyId::NONE
    );
    assert_eq!(cont, TrackPointId::NONE);

    assert_eq!(
        env.algo.create_bind_propagate_all_dependency(
            &mut cont,
            &mut process_indi,
            con_des,
            prev_dep_track_point,
            link_dep_track_point,
            &mut env.ctx,
        ),
        DependencyId::NONE
    );
    assert_eq!(cont, TrackPointId::NONE);

    assert_eq!(
        env.algo.create_propagate_bindings_successor_dependency(
            &mut cont,
            &mut process_indi,
            con_des,
            prev_dep_track_point,
            link_dep_track_point,
            &mut env.ctx,
        ),
        DependencyId::NONE
    );
    assert_eq!(cont, TrackPointId::NONE);

    assert_eq!(
        env.algo.create_bind_propagate_implication_dependency(
            &mut cont,
            &mut process_indi,
            con_des,
            prev_dep_track_point,
            prev_other_dependencies,
            &mut env.ctx,
        ),
        DependencyId::NONE
    );
    assert_eq!(cont, TrackPointId::NONE);

    assert_eq!(
        env.algo.create_bind_propagate_and_dependency(
            &mut cont,
            &mut process_indi,
            con_des,
            prev_dep_track_point,
            &mut env.ctx,
        ),
        DependencyId::NONE
    );
    assert_eq!(cont, TrackPointId::NONE);

    assert_eq!(
        env.algo.create_propagate_binding_dependency(
            &mut cont,
            &mut process_indi,
            con_des,
            prev_dep_track_point,
            prev_other_dependencies,
            &mut env.ctx,
        ),
        DependencyId::NONE
    );
    assert_eq!(cont, TrackPointId::NONE);

    assert_eq!(
        env.algo.create_bind_variable_dependency(
            &mut cont,
            &mut process_indi,
            con_des,
            prev_dep_track_point,
            &mut env.ctx,
        ),
        DependencyId::NONE
    );
    assert_eq!(cont, TrackPointId::NONE);

    assert_eq!(
        env.algo.create_nominal_dependency(
            &mut cont,
            &mut process_indi,
            con_des,
            prev_dep_track_point,
            nominal_dep_track_point,
            &mut env.ctx,
        ),
        DependencyId::NONE
    );
    assert_eq!(cont, TrackPointId::NONE);
    assert_eq!(process_indi, env.root);
}

#[test]
fn create_reuse_backend_dependency_wrappers_preserve_factory_shapes() {
    let mut env = build_env();
    env.algo.conf_build_dependencies = true;
    let mut process_indi = env.root;
    let con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    let prev_dep_track_point = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
    env.ctx
        .process_context_mut()
        .track_point_mut(prev_dep_track_point)
        .add_maximum_branching_tag_candidate(23);
    let nominal_dep_track_point = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
    let used_branch = env
        .ctx
        .process_context_mut()
        .alloc_branch_child_node(BranchNodeId::NONE, INVALID);
    env.ctx.base.used_branch_tree_node = used_branch;

    let modes_dep = env
        .algo
        .create_reuse_backend_expansion_modes_dependency(prev_dep_track_point, &mut env.ctx);
    assert!(modes_dep.is_some());
    match env.ctx.process_context().dep_node(modes_dep) {
        DependencyNode::ReuseBackendModes {
            base,
            nd,
            fixed_reuse_dep_track_point,
            priorized_reuse_dep_track_point,
            involved,
            affected,
        } => {
            assert_eq!(base.kind, DepKind::ReuseBackendExpansionModes);
            assert_eq!(base.individual_node, NodeId::NONE);
            assert_eq!(base.concept_descriptor, ConDescId::NONE);
            assert_eq!(base.dep_track_point, prev_dep_track_point);
            assert_eq!(nd.branch_track_points, nd.clash_track_point);
            assert_eq!(nd.branch_node, used_branch);
            assert_eq!(nd.branch_tag, 23);
            assert_eq!(nd.closed_track_point, TrackPointId::NONE);
            assert_eq!(nd.closing_track_point, TrackPointId::NONE);
            assert_eq!(nd.dependency_clashes, ClashDescId::NONE);
            assert_eq!(*fixed_reuse_dep_track_point, TrackPointId::NONE);
            assert_eq!(*priorized_reuse_dep_track_point, TrackPointId::NONE);
            assert!(involved.is_empty());
            assert!(affected.is_empty());
            assert!(env
                .ctx
                .process_context()
                .track_point(nd.clash_track_point)
                .is_clashed_or_irelevant_branch());
            assert_eq!(
                env.ctx
                    .process_context()
                    .track_point(nd.clash_track_point)
                    .get_branching_tag(),
                23
            );
        }
        other => panic!(
            "expected REUSEBACKENDEXPANSIONMODES dependency, got {:?}",
            other
        ),
    }

    let fixed_dep = env
        .algo
        .create_reuse_backend_fixed_individual_expansion_dependency(
            &mut process_indi,
            prev_dep_track_point,
            &mut env.ctx,
        );
    assert_eq!(process_indi, env.root);
    assert_factory_shaped_non_det_dependency(
        &env,
        fixed_dep,
        DepKind::ReuseBackendFixedIndividualExpansion,
        env.root,
        ConDescId::NONE,
        prev_dep_track_point,
        used_branch,
        23,
    );

    let prioritized_dep = env
        .algo
        .create_reuse_backend_prioritized_individual_expansion_dependency(
            &mut process_indi,
            prev_dep_track_point,
            &mut env.ctx,
        );
    assert_eq!(process_indi, env.root);
    assert_factory_shaped_non_det_dependency(
        &env,
        prioritized_dep,
        DepKind::ReuseBackendPrioritizedIndividualExpansion,
        env.root,
        ConDescId::NONE,
        prev_dep_track_point,
        used_branch,
        23,
    );

    let mut value_continue = TrackPointId::NONE;
    let value_dep = env.algo.create_reuse_backend_value_dependency(
        &mut value_continue,
        &mut process_indi,
        con_des,
        prev_dep_track_point,
        nominal_dep_track_point,
        &mut env.ctx,
    );
    assert!(value_dep.is_some());
    assert_eq!(process_indi, env.root);
    assert_eq!(
        env.ctx
            .process_context()
            .track_point(value_continue)
            .dependency_node(),
        value_dep
    );
    match env.ctx.process_context().dep_node(value_dep) {
        DependencyNode::DetLink { base, prev } => {
            assert_eq!(base.kind, DepKind::ReuseBackendValue);
            assert_eq!(base.individual_node, env.root);
            assert_eq!(base.concept_descriptor, con_des);
            assert_eq!(base.dep_track_point, prev_dep_track_point);
            assert_eq!(
                env.ctx.process_context().dep_link(*prev).dep_track_point,
                nominal_dep_track_point
            );
        }
        other => panic!(
            "expected REUSEBACKENDVALUE DetLink dependency, got {:?}",
            other
        ),
    }
}

#[test]
fn create_reuse_backend_dependency_wrappers_preserve_build_dependencies_guard() {
    let mut env = build_env();
    env.algo.conf_build_dependencies = false;
    let mut process_indi = env.root;
    let con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    let prev_dep_track_point = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
    let nominal_dep_track_point = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));

    assert_eq!(
        env.algo
            .create_reuse_backend_expansion_modes_dependency(prev_dep_track_point, &mut env.ctx),
        DependencyId::NONE
    );
    assert_eq!(
        env.algo
            .create_reuse_backend_fixed_individual_expansion_dependency(
                &mut process_indi,
                prev_dep_track_point,
                &mut env.ctx,
            ),
        DependencyId::NONE
    );
    assert_eq!(process_indi, env.root);
    assert_eq!(
        env.algo
            .create_reuse_backend_prioritized_individual_expansion_dependency(
                &mut process_indi,
                prev_dep_track_point,
                &mut env.ctx,
            ),
        DependencyId::NONE
    );
    assert_eq!(process_indi, env.root);
    let mut value_continue = TrackPointId::NONE;
    assert_eq!(
        env.algo.create_reuse_backend_value_dependency(
            &mut value_continue,
            &mut process_indi,
            con_des,
            prev_dep_track_point,
            nominal_dep_track_point,
            &mut env.ctx,
        ),
        DependencyId::NONE
    );
    assert_eq!(value_continue, TrackPointId::NONE);
    assert_eq!(process_indi, env.root);
}

#[test]
fn create_and_dependency_preserves_guard_and_factory_continuation_semantics() {
    let mut env = build_env();
    let mut process_indi = env.root;
    let mut and_dep_track_point = TrackPointId::NONE;
    let prev_dep_track_point = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
    env.ctx
        .process_context_mut()
        .track_point_mut(prev_dep_track_point)
        .add_maximum_branching_tag_candidate(31);
    let mut con_desc = ConceptDescriptor::new();
    con_desc.concept = env.concept_a;
    con_desc.negated = false;
    let con_des = env.ctx.process_context_mut().alloc_con_desc(con_desc);

    env.algo.conf_build_dependencies = false;
    let disabled_dep = env.algo.create_and_dependency(
        &mut and_dep_track_point,
        &mut process_indi,
        con_des,
        prev_dep_track_point,
        &mut env.ctx,
    );

    assert_eq!(disabled_dep, DependencyId::NONE);
    assert_eq!(and_dep_track_point, TrackPointId::NONE);
    assert_eq!(process_indi, env.root);

    env.algo.conf_build_dependencies = true;
    let dep_node = env.algo.create_and_dependency(
        &mut and_dep_track_point,
        &mut process_indi,
        con_des,
        prev_dep_track_point,
        &mut env.ctx,
    );

    assert!(dep_node.is_some());
    assert!(and_dep_track_point.is_some());
    assert_eq!(process_indi, env.root);
    assert_eq!(
        env.ctx
            .process_context()
            .track_point(and_dep_track_point)
            .dependency_node(),
        dep_node
    );

    match env.ctx.process_context().dep_node(dep_node) {
        DependencyNode::Deterministic { base } => {
            assert_eq!(base.kind, DepKind::And);
            assert_eq!(base.individual_node, NodeId::NONE);
            assert_eq!(base.concept_descriptor, con_des);
            assert_eq!(base.dep_track_point, prev_dep_track_point);
            assert_eq!(base.process_tag, 31);
        }
        other => panic!("expected AND deterministic dependency, got {:?}", other),
    }
    assert_eq!(
        env.ctx
            .process_context()
            .track_point(and_dep_track_point)
            .get_branching_tag(),
        31
    );
}

#[test]
fn create_automat_some_self_dependencies_preserve_factory_shapes() {
    let mut env = build_env();
    env.algo.conf_build_dependencies = true;
    let mut process_indi = env.root;
    let prev_dep_track_point = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
    env.ctx
        .process_context_mut()
        .track_point_mut(prev_dep_track_point)
        .add_maximum_branching_tag_candidate(37);
    let con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());

    let mut auto_tp = TrackPointId::NONE;
    let auto_dep = env.algo.create_automat_choose_dependency(
        &mut auto_tp,
        &mut process_indi,
        con_des,
        prev_dep_track_point,
        &mut env.ctx,
    );
    assert!(auto_dep.is_some());
    assert_eq!(
        env.ctx
            .process_context()
            .track_point(auto_tp)
            .dependency_node(),
        auto_dep
    );
    match env.ctx.process_context().dep_node(auto_dep) {
        DependencyNode::Deterministic { base } => {
            assert_eq!(base.kind, DepKind::AutomatChoose);
            assert_eq!(base.individual_node, NodeId::NONE);
            assert_eq!(base.concept_descriptor, con_des);
            assert_eq!(base.dep_track_point, prev_dep_track_point);
        }
        other => panic!(
            "expected AUTOMATCHOOSE deterministic dependency, got {:?}",
            other
        ),
    }

    let mut some_tp = TrackPointId::NONE;
    let some_dep = env.algo.create_some_dependency(
        &mut some_tp,
        &mut process_indi,
        con_des,
        prev_dep_track_point,
        &mut env.ctx,
    );
    assert!(some_dep.is_some());
    assert_eq!(
        env.ctx
            .process_context()
            .track_point(some_tp)
            .dependency_node(),
        some_dep
    );
    match env.ctx.process_context().dep_node(some_dep) {
        DependencyNode::Deterministic { base } => {
            assert_eq!(base.kind, DepKind::Some);
            assert_eq!(base.individual_node, env.root);
            assert_eq!(base.concept_descriptor, con_des);
            assert_eq!(base.dep_track_point, prev_dep_track_point);
        }
        other => panic!("expected SOME deterministic dependency, got {:?}", other),
    }

    let mut self_tp = TrackPointId::NONE;
    let self_dep = env.algo.create_self_dependency(
        &mut self_tp,
        &mut process_indi,
        con_des,
        prev_dep_track_point,
        &mut env.ctx,
    );
    assert!(self_dep.is_some());
    assert_eq!(
        env.ctx
            .process_context()
            .track_point(self_tp)
            .dependency_node(),
        self_dep
    );
    match env.ctx.process_context().dep_node(self_dep) {
        DependencyNode::Deterministic { base } => {
            assert_eq!(base.kind, DepKind::Self_);
            assert_eq!(base.individual_node, env.root);
            assert_eq!(base.concept_descriptor, con_des);
            assert_eq!(base.dep_track_point, prev_dep_track_point);
        }
        other => panic!("expected SELF deterministic dependency, got {:?}", other),
    }
}

#[test]
fn create_value_negvalue_all_dependencies_preserve_detlink_shapes() {
    let mut env = build_env();
    env.algo.conf_build_dependencies = true;
    let mut process_indi = env.root;
    let prev_dep_track_point = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
    let link_dep_track_point = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
    let con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());

    let mut value_tp = TrackPointId::NONE;
    let value_dep = env.algo.create_value_dependency(
        &mut value_tp,
        &mut process_indi,
        con_des,
        prev_dep_track_point,
        link_dep_track_point,
        &mut env.ctx,
    );
    assert!(value_dep.is_some());
    assert_eq!(
        env.ctx
            .process_context()
            .track_point(value_tp)
            .dependency_node(),
        value_dep
    );
    match env.ctx.process_context().dep_node(value_dep) {
        DependencyNode::DetLink { base, prev } => {
            assert_eq!(base.kind, DepKind::Value);
            assert_eq!(base.individual_node, env.root);
            assert_eq!(base.concept_descriptor, con_des);
            assert_eq!(base.dep_track_point, prev_dep_track_point);
            assert_eq!(
                env.ctx.process_context().dep_link(*prev).dep_track_point,
                link_dep_track_point
            );
        }
        other => panic!("expected VALUE DetLink dependency, got {:?}", other),
    }

    let mut neg_value_tp = TrackPointId::NONE;
    let neg_value_dep = env.algo.create_neg_value_dependency(
        &mut neg_value_tp,
        &mut process_indi,
        con_des,
        prev_dep_track_point,
        link_dep_track_point,
        &mut env.ctx,
    );
    assert!(neg_value_dep.is_some());
    assert_eq!(
        env.ctx
            .process_context()
            .track_point(neg_value_tp)
            .dependency_node(),
        neg_value_dep
    );
    match env.ctx.process_context().dep_node(neg_value_dep) {
        DependencyNode::DetLink { base, prev } => {
            assert_eq!(base.kind, DepKind::NegValue);
            assert_eq!(base.individual_node, env.root);
            assert_eq!(base.concept_descriptor, con_des);
            assert_eq!(base.dep_track_point, prev_dep_track_point);
            assert_eq!(
                env.ctx.process_context().dep_link(*prev).dep_track_point,
                link_dep_track_point
            );
        }
        other => panic!("expected NEGVALUE DetLink dependency, got {:?}", other),
    }

    let mut all_tp = TrackPointId::NONE;
    let all_dep = env.algo.create_all_dependency(
        &mut all_tp,
        &mut process_indi,
        con_des,
        prev_dep_track_point,
        link_dep_track_point,
        &mut env.ctx,
    );
    assert!(all_dep.is_some());
    assert_eq!(
        env.ctx
            .process_context()
            .track_point(all_tp)
            .dependency_node(),
        all_dep
    );
    match env.ctx.process_context().dep_node(all_dep) {
        DependencyNode::DetLink { base, prev } => {
            assert_eq!(base.kind, DepKind::All);
            assert_eq!(base.individual_node, env.root);
            assert_eq!(base.concept_descriptor, con_des);
            assert_eq!(base.dep_track_point, prev_dep_track_point);
            assert_eq!(
                env.ctx.process_context().dep_link(*prev).dep_track_point,
                link_dep_track_point
            );
        }
        other => panic!("expected ALL DetLink dependency, got {:?}", other),
    }
}

#[test]
fn create_role_assertion_and_functional_dependencies_preserve_factory_shapes() {
    use super::super::model::role::Role;

    let mut env = build_env();
    env.algo.conf_build_dependencies = true;
    let mut process_indi = env.root;
    let base_assertion_role = env.ctx.ontology_arenas_mut().alloc_role(Role::new());
    let base_assertion_indi = env
        .ctx
        .ontology_arenas_mut()
        .alloc_individual(Individual::new(71));
    let prev_dep_track_point = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
    let link1_dep_track_point = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
    let link2_dep_track_point = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
    let con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());

    let mut role_assertion_tp = TrackPointId::NONE;
    let role_assertion_dep = env.algo.create_role_assertion_dependency(
        &mut role_assertion_tp,
        process_indi,
        prev_dep_track_point,
        link1_dep_track_point,
        base_assertion_role,
        base_assertion_indi,
        &mut env.ctx,
    );
    assert!(role_assertion_dep.is_some());
    assert_eq!(
        env.ctx
            .process_context()
            .track_point(role_assertion_tp)
            .dependency_node(),
        role_assertion_dep
    );
    match env.ctx.process_context().dep_node(role_assertion_dep) {
        DependencyNode::DetLink { base, prev } => {
            assert_eq!(base.kind, DepKind::RoleAssertion);
            assert_eq!(base.individual_node, env.root);
            assert_eq!(base.concept_descriptor, ConDescId::NONE);
            assert_eq!(base.dep_track_point, prev_dep_track_point);
            assert_eq!(base.base_assertion_role, base_assertion_role);
            assert_eq!(base.base_assertion_individual, base_assertion_indi);
            assert_eq!(
                env.ctx.process_context().dep_link(*prev).dep_track_point,
                link1_dep_track_point
            );
        }
        other => panic!("expected ROLEASSERTION DetLink dependency, got {:?}", other),
    }

    let mut functional_tp = TrackPointId::NONE;
    let functional_dep = env.algo.create_functional_dependency(
        &mut functional_tp,
        &mut process_indi,
        con_des,
        prev_dep_track_point,
        link1_dep_track_point,
        link2_dep_track_point,
        &mut env.ctx,
    );
    assert!(functional_dep.is_some());
    assert_eq!(process_indi, env.root);
    assert_eq!(
        env.ctx
            .process_context()
            .track_point(functional_tp)
            .dependency_node(),
        functional_dep
    );
    match env.ctx.process_context().dep_node(functional_dep) {
        DependencyNode::DetLink2 { base, prev1, prev2 } => {
            assert_eq!(base.kind, DepKind::Functional);
            assert_eq!(base.individual_node, env.root);
            assert_eq!(base.concept_descriptor, con_des);
            assert_eq!(base.dep_track_point, prev_dep_track_point);
            assert_eq!(
                env.ctx.process_context().dep_link(*prev1).dep_track_point,
                link1_dep_track_point
            );
            assert_eq!(
                env.ctx.process_context().dep_link(*prev2).dep_track_point,
                link2_dep_track_point
            );
        }
        other => panic!("expected FUNCTIONAL DetLink2 dependency, got {:?}", other),
    }
}

#[test]
fn create_role_assertion_and_functional_dependencies_preserve_build_dependencies_guard() {
    let mut env = build_env();
    env.algo.conf_build_dependencies = false;
    let mut process_indi = env.root;
    let prev_dep_track_point = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
    let link1_dep_track_point = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
    let link2_dep_track_point = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
    let con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());

    let mut role_assertion_tp = TrackPointId::NONE;
    assert_eq!(
        env.algo.create_role_assertion_dependency(
            &mut role_assertion_tp,
            process_indi,
            prev_dep_track_point,
            link1_dep_track_point,
            Id::NONE,
            Id::NONE,
            &mut env.ctx,
        ),
        DependencyId::NONE
    );
    assert_eq!(role_assertion_tp, TrackPointId::NONE);

    let mut functional_tp = TrackPointId::NONE;
    assert_eq!(
        env.algo.create_functional_dependency(
            &mut functional_tp,
            &mut process_indi,
            con_des,
            prev_dep_track_point,
            link1_dep_track_point,
            link2_dep_track_point,
            &mut env.ctx,
        ),
        DependencyId::NONE
    );
    assert_eq!(functional_tp, TrackPointId::NONE);
    assert_eq!(process_indi, env.root);
}

#[test]
fn create_distinct_automat_transaction_atleast_dependencies_preserve_factory_shapes() {
    let mut env = build_env();
    env.algo.conf_build_dependencies = true;
    let mut process_indi = env.root;
    let prev_dep_track_point = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
    let link_dep_track_point = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
    let con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());

    let mut distinct_tp = TrackPointId::NONE;
    let distinct_dep = env.algo.create_distinct_dependency(
        &mut distinct_tp,
        &mut process_indi,
        con_des,
        prev_dep_track_point,
        &mut env.ctx,
    );
    assert!(distinct_dep.is_some());
    assert_eq!(
        env.ctx
            .process_context()
            .track_point(distinct_tp)
            .dependency_node(),
        distinct_dep
    );
    match env.ctx.process_context().dep_node(distinct_dep) {
        DependencyNode::Deterministic { base } => {
            assert_eq!(base.kind, DepKind::Distinct);
            assert_eq!(base.individual_node, env.root);
            assert_eq!(base.concept_descriptor, con_des);
            assert_eq!(base.dep_track_point, prev_dep_track_point);
        }
        other => panic!(
            "expected DISTINCT deterministic dependency, got {:?}",
            other
        ),
    }

    let mut auto_trans_tp = TrackPointId::NONE;
    let auto_trans_dep = env.algo.create_automat_transaction_dependency(
        &mut auto_trans_tp,
        &mut process_indi,
        con_des,
        prev_dep_track_point,
        link_dep_track_point,
        &mut env.ctx,
    );
    assert!(auto_trans_dep.is_some());
    assert_eq!(
        env.ctx
            .process_context()
            .track_point(auto_trans_tp)
            .dependency_node(),
        auto_trans_dep
    );
    match env.ctx.process_context().dep_node(auto_trans_dep) {
        DependencyNode::DetLink { base, prev } => {
            assert_eq!(base.kind, DepKind::AutomatTransaction);
            assert_eq!(base.individual_node, env.root);
            assert_eq!(base.concept_descriptor, con_des);
            assert_eq!(base.dep_track_point, prev_dep_track_point);
            assert_eq!(
                env.ctx.process_context().dep_link(*prev).dep_track_point,
                link_dep_track_point
            );
        }
        other => panic!(
            "expected AUTOMATTRANSACTION DetLink dependency, got {:?}",
            other
        ),
    }

    let mut atleast_tp = TrackPointId::NONE;
    let atleast_dep = env.algo.create_atleast_dependency(
        &mut atleast_tp,
        &mut process_indi,
        con_des,
        prev_dep_track_point,
        &mut env.ctx,
    );
    assert!(atleast_dep.is_some());
    assert_eq!(
        env.ctx
            .process_context()
            .track_point(atleast_tp)
            .dependency_node(),
        atleast_dep
    );
    match env.ctx.process_context().dep_node(atleast_dep) {
        DependencyNode::Deterministic { base } => {
            assert_eq!(base.kind, DepKind::AtLeast);
            assert_eq!(base.individual_node, env.root);
            assert_eq!(base.concept_descriptor, con_des);
            assert_eq!(base.dep_track_point, prev_dep_track_point);
        }
        other => panic!("expected ATLEAST deterministic dependency, got {:?}", other),
    }
}

#[test]
fn create_or_dependency_preserves_or_factory_shape() {
    let mut env = build_env();
    env.algo.conf_build_dependencies = true;
    let mut process_indi = env.root;
    let con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    let prev_dep_track_point = env
        .ctx
        .process_context_mut()
        .alloc_track_point(DependencyTrackPoint::new(DependencyId::NONE));
    env.ctx
        .process_context_mut()
        .track_point_mut(prev_dep_track_point)
        .add_maximum_branching_tag_candidate(37);
    let used_branch = env
        .ctx
        .process_context_mut()
        .alloc_branch_child_node(BranchNodeId::NONE, INVALID);
    env.ctx.base.used_branch_tree_node = used_branch;

    let dep_node = env.algo.create_or_dependency(
        &mut process_indi,
        con_des,
        prev_dep_track_point,
        &mut env.ctx,
    );

    assert!(dep_node.is_some());
    assert_eq!(process_indi, env.root);
    match env.ctx.process_context().dep_node(dep_node) {
        DependencyNode::Or { base, nd, disj } => {
            assert_eq!(base.kind, DepKind::Or);
            assert_eq!(base.individual_node, NodeId::NONE);
            assert_eq!(base.concept_descriptor, con_des);
            assert_eq!(base.dep_track_point, prev_dep_track_point);
            assert_eq!(nd.branch_track_points, nd.clash_track_point);
            assert_eq!(nd.branch_node, used_branch);
            assert_eq!(nd.branch_tag, 37);
            assert_eq!(nd.closed_track_point, TrackPointId::NONE);
            assert_eq!(nd.closing_track_point, TrackPointId::NONE);
            assert_eq!(nd.dependency_clashes, ClashDescId::NONE);
            assert!(env
                .ctx
                .process_context()
                .track_point(nd.clash_track_point)
                .is_clashed_or_irelevant_branch());
            assert_eq!(
                env.ctx
                    .process_context()
                    .track_point(nd.clash_track_point)
                    .get_branching_tag(),
                37
            );
            assert!(disj.disjunct_concept_linker.is_empty());
            assert_eq!(disj.disjunct_branch_stats, INVALID);
        }
        other => panic!("expected OR dependency variant, got {:?}", other),
    }
}

#[test]
fn create_dependend_branching_task_list_front_splices_children() {
    let mut env = build_env();

    let parent = env
        .ctx
        .base
        .alloc_sat_calc_task(SatisfiableCalculationTask::new());
    env.ctx.base.used_sat_calc_task = parent;
    env.ctx.base.sat_calc_task_mut(parent).base.root_task = Id::new(parent.raw);
    env.ctx.base.sat_calc_task_mut(parent).base.task_depth = 2;
    env.ctx.base.sat_calc_task_mut(parent).base.task_type = 17;
    env.ctx.base.sat_calc_task_mut(parent).process_context = 31;
    env.ctx.base.sat_calc_task_mut(parent).processing_data_box = 32;
    env.algo.debug_task_id_vector[3] = 7;

    let head = env
        .algo
        .create_dependend_branching_task_list(3, &mut env.ctx);

    let first = head;
    let second = env.ctx.base.sat_calc_task(first).get_next();
    let third = env.ctx.base.sat_calc_task(second).get_next();
    assert_eq!(env.ctx.base.sat_calc_task(third).get_next(), Id::NONE);

    let first_task = env.ctx.base.sat_calc_task(first);
    assert_eq!(first_task.base.get_task_id(), 9);
    assert_eq!(first_task.base.parent_task.raw, parent.raw);
    assert_eq!(first_task.base.root_task.raw, parent.raw);
    assert_eq!(first_task.base.get_task_depth(), 3);
    assert_eq!(first_task.base.get_task_type(), 17);
    assert_eq!(first_task.process_context, 31);
    assert_eq!(first_task.processing_data_box, 32);

    assert_eq!(env.ctx.base.sat_calc_task(second).base.get_task_id(), 8);
    assert_eq!(env.ctx.base.sat_calc_task(third).base.get_task_id(), 7);
    assert_eq!(env.algo.debug_task_id_vector[3], 10);
    assert_eq!(
        env.ctx
            .base
            .sat_calc_task(parent)
            .base
            .get_active_reference_count(),
        3
    );
    assert_eq!(
        env.ctx
            .base
            .sat_calc_task(parent)
            .base
            .get_referenced_task_linker()
            .len(),
        3
    );
}

#[test]
fn create_dependend_branching_task_list_skips_debug_ids_after_depth_limit() {
    let mut env = build_env();

    let parent = env
        .ctx
        .base
        .alloc_sat_calc_task(SatisfiableCalculationTask::new());
    env.ctx.base.used_sat_calc_task = parent;
    env.ctx.base.sat_calc_task_mut(parent).base.root_task = Id::new(parent.raw);
    env.ctx.base.sat_calc_task_mut(parent).base.task_depth = 90;
    env.algo.debug_task_id_vector[91] = 44;

    let head = env
        .algo
        .create_dependend_branching_task_list(1, &mut env.ctx);

    assert_eq!(env.ctx.base.sat_calc_task(head).base.get_task_id(), 0);
    assert_eq!(env.algo.debug_task_id_vector[91], 44);
}

#[test]
fn create_merge_branching_task_allocates_dependent_child() {
    let mut env = build_env();

    let parent = env
        .ctx
        .base
        .alloc_sat_calc_task(SatisfiableCalculationTask::new());
    env.ctx.base.used_sat_calc_task = parent;
    env.ctx.base.used_task_priority_strategy =
        Some(TaskProcessingPriorityStrategy::new_equal_depth_cache_orientated());
    env.ctx.base.sat_calc_task_mut(parent).base.root_task = Id::new(parent.raw);
    env.ctx.base.sat_calc_task_mut(parent).base.task_depth = 4;
    env.ctx.base.sat_calc_task_mut(parent).base.task_type = 19;
    env.algo.debug_task_id_vector[5] = 50;

    let mut process_indi_node = NodeId::NONE;
    let mut con_pro_des = ConProcDescId::NONE;
    let mut distinct_indi_node = NodeId::NONE;
    let mut merging_indi_node = NodeId::NONE;
    let child = env.algo.create_merge_branching_task(
        &mut process_indi_node,
        &mut con_pro_des,
        &mut distinct_indi_node,
        &mut merging_indi_node,
        Id::NONE,
        RestrictionSpecId::NONE,
        &mut env.ctx,
    );

    assert!(child.is_some());
    let child_task = env.ctx.base.sat_calc_task(child);
    assert_eq!(child_task.base.parent_task.raw, parent.raw);
    assert_eq!(child_task.base.root_task.raw, parent.raw);
    assert_eq!(child_task.base.get_task_depth(), 5);
    assert_eq!(child_task.base.get_task_type(), 19);
    assert_eq!(child_task.base.get_task_id(), 50);
    assert_eq!(child_task.base.get_task_priority(), 5.0);
    assert_eq!(child_task.get_next(), Id::NONE);
    assert_eq!(env.algo.debug_task_id_vector[5], 51);
    assert_eq!(
        env.ctx
            .base
            .sat_calc_task(parent)
            .base
            .get_active_reference_count(),
        1
    );
}

#[test]
fn create_distinct_branching_task_allocates_dependent_child() {
    let mut env = build_env();

    let parent = env
        .ctx
        .base
        .alloc_sat_calc_task(SatisfiableCalculationTask::new());
    env.ctx.base.used_sat_calc_task = parent;
    env.ctx.base.used_task_priority_strategy =
        Some(TaskProcessingPriorityStrategy::new_equal_depth_cache_orientated());
    env.ctx.base.sat_calc_task_mut(parent).base.root_task = Id::new(parent.raw);
    env.ctx.base.sat_calc_task_mut(parent).base.task_depth = 6;
    env.algo.debug_task_id_vector[7] = 80;

    let mut process_indi_node = NodeId::NONE;
    let mut distinct_indi_node = NodeId::NONE;
    let child = env.algo.create_distinct_branching_task(
        &mut process_indi_node,
        ConProcDescId::NONE,
        &mut distinct_indi_node,
        false,
        Id::NONE,
        RestrictionSpecId::NONE,
        &mut env.ctx,
    );

    assert!(child.is_some());
    let child_task = env.ctx.base.sat_calc_task(child);
    assert_eq!(child_task.base.parent_task.raw, parent.raw);
    assert_eq!(child_task.base.root_task.raw, parent.raw);
    assert_eq!(child_task.base.get_task_depth(), 7);
    assert_eq!(child_task.base.get_task_id(), 80);
    assert_eq!(child_task.base.get_task_priority(), 7.0);
    assert_eq!(child_task.get_next(), Id::NONE);
    assert_eq!(env.algo.debug_task_id_vector[7], 81);
    assert_eq!(
        env.ctx
            .base
            .sat_calc_task(parent)
            .base
            .get_referenced_task_linker()
            .len(),
        1
    );
}

#[test]
fn get_collected_filtered_clashed_descriptors_from_branch_deduplicates_and_replays_self_pointing() {
    let mut env = build_env();
    let node = test_node_at_depth(&mut env, 95, 4);
    let concept_a = env.concept_a;
    let mut con_des = ConceptDescriptor::new();
    con_des.concept = concept_a;
    let con_des = env.ctx.process_context_mut().alloc_con_desc(con_des);
    let base_tp =
        real_dependency_track_point(&mut env, node, con_des, DepKind::IndependentBase, 113, 113);

    let base = DepNodeBase {
        process_tag: 114,
        concept_descriptor: ConDescId::NONE,
        individual_node: node,
        kind: DepKind::Or,
        dep_track_point: base_tp,
        additional_after: Id::NONE,
        selected_var_bind_path: VarBindingPathId::NONE,
        resolve_var_bind_path_map: None,
        resolve_rep_prop_map: None,
        base_assertion_role: Id::NONE,
        base_assertion_individual: Id::NONE,
    };
    let non_det_dep =
        env.ctx
            .process_context_mut()
            .alloc_dep_node(DependencyNode::NonDeterministic {
                base,
                nd: NonDetData {
                    branch_track_points: TrackPointId::NONE,
                    clash_track_point: TrackPointId::NONE,
                    dependency_clashes: ClashDescId::NONE,
                    branch_node: BranchNodeId::NONE,
                    branch_tag: 114,
                    closing_track_point: TrackPointId::NONE,
                    closed_track_point: TrackPointId::NONE,
                },
            });

    let mut branch_tp1 = DependencyTrackPoint::new(non_det_dep);
    branch_tp1.process_tag = 114;
    branch_tp1.involved_indi_ids = vec![771];
    let branch_tp1 = env.ctx.process_context_mut().alloc_track_point(branch_tp1);
    let mut branch_tp2 = DependencyTrackPoint::new(non_det_dep);
    branch_tp2.process_tag = 114;
    branch_tp2.involved_indi_ids = vec![772];
    let branch_tp2 = env.ctx.process_context_mut().alloc_track_point(branch_tp2);
    env.ctx
        .process_context_mut()
        .track_point_mut(branch_tp1)
        .next = branch_tp2;
    if let DependencyNode::NonDeterministic { nd, .. } =
        env.ctx.process_context_mut().dep_node_mut(non_det_dep)
    {
        nd.branch_track_points = branch_tp1;
    } else {
        panic!("expected non-deterministic dependency node");
    }

    let mut clash_node = node;
    let non_self_clash_1 = env.algo.create_clashed_concept_descriptor(
        Id::NONE,
        &mut clash_node,
        con_des,
        base_tp,
        &mut env.ctx,
    );
    let mut clash_node = node;
    let non_self_clash_2 = env.algo.create_clashed_concept_descriptor(
        Id::NONE,
        &mut clash_node,
        con_des,
        base_tp,
        &mut env.ctx,
    );
    let self_clash = clash_descriptor_for_track_point(&mut env, branch_tp1);
    env.ctx
        .process_context_mut()
        .clash_desc_mut(non_self_clash_1)
        .set_next(self_clash);
    env.ctx
        .process_context_mut()
        .track_point_mut(branch_tp1)
        .set_clashes(non_self_clash_1, false);
    env.ctx
        .process_context_mut()
        .track_point_mut(branch_tp2)
        .set_clashes(non_self_clash_2, false);

    let mut line = TrackedClashedDependencyLine::new();
    line.init_tracked_clashed_dependency_line(false, 0, 114);
    line.set_involved_individual_tracking_set(Some(Default::default()));

    let collected = env
        .algo
        .get_collected_filtered_clashed_descriptors_from_branch(
            Id::NONE,
            non_det_dep,
            &mut line,
            &mut env.ctx,
            INVALID,
        );
    let head = env.ctx.process_context().clash_desc(collected);
    let second = head.get_next_descriptor();
    let second_desc = env.ctx.process_context().clash_desc(second);

    assert_eq!(head.get_dependency_track_point(), base_tp);
    assert_eq!(head.get_concept_descriptor(), Id::NONE);
    assert_eq!(second_desc.get_dependency_track_point(), base_tp);
    assert_eq!(second_desc.get_concept_descriptor(), con_des);
    assert_eq!(second_desc.get_next_descriptor(), Id::NONE);
    assert_eq!(
        line.get_involved_individual_tracking_set().unwrap().len(),
        2
    );
    assert_eq!(
        line.take_next_free_tracked_clashed_descriptor(&mut env.ctx),
        Id::NONE
    );
}

#[test]
fn initialize_tracking_line_initializes_bounds_and_buckets() {
    let mut env = build_env();
    let root = env.root;
    let concept_a = env.concept_a;
    let top_concept = env.top_concept;
    let previous_level_node = test_node_at_depth(&mut env, 88, 2);
    let mut line = TrackedClashedDependencyLine::new();

    let level = tracked_concept_clash(&mut env, root, concept_a, false, DepKind::And, 81, 40);
    let previous = tracked_concept_clash(
        &mut env,
        previous_level_node,
        top_concept,
        false,
        DepKind::And,
        82,
        44,
    );
    env.ctx
        .process_context_mut()
        .clash_desc_mut(level)
        .set_next(previous);

    assert!(env
        .algo
        .initialize_tracking_line(&mut line, level, &mut env.ctx));
    assert_eq!(line.get_individual_node_level(), 0);
    assert_eq!(line.get_branching_level(), 44);
    assert!(!line.is_exact_individual_tracking());
    assert_eq!(line.take_next_tracked_clashed_list(), level);
    assert_eq!(line.take_next_tracked_clashed_list(), previous);
    assert_eq!(line.take_next_tracked_clashed_list(), Id::NONE);
}

#[test]
fn initialize_tracking_line_rejects_tracking_error_without_sorting() {
    let mut env = build_env();
    let root = env.root;
    let mut line = TrackedClashedDependencyLine::new();
    let errored = errored_tracked_concept_clash(&mut env, root);

    assert!(env
        .ctx
        .process_context()
        .clash_desc(errored)
        .is_tracking_error());
    assert!(!env
        .algo
        .initialize_tracking_line(&mut line, errored, &mut env.ctx));
    assert_eq!(line.get_individual_node_level(), INVALID);
    assert_eq!(line.get_branching_level(), INVALID);
    assert!(!line.has_more_tracked_clashed_list());
}

#[test]
fn initialize_tracking_line_detects_nominal_tracking() {
    let mut env = build_env();
    let root = env.root;
    let concept_a = env.concept_a;
    env.ctx
        .process_context_mut()
        .node_mut(root)
        .set_individual_type(IndividualType::Nominal);
    let tracked = tracked_concept_clash(&mut env, root, concept_a, false, DepKind::And, 83, 45);
    let mut line = TrackedClashedDependencyLine::new();

    assert!(env
        .algo
        .initialize_tracking_line(&mut line, tracked, &mut env.ctx));
    assert!(line.is_exact_individual_tracking());
    assert_eq!(line.get_individual_node_level(), 0);
    assert_eq!(line.get_branching_level(), 45);
}

#[test]
fn get_sorted_clashed_descriptors_orders_by_concept_tag_and_detaches_tail() {
    let mut env = build_env();
    let root = env.root;
    let c7a = marker_concept(&mut env, 7);
    let c3 = marker_concept(&mut env, 3);
    let c11 = marker_concept(&mut env, 11);
    let c7b = marker_concept(&mut env, 7);

    let tracked_7a = tracked_concept_clash(&mut env, root, c7a, false, DepKind::And, 91, 50);
    let tracked_3 = tracked_concept_clash(&mut env, root, c3, false, DepKind::And, 92, 50);
    let tracked_11 = tracked_concept_clash(&mut env, root, c11, false, DepKind::And, 93, 50);
    let tracked_7b = tracked_concept_clash(&mut env, root, c7b, false, DepKind::And, 94, 50);

    env.ctx
        .process_context_mut()
        .clash_desc_mut(tracked_7a)
        .set_next(tracked_3);
    env.ctx
        .process_context_mut()
        .clash_desc_mut(tracked_3)
        .set_next(tracked_11);
    env.ctx
        .process_context_mut()
        .clash_desc_mut(tracked_11)
        .set_next(tracked_7b);

    let sorted = env
        .algo
        .get_sorted_clashed_descriptors(tracked_7a, &mut env.ctx);
    assert_eq!(tracked_chain_tags(&env, sorted), vec![3, 7, 7, 11]);
    assert_eq!(sorted, tracked_3);
    let second = env
        .ctx
        .process_context()
        .clash_desc(sorted)
        .get_next_descriptor();
    assert_eq!(second, tracked_7b);
    let third = env
        .ctx
        .process_context()
        .clash_desc(second)
        .get_next_descriptor();
    assert_eq!(third, tracked_7a);
    let fourth = env
        .ctx
        .process_context()
        .clash_desc(third)
        .get_next_descriptor();
    assert_eq!(fourth, tracked_11);
    assert_eq!(
        env.ctx
            .process_context()
            .clash_desc(fourth)
            .get_next_descriptor(),
        Id::NONE
    );
}

#[test]
fn write_clash_descriptors_to_cache_from_line_drains_and_restores_tracking_line() {
    let mut env = build_env();
    let root = env.root;
    let concept_a = env.concept_a;
    let top_concept = env.top_concept;
    let mut line = TrackedClashedDependencyLine::new();
    line.init_tracked_clashed_dependency_line(false, 0, 101);

    let level = tracked_concept_clash(&mut env, root, concept_a, false, DepKind::And, 101, 100);
    let independent = tracked_concept_clash(
        &mut env,
        root,
        top_concept,
        false,
        DepKind::IndependentBase,
        102,
        101,
    );
    line.sort_in_tracked_clashed_descriptors(level, false, &mut env.ctx);
    line.sort_in_tracked_clashed_descriptors(independent, false, &mut env.ctx);

    assert!(!env
        .algo
        .write_clash_descriptors_to_cache_from_line(&mut line, &mut env.ctx));
    assert_eq!(line.take_next_tracked_clashed_list(), level);
    assert_eq!(line.take_next_tracked_clashed_list(), independent);
    assert_eq!(line.take_next_tracked_clashed_list(), Id::NONE);
}

#[test]
fn write_clash_descriptors_to_cache_with_additional_removes_failed_additional() {
    let mut env = build_env();
    let root = env.root;
    let concept_a = env.concept_a;
    let top_concept = env.top_concept;
    let top_data_range_concept = env.top_data_range_concept;
    let mut line = TrackedClashedDependencyLine::new();
    line.init_tracked_clashed_dependency_line(false, 0, 111);

    let first = tracked_concept_clash(&mut env, root, concept_a, false, DepKind::And, 111, 111);
    let second = tracked_concept_clash(&mut env, root, top_concept, false, DepKind::And, 112, 111);
    let additional = tracked_concept_clash(
        &mut env,
        root,
        top_data_range_concept,
        false,
        DepKind::And,
        113,
        111,
    );
    env.ctx
        .process_context_mut()
        .clash_desc_mut(first)
        .set_next(second);
    let mut tracked = first;

    assert!(!env.algo.write_clash_descriptors_to_cache_with_additional(
        &mut tracked,
        additional,
        &mut line,
        &mut env.ctx,
    ));
    assert_eq!(tracked, first);
    assert_eq!(
        env.ctx
            .process_context()
            .clash_desc(first)
            .get_next_descriptor(),
        second
    );
    assert_eq!(
        env.ctx
            .process_context()
            .clash_desc(second)
            .get_next_descriptor(),
        Id::NONE
    );
    assert_eq!(
        env.ctx
            .process_context()
            .clash_desc(additional)
            .get_next_descriptor(),
        Id::NONE
    );
}

#[test]
fn write_clash_descriptors_to_cache_validates_sorts_then_null_handler_fails() {
    let mut env = build_env();
    env.algo.conf_write_unsat_caching = true;
    let root = env.root;
    let c9 = marker_concept(&mut env, 9);
    let c4 = marker_concept(&mut env, 4);
    env.ctx
        .ontology_arenas_mut()
        .concept_mut(c9)
        .set_terminology(1);
    env.ctx
        .ontology_arenas_mut()
        .concept_mut(c4)
        .set_terminology(1);
    let first = tracked_concept_clash(&mut env, root, c9, false, DepKind::And, 121, 121);
    let second = tracked_concept_clash(&mut env, root, c4, false, DepKind::And, 122, 121);
    env.ctx
        .process_context_mut()
        .clash_desc_mut(first)
        .set_next(second);
    let mut tracked = first;
    let mut line = TrackedClashedDependencyLine::new();
    line.init_tracked_clashed_dependency_line(false, 0, 121);

    assert!(!env
        .algo
        .write_clash_descriptors_to_cache(&mut tracked, &mut line, &mut env.ctx));
    assert_eq!(tracked, second);
    assert_eq!(tracked_chain_tags(&env, tracked), vec![4, 9]);
}

#[test]
fn write_clash_descriptors_to_cache_forwards_to_installed_unsat_handler() {
    let mut env = build_env();
    env.algo.conf_write_unsat_caching = true;
    install_unsat_cache_handler(&mut env);

    let root = env.root;
    let c9 = marker_concept(&mut env, 9);
    let c4 = marker_concept(&mut env, 4);
    env.ctx
        .ontology_arenas_mut()
        .concept_mut(c9)
        .set_terminology(1);
    env.ctx
        .ontology_arenas_mut()
        .concept_mut(c4)
        .set_terminology(1);
    let first = tracked_concept_clash(&mut env, root, c9, false, DepKind::And, 121, 121);
    let second = tracked_concept_clash(&mut env, root, c4, false, DepKind::And, 122, 121);
    env.ctx
        .process_context_mut()
        .clash_desc_mut(first)
        .set_next(second);
    let mut tracked = first;
    let mut line = TrackedClashedDependencyLine::new();
    line.init_tracked_clashed_dependency_line(false, 0, 121);

    assert!(env
        .algo
        .write_clash_descriptors_to_cache(&mut tracked, &mut line, &mut env.ctx));
    assert_eq!(tracked_chain_tags(&env, tracked), vec![4, 9]);
    assert!(env.ctx.base.used_unsat_cache_handler_state.is_some());
}

#[test]
fn write_clash_descriptors_to_cache_rejects_invalid_terminology_without_sorting() {
    let mut env = build_env();
    env.algo.conf_write_unsat_caching = true;
    let root = env.root;
    let c9 = marker_concept(&mut env, 9);
    let c4 = marker_concept(&mut env, 4);
    env.ctx
        .ontology_arenas_mut()
        .concept_mut(c9)
        .set_terminology(1);
    let first = tracked_concept_clash(&mut env, root, c9, false, DepKind::And, 131, 131);
    let second = tracked_concept_clash(&mut env, root, c4, false, DepKind::And, 132, 131);
    env.ctx
        .process_context_mut()
        .clash_desc_mut(first)
        .set_next(second);
    let mut tracked = first;
    let mut line = TrackedClashedDependencyLine::new();
    line.init_tracked_clashed_dependency_line(false, 0, 131);

    assert!(!env
        .algo
        .write_clash_descriptors_to_cache(&mut tracked, &mut line, &mut env.ctx));
    assert_eq!(tracked, first);
    assert_eq!(tracked_chain_tags(&env, tracked), vec![9, 4]);
}

#[test]
fn write_clash_descriptors_to_cache_rejects_nominal_tracking() {
    let mut env = build_env();
    env.algo.conf_write_unsat_caching = true;
    let root = env.root;
    let concept_a = env.concept_a;
    env.ctx
        .ontology_arenas_mut()
        .concept_mut(concept_a)
        .set_terminology(1);
    env.ctx
        .process_context_mut()
        .node_mut(root)
        .set_individual_type(IndividualType::Nominal);
    let mut tracked =
        tracked_concept_clash(&mut env, root, concept_a, false, DepKind::And, 141, 141);
    let mut line = TrackedClashedDependencyLine::new();
    line.init_tracked_clashed_dependency_line(true, 0, 141);

    assert!(!env
        .algo
        .write_clash_descriptors_to_cache(&mut tracked, &mut line, &mut env.ctx));
}

#[test]
fn write_clash_descriptors_to_cache_rejects_atomic_opposite_polarity() {
    let mut env = build_env();
    env.algo.conf_write_unsat_caching = true;
    let root = env.root;
    let concept_a = env.concept_a;
    env.ctx
        .ontology_arenas_mut()
        .concept_mut(concept_a)
        .set_terminology(1);
    let first = tracked_concept_clash(&mut env, root, concept_a, false, DepKind::And, 151, 151);
    let second = tracked_concept_clash(&mut env, root, concept_a, true, DepKind::And, 152, 151);
    env.ctx
        .process_context_mut()
        .clash_desc_mut(first)
        .set_next(second);
    let mut tracked = first;
    let mut line = TrackedClashedDependencyLine::new();
    line.init_tracked_clashed_dependency_line(false, 0, 151);

    assert!(!env
        .algo
        .write_clash_descriptors_to_cache(&mut tracked, &mut line, &mut env.ctx));
    assert_eq!(tracked, first);
    assert_eq!(tracked_chain_tags(&env, tracked), vec![100, 100]);
}

#[test]
fn raised_clash_carries_clashed_concept_descriptor() {
    let mut env = build_env();
    let mut root = env.root;
    let tp = deterministic_track_point(&mut env);
    let mut con_des = ConceptDescriptor::new();
    con_des.concept = env.concept_a;
    con_des.set_dependency_track_point(tp);
    let con_des = env.ctx.process_context_mut().alloc_con_desc(con_des);

    let clash =
        env.algo
            .create_clashed_concept_descriptor(Id::NONE, &mut root, con_des, tp, &mut env.ctx);
    env.ctx.raise_clash(clash);

    assert_eq!(env.ctx.pending_signal(), CalcSignal::Clash(clash));
    let desc = env.ctx.process_context().clash_desc(clash);
    assert_eq!(desc.get_concept_descriptor(), con_des);
    assert_eq!(desc.get_appropriated_individual(), root);
}

#[test]
fn concept_unsatisfiability_saturated_reads_reference_linking() {
    let mut env = build_env();
    let concept_a = env.concept_a;
    attach_saturation_unsat_reference(&mut env, concept_a, false, true);

    assert!(env
        .algo
        .is_concept_unsatisfiability_saturated(concept_a, false, &mut env.ctx));
    assert!(!env
        .algo
        .is_concept_unsatisfiability_saturated(concept_a, true, &mut env.ctx));
}

#[test]
fn has_saturated_clashed_flag_for_concept_reads_reference_linking() {
    let mut env = build_env();
    let concept_a = env.concept_a;
    let top_concept = env.top_concept;
    attach_saturation_unsat_reference(&mut env, concept_a, true, true);
    attach_saturation_unsat_reference(&mut env, top_concept, false, false);

    assert!(env
        .algo
        .has_saturated_clashed_flag_for_concept(concept_a, true, &mut env.ctx));
    assert!(!env
        .algo
        .has_saturated_clashed_flag_for_concept(concept_a, false, &mut env.ctx));
    assert!(!env
        .algo
        .has_saturated_clashed_flag_for_concept(top_concept, false, &mut env.ctx));
}

#[test]
fn add_concept_to_individual_raises_saturated_unsat_clash_descriptor() {
    let mut env = build_env();
    env.algo.conf_concept_unsatisfiability_saturated_testing = true;
    let mut root = env.root;
    let concept_a = env.concept_a;
    attach_saturation_unsat_reference(&mut env, concept_a, false, true);
    let dep_track_point = deterministic_track_point(&mut env);

    env.algo.add_concept_to_individual(
        concept_a,
        false,
        &mut root,
        dep_track_point,
        false,
        true,
        &mut env.ctx,
    );

    let clash = match env.ctx.pending_signal() {
        CalcSignal::Clash(clash) => clash,
        signal => panic!("expected saturated-unsat clash, got {signal:?}"),
    };
    let desc = env.ctx.process_context().clash_desc(clash);
    assert_eq!(desc.get_appropriated_individual(), root);
    assert_eq!(desc.get_dependency_track_point(), dep_track_point);
    let con_des = desc.get_concept_descriptor();
    assert_eq!(
        env.ctx.process_context().con_desc(con_des).get_concept(),
        concept_a
    );
    assert_eq!(
        env.ctx.process_context().con_desc(con_des).is_negated(),
        false
    );
}

#[test]
fn concept_label_set_modified_updates_tagger_and_label_set_tag() {
    let mut env = build_env();
    let mut root = env.root;

    assert!(!env
        .algo
        .is_individual_node_concept_label_set_modified(&mut root, 0, &mut env.ctx));

    env.algo
        .set_individual_node_concept_label_set_modified(&mut root, &mut env.ctx);

    let current_tag = env
        .ctx
        .process_context()
        .used_process_tagger()
        .get_current_concept_label_set_modification_tag();
    let label_set = env
        .ctx
        .process_context()
        .node(root)
        .use_reapply_con_label_set;
    assert_eq!(current_tag, 1);
    assert_eq!(
        env.ctx
            .process_context()
            .label_set(label_set)
            .get_concept_label_set_modification_tag(),
        current_tag
    );
    assert!(env.algo.is_individual_node_concept_label_set_modified(
        &mut root,
        current_tag,
        &mut env.ctx
    ));
    assert!(!env.algo.is_individual_node_concept_label_set_modified(
        &mut root,
        current_tag + 1,
        &mut env.ctx,
    ));
}

#[test]
fn concept_label_set_modified_increments_tag_on_each_call() {
    let mut env = build_env();
    let mut root = env.root;

    env.algo
        .set_individual_node_concept_label_set_modified(&mut root, &mut env.ctx);
    env.algo
        .set_individual_node_concept_label_set_modified(&mut root, &mut env.ctx);

    let current_tag = env
        .ctx
        .process_context()
        .used_process_tagger()
        .get_current_concept_label_set_modification_tag();
    let label_set = env
        .ctx
        .process_context()
        .node(root)
        .use_reapply_con_label_set;
    assert_eq!(current_tag, 2);
    assert_eq!(
        env.ctx
            .process_context()
            .label_set(label_set)
            .get_concept_label_set_modification_tag(),
        current_tag
    );
}

#[test]
fn add_marker_concept_to_individual_registers_marker_node() {
    let mut env = build_env();
    let marker = marker_concept(&mut env, 301);
    let mut root = env.root;

    env.algo.add_concept_to_individual(
        marker,
        false,
        &mut root,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );

    let entries = marker_entries(&env, marker);
    assert_eq!(entries, vec![(root, true)]);
}

#[test]
fn add_marker_concept_to_individual_skips_contained_duplicate() {
    let mut env = build_env();
    let marker = marker_concept(&mut env, 302);
    let mut root = env.root;

    for _ in 0..2 {
        env.algo.add_concept_to_individual(
            marker,
            false,
            &mut root,
            TrackPointId::NONE,
            false,
            true,
            &mut env.ctx,
        );
    }

    let entries = marker_entries(&env, marker);
    assert_eq!(entries, vec![(root, true)]);
}

#[test]
fn add_non_marker_concept_to_individual_does_not_allocate_marker_hash() {
    let mut env = build_env();
    let mut root = env.root;

    env.algo.add_concept_to_individual(
        env.concept_a,
        false,
        &mut root,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );

    assert!(
        env.ctx
            .processing_data_box()
            .use_marker_indi_node_hash
            .is_none(),
        "non-marker labels must not allocate the marker individual node hash"
    );
}

#[test]
fn marker_hash_keeps_deterministic_and_nondeterministic_entries_distinct() {
    let mut env = build_env();
    let marker = marker_concept(&mut env, 303);
    let deterministic_tp = deterministic_track_point(&mut env);
    let mut root = env.root;

    env.algo.add_concept_to_individual(
        marker,
        false,
        &mut root,
        deterministic_tp,
        false,
        true,
        &mut env.ctx,
    );
    let mut other = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(other)
        .set_individual_node_id(1);
    env.ctx
        .processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(1, other);
    env.algo.add_concept_to_individual(
        marker,
        false,
        &mut other,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );

    let mut entries = marker_entries(&env, marker);
    entries.sort_by_key(|(node, nondeterministic)| {
        (
            env.ctx.process_context().node(*node).individual_node_id(),
            *nondeterministic,
        )
    });
    assert_eq!(entries, vec![(root, false), (other, true)]);
}

#[test]
fn marker_hash_localization_preserves_inherited_entries() {
    let mut env = build_env();
    let marker = marker_concept(&mut env, 304);
    let mut root = env.root;

    env.algo.add_concept_to_individual(
        marker,
        false,
        &mut root,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );
    let inherited_hash = env.ctx.processing_data_box().use_marker_indi_node_hash;

    env.ctx.processing_data_box_mut().loc_marker_indi_node_hash = Id::NONE;
    env.ctx.processing_data_box_mut().use_marker_indi_node_hash = inherited_hash;

    let localized_hash = env.ctx.marker_individual_node_hash(true);
    assert_ne!(localized_hash, inherited_hash);
    assert!(!MarkerIndividualNodeHash::add_marker_individual_node(
        env.ctx.process_context_mut(),
        localized_hash,
        marker,
        root,
        true,
    ));

    let other = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(other)
        .set_individual_node_id(1);
    assert!(MarkerIndividualNodeHash::add_marker_individual_node(
        env.ctx.process_context_mut(),
        localized_hash,
        marker,
        other,
        true,
    ));

    assert_eq!(
        marker_entries(&env, marker),
        vec![(other, true), (root, true)]
    );
}

/// gap (a): the concept-processing-queue INSERT primitive — allocate a
/// `CConceptProcessDescriptor` and push it onto a node's `CConceptProcessingQueue`,
/// then take it back. This is the seed primitive the future full drive loop pops.
#[test]
fn concept_queue_insert_primitive() {
    let mut env = build_env();
    let root = env.root;

    // processIndi->getConceptProcessingQueue(true) — materialise the per-node queue.
    let queue = env
        .ctx
        .process_context_mut()
        .node_concept_processing_queue(root, true);
    assert!(
        queue.is_some(),
        "concept processing queue must be allocated"
    );
    assert!(
        env.ctx
            .process_context()
            .concept_proc_queue(queue)
            .is_empty(),
        "a fresh concept processing queue is empty"
    );

    // createConceptDescriptor + initConceptDescriptor(A, false, …).
    let con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    env.ctx.process_context_mut().con_desc_mut(con_des).concept = env.concept_a;

    // new CConceptProcessDescriptor; conProDes->init(conceptDescriptor, priority, …).
    let mut cpd_val = ConceptProcessDescriptor::new();
    cpd_val.concept_des = con_des;
    let cpd = env.ctx.process_context_mut().alloc_con_proc_desc(cpd_val);

    // conceptProcessingQueue->insertConceptProcessDescriptor(conProDes).
    ConceptProcessingQueue::insert_concept_process_descriptor(
        queue,
        cpd,
        env.ctx.process_context_mut(),
    );
    assert!(
        !env.ctx
            .process_context()
            .concept_proc_queue(queue)
            .is_empty(),
        "queue must be non-empty after insert"
    );

    // conProDes = conProcQueue->takeNextConceptDescriptorProcess() — the drive-loop pop.
    let taken = ConceptProcessingQueue::take_next_concept_descriptor_process(
        queue,
        env.ctx.process_context_mut(),
    );
    assert_eq!(taken, cpd, "take must return the inserted descriptor");
    assert!(
        env.ctx
            .process_context()
            .concept_proc_queue(queue)
            .is_empty(),
        "queue must be empty again after take"
    );
}

#[test]
fn priority_for_concept_uses_context_strategy() {
    let mut env = build_env();
    let root = env.root;

    let con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    env.ctx.process_context_mut().con_desc_mut(con_des).concept = env.concept_a;

    let priority = env.algo.priority_for_concept(con_des, root, &env.ctx);

    assert_eq!(priority.get_priority(), 14.0);
}

#[test]
fn add_individual_node_for_cache_unsatisfiable_retrieval_prepends_databox_queue() {
    let mut env = build_env();
    let mut first = env.root;
    let mut second = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));

    env.algo
        .add_individual_node_for_cache_unsatisfiable_retrieval(&mut first, &mut env.ctx);
    env.algo
        .add_individual_node_for_cache_unsatisfiable_retrieval(&mut second, &mut env.ctx);

    assert!(env
        .ctx
        .processing_data_box()
        .has_cache_testing_individual_nodes());
    assert_eq!(
        env.ctx
            .processing_data_box_mut()
            .take_next_cache_testing_individual_node(),
        second
    );
    assert_eq!(
        env.ctx
            .processing_data_box_mut()
            .take_next_cache_testing_individual_node(),
        first
    );
    assert!(!env
        .ctx
        .processing_data_box()
        .has_cache_testing_individual_nodes());
}

#[test]
fn take_next_process_individual_prefers_cache_test_queue() {
    let mut env = build_env();
    let mut cache_test_node = env.root;
    let immediate_node = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    let iq = env.ctx.get_individual_immediately_processing_queue(true);
    env.ctx
        .process_context_mut()
        .indi_unsorted_proc_queue_mut(iq)
        .insert_indiviudal_process_node(immediate_node);

    env.algo
        .add_individual_node_for_cache_unsatisfiable_retrieval(&mut cache_test_node, &mut env.ctx);

    let next = env.algo.take_next_process_individual(&mut env.ctx);

    assert_eq!(next, cache_test_node);
    assert!(env.algo.indi_node_conclude_unsat_caching);
    assert_eq!(
        env.algo.indi_node_from_queue_type,
        IndiNodeQueueType::Inqt_CacheTest
    );
}

/// Role-keyed reapply queues: add a descriptor under a role trigger, then reapply
/// that role and verify the descriptor is materialised into the node's concept
/// processing queue. This is the live-path counterpart of Konclude's
/// `addConceptToReapplyQueue(role,...)` + `applyReapplyQueueConcepts(role)`.
#[test]
fn role_reapply_queue_applies_to_concept_processing_queue() {
    use super::super::model::op;
    use super::super::model::role::Role;

    let mut env = build_env();
    let root = env.root;

    let role_r = {
        let mut r = Role::new();
        r.set_role_tag(70);
        env.ctx.ontology_arenas_mut().alloc_role(r)
    };
    let triggered_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(170);
        c.set_operator_code(op::CCAND);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(con_des);
        d.concept = triggered_concept;
        d.dep_track_point = TrackPointId::NONE;
    }

    env.algo.add_concept_to_reapply_queue_role(
        con_des,
        role_r,
        root,
        true,
        TrackPointId::NONE,
        &mut env.ctx,
    );
    assert!(
        env.algo
            .is_concept_in_reapply_queue_role(con_des, role_r, root, &mut env.ctx),
        "the descriptor must be present in the role-keyed reapply queue"
    );

    env.algo
        .apply_reapply_queue_concepts_role(root, role_r, &mut env.ctx);

    let queue = env
        .ctx
        .process_context_mut()
        .node_concept_processing_queue(root, false);
    assert!(
        queue.is_some(),
        "reapply must allocate/use the concept queue"
    );
    assert_eq!(
        env.ctx
            .process_context()
            .concept_proc_queue(queue)
            .get_descriptor_count(),
        1,
        "one reapplied descriptor must be queued for processing"
    );
    let taken = ConceptProcessingQueue::take_next_concept_descriptor_process(
        queue,
        env.ctx.process_context_mut(),
    );
    assert_eq!(
        env.ctx
            .process_context()
            .con_proc_desc(taken)
            .get_concept_descriptor(),
        con_des,
        "the queued process descriptor must wrap the reapplied concept descriptor"
    );
}

/// `getIndividualNodeLink` scans the source node's successor-role iterator for
/// the destination individual id and returns the first link with the requested
/// role.
#[test]
fn individual_node_link_lookup_returns_matching_successor_role_edge() {
    use super::super::model::role::Role;
    use super::super::process::edge::IndividualLinkEdge;
    use super::super::process::rs1::ReapplyQueueIterator;

    let mut env = build_env();
    let mut source = env.root;
    let mut destination = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(destination)
        .set_individual_node_id(1);
    env.ctx
        .processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(1, destination);

    let role_r = {
        let mut r = Role::new();
        r.set_role_tag(71);
        env.ctx.ontology_arenas_mut().alloc_role(r)
    };
    let other_role = {
        let mut r = Role::new();
        r.set_role_tag(72);
        env.ctx.ontology_arenas_mut().alloc_role(r)
    };
    let edge = {
        let mut edge = IndividualLinkEdge::new();
        edge.set_source_individual(source);
        edge.set_destination_individual(destination);
        edge.set_link_role(role_r);
        env.ctx.process_context_mut().alloc_edge(edge)
    };
    let mut reapply_it = ReapplyQueueIterator::empty();
    env.ctx
        .process_context_mut()
        .node_install_individual_link(source, edge, &mut reapply_it);

    assert_eq!(
        env.algo
            .get_individual_node_link(&mut source, &mut destination, role_r, &mut env.ctx),
        edge
    );
    assert_eq!(
        env.algo
            .get_individual_node_link(&mut source, &mut destination, other_role, &mut env.ctx),
        Id::NONE
    );
}

#[test]
fn create_new_individuals_links_reapplyed_installs_direct_role_edge() {
    use super::super::model::role::Role;
    use super::super::model::substrate::NegLink;

    let mut env = build_env();
    let mut source = env.root;
    let mut destination = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(destination)
        .set_individual_node_id(2);
    env.ctx
        .processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(2, destination);

    let role_r = {
        let mut r = Role::new();
        r.set_role_tag(73);
        env.ctx.ontology_arenas_mut().alloc_role(r)
    };
    let role_linker = [NegLink {
        target: role_r,
        negated: false,
    }];

    let edge = env.algo.create_new_individuals_links_reapplyed(
        source,
        destination,
        &role_linker,
        role_r,
        TrackPointId::NONE,
        true,
        &mut env.ctx,
    );
    assert!(edge.is_some());
    assert_eq!(
        env.ctx.process_context().edge(edge).get_source_individual(),
        source
    );
    assert_eq!(
        env.ctx
            .process_context()
            .edge(edge)
            .get_destination_individual(),
        destination
    );
    assert_eq!(
        env.algo
            .get_individual_node_link(&mut source, &mut destination, role_r, &mut env.ctx),
        edge
    );
}

#[test]
fn create_new_individuals_links_reapplyed_installs_inverse_role_edge() {
    use super::super::model::role::Role;
    use super::super::model::substrate::NegLink;

    let mut env = build_env();
    let mut source = env.root;
    let mut destination = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(destination)
        .set_individual_node_id(3);
    env.ctx
        .processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(3, destination);

    let role_r = {
        let mut r = Role::new();
        r.set_role_tag(74);
        env.ctx.ontology_arenas_mut().alloc_role(r)
    };
    let role_linker = [NegLink {
        target: role_r,
        negated: true,
    }];

    let edge = env.algo.create_new_individuals_links_reapplyed(
        source,
        destination,
        &role_linker,
        role_r,
        TrackPointId::NONE,
        true,
        &mut env.ctx,
    );
    assert!(edge.is_some());
    assert_eq!(
        env.ctx.process_context().edge(edge).get_source_individual(),
        destination
    );
    assert_eq!(
        env.ctx
            .process_context()
            .edge(edge)
            .get_destination_individual(),
        source
    );
    assert_eq!(
        env.algo
            .get_individual_node_link(&mut destination, &mut source, role_r, &mut env.ctx),
        edge
    );
}

#[test]
fn create_new_individuals_link_reapplyed_installs_single_role_edge() {
    use super::super::model::role::Role;

    let mut env = build_env();
    let mut source = env.root;
    let mut destination = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(destination)
        .set_individual_node_id(4);
    env.ctx
        .processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(4, destination);

    let role_r = {
        let mut r = Role::new();
        r.set_role_tag(75);
        env.ctx.ontology_arenas_mut().alloc_role(r)
    };

    let edge = env.algo.create_new_individuals_link_reapplyed(
        source,
        source,
        destination,
        role_r,
        TrackPointId::NONE,
        &mut env.ctx,
    );
    assert!(edge.is_some());
    assert_eq!(
        env.ctx.process_context().edge(edge).get_source_individual(),
        source
    );
    assert_eq!(
        env.ctx
            .process_context()
            .edge(edge)
            .get_destination_individual(),
        destination
    );
    assert_eq!(
        env.algo
            .get_individual_node_link(&mut source, &mut destination, role_r, &mut env.ctx),
        edge
    );
}

#[test]
fn disjoint_role_links_install_negation_disjoint_edge() {
    use super::super::model::role::Role;
    use super::super::model::substrate::NegLink;

    let mut env = build_env();
    let mut source = env.root;
    let mut destination = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(destination)
        .set_individual_node_id(5);
    env.ctx
        .processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(5, destination);

    let role_s = {
        let mut r = Role::new();
        r.set_role_tag(77);
        env.ctx.ontology_arenas_mut().alloc_role(r)
    };
    let disjoint_roles = [NegLink {
        target: role_s,
        negated: false,
    }];

    env.algo.create_individual_node_disjoint_roles_links(
        &mut source,
        &mut destination,
        &disjoint_roles,
        TrackPointId::NONE,
        &mut env.ctx,
    );

    let dest_id = env
        .ctx
        .process_context()
        .node(destination)
        .individual_node_id();
    let mut it = env
        .ctx
        .process_context()
        .node_disjoint_successor_role_iterator(source, dest_id);
    assert!(it.has_next(), "disjoint edge must be installed");
    let edge = it.next(true);
    assert_eq!(
        env.ctx
            .process_context()
            .disjoint_edge(edge)
            .get_link_role(),
        role_s
    );
    assert!(env
        .ctx
        .process_context()
        .node(source)
        .has_disjoint_role_connections());
    assert!(env
        .ctx
        .process_context()
        .node(destination)
        .has_disjoint_role_connections());
}

#[test]
fn disjoint_role_link_clashes_with_existing_role_edge() {
    use super::super::model::role::Role;
    use super::super::model::substrate::NegLink;

    let mut env = build_env();
    let mut source = env.root;
    let mut destination = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(destination)
        .set_individual_node_id(6);
    env.ctx
        .processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(6, destination);

    let role_s = {
        let mut r = Role::new();
        r.set_role_tag(78);
        env.ctx.ontology_arenas_mut().alloc_role(r)
    };
    let edge = env.algo.create_new_individuals_link_reapplyed(
        source,
        source,
        destination,
        role_s,
        TrackPointId::NONE,
        &mut env.ctx,
    );
    assert!(edge.is_some());

    let disjoint_roles = [NegLink {
        target: role_s,
        negated: false,
    }];
    env.algo.create_individual_node_disjoint_roles_links(
        &mut source,
        &mut destination,
        &disjoint_roles,
        TrackPointId::NONE,
        &mut env.ctx,
    );

    match env.ctx.pending_signal() {
        CalcSignal::Clash(_) => {}
        other => panic!("expected a Clash signal, got {:?}", other),
    }
}

#[test]
fn role_link_install_clashes_with_existing_negation_disjoint_edge() {
    use super::super::model::role::Role;
    use super::super::process::edge::IndividualLinkEdge;

    let mut env = build_env();
    let mut source = env.root;
    let mut destination = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(destination)
        .set_individual_node_id(7);
    env.ctx
        .processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(7, destination);

    let role_s = {
        let mut r = Role::new();
        r.set_role_tag(79);
        env.ctx.ontology_arenas_mut().alloc_role(r)
    };
    env.algo.create_individual_node_negation_link(
        &mut source,
        &mut destination,
        role_s,
        TrackPointId::NONE,
        &mut env.ctx,
    );
    assert_eq!(env.ctx.pending_signal(), CalcSignal::Continue);

    let source_id = env.ctx.process_context().node(source).individual_node_id();
    let conn_set = env
        .ctx
        .process_context()
        .node(destination)
        .use_conn_succ_set;
    assert!(
        env.ctx
            .process_context()
            .conn_succ_set(conn_set)
            .has_connection_successor(source_id),
        "negation link must register the source as a connection successor"
    );

    let edge = {
        let mut edge = IndividualLinkEdge::new();
        edge.set_source_individual(source);
        edge.set_destination_individual(destination);
        edge.set_link_role(role_s);
        env.ctx.process_context_mut().alloc_edge(edge)
    };
    let reapply_it = env.algo.install_individual_node_role_link_reapplied(
        &mut source,
        &mut destination,
        edge,
        &mut env.ctx,
    );

    assert!(!reapply_it.has_next());
    match env.ctx.pending_signal() {
        CalcSignal::Clash(_) => {}
        other => panic!("expected a Clash signal, got {:?}", other),
    }
}

#[test]
fn create_new_individuals_links_installs_direct_role_edge() {
    use super::super::model::role::Role;
    use super::super::model::substrate::NegLink;

    let mut env = build_env();
    let mut source = env.root;
    let mut destination = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(destination)
        .set_individual_node_id(8);
    env.ctx
        .processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(8, destination);

    let role_r = {
        let mut r = Role::new();
        r.set_role_tag(80);
        env.ctx.ontology_arenas_mut().alloc_role(r)
    };
    let role_linker = [NegLink {
        target: role_r,
        negated: false,
    }];

    let edge = env.algo.create_new_individuals_links(
        &mut source,
        &mut destination,
        &role_linker,
        role_r,
        TrackPointId::NONE,
        &mut env.ctx,
    );

    assert!(edge.is_some());
    assert_eq!(
        env.ctx.process_context().edge(edge).get_source_individual(),
        source
    );
    assert_eq!(
        env.ctx
            .process_context()
            .edge(edge)
            .get_destination_individual(),
        destination
    );
    assert_eq!(
        env.ctx
            .process_context()
            .edge(edge)
            .get_creator_individual(),
        source
    );
    assert_eq!(
        env.algo
            .get_individual_node_link(&mut source, &mut destination, role_r, &mut env.ctx),
        edge
    );
    let source_id = env.ctx.process_context().node(source).individual_node_id();
    let dest_conn_set = env
        .ctx
        .process_context()
        .node(destination)
        .use_conn_succ_set;
    assert!(
        env.ctx
            .process_context()
            .conn_succ_set(dest_conn_set)
            .has_connection_successor(source_id),
        "destination must record the source connection successor"
    );
}

#[test]
fn role_link_install_updates_occurrence_statistics_for_first_successor_link() {
    use super::super::model::role::Role;

    let mut env = build_env();
    env.algo.conf_occurrence_statistics_collecting = true;
    env.algo.opt_collect_occurrence_statistics = true;

    let mut source = env.root;
    let mut destination = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(destination)
        .set_individual_node_id(208);
    env.ctx
        .processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(208, destination);

    let role_r = {
        let mut r = Role::new();
        r.set_role_tag(0);
        env.ctx.ontology_arenas_mut().alloc_role(r)
    };
    let mut edge = super::super::process::edge::IndividualLinkEdge::new();
    edge.creator = source;
    edge.set_source_individual(source);
    edge.set_destination_individual(destination);
    edge.set_link_role(role_r);
    edge.set_dependency_track_point(TrackPointId::NONE);
    let edge = env.ctx.process_context_mut().alloc_edge(edge);

    env.algo
        .install_individual_node_role_link(&mut source, &mut destination, edge, &mut env.ctx);

    let stats = env
        .ctx
        .occurrence_statistics_cache_handler_mut()
        .accummulated_role_data_occurrence_statistics(0);
    assert_eq!(stats.get_deterministic_instance_occurrences_count(), 0);
    assert_eq!(stats.get_non_deterministic_instance_occurrences_count(), 1);
    assert_eq!(stats.get_existential_instance_occurrences_count(), 1);
    assert_eq!(stats.get_individual_instance_occurrences_count(), 0);
    assert_eq!(stats.get_outgoing_node_instance_occurrences_count(), 1);
    assert_eq!(stats.get_incoming_node_instance_occurrences_count(), 1);
}

#[test]
fn role_link_reapplied_occurrence_statistics_skip_duplicate_successor_link() {
    use super::super::model::role::Role;

    let mut env = build_env();
    env.algo.conf_occurrence_statistics_collecting = true;
    env.algo.opt_collect_occurrence_statistics = true;

    let mut source = env.root;
    let mut destination = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(destination)
        .set_individual_node_id(209);
    env.ctx
        .processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(209, destination);

    let role_r = {
        let mut r = Role::new();
        r.set_role_tag(0);
        env.ctx.ontology_arenas_mut().alloc_role(r)
    };
    for _ in 0..2 {
        let mut edge = super::super::process::edge::IndividualLinkEdge::new();
        edge.creator = source;
        edge.set_source_individual(source);
        edge.set_destination_individual(destination);
        edge.set_link_role(role_r);
        edge.set_dependency_track_point(TrackPointId::NONE);
        let edge = env.ctx.process_context_mut().alloc_edge(edge);
        let _ = env.algo.install_individual_node_role_link_reapplied(
            &mut source,
            &mut destination,
            edge,
            &mut env.ctx,
        );
    }

    let stats = env
        .ctx
        .occurrence_statistics_cache_handler_mut()
        .accummulated_role_data_occurrence_statistics(0);
    assert_eq!(
        stats.get_outgoing_node_instance_occurrences_count(),
        1,
        "Konclude updates occurrence stats only for the first role-successor link"
    );
    assert_eq!(stats.get_incoming_node_instance_occurrences_count(), 1);
    assert_eq!(stats.get_deterministic_instance_occurrences_count(), 0);
    assert_eq!(stats.get_non_deterministic_instance_occurrences_count(), 1);
}

#[test]
fn role_link_occurrence_statistics_do_not_update_after_disjoint_clash() {
    use super::super::model::role::Role;

    let mut env = build_env();
    env.algo.conf_occurrence_statistics_collecting = true;
    env.algo.opt_collect_occurrence_statistics = true;

    let mut source = env.root;
    let mut destination = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(destination)
        .set_individual_node_id(210);
    env.ctx
        .processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(210, destination);

    let role_r = {
        let mut r = Role::new();
        r.set_role_tag(0);
        env.ctx.ontology_arenas_mut().alloc_role(r)
    };
    env.algo.create_individual_node_negation_link(
        &mut source,
        &mut destination,
        role_r,
        TrackPointId::NONE,
        &mut env.ctx,
    );

    let mut edge = super::super::process::edge::IndividualLinkEdge::new();
    edge.creator = source;
    edge.set_source_individual(source);
    edge.set_destination_individual(destination);
    edge.set_link_role(role_r);
    edge.set_dependency_track_point(TrackPointId::NONE);
    let edge = env.ctx.process_context_mut().alloc_edge(edge);

    let _ = env.algo.install_individual_node_role_link_reapplied(
        &mut source,
        &mut destination,
        edge,
        &mut env.ctx,
    );

    match env.ctx.pending_signal() {
        CalcSignal::Clash(_) => {}
        other => panic!("expected a Clash signal, got {:?}", other),
    }
    let stats = env
        .ctx
        .occurrence_statistics_cache_handler_mut()
        .accummulated_role_data_occurrence_statistics(0);
    assert_eq!(stats.get_outgoing_node_instance_occurrences_count(), 0);
    assert_eq!(stats.get_incoming_node_instance_occurrences_count(), 0);
    assert_eq!(stats.get_deterministic_instance_occurrences_count(), 0);
}

#[test]
fn create_new_individuals_links_installs_inverse_role_edge_and_reverse_connection() {
    use super::super::model::role::Role;
    use super::super::model::substrate::NegLink;

    let mut env = build_env();
    let mut source = env.root;
    let mut destination = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(destination)
        .set_individual_node_id(9);
    env.ctx
        .processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(9, destination);

    let role_r = {
        let mut r = Role::new();
        r.set_role_tag(81);
        env.ctx.ontology_arenas_mut().alloc_role(r)
    };
    let role_linker = [NegLink {
        target: role_r,
        negated: true,
    }];

    let edge = env.algo.create_new_individuals_links(
        &mut source,
        &mut destination,
        &role_linker,
        role_r,
        TrackPointId::NONE,
        &mut env.ctx,
    );

    assert!(edge.is_some());
    assert_eq!(
        env.ctx.process_context().edge(edge).get_source_individual(),
        destination
    );
    assert_eq!(
        env.ctx
            .process_context()
            .edge(edge)
            .get_destination_individual(),
        source
    );
    assert_eq!(
        env.ctx
            .process_context()
            .edge(edge)
            .get_creator_individual(),
        source
    );
    assert_eq!(
        env.algo
            .get_individual_node_link(&mut destination, &mut source, role_r, &mut env.ctx),
        edge
    );

    let source_id = env.ctx.process_context().node(source).individual_node_id();
    let destination_id = env
        .ctx
        .process_context()
        .node(destination)
        .individual_node_id();
    let source_conn_set = env.ctx.process_context().node(source).use_conn_succ_set;
    let destination_conn_set = env
        .ctx
        .process_context()
        .node(destination)
        .use_conn_succ_set;
    assert!(
        env.ctx
            .process_context()
            .conn_succ_set(source_conn_set)
            .has_connection_successor(destination_id),
        "inverse link generation must register destination on the source"
    );
    assert!(
        env.ctx
            .process_context()
            .conn_succ_set(destination_conn_set)
            .has_connection_successor(source_id),
        "destination must always register the source"
    );
}

#[test]
fn create_new_individuals_link_installs_single_role_edge() {
    use super::super::model::role::Role;

    let mut env = build_env();
    let mut source = env.root;
    let mut destination = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(destination)
        .set_individual_node_id(10);
    env.ctx
        .processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(10, destination);

    let role_r = {
        let mut r = Role::new();
        r.set_role_tag(82);
        env.ctx.ontology_arenas_mut().alloc_role(r)
    };

    let mut creator = source;
    let edge = env.algo.create_new_individuals_link(
        &mut creator,
        &mut source,
        &mut destination,
        role_r,
        TrackPointId::NONE,
        &mut env.ctx,
    );

    assert!(edge.is_some());
    assert_eq!(
        env.ctx.process_context().edge(edge).get_source_individual(),
        source
    );
    assert_eq!(
        env.ctx
            .process_context()
            .edge(edge)
            .get_destination_individual(),
        destination
    );
    assert_eq!(
        env.ctx
            .process_context()
            .edge(edge)
            .get_creator_individual(),
        source
    );
    assert_eq!(
        env.algo
            .get_individual_node_link(&mut source, &mut destination, role_r, &mut env.ctx),
        edge
    );
}

#[test]
fn create_new_individuals_link_clashes_with_existing_negation_disjoint_edge() {
    use super::super::model::role::Role;

    let mut env = build_env();
    let mut source = env.root;
    let mut destination = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(destination)
        .set_individual_node_id(11);
    env.ctx
        .processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(11, destination);

    let role_r = {
        let mut r = Role::new();
        r.set_role_tag(83);
        env.ctx.ontology_arenas_mut().alloc_role(r)
    };
    env.algo.create_individual_node_negation_link(
        &mut source,
        &mut destination,
        role_r,
        TrackPointId::NONE,
        &mut env.ctx,
    );
    assert_eq!(env.ctx.pending_signal(), CalcSignal::Continue);

    let mut creator = source;
    let edge = env.algo.create_new_individuals_link(
        &mut creator,
        &mut source,
        &mut destination,
        role_r,
        TrackPointId::NONE,
        &mut env.ctx,
    );

    assert!(edge.is_some());
    match env.ctx.pending_signal() {
        CalcSignal::Clash(_) => {}
        other => panic!("expected a Clash signal, got {:?}", other),
    }
}

#[test]
fn create_individuals_distinct_pair_installs_symmetric_distinct_edge() {
    let mut env = build_env();
    let mut source = env.root;
    let mut destination = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(destination)
        .set_individual_node_id(12);
    env.ctx
        .processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(12, destination);

    env.algo.create_individuals_distinct_pair(
        &mut source,
        &mut destination,
        TrackPointId::NONE,
        &mut env.ctx,
    );

    let source_id = env.ctx.process_context().node(source).individual_node_id();
    let destination_id = env
        .ctx
        .process_context()
        .node(destination)
        .individual_node_id();
    let source_hash = env.ctx.process_context().node(source).use_distinct_hash;
    let destination_hash = env
        .ctx
        .process_context()
        .node(destination)
        .use_distinct_hash;
    let edge_from_source = env
        .ctx
        .process_context()
        .distinct_hash(source_hash)
        .get_individual_distinct_edge(destination_id);
    let edge_from_destination = env
        .ctx
        .process_context()
        .distinct_hash(destination_hash)
        .get_individual_distinct_edge(source_id);

    assert!(
        edge_from_source.is_some(),
        "source distinct hash must point at destination"
    );
    assert_eq!(
        edge_from_source, edge_from_destination,
        "both endpoints must reference the same CDistinctEdge"
    );
    assert_eq!(
        env.ctx
            .process_context()
            .distinct_edge(edge_from_source)
            .get_source_individual(),
        source
    );
    assert_eq!(
        env.ctx
            .process_context()
            .distinct_edge(edge_from_source)
            .get_destination_individual(),
        destination
    );
    assert_eq!(
        env.ctx
            .process_context()
            .distinct_edge(edge_from_source)
            .get_dependency_track_point(),
        TrackPointId::NONE
    );
}

#[test]
fn create_individuals_distinct_installs_all_unordered_pairs() {
    let mut env = build_env();
    let first = env.root;
    let second = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(second)
        .set_individual_node_id(13);
    env.ctx
        .processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(13, second);
    let third = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(third)
        .set_individual_node_id(14);
    env.ctx
        .processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(14, third);

    let mut nodes = vec![first, second, third];
    env.algo
        .create_individuals_distinct(&mut nodes, TrackPointId::NONE, &mut env.ctx);

    let first_id = env.ctx.process_context().node(first).individual_node_id();
    let second_id = env.ctx.process_context().node(second).individual_node_id();
    let third_id = env.ctx.process_context().node(third).individual_node_id();
    let first_hash = env.ctx.process_context().node(first).use_distinct_hash;
    let second_hash = env.ctx.process_context().node(second).use_distinct_hash;
    let third_hash = env.ctx.process_context().node(third).use_distinct_hash;

    assert_eq!(
        env.ctx
            .process_context()
            .distinct_hash(first_hash)
            .get_distinct_count(),
        2
    );
    assert_eq!(
        env.ctx
            .process_context()
            .distinct_hash(second_hash)
            .get_distinct_count(),
        2
    );
    assert_eq!(
        env.ctx
            .process_context()
            .distinct_hash(third_hash)
            .get_distinct_count(),
        2
    );

    let first_second = env
        .ctx
        .process_context()
        .distinct_hash(first_hash)
        .get_individual_distinct_edge(second_id);
    let second_first = env
        .ctx
        .process_context()
        .distinct_hash(second_hash)
        .get_individual_distinct_edge(first_id);
    let first_third = env
        .ctx
        .process_context()
        .distinct_hash(first_hash)
        .get_individual_distinct_edge(third_id);
    let third_first = env
        .ctx
        .process_context()
        .distinct_hash(third_hash)
        .get_individual_distinct_edge(first_id);
    let second_third = env
        .ctx
        .process_context()
        .distinct_hash(second_hash)
        .get_individual_distinct_edge(third_id);
    let third_second = env
        .ctx
        .process_context()
        .distinct_hash(third_hash)
        .get_individual_distinct_edge(second_id);

    assert!(first_second.is_some());
    assert!(first_third.is_some());
    assert!(second_third.is_some());
    assert_eq!(first_second, second_first);
    assert_eq!(first_third, third_first);
    assert_eq!(second_third, third_second);
    assert_ne!(first_second, first_third);
    assert_ne!(first_second, second_third);
    assert_ne!(first_third, second_third);
}

#[test]
fn create_new_empty_individual_uses_next_sequential_id_after_root() {
    let mut env = build_env();

    let individual = env.algo.create_new_empty_individual(&mut env.ctx);

    assert_eq!(
        env.ctx
            .process_context()
            .node(individual)
            .individual_node_id(),
        1
    );
    assert_eq!(
        env.ctx
            .processing_data_box()
            .individual_process_node_vector()
            .get_data(1),
        individual
    );
}

#[test]
fn create_new_empty_individual_registers_next_id_and_flags() {
    let mut env = build_env();
    env.algo.opt_consistence_node_marking = true;
    env.algo.opt_incremental_compatible_expansion = true;
    env.ctx
        .processing_data_box_mut()
        .set_first_possible_individual_node_id(42);
    env.ctx
        .processing_data_box_mut()
        .set_incremental_expansion_id(99);

    let individual = env.algo.create_new_empty_individual(&mut env.ctx);
    let node = env.ctx.process_context().node(individual);

    assert_eq!(node.individual_node_id(), 42);
    assert_eq!(
        env.ctx
            .processing_data_box()
            .individual_process_node_vector()
            .get_data(42),
        individual
    );
    assert!(node
        .has_processing_restriction_flags(IndividualProcessNode::PRF_CONSNODEPREPARATIONINDINODE));
    assert!(node.has_processing_restriction_flags(IndividualProcessNode::PRF_INCREMENTALEXPANDING));
    assert_eq!(node.incremental_expansion_id(), 99);
}

#[test]
fn create_new_individual_seeds_object_top_concept() {
    let mut env = build_env();

    let mut individual = env
        .algo
        .create_new_individual(TrackPointId::NONE, false, &mut env.ctx);

    assert_eq!(
        env.ctx
            .process_context()
            .node(individual)
            .dependency_track_point(),
        TrackPointId::NONE
    );
    assert!(env.algo.contains_individual_node_concept(
        &mut individual,
        env.top_concept,
        None,
        &mut env.ctx
    ));
    assert!(!env
        .ctx
        .process_context()
        .node(individual)
        .is_extended_queue_processing());
    assert!(!env
        .ctx
        .process_context()
        .node(individual)
        .has_processing_restriction_flags(IndividualProcessNode::PRF_CONCRETEDATAINDINODE));
}

#[test]
fn create_new_individual_seeds_data_top_range_and_data_flags() {
    let mut env = build_env();

    let mut individual = env
        .algo
        .create_new_individual(TrackPointId::NONE, true, &mut env.ctx);

    assert!(env.algo.contains_individual_node_concept(
        &mut individual,
        env.top_data_range_concept,
        None,
        &mut env.ctx
    ));
    assert!(env
        .ctx
        .process_context()
        .node(individual)
        .is_extended_queue_processing());
    assert!(env
        .ctx
        .process_context()
        .node(individual)
        .has_processing_restriction_flags(IndividualProcessNode::PRF_CONCRETEDATAINDINODE));
}

#[test]
fn up_to_date_individual_helpers_follow_node_vector_availability() {
    let mut env = build_env();
    let old = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(old)
        .set_individual_node_id(43);
    env.ctx
        .process_context_mut()
        .node_mut(old)
        .set_localization_tag(0)
        .set_relocalized(true);
    let current = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(current)
        .set_individual_node_id(43)
        .set_localization_tag(2);
    env.ctx
        .processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(43, current);
    env.ctx
        .process_context_mut()
        .used_process_tagger
        .set_current_localization_tag(1);

    assert_eq!(
        env.algo
            .get_available_up_to_date_individual(43, &mut env.ctx),
        current
    );
    assert_eq!(
        env.algo
            .get_available_up_to_date_individual(44, &mut env.ctx),
        NodeId::NONE
    );
    assert_eq!(
        env.algo.get_up_to_date_individual(old, &mut env.ctx),
        current
    );
    assert_eq!(
        env.algo.get_up_to_date_individual(current, &mut env.ctx),
        current
    );
}

#[test]
fn role_successor_concept_scanners_find_labeled_successors() {
    use super::super::model::role::Role;
    use super::super::model::substrate::NegLink;

    let mut env = build_env();
    let mut source = env.root;
    let mut first = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(first)
        .set_individual_node_id(50);
    env.ctx
        .processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(50, first);
    let mut second = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(second)
        .set_individual_node_id(51);
    env.ctx
        .processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(51, second);

    let role_r = {
        let mut r = Role::new();
        r.set_role_tag(84);
        env.ctx.ontology_arenas_mut().alloc_role(r)
    };
    let other_role = {
        let mut r = Role::new();
        r.set_role_tag(85);
        env.ctx.ontology_arenas_mut().alloc_role(r)
    };
    let concept_b = {
        let mut c = Concept::new();
        c.set_concept_tag(184);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };

    let mut creator = source;
    env.algo.create_new_individuals_link(
        &mut creator,
        &mut source,
        &mut first,
        role_r,
        TrackPointId::NONE,
        &mut env.ctx,
    );
    creator = source;
    env.algo.create_new_individuals_link(
        &mut creator,
        &mut source,
        &mut second,
        role_r,
        TrackPointId::NONE,
        &mut env.ctx,
    );
    env.algo.add_concept_to_individual(
        env.concept_a,
        false,
        &mut first,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );
    env.algo.add_concept_to_individual(
        concept_b,
        true,
        &mut first,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );
    env.algo.add_concept_to_individual(
        env.concept_a,
        true,
        &mut second,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );

    assert!(env.algo.has_role_successor_concept(
        &mut source,
        role_r,
        env.concept_a,
        false,
        &mut env.ctx
    ));
    assert!(env.algo.has_role_successor_concept(
        &mut source,
        role_r,
        env.concept_a,
        true,
        &mut env.ctx
    ));
    assert!(!env.algo.has_role_successor_concept(
        &mut source,
        other_role,
        env.concept_a,
        false,
        &mut env.ctx
    ));

    let required = [
        NegLink {
            target: env.concept_a,
            negated: false,
        },
        NegLink {
            target: concept_b,
            negated: true,
        },
    ];
    assert!(env.algo.has_role_successor_concepts(
        &mut source,
        role_r,
        &required,
        false,
        &mut env.ctx
    ));
    assert_eq!(
        env.algo.get_role_successor_with_concepts(
            &mut source,
            role_r,
            &required,
            false,
            &mut env.ctx
        ),
        first
    );

    let impossible = [NegLink {
        target: concept_b,
        negated: false,
    }];
    assert!(!env.algo.has_role_successor_concepts(
        &mut source,
        role_r,
        &impossible,
        false,
        &mut env.ctx
    ));
    assert_eq!(
        env.algo.get_role_successor_with_concepts(
            &mut source,
            role_r,
            &impossible,
            false,
            &mut env.ctx
        ),
        NodeId::NONE
    );
}

#[test]
fn distinct_role_successor_concept_scanner_counts_distinct_labeled_successors() {
    use super::super::model::role::Role;
    use super::super::model::substrate::NegLink;

    let mut env = build_env();
    let mut source = env.root;
    let mut first = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(first)
        .set_individual_node_id(50);
    env.ctx
        .processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(50, first);
    let mut second = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(second)
        .set_individual_node_id(51);
    env.ctx
        .processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(51, second);
    let mut third = env
        .ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .node_mut(third)
        .set_individual_node_id(52);
    env.ctx
        .processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(52, third);

    let role_r = {
        let mut r = Role::new();
        r.set_role_tag(86);
        env.ctx.ontology_arenas_mut().alloc_role(r)
    };
    let other_role = {
        let mut r = Role::new();
        r.set_role_tag(87);
        env.ctx.ontology_arenas_mut().alloc_role(r)
    };

    for target in [first, second, third] {
        let mut creator = source;
        let mut target = target;
        env.algo.create_new_individuals_link(
            &mut creator,
            &mut source,
            &mut target,
            role_r,
            TrackPointId::NONE,
            &mut env.ctx,
        );
    }
    env.algo.create_individuals_distinct_pair(
        &mut first,
        &mut second,
        TrackPointId::NONE,
        &mut env.ctx,
    );

    for target in [&mut first, &mut second, &mut third] {
        env.algo.add_concept_to_individual(
            env.concept_a,
            false,
            target,
            TrackPointId::NONE,
            false,
            true,
            &mut env.ctx,
        );
    }

    assert!(env
        .algo
        .has_individuals_link(&mut source, &mut first, role_r, true, &mut env.ctx));
    assert!(!env.algo.has_individuals_link(
        &mut source,
        &mut first,
        other_role,
        true,
        &mut env.ctx
    ));

    let required = [NegLink {
        target: env.concept_a,
        negated: false,
    }];
    assert!(env.algo.has_distinct_role_successor_concepts(
        &mut source,
        role_r,
        &required,
        false,
        2,
        &mut env.ctx
    ));
    assert!(!env.algo.has_distinct_role_successor_concepts(
        &mut source,
        role_r,
        &required,
        false,
        3,
        &mut env.ctx
    ));
    assert!(!env.algo.has_distinct_role_successor_concepts(
        &mut source,
        other_role,
        &required,
        false,
        2,
        &mut env.ctx
    ));

    let impossible = [NegLink {
        target: env.concept_a,
        negated: true,
    }];
    assert!(!env.algo.has_distinct_role_successor_concepts(
        &mut source,
        role_r,
        &impossible,
        false,
        2,
        &mut env.ctx
    ));
}

#[test]
fn create_successor_individual_builds_ancestor_link_and_labels_successor() {
    use super::super::model::role::Role;
    use super::super::model::substrate::NegLink;

    let mut env = build_env();
    let mut source = env.root;
    env.ctx
        .process_context_mut()
        .node_mut(source)
        .set_individual_ancestor_depth(4)
        .add_processing_restriction_flags(
            IndividualProcessNode::PRF_SATISFIABLECACHED
                | IndividualProcessNode::PRF_ANCESTORSIGNATUREBLOCKINGCACHED
                | IndividualProcessNode::PRF_SATURATIONBLOCKINGCACHED,
        );

    let role_r = {
        let mut r = Role::new();
        r.set_role_tag(88);
        env.ctx.ontology_arenas_mut().alloc_role(r)
    };
    let concept_b = {
        let mut c = Concept::new();
        c.set_concept_tag(188);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let role_linker = [NegLink {
        target: role_r,
        negated: false,
    }];
    let concept_linker = [
        NegLink {
            target: env.concept_a,
            negated: false,
        },
        NegLink {
            target: concept_b,
            negated: true,
        },
    ];

    let succ = env.algo.create_successor_individual(
        &mut source,
        ConDescId::NONE,
        &role_linker,
        role_r,
        &concept_linker,
        false,
        TrackPointId::NONE,
        SatNodeId::NONE,
        &mut env.ctx,
    );

    assert!(succ.is_some());
    let succ_node = env.ctx.process_context().node(succ);
    assert_eq!(succ_node.individual_ancestor_depth(), 5);
    assert!(succ_node.has_partial_processing_restriction_flags(
        IndividualProcessNode::PRF_ANCESTORSATISFIABLECACHED
    ));
    assert!(succ_node.has_partial_processing_restriction_flags(
        IndividualProcessNode::PRF_ANCESTORSIGNATUREBLOCKINGCACHED
    ));
    assert!(succ_node.has_partial_processing_restriction_flags(
        IndividualProcessNode::PRF_ANCESTORSATURATIONBLOCKINGCACHED
    ));
    let ancestor_link = succ_node.get_ancestor_link();
    assert!(ancestor_link.is_some());
    let edge = env.ctx.process_context().edge(ancestor_link);
    assert_eq!(edge.get_source_individual(), source);
    assert_eq!(edge.get_destination_individual(), succ);
    assert_eq!(edge.get_link_role(), role_r);

    let mut succ_for_link_check = succ;
    assert!(env.algo.has_individuals_link(
        &mut source,
        &mut succ_for_link_check,
        role_r,
        true,
        &mut env.ctx
    ));
    assert!(env.algo.has_role_successor_concepts(
        &mut source,
        role_r,
        &concept_linker,
        false,
        &mut env.ctx
    ));
}

#[test]
fn create_distinct_successor_individuals_builds_pairwise_distinct_labeled_successors() {
    use super::super::model::role::Role;
    use super::super::model::substrate::NegLink;

    let mut env = build_env();
    let mut source = env.root;
    env.ctx
        .process_context_mut()
        .node_mut(source)
        .set_individual_ancestor_depth(2)
        .add_processing_restriction_flags(
            IndividualProcessNode::PRF_ANCESTORSATISFIABLECACHED
                | IndividualProcessNode::PRF_SIGNATUREBLOCKINGCACHED,
        );

    let role_r = {
        let mut r = Role::new();
        r.set_role_tag(89);
        env.ctx.ontology_arenas_mut().alloc_role(r)
    };
    let concept_b = {
        let mut c = Concept::new();
        c.set_concept_tag(189);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let role_linker = [NegLink {
        target: role_r,
        negated: false,
    }];
    let concept_linker = [
        NegLink {
            target: env.concept_a,
            negated: false,
        },
        NegLink {
            target: concept_b,
            negated: true,
        },
    ];
    let mut successors = Vec::new();

    env.algo.create_distinct_successor_individuals(
        &mut source,
        ConDescId::NONE,
        &mut successors,
        &role_linker,
        role_r,
        &concept_linker,
        false,
        TrackPointId::NONE,
        3,
        &mut env.ctx,
    );

    assert_eq!(successors.len(), 3);
    let successor_ids: Vec<_> = successors
        .iter()
        .map(|succ| env.ctx.process_context().node(*succ).individual_node_id())
        .collect();
    for (index, succ) in successors.iter().copied().enumerate() {
        let succ_node = env.ctx.process_context().node(succ);
        assert_eq!(succ_node.individual_ancestor_depth(), 3);
        assert!(succ_node.has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_ANCESTORSATISFIABLECACHED
        ));
        assert!(succ_node.has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_ANCESTORSIGNATUREBLOCKINGCACHED
        ));
        let ancestor_link = succ_node.get_ancestor_link();
        assert!(ancestor_link.is_some());
        let edge = env.ctx.process_context().edge(ancestor_link);
        assert_eq!(edge.get_source_individual(), source);
        assert_eq!(edge.get_destination_individual(), succ);
        assert_eq!(edge.get_link_role(), role_r);

        let distinct_hash = env.ctx.process_context().node_distinct_hash_existing(succ);
        assert!(distinct_hash.is_some());
        assert_eq!(
            env.ctx
                .process_context()
                .distinct_hash(distinct_hash)
                .get_distinct_count(),
            2
        );
        for (other_index, other_id) in successor_ids.iter().copied().enumerate() {
            if other_index != index {
                assert!(env
                    .ctx
                    .process_context()
                    .distinct_hash(distinct_hash)
                    .is_individual_distinct(other_id));
            }
        }
    }

    assert!(env.algo.has_distinct_role_successor_concepts(
        &mut source,
        role_r,
        &concept_linker,
        false,
        3,
        &mut env.ctx
    ));
}

#[test]
fn try_extend_functional_successor_individual_reuses_existing_successor() {
    use super::super::model::role::Role;
    use super::super::model::substrate::NegLink;

    let mut env = build_env();
    let mut source = env.root;
    let mut succ = env
        .algo
        .create_new_individual(TrackPointId::NONE, false, &mut env.ctx);

    let functional_role = {
        let mut r = Role::new();
        r.set_role_tag(90);
        r.set_functional(true);
        env.ctx.ontology_arenas_mut().alloc_role(r)
    };
    let extra_role = {
        let mut r = Role::new();
        r.set_role_tag(91);
        env.ctx.ontology_arenas_mut().alloc_role(r)
    };
    let inverse_role = {
        let mut r = Role::new();
        r.set_role_tag(92);
        env.ctx.ontology_arenas_mut().alloc_role(r)
    };
    let concept_b = {
        let mut c = Concept::new();
        c.set_concept_tag(190);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };

    let mut creator = source;
    env.algo.create_new_individuals_link(
        &mut creator,
        &mut source,
        &mut succ,
        functional_role,
        TrackPointId::NONE,
        &mut env.ctx,
    );

    let role_linker = [
        NegLink {
            target: functional_role,
            negated: false,
        },
        NegLink {
            target: extra_role,
            negated: false,
        },
        NegLink {
            target: inverse_role,
            negated: true,
        },
    ];
    let concept_linker = [
        NegLink {
            target: env.concept_a,
            negated: false,
        },
        NegLink {
            target: concept_b,
            negated: true,
        },
    ];

    let reused = env.algo.try_extend_functional_successor_individual(
        &mut source,
        ConDescId::NONE,
        &role_linker,
        functional_role,
        &concept_linker,
        false,
        TrackPointId::NONE,
        SatNodeId::NONE,
        &mut env.ctx,
    );

    assert_eq!(reused, succ);
    let mut succ_for_link = succ;
    assert!(env.algo.has_individuals_link(
        &mut source,
        &mut succ_for_link,
        functional_role,
        true,
        &mut env.ctx
    ));
    succ_for_link = succ;
    assert!(env.algo.has_individuals_link(
        &mut source,
        &mut succ_for_link,
        extra_role,
        true,
        &mut env.ctx
    ));
    let mut inverse_source = succ;
    let mut inverse_target = source;
    assert!(env.algo.has_individuals_link(
        &mut inverse_source,
        &mut inverse_target,
        inverse_role,
        true,
        &mut env.ctx
    ));
    assert!(env.algo.has_role_successor_concepts(
        &mut source,
        extra_role,
        &concept_linker,
        false,
        &mut env.ctx
    ));
    assert!(env
        .ctx
        .process_context()
        .node(succ)
        .has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_SATURATIONBLOCKINGCACHEDRETESTDUETOMODIFICATION
        ));
}

#[test]
fn prune_successors_recurses_and_removes_nominal_links() {
    use super::super::model::role::Role;

    let mut env = build_env();
    let mut root = env.root;
    let mut child = env
        .algo
        .create_new_individual(TrackPointId::NONE, false, &mut env.ctx);
    let mut grandchild = env
        .algo
        .create_new_individual(TrackPointId::NONE, false, &mut env.ctx);
    let mut nominal = env
        .algo
        .create_new_individual(TrackPointId::NONE, false, &mut env.ctx);

    env.ctx
        .process_context_mut()
        .node_mut(root)
        .set_individual_ancestor_depth(0);
    env.ctx
        .process_context_mut()
        .node_mut(child)
        .set_individual_ancestor_depth(1);
    env.ctx
        .process_context_mut()
        .node_mut(grandchild)
        .set_individual_ancestor_depth(2);
    env.ctx
        .process_context_mut()
        .node_mut(nominal)
        .set_individual_type(IndividualType::Nominal);

    let role_r = {
        let mut r = Role::new();
        r.set_role_tag(93);
        env.ctx.ontology_arenas_mut().alloc_role(r)
    };
    let nominal_role = {
        let mut r = Role::new();
        r.set_role_tag(94);
        env.ctx.ontology_arenas_mut().alloc_role(r)
    };

    let mut creator = root;
    env.algo.create_new_individuals_link(
        &mut creator,
        &mut root,
        &mut child,
        role_r,
        TrackPointId::NONE,
        &mut env.ctx,
    );
    creator = child;
    env.algo.create_new_individuals_link(
        &mut creator,
        &mut child,
        &mut grandchild,
        role_r,
        TrackPointId::NONE,
        &mut env.ctx,
    );
    creator = nominal;
    env.algo.create_new_individuals_link(
        &mut creator,
        &mut nominal,
        &mut child,
        nominal_role,
        TrackPointId::NONE,
        &mut env.ctx,
    );

    assert!(env.algo.has_individuals_link(
        &mut nominal,
        &mut child,
        nominal_role,
        true,
        &mut env.ctx
    ));

    env.algo
        .prune_successors(&mut root, NodeId::NONE, false, &mut env.ctx);

    assert!(env
        .ctx
        .process_context()
        .node(root)
        .has_purged_blocked_processing_restriction_flags());
    assert!(env
        .ctx
        .process_context()
        .node(child)
        .has_purged_blocked_processing_restriction_flags());
    assert!(env
        .ctx
        .process_context()
        .node(grandchild)
        .has_purged_blocked_processing_restriction_flags());
    assert!(!env.algo.has_individuals_link(
        &mut nominal,
        &mut child,
        nominal_role,
        true,
        &mut env.ctx
    ));
}

#[test]
fn add_individual_node_candidate_for_concept_populates_blocking_candidate_hash() {
    use super::super::model::op;
    use super::super::model::substrate::NegLink;
    use super::super::process::blocking_hash::BlockingIndividualNodeCandidateHash;

    let mut env = build_env();
    let mut root = env.root;
    let mut other = env
        .algo
        .create_new_individual(TrackPointId::NONE, false, &mut env.ctx);

    let atom_b = {
        let mut c = Concept::new();
        c.set_concept_tag(195);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let atom_c = {
        let mut c = Concept::new();
        c.set_concept_tag(196);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let and_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(197);
        c.set_operator_code(op::CCAND);
        c.add_operand_linker(atom_b, false);
        c.add_operand_linker(atom_c, false);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let or_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(198);
        c.set_operator_code(op::CCOR);
        c.add_operand_linker(atom_b, false);
        c.add_operand_linker(atom_c, false);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };

    let con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(con_des);
        d.concept = env.concept_a;
        d.negated = false;
    }

    env.algo
        .add_individual_node_candidate_for_concept_descriptor(&mut root, con_des, &mut env.ctx);
    let linker = [
        NegLink {
            target: and_concept,
            negated: false,
        },
        NegLink {
            target: or_concept,
            negated: true,
        },
    ];
    env.algo
        .add_individual_node_candidate_for_concept(&mut other, &linker, false, &mut env.ctx);

    let hash = env.ctx.blocking_individual_node_candidate_hash(false);
    assert!(hash.is_some());

    let root_id = env.ctx.process_context().node(root).individual_node_id();
    let other_id = env.ctx.process_context().node(other).individual_node_id();

    let descriptor_data =
        BlockingIndividualNodeCandidateHash::get_blocking_individual_candidate_data_for_concept_descriptor(
            env.ctx.process_context_mut(),
            hash,
            con_des,
            false,
        );
    assert!(env
        .ctx
        .process_context()
        .blocking_indi_node_cand_data(descriptor_data)
        .get_blocking_candidates_individual_node_iterator(root_id)
        .has_individual_candidate(root_id));

    for (concept, negated) in [
        (and_concept, false),
        (or_concept, true),
        (atom_b, false),
        (atom_c, false),
    ] {
        let data = BlockingIndividualNodeCandidateHash::get_blocking_individual_candidate_data(
            env.ctx.process_context_mut(),
            hash,
            concept,
            negated,
            false,
        );
        assert!(data.is_some(), "missing candidate data for {:?}", concept);
        assert!(env
            .ctx
            .process_context()
            .blocking_indi_node_cand_data(data)
            .get_blocking_candidates_individual_node_iterator(other_id)
            .has_individual_candidate(other_id));
    }
}

#[test]
fn debug_associated_concepts_strings_match_konclude_tag_formatting() {
    let mut env = build_env();
    let mut root = env.root;
    let mut ancestor = env
        .algo
        .create_new_individual(TrackPointId::NONE, false, &mut env.ctx);
    env.ctx
        .process_context_mut()
        .node_mut(root)
        .set_individual_node_id(31);
    env.ctx
        .process_context_mut()
        .node_mut(ancestor)
        .set_individual_node_id(17);

    let concept_7 = {
        let mut c = Concept::new();
        c.set_concept_tag(7);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let concept_3 = {
        let mut c = Concept::new();
        c.set_concept_tag(3);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let concept_11 = {
        let mut c = Concept::new();
        c.set_concept_tag(11);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let duplicate_7 = {
        let mut c = Concept::new();
        c.set_concept_tag(7);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };

    assert_eq!(
        env.algo
            .generate_debug_individual_node_associated_concepts_string(
                31,
                &[concept_7, concept_3, duplicate_7, concept_11],
                &mut env.ctx,
            ),
        "31 : {3, 7, 11}"
    );

    assert_eq!(
        env.algo
            .generate_debug_individual_node_associated_concepts_set_string(
                &mut root,
                &[vec![concept_11, concept_3], vec![concept_7]],
                &mut env.ctx,
            ),
        "31 : {3, 11}<br>\n31 : {7}"
    );

    assert_eq!(
        env.algo
            .generate_debug_individual_nodes_list_associated_concepts_set_string(
                &mut root,
                &mut ancestor,
                &[101, 102],
                &[
                    vec![
                        vec![concept_7, concept_3],
                        vec![concept_11],
                        vec![concept_3],
                        vec![concept_7, concept_11],
                    ],
                    vec![vec![concept_11], vec![concept_3]],
                ],
                "testing",
                &mut env.ctx,
            ),
        concat!(
            "testing node 31 : {3, 7}  |||  ",
            "testing predecessor 17 : {11}  |||  ",
            "nominal node 101 : {3}  |||  ",
            "nominal node 102 : {7, 11}",
            "<br>\n",
            "testing node 31 : {11}  |||  ",
            "testing predecessor 17 : {3}"
        )
    );
}

#[test]
fn apply_self_rule_positive_creates_missing_self_edge() {
    use super::super::model::op;
    use super::super::model::role::Role;
    use super::super::model::substrate::NegLink;

    let mut env = build_env();
    let mut root = env.root;

    let role_r = {
        let mut r = Role::new();
        r.set_role_tag(76);
        env.ctx.ontology_arenas_mut().alloc_role(r)
    };
    env.ctx
        .ontology_arenas_mut()
        .role_mut(role_r)
        .add_indirect_super_role_linker(NegLink {
            target: role_r,
            negated: false,
        });
    let self_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(176);
        c.set_operator_code(op::CCSELF);
        c.set_role(role_r);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    env.ctx.process_context_mut().con_desc_mut(con_des).concept = self_concept;
    let mut cpd_val = ConceptProcessDescriptor::new();
    cpd_val.concept_des = con_des;
    cpd_val.dep_track_point = TrackPointId::NONE;
    let mut con_proc_des = env.ctx.process_context_mut().alloc_con_proc_desc(cpd_val);

    env.algo
        .apply_self_rule(&mut root, &mut con_proc_des, false, &mut env.ctx);

    let mut self_destination = root;
    let edge =
        env.algo
            .get_individual_node_link(&mut root, &mut self_destination, role_r, &mut env.ctx);
    assert!(edge.is_some(), "positive SELF must install a self edge");
    assert_eq!(
        env.ctx.process_context().edge(edge).get_source_individual(),
        root
    );
    assert_eq!(
        env.ctx
            .process_context()
            .edge(edge)
            .get_destination_individual(),
        root
    );
}

#[test]
fn apply_self_rule_negative_clashes_on_existing_self_edge() {
    use super::super::model::op;
    use super::super::model::role::Role;
    use super::super::model::substrate::NegLink;

    let mut env = build_env();
    let mut root = env.root;

    let role_r = {
        let mut r = Role::new();
        r.set_role_tag(77);
        env.ctx.ontology_arenas_mut().alloc_role(r)
    };
    let role_linker = [NegLink {
        target: role_r,
        negated: false,
    }];
    env.algo.create_new_individuals_links_reapplyed(
        root,
        root,
        &role_linker,
        role_r,
        TrackPointId::NONE,
        true,
        &mut env.ctx,
    );

    let self_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(177);
        c.set_operator_code(op::CCSELF);
        c.set_role(role_r);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    env.ctx.process_context_mut().con_desc_mut(con_des).concept = self_concept;
    let mut cpd_val = ConceptProcessDescriptor::new();
    cpd_val.concept_des = con_des;
    cpd_val.dep_track_point = TrackPointId::NONE;
    let mut con_proc_des = env.ctx.process_context_mut().alloc_con_proc_desc(cpd_val);

    env.algo
        .apply_self_rule(&mut root, &mut con_proc_des, true, &mut env.ctx);

    match env.ctx.pending_signal() {
        CalcSignal::Clash(_) => {}
        other => panic!("negative SELF over an existing self edge must clash, got {other:?}"),
    }
}

#[test]
fn apply_self_rule_negative_without_edge_adds_role_reapply_descriptor() {
    use super::super::model::op;
    use super::super::model::role::Role;

    let mut env = build_env();
    let mut root = env.root;

    let role_r = {
        let mut r = Role::new();
        r.set_role_tag(78);
        env.ctx.ontology_arenas_mut().alloc_role(r)
    };
    let self_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(178);
        c.set_operator_code(op::CCSELF);
        c.set_role(role_r);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    env.ctx.process_context_mut().con_desc_mut(con_des).concept = self_concept;
    let mut cpd_val = ConceptProcessDescriptor::new();
    cpd_val.concept_des = con_des;
    cpd_val.dep_track_point = TrackPointId::NONE;
    let mut con_proc_des = env.ctx.process_context_mut().alloc_con_proc_desc(cpd_val);

    env.algo
        .apply_self_rule(&mut root, &mut con_proc_des, true, &mut env.ctx);

    assert_eq!(env.ctx.pending_signal(), CalcSignal::Continue);
    assert!(
        env.algo
            .is_concept_in_reapply_queue_role(con_des, role_r, root, &mut env.ctx),
        "negative SELF without a current self edge must be queued for role reapply"
    );
}

/// Concept-keyed condensed reapply queues: add a descriptor under a concept trigger,
/// then reapply that concept and verify the descriptor is materialised into the
/// node's concept-processing queue. This covers Konclude's
/// `addConceptToReapplyQueue(concept,negation,...)` +
/// `applyReapplyQueueConcepts(concept,negation)` path.
#[test]
fn concept_reapply_queue_applies_to_concept_processing_queue() {
    use super::super::model::op;

    let mut env = build_env();
    let root = env.root;

    let trigger_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(171);
        c.set_operator_code(op::CCATOM);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let queued_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(172);
        c.set_operator_code(op::CCAND);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(con_des);
        d.concept = queued_concept;
        d.dep_track_point = TrackPointId::NONE;
    }

    env.algo.add_concept_to_reapply_queue_concept(
        con_des,
        trigger_concept,
        false,
        root,
        false,
        TrackPointId::NONE,
        &mut env.ctx,
    );
    assert!(
        env.algo.is_concept_in_reapply_queue_concept(
            con_des,
            trigger_concept,
            false,
            root,
            &mut env.ctx
        ),
        "the descriptor must be present in the concept-keyed condensed reapply queue"
    );

    env.algo
        .apply_reapply_queue_concepts_concept(root, trigger_concept, false, &mut env.ctx);
    assert!(
        !env.algo.is_concept_in_reapply_queue_concept(
            con_des,
            trigger_concept,
            false,
            root,
            &mut env.ctx
        ),
        "applying with clearDynamicReapplyQueue=true must clear the dynamic queue"
    );

    let queue = env
        .ctx
        .process_context_mut()
        .node_concept_processing_queue(root, false);
    assert!(
        queue.is_some(),
        "reapply must allocate/use the concept queue"
    );
    assert_eq!(
        env.ctx
            .process_context()
            .concept_proc_queue(queue)
            .get_descriptor_count(),
        1,
        "one reapplied descriptor must be queued for processing"
    );
    let taken = ConceptProcessingQueue::take_next_concept_descriptor_process(
        queue,
        env.ctx.process_context_mut(),
    );
    assert_eq!(
        env.ctx
            .process_context()
            .con_proc_desc(taken)
            .get_concept_descriptor(),
        con_des,
        "the queued process descriptor must wrap the concept-keyed reapplied descriptor"
    );
}

/// Installing a fresh role edge must fill the role reapply iterator from the
/// source node's `CReapplyRoleSuccessorHash`, so restricted edge-triggered
/// reapplication can queue the role-triggered descriptor for processing.
#[test]
fn role_link_install_returns_reapply_iterator() {
    use super::super::model::op;
    use super::super::model::role::Role;

    let mut env = build_env();
    let root = env.root;

    let role_r = {
        let mut r = Role::new();
        r.set_role_tag(71);
        env.ctx.ontology_arenas_mut().alloc_role(r)
    };
    let triggered_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(173);
        c.set_operator_code(op::CCAND);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(con_des);
        d.concept = triggered_concept;
        d.dep_track_point = TrackPointId::NONE;
    }
    env.algo.add_concept_to_reapply_queue_role(
        con_des,
        role_r,
        root,
        true,
        TrackPointId::NONE,
        &mut env.ctx,
    );

    let mut succ = env
        .algo
        .create_new_individual(TrackPointId::NONE, false, &mut env.ctx);
    let mut edge = super::super::process::edge::IndividualLinkEdge::new();
    edge.creator = root;
    edge.set_source_individual(root);
    edge.set_destination_individual(succ);
    edge.set_link_role(role_r);
    edge.set_dependency_track_point(TrackPointId::NONE);
    let edge = env.ctx.process_context_mut().alloc_edge(edge);

    let mut src = root;
    let mut reapply_it = env.algo.install_individual_node_role_link_reapplied(
        &mut src,
        &mut succ,
        edge,
        &mut env.ctx,
    );
    assert!(
        reapply_it.has_next(),
        "installing the role edge must expose queued role reapply descriptors"
    );

    let first = reapply_it.next(env.ctx.process_context(), false);
    assert_eq!(
        env.ctx
            .process_context()
            .reapply_con_desc(first)
            .get_concept_descriptor(),
        con_des,
        "the iterator must expose the descriptor registered under the edge role"
    );

    env.algo
        .apply_reapply_queue_concepts_role(root, role_r, &mut env.ctx);
    let queue = env
        .ctx
        .process_context_mut()
        .node_concept_processing_queue(root, false);
    assert_eq!(
        env.ctx
            .process_context()
            .concept_proc_queue(queue)
            .get_descriptor_count(),
        1,
        "the installed edge's role reapply queue must feed concept processing"
    );
}

#[test]
fn restricted_reapply_queue_attaches_link_restriction() {
    use super::super::model::op;
    use super::super::model::role::Role;

    let mut env = build_env();
    let root = env.root;

    let role_r = {
        let mut r = Role::new();
        r.set_role_tag(72);
        env.ctx.ontology_arenas_mut().alloc_role(r)
    };
    let triggered_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(174);
        c.set_operator_code(op::CCAND);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(con_des);
        d.concept = triggered_concept;
        d.dep_track_point = TrackPointId::NONE;
    }
    env.algo.add_concept_to_reapply_queue_role(
        con_des,
        role_r,
        root,
        true,
        TrackPointId::NONE,
        &mut env.ctx,
    );

    let mut succ = env
        .algo
        .create_new_individual(TrackPointId::NONE, false, &mut env.ctx);
    let mut edge = super::super::process::edge::IndividualLinkEdge::new();
    edge.creator = root;
    edge.set_source_individual(root);
    edge.set_destination_individual(succ);
    edge.set_link_role(role_r);
    edge.set_dependency_track_point(TrackPointId::NONE);
    let edge = env.ctx.process_context_mut().alloc_edge(edge);

    let mut src = root;
    let reapply_it = env.algo.install_individual_node_role_link_reapplied(
        &mut src,
        &mut succ,
        edge,
        &mut env.ctx,
    );
    env.algo
        .apply_reapply_queue_concepts_restricted(root, reapply_it, edge, &mut env.ctx);

    let queue = env
        .ctx
        .process_context_mut()
        .node_concept_processing_queue(root, false);
    assert_eq!(
        env.ctx
            .process_context()
            .concept_proc_queue(queue)
            .get_descriptor_count(),
        1,
        "restricted reapply must queue one concept-processing descriptor"
    );
    let queued = ConceptProcessingQueue::take_next_concept_descriptor_process(
        queue,
        env.ctx.process_context_mut(),
    );
    let proc_spec = env
        .ctx
        .process_context()
        .con_proc_desc(queued)
        .get_processing_restriction_specification();
    assert!(
        proc_spec.is_some(),
        "restricted reapply must attach a link processing restriction"
    );
    assert_eq!(
        env.ctx
            .process_context()
            .restriction_spec(proc_spec)
            .get_link_restriction(),
        edge,
        "the generated restriction must carry the edge that triggered reapply"
    );
}

#[test]
fn condensed_iterator_reapply_queues_matching_descriptors() {
    use super::super::model::op;
    use super::super::process::reapply_sat::{
        CondensedReapplyConceptDescriptor, CondensedReapplyQueueIterator,
    };

    let mut env = build_env();
    let root = env.root;

    let triggered_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(175);
        c.set_operator_code(op::CCAND);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let matching_con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(matching_con_des);
        d.concept = triggered_concept;
        d.dep_track_point = TrackPointId::NONE;
    }
    let filtered_con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(filtered_con_des);
        d.concept = triggered_concept;
        d.negated = true;
        d.dep_track_point = TrackPointId::NONE;
    }

    let filtered = env.ctx.process_context_mut().alloc_cond_reapply_con_desc(
        CondensedReapplyConceptDescriptor::new(filtered_con_des, TrackPointId::NONE, false),
    );
    let matching = env.ctx.process_context_mut().alloc_cond_reapply_con_desc(
        CondensedReapplyConceptDescriptor::new(matching_con_des, TrackPointId::NONE, true),
    );
    env.ctx
        .process_context_mut()
        .cond_reapply_con_desc_mut(matching)
        .next = filtered;

    let reapply_it =
        CondensedReapplyQueueIterator::new_only_positive(env.ctx.process_context(), matching, true);
    env.algo
        .apply_reapply_queue_concepts_condensed_iterator(root, reapply_it, &mut env.ctx);

    let queue = env
        .ctx
        .process_context_mut()
        .node_concept_processing_queue(root, false);
    assert_eq!(
        env.ctx
            .process_context()
            .concept_proc_queue(queue)
            .get_descriptor_count(),
        1,
        "condensed iterator apply must queue only descriptors admitted by polarity"
    );
    let queued = ConceptProcessingQueue::take_next_concept_descriptor_process(
        queue,
        env.ctx.process_context_mut(),
    );
    assert_eq!(
        env.ctx
            .process_context()
            .con_proc_desc(queued)
            .get_concept_descriptor(),
        matching_con_des,
        "the queued concept-process descriptor must wrap the matching condensed descriptor"
    );
}

#[test]
fn add_concept_to_individual_drains_condensed_reapply_iterator() {
    use super::super::model::op;

    let mut env = build_env();
    let mut root = env.root;

    let trigger_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(176);
        c.set_operator_code(op::CCATOM);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let reapplied_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(177);
        c.set_operator_code(op::CCAND);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let reapply_con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(reapply_con_des);
        d.concept = reapplied_concept;
        d.dep_track_point = TrackPointId::NONE;
    }

    env.algo.add_concept_to_reapply_queue_concept(
        reapply_con_des,
        trigger_concept,
        false,
        root,
        false,
        TrackPointId::NONE,
        &mut env.ctx,
    );
    assert!(
        env.algo.is_concept_in_reapply_queue_concept(
            reapply_con_des,
            trigger_concept,
            false,
            root,
            &mut env.ctx,
        ),
        "setup must seed the concept-keyed condensed reapply queue"
    );

    env.algo.add_concept_to_individual(
        trigger_concept,
        false,
        &mut root,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );

    assert!(
        !env.algo.is_concept_in_reapply_queue_concept(
            reapply_con_des,
            trigger_concept,
            false,
            root,
            &mut env.ctx,
        ),
        "Unit 36 insertion must clear the drained dynamic condensed queue"
    );
    let queue = env
        .ctx
        .process_context_mut()
        .node_concept_processing_queue(root, false);
    assert_eq!(
        env.ctx
            .process_context()
            .concept_proc_queue(queue)
            .get_descriptor_count(),
        1,
        "insertion must queue the drained reapply descriptor"
    );
    let queued = ConceptProcessingQueue::take_next_concept_descriptor_process(
        queue,
        env.ctx.process_context_mut(),
    );
    assert_eq!(
        env.ctx
            .process_context()
            .con_proc_desc(queued)
            .get_concept_descriptor(),
        reapply_con_des,
        "the condensed reapply descriptor must reach the concept-processing queue"
    );
}

#[test]
fn add_concept_to_individual_return_descriptor_drains_condensed_reapply_iterator() {
    use super::super::model::op;

    let mut env = build_env();
    let mut root = env.root;

    let trigger_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(178);
        c.set_operator_code(op::CCATOM);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let reapplied_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(179);
        c.set_operator_code(op::CCAND);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let reapply_con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(reapply_con_des);
        d.concept = reapplied_concept;
        d.dep_track_point = TrackPointId::NONE;
    }

    env.algo.add_concept_to_reapply_queue_concept(
        reapply_con_des,
        trigger_concept,
        false,
        root,
        false,
        TrackPointId::NONE,
        &mut env.ctx,
    );

    let inserted = env
        .algo
        .add_concept_to_individual_return_concept_descriptor(
            trigger_concept,
            false,
            &mut root,
            TrackPointId::NONE,
            false,
            true,
            &mut env.ctx,
        );

    assert!(
        inserted.is_some(),
        "return-descriptor overload must still return the inserted descriptor"
    );
    assert!(
        !env.algo.is_concept_in_reapply_queue_concept(
            reapply_con_des,
            trigger_concept,
            false,
            root,
            &mut env.ctx,
        ),
        "return-descriptor overload must clear the drained dynamic condensed queue"
    );
    let queue = env
        .ctx
        .process_context_mut()
        .node_concept_processing_queue(root, false);
    assert_eq!(
        env.ctx
            .process_context()
            .concept_proc_queue(queue)
            .get_descriptor_count(),
        1,
        "return-descriptor overload must queue the drained reapply descriptor"
    );
    let queued = ConceptProcessingQueue::take_next_concept_descriptor_process(
        queue,
        env.ctx.process_context_mut(),
    );
    assert_eq!(
        env.ctx
            .process_context()
            .con_proc_desc(queued)
            .get_concept_descriptor(),
        reapply_con_des,
        "the condensed reapply descriptor must reach the concept-processing queue"
    );
}

#[test]
fn add_concepts_to_individual_drains_condensed_reapply_iterator() {
    use super::super::model::op;

    let mut env = build_env();
    let mut root = env.root;

    let trigger_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(180);
        c.set_operator_code(op::CCATOM);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let reapplied_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(181);
        c.set_operator_code(op::CCAND);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let reapply_con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(reapply_con_des);
        d.concept = reapplied_concept;
        d.dep_track_point = TrackPointId::NONE;
    }

    env.algo.add_concept_to_reapply_queue_concept(
        reapply_con_des,
        trigger_concept,
        false,
        root,
        false,
        TrackPointId::NONE,
        &mut env.ctx,
    );

    let mut concept_count = 0;
    env.algo.add_concepts_to_individual(
        &[NegLink {
            target: trigger_concept,
            negated: false,
        }],
        false,
        &mut root,
        TrackPointId::NONE,
        false,
        true,
        Some(&mut concept_count),
        &mut env.ctx,
    );

    assert_eq!(concept_count, 1);
    assert!(
        !env.algo.is_concept_in_reapply_queue_concept(
            reapply_con_des,
            trigger_concept,
            false,
            root,
            &mut env.ctx,
        ),
        "bulk overload must clear the drained dynamic condensed queue"
    );
    let queue = env
        .ctx
        .process_context_mut()
        .node_concept_processing_queue(root, false);
    assert_eq!(
        env.ctx
            .process_context()
            .concept_proc_queue(queue)
            .get_descriptor_count(),
        1,
        "bulk overload must queue the drained reapply descriptor"
    );
    let queued = ConceptProcessingQueue::take_next_concept_descriptor_process(
        queue,
        env.ctx.process_context_mut(),
    );
    assert_eq!(
        env.ctx
            .process_context()
            .con_proc_desc(queued)
            .get_concept_descriptor(),
        reapply_con_des
    );
}

#[test]
fn propagation_binding_reapply_linker_queues_concepts() {
    use super::super::model::op;
    use super::super::process::propagation_binding::PropagationBindingReapplyConceptDescriptor;

    let mut env = build_env();
    let root = env.root;

    let triggered_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(176);
        c.set_operator_code(op::CCAND);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let first_con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(first_con_des);
        d.concept = triggered_concept;
        d.dep_track_point = TrackPointId::NONE;
    }
    let second_con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(second_con_des);
        d.concept = triggered_concept;
        d.dep_track_point = TrackPointId::NONE;
    }

    let first = {
        let mut d = PropagationBindingReapplyConceptDescriptor::new();
        d.init_reapply_descriptor(root, Id::NONE, first_con_des, TrackPointId::NONE);
        env.ctx
            .process_context_mut()
            .alloc_prop_binding_reapply_con_des(d)
    };
    let second = {
        let mut d = PropagationBindingReapplyConceptDescriptor::new();
        d.init_reapply_descriptor(root, Id::NONE, second_con_des, TrackPointId::NONE);
        env.ctx
            .process_context_mut()
            .alloc_prop_binding_reapply_con_des(d)
    };
    env.ctx
        .process_context_mut()
        .prop_binding_reapply_con_des_mut(first)
        .set_next(second);

    env.algo
        .apply_reapply_queue_concepts_propagation_binding(root, first, &mut env.ctx);

    let queue = env
        .ctx
        .process_context_mut()
        .node_concept_processing_queue(root, false);
    assert_eq!(
        env.ctx
            .process_context()
            .concept_proc_queue(queue)
            .get_descriptor_count(),
        2,
        "propagation-binding reapply must queue every descriptor in the linker"
    );
    let first_queued = ConceptProcessingQueue::take_next_concept_descriptor_process(
        queue,
        env.ctx.process_context_mut(),
    );
    let second_queued = ConceptProcessingQueue::take_next_concept_descriptor_process(
        queue,
        env.ctx.process_context_mut(),
    );
    let mut queued = vec![
        env.ctx
            .process_context()
            .con_proc_desc(first_queued)
            .get_concept_descriptor(),
        env.ctx
            .process_context()
            .con_proc_desc(second_queued)
            .get_concept_descriptor(),
    ];
    queued.sort_by_key(|id| id.raw);
    let mut expected = vec![first_con_des, second_con_des];
    expected.sort_by_key(|id| id.raw);
    assert_eq!(queued, expected);
}

#[test]
fn propagation_binding_fresh_producer_applies_existing_reapply_linker() {
    use super::super::model::op;
    use super::super::process::propagation_binding::{
        PropagationBinding, PropagationBindingDescriptor, PropagationBindingMapData,
        PropagationBindingReapplyConceptDescriptor, PropagationBindingSet,
    };

    let mut env = build_env();
    let root = env.root;

    let triggered_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(177);
        c.set_operator_code(op::CCAND);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let binding_con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(binding_con_des);
        d.concept = triggered_concept;
        d.dep_track_point = TrackPointId::NONE;
    }
    let reapply_con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(reapply_con_des);
        d.concept = triggered_concept;
        d.dep_track_point = TrackPointId::NONE;
    }

    let prop_binding = {
        let mut b = PropagationBinding::new();
        b.init_propagation_binding(901, TrackPointId::NONE, root, binding_con_des, Id::NONE);
        env.ctx.process_context_mut().alloc_prop_binding(b)
    };
    let prev_des = {
        let mut d = PropagationBindingDescriptor::new();
        d.init_propagation_binding_descriptor(prop_binding, TrackPointId::NONE);
        let id = env.ctx.process_context_mut().alloc_prop_binding_des(d);
        env.ctx
            .process_context_mut()
            .prop_binding_des_mut(id)
            .set_data(id);
        id
    };
    let reapply_des = {
        let mut d = PropagationBindingReapplyConceptDescriptor::new();
        d.init_reapply_descriptor(root, prop_binding, reapply_con_des, TrackPointId::NONE);
        env.ctx
            .process_context_mut()
            .alloc_prop_binding_reapply_con_des(d)
    };

    let prev_set = env
        .ctx
        .process_context_mut()
        .alloc_prop_binding_set(PropagationBindingSet::new(INVALID));
    {
        let data = env
            .ctx
            .process_context_mut()
            .prop_binding_set_mut(prev_set)
            .prop_map
            .entry_mut(901);
        data.set_propagation_binding_descriptor(prev_des);
    }
    let new_set = env
        .ctx
        .process_context_mut()
        .alloc_prop_binding_set(PropagationBindingSet::new(INVALID));
    {
        env.ctx
            .process_context_mut()
            .prop_binding_set_mut(new_set)
            .prop_map
            .map
            .insert(901, PropagationBindingMapData::new(Id::NONE));
        env.ctx
            .process_context_mut()
            .prop_binding_set_mut(new_set)
            .prop_map
            .entry_mut(901)
            .set_reapply_concept_descriptor(reapply_des);
    }

    let mut root_ref = root;
    assert!(
        env.algo.propagate_fresh_propagation_bindings(
            &mut root_ref,
            binding_con_des,
            new_set,
            prev_set,
            DepLinkId::NONE,
            &mut env.ctx,
        ),
        "fresh propagation-binding production must report propagated bindings"
    );

    let new_descriptor = env
        .ctx
        .process_context()
        .prop_binding_set(new_set)
        .prop_map
        .value(901)
        .get_propagation_binding_descriptor();
    assert!(
        new_descriptor.is_some(),
        "producer must install a new propagation-binding descriptor in the new set"
    );
    assert_ne!(
        new_descriptor, prev_des,
        "producer must allocate a fresh descriptor rather than reusing the previous set descriptor"
    );

    let queue = env
        .ctx
        .process_context_mut()
        .node_concept_processing_queue(root, false);
    assert_eq!(
        env.ctx
            .process_context()
            .concept_proc_queue(queue)
            .get_descriptor_count(),
        1,
        "producer must apply the existing propagation-binding reapply linker"
    );
    let queued = ConceptProcessingQueue::take_next_concept_descriptor_process(
        queue,
        env.ctx.process_context_mut(),
    );
    assert_eq!(
        env.ctx
            .process_context()
            .con_proc_desc(queued)
            .get_concept_descriptor(),
        reapply_con_des
    );
}

#[test]
fn propagation_binding_initial_producer_copies_prev_map_with_fresh_descriptors() {
    use super::super::model::op;
    use super::super::process::propagation_binding::{
        PropagationBinding, PropagationBindingDescriptor,
        PropagationBindingReapplyConceptDescriptor, PropagationBindingSet,
    };

    let mut env = build_env();
    let root = env.root;

    let triggered_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(181);
        c.set_operator_code(op::CCAND);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let binding_con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(binding_con_des);
        d.concept = triggered_concept;
        d.dep_track_point = TrackPointId::NONE;
    }
    let reapply_con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(reapply_con_des);
        d.concept = triggered_concept;
        d.dep_track_point = TrackPointId::NONE;
    }

    let first_binding = {
        let mut b = PropagationBinding::new();
        b.init_propagation_binding(911, TrackPointId::NONE, root, binding_con_des, Id::NONE);
        env.ctx.process_context_mut().alloc_prop_binding(b)
    };
    let first_prev_des = {
        let mut d = PropagationBindingDescriptor::new();
        d.init_propagation_binding_descriptor(first_binding, TrackPointId::NONE);
        let id = env.ctx.process_context_mut().alloc_prop_binding_des(d);
        env.ctx
            .process_context_mut()
            .prop_binding_des_mut(id)
            .set_data(id);
        id
    };
    let second_binding = {
        let mut b = PropagationBinding::new();
        b.init_propagation_binding(912, TrackPointId::NONE, root, binding_con_des, Id::NONE);
        env.ctx.process_context_mut().alloc_prop_binding(b)
    };
    let second_prev_des = {
        let mut d = PropagationBindingDescriptor::new();
        d.init_propagation_binding_descriptor(second_binding, TrackPointId::NONE);
        let id = env.ctx.process_context_mut().alloc_prop_binding_des(d);
        env.ctx
            .process_context_mut()
            .prop_binding_des_mut(id)
            .set_data(id);
        id
    };
    let prev_reapply_des = {
        let mut d = PropagationBindingReapplyConceptDescriptor::new();
        d.init_reapply_descriptor(root, first_binding, reapply_con_des, TrackPointId::NONE);
        env.ctx
            .process_context_mut()
            .alloc_prop_binding_reapply_con_des(d)
    };

    let prev_set = env
        .ctx
        .process_context_mut()
        .alloc_prop_binding_set(PropagationBindingSet::new(INVALID));
    {
        let prev_set_ref = env.ctx.process_context_mut().prop_binding_set_mut(prev_set);
        prev_set_ref.set_propagate_all_flag(true);
        prev_set_ref
            .prop_map
            .entry_mut(911)
            .set_propagation_binding_descriptor(first_prev_des)
            .set_reapply_concept_descriptor(prev_reapply_des);
        prev_set_ref
            .prop_map
            .entry_mut(912)
            .set_propagation_binding_descriptor(second_prev_des);
    }
    let new_set = env
        .ctx
        .process_context_mut()
        .alloc_prop_binding_set(PropagationBindingSet::new(INVALID));

    let mut root_ref = root;
    assert!(
        env.algo.propagate_initial_propagation_bindings(
            &mut root_ref,
            binding_con_des,
            new_set,
            prev_set,
            DepLinkId::NONE,
            &mut env.ctx,
        ),
        "initial propagation-binding production must report copied bindings"
    );

    let new_set_ref = env.ctx.process_context().prop_binding_set(new_set);
    assert!(
        new_set_ref.get_propagate_all_flag(),
        "initial propagation-binding production must adopt propagate-all"
    );
    let first_new_des = new_set_ref
        .prop_map
        .value(911)
        .get_propagation_binding_descriptor();
    let second_new_des = new_set_ref
        .prop_map
        .value(912)
        .get_propagation_binding_descriptor();
    assert!(first_new_des.is_some());
    assert!(second_new_des.is_some());
    assert_ne!(first_new_des, first_prev_des);
    assert_ne!(second_new_des, second_prev_des);
    assert!(
        new_set_ref
            .prop_map
            .value(911)
            .get_reapply_concept_descriptor()
            .is_none(),
        "copied map-data reapply descriptor must be cleared before descriptor refresh"
    );
    assert!(new_set_ref
        .prop_map
        .value(912)
        .get_reapply_concept_descriptor()
        .is_none());

    let first_new = env.ctx.process_context().prop_binding_des(first_new_des);
    assert_eq!(first_new.get_propagation_binding(), first_binding);
    assert_eq!(
        first_new.get_dependency_track_point(),
        env.ctx
            .process_context()
            .prop_binding_des(first_prev_des)
            .get_dependency_track_point()
    );
    let second_new = env.ctx.process_context().prop_binding_des(second_new_des);
    assert_eq!(second_new.get_propagation_binding(), second_binding);
    assert_eq!(
        second_new.get_dependency_track_point(),
        env.ctx
            .process_context()
            .prop_binding_des(second_prev_des)
            .get_dependency_track_point()
    );

    let mut link = new_set_ref.get_propagation_binding_descriptor_linker();
    let mut linked_bindings = Vec::new();
    while link.is_some() {
        linked_bindings.push(
            env.ctx
                .process_context()
                .prop_binding_des(link)
                .get_propagation_binding(),
        );
        link = env.ctx.process_context().prop_binding_des(link).get_next();
    }
    linked_bindings.sort_by_key(|id| id.raw);
    assert_eq!(linked_bindings, vec![first_binding, second_binding]);
}

#[test]
fn pbind_implication_existing_binding_refreshes_fresh_bindings() {
    use super::super::model::op;
    use super::super::process::binding_hash::ConceptPropagationBindingSetHash;
    use super::super::process::propagation_binding::{
        PropagationBinding, PropagationBindingDescriptor, PropagationBindingMapData,
        PropagationBindingReapplyConceptDescriptor,
    };

    let mut env = build_env();
    let root = env.root;

    let binding_trigger = {
        let mut c = Concept::new();
        c.set_concept_tag(178);
        c.set_operator_code(op::CCPBINDTRIG);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let source_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(179);
        c.set_operator_code(op::CCPBINDIMPL);
        c.set_operand_count(1);
        c.add_operand_linker(binding_trigger, false);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let reapply_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(180);
        c.set_operator_code(op::CCAND);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };

    let mut root_ref = root;
    let binding_con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(binding_con_des);
        d.concept = binding_trigger;
        d.dep_track_point = TrackPointId::NONE;
    }
    let binding_label_set = env
        .ctx
        .process_context_mut()
        .node_reapply_concept_label_set(root);
    let binding_tag = env
        .ctx
        .ontology_arenas()
        .concept(binding_trigger)
        .get_concept_tag();
    let mut lifted_label_set = std::mem::replace(
        env.ctx
            .process_context_mut()
            .label_set_mut(binding_label_set),
        Default::default(),
    );
    {
        let pc = env.ctx.process_context();
        lifted_label_set.insert_concept_get_clash_resolved(
            binding_con_des,
            binding_trigger,
            binding_tag,
            false,
            &|d| pc.con_desc(d).is_negated(),
            None,
            None,
        );
    }
    *env.ctx
        .process_context_mut()
        .label_set_mut(binding_label_set) = lifted_label_set;

    let source_con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(source_con_des);
        d.concept = source_concept;
        d.dep_track_point = TrackPointId::NONE;
    }
    let mut cpd_val = ConceptProcessDescriptor::new();
    cpd_val.concept_des = source_con_des;
    cpd_val.dep_track_point = TrackPointId::NONE;
    let mut con_proc_des = env.ctx.process_context_mut().alloc_con_proc_desc(cpd_val);

    let reapply_con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(reapply_con_des);
        d.concept = reapply_concept;
        d.dep_track_point = TrackPointId::NONE;
    }

    let prop_binding = {
        let mut b = PropagationBinding::new();
        b.init_propagation_binding(902, TrackPointId::NONE, root, binding_con_des, Id::NONE);
        env.ctx.process_context_mut().alloc_prop_binding(b)
    };
    let prev_des = {
        let mut d = PropagationBindingDescriptor::new();
        d.init_propagation_binding_descriptor(prop_binding, TrackPointId::NONE);
        let id = env.ctx.process_context_mut().alloc_prop_binding_des(d);
        env.ctx
            .process_context_mut()
            .prop_binding_des_mut(id)
            .set_data(id);
        id
    };
    let reapply_des = {
        let mut d = PropagationBindingReapplyConceptDescriptor::new();
        d.init_reapply_descriptor(root, prop_binding, reapply_con_des, TrackPointId::NONE);
        env.ctx
            .process_context_mut()
            .alloc_prop_binding_reapply_con_des(d)
    };

    let hash = env
        .ctx
        .process_context_mut()
        .node_concept_propagation_binding_set_hash(root);
    let source_tag = env
        .ctx
        .ontology_arenas()
        .concept(source_concept)
        .get_concept_tag();
    let source_set = ConceptPropagationBindingSetHash::get_propagation_binding_set(
        env.ctx.process_context_mut(),
        hash,
        source_tag,
        true,
    );
    env.ctx
        .process_context_mut()
        .prop_binding_set_mut(source_set)
        .prop_map
        .entry_mut(902)
        .set_propagation_binding_descriptor(prev_des);

    let trigger_set = ConceptPropagationBindingSetHash::get_propagation_binding_set(
        env.ctx.process_context_mut(),
        hash,
        binding_tag,
        true,
    );
    env.ctx
        .process_context_mut()
        .prop_binding_set_mut(trigger_set)
        .prop_map
        .map
        .insert(902, PropagationBindingMapData::new(Id::NONE));
    env.ctx
        .process_context_mut()
        .prop_binding_set_mut(trigger_set)
        .prop_map
        .entry_mut(902)
        .set_reapply_concept_descriptor(reapply_des);

    env.algo.apply_bind_propagate_implication_rule(
        &mut root_ref,
        &mut con_proc_des,
        false,
        &mut env.ctx,
    );

    let installed = env
        .ctx
        .process_context()
        .prop_binding_set(trigger_set)
        .prop_map
        .value(902)
        .get_propagation_binding_descriptor();
    assert!(
        installed.is_some(),
        "PBIND implication existing-binding path must install a fresh propagated descriptor"
    );
    assert_ne!(installed, prev_des);

    let queue = env
        .ctx
        .process_context_mut()
        .node_concept_processing_queue(root, false);
    assert_eq!(
        env.ctx
            .process_context()
            .concept_proc_queue(queue)
            .get_descriptor_count(),
        1,
        "PBIND implication refresh must leave the non-propagation reapply linker in the node queue"
    );
    let batch_queue = env
        .ctx
        .get_variable_binding_concept_batch_processing_queue(false);
    assert!(batch_queue.is_some());
    let batch_entry = env
        .ctx
        .take_next_variable_binding_concept_batch_process_individual(batch_queue);
    assert!(
        matches!(batch_entry, Some((_, node, des)) if node == root && des.is_some()),
        "PBIND implication refresh must route the binding concept through the variable-binding batch queue"
    );
}

#[test]
fn propagation_binding_initial_successor_producer_copies_prev_map_with_fresh_descriptors() {
    use super::super::model::op;
    use super::super::model::role::Role;
    use super::super::process::edge::IndividualLinkEdge;
    use super::super::process::propagation_binding::{
        PropagationBinding, PropagationBindingDescriptor,
        PropagationBindingReapplyConceptDescriptor, PropagationBindingSet,
    };

    let mut env = build_env();
    let root = env.root;
    let succ = env
        .algo
        .create_new_individual(TrackPointId::NONE, false, &mut env.ctx);
    let role_r = env.ctx.ontology_arenas_mut().alloc_role(Role::new());
    let rest_link = {
        let mut edge = IndividualLinkEdge::new();
        edge.creator = root;
        edge.set_source_individual(root);
        edge.set_destination_individual(succ);
        edge.set_link_role(role_r);
        edge.set_dependency_track_point(TrackPointId::NONE);
        env.ctx.process_context_mut().alloc_edge(edge)
    };

    let triggered_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(182);
        c.set_operator_code(op::CCAND);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let binding_con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(binding_con_des);
        d.concept = triggered_concept;
        d.dep_track_point = TrackPointId::NONE;
    }
    let reapply_con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(reapply_con_des);
        d.concept = triggered_concept;
        d.dep_track_point = TrackPointId::NONE;
    }

    let first_binding = {
        let mut b = PropagationBinding::new();
        b.init_propagation_binding(921, TrackPointId::NONE, root, binding_con_des, Id::NONE);
        env.ctx.process_context_mut().alloc_prop_binding(b)
    };
    let first_prev_des = {
        let mut d = PropagationBindingDescriptor::new();
        d.init_propagation_binding_descriptor(first_binding, TrackPointId::NONE);
        let id = env.ctx.process_context_mut().alloc_prop_binding_des(d);
        env.ctx
            .process_context_mut()
            .prop_binding_des_mut(id)
            .set_data(id);
        id
    };
    let second_binding = {
        let mut b = PropagationBinding::new();
        b.init_propagation_binding(922, TrackPointId::NONE, root, binding_con_des, Id::NONE);
        env.ctx.process_context_mut().alloc_prop_binding(b)
    };
    let second_prev_des = {
        let mut d = PropagationBindingDescriptor::new();
        d.init_propagation_binding_descriptor(second_binding, TrackPointId::NONE);
        let id = env.ctx.process_context_mut().alloc_prop_binding_des(d);
        env.ctx
            .process_context_mut()
            .prop_binding_des_mut(id)
            .set_data(id);
        id
    };
    let prev_reapply_des = {
        let mut d = PropagationBindingReapplyConceptDescriptor::new();
        d.init_reapply_descriptor(root, first_binding, reapply_con_des, TrackPointId::NONE);
        env.ctx
            .process_context_mut()
            .alloc_prop_binding_reapply_con_des(d)
    };

    let prev_set = env
        .ctx
        .process_context_mut()
        .alloc_prop_binding_set(PropagationBindingSet::new(INVALID));
    {
        let prev_set_ref = env.ctx.process_context_mut().prop_binding_set_mut(prev_set);
        prev_set_ref.set_propagate_all_flag(true);
        prev_set_ref
            .prop_map
            .entry_mut(921)
            .set_propagation_binding_descriptor(first_prev_des)
            .set_reapply_concept_descriptor(prev_reapply_des);
        prev_set_ref
            .prop_map
            .entry_mut(922)
            .set_propagation_binding_descriptor(second_prev_des);
    }
    let new_set = env
        .ctx
        .process_context_mut()
        .alloc_prop_binding_set(PropagationBindingSet::new(INVALID));

    let mut root_ref = root;
    assert!(
        env.algo
            .propagate_initial_propagation_bindings_to_successor(
                &mut root_ref,
                succ,
                binding_con_des,
                new_set,
                prev_set,
                rest_link,
                &mut env.ctx,
            ),
        "successor initial producer must report copied bindings"
    );

    let new_set_ref = env.ctx.process_context().prop_binding_set(new_set);
    assert!(new_set_ref.get_propagate_all_flag());
    let first_new_des = new_set_ref
        .prop_map
        .value(921)
        .get_propagation_binding_descriptor();
    let second_new_des = new_set_ref
        .prop_map
        .value(922)
        .get_propagation_binding_descriptor();
    assert!(first_new_des.is_some());
    assert!(second_new_des.is_some());
    assert_ne!(first_new_des, first_prev_des);
    assert_ne!(second_new_des, second_prev_des);
    assert!(new_set_ref
        .prop_map
        .value(921)
        .get_reapply_concept_descriptor()
        .is_none());
    assert!(new_set_ref
        .prop_map
        .value(922)
        .get_reapply_concept_descriptor()
        .is_none());
    assert_eq!(
        env.ctx
            .process_context()
            .prop_binding_des(first_new_des)
            .get_propagation_binding(),
        first_binding
    );
    assert_eq!(
        env.ctx
            .process_context()
            .prop_binding_des(second_new_des)
            .get_propagation_binding(),
        second_binding
    );

    let mut link = new_set_ref.get_propagation_binding_descriptor_linker();
    let mut linked_bindings = Vec::new();
    while link.is_some() {
        linked_bindings.push(
            env.ctx
                .process_context()
                .prop_binding_des(link)
                .get_propagation_binding(),
        );
        link = env.ctx.process_context().prop_binding_des(link).get_next();
    }
    linked_bindings.sort_by_key(|id| id.raw);
    assert_eq!(linked_bindings, vec![first_binding, second_binding]);
}

#[test]
fn pbind_implication_new_binding_initializes_propagation_bindings() {
    use super::super::model::op;
    use super::super::process::binding_hash::ConceptPropagationBindingSetHash;
    use super::super::process::propagation_binding::{
        PropagationBinding, PropagationBindingDescriptor,
    };

    let mut env = build_env();
    let root = env.root;

    let binding_trigger = {
        let mut c = Concept::new();
        c.set_concept_tag(183);
        c.set_operator_code(op::CCPBINDTRIG);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let source_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(184);
        c.set_operator_code(op::CCPBINDIMPL);
        c.set_operand_count(1);
        c.add_operand_linker(binding_trigger, false);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let source_con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(source_con_des);
        d.concept = source_concept;
        d.dep_track_point = TrackPointId::NONE;
    }
    let mut cpd_val = ConceptProcessDescriptor::new();
    cpd_val.concept_des = source_con_des;
    cpd_val.dep_track_point = TrackPointId::NONE;
    let mut con_proc_des = env.ctx.process_context_mut().alloc_con_proc_desc(cpd_val);

    let prop_binding = {
        let mut b = PropagationBinding::new();
        b.init_propagation_binding(923, TrackPointId::NONE, root, source_con_des, Id::NONE);
        env.ctx.process_context_mut().alloc_prop_binding(b)
    };
    let prev_des = {
        let mut d = PropagationBindingDescriptor::new();
        d.init_propagation_binding_descriptor(prop_binding, TrackPointId::NONE);
        let id = env.ctx.process_context_mut().alloc_prop_binding_des(d);
        env.ctx
            .process_context_mut()
            .prop_binding_des_mut(id)
            .set_data(id);
        id
    };

    let hash = env
        .ctx
        .process_context_mut()
        .node_concept_propagation_binding_set_hash(root);
    let source_tag = env
        .ctx
        .ontology_arenas()
        .concept(source_concept)
        .get_concept_tag();
    let source_set = ConceptPropagationBindingSetHash::get_propagation_binding_set(
        env.ctx.process_context_mut(),
        hash,
        source_tag,
        true,
    );
    env.ctx
        .process_context_mut()
        .prop_binding_set_mut(source_set)
        .prop_map
        .entry_mut(923)
        .set_propagation_binding_descriptor(prev_des);

    let binding_tag = env
        .ctx
        .ontology_arenas()
        .concept(binding_trigger)
        .get_concept_tag();
    env.ctx
        .process_context_mut()
        .node_concept_processing_queue(root, true);
    let mut root_ref = root;
    env.algo.apply_bind_propagate_implication_rule(
        &mut root_ref,
        &mut con_proc_des,
        false,
        &mut env.ctx,
    );

    let trigger_set = ConceptPropagationBindingSetHash::get_propagation_binding_set(
        env.ctx.process_context_mut(),
        hash,
        binding_tag,
        false,
    );
    assert!(
        trigger_set.is_some(),
        "PBIND implication new-binding path must create the trigger propagation-binding set"
    );
    let installed = env
        .ctx
        .process_context()
        .prop_binding_set(trigger_set)
        .prop_map
        .value(923)
        .get_propagation_binding_descriptor();
    assert!(
        installed.is_some(),
        "PBIND implication new-binding path must initialize copied propagation bindings"
    );
    assert_ne!(installed, prev_des);
    assert_eq!(
        env.ctx
            .process_context()
            .prop_binding_des(installed)
            .get_propagation_binding(),
        prop_binding
    );
    let binding_con_des = env
        .ctx
        .process_context()
        .prop_binding_set(trigger_set)
        .get_concept_descriptor();
    assert!(binding_con_des.is_some());
    assert_eq!(
        env.ctx
            .process_context()
            .con_desc(binding_con_des)
            .get_concept(),
        binding_trigger
    );
}

#[test]
fn pbind_variable_new_binding_allocates_special_propagation_binding() {
    use super::super::model::individual::Variable;
    use super::super::model::op;
    use super::super::process::binding_hash::ConceptPropagationBindingSetHash;

    let mut env = build_env();
    let root = env.root;

    let variable = env
        .ctx
        .ontology_arenas_mut()
        .alloc_variable(Variable::new());
    let binding_trigger = {
        let mut c = Concept::new();
        c.set_concept_tag(185);
        c.set_operator_code(op::CCPBINDTRIG);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let variable_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(186);
        c.set_operator_code(op::CCPBINDVARIABLE);
        c.set_operand_count(1);
        c.add_operand_linker(binding_trigger, false);
        c.add_variable_linker(variable);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let source_con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(source_con_des);
        d.concept = variable_concept;
        d.dep_track_point = TrackPointId::NONE;
    }
    let mut cpd_val = ConceptProcessDescriptor::new();
    cpd_val.concept_des = source_con_des;
    cpd_val.dep_track_point = TrackPointId::NONE;
    let mut con_proc_des = env.ctx.process_context_mut().alloc_con_proc_desc(cpd_val);
    let expected_prop_id = env
        .ctx
        .processing_data_box_mut()
        .next_binding_propagation_id(false);

    env.ctx
        .process_context_mut()
        .node_concept_processing_queue(root, true);
    let mut root_ref = root;
    env.algo
        .apply_bind_variable_rule(&mut root_ref, &mut con_proc_des, false, &mut env.ctx);

    let hash = env
        .ctx
        .process_context_mut()
        .node_concept_propagation_binding_set_hash(root);
    let binding_tag = env
        .ctx
        .ontology_arenas()
        .concept(binding_trigger)
        .get_concept_tag();
    let trigger_set = ConceptPropagationBindingSetHash::get_propagation_binding_set(
        env.ctx.process_context_mut(),
        hash,
        binding_tag,
        false,
    );
    assert!(
        trigger_set.is_some(),
        "PBIND variable new-binding path must create the trigger propagation-binding set"
    );
    let special_des = env
        .ctx
        .process_context()
        .prop_binding_set(trigger_set)
        .get_new_special_propagation_binding_descriptor();
    assert!(
        special_des.is_some(),
        "PBIND variable new-binding path must install the special propagation-binding descriptor"
    );
    let prop_binding = env
        .ctx
        .process_context()
        .prop_binding_des(special_des)
        .get_propagation_binding();
    let prop_binding_ref = env.ctx.process_context().prop_binding(prop_binding);
    assert_eq!(prop_binding_ref.get_propagation_id(), expected_prop_id);
    assert_eq!(prop_binding_ref.get_binded_individual(), root);
    assert_eq!(prop_binding_ref.get_binded_variable(), variable);
    let binding_con_des = prop_binding_ref.get_binded_concept_descriptor();
    assert_eq!(
        env.ctx
            .process_context()
            .con_desc(binding_con_des)
            .get_concept(),
        binding_trigger
    );
    assert_eq!(
        env.ctx
            .process_context()
            .prop_binding_set(trigger_set)
            .prop_map
            .value(expected_prop_id)
            .get_propagation_binding_descriptor(),
        special_des
    );
}

#[test]
fn pbind_variable_existing_binding_allocates_missing_special_propagation_binding() {
    use super::super::model::individual::Variable;
    use super::super::model::op;
    use super::super::process::binding_hash::ConceptPropagationBindingSetHash;

    let mut env = build_env();
    let root = env.root;

    let variable = env
        .ctx
        .ontology_arenas_mut()
        .alloc_variable(Variable::new());
    let binding_trigger = {
        let mut c = Concept::new();
        c.set_concept_tag(187);
        c.set_operator_code(op::CCPBINDTRIG);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let variable_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(188);
        c.set_operator_code(op::CCPBINDVARIABLE);
        c.set_operand_count(1);
        c.add_operand_linker(binding_trigger, false);
        c.add_variable_linker(variable);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let source_con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(source_con_des);
        d.concept = variable_concept;
        d.dep_track_point = TrackPointId::NONE;
    }
    let mut cpd_val = ConceptProcessDescriptor::new();
    cpd_val.concept_des = source_con_des;
    cpd_val.dep_track_point = TrackPointId::NONE;
    let mut con_proc_des = env.ctx.process_context_mut().alloc_con_proc_desc(cpd_val);

    let binding_con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(binding_con_des);
        d.concept = binding_trigger;
        d.dep_track_point = TrackPointId::NONE;
    }
    let binding_tag = env
        .ctx
        .ontology_arenas()
        .concept(binding_trigger)
        .get_concept_tag();
    let label_set = env
        .ctx
        .process_context_mut()
        .node_reapply_concept_label_set(root);
    let desc_negated = |_id| false;
    env.ctx
        .process_context_mut()
        .label_set_mut(label_set)
        .insert_concept_get_clash_resolved(
            binding_con_des,
            binding_trigger,
            binding_tag,
            false,
            &desc_negated,
            None,
            None,
        );
    let hash = env
        .ctx
        .process_context_mut()
        .node_concept_propagation_binding_set_hash(root);
    let trigger_set = ConceptPropagationBindingSetHash::get_propagation_binding_set(
        env.ctx.process_context_mut(),
        hash,
        binding_tag,
        true,
    );
    env.ctx
        .process_context_mut()
        .prop_binding_set_mut(trigger_set)
        .set_concept_descriptor(binding_con_des);
    assert!(
        env.ctx
            .process_context()
            .prop_binding_set(trigger_set)
            .get_new_special_propagation_binding_descriptor()
            .is_none(),
        "test setup must enter the existing-binding branch without a special descriptor"
    );
    let expected_prop_id = env
        .ctx
        .processing_data_box_mut()
        .next_binding_propagation_id(false);

    env.ctx
        .process_context_mut()
        .node_concept_processing_queue(root, true);
    let mut root_ref = root;
    env.algo
        .apply_bind_variable_rule(&mut root_ref, &mut con_proc_des, false, &mut env.ctx);

    let special_des = env
        .ctx
        .process_context()
        .prop_binding_set(trigger_set)
        .get_new_special_propagation_binding_descriptor();
    assert!(
        special_des.is_some(),
        "PBIND variable existing-binding path must allocate the missing special descriptor"
    );
    let prop_binding = env
        .ctx
        .process_context()
        .prop_binding_des(special_des)
        .get_propagation_binding();
    let prop_binding_ref = env.ctx.process_context().prop_binding(prop_binding);
    assert_eq!(prop_binding_ref.get_propagation_id(), expected_prop_id);
    assert_eq!(prop_binding_ref.get_binded_individual(), root);
    assert_eq!(prop_binding_ref.get_binded_variable(), variable);
    assert_eq!(
        prop_binding_ref.get_binded_concept_descriptor(),
        binding_con_des
    );
    assert_eq!(
        env.ctx
            .process_context()
            .prop_binding_set(trigger_set)
            .prop_map
            .value(expected_prop_id)
            .get_propagation_binding_descriptor(),
        special_des
    );
}

#[test]
fn varbind_variable_without_propagation_set_does_not_create_binding_path() {
    use super::super::model::individual::Variable;
    use super::super::model::op;

    let mut env = build_env();
    let mut root = env.root;
    let variable = env
        .ctx
        .ontology_arenas_mut()
        .alloc_variable(Variable::new());
    let binding_trigger = {
        let mut c = Concept::new();
        c.set_concept_tag(218);
        c.set_operator_code(op::CCVARBINDTRIG);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let variable_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(219);
        c.set_operator_code(op::CCVARBINDVARIABLE);
        c.set_operand_count(1);
        c.add_operand_linker(binding_trigger, false);
        c.add_variable_linker(variable);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let source_con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(source_con_des);
        d.concept = variable_concept;
        d.dep_track_point = TrackPointId::NONE;
    }
    let mut cpd_val = ConceptProcessDescriptor::new();
    cpd_val.concept_des = source_con_des;
    cpd_val.dep_track_point = TrackPointId::NONE;
    let mut con_proc_des = env.ctx.process_context_mut().alloc_con_proc_desc(cpd_val);

    env.algo
        .apply_varbind_variable_rule(&mut root, &mut con_proc_des, false, &mut env.ctx);

    assert!(
        env.ctx
            .process_context()
            .node(root)
            .use_concept_var_bind_path_set_hash
            .is_none(),
        "without a source propagation-binding set, VARBINDVARIABLE must not create variable-binding paths"
    );
}

#[test]
fn varbind_variable_matching_propagation_binding_creates_binding_path() {
    use super::super::model::individual::Variable;
    use super::super::model::op;
    use super::super::process::binding_hash::{
        ConceptPropagationBindingSetHash, ConceptVariableBindingPathSetHash,
    };
    use super::super::process::propagation_binding::{
        PropagationBinding, PropagationBindingDescriptor, PropagationBindingSet,
    };

    let mut env = build_env();
    let mut root = env.root;
    let variable = env
        .ctx
        .ontology_arenas_mut()
        .alloc_variable(Variable::new());
    let binding_trigger = {
        let mut c = Concept::new();
        c.set_concept_tag(220);
        c.set_operator_code(op::CCVARBINDTRIG);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let variable_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(221);
        c.set_operator_code(op::CCVARBINDVARIABLE);
        c.set_operand_count(1);
        c.add_operand_linker(binding_trigger, false);
        c.add_variable_linker(variable);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let source_con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(source_con_des);
        d.concept = variable_concept;
        d.dep_track_point = TrackPointId::NONE;
    }
    let mut cpd_val = ConceptProcessDescriptor::new();
    cpd_val.concept_des = source_con_des;
    cpd_val.dep_track_point = TrackPointId::NONE;
    let mut con_proc_des = env.ctx.process_context_mut().alloc_con_proc_desc(cpd_val);

    let prop_binding = {
        let mut b = PropagationBinding::new();
        b.init_propagation_binding(951, TrackPointId::NONE, root, source_con_des, variable);
        env.ctx.process_context_mut().alloc_prop_binding(b)
    };
    let prop_des = {
        let mut d = PropagationBindingDescriptor::new();
        d.init_propagation_binding_descriptor(prop_binding, TrackPointId::NONE);
        env.ctx.process_context_mut().alloc_prop_binding_des(d)
    };
    let prop_hash = env
        .ctx
        .process_context_mut()
        .node_concept_propagation_binding_set_hash(root);
    let source_tag = env
        .ctx
        .ontology_arenas()
        .concept(variable_concept)
        .get_concept_tag();
    let source_set = ConceptPropagationBindingSetHash::get_propagation_binding_set(
        env.ctx.process_context_mut(),
        prop_hash,
        source_tag,
        true,
    );
    PropagationBindingSet::add_propagation_binding(
        env.ctx.process_context_mut(),
        source_set,
        prop_des,
        false,
    );
    let expected_path_id = env
        .ctx
        .processing_data_box_mut()
        .next_variable_binding_path_id(false);

    env.algo
        .apply_varbind_variable_rule(&mut root, &mut con_proc_des, false, &mut env.ctx);

    let binding_tag = env
        .ctx
        .ontology_arenas()
        .concept(binding_trigger)
        .get_concept_tag();
    let path_hash = env
        .ctx
        .process_context_mut()
        .node_concept_variable_binding_path_set_hash(root);
    let trigger_set = ConceptVariableBindingPathSetHash::get_variable_binding_path_set(
        env.ctx.process_context_mut(),
        path_hash,
        binding_tag,
        false,
    );
    assert!(trigger_set.is_some());
    let path_des = env
        .ctx
        .process_context()
        .vbpath_set(trigger_set)
        .get_variable_binding_path_map()
        .value(expected_path_id)
        .get_variable_binding_path_descriptor();
    assert!(path_des.is_some());
    let path = env
        .ctx
        .process_context()
        .vbpath_des(path_des)
        .get_variable_binding_path();
    assert_eq!(
        env.ctx.process_context().vbpath(path).get_propagation_id(),
        expected_path_id
    );
    let var_binding_des = env
        .ctx
        .process_context()
        .vbpath(path)
        .get_variable_binding_descriptor_linker();
    let var_binding = env
        .ctx
        .process_context()
        .var_binding_des(var_binding_des)
        .get_variable_binding();
    let var_binding_ref = env.ctx.process_context().var_binding(var_binding);
    assert_eq!(var_binding_ref.get_binded_variable(), variable);
    assert_eq!(var_binding_ref.get_binded_individual(), root);
    assert_eq!(
        env.ctx
            .process_context()
            .con_desc(
                env.ctx
                    .process_context()
                    .vbpath_set(trigger_set)
                    .get_concept_descriptor()
            )
            .get_concept(),
        binding_trigger
    );
    assert_eq!(
        env.ctx
            .process_context()
            .con_var_bind_path_set_hash(path_hash)
            .get_last_variable_binding_description_linker(),
        path_des
    );
}

#[test]
fn varbind_variable_completed_transition_extension_prevents_duplicate_path() {
    use super::super::model::individual::Variable;
    use super::super::model::op;
    use super::super::process::binding_hash::{
        ConceptPropagationBindingSetHash, ConceptVariableBindingPathSetHash,
    };
    use super::super::process::propagation_binding::{
        PropagationBinding, PropagationBindingDescriptor, PropagationBindingSet,
    };

    let mut env = build_env();
    let mut root = env.root;
    let variable = env
        .ctx
        .ontology_arenas_mut()
        .alloc_variable(Variable::new());
    let binding_trigger = {
        let mut c = Concept::new();
        c.set_concept_tag(222);
        c.set_operator_code(op::CCVARBINDTRIG);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let variable_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(223);
        c.set_operator_code(op::CCVARBINDVARIABLE);
        c.set_operand_count(1);
        c.add_operand_linker(binding_trigger, false);
        c.add_variable_linker(variable);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let source_con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(source_con_des);
        d.concept = variable_concept;
        d.dep_track_point = TrackPointId::NONE;
    }
    let mut cpd_val = ConceptProcessDescriptor::new();
    cpd_val.concept_des = source_con_des;
    cpd_val.dep_track_point = TrackPointId::NONE;
    let mut con_proc_des = env.ctx.process_context_mut().alloc_con_proc_desc(cpd_val);

    let prop_binding = {
        let mut b = PropagationBinding::new();
        b.init_propagation_binding(952, TrackPointId::NONE, root, source_con_des, variable);
        env.ctx.process_context_mut().alloc_prop_binding(b)
    };
    let prop_des = {
        let mut d = PropagationBindingDescriptor::new();
        d.init_propagation_binding_descriptor(prop_binding, TrackPointId::NONE);
        env.ctx.process_context_mut().alloc_prop_binding_des(d)
    };
    let prop_hash = env
        .ctx
        .process_context_mut()
        .node_concept_propagation_binding_set_hash(root);
    let source_tag = env
        .ctx
        .ontology_arenas()
        .concept(variable_concept)
        .get_concept_tag();
    let source_set = ConceptPropagationBindingSetHash::get_propagation_binding_set(
        env.ctx.process_context_mut(),
        prop_hash,
        source_tag,
        true,
    );
    PropagationBindingSet::add_propagation_binding(
        env.ctx.process_context_mut(),
        source_set,
        prop_des,
        false,
    );
    let first_path_id = env
        .ctx
        .processing_data_box_mut()
        .next_variable_binding_path_id(false);

    env.algo
        .apply_varbind_variable_rule(&mut root, &mut con_proc_des, false, &mut env.ctx);
    let next_after_first = env
        .ctx
        .processing_data_box_mut()
        .next_variable_binding_path_id(false);
    env.algo
        .apply_varbind_variable_rule(&mut root, &mut con_proc_des, false, &mut env.ctx);
    let next_after_second = env
        .ctx
        .processing_data_box_mut()
        .next_variable_binding_path_id(false);

    assert_eq!(next_after_first, first_path_id + 1);
    assert_eq!(
        next_after_second, next_after_first,
        "completed transition extension must prevent duplicate variable-binding path creation"
    );
    let binding_tag = env
        .ctx
        .ontology_arenas()
        .concept(binding_trigger)
        .get_concept_tag();
    let path_hash = env
        .ctx
        .process_context_mut()
        .node_concept_variable_binding_path_set_hash(root);
    let trigger_set = ConceptVariableBindingPathSetHash::get_variable_binding_path_set(
        env.ctx.process_context_mut(),
        path_hash,
        binding_tag,
        false,
    );
    assert_eq!(
        env.ctx
            .process_context()
            .vbpath_set(trigger_set)
            .get_variable_binding_path_map()
            .count(),
        1
    );
}

#[test]
fn varbind_join_get_joined_path_merges_sorted_bindings_and_caches_symmetrically() {
    use super::super::model::individual::Variable;
    use super::super::process::varbind::{
        VarBindingDescriptorId, VarBindingPathId, VariableBinding, VariableBindingDescriptor,
        VariableBindingPath,
    };

    fn make_path(
        env: &mut SelfTestEnv,
        root: NodeId,
        prop_id: i64,
        vars: &[super::super::model::VariableId],
    ) -> VarBindingPathId {
        let mut head = VarBindingDescriptorId::NONE;
        let mut last = VarBindingDescriptorId::NONE;
        for var in vars {
            let mut binding = VariableBinding::new();
            binding.init_variable_binding(TrackPointId::NONE, root, *var);
            let binding_id = env.ctx.process_context_mut().alloc_var_binding(binding);
            let mut des = VariableBindingDescriptor::new();
            des.init_variable_binding_descriptor(binding_id);
            let des_id = env.ctx.process_context_mut().alloc_var_binding_des(des);
            if last.is_some() {
                env.ctx
                    .process_context_mut()
                    .var_binding_des_mut(last)
                    .set_next(des_id);
            } else {
                head = des_id;
            }
            last = des_id;
        }
        let mut path = VariableBindingPath::new();
        path.init_variable_binding_path(prop_id, head);
        env.ctx.process_context_mut().alloc_vbpath(path)
    }

    fn binding_vars(
        env: &SelfTestEnv,
        path: VarBindingPathId,
    ) -> Vec<super::super::model::VariableId> {
        let mut vars = Vec::new();
        let mut des = env
            .ctx
            .process_context()
            .vbpath(path)
            .get_variable_binding_descriptor_linker();
        while des.is_some() {
            let binding = env
                .ctx
                .process_context()
                .var_binding_des(des)
                .get_variable_binding();
            vars.push(
                env.ctx
                    .process_context()
                    .var_binding(binding)
                    .get_binded_variable(),
            );
            des = env.ctx.process_context().var_binding_des(des).get_next();
        }
        vars
    }

    let mut env = build_env();
    let root = env.root;
    let var_a = env
        .ctx
        .ontology_arenas_mut()
        .alloc_variable(Variable::new());
    let var_b = env
        .ctx
        .ontology_arenas_mut()
        .alloc_variable(Variable::new());
    let left = make_path(&mut env, root, 701, &[var_a]);
    let right = make_path(&mut env, root, 702, &[var_a, var_b]);

    let merged = env
        .algo
        .get_joined_variable_binding_path(left, right, &mut env.ctx);
    let merged_again = env
        .algo
        .get_joined_variable_binding_path(right, left, &mut env.ctx);

    assert_eq!(merged, merged_again, "merge hash must be symmetric");
    assert_eq!(binding_vars(&env, merged), vec![var_a, var_b]);
}

#[test]
fn varbind_join_propagate_records_one_side_then_combines_other_side() {
    use super::super::model::individual::Variable;
    use super::super::process::binding_hash::ConceptVariableBindingPathSetHash;
    use super::super::process::varbind::{
        VarBindingId, VarBindingPathDescriptorId, VarBindingPathId, VarBindingPathSetId,
        VariableBinding, VariableBindingDescriptor, VariableBindingPath,
        VariableBindingPathDescriptor, VariableBindingPathJoiningHash,
    };

    fn make_path_descriptor(
        env: &mut SelfTestEnv,
        prop_id: i64,
        binding_id: VarBindingId,
    ) -> VarBindingPathDescriptorId {
        let mut binding_des = VariableBindingDescriptor::new();
        binding_des.init_variable_binding_descriptor(binding_id);
        let binding_des_id = env
            .ctx
            .process_context_mut()
            .alloc_var_binding_des(binding_des);
        let mut path = VariableBindingPath::new();
        path.init_variable_binding_path(prop_id, binding_des_id);
        let path_id: VarBindingPathId = env.ctx.process_context_mut().alloc_vbpath(path);
        let mut path_des = VariableBindingPathDescriptor::new();
        path_des.init_variable_binding_path_descriptor(path_id, TrackPointId::NONE);
        env.ctx.process_context_mut().alloc_vbpath_des(path_des)
    }

    let mut env = build_env();
    let root = env.root;
    let var_a = env
        .ctx
        .ontology_arenas_mut()
        .alloc_variable(Variable::new());
    let shared_binding = {
        let mut binding = VariableBinding::new();
        binding.init_variable_binding(TrackPointId::NONE, root, var_a);
        env.ctx.process_context_mut().alloc_var_binding(binding)
    };
    let join_trigger_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(230);
        c.add_variable_linker(var_a);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let join_output_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(231);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let joining_con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    env.ctx
        .process_context_mut()
        .con_desc_mut(joining_con_des)
        .concept = join_trigger_concept;
    let left_des = make_path_descriptor(&mut env, 801, shared_binding);
    let right_des = make_path_descriptor(&mut env, 802, shared_binding);
    let join_hash = env
        .ctx
        .process_context_mut()
        .alloc_vbpath_join_hash(VariableBindingPathJoiningHash::new(INVALID));
    let path_set_hash = env
        .ctx
        .process_context_mut()
        .node_concept_variable_binding_path_set_hash(root);
    let mut join_con_des = ConDescId::NONE;
    let mut join_path_set = VarBindingPathSetId::NONE;

    let first_added = env.algo.propagate_variable_bindings_joins(
        root,
        joining_con_des,
        join_output_concept,
        left_des,
        true,
        join_hash,
        path_set_hash,
        &mut join_con_des,
        &mut join_path_set,
        &mut env.ctx,
    );
    assert!(!first_added, "first side only records the left path");
    assert!(join_con_des.is_none());
    assert!(join_path_set.is_none());

    let second_added = env.algo.propagate_variable_bindings_joins(
        root,
        joining_con_des,
        join_output_concept,
        right_des,
        false,
        join_hash,
        path_set_hash,
        &mut join_con_des,
        &mut join_path_set,
        &mut env.ctx,
    );
    assert!(second_added, "opposite side must create a joined path");
    assert!(join_con_des.is_some());
    assert!(join_path_set.is_some());
    assert_eq!(
        env.ctx
            .process_context()
            .vbpath_set(join_path_set)
            .get_variable_binding_path_map()
            .count(),
        1
    );
    assert_eq!(
        env.ctx
            .process_context()
            .vbpath_set(join_path_set)
            .get_concept_descriptor(),
        join_con_des
    );
    let join_tag = env
        .ctx
        .ontology_arenas()
        .concept(join_output_concept)
        .get_concept_tag();
    assert_eq!(
        ConceptVariableBindingPathSetHash::get_variable_binding_path_set(
            env.ctx.process_context_mut(),
            path_set_hash,
            join_tag,
            false,
        ),
        join_path_set
    );
}

struct VarbindJoinRuleFixture {
    root: NodeId,
    con_proc_des: super::super::process::ConProcDescId,
    join_concept: ConceptId,
    join_tag: i64,
}

fn build_varbind_join_rule_fixture(env: &mut SelfTestEnv, base_tag: i64) -> VarbindJoinRuleFixture {
    use super::super::model::individual::Variable;
    use super::super::model::op;
    use super::super::process::binding_hash::{
        ConceptPropagationBindingSetHash, ConceptVariableBindingPathSetHash,
    };
    use super::super::process::varbind::{
        VarBindingId, VarBindingPathDescriptorId, VariableBinding, VariableBindingDescriptor,
        VariableBindingPath, VariableBindingPathDescriptor, VariableBindingPathSet,
    };

    fn make_path_descriptor(
        env: &mut SelfTestEnv,
        prop_id: i64,
        binding_id: VarBindingId,
    ) -> VarBindingPathDescriptorId {
        let mut binding_des = VariableBindingDescriptor::new();
        binding_des.init_variable_binding_descriptor(binding_id);
        let binding_des_id = env
            .ctx
            .process_context_mut()
            .alloc_var_binding_des(binding_des);
        let mut path = VariableBindingPath::new();
        path.init_variable_binding_path(prop_id, binding_des_id);
        let path_id = env.ctx.process_context_mut().alloc_vbpath(path);
        let mut path_des = VariableBindingPathDescriptor::new();
        path_des.init_variable_binding_path_descriptor(path_id, TrackPointId::NONE);
        env.ctx.process_context_mut().alloc_vbpath_des(path_des)
    }

    let mut root = env.root;
    let variable = env
        .ctx
        .ontology_arenas_mut()
        .alloc_variable(Variable::new());
    let join_output = {
        let mut c = Concept::new();
        c.set_concept_tag(base_tag);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let left_trigger = {
        let mut c = Concept::new();
        c.set_concept_tag(base_tag + 1);
        c.set_operator_code(op::CCVARBINDTRIG);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let right_trigger = {
        let mut c = Concept::new();
        c.set_concept_tag(base_tag + 2);
        c.set_operator_code(op::CCVARBINDTRIG);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let join_rule = {
        let mut c = Concept::new();
        c.set_concept_tag(base_tag + 3);
        c.set_operator_code(op::CCVARBINDJOIN);
        c.set_operand_count(3);
        c.add_operand_linker(join_output, false);
        c.add_operand_linker(left_trigger, false);
        c.add_operand_linker(right_trigger, false);
        c.add_variable_linker(variable);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };

    env.algo.add_concept_to_individual(
        left_trigger,
        true,
        &mut root,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );
    env.algo.add_concept_to_individual(
        right_trigger,
        true,
        &mut root,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );

    let source_con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(source_con_des);
        d.concept = join_rule;
        d.dep_track_point = TrackPointId::NONE;
    }
    let mut cpd_val = ConceptProcessDescriptor::new();
    cpd_val.concept_des = source_con_des;
    cpd_val.dep_track_point = TrackPointId::NONE;
    let con_proc_des = env.ctx.process_context_mut().alloc_con_proc_desc(cpd_val);

    let prop_hash = env
        .ctx
        .process_context_mut()
        .node_concept_propagation_binding_set_hash(root);
    let source_tag = env
        .ctx
        .ontology_arenas()
        .concept(join_rule)
        .get_concept_tag();
    let source_set = ConceptPropagationBindingSetHash::get_propagation_binding_set(
        env.ctx.process_context_mut(),
        prop_hash,
        source_tag,
        true,
    );
    env.ctx
        .process_context_mut()
        .prop_binding_set_mut(source_set)
        .set_propagate_all_flag(true);

    let shared_binding = {
        let mut binding = VariableBinding::new();
        binding.init_variable_binding(TrackPointId::NONE, root, variable);
        env.ctx.process_context_mut().alloc_var_binding(binding)
    };
    let left_des = make_path_descriptor(env, base_tag * 10 + 1, shared_binding);
    let right_des = make_path_descriptor(env, base_tag * 10 + 2, shared_binding);
    let path_hash = env
        .ctx
        .process_context_mut()
        .node_concept_variable_binding_path_set_hash(root);
    for (concept, path_id, path_des) in [
        (left_trigger, base_tag * 10 + 1, left_des),
        (right_trigger, base_tag * 10 + 2, right_des),
    ] {
        let tag = env.ctx.ontology_arenas().concept(concept).get_concept_tag();
        let set = ConceptVariableBindingPathSetHash::get_variable_binding_path_set(
            env.ctx.process_context_mut(),
            path_hash,
            tag,
            true,
        );
        env.ctx
            .process_context_mut()
            .vbpath_set_mut(set)
            .get_variable_binding_path_map_mut()
            .entry_mut(path_id)
            .set_variable_binding_path_descriptor(path_des);
        VariableBindingPathSet::add_variable_binding_path_descriptor_linker(
            env.ctx.process_context_mut(),
            set,
            path_des,
        );
    }

    VarbindJoinRuleFixture {
        root,
        con_proc_des,
        join_concept: join_output,
        join_tag: base_tag,
    }
}

#[test]
fn varbind_join_rule_combines_existing_left_and_right_paths() {
    use super::super::process::binding_hash::ConceptVariableBindingPathSetHash;

    let mut env = build_env();
    let fixture = build_varbind_join_rule_fixture(&mut env, 240);
    let mut root = fixture.root;
    let mut con_proc_des = fixture.con_proc_des;

    env.algo
        .apply_varbind_propagate_join_rule(&mut root, &mut con_proc_des, false, &mut env.ctx);

    let path_hash = env
        .ctx
        .process_context()
        .node(root)
        .use_concept_var_bind_path_set_hash;
    let join_set = ConceptVariableBindingPathSetHash::get_variable_binding_path_set(
        env.ctx.process_context_mut(),
        path_hash,
        fixture.join_tag,
        false,
    );
    assert!(
        join_set.is_some(),
        "VARBINDJOIN rule must create the output concept's variable-binding path set"
    );
    assert_eq!(
        env.ctx
            .process_context()
            .vbpath_set(join_set)
            .get_variable_binding_path_map()
            .count(),
        1
    );
    let join_con_des = env
        .ctx
        .process_context()
        .vbpath_set(join_set)
        .get_concept_descriptor();
    assert_eq!(
        env.ctx
            .process_context()
            .con_desc(join_con_des)
            .get_concept(),
        fixture.join_concept
    );
}

#[test]
fn varbind_join_rule_completed_extension_prevents_duplicate_join_path() {
    use super::super::process::binding_hash::ConceptVariableBindingPathSetHash;

    let mut env = build_env();
    let fixture = build_varbind_join_rule_fixture(&mut env, 250);
    let mut root = fixture.root;
    let mut con_proc_des = fixture.con_proc_des;

    env.algo
        .apply_varbind_propagate_join_rule(&mut root, &mut con_proc_des, false, &mut env.ctx);
    env.algo
        .apply_varbind_propagate_join_rule(&mut root, &mut con_proc_des, false, &mut env.ctx);

    let path_hash = env
        .ctx
        .process_context()
        .node(root)
        .use_concept_var_bind_path_set_hash;
    let join_set = ConceptVariableBindingPathSetHash::get_variable_binding_path_set(
        env.ctx.process_context_mut(),
        path_hash,
        fixture.join_tag,
        false,
    );
    assert!(join_set.is_some());
    assert_eq!(
        env.ctx
            .process_context()
            .vbpath_set(join_set)
            .get_variable_binding_path_map()
            .count(),
        1,
        "unchanged transition extension must not duplicate the joined path"
    );
}

#[test]
fn varbind_grounding_without_path_set_noops_after_live_prelude() {
    use super::super::model::op;

    let mut env = build_env();
    let mut root = env.root;
    let grounding_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(260);
        c.set_operator_code(op::CCVARBINDGROUND);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let source_con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(source_con_des);
        d.concept = grounding_concept;
        d.dep_track_point = TrackPointId::NONE;
    }
    let mut cpd_val = ConceptProcessDescriptor::new();
    cpd_val.concept_des = source_con_des;
    cpd_val.dep_track_point = TrackPointId::NONE;
    let mut con_proc_des = env.ctx.process_context_mut().alloc_con_proc_desc(cpd_val);

    env.algo.apply_varbind_propagate_grounding_rule(
        &mut root,
        &mut con_proc_des,
        false,
        &mut env.ctx,
    );

    assert_eq!(
        env.algo.stat_var_binding_grounding_count, 0,
        "without a source variable-binding path set, VARBIND grounding must not emit concepts"
    );
    assert!(
        env.ctx
            .process_context()
            .node(root)
            .use_concept_var_bind_path_set_hash
            .is_none(),
        "the false-localize path-set lookup must not allocate the node path-set hash"
    );
}

#[test]
fn propagation_binding_fresh_successor_producer_updates_missing_entries_and_reapplies() {
    use super::super::model::op;
    use super::super::model::role::Role;
    use super::super::process::edge::IndividualLinkEdge;
    use super::super::process::propagation_binding::{
        PropagationBinding, PropagationBindingDescriptor, PropagationBindingMapData,
        PropagationBindingReapplyConceptDescriptor, PropagationBindingSet,
    };

    let mut env = build_env();
    let root = env.root;
    let succ = env
        .algo
        .create_new_individual(TrackPointId::NONE, false, &mut env.ctx);
    let role_r = env.ctx.ontology_arenas_mut().alloc_role(Role::new());
    let rest_link = {
        let mut edge = IndividualLinkEdge::new();
        edge.creator = root;
        edge.set_source_individual(root);
        edge.set_destination_individual(succ);
        edge.set_link_role(role_r);
        edge.set_dependency_track_point(TrackPointId::NONE);
        env.ctx.process_context_mut().alloc_edge(edge)
    };

    let triggered_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(187);
        c.set_operator_code(op::CCAND);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let binding_con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(binding_con_des);
        d.concept = triggered_concept;
        d.dep_track_point = TrackPointId::NONE;
    }
    let reapply_con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(reapply_con_des);
        d.concept = triggered_concept;
        d.dep_track_point = TrackPointId::NONE;
    }

    let update_binding = {
        let mut b = PropagationBinding::new();
        b.init_propagation_binding(931, TrackPointId::NONE, succ, binding_con_des, Id::NONE);
        env.ctx.process_context_mut().alloc_prop_binding(b)
    };
    let update_prev_des = {
        let mut d = PropagationBindingDescriptor::new();
        d.init_propagation_binding_descriptor(update_binding, TrackPointId::NONE);
        let id = env.ctx.process_context_mut().alloc_prop_binding_des(d);
        env.ctx
            .process_context_mut()
            .prop_binding_des_mut(id)
            .set_data(id);
        id
    };
    let insert_binding = {
        let mut b = PropagationBinding::new();
        b.init_propagation_binding(932, TrackPointId::NONE, succ, binding_con_des, Id::NONE);
        env.ctx.process_context_mut().alloc_prop_binding(b)
    };
    let insert_prev_des = {
        let mut d = PropagationBindingDescriptor::new();
        d.init_propagation_binding_descriptor(insert_binding, TrackPointId::NONE);
        let id = env.ctx.process_context_mut().alloc_prop_binding_des(d);
        env.ctx
            .process_context_mut()
            .prop_binding_des_mut(id)
            .set_data(id);
        id
    };
    let keep_binding = {
        let mut b = PropagationBinding::new();
        b.init_propagation_binding(933, TrackPointId::NONE, succ, binding_con_des, Id::NONE);
        env.ctx.process_context_mut().alloc_prop_binding(b)
    };
    let keep_prev_des = {
        let mut d = PropagationBindingDescriptor::new();
        d.init_propagation_binding_descriptor(keep_binding, TrackPointId::NONE);
        let id = env.ctx.process_context_mut().alloc_prop_binding_des(d);
        env.ctx
            .process_context_mut()
            .prop_binding_des_mut(id)
            .set_data(id);
        id
    };
    let keep_existing_des = {
        let mut d = PropagationBindingDescriptor::new();
        d.init_propagation_binding_descriptor(keep_binding, TrackPointId::NONE);
        let id = env.ctx.process_context_mut().alloc_prop_binding_des(d);
        env.ctx
            .process_context_mut()
            .prop_binding_des_mut(id)
            .set_data(id);
        id
    };
    let reapply_des = {
        let mut d = PropagationBindingReapplyConceptDescriptor::new();
        d.init_reapply_descriptor(succ, update_binding, reapply_con_des, TrackPointId::NONE);
        env.ctx
            .process_context_mut()
            .alloc_prop_binding_reapply_con_des(d)
    };

    let prev_set = env
        .ctx
        .process_context_mut()
        .alloc_prop_binding_set(PropagationBindingSet::new(INVALID));
    {
        let prev_set_ref = env.ctx.process_context_mut().prop_binding_set_mut(prev_set);
        prev_set_ref.set_propagate_all_flag(true);
        prev_set_ref
            .prop_map
            .entry_mut(931)
            .set_propagation_binding_descriptor(update_prev_des);
        prev_set_ref
            .prop_map
            .entry_mut(932)
            .set_propagation_binding_descriptor(insert_prev_des);
        prev_set_ref
            .prop_map
            .entry_mut(933)
            .set_propagation_binding_descriptor(keep_prev_des);
    }
    let new_set = env
        .ctx
        .process_context_mut()
        .alloc_prop_binding_set(PropagationBindingSet::new(INVALID));
    {
        let new_set_ref = env.ctx.process_context_mut().prop_binding_set_mut(new_set);
        new_set_ref
            .prop_map
            .map
            .insert(931, PropagationBindingMapData::new(Id::NONE));
        new_set_ref
            .prop_map
            .entry_mut(931)
            .set_reapply_concept_descriptor(reapply_des);
        new_set_ref
            .prop_map
            .entry_mut(933)
            .set_propagation_binding_descriptor(keep_existing_des);
    }

    let mut root_ref = root;
    assert!(
        env.algo.propagate_fresh_propagation_bindings_to_successor(
            &mut root_ref,
            succ,
            binding_con_des,
            new_set,
            prev_set,
            rest_link,
            &mut env.ctx,
        ),
        "successor fresh producer must report propagated bindings"
    );

    let new_set_ref = env.ctx.process_context().prop_binding_set(new_set);
    assert!(new_set_ref.get_propagate_all_flag());
    let update_new_des = new_set_ref
        .prop_map
        .value(931)
        .get_propagation_binding_descriptor();
    let insert_new_des = new_set_ref
        .prop_map
        .value(932)
        .get_propagation_binding_descriptor();
    let keep_new_des = new_set_ref
        .prop_map
        .value(933)
        .get_propagation_binding_descriptor();
    assert!(update_new_des.is_some());
    assert!(insert_new_des.is_some());
    assert_ne!(update_new_des, update_prev_des);
    assert_ne!(insert_new_des, insert_prev_des);
    assert_eq!(keep_new_des, keep_existing_des);
    assert_eq!(
        env.ctx
            .process_context()
            .prop_binding_des(update_new_des)
            .get_propagation_binding(),
        update_binding
    );
    assert_eq!(
        env.ctx
            .process_context()
            .prop_binding_des(insert_new_des)
            .get_propagation_binding(),
        insert_binding
    );

    let queue = env
        .ctx
        .process_context_mut()
        .node_concept_processing_queue(succ, false);
    let mut queued_concepts = Vec::new();
    while !env
        .ctx
        .process_context()
        .concept_proc_queue(queue)
        .is_empty()
    {
        let queued = ConceptProcessingQueue::take_next_concept_descriptor_process(
            queue,
            env.ctx.process_context_mut(),
        );
        queued_concepts.push(
            env.ctx
                .process_context()
                .con_proc_desc(queued)
                .get_concept_descriptor(),
        );
    }
    assert!(
        queued_concepts.contains(&reapply_con_des),
        "successor fresh update must apply the existing propagation-binding reapply linker"
    );
}

#[test]
fn propagation_binding_successor_dispatcher_initializes_missing_operand_binding() {
    use super::super::model::op;
    use super::super::model::role::Role;
    use super::super::process::binding_hash::ConceptPropagationBindingSetHash;
    use super::super::process::edge::IndividualLinkEdge;
    use super::super::process::propagation_binding::{
        PropagationBinding, PropagationBindingDescriptor,
    };

    let mut env = build_env();
    let root = env.root;
    let mut succ = env
        .algo
        .create_new_individual(TrackPointId::NONE, false, &mut env.ctx);
    let role_r = env.ctx.ontology_arenas_mut().alloc_role(Role::new());
    let rest_link = {
        let mut edge = IndividualLinkEdge::new();
        edge.creator = root;
        edge.set_source_individual(root);
        edge.set_destination_individual(succ);
        edge.set_link_role(role_r);
        edge.set_dependency_track_point(TrackPointId::NONE);
        env.ctx.process_context_mut().alloc_edge(edge)
    };

    let binding_operand = {
        let mut c = Concept::new();
        c.set_concept_tag(189);
        c.set_operator_code(op::CCPBINDTRIG);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let source_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(190);
        c.set_operator_code(op::CCPBINDALL);
        c.set_operand_count(1);
        c.add_operand_linker(binding_operand, false);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let source_con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(source_con_des);
        d.concept = source_concept;
        d.dep_track_point = TrackPointId::NONE;
    }
    let source_tag = env
        .ctx
        .ontology_arenas()
        .concept(source_concept)
        .get_concept_tag();
    let operand_tag = env
        .ctx
        .ontology_arenas()
        .concept(binding_operand)
        .get_concept_tag();

    let prop_binding = {
        let mut b = PropagationBinding::new();
        b.init_propagation_binding(941, TrackPointId::NONE, root, source_con_des, Id::NONE);
        env.ctx.process_context_mut().alloc_prop_binding(b)
    };
    let prev_des = {
        let mut d = PropagationBindingDescriptor::new();
        d.init_propagation_binding_descriptor(prop_binding, TrackPointId::NONE);
        let id = env.ctx.process_context_mut().alloc_prop_binding_des(d);
        env.ctx
            .process_context_mut()
            .prop_binding_des_mut(id)
            .set_data(id);
        id
    };
    let source_hash = env
        .ctx
        .process_context_mut()
        .node_concept_propagation_binding_set_hash(root);
    let prev_set = ConceptPropagationBindingSetHash::get_propagation_binding_set(
        env.ctx.process_context_mut(),
        source_hash,
        source_tag,
        true,
    );
    {
        let prev_set_ref = env.ctx.process_context_mut().prop_binding_set_mut(prev_set);
        prev_set_ref.set_propagate_all_flag(true);
        prev_set_ref
            .prop_map
            .entry_mut(941)
            .set_propagation_binding_descriptor(prev_des);
    }

    env.algo.propagate_propagation_bindings_to_successor(
        root,
        &mut succ,
        source_concept,
        false,
        source_con_des,
        rest_link,
        &mut env.ctx,
    );

    let succ_hash = env
        .ctx
        .process_context_mut()
        .node_concept_propagation_binding_set_hash(succ);
    let succ_set = ConceptPropagationBindingSetHash::get_propagation_binding_set(
        env.ctx.process_context_mut(),
        succ_hash,
        operand_tag,
        false,
    );
    assert!(
        succ_set.is_some(),
        "successor dispatcher must create the operand propagation-binding set"
    );
    let succ_set_ref = env.ctx.process_context().prop_binding_set(succ_set);
    assert!(succ_set_ref.get_propagate_all_flag());
    let copied_des = succ_set_ref
        .prop_map
        .value(941)
        .get_propagation_binding_descriptor();
    assert!(copied_des.is_some());
    assert_ne!(copied_des, prev_des);
    assert_eq!(
        env.ctx
            .process_context()
            .prop_binding_des(copied_des)
            .get_propagation_binding(),
        prop_binding
    );
    assert!(
        env.ctx
            .process_context()
            .prop_binding_set(succ_set)
            .get_concept_descriptor()
            .is_some(),
        "successor dispatcher must bind the new operand concept descriptor to the set"
    );
}

#[test]
fn propagation_binding_successor_dispatcher_refreshes_existing_operand_binding() {
    use super::super::model::op;
    use super::super::model::role::Role;
    use super::super::process::binding_hash::ConceptPropagationBindingSetHash;
    use super::super::process::edge::IndividualLinkEdge;
    use super::super::process::propagation_binding::{
        PropagationBinding, PropagationBindingDescriptor,
    };

    let mut env = build_env();
    let root = env.root;
    let mut succ = env
        .algo
        .create_new_individual(TrackPointId::NONE, false, &mut env.ctx);
    let role_r = env.ctx.ontology_arenas_mut().alloc_role(Role::new());
    let rest_link = {
        let mut edge = IndividualLinkEdge::new();
        edge.creator = root;
        edge.set_source_individual(root);
        edge.set_destination_individual(succ);
        edge.set_link_role(role_r);
        edge.set_dependency_track_point(TrackPointId::NONE);
        env.ctx.process_context_mut().alloc_edge(edge)
    };

    let binding_operand = {
        let mut c = Concept::new();
        c.set_concept_tag(191);
        c.set_operator_code(op::CCPBINDTRIG);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let source_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(192);
        c.set_operator_code(op::CCPBINDALL);
        c.set_operand_count(1);
        c.add_operand_linker(binding_operand, false);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let source_con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(source_con_des);
        d.concept = source_concept;
        d.dep_track_point = TrackPointId::NONE;
    }
    let binding_con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(binding_con_des);
        d.concept = binding_operand;
        d.dep_track_point = TrackPointId::NONE;
    }
    let source_tag = env
        .ctx
        .ontology_arenas()
        .concept(source_concept)
        .get_concept_tag();
    let operand_tag = env
        .ctx
        .ontology_arenas()
        .concept(binding_operand)
        .get_concept_tag();

    let succ_label_set = env
        .ctx
        .process_context_mut()
        .node_reapply_concept_label_set(succ);
    let desc_negated = |_id| false;
    env.ctx
        .process_context_mut()
        .label_set_mut(succ_label_set)
        .insert_concept_get_clash_resolved(
            binding_con_des,
            binding_operand,
            operand_tag,
            false,
            &desc_negated,
            None,
            None,
        );

    let prop_binding = {
        let mut b = PropagationBinding::new();
        b.init_propagation_binding(942, TrackPointId::NONE, root, source_con_des, Id::NONE);
        env.ctx.process_context_mut().alloc_prop_binding(b)
    };
    let prev_des = {
        let mut d = PropagationBindingDescriptor::new();
        d.init_propagation_binding_descriptor(prop_binding, TrackPointId::NONE);
        let id = env.ctx.process_context_mut().alloc_prop_binding_des(d);
        env.ctx
            .process_context_mut()
            .prop_binding_des_mut(id)
            .set_data(id);
        id
    };
    let source_hash = env
        .ctx
        .process_context_mut()
        .node_concept_propagation_binding_set_hash(root);
    let prev_set = ConceptPropagationBindingSetHash::get_propagation_binding_set(
        env.ctx.process_context_mut(),
        source_hash,
        source_tag,
        true,
    );
    env.ctx
        .process_context_mut()
        .prop_binding_set_mut(prev_set)
        .prop_map
        .entry_mut(942)
        .set_propagation_binding_descriptor(prev_des);

    env.algo.propagate_propagation_bindings_to_successor(
        root,
        &mut succ,
        source_concept,
        false,
        source_con_des,
        rest_link,
        &mut env.ctx,
    );

    let succ_hash = env
        .ctx
        .process_context_mut()
        .node_concept_propagation_binding_set_hash(succ);
    let succ_set = ConceptPropagationBindingSetHash::get_propagation_binding_set(
        env.ctx.process_context_mut(),
        succ_hash,
        operand_tag,
        false,
    );
    assert!(
        succ_set.is_some(),
        "existing-operand dispatcher path must create/refresh the successor propagation set"
    );
    let refreshed_des = env
        .ctx
        .process_context()
        .prop_binding_set(succ_set)
        .prop_map
        .value(942)
        .get_propagation_binding_descriptor();
    assert!(refreshed_des.is_some());
    assert_ne!(refreshed_des, prev_des);
    assert_eq!(
        env.ctx
            .process_context()
            .prop_binding_des(refreshed_des)
            .get_propagation_binding(),
        prop_binding
    );
}

#[test]
fn pbind_all_nonrestricted_fans_out_over_role_successor_links() {
    use super::super::model::op;
    use super::super::model::role::Role;
    use super::super::process::binding_hash::ConceptPropagationBindingSetHash;
    use super::super::process::edge::IndividualLinkEdge;
    use super::super::process::propagation_binding::{
        PropagationBinding, PropagationBindingDescriptor,
    };
    use super::super::process::rs1::ReapplyQueueIterator;

    let mut env = build_env();
    let root = env.root;
    let succ = env
        .algo
        .create_new_individual(TrackPointId::NONE, false, &mut env.ctx);
    let role_r = {
        let mut r = Role::new();
        r.set_role_tag(193);
        env.ctx.ontology_arenas_mut().alloc_role(r)
    };
    let rest_link = {
        let mut edge = IndividualLinkEdge::new();
        edge.creator = root;
        edge.set_source_individual(root);
        edge.set_destination_individual(succ);
        edge.set_link_role(role_r);
        edge.set_dependency_track_point(TrackPointId::NONE);
        env.ctx.process_context_mut().alloc_edge(edge)
    };
    let mut reapply_it = ReapplyQueueIterator::empty();
    env.ctx
        .process_context_mut()
        .node_install_individual_link(root, rest_link, &mut reapply_it);

    let binding_operand = {
        let mut c = Concept::new();
        c.set_concept_tag(193);
        c.set_operator_code(op::CCPBINDTRIG);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let source_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(194);
        c.set_operator_code(op::CCPBINDALL);
        c.set_role(role_r);
        c.set_operand_count(1);
        c.add_operand_linker(binding_operand, false);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let source_con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(source_con_des);
        d.concept = source_concept;
        d.dep_track_point = TrackPointId::NONE;
    }
    let mut cpd_val = ConceptProcessDescriptor::new();
    cpd_val.concept_des = source_con_des;
    cpd_val.dep_track_point = TrackPointId::NONE;
    let mut con_proc_des = env.ctx.process_context_mut().alloc_con_proc_desc(cpd_val);

    let source_tag = env
        .ctx
        .ontology_arenas()
        .concept(source_concept)
        .get_concept_tag();
    let operand_tag = env
        .ctx
        .ontology_arenas()
        .concept(binding_operand)
        .get_concept_tag();
    let prop_binding = {
        let mut b = PropagationBinding::new();
        b.init_propagation_binding(943, TrackPointId::NONE, root, source_con_des, Id::NONE);
        env.ctx.process_context_mut().alloc_prop_binding(b)
    };
    let prev_des = {
        let mut d = PropagationBindingDescriptor::new();
        d.init_propagation_binding_descriptor(prop_binding, TrackPointId::NONE);
        let id = env.ctx.process_context_mut().alloc_prop_binding_des(d);
        env.ctx
            .process_context_mut()
            .prop_binding_des_mut(id)
            .set_data(id);
        id
    };
    let source_hash = env
        .ctx
        .process_context_mut()
        .node_concept_propagation_binding_set_hash(root);
    let prev_set = ConceptPropagationBindingSetHash::get_propagation_binding_set(
        env.ctx.process_context_mut(),
        source_hash,
        source_tag,
        true,
    );
    env.ctx
        .process_context_mut()
        .prop_binding_set_mut(prev_set)
        .prop_map
        .entry_mut(943)
        .set_propagation_binding_descriptor(prev_des);

    let mut root_ref = root;
    env.algo
        .apply_bind_propagate_all_rule(&mut root_ref, &mut con_proc_des, false, &mut env.ctx);

    let succ_hash = env
        .ctx
        .process_context_mut()
        .node_concept_propagation_binding_set_hash(succ);
    let succ_set = ConceptPropagationBindingSetHash::get_propagation_binding_set(
        env.ctx.process_context_mut(),
        succ_hash,
        operand_tag,
        false,
    );
    assert!(
        succ_set.is_some(),
        "non-restricted PBINDALL must fan out over installed role successor links"
    );
    let copied_des = env
        .ctx
        .process_context()
        .prop_binding_set(succ_set)
        .prop_map
        .value(943)
        .get_propagation_binding_descriptor();
    assert!(copied_des.is_some());
    assert_ne!(copied_des, prev_des);
    assert_eq!(
        env.ctx
            .process_context()
            .prop_binding_des(copied_des)
            .get_propagation_binding(),
        prop_binding
    );
}

#[test]
fn varbind_all_nonrestricted_initializes_successor_variable_bindings() {
    use super::super::model::op;
    use super::super::model::role::Role;
    use super::super::process::binding_hash::ConceptVariableBindingPathSetHash;
    use super::super::process::edge::IndividualLinkEdge;
    use super::super::process::rs1::ReapplyQueueIterator;
    use super::super::process::varbind::{
        VariableBindingPath, VariableBindingPathDescriptor, VariableBindingPathSet,
    };

    let mut env = build_env();
    let root = env.root;
    let succ = env
        .algo
        .create_new_individual(TrackPointId::NONE, false, &mut env.ctx);
    let role_r = {
        let mut r = Role::new();
        r.set_role_tag(195);
        env.ctx.ontology_arenas_mut().alloc_role(r)
    };
    let rest_link = {
        let mut edge = IndividualLinkEdge::new();
        edge.creator = root;
        edge.set_source_individual(root);
        edge.set_destination_individual(succ);
        edge.set_link_role(role_r);
        edge.set_dependency_track_point(TrackPointId::NONE);
        env.ctx.process_context_mut().alloc_edge(edge)
    };
    let mut reapply_it = ReapplyQueueIterator::empty();
    env.ctx
        .process_context_mut()
        .node_install_individual_link(root, rest_link, &mut reapply_it);

    let binding_operand = {
        let mut c = Concept::new();
        c.set_concept_tag(196);
        c.set_operator_code(op::CCVARBINDTRIG);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let source_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(197);
        c.set_operator_code(op::CCVARBINDALL);
        c.set_role(role_r);
        c.set_operand_count(1);
        c.add_operand_linker(binding_operand, false);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let source_con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(source_con_des);
        d.concept = source_concept;
        d.dep_track_point = TrackPointId::NONE;
    }
    let mut cpd_val = ConceptProcessDescriptor::new();
    cpd_val.concept_des = source_con_des;
    cpd_val.dep_track_point = TrackPointId::NONE;
    let mut con_proc_des = env.ctx.process_context_mut().alloc_con_proc_desc(cpd_val);

    let source_tag = env
        .ctx
        .ontology_arenas()
        .concept(source_concept)
        .get_concept_tag();
    let operand_tag = env
        .ctx
        .ontology_arenas()
        .concept(binding_operand)
        .get_concept_tag();
    let var_path = {
        let id = env
            .ctx
            .process_context_mut()
            .alloc_vbpath(VariableBindingPath::new());
        env.ctx
            .process_context_mut()
            .vbpath_mut(id)
            .init_variable_binding_path(944, Id::NONE);
        id
    };
    let prev_des = {
        let mut d = VariableBindingPathDescriptor::new();
        d.init_variable_binding_path_descriptor(var_path, TrackPointId::NONE);
        env.ctx.process_context_mut().alloc_vbpath_des(d)
    };
    let source_hash = env
        .ctx
        .process_context_mut()
        .node_concept_variable_binding_path_set_hash(root);
    let prev_set = ConceptVariableBindingPathSetHash::get_variable_binding_path_set(
        env.ctx.process_context_mut(),
        source_hash,
        source_tag,
        true,
    );
    env.ctx
        .process_context_mut()
        .vbpath_set_mut(prev_set)
        .get_variable_binding_path_map_mut()
        .entry_mut(944)
        .set_variable_binding_path_descriptor(prev_des);
    VariableBindingPathSet::add_variable_binding_path_descriptor_linker(
        env.ctx.process_context_mut(),
        prev_set,
        prev_des,
    );

    let mut root_ref = root;
    env.algo.apply_varbind_propagate_all_rule(
        &mut root_ref,
        &mut con_proc_des,
        false,
        &mut env.ctx,
    );

    let succ_hash = env
        .ctx
        .process_context_mut()
        .node_concept_variable_binding_path_set_hash(succ);
    let succ_set = ConceptVariableBindingPathSetHash::get_variable_binding_path_set(
        env.ctx.process_context_mut(),
        succ_hash,
        operand_tag,
        false,
    );
    assert!(
        succ_set.is_some(),
        "non-restricted VARBINDALL must initialize the successor variable-binding path set"
    );
    let copied_des = env
        .ctx
        .process_context()
        .vbpath_set(succ_set)
        .get_variable_binding_path_map()
        .value(944)
        .get_variable_binding_path_descriptor();
    assert!(copied_des.is_some());
    assert_ne!(copied_des, prev_des);
    assert_eq!(
        env.ctx
            .process_context()
            .vbpath_des(copied_des)
            .get_variable_binding_path(),
        var_path
    );
}

#[test]
fn varbind_all_nonrestricted_refreshes_existing_successor_variable_bindings() {
    use super::super::model::op;
    use super::super::model::role::Role;
    use super::super::process::binding_hash::ConceptVariableBindingPathSetHash;
    use super::super::process::edge::IndividualLinkEdge;
    use super::super::process::rs1::ReapplyQueueIterator;
    use super::super::process::varbind::{VariableBindingPath, VariableBindingPathDescriptor};

    let mut env = build_env();
    let root = env.root;
    let mut succ = env
        .algo
        .create_new_individual(TrackPointId::NONE, false, &mut env.ctx);
    let role_r = {
        let mut r = Role::new();
        r.set_role_tag(198);
        env.ctx.ontology_arenas_mut().alloc_role(r)
    };
    let rest_link = {
        let mut edge = IndividualLinkEdge::new();
        edge.creator = root;
        edge.set_source_individual(root);
        edge.set_destination_individual(succ);
        edge.set_link_role(role_r);
        edge.set_dependency_track_point(TrackPointId::NONE);
        env.ctx.process_context_mut().alloc_edge(edge)
    };
    let mut reapply_it = ReapplyQueueIterator::empty();
    env.ctx
        .process_context_mut()
        .node_install_individual_link(root, rest_link, &mut reapply_it);

    let binding_operand = {
        let mut c = Concept::new();
        c.set_concept_tag(199);
        c.set_operator_code(op::CCVARBINDTRIG);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let source_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(200);
        c.set_operator_code(op::CCVARBINDALL);
        c.set_role(role_r);
        c.set_operand_count(1);
        c.add_operand_linker(binding_operand, false);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let source_con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(source_con_des);
        d.concept = source_concept;
        d.dep_track_point = TrackPointId::NONE;
    }
    let mut cpd_val = ConceptProcessDescriptor::new();
    cpd_val.concept_des = source_con_des;
    cpd_val.dep_track_point = TrackPointId::NONE;
    let mut con_proc_des = env.ctx.process_context_mut().alloc_con_proc_desc(cpd_val);

    env.algo.add_concept_to_individual(
        binding_operand,
        false,
        &mut succ,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );

    let source_tag = env
        .ctx
        .ontology_arenas()
        .concept(source_concept)
        .get_concept_tag();
    let operand_tag = env
        .ctx
        .ontology_arenas()
        .concept(binding_operand)
        .get_concept_tag();
    let var_path = {
        let id = env
            .ctx
            .process_context_mut()
            .alloc_vbpath(VariableBindingPath::new());
        env.ctx
            .process_context_mut()
            .vbpath_mut(id)
            .init_variable_binding_path(945, Id::NONE);
        id
    };
    let prev_des = {
        let mut d = VariableBindingPathDescriptor::new();
        d.init_variable_binding_path_descriptor(var_path, TrackPointId::NONE);
        env.ctx.process_context_mut().alloc_vbpath_des(d)
    };
    let source_hash = env
        .ctx
        .process_context_mut()
        .node_concept_variable_binding_path_set_hash(root);
    let prev_set = ConceptVariableBindingPathSetHash::get_variable_binding_path_set(
        env.ctx.process_context_mut(),
        source_hash,
        source_tag,
        true,
    );
    env.ctx
        .process_context_mut()
        .vbpath_set_mut(prev_set)
        .get_variable_binding_path_map_mut()
        .entry_mut(945)
        .set_variable_binding_path_descriptor(prev_des);

    let mut root_ref = root;
    env.algo.apply_varbind_propagate_all_rule(
        &mut root_ref,
        &mut con_proc_des,
        false,
        &mut env.ctx,
    );

    let succ_hash = env
        .ctx
        .process_context_mut()
        .node_concept_variable_binding_path_set_hash(succ);
    let succ_set = ConceptVariableBindingPathSetHash::get_variable_binding_path_set(
        env.ctx.process_context_mut(),
        succ_hash,
        operand_tag,
        false,
    );
    let copied_des = env
        .ctx
        .process_context()
        .vbpath_set(succ_set)
        .get_variable_binding_path_map()
        .value(945)
        .get_variable_binding_path_descriptor();
    assert!(copied_des.is_some());
    assert_ne!(copied_des, prev_des);
    assert_eq!(
        env.ctx
            .process_context()
            .vbpath_des(copied_des)
            .get_variable_binding_path(),
        var_path
    );
}

#[test]
fn varbind_and_initializes_same_node_variable_bindings() {
    use super::super::model::op;
    use super::super::process::binding_hash::ConceptVariableBindingPathSetHash;
    use super::super::process::varbind::{
        VariableBindingPath, VariableBindingPathDescriptor, VariableBindingPathSet,
    };

    let mut env = build_env();
    let root = env.root;
    let binding_operand = {
        let mut c = Concept::new();
        c.set_concept_tag(201);
        c.set_operator_code(op::CCVARBINDTRIG);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let source_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(202);
        c.set_operator_code(op::CCVARBINDAND);
        c.set_operand_count(1);
        c.add_operand_linker(binding_operand, false);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let source_con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(source_con_des);
        d.concept = source_concept;
        d.dep_track_point = TrackPointId::NONE;
    }
    let mut cpd_val = ConceptProcessDescriptor::new();
    cpd_val.concept_des = source_con_des;
    cpd_val.dep_track_point = TrackPointId::NONE;
    let mut con_proc_des = env.ctx.process_context_mut().alloc_con_proc_desc(cpd_val);

    let source_tag = env
        .ctx
        .ontology_arenas()
        .concept(source_concept)
        .get_concept_tag();
    let operand_tag = env
        .ctx
        .ontology_arenas()
        .concept(binding_operand)
        .get_concept_tag();
    let source_hash = env
        .ctx
        .process_context_mut()
        .node_concept_variable_binding_path_set_hash(root);
    let prev_set = ConceptVariableBindingPathSetHash::get_variable_binding_path_set(
        env.ctx.process_context_mut(),
        source_hash,
        source_tag,
        true,
    );
    let mut previous_descriptors = Vec::new();
    for prop_id in [952, 951] {
        let path = {
            let id = env
                .ctx
                .process_context_mut()
                .alloc_vbpath(VariableBindingPath::new());
            env.ctx
                .process_context_mut()
                .vbpath_mut(id)
                .init_variable_binding_path(prop_id, Id::NONE);
            id
        };
        let des = {
            let mut d = VariableBindingPathDescriptor::new();
            d.init_variable_binding_path_descriptor(path, TrackPointId::NONE);
            env.ctx.process_context_mut().alloc_vbpath_des(d)
        };
        env.ctx
            .process_context_mut()
            .vbpath_set_mut(prev_set)
            .get_variable_binding_path_map_mut()
            .entry_mut(prop_id)
            .set_variable_binding_path_descriptor(des);
        VariableBindingPathSet::add_variable_binding_path_descriptor_linker(
            env.ctx.process_context_mut(),
            prev_set,
            des,
        );
        previous_descriptors.push((prop_id, path, des));
    }

    let mut root_ref = root;
    env.algo
        .apply_variable_binding_and_rule(&mut root_ref, &mut con_proc_des, false, &mut env.ctx);

    let trigger_set = ConceptVariableBindingPathSetHash::get_variable_binding_path_set(
        env.ctx.process_context_mut(),
        source_hash,
        operand_tag,
        false,
    );
    assert!(
        trigger_set.is_some(),
        "VARBINDAND missing-trigger branch must create the trigger variable-binding set"
    );
    for (prop_id, path, old_des) in previous_descriptors {
        let new_des = env
            .ctx
            .process_context()
            .vbpath_set(trigger_set)
            .get_variable_binding_path_map()
            .value(prop_id)
            .get_variable_binding_path_descriptor();
        assert!(new_des.is_some());
        assert_ne!(new_des, old_des);
        assert_eq!(
            env.ctx
                .process_context()
                .vbpath_des(new_des)
                .get_variable_binding_path(),
            path
        );
    }
}

#[test]
fn varbind_and_refreshes_same_node_variable_bindings_in_merge_order() {
    use super::super::model::op;
    use super::super::process::binding_hash::ConceptVariableBindingPathSetHash;
    use super::super::process::varbind::{VariableBindingPath, VariableBindingPathDescriptor};

    let mut env = build_env();
    let mut root = env.root;
    let binding_operand = {
        let mut c = Concept::new();
        c.set_concept_tag(203);
        c.set_operator_code(op::CCVARBINDTRIG);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let source_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(204);
        c.set_operator_code(op::CCVARBINDAND);
        c.set_operand_count(1);
        c.add_operand_linker(binding_operand, false);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let source_con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(source_con_des);
        d.concept = source_concept;
        d.dep_track_point = TrackPointId::NONE;
    }
    let mut cpd_val = ConceptProcessDescriptor::new();
    cpd_val.concept_des = source_con_des;
    cpd_val.dep_track_point = TrackPointId::NONE;
    let mut con_proc_des = env.ctx.process_context_mut().alloc_con_proc_desc(cpd_val);

    env.algo.add_concept_to_individual(
        binding_operand,
        false,
        &mut root,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );

    let source_tag = env
        .ctx
        .ontology_arenas()
        .concept(source_concept)
        .get_concept_tag();
    let operand_tag = env
        .ctx
        .ontology_arenas()
        .concept(binding_operand)
        .get_concept_tag();
    let source_hash = env
        .ctx
        .process_context_mut()
        .node_concept_variable_binding_path_set_hash(root);
    let prev_set = ConceptVariableBindingPathSetHash::get_variable_binding_path_set(
        env.ctx.process_context_mut(),
        source_hash,
        source_tag,
        true,
    );
    let trigger_set = ConceptVariableBindingPathSetHash::get_variable_binding_path_set(
        env.ctx.process_context_mut(),
        source_hash,
        operand_tag,
        true,
    );

    let mut paths = Vec::new();
    for prop_id in [10, 20, 30] {
        let path = {
            let id = env
                .ctx
                .process_context_mut()
                .alloc_vbpath(VariableBindingPath::new());
            env.ctx
                .process_context_mut()
                .vbpath_mut(id)
                .init_variable_binding_path(prop_id, Id::NONE);
            id
        };
        let des = {
            let mut d = VariableBindingPathDescriptor::new();
            d.init_variable_binding_path_descriptor(path, TrackPointId::NONE);
            env.ctx.process_context_mut().alloc_vbpath_des(d)
        };
        env.ctx
            .process_context_mut()
            .vbpath_set_mut(prev_set)
            .get_variable_binding_path_map_mut()
            .entry_mut(prop_id)
            .set_variable_binding_path_descriptor(des);
        paths.push((prop_id, path, des));
    }

    let existing_path = paths
        .iter()
        .find(|(prop_id, _, _)| *prop_id == 10)
        .map(|(_, path, _)| *path)
        .unwrap();
    let existing_des = {
        let mut d = VariableBindingPathDescriptor::new();
        d.init_variable_binding_path_descriptor(existing_path, TrackPointId::NONE);
        env.ctx.process_context_mut().alloc_vbpath_des(d)
    };
    env.ctx
        .process_context_mut()
        .vbpath_set_mut(trigger_set)
        .get_variable_binding_path_map_mut()
        .entry_mut(10)
        .set_variable_binding_path_descriptor(existing_des);

    env.algo
        .apply_variable_binding_and_rule(&mut root, &mut con_proc_des, false, &mut env.ctx);

    let map = env
        .ctx
        .process_context()
        .vbpath_set(trigger_set)
        .get_variable_binding_path_map();
    assert_eq!(
        map.value(10).get_variable_binding_path_descriptor(),
        existing_des,
        "fresh propagation must preserve already-present path descriptors"
    );
    let des20 = map.value(20).get_variable_binding_path_descriptor();
    let des30 = map.value(30).get_variable_binding_path_descriptor();
    assert!(des20.is_some());
    assert!(des30.is_some());
    assert_ne!(des20, paths[1].2);
    assert_ne!(des30, paths[2].2);
    assert_eq!(
        env.ctx
            .process_context()
            .vbpath_des(des20)
            .get_variable_binding_path(),
        paths[1].1
    );
    assert_eq!(
        env.ctx
            .process_context()
            .vbpath_des(des30)
            .get_variable_binding_path(),
        paths[2].1
    );

    let last = env
        .ctx
        .process_context()
        .con_var_bind_path_set_hash(source_hash)
        .get_last_variable_binding_description_linker();
    assert_eq!(
        last, des30,
        "ascending merge with front append yields 30 first"
    );
    assert_eq!(
        env.ctx.process_context().vbpath_des(last).get_next(),
        des20,
        "descriptor linker preserves the Konclude append order 30 -> 20"
    );
}

#[test]
fn varbind_and_existing_trigger_drains_condensed_reapply_queue_after_fresh_paths() {
    use super::super::model::op;
    use super::super::process::binding_hash::ConceptVariableBindingPathSetHash;
    use super::super::process::varbind::{VariableBindingPath, VariableBindingPathDescriptor};

    let mut env = build_env();
    let mut root = env.root;
    let binding_operand = {
        let mut c = Concept::new();
        c.set_concept_tag(205);
        c.set_operator_code(op::CCVARBINDTRIG);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let source_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(206);
        c.set_operator_code(op::CCVARBINDAND);
        c.set_operand_count(1);
        c.add_operand_linker(binding_operand, false);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let queued_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(207);
        c.set_operator_code(op::CCAND);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let source_con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(source_con_des);
        d.concept = source_concept;
        d.dep_track_point = TrackPointId::NONE;
    }
    let queued_con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(queued_con_des);
        d.concept = queued_concept;
        d.dep_track_point = TrackPointId::NONE;
    }
    let mut cpd_val = ConceptProcessDescriptor::new();
    cpd_val.concept_des = source_con_des;
    cpd_val.dep_track_point = TrackPointId::NONE;
    let mut con_proc_des = env.ctx.process_context_mut().alloc_con_proc_desc(cpd_val);

    env.algo.add_concept_to_individual(
        binding_operand,
        false,
        &mut root,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );
    let setup_queue = env
        .ctx
        .process_context_mut()
        .node_concept_processing_queue(root, false);
    while setup_queue.is_some()
        && env
            .ctx
            .process_context()
            .concept_proc_queue(setup_queue)
            .get_descriptor_count()
            > 0
    {
        ConceptProcessingQueue::take_next_concept_descriptor_process(
            setup_queue,
            env.ctx.process_context_mut(),
        );
    }

    let source_tag = env
        .ctx
        .ontology_arenas()
        .concept(source_concept)
        .get_concept_tag();
    let operand_tag = env
        .ctx
        .ontology_arenas()
        .concept(binding_operand)
        .get_concept_tag();
    let source_hash = env
        .ctx
        .process_context_mut()
        .node_concept_variable_binding_path_set_hash(root);
    let prev_set = ConceptVariableBindingPathSetHash::get_variable_binding_path_set(
        env.ctx.process_context_mut(),
        source_hash,
        source_tag,
        true,
    );
    let trigger_set = ConceptVariableBindingPathSetHash::get_variable_binding_path_set(
        env.ctx.process_context_mut(),
        source_hash,
        operand_tag,
        true,
    );

    let existing_path = {
        let id = env
            .ctx
            .process_context_mut()
            .alloc_vbpath(VariableBindingPath::new());
        env.ctx
            .process_context_mut()
            .vbpath_mut(id)
            .init_variable_binding_path(40, Id::NONE);
        id
    };
    let fresh_path = {
        let id = env
            .ctx
            .process_context_mut()
            .alloc_vbpath(VariableBindingPath::new());
        env.ctx
            .process_context_mut()
            .vbpath_mut(id)
            .init_variable_binding_path(50, Id::NONE);
        id
    };
    for (prop_id, path) in [(40, existing_path), (50, fresh_path)] {
        let mut d = VariableBindingPathDescriptor::new();
        d.init_variable_binding_path_descriptor(path, TrackPointId::NONE);
        let des = env.ctx.process_context_mut().alloc_vbpath_des(d);
        env.ctx
            .process_context_mut()
            .vbpath_set_mut(prev_set)
            .get_variable_binding_path_map_mut()
            .entry_mut(prop_id)
            .set_variable_binding_path_descriptor(des);
    }
    let mut existing_d = VariableBindingPathDescriptor::new();
    existing_d.init_variable_binding_path_descriptor(existing_path, TrackPointId::NONE);
    let existing_des = env.ctx.process_context_mut().alloc_vbpath_des(existing_d);
    env.ctx
        .process_context_mut()
        .vbpath_set_mut(trigger_set)
        .get_variable_binding_path_map_mut()
        .entry_mut(40)
        .set_variable_binding_path_descriptor(existing_des);

    env.algo.add_concept_to_reapply_queue_concept(
        queued_con_des,
        binding_operand,
        false,
        root,
        false,
        TrackPointId::NONE,
        &mut env.ctx,
    );
    assert!(
        env.algo.is_concept_in_reapply_queue_concept(
            queued_con_des,
            binding_operand,
            false,
            root,
            &mut env.ctx
        ),
        "setup must seed the binding-trigger condensed reapply queue"
    );

    env.algo
        .apply_variable_binding_and_rule(&mut root, &mut con_proc_des, false, &mut env.ctx);

    assert!(
        !env.algo.is_concept_in_reapply_queue_concept(
            queued_con_des,
            binding_operand,
            false,
            root,
            &mut env.ctx
        ),
        "VARBINDAND existing-trigger reapply drain must clear the dynamic queue"
    );

    let queue = env
        .ctx
        .process_context_mut()
        .node_concept_processing_queue(root, false);
    assert_eq!(
        env.ctx
            .process_context()
            .concept_proc_queue(queue)
            .get_descriptor_count(),
        1,
        "drained condensed reapply descriptor must remain in the node concept queue"
    );
    let queued = ConceptProcessingQueue::take_next_concept_descriptor_process(
        queue,
        env.ctx.process_context_mut(),
    );
    let queued_con_des_from_queue = env
        .ctx
        .process_context()
        .con_proc_desc(queued)
        .get_concept_descriptor();
    assert_eq!(
        queued_con_des_from_queue, queued_con_des,
        "drained reapply descriptor must reach the concept processing queue"
    );
    let batch_queue = env
        .ctx
        .get_variable_binding_concept_batch_processing_queue(false);
    assert!(batch_queue.is_some());
    let batch_entry = env
        .ctx
        .take_next_variable_binding_concept_batch_process_individual(batch_queue);
    assert!(
        matches!(batch_entry, Some((concept, node, des)) if concept == binding_operand
            && node == root
            && env.ctx.process_context().con_desc(
                env.ctx.process_context().con_proc_desc(des).get_concept_descriptor()
            ).get_concept() == binding_operand),
        "fresh propagation must requeue the existing binding trigger descriptor through the batch queue"
    );
}

#[test]
fn varbind_implication_installs_missing_trigger_reapply() {
    use super::super::model::op;

    let mut env = build_env();
    let mut root = env.root;
    let binding_operand = {
        let mut c = Concept::new();
        c.set_concept_tag(208);
        c.set_operator_code(op::CCVARBINDTRIG);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let trigger_operand = {
        let mut c = Concept::new();
        c.set_concept_tag(209);
        c.set_operator_code(op::CCAND);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let source_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(210);
        c.set_operator_code(op::CCVARBINDIMPL);
        c.set_operand_count(2);
        c.add_operand_linker(binding_operand, false);
        c.add_operand_linker(trigger_operand, false);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let source_con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(source_con_des);
        d.concept = source_concept;
        d.dep_track_point = TrackPointId::NONE;
    }
    let mut cpd_val = ConceptProcessDescriptor::new();
    cpd_val.concept_des = source_con_des;
    cpd_val.dep_track_point = TrackPointId::NONE;
    let mut con_proc_des = env.ctx.process_context_mut().alloc_con_proc_desc(cpd_val);

    env.algo.apply_varbind_propagate_implication_rule(
        &mut root,
        &mut con_proc_des,
        false,
        &mut env.ctx,
    );

    assert!(
        env.algo.is_concept_in_reapply_queue_concept(
            source_con_des,
            trigger_operand,
            true,
            root,
            &mut env.ctx
        ),
        "missing implication trigger must install a reapply entry for the inverted trigger"
    );
}

#[test]
fn varbind_implication_initializes_binding_paths_when_all_triggers_present() {
    use super::super::model::op;
    use super::super::process::binding_hash::ConceptVariableBindingPathSetHash;
    use super::super::process::varbind::{VariableBindingPath, VariableBindingPathDescriptor};

    let mut env = build_env();
    let mut root = env.root;
    let binding_operand = {
        let mut c = Concept::new();
        c.set_concept_tag(211);
        c.set_operator_code(op::CCVARBINDTRIG);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let trigger_operand = {
        let mut c = Concept::new();
        c.set_concept_tag(212);
        c.set_operator_code(op::CCAND);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let source_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(213);
        c.set_operator_code(op::CCVARBINDIMPL);
        c.set_operand_count(2);
        c.add_operand_linker(binding_operand, false);
        c.add_operand_linker(trigger_operand, false);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let source_con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(source_con_des);
        d.concept = source_concept;
        d.dep_track_point = TrackPointId::NONE;
    }
    let mut cpd_val = ConceptProcessDescriptor::new();
    cpd_val.concept_des = source_con_des;
    cpd_val.dep_track_point = TrackPointId::NONE;
    let mut con_proc_des = env.ctx.process_context_mut().alloc_con_proc_desc(cpd_val);

    env.algo.add_concept_to_individual(
        trigger_operand,
        true,
        &mut root,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );
    let setup_queue = env
        .ctx
        .process_context_mut()
        .node_concept_processing_queue(root, false);
    while setup_queue.is_some()
        && env
            .ctx
            .process_context()
            .concept_proc_queue(setup_queue)
            .get_descriptor_count()
            > 0
    {
        ConceptProcessingQueue::take_next_concept_descriptor_process(
            setup_queue,
            env.ctx.process_context_mut(),
        );
    }

    let source_tag = env
        .ctx
        .ontology_arenas()
        .concept(source_concept)
        .get_concept_tag();
    let binding_tag = env
        .ctx
        .ontology_arenas()
        .concept(binding_operand)
        .get_concept_tag();
    let source_hash = env
        .ctx
        .process_context_mut()
        .node_concept_variable_binding_path_set_hash(root);
    let prev_set = ConceptVariableBindingPathSetHash::get_variable_binding_path_set(
        env.ctx.process_context_mut(),
        source_hash,
        source_tag,
        true,
    );

    let path = {
        let id = env
            .ctx
            .process_context_mut()
            .alloc_vbpath(VariableBindingPath::new());
        env.ctx
            .process_context_mut()
            .vbpath_mut(id)
            .init_variable_binding_path(80, Id::NONE);
        id
    };
    let mut d = VariableBindingPathDescriptor::new();
    d.init_variable_binding_path_descriptor(path, TrackPointId::NONE);
    let prev_des = env.ctx.process_context_mut().alloc_vbpath_des(d);
    env.ctx
        .process_context_mut()
        .vbpath_set_mut(prev_set)
        .get_variable_binding_path_map_mut()
        .entry_mut(80)
        .set_variable_binding_path_descriptor(prev_des);

    env.algo.apply_varbind_propagate_implication_rule(
        &mut root,
        &mut con_proc_des,
        false,
        &mut env.ctx,
    );

    let con_set = env
        .ctx
        .process_context_mut()
        .node_reapply_concept_label_set(root);
    let mut binding_con_des = Id::NONE;
    let mut binding_dep_track_point = Id::NONE;
    assert!(
        env.ctx
            .process_context()
            .label_set(con_set)
            .get_concept_descriptor_by_tag(
                binding_tag,
                &mut binding_con_des,
                &mut binding_dep_track_point
            ),
        "all triggers present must add the binding trigger concept"
    );

    let trigger_set = ConceptVariableBindingPathSetHash::get_variable_binding_path_set(
        env.ctx.process_context_mut(),
        source_hash,
        binding_tag,
        false,
    );
    let copied_des = env
        .ctx
        .process_context()
        .vbpath_set(trigger_set)
        .get_variable_binding_path_map()
        .value(80)
        .get_variable_binding_path_descriptor();
    assert!(copied_des.is_some());
    assert_ne!(
        copied_des, prev_des,
        "initial implication propagation must create a fresh descriptor"
    );
    assert_eq!(
        env.ctx
            .process_context()
            .vbpath_des(copied_des)
            .get_variable_binding_path(),
        path
    );
}

#[test]
fn varbind_implication_existing_binding_refreshes_and_drains_reapply() {
    use super::super::model::op;
    use super::super::process::binding_hash::ConceptVariableBindingPathSetHash;
    use super::super::process::varbind::{VariableBindingPath, VariableBindingPathDescriptor};

    let mut env = build_env();
    let mut root = env.root;
    let binding_operand = {
        let mut c = Concept::new();
        c.set_concept_tag(214);
        c.set_operator_code(op::CCVARBINDTRIG);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let trigger_operand = {
        let mut c = Concept::new();
        c.set_concept_tag(215);
        c.set_operator_code(op::CCAND);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let queued_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(216);
        c.set_operator_code(op::CCAND);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let source_concept = {
        let mut c = Concept::new();
        c.set_concept_tag(217);
        c.set_operator_code(op::CCVARBINDIMPL);
        c.set_operand_count(2);
        c.add_operand_linker(binding_operand, false);
        c.add_operand_linker(trigger_operand, false);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let source_con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(source_con_des);
        d.concept = source_concept;
        d.dep_track_point = TrackPointId::NONE;
    }
    let queued_con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(queued_con_des);
        d.concept = queued_concept;
        d.dep_track_point = TrackPointId::NONE;
    }
    let mut cpd_val = ConceptProcessDescriptor::new();
    cpd_val.concept_des = source_con_des;
    cpd_val.dep_track_point = TrackPointId::NONE;
    let mut con_proc_des = env.ctx.process_context_mut().alloc_con_proc_desc(cpd_val);

    env.algo.add_concept_to_individual(
        binding_operand,
        false,
        &mut root,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );
    env.algo.add_concept_to_individual(
        trigger_operand,
        true,
        &mut root,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );
    let setup_queue = env
        .ctx
        .process_context_mut()
        .node_concept_processing_queue(root, false);
    while setup_queue.is_some()
        && env
            .ctx
            .process_context()
            .concept_proc_queue(setup_queue)
            .get_descriptor_count()
            > 0
    {
        ConceptProcessingQueue::take_next_concept_descriptor_process(
            setup_queue,
            env.ctx.process_context_mut(),
        );
    }

    let source_tag = env
        .ctx
        .ontology_arenas()
        .concept(source_concept)
        .get_concept_tag();
    let binding_tag = env
        .ctx
        .ontology_arenas()
        .concept(binding_operand)
        .get_concept_tag();
    let source_hash = env
        .ctx
        .process_context_mut()
        .node_concept_variable_binding_path_set_hash(root);
    let prev_set = ConceptVariableBindingPathSetHash::get_variable_binding_path_set(
        env.ctx.process_context_mut(),
        source_hash,
        source_tag,
        true,
    );
    let trigger_set = ConceptVariableBindingPathSetHash::get_variable_binding_path_set(
        env.ctx.process_context_mut(),
        source_hash,
        binding_tag,
        true,
    );

    let mut seeded = Vec::new();
    for prop_id in [90, 100] {
        let path = {
            let id = env
                .ctx
                .process_context_mut()
                .alloc_vbpath(VariableBindingPath::new());
            env.ctx
                .process_context_mut()
                .vbpath_mut(id)
                .init_variable_binding_path(prop_id, Id::NONE);
            id
        };
        let mut d = VariableBindingPathDescriptor::new();
        d.init_variable_binding_path_descriptor(path, TrackPointId::NONE);
        let des = env.ctx.process_context_mut().alloc_vbpath_des(d);
        env.ctx
            .process_context_mut()
            .vbpath_set_mut(prev_set)
            .get_variable_binding_path_map_mut()
            .entry_mut(prop_id)
            .set_variable_binding_path_descriptor(des);
        seeded.push((prop_id, path, des));
    }
    let mut existing_d = VariableBindingPathDescriptor::new();
    existing_d.init_variable_binding_path_descriptor(seeded[0].1, TrackPointId::NONE);
    let existing_des = env.ctx.process_context_mut().alloc_vbpath_des(existing_d);
    env.ctx
        .process_context_mut()
        .vbpath_set_mut(trigger_set)
        .get_variable_binding_path_map_mut()
        .entry_mut(90)
        .set_variable_binding_path_descriptor(existing_des);

    env.algo.add_concept_to_reapply_queue_concept(
        queued_con_des,
        binding_operand,
        false,
        root,
        false,
        TrackPointId::NONE,
        &mut env.ctx,
    );

    env.algo.apply_varbind_propagate_implication_rule(
        &mut root,
        &mut con_proc_des,
        false,
        &mut env.ctx,
    );

    let map = env
        .ctx
        .process_context()
        .vbpath_set(trigger_set)
        .get_variable_binding_path_map();
    assert_eq!(
        map.value(90).get_variable_binding_path_descriptor(),
        existing_des,
        "fresh implication propagation must preserve existing path descriptors"
    );
    let fresh_des = map.value(100).get_variable_binding_path_descriptor();
    assert!(fresh_des.is_some());
    assert_ne!(fresh_des, seeded[1].2);
    assert_eq!(
        env.ctx
            .process_context()
            .vbpath_des(fresh_des)
            .get_variable_binding_path(),
        seeded[1].1
    );
    assert!(
        !env.algo.is_concept_in_reapply_queue_concept(
            queued_con_des,
            binding_operand,
            false,
            root,
            &mut env.ctx
        ),
        "existing binding trigger must drain the condensed reapply queue"
    );
    let queue = env
        .ctx
        .process_context_mut()
        .node_concept_processing_queue(root, false);
    assert!(
        env.ctx
            .process_context()
            .concept_proc_queue(queue)
            .get_descriptor_count()
            >= 1,
        "drained reapply descriptor must be added to the concept processing queue"
    );
    let next = ConceptProcessingQueue::take_next_concept_descriptor_process(
        queue,
        env.ctx.process_context_mut(),
    );
    assert_eq!(
        env.ctx
            .process_context()
            .con_proc_desc(next)
            .get_concept_descriptor(),
        queued_con_des
    );
}

#[test]
fn optimized_blocking_b2_role_reapply_rejects_missing_forall_operand() {
    use super::super::model::op;
    use super::super::model::role::Role;

    let mut env = build_env();
    env.algo.conf_signature_mirroring_blocking = true;
    env.algo.opt_signature_mirroring_blocking_in_blocking = true;
    let root = env.root;

    let role_r = {
        let mut r = Role::new();
        r.set_role_tag(74);
        env.ctx.ontology_arenas_mut().alloc_role(r)
    };
    let marker = {
        let mut c = Concept::new();
        c.set_concept_tag(178);
        c.set_operator_code(op::CCATOM);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let required_c = {
        let mut c = Concept::new();
        c.set_concept_tag(179);
        c.set_operator_code(op::CCATOM);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let all_r_c = {
        let mut c = Concept::new();
        c.set_concept_tag(278);
        c.set_operator_code(op::CCALL);
        c.set_role(role_r);
        c.add_operand_linker(required_c, false);
        c.set_operand_count(1);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };

    let w_node = build_role_successor(&mut env, root, role_r);
    let blocker = env
        .algo
        .create_new_individual(TrackPointId::NONE, false, &mut env.ctx);
    env.algo
        .ht_install_role_successor_edge(w_node, root, role_r, TrackPointId::NONE, &mut env.ctx);

    let mut w_node_mut = w_node;
    env.algo.add_concept_to_individual(
        marker,
        false,
        &mut w_node_mut,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );
    let mut blocker_mut = blocker;
    env.algo.add_concept_to_individual(
        marker,
        false,
        &mut blocker_mut,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );
    let mut root_mut = root;
    env.algo.add_concept_to_individual(
        marker,
        false,
        &mut root_mut,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );

    let all_con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(all_con_des);
        d.concept = all_r_c;
        d.dep_track_point = TrackPointId::NONE;
    }
    env.algo.add_concept_to_reapply_queue_role(
        all_con_des,
        role_r,
        blocker,
        true,
        TrackPointId::NONE,
        &mut env.ctx,
    );

    let mut block_alt_data = Id::NONE;
    assert!(
        !env.algo.is_label_concept_optimized_blocking(
            w_node,
            blocker,
            Id::NONE,
            false,
            &mut block_alt_data,
            &mut env.ctx,
        ),
        "B2 must reject the blocker when v lacks the operand required by blocker ∀R.C"
    );
}

#[test]
fn optimized_blocking_b3_b5_counts_blocker_role_successors() {
    use super::super::model::op;
    use super::super::model::role::Role;

    let mut env = build_env();
    let root = env.root;

    let role_r = {
        let mut r = Role::new();
        r.set_role_tag(75);
        env.ctx.ontology_arenas_mut().alloc_role(r)
    };
    let marker = {
        let mut c = Concept::new();
        c.set_concept_tag(181);
        c.set_operator_code(op::CCATOM);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let qualifier = {
        let mut c = Concept::new();
        c.set_concept_tag(182);
        c.set_operator_code(op::CCATOM);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let atmost_one_r_qualifier = {
        let mut c = Concept::new();
        c.set_concept_tag(282);
        c.set_operator_code(op::CCATMOST);
        c.set_role(role_r);
        c.set_parameter(1);
        c.add_operand_linker(qualifier, false);
        c.set_operand_count(1);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };

    let w_node = build_role_successor(&mut env, root, role_r);
    let blocker = env
        .algo
        .create_new_individual(TrackPointId::NONE, false, &mut env.ctx);
    env.algo
        .ht_install_role_successor_edge(w_node, root, role_r, TrackPointId::NONE, &mut env.ctx);

    let mut w_node_mut = w_node;
    env.algo.add_concept_to_individual(
        marker,
        false,
        &mut w_node_mut,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );
    let mut blocker_mut = blocker;
    env.algo.add_concept_to_individual(
        marker,
        false,
        &mut blocker_mut,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );
    let mut root_mut = root;
    env.algo.add_concept_to_individual(
        marker,
        false,
        &mut root_mut,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );

    let atmost_con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(atmost_con_des);
        d.concept = atmost_one_r_qualifier;
        d.dep_track_point = TrackPointId::NONE;
    }
    env.algo.add_concept_to_reapply_queue_role(
        atmost_con_des,
        role_r,
        blocker,
        true,
        TrackPointId::NONE,
        &mut env.ctx,
    );

    let blocker_succ = build_role_successor(&mut env, blocker, role_r);
    let mut blocker_succ_mut = blocker_succ;
    env.algo.add_concept_to_individual(
        qualifier,
        false,
        &mut blocker_succ_mut,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );

    let mut block_alt_data = Id::NONE;
    assert!(
        !env.algo.is_label_concept_optimized_blocking(
            w_node,
            blocker,
            Id::NONE,
            false,
            &mut block_alt_data,
            &mut env.ctx,
        ),
        "B3/B5 must reject when the blocker already has enough matching R-successors"
    );
}

#[test]
fn optimized_blocking_b4a_counts_insufficient_blocker_successors() {
    use super::super::model::op;
    use super::super::model::role::Role;

    let mut env = build_env();
    let root = env.root;

    let role_r = {
        let mut r = Role::new();
        r.set_role_tag(76);
        env.ctx.ontology_arenas_mut().alloc_role(r)
    };
    let marker = {
        let mut c = Concept::new();
        c.set_concept_tag(183);
        c.set_operator_code(op::CCATOM);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let qualifier = {
        let mut c = Concept::new();
        c.set_concept_tag(184);
        c.set_operator_code(op::CCATOM);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let atleast_two_r_qualifier = {
        let mut c = Concept::new();
        c.set_concept_tag(284);
        c.set_operator_code(op::CCATLEAST);
        c.set_role(role_r);
        c.set_parameter(2);
        c.add_operand_linker(qualifier, false);
        c.set_operand_count(1);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let atmost_two_r_qualifier = {
        let mut c = Concept::new();
        c.set_concept_tag(285);
        c.set_operator_code(op::CCATMOST);
        c.set_role(role_r);
        c.set_parameter(2);
        c.add_operand_linker(qualifier, false);
        c.set_operand_count(1);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };

    let w_node = build_role_successor(&mut env, root, role_r);
    let blocker = env
        .algo
        .create_new_individual(TrackPointId::NONE, false, &mut env.ctx);
    env.algo
        .ht_install_role_successor_edge(w_node, root, role_r, TrackPointId::NONE, &mut env.ctx);

    let mut w_node_mut = w_node;
    env.algo.add_concept_to_individual(
        marker,
        false,
        &mut w_node_mut,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );
    let mut blocker_mut = blocker;
    env.algo.add_concept_to_individual(
        marker,
        false,
        &mut blocker_mut,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );
    env.algo.add_concept_to_individual(
        atleast_two_r_qualifier,
        false,
        &mut blocker_mut,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );
    let mut root_mut = root;
    env.algo.add_concept_to_individual(
        marker,
        false,
        &mut root_mut,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );

    let atmost_con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let d = env.ctx.process_context_mut().con_desc_mut(atmost_con_des);
        d.concept = atmost_two_r_qualifier;
        d.dep_track_point = TrackPointId::NONE;
    }
    env.algo.add_concept_to_reapply_queue_role(
        atmost_con_des,
        role_r,
        blocker,
        true,
        TrackPointId::NONE,
        &mut env.ctx,
    );

    let blocker_succ = build_role_successor(&mut env, blocker, role_r);
    let mut blocker_succ_mut = blocker_succ;
    env.algo.add_concept_to_individual(
        qualifier,
        false,
        &mut blocker_succ_mut,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );

    let mut block_alt_data = Id::NONE;
    assert!(
        !env.algo.is_label_concept_optimized_blocking(
            w_node,
            blocker,
            Id::NONE,
            false,
            &mut block_alt_data,
            &mut env.ctx,
        ),
        "B4a must reject when the blocker has fewer matching R-successors than its >= restriction"
    );
}

/// REAL INFERENCE over the FULL drive loop: a root whose concept-processing queue
/// holds the conjunction `A ⊓ B`. After `run_completion_on` drains the queue and
/// fires the rule engine, the ⊓-rule (`apply_and_rule`) has materialised BOTH
/// operands A and B in the root's concept label set — a sound consequence,
/// produced with no new node created. This is the first inference the ported
/// Konclude completion engine derives by RUNNING its main loop (take-next →
/// individual_node_initializing → concept-queue drain → tableau_rule_choice →
/// apply_and_rule), not just at clash-initialization.
#[test]
fn conjunction_rule_fires_over_drive_loop() {
    use super::super::model::op;

    let mut env = build_env();

    // --- two atomic operand concepts A (tag 101) and B (tag 102). CCATOM ⇒ the
    //     dispatch `_` arm fires no rule, so they terminate the drain cleanly. ---
    let con_a = {
        let mut c = Concept::new();
        c.set_concept_tag(101);
        c.set_operator_code(op::CCATOM);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let con_b = {
        let mut c = Concept::new();
        c.set_concept_tag(102);
        c.set_operator_code(op::CCATOM);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    // --- the conjunction C = A ⊓ B (tag 200, operator CCAND, operands A, B) ---
    let con_and = {
        let mut c = Concept::new();
        c.set_concept_tag(200);
        c.set_operator_code(op::CCAND);
        c.add_operand_linker(con_a, false);
        c.add_operand_linker(con_b, false);
        c.set_operand_count(2);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };

    let root = env.root;

    // --- buildCompletionGraph seed (gap a): place the C=(A⊓B) descriptor directly
    //     on the root's concept-processing queue (the drive loop pops it). The
    //     `add_concept_preprocessed_to_processing_queue_skip` enqueue path is still
    //     W*-DEFER — it reads a hardcoded op-code 0, allocates `Id::NONE`, and the
    //     opaque jump-func table gates it off — so a real descriptor cannot yet be
    //     enqueued through `add_concept_to_individual`; the seed is placed directly,
    //     exactly as `concept_queue_insert_primitive` does. ---
    let queue = env
        .ctx
        .process_context_mut()
        .node_concept_processing_queue(root, true);
    let con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    env.ctx.process_context_mut().con_desc_mut(con_des).concept = con_and;
    let mut cpd_val = ConceptProcessDescriptor::new();
    cpd_val.concept_des = con_des;
    // getPriorityForConcept would assign this; seed it at the immediate level so
    // `continue_individual_processing`'s priority gate (>= IMMEDIATELY = 8, the level
    // the immediately-processing queue sets) admits it.
    cpd_val.priority = ConceptProcessPriority::new(8.0);
    let cpd = env.ctx.process_context_mut().alloc_con_proc_desc(cpd_val);
    ConceptProcessingQueue::insert_concept_process_descriptor(
        queue,
        cpd,
        env.ctx.process_context_mut(),
    );

    // --- seed the root onto the immediately-processing individual queue so
    //     take_next_process_individual (Probe 2, LIVE) returns it. ---
    let iq = env.ctx.get_individual_immediately_processing_queue(true);
    env.ctx
        .process_context_mut()
        .indi_unsorted_proc_queue_mut(iq)
        .insert_indiviudal_process_node(root);

    // --- RUN the completion main loop directly on the constructed context ---
    let consistent = env.algo.run_completion_on(&mut env.ctx);

    // VERDICT: consistent (no clash), and the ⊓-rule added A and B to the label set.
    assert!(consistent, "A ⊓ B is consistent (no clash expected)");
    assert!(
        !env.ctx.has_pending_signal(),
        "no clash/stop signal expected for a consistent conjunction"
    );

    let label_set = env
        .ctx
        .process_context_mut()
        .node_reapply_concept_label_set(root);
    let mut cd: ConDescId = Id::NONE;
    let mut dtp = TrackPointId::NONE;
    let pc = env.ctx.process_context();
    assert!(
        pc.label_set(label_set)
            .get_concept_descriptor_by_tag(101, &mut cd, &mut dtp),
        "the ⊓-rule must add operand A (tag 101) to the root concept label set"
    );
    assert!(
        pc.label_set(label_set)
            .get_concept_descriptor_by_tag(102, &mut cd, &mut dtp),
        "the ⊓-rule must add operand B (tag 102) to the root concept label set"
    );
}

/// DISJUNCTION BRANCHING (the ⊔-rule): a root whose concept-processing queue holds
/// the disjunction `A ⊔ B`. After `run_completion_on` drives the rule engine, the
/// ⊔-rule (`apply_or_rule` → `plan_or_processing` → `initialize_or_processing`)
/// created a branch point and EXPLORED the first alternative — adding A (and only A)
/// to the root label set — with no clash, so the completion graph is CONSISTENT with
/// one open branch. This is the first time the ported engine takes a non-deterministic
/// choice and runs through it.
#[test]
fn disjunction_branch_explored() {
    use super::super::model::op;

    let mut env = build_env();

    // atomic operands A (tag 101) and B (tag 102).
    let con_a = {
        let mut c = Concept::new();
        c.set_concept_tag(101);
        c.set_operator_code(op::CCATOM);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let con_b = {
        let mut c = Concept::new();
        c.set_concept_tag(102);
        c.set_operator_code(op::CCATOM);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    // the disjunction C = A ⊔ B (tag 201, operator CCOR, operands A, B).
    let con_or = {
        let mut c = Concept::new();
        c.set_concept_tag(201);
        c.set_operator_code(op::CCOR);
        c.add_operand_linker(con_a, false);
        c.add_operand_linker(con_b, false);
        c.set_operand_count(2);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };

    let root = env.root;

    // seed the (A⊔B) descriptor on the root concept-processing queue.
    let queue = env
        .ctx
        .process_context_mut()
        .node_concept_processing_queue(root, true);
    let con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    env.ctx.process_context_mut().con_desc_mut(con_des).concept = con_or;
    let mut cpd_val = ConceptProcessDescriptor::new();
    cpd_val.concept_des = con_des;
    cpd_val.priority = ConceptProcessPriority::new(8.0);
    let cpd = env.ctx.process_context_mut().alloc_con_proc_desc(cpd_val);
    ConceptProcessingQueue::insert_concept_process_descriptor(
        queue,
        cpd,
        env.ctx.process_context_mut(),
    );

    // seed the root onto the immediately-processing individual queue.
    let iq = env.ctx.get_individual_immediately_processing_queue(true);
    env.ctx
        .process_context_mut()
        .indi_unsorted_proc_queue_mut(iq)
        .insert_indiviudal_process_node(root);

    // RUN the completion main loop.
    let consistent = env.algo.run_completion_on(&mut env.ctx);

    // VERDICT: consistent, one branch open, the first disjunct A chosen.
    assert!(consistent, "A ⊔ B is consistent (first branch A explored)");
    assert!(
        !env.ctx.has_pending_signal(),
        "no clash expected for a satisfiable disjunction"
    );
    assert_eq!(
        env.algo.or_branch_stack.len(),
        1,
        "exactly one open disjunction branch point remains"
    );

    let label_set = env
        .ctx
        .process_context_mut()
        .node_reapply_concept_label_set(root);
    let mut cd: ConDescId = Id::NONE;
    let mut dtp = TrackPointId::NONE;
    let pc = env.ctx.process_context();
    assert!(
        pc.label_set(label_set)
            .get_concept_descriptor_by_tag(101, &mut cd, &mut dtp),
        "the ⊔-rule must add the first disjunct A (tag 101)"
    );
    let mut cd2: ConDescId = Id::NONE;
    let mut dtp2 = TrackPointId::NONE;
    assert!(
        !pc.label_set(label_set)
            .get_concept_descriptor_by_tag(102, &mut cd2, &mut dtp2),
        "only the first branch is explored — B (tag 102) is NOT added"
    );
}

/// DISJUNCTION BACKTRACKING (the ⊔-rule + chronological backjump): a root in the
/// context `(A ⊔ B) ⊓ ¬A ⊓ ¬B` — the label set already holds ¬A and ¬B and the
/// concept queue holds the disjunction `A ⊔ B`. The drive explores the first
/// disjunct A (clashes with ¬A), BACKTRACKS to the branch point and tries the second
/// disjunct B (clashes with ¬B); with no alternative left the clash propagates and
/// the completion graph is INCONSISTENT. This exercises the in-process branch
/// creation AND the chronological backtrack in `run_completion_on`.
#[test]
fn disjunction_all_branches_clash() {
    use super::super::model::op;

    let mut env = build_env();

    let con_a = {
        let mut c = Concept::new();
        c.set_concept_tag(101);
        c.set_operator_code(op::CCATOM);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let con_b = {
        let mut c = Concept::new();
        c.set_concept_tag(102);
        c.set_operator_code(op::CCATOM);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let con_or = {
        let mut c = Concept::new();
        c.set_concept_tag(201);
        c.set_operator_code(op::CCOR);
        c.add_operand_linker(con_a, false);
        c.add_operand_linker(con_b, false);
        c.set_operand_count(2);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };

    let mut root = env.root;

    // the ⊓ ¬A ⊓ ¬B context: pre-add ¬A and ¬B to the root label set. They do not
    // clash with each other (distinct concept tags).
    env.algo.add_concept_to_individual(
        con_a,
        true,
        &mut root,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );
    env.algo.add_concept_to_individual(
        con_b,
        true,
        &mut root,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );
    assert!(
        !env.ctx.has_pending_signal(),
        "¬A and ¬B must not clash with each other"
    );

    // seed the (A⊔B) descriptor on the root concept-processing queue.
    let queue = env
        .ctx
        .process_context_mut()
        .node_concept_processing_queue(root, true);
    let con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    env.ctx.process_context_mut().con_desc_mut(con_des).concept = con_or;
    let mut cpd_val = ConceptProcessDescriptor::new();
    cpd_val.concept_des = con_des;
    cpd_val.priority = ConceptProcessPriority::new(8.0);
    let cpd = env.ctx.process_context_mut().alloc_con_proc_desc(cpd_val);
    ConceptProcessingQueue::insert_concept_process_descriptor(
        queue,
        cpd,
        env.ctx.process_context_mut(),
    );

    // seed the root onto the immediately-processing individual queue.
    let iq = env.ctx.get_individual_immediately_processing_queue(true);
    env.ctx
        .process_context_mut()
        .indi_unsorted_proc_queue_mut(iq)
        .insert_indiviudal_process_node(root);

    // RUN: explore A → clash, backtrack, explore B → clash, propagate.
    let consistent = env.algo.run_completion_on(&mut env.ctx);

    // VERDICT: inconsistent — both branches clashed and were exhausted.
    assert!(
        !consistent,
        "(A ⊔ B) ⊓ ¬A ⊓ ¬B is INCONSISTENT (both disjuncts clash)"
    );
    assert!(
        env.ctx.has_pending_signal(),
        "a clash must be pending after both branches fail"
    );
    match env.ctx.pending_signal() {
        CalcSignal::Clash(_) => {}
        other => panic!("expected a Clash signal, got {:?}", other),
    }
    assert!(
        env.algo.or_branch_stack.is_empty(),
        "the exhausted disjunction branch point must be popped"
    );
}

/// REAL TBox UNFOLDING over the FULL drive loop: a GCI `A ⊑ B` (a real IMPL
/// `CConcept`) plus a root labelled `A`. The implication concept is enqueued the
/// NATURAL way — `add_concept_to_individual` reads its op-code (CCIMPL), sees it has
/// a tableau rule (`has_tableau_rule`), computes its priority (9 ≥ IMMEDIATELY = 8)
/// and pushes a real `CConceptProcessDescriptor`; the selftest no longer seeds the
/// concept queue directly. `run_completion_on` then drains the queue →
/// `apply_implication_rule`, whose trigger `¬A` is satisfied by the present positive
/// `A`, so the implied `B` is added to the root. After the run the root concept label
/// set contains `B` — the first consequence the engine derives by UNFOLDING a GCI.
///
/// `A ⊑ B` is the disjunction `¬A ⊔ B`: the IMPL concept's operand list is
/// `[B(implied), ¬A(trigger)]`; the rule waits for the trigger concept `A` with the
/// OPPOSITE polarity of the `¬A` linker (i.e. positive `A`).
#[test]
fn implication_unfolds_a_to_b() {
    use super::super::model::op;

    let mut env = build_env();

    let con_a = {
        let mut c = Concept::new();
        c.set_concept_tag(101);
        c.set_operator_code(op::CCATOM);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let con_b = {
        let mut c = Concept::new();
        c.set_concept_tag(102);
        c.set_operator_code(op::CCATOM);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    // the GCI  A ⊑ B  ==  ¬A ⊔ B : IMPL concept (tag 300), operands [B(implied), ¬A(trigger)].
    let con_impl = {
        let mut c = Concept::new();
        c.set_concept_tag(300);
        c.set_operator_code(op::CCIMPL);
        c.add_operand_linker(con_b, false); // implied head B
        c.add_operand_linker(con_a, true); // trigger ¬A
        c.set_operand_count(2);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };

    let mut root = env.root;

    // root labelled A (atomic ⇒ no tableau rule ⇒ lands in the label set, not enqueued).
    env.algo.add_concept_to_individual(
        con_a,
        false,
        &mut root,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );
    // add the implication concept — the NATURAL enqueue path pushes a real descriptor.
    env.algo.add_concept_to_individual(
        con_impl,
        false,
        &mut root,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );

    // seed the root onto the immediately-processing individual queue.
    let iq = env.ctx.get_individual_immediately_processing_queue(true);
    env.ctx
        .process_context_mut()
        .indi_unsorted_proc_queue_mut(iq)
        .insert_indiviudal_process_node(root);

    let consistent = env.algo.run_completion_on(&mut env.ctx);

    assert!(consistent, "A ⊑ B with A present is consistent (no clash)");
    assert!(!env.ctx.has_pending_signal(), "no clash/stop expected");

    let label_set = env
        .ctx
        .process_context_mut()
        .node_reapply_concept_label_set(root);
    let mut cd: ConDescId = Id::NONE;
    let mut dtp = TrackPointId::NONE;
    let pc = env.ctx.process_context();
    assert!(
        pc.label_set(label_set)
            .get_concept_descriptor_by_tag(102, &mut cd, &mut dtp),
        "the IMPLICATION rule must unfold A ⊑ B and add B (tag 102) to the root label set"
    );
}

/// CLASH through TBox unfolding: `A ⊑ B` and `A ⊑ ¬B` over a root labelled `A`. Both
/// implications are enqueued naturally and fire from the same trigger `A`; the first
/// adds `B`, the second adds `¬B`, and the label-set polarity compare raises a CLASH.
/// `run_completion_on` ends the drive with the inconsistent verdict.
#[test]
fn implication_unfold_clash() {
    use super::super::model::op;

    let mut env = build_env();

    let con_a = {
        let mut c = Concept::new();
        c.set_concept_tag(101);
        c.set_operator_code(op::CCATOM);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let con_b = {
        let mut c = Concept::new();
        c.set_concept_tag(102);
        c.set_operator_code(op::CCATOM);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    // A ⊑ B : operands [B(implied), ¬A(trigger)].
    let con_impl_b = {
        let mut c = Concept::new();
        c.set_concept_tag(301);
        c.set_operator_code(op::CCIMPL);
        c.add_operand_linker(con_b, false);
        c.add_operand_linker(con_a, true);
        c.set_operand_count(2);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    // A ⊑ ¬B : operands [¬B(implied), ¬A(trigger)].
    let con_impl_not_b = {
        let mut c = Concept::new();
        c.set_concept_tag(302);
        c.set_operator_code(op::CCIMPL);
        c.add_operand_linker(con_b, true);
        c.add_operand_linker(con_a, true);
        c.set_operand_count(2);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };

    let mut root = env.root;

    env.algo.add_concept_to_individual(
        con_a,
        false,
        &mut root,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );
    env.algo.add_concept_to_individual(
        con_impl_b,
        false,
        &mut root,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );
    env.algo.add_concept_to_individual(
        con_impl_not_b,
        false,
        &mut root,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );

    let iq = env.ctx.get_individual_immediately_processing_queue(true);
    env.ctx
        .process_context_mut()
        .indi_unsorted_proc_queue_mut(iq)
        .insert_indiviudal_process_node(root);

    let consistent = env.algo.run_completion_on(&mut env.ctx);

    assert!(
        !consistent,
        "A ⊑ B and A ⊑ ¬B over A must derive B and ¬B ⇒ CLASH (inconsistent)"
    );
    assert!(
        env.ctx.has_pending_signal(),
        "the unfolded B / ¬B contradiction must raise a clash signal"
    );
    match env.ctx.pending_signal() {
        CalcSignal::Clash(_) => {}
        other => panic!("expected a Clash signal, got {:?}", other),
    }
}

// ===========================================================================
// W9-W11 follow-on: the ∃/∀ EDGE subsystem — the rules that make this a
// hypertableau. ∃R.C builds a fresh successor node + an R link-edge and labels
// it C; ∀R.C re-propagates C onto the predecessor's R-successors (existing ones
// via the ALL rule, and a later-created one via the edge-triggered ∀ in the
// SOME rule). Drives end-to-end through `run_completion_on`.
// ===========================================================================

/// Seed a concept-process descriptor for `concept` on `root`'s concept-processing
/// queue at the immediately-processing priority (8). SOME's own priority is 4
/// (the deterministic level); the harness seeds at the immediate level to drive
/// the rule directly, exactly as the conjunction / disjunction selftests do.
fn seed_concept_on_queue(env: &mut SelfTestEnv, root: NodeId, concept: ConceptId) {
    let queue = env
        .ctx
        .process_context_mut()
        .node_concept_processing_queue(root, true);
    let con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    env.ctx.process_context_mut().con_desc_mut(con_des).concept = concept;
    let mut cpd_val = ConceptProcessDescriptor::new();
    cpd_val.concept_des = con_des;
    cpd_val.priority = ConceptProcessPriority::new(8.0);
    let cpd = env.ctx.process_context_mut().alloc_con_proc_desc(cpd_val);
    ConceptProcessingQueue::insert_concept_process_descriptor(
        queue,
        cpd,
        env.ctx.process_context_mut(),
    );
}

/// Seed `root` onto the immediately-processing individual queue (Probe 2).
fn seed_root_immediate(env: &mut SelfTestEnv, root: NodeId) {
    let iq = env.ctx.get_individual_immediately_processing_queue(true);
    env.ctx
        .process_context_mut()
        .indi_unsorted_proc_queue_mut(iq)
        .insert_indiviudal_process_node(root);
}

/// The first R-successor node of `node` (resolved through the node's successor-role
/// hash + the node vector), or panic if none.
fn first_role_successor(env: &SelfTestEnv, node: NodeId) -> NodeId {
    let mut it = env.ctx.process_context().node_successor_iterator(node);
    assert!(it.has_next(), "expected a role successor but found none");
    let succ_id = it.next_individual_id(true);
    let succ = env
        .ctx
        .processing_data_box()
        .individual_process_node_vector()
        .get_data(succ_id);
    assert!(
        succ.is_some(),
        "the successor must be registered in the node vector"
    );
    succ
}

/// Optional variant of `first_role_successor`, used when the absence of a
/// generated successor is itself the assertion.
fn first_role_successor_optional(env: &SelfTestEnv, node: NodeId) -> Option<NodeId> {
    let mut it = env.ctx.process_context().node_successor_iterator(node);
    if !it.has_next() {
        return None;
    }
    let succ_id = it.next_individual_id(true);
    let succ = env
        .ctx
        .processing_data_box()
        .individual_process_node_vector()
        .get_data(succ_id);
    assert!(
        succ.is_some(),
        "a successor edge must resolve through the node vector"
    );
    Some(succ)
}

/// Does `node`'s concept label set contain the concept with tag `tag`?
fn label_set_has_tag(env: &mut SelfTestEnv, node: NodeId, tag: i64) -> bool {
    let ls = env
        .ctx
        .process_context_mut()
        .node_reapply_concept_label_set(node);
    let mut cd: ConDescId = Id::NONE;
    let mut dtp = TrackPointId::NONE;
    env.ctx
        .process_context()
        .label_set(ls)
        .get_concept_descriptor_by_tag(tag, &mut cd, &mut dtp)
}

/// ∃R.C over the drive loop: a root with `∃R.C` on its concept queue. After the
/// run there is an R-successor node carrying C, and the graph is CONSISTENT.
#[test]
fn exists_creates_successor() {
    use super::super::model::op;
    use super::super::model::role::Role;

    let mut env = build_env();
    let role_r = env.ctx.ontology_arenas_mut().alloc_role(Role::new());
    let con_c = {
        let mut c = Concept::new();
        c.set_concept_tag(150);
        c.set_operator_code(op::CCATOM);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    // ∃R.C : CCSOME, role R, operand list [C].
    let some_rc = {
        let mut c = Concept::new();
        c.set_concept_tag(250);
        c.set_operator_code(op::CCSOME);
        c.set_role(role_r);
        c.add_operand_linker(con_c, false);
        c.set_operand_count(1);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };

    let root = env.root;
    seed_concept_on_queue(&mut env, root, some_rc);
    seed_root_immediate(&mut env, root);

    let consistent = env.algo.run_completion_on(&mut env.ctx);

    assert!(consistent, "∃R.C is consistent");
    assert!(!env.ctx.has_pending_signal(), "no clash expected for ∃R.C");

    let succ = first_role_successor(&env, root);
    assert!(
        label_set_has_tag(&mut env, succ, 150),
        "the ∃-rule must label the new successor with the qualifier C (tag 150)"
    );
}

/// `∃R.D ⊓ ∀R.C` over the drive loop: the ∀ restriction must reach the
/// ∃-generated successor. After the run the R-successor carries BOTH D (from ∃)
/// and C (from ∀ propagation), and the graph is CONSISTENT.
#[test]
fn all_propagates_to_successor() {
    use super::super::model::op;
    use super::super::model::role::Role;

    let mut env = build_env();
    let role_r = env.ctx.ontology_arenas_mut().alloc_role(Role::new());
    let con_d = {
        let mut c = Concept::new();
        c.set_concept_tag(151);
        c.set_operator_code(op::CCATOM);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let con_c = {
        let mut c = Concept::new();
        c.set_concept_tag(152);
        c.set_operator_code(op::CCATOM);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let some_rd = {
        let mut c = Concept::new();
        c.set_concept_tag(251);
        c.set_operator_code(op::CCSOME);
        c.set_role(role_r);
        c.add_operand_linker(con_d, false);
        c.set_operand_count(1);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    // ∀R.C : CCALL, role R, operand list [C].
    let all_rc = {
        let mut c = Concept::new();
        c.set_concept_tag(252);
        c.set_operator_code(op::CCALL);
        c.set_role(role_r);
        c.add_operand_linker(con_c, false);
        c.set_operand_count(1);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };

    let mut root = env.root;
    // ∀R.C added the natural way → into the label set (so the ∃-rule's edge-triggered
    // ∀ re-application finds it) AND onto the queue at priority 12 (≥ immediate).
    env.algo.add_concept_to_individual(
        all_rc,
        false,
        &mut root,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );
    // ∃R.D seeded on the concept queue at the immediate priority.
    seed_concept_on_queue(&mut env, root, some_rd);
    seed_root_immediate(&mut env, root);

    let consistent = env.algo.run_completion_on(&mut env.ctx);

    assert!(consistent, "∃R.D ⊓ ∀R.C is consistent");
    assert!(!env.ctx.has_pending_signal(), "no clash expected");

    let succ = first_role_successor(&env, root);
    assert!(
        label_set_has_tag(&mut env, succ, 151),
        "the successor must carry D (tag 151) from ∃R.D"
    );
    assert!(
        label_set_has_tag(&mut env, succ, 152),
        "the ∀-restriction must propagate C (tag 152) onto the R-successor"
    );
}

/// `∃R.C ⊓ ∀R.¬C` over the drive loop: the ∃-successor gets C (from ∃) and ¬C
/// (from the ∀ propagation), so the successor's label-set polarity compare raises a
/// CLASH and the graph is INCONSISTENT.
#[test]
fn exists_all_clash() {
    use super::super::model::op;
    use super::super::model::role::Role;

    let mut env = build_env();
    let role_r = env.ctx.ontology_arenas_mut().alloc_role(Role::new());
    let con_c = {
        let mut c = Concept::new();
        c.set_concept_tag(153);
        c.set_operator_code(op::CCATOM);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let some_rc = {
        let mut c = Concept::new();
        c.set_concept_tag(253);
        c.set_operator_code(op::CCSOME);
        c.set_role(role_r);
        c.add_operand_linker(con_c, false);
        c.set_operand_count(1);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    // ∀R.¬C : CCALL, role R, operand list [¬C].
    let all_not_c = {
        let mut c = Concept::new();
        c.set_concept_tag(254);
        c.set_operator_code(op::CCALL);
        c.set_role(role_r);
        c.add_operand_linker(con_c, true);
        c.set_operand_count(1);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };

    let mut root = env.root;
    env.algo.add_concept_to_individual(
        all_not_c,
        false,
        &mut root,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );
    seed_concept_on_queue(&mut env, root, some_rc);
    seed_root_immediate(&mut env, root);

    let consistent = env.algo.run_completion_on(&mut env.ctx);

    assert!(
        !consistent,
        "∃R.C ⊓ ∀R.¬C is INCONSISTENT (successor gets C and ¬C)"
    );
    assert!(
        env.ctx.has_pending_signal(),
        "the C / ¬C contradiction on the successor must raise a clash"
    );
    match env.ctx.pending_signal() {
        CalcSignal::Clash(_) => {}
        other => panic!("expected a Clash signal, got {:?}", other),
    }
}

/// NESTED ∃ GROWS over the drive loop (W16-successor-drain): a root with
/// `∃R.(∃R.D)` on its concept queue. The ∃-rule builds the first successor `n1`
/// labelled `∃R.D`; because `n1` is now routed onto the DEPTH processing queue,
/// `take_next_process_individual` returns it with `min = DETERMINISTIC (4)`, so its
/// own `∃R.D` (priority 4) DRAINS and builds the SECOND hop `n2` labelled `D`. After
/// the run there are two successor hops root --R--> n1 --R--> n2, n2 carries D, and
/// the graph is CONSISTENT. This is the multi-node growth the immediate-queue routing
/// (min = 8) silently blocked.
#[test]
fn nested_exists_grows() {
    use super::super::model::op;
    use super::super::model::role::Role;

    let mut env = build_env();
    let role_r = env.ctx.ontology_arenas_mut().alloc_role(Role::new());
    let con_d = {
        let mut c = Concept::new();
        c.set_concept_tag(170);
        c.set_operator_code(op::CCATOM);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    // ∃R.D : CCSOME, role R, operand [D].
    let some_rd = {
        let mut c = Concept::new();
        c.set_concept_tag(270);
        c.set_operator_code(op::CCSOME);
        c.set_role(role_r);
        c.add_operand_linker(con_d, false);
        c.set_operand_count(1);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    // ∃R.(∃R.D) : CCSOME, role R, operand [∃R.D].
    let some_r_some_rd = {
        let mut c = Concept::new();
        c.set_concept_tag(271);
        c.set_operator_code(op::CCSOME);
        c.set_role(role_r);
        c.add_operand_linker(some_rd, false);
        c.set_operand_count(1);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };

    let root = env.root;
    seed_concept_on_queue(&mut env, root, some_r_some_rd);
    seed_root_immediate(&mut env, root);

    let consistent = env.algo.run_completion_on(&mut env.ctx);
    assert!(consistent, "∃R.(∃R.D) is consistent");
    assert!(
        !env.ctx.has_pending_signal(),
        "no clash expected for ∃R.(∃R.D)"
    );

    // first hop: root --R--> n1.
    let n1 = first_role_successor(&env, root);
    // second hop: n1 --R--> n2 — exists only if n1's own ∃R.D drained.
    let n2 = first_role_successor(&env, n1);
    assert_ne!(n1, n2, "the second hop must be a distinct fresh successor");
    assert!(
        label_set_has_tag(&mut env, n2, 170),
        "the nested ∃ must grow a SECOND successor n2 labelled D (tag 170)"
    );
}

/// CYCLIC TBox BLOCKING: `A ⊑ ∃R.A` should terminate by ancestor blocking, not by
/// generating successors until the drive-loop hard stop. The full global-TBox
/// injection path is still deferred in `initial_node_initialize`, so this test
/// carries the same implication on each generated successor as part of the ∃
/// payload. That models the per-node TBox label the full initializer will add,
/// while still driving the real implication, ∃, successor queue, and blocking call
/// path end-to-end.
#[test]
fn cyclic_tbox_exists_blocks() {
    use super::super::model::op;
    use super::super::model::role::Role;

    let mut env = build_env();
    env.algo.conf_ancestor_blocking_search = true;
    env.algo.conf_sub_set_blocking = true;

    let role_r = env.ctx.ontology_arenas_mut().alloc_role(Role::new());
    let con_a = {
        let mut c = Concept::new();
        c.set_concept_tag(180);
        c.set_operator_code(op::CCATOM);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let con_impl = env.ctx.ontology_arenas_mut().alloc_concept({
        let mut c = Concept::new();
        c.set_concept_tag(280);
        c
    });
    let some_ra = env.ctx.ontology_arenas_mut().alloc_concept({
        let mut c = Concept::new();
        c.set_concept_tag(281);
        c
    });
    {
        let c = env.ctx.ontology_arenas_mut().concept_mut(some_ra);
        c.set_operator_code(op::CCSOME);
        c.set_role(role_r);
        c.add_operand_linker(con_a, false);
        c.add_operand_linker(con_impl, false);
        c.set_operand_count(2);
    }
    {
        let c = env.ctx.ontology_arenas_mut().concept_mut(con_impl);
        c.set_operator_code(op::CCIMPL);
        c.add_operand_linker(some_ra, false);
        c.add_operand_linker(con_a, true);
        c.set_operand_count(2);
    }

    let mut root = env.root;
    let top = env.ctx.processing_data_box().ontology_top_concept();
    env.algo.add_concept_to_individual(
        top,
        false,
        &mut root,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );
    env.algo.add_concept_to_individual(
        con_a,
        false,
        &mut root,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );
    env.algo.add_concept_to_individual(
        con_impl,
        false,
        &mut root,
        TrackPointId::NONE,
        false,
        true,
        &mut env.ctx,
    );
    seed_root_immediate(&mut env, root);

    let consistent = env.algo.run_completion_on(&mut env.ctx);
    assert!(
        consistent,
        "cyclic A ⊑ ∃R.A must be CONSISTENT by blocking, not stopped"
    );
    assert!(
        !env.ctx.has_pending_signal(),
        "blocking should terminate without a clash or stop signal"
    );
    assert!(
        label_set_has_tag(&mut env, root, 281),
        "the implication A ⊑ ∃R.A must add the existential to the root before blocking is tested"
    );

    let n1 = first_role_successor(&env, root);
    assert!(
        first_role_successor_optional(&env, n1).is_none(),
        "a blocked successor must not fire ∃R.A again"
    );
    assert!(
        env.ctx
            .process_context()
            .node(n1)
            .has_partial_processing_restriction_flags(IndividualProcessNode::PRF_DIRECTBLOCKED),
        "the repeated A / TBox successor must be direct-blocked by an ancestor"
    );
}

/// NESTED ∃ CLASH at depth 2 (W16-successor-drain): a root with `∃R.(∃R.(D ⊓ ¬D))`.
/// The drive grows root --R--> n1 --R--> n2, and the innermost qualifier `D ⊓ ¬D` on
/// `n2` unfolds (the ⊓-rule) to `D` and `¬D`, whose polarity compare raises a CLASH at
/// depth 2 ⇒ the graph is INCONSISTENT. Proves the clash channel reaches a node two
/// hops deep — only possible if successors actually drain.
#[test]
fn nested_exists_clash() {
    use super::super::model::op;
    use super::super::model::role::Role;

    let mut env = build_env();
    let role_r = env.ctx.ontology_arenas_mut().alloc_role(Role::new());
    let con_d = {
        let mut c = Concept::new();
        c.set_concept_tag(171);
        c.set_operator_code(op::CCATOM);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    // D ⊓ ¬D : CCAND, operands [D(false), D(true)].
    let d_and_not_d = {
        let mut c = Concept::new();
        c.set_concept_tag(272);
        c.set_operator_code(op::CCAND);
        c.add_operand_linker(con_d, false);
        c.add_operand_linker(con_d, true);
        c.set_operand_count(2);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    // ∃R.(D ⊓ ¬D) : CCSOME, role R, operand [D ⊓ ¬D].
    let some_r_clash = {
        let mut c = Concept::new();
        c.set_concept_tag(273);
        c.set_operator_code(op::CCSOME);
        c.set_role(role_r);
        c.add_operand_linker(d_and_not_d, false);
        c.set_operand_count(1);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    // ∃R.(∃R.(D ⊓ ¬D)) : CCSOME, role R, operand [∃R.(D ⊓ ¬D)].
    let some_r_some_r_clash = {
        let mut c = Concept::new();
        c.set_concept_tag(274);
        c.set_operator_code(op::CCSOME);
        c.set_role(role_r);
        c.add_operand_linker(some_r_clash, false);
        c.set_operand_count(1);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };

    let root = env.root;
    seed_concept_on_queue(&mut env, root, some_r_some_r_clash);
    seed_root_immediate(&mut env, root);

    let consistent = env.algo.run_completion_on(&mut env.ctx);
    assert!(
        !consistent,
        "∃R.(∃R.(D ⊓ ¬D)) is INCONSISTENT — the depth-2 successor gets D and ¬D"
    );
    assert!(
        env.ctx.has_pending_signal(),
        "the depth-2 D / ¬D contradiction must raise a clash"
    );
    match env.ctx.pending_signal() {
        CalcSignal::Clash(_) => {}
        other => panic!("expected a Clash signal, got {:?}", other),
    }
}

// ===========================================================================
// W14-number: the SHIQ qualified-cardinality core (≥n R.C / ≤n R.C). ≥n builds
// n fresh PAIRWISE-DISTINCT successors each labelled C; ≤n merges or, when the
// successors are forced distinct, CLASHES. Drives end-to-end through
// `run_completion_on`.
// ===========================================================================

/// All distinct `role`-successor nodes of `node` (via the algorithm's live
/// role-successor link iterator).
fn role_successors(
    env: &SelfTestEnv,
    node: NodeId,
    role: super::super::model::RoleId,
) -> Vec<NodeId> {
    let mut out: Vec<NodeId> = Vec::new();
    for (_link, succ) in env.algo.ht_role_successor_links(node, role, &env.ctx) {
        if !out.contains(&succ) {
            out.push(succ);
        }
    }
    out
}

/// `≥2 R.C` over the drive loop: after the run there are exactly TWO R-successor
/// nodes, each labelled C, pairwise DISTINCT, and the graph is CONSISTENT.
#[test]
fn at_least_creates_n_successors() {
    use super::super::model::op;
    use super::super::model::role::Role;

    let mut env = build_env();
    let role_r = env.ctx.ontology_arenas_mut().alloc_role(Role::new());
    let con_c = {
        let mut c = Concept::new();
        c.set_concept_tag(160);
        c.set_operator_code(op::CCATOM);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    // ≥2 R.C : CCATLEAST, role R, parameter 2, operand list [C].
    let atleast_2_rc = {
        let mut c = Concept::new();
        c.set_concept_tag(260);
        c.set_operator_code(op::CCATLEAST);
        c.set_role(role_r);
        c.set_parameter(2);
        c.add_operand_linker(con_c, false);
        c.set_operand_count(1);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };

    let root = env.root;
    seed_concept_on_queue(&mut env, root, atleast_2_rc);
    seed_root_immediate(&mut env, root);

    let consistent = env.algo.run_completion_on(&mut env.ctx);

    assert!(consistent, "≥2 R.C is consistent");
    assert!(
        !env.ctx.has_pending_signal(),
        "no clash expected for ≥2 R.C"
    );

    let succs = role_successors(&env, root, role_r);
    assert_eq!(
        succs.len(),
        2,
        "the ≥2-rule must create exactly two R-successors (got {})",
        succs.len()
    );
    for &s in &succs {
        assert!(
            label_set_has_tag(&mut env, s, 160),
            "each ≥n successor must carry the qualifier C (tag 160)"
        );
    }
    assert!(
        !env.algo
            .ht_individuals_mergeable(succs[0], succs[1], &env.ctx),
        "the two ≥n successors must be pairwise distinct (a distinct-edge links them)"
    );
}

/// `≥2 R.C ⊓ ≤1 R.⊤` over the drive loop. ≥2 forces two DISTINCT R-successors;
/// the unqualified ≤1 (functional) then sees two distinct R-successors over the
/// bound and they cannot merge ⇒ CLASH. (The faithful Konclude outcome: forced
/// distinct successors over an at-most bound are inconsistent, not merged.)
#[test]
fn at_most_merges_or_clashes() {
    use super::super::model::op;
    use super::super::model::role::Role;

    let mut env = build_env();
    let role_r = env.ctx.ontology_arenas_mut().alloc_role(Role::new());
    let con_c = {
        let mut c = Concept::new();
        c.set_concept_tag(161);
        c.set_operator_code(op::CCATOM);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let atleast_2_rc = {
        let mut c = Concept::new();
        c.set_concept_tag(261);
        c.set_operator_code(op::CCATLEAST);
        c.set_role(role_r);
        c.set_parameter(2);
        c.add_operand_linker(con_c, false);
        c.set_operand_count(1);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    // ≤1 R.⊤ : CCATMOST, role R, parameter 1, NO operands (unqualified / functional).
    let atmost_1_top = {
        let mut c = Concept::new();
        c.set_concept_tag(262);
        c.set_operator_code(op::CCATMOST);
        c.set_role(role_r);
        c.set_parameter(1);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };

    let root = env.root;

    // run 1: ≥2 R.C creates the two distinct successors.
    seed_concept_on_queue(&mut env, root, atleast_2_rc);
    seed_root_immediate(&mut env, root);
    let consistent1 = env.algo.run_completion_on(&mut env.ctx);
    assert!(consistent1, "≥2 R.C alone is consistent");
    assert_eq!(
        role_successors(&env, root, role_r).len(),
        2,
        "two successors after ≥2"
    );

    // run 2: ≤1 R.⊤ now sees two distinct R-successors over the bound ⇒ CLASH.
    seed_concept_on_queue(&mut env, root, atmost_1_top);
    seed_root_immediate(&mut env, root);
    let consistent2 = env.algo.run_completion_on(&mut env.ctx);

    assert!(
        !consistent2,
        "≥2 R.C ⊓ ≤1 R.⊤ is INCONSISTENT (two forced-distinct successors over the at-most bound)"
    );
    assert!(
        env.ctx.has_pending_signal(),
        "the at-most violation must raise a clash"
    );
    match env.ctx.pending_signal() {
        CalcSignal::Clash(_) => {}
        other => panic!("expected a Clash signal, got {:?}", other),
    }
}

/// `≥2 R.C ⊓ ≤1 R.C` over the drive loop: the two distinct R-successors both carry
/// C, so the QUALIFIED ≤1 R.C sees them over the bound and — being pairwise distinct
/// — raises a CLASH ⇒ INCONSISTENT.
#[test]
fn cardinality_clash() {
    use super::super::model::op;
    use super::super::model::role::Role;

    let mut env = build_env();
    let role_r = env.ctx.ontology_arenas_mut().alloc_role(Role::new());
    let con_c = {
        let mut c = Concept::new();
        c.set_concept_tag(162);
        c.set_operator_code(op::CCATOM);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let atleast_2_rc = {
        let mut c = Concept::new();
        c.set_concept_tag(263);
        c.set_operator_code(op::CCATLEAST);
        c.set_role(role_r);
        c.set_parameter(2);
        c.add_operand_linker(con_c, false);
        c.set_operand_count(1);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    // ≤1 R.C : CCATMOST, role R, parameter 1, operand list [C] (qualified).
    let atmost_1_rc = {
        let mut c = Concept::new();
        c.set_concept_tag(264);
        c.set_operator_code(op::CCATMOST);
        c.set_role(role_r);
        c.set_parameter(1);
        c.add_operand_linker(con_c, false);
        c.set_operand_count(1);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };

    let root = env.root;

    seed_concept_on_queue(&mut env, root, atleast_2_rc);
    seed_root_immediate(&mut env, root);
    let consistent1 = env.algo.run_completion_on(&mut env.ctx);
    assert!(consistent1, "≥2 R.C alone is consistent");
    assert_eq!(
        role_successors(&env, root, role_r).len(),
        2,
        "two successors after ≥2"
    );

    seed_concept_on_queue(&mut env, root, atmost_1_rc);
    seed_root_immediate(&mut env, root);
    let consistent2 = env.algo.run_completion_on(&mut env.ctx);

    assert!(
        !consistent2,
        "≥2 R.C ⊓ ≤1 R.C with the two successors distinct is INCONSISTENT"
    );
    assert!(
        env.ctx.has_pending_signal(),
        "the qualified at-most violation must clash"
    );
    match env.ctx.pending_signal() {
        CalcSignal::Clash(_) => {}
        other => panic!("expected a Clash signal, got {:?}", other),
    }
}

// ===========================================================================
// At-most RESUME (`KM_HT_ATMOST_REST` / `conf_atmost_rest`): the
// `branchingMergingProcRest` machinery must reproduce the legacy outcomes
// (same clash/consistency verdicts) while classifying each link only once
// and resuming across re-fires. Same scenarios as the block above, plus the
// reapply-driven resume itself.
// ===========================================================================

/// `≥2 R.C ⊓ ≤1 R.⊤` under the rest machinery: the two forced-distinct
/// successors trip the DISTINCT-CLIQUE initialization clash (cpp 15988–16015)
/// — inconsistent, same verdict as the legacy spine.
#[test]
fn atmost_rest_functional_distinct_clash() {
    use super::super::model::op;
    use super::super::model::role::Role;

    let mut env = build_env();
    env.algo.conf_atmost_rest = true;
    let role_r = env.ctx.ontology_arenas_mut().alloc_role(Role::new());
    let con_c = {
        let mut c = Concept::new();
        c.set_concept_tag(1650);
        c.set_operator_code(op::CCATOM);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let atleast_2_rc = {
        let mut c = Concept::new();
        c.set_concept_tag(2650);
        c.set_operator_code(op::CCATLEAST);
        c.set_role(role_r);
        c.set_parameter(2);
        c.add_operand_linker(con_c, false);
        c.set_operand_count(1);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let atmost_1_top = {
        let mut c = Concept::new();
        c.set_concept_tag(2651);
        c.set_operator_code(op::CCATMOST);
        c.set_role(role_r);
        c.set_parameter(1);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };

    let root = env.root;
    seed_concept_on_queue(&mut env, root, atleast_2_rc);
    seed_root_immediate(&mut env, root);
    assert!(env.algo.run_completion_on(&mut env.ctx), "≥2 R.C alone is consistent");

    seed_concept_on_queue(&mut env, root, atmost_1_top);
    seed_root_immediate(&mut env, root);
    let consistent = env.algo.run_completion_on(&mut env.ctx);
    assert!(
        !consistent,
        "rest path: two forced-distinct successors over ≤1 must be INCONSISTENT"
    );
    match env.ctx.pending_signal() {
        CalcSignal::Clash(_) => {}
        other => panic!("expected a Clash signal, got {:?}", other),
    }
}

/// `≥2 R.C ⊓ ≤1 R.C` under the rest machinery — the QUALIFIED variant of the
/// distinct clash. Same verdict as the legacy `cardinality_clash`.
#[test]
fn atmost_rest_qualified_distinct_clash() {
    use super::super::model::op;
    use super::super::model::role::Role;

    let mut env = build_env();
    env.algo.conf_atmost_rest = true;
    let role_r = env.ctx.ontology_arenas_mut().alloc_role(Role::new());
    let con_c = {
        let mut c = Concept::new();
        c.set_concept_tag(1651);
        c.set_operator_code(op::CCATOM);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let atleast_2_rc = {
        let mut c = Concept::new();
        c.set_concept_tag(2652);
        c.set_operator_code(op::CCATLEAST);
        c.set_role(role_r);
        c.set_parameter(2);
        c.add_operand_linker(con_c, false);
        c.set_operand_count(1);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let atmost_1_rc = {
        let mut c = Concept::new();
        c.set_concept_tag(2653);
        c.set_operator_code(op::CCATMOST);
        c.set_role(role_r);
        c.set_parameter(1);
        c.add_operand_linker(con_c, false);
        c.set_operand_count(1);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };

    let root = env.root;
    seed_concept_on_queue(&mut env, root, atleast_2_rc);
    seed_root_immediate(&mut env, root);
    assert!(env.algo.run_completion_on(&mut env.ctx), "≥2 R.C alone is consistent");

    seed_concept_on_queue(&mut env, root, atmost_1_rc);
    seed_root_immediate(&mut env, root);
    let consistent = env.algo.run_completion_on(&mut env.ctx);
    assert!(
        !consistent,
        "rest path: qualified ≤1 R.C over two distinct C-successors must be INCONSISTENT"
    );
    match env.ctx.pending_signal() {
        CalcSignal::Clash(_) => {}
        other => panic!("expected a Clash signal, got {:?}", other),
    }
}

/// The resume itself: `∃R.C`, then `≤1 R.⊤` (fires below the bound, arms the
/// rest-carrying static reapply), THEN `∃R.D` adds a second — mergeable —
/// successor. The reapply must re-fire the ≤1 with the persisted rest (only
/// the NEW link is classified) and merge the two successors: consistent, ONE
/// live R-successor carrying both C and D.
#[test]
fn atmost_rest_reapply_resumes_and_merges() {
    use super::super::model::op;
    use super::super::model::role::Role;

    let mut env = build_env();
    env.algo.conf_atmost_rest = true;
    let role_r = env.ctx.ontology_arenas_mut().alloc_role(Role::new());
    let con_c = {
        let mut c = Concept::new();
        c.set_concept_tag(1652);
        c.set_operator_code(op::CCATOM);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let con_d = {
        let mut c = Concept::new();
        c.set_concept_tag(1653);
        c.set_operator_code(op::CCATOM);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let some_rc = {
        let mut c = Concept::new();
        c.set_concept_tag(2654);
        c.set_operator_code(op::CCSOME);
        c.set_role(role_r);
        c.add_operand_linker(con_c, false);
        c.set_operand_count(1);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let some_rd = {
        let mut c = Concept::new();
        c.set_concept_tag(2655);
        c.set_operator_code(op::CCSOME);
        c.set_role(role_r);
        c.add_operand_linker(con_d, false);
        c.set_operand_count(1);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let atmost_1_top = {
        let mut c = Concept::new();
        c.set_concept_tag(2656);
        c.set_operator_code(op::CCATMOST);
        c.set_role(role_r);
        c.set_parameter(1);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };

    let root = env.root;
    // run 1: one successor, ≤1 fires below the bound and arms the resume.
    seed_concept_on_queue(&mut env, root, some_rc);
    seed_concept_on_queue(&mut env, root, atmost_1_top);
    seed_root_immediate(&mut env, root);
    assert!(
        env.algo.run_completion_on(&mut env.ctx),
        "∃R.C ⊓ ≤1 R.⊤ is consistent"
    );
    assert_eq!(
        role_successors(&env, root, role_r).len(),
        1,
        "one successor after run 1"
    );

    // run 2: a second successor arrives; the armed reapply must re-fire the
    // ≤1 and merge (the two successors are mergeable — no distinct edge).
    seed_concept_on_queue(&mut env, root, some_rd);
    seed_root_immediate(&mut env, root);
    let consistent = env.algo.run_completion_on(&mut env.ctx);
    assert!(
        consistent,
        "∃R.C ⊓ ∃R.D ⊓ ≤1 R.⊤ is consistent (the successors merge)"
    );
    let succs = role_successors(&env, root, role_r);
    assert_eq!(
        succs.len(),
        1,
        "the rest-driven reapply must merge the two successors into one (got {})",
        succs.len()
    );
    assert!(
        label_set_has_tag(&mut env, succs[0], 1652),
        "the merged successor carries C"
    );
    assert!(
        label_set_has_tag(&mut env, succs[0], 1653),
        "the merged successor carries D"
    );
}

/// The choose rule under the rest machinery: `≥2 R.C ⊓ ≤1 R.D` — the two
/// C-successors are UNDECIDED for D, so the choose rule qualifies them; the
/// ¬D alternatives leave the ≤1 D-count at zero ⇒ CONSISTENT (still two
/// R-successors, both forced distinct by the ≥2).
#[test]
fn atmost_rest_choose_qualifies_undecided() {
    use super::super::model::op;
    use super::super::model::role::Role;

    let mut env = build_env();
    env.algo.conf_atmost_rest = true;
    let role_r = env.ctx.ontology_arenas_mut().alloc_role(Role::new());
    let con_c = {
        let mut c = Concept::new();
        c.set_concept_tag(1654);
        c.set_operator_code(op::CCATOM);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let con_d = {
        let mut c = Concept::new();
        c.set_concept_tag(1655);
        c.set_operator_code(op::CCATOM);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let atleast_2_rc = {
        let mut c = Concept::new();
        c.set_concept_tag(2657);
        c.set_operator_code(op::CCATLEAST);
        c.set_role(role_r);
        c.set_parameter(2);
        c.add_operand_linker(con_c, false);
        c.set_operand_count(1);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let atmost_1_rd = {
        let mut c = Concept::new();
        c.set_concept_tag(2658);
        c.set_operator_code(op::CCATMOST);
        c.set_role(role_r);
        c.set_parameter(1);
        c.add_operand_linker(con_d, false);
        c.set_operand_count(1);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };

    let root = env.root;
    seed_concept_on_queue(&mut env, root, atleast_2_rc);
    seed_root_immediate(&mut env, root);
    assert!(env.algo.run_completion_on(&mut env.ctx), "≥2 R.C alone is consistent");

    seed_concept_on_queue(&mut env, root, atmost_1_rd);
    seed_root_immediate(&mut env, root);
    let consistent = env.algo.run_completion_on(&mut env.ctx);
    assert!(
        consistent,
        "≥2 R.C ⊓ ≤1 R.D is consistent (choose decides ¬D on the C-successors)"
    );
    assert_eq!(
        role_successors(&env, root, role_r).len(),
        2,
        "both distinct C-successors survive (no D-merge needed)"
    );
}

/// The choose-trigger REACTIVATION end-to-end: `≥2 R.C ⊓ ≤1 R.D` defers the
/// undecided successors (atomic qualifier D → hooks, no eager branch); a
/// LATER `∀R.D` pushes D onto both successors, the hooks fire, the ≤1 R.D
/// re-queues on the root, sees two counted forced-distinct D-successors and
/// CLASHES ⇒ INCONSISTENT.
#[test]
fn atmost_rest_trigger_reactivation_clashes() {
    use super::super::model::op;
    use super::super::model::role::Role;

    let mut env = build_env();
    env.algo.conf_atmost_rest = true;
    let role_r = env.ctx.ontology_arenas_mut().alloc_role(Role::new());
    let con_c = {
        let mut c = Concept::new();
        c.set_concept_tag(1656);
        c.set_operator_code(op::CCATOM);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let con_d = {
        let mut c = Concept::new();
        c.set_concept_tag(1657);
        c.set_operator_code(op::CCATOM);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let atleast_2_rc = {
        let mut c = Concept::new();
        c.set_concept_tag(2659);
        c.set_operator_code(op::CCATLEAST);
        c.set_role(role_r);
        c.set_parameter(2);
        c.add_operand_linker(con_c, false);
        c.set_operand_count(1);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let atmost_1_rd = {
        let mut c = Concept::new();
        c.set_concept_tag(2660);
        c.set_operator_code(op::CCATMOST);
        c.set_role(role_r);
        c.set_parameter(1);
        c.add_operand_linker(con_d, false);
        c.set_operand_count(1);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let all_rd = {
        let mut c = Concept::new();
        c.set_concept_tag(2661);
        c.set_operator_code(op::CCALL);
        c.set_role(role_r);
        c.add_operand_linker(con_d, false);
        c.set_operand_count(1);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };

    let root = env.root;
    // run 1: two distinct C-successors, ≤1 R.D defers (both undecided for D).
    seed_concept_on_queue(&mut env, root, atleast_2_rc);
    seed_concept_on_queue(&mut env, root, atmost_1_rd);
    seed_root_immediate(&mut env, root);
    assert!(
        env.algo.run_completion_on(&mut env.ctx),
        "≥2 R.C ⊓ ≤1 R.D is consistent (deferred choose)"
    );
    assert_eq!(role_successors(&env, root, role_r).len(), 2);

    // run 2: ∀R.D lands D on both successors → reactivation hooks fire →
    // ≤1 R.D re-fires and the two forced-distinct D-successors clash.
    seed_concept_on_queue(&mut env, root, all_rd);
    seed_root_immediate(&mut env, root);
    let consistent = env.algo.run_completion_on(&mut env.ctx);
    assert!(
        !consistent,
        "∀R.D must reactivate the deferred ≤1 R.D and refute (two distinct D-successors)"
    );
    match env.ctx.pending_signal() {
        CalcSignal::Clash(_) => {}
        other => panic!("expected a Clash signal, got {:?}", other),
    }
}

// ===========================================================================
// W15-rbox: the SHIQ RBox-side propagation that ∀/∃ depend on — role HIERARCHY
// (`R ⊑ S`), INVERSE roles (`R⁻`), and TRANSITIVE roles (`Trans(R)`). Resolved by
// `apply_all_rule` (u09) via the `ht_all_rule_targets` lookup (u10): a ∀S restriction
// reaches R-successors with `R ⊑ S`, the inverse predecessor via the ancestor link,
// and re-propagates itself across transitive roles. Drives end-to-end through
// `run_completion_on`.
// ===========================================================================

/// Seed a concept-process descriptor for `concept` on `root`'s concept queue at an
/// explicit priority `pri` (higher = taken first). Lets a test order ∃ before ∀.
fn seed_concept_on_queue_pri(env: &mut SelfTestEnv, root: NodeId, concept: ConceptId, pri: f64) {
    let queue = env
        .ctx
        .process_context_mut()
        .node_concept_processing_queue(root, true);
    let con_des = env
        .ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    env.ctx.process_context_mut().con_desc_mut(con_des).concept = concept;
    let mut cpd_val = ConceptProcessDescriptor::new();
    cpd_val.concept_des = con_des;
    cpd_val.priority = ConceptProcessPriority::new(pri);
    let cpd = env.ctx.process_context_mut().alloc_con_proc_desc(cpd_val);
    ConceptProcessingQueue::insert_concept_process_descriptor(
        queue,
        cpd,
        env.ctx.process_context_mut(),
    );
}

/// `R ⊑ S`, root `∃R.D ⊓ ∀S.C`: the ∃ builds an R-successor; the ∀S restriction must
/// reach it BECAUSE the R-edge is also an S-edge (`R ⊑ S`). After the run the
/// R-successor carries BOTH D (from ∃R.D) and C (from ∀S.C via the hierarchy).
#[test]
fn role_hierarchy_forall() {
    use super::super::model::op;
    use super::super::model::role::Role;
    use super::super::model::substrate::NegLink;

    let mut env = build_env();
    // role S, then role R with `R ⊑ S` (S in R's indirect-super-role list).
    let role_s = {
        let mut r = Role::new();
        r.set_role_tag(2);
        env.ctx.ontology_arenas_mut().alloc_role(r)
    };
    let role_r = {
        let mut r = Role::new();
        r.set_role_tag(1);
        r.add_indirect_super_role_linker(NegLink {
            target: role_s,
            negated: false,
        });
        env.ctx.ontology_arenas_mut().alloc_role(r)
    };
    let con_d = {
        let mut c = Concept::new();
        c.set_concept_tag(160);
        c.set_operator_code(op::CCATOM);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let con_c = {
        let mut c = Concept::new();
        c.set_concept_tag(161);
        c.set_operator_code(op::CCATOM);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    let some_rd = {
        let mut c = Concept::new();
        c.set_concept_tag(260);
        c.set_operator_code(op::CCSOME);
        c.set_role(role_r);
        c.add_operand_linker(con_d, false);
        c.set_operand_count(1);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    // ∀S.C : CCALL, role S, operand [C].
    let all_sc = {
        let mut c = Concept::new();
        c.set_concept_tag(261);
        c.set_operator_code(op::CCALL);
        c.set_role(role_s);
        c.add_operand_linker(con_c, false);
        c.set_operand_count(1);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };

    let root = env.root;
    // ∃R.D at higher priority (12) so the R-successor exists when ∀S.C (8) is processed.
    seed_concept_on_queue_pri(&mut env, root, some_rd, 12.0);
    seed_concept_on_queue_pri(&mut env, root, all_sc, 8.0);
    seed_root_immediate(&mut env, root);

    let consistent = env.algo.run_completion_on(&mut env.ctx);
    assert!(consistent, "∃R.D ⊓ ∀S.C with R ⊑ S is consistent");
    assert!(!env.ctx.has_pending_signal(), "no clash expected");

    let succ = first_role_successor(&env, root);
    assert!(
        label_set_has_tag(&mut env, succ, 160),
        "the R-successor must carry D (tag 160) from ∃R.D"
    );
    assert!(
        label_set_has_tag(&mut env, succ, 161),
        "∀S.C must reach the R-successor via the hierarchy R ⊑ S (tag 161)"
    );
}

/// `R⁻` inverse, root `∃R.(∀R⁻.C)`: the ∃ builds an R-successor whose qualifier is
/// `∀R⁻.C`; since the R-edge root→succ is an R⁻-edge succ→root, that ∀R⁻ restriction
/// must propagate C BACK to the root (the predecessor). After the run the ROOT carries
/// C, reached purely through the inverse role.
#[test]
fn inverse_role_propagation() {
    use super::super::model::op;
    use super::super::model::role::Role;

    let mut env = build_env();
    let role_rinv = {
        let mut r = Role::new();
        r.set_role_tag(4);
        env.ctx.ontology_arenas_mut().alloc_role(r)
    };
    let role_r = {
        let mut r = Role::new();
        r.set_role_tag(3);
        r.set_inverse_role(role_rinv);
        env.ctx.ontology_arenas_mut().alloc_role(r)
    };
    env.ctx
        .ontology_arenas_mut()
        .role_mut(role_rinv)
        .set_inverse_role(role_r);

    let con_c = {
        let mut c = Concept::new();
        c.set_concept_tag(162);
        c.set_operator_code(op::CCATOM);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    // ∀R⁻.C : CCALL, role R⁻, operand [C].
    let all_rinv_c = {
        let mut c = Concept::new();
        c.set_concept_tag(262);
        c.set_operator_code(op::CCALL);
        c.set_role(role_rinv);
        c.add_operand_linker(con_c, false);
        c.set_operand_count(1);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    // ∃R.(∀R⁻.C) : CCSOME, role R, operand [∀R⁻.C].
    let some_r_all = {
        let mut c = Concept::new();
        c.set_concept_tag(263);
        c.set_operator_code(op::CCSOME);
        c.set_role(role_r);
        c.add_operand_linker(all_rinv_c, false);
        c.set_operand_count(1);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };

    let root = env.root;
    seed_concept_on_queue(&mut env, root, some_r_all);
    seed_root_immediate(&mut env, root);

    let consistent = env.algo.run_completion_on(&mut env.ctx);
    assert!(consistent, "∃R.(∀R⁻.C) is consistent");
    assert!(!env.ctx.has_pending_signal(), "no clash expected");

    assert!(
        label_set_has_tag(&mut env, root, 162),
        "∀R⁻.C on the successor must propagate C back to the root predecessor (tag 162)"
    );
}

/// Build a fresh `role`-successor of `parent`: a new node, the directed `parent
/// --role--> child` link-edge installed into `parent`'s successor-role hash, plus the
/// child's ancestor link / depth — the same wiring `apply_some_rule` performs, exposed
/// so a test can pre-build a role CHAIN. (Needed because existentials on SUCCESSOR
/// nodes are not yet drained — `take_next_process_individual`'s depth-expansion probes
/// are PORT-PENDING (W8.1) — so a nested `∃R.(∃R.D)` cannot grow the second hop on its
/// own. The RBox transitivity rule under test is independent of that gap.)
fn build_role_successor(
    env: &mut SelfTestEnv,
    parent: NodeId,
    role: super::super::model::RoleId,
) -> NodeId {
    let child = env
        .algo
        .create_new_individual(TrackPointId::NONE, false, &mut env.ctx);
    let link = env.algo.ht_install_role_successor_edge(
        parent,
        child,
        role,
        TrackPointId::NONE,
        &mut env.ctx,
    );
    let depth = env
        .ctx
        .process_context()
        .node(parent)
        .individual_ancestor_depth();
    {
        let n = env.ctx.process_context_mut().node_mut(child);
        n.set_ancestor_link(link);
        n.set_individual_ancestor_depth(depth + 1);
    }
    child
}

/// `Trans(R)` over a pre-built chain `root --R--> m --R--> n`, with `∀R.C` on the root:
/// the transitivity ∀-rule must re-propagate `∀R.C` ITSELF (not just `C`) along R, so
/// `C` reaches BOTH the direct R-successor `m` AND the R-R-successor `n`. Driven in two
/// phases (root, then m) because successor existential/queue draining is a separate
/// unported subsystem (W8.1); the transitivity propagation itself is what is exercised.
#[test]
fn transitive_forall() {
    use super::super::model::op;
    use super::super::model::role::Role;

    let mut env = build_env();
    let role_r = {
        let mut r = Role::new();
        r.set_role_tag(5);
        r.set_transitive(true);
        env.ctx.ontology_arenas_mut().alloc_role(r)
    };
    let con_c = {
        let mut c = Concept::new();
        c.set_concept_tag(164);
        c.set_operator_code(op::CCATOM);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };
    // ∀R.C : CCALL, role R, operand [C].
    let all_r_c = {
        let mut c = Concept::new();
        c.set_concept_tag(266);
        c.set_operator_code(op::CCALL);
        c.set_role(role_r);
        c.add_operand_linker(con_c, false);
        c.set_operand_count(1);
        env.ctx.ontology_arenas_mut().alloc_concept(c)
    };

    let root = env.root;
    // pre-build the two-hop R-chain root --R--> m --R--> n.
    let m = build_role_successor(&mut env, root, role_r);
    let n = build_role_successor(&mut env, m, role_r);

    // phase 1: ∀R.C on the root → reaches m (C + the re-propagating ∀R.C).
    seed_concept_on_queue(&mut env, root, all_r_c);
    seed_root_immediate(&mut env, root);
    let consistent1 = env.algo.run_completion_on(&mut env.ctx);
    assert!(consistent1, "phase 1 is consistent");
    assert!(!env.ctx.has_pending_signal(), "no clash in phase 1");
    assert!(
        label_set_has_tag(&mut env, m, 164),
        "the direct R-successor m must carry C (tag 164)"
    );
    assert!(
        label_set_has_tag(&mut env, m, 266),
        "the transitivity ∀-rule must re-propagate ∀R.C ITSELF (tag 266) onto m"
    );

    // phase 2: drive m → the re-propagated ∀R.C on m reaches the R-R-successor n.
    seed_root_immediate(&mut env, m);
    let consistent2 = env.algo.run_completion_on(&mut env.ctx);
    assert!(consistent2, "phase 2 is consistent");
    assert!(!env.ctx.has_pending_signal(), "no clash in phase 2");
    assert!(
        label_set_has_tag(&mut env, n, 164),
        "the R-R-successor n must carry C (tag 164) via the transitivity ∀-rule"
    );
}
