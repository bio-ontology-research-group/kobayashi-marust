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

use super::super::model::concept::Concept;
use super::super::model::substrate::Id;
use super::super::model::ConceptId;
use super::super::process::descriptor::{ConceptProcessDescriptor, ConceptDescriptor};
use super::super::process::node::IndividualProcessNode;
use super::super::process::queues::ConceptProcessingQueue;
use super::super::process::{NodeId, TrackPointId};
use super::algorithm::CompletionTaskHandleAlgorithm;
use super::clash::CalcSignal;
use super::context::CalculationAlgorithmContextBase;

/// The thin test harness: a constructed per-thread context, the completion
/// algorithm, the hand-built concept A and a seeded root individual node.
struct SelfTestEnv {
    algo: CompletionTaskHandleAlgorithm,
    ctx: CalculationAlgorithmContextBase,
    concept_a: ConceptId,
    root: NodeId,
}

/// Port-faithful analogue of `initializeCompletionGraph` + `buildCompletionGraph`'s
/// root-node creation: build the context, a one-concept TBox, and a root nominal
/// node registered in the node vector.
fn build_env() -> SelfTestEnv {
    let algo = CompletionTaskHandleAlgorithm::new();
    let mut ctx = CalculationAlgorithmContextBase::new();

    // --- hand-build the static terminology: one named concept A ---
    let concept_a = {
        let mut c = Concept::new();
        // CConcept::setConceptTag — the value `insertConceptGetClash` keys the label
        // set by (so A and ¬A collide on the same key and the polarity compare runs).
        c.set_concept_tag(100);
        ctx.ontology_arenas_mut().alloc_concept(c)
    };

    // --- minimal completion-graph init: the root individual node ---
    // new CIndividualProcessNode(processContext) — no process-context arena handle
    // is needed here, so `Id::NONE` (the node-resolution keystone uses the same).
    let root = ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    // setIndividualNodeID(0) — the (anonymous) root individual id.
    ctx.process_context_mut().node_mut(root).set_individual_node_id(0);
    // indiProcNodeVec->setLocalData(indiID, root) — register it so the resolvers see it.
    ctx.processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(0, root);

    SelfTestEnv { algo, ctx, concept_a, root }
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
    assert!(queue.is_some(), "concept processing queue must be allocated");
    assert!(
        env.ctx.process_context().concept_proc_queue(queue).is_empty(),
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
        !env.ctx.process_context().concept_proc_queue(queue).is_empty(),
        "queue must be non-empty after insert"
    );

    // conProDes = conProcQueue->takeNextConceptDescriptorProcess() — the drive-loop pop.
    let taken = ConceptProcessingQueue::take_next_concept_descriptor_process(
        queue,
        env.ctx.process_context_mut(),
    );
    assert_eq!(taken, cpd, "take must return the inserted descriptor");
    assert!(
        env.ctx.process_context().concept_proc_queue(queue).is_empty(),
        "queue must be empty again after take"
    );
}
