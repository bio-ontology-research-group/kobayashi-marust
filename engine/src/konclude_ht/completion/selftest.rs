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
use super::super::process::descriptor::{
    ConceptProcessDescriptor, ConceptProcessPriority, ConceptDescriptor,
};
use super::super::process::node::IndividualProcessNode;
use super::super::process::queues::ConceptProcessingQueue;
use super::super::process::{ConDescId, NodeId, TrackPointId};
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

    // --- the ontology TOP concept (CCTOP) — `create_new_individual` seeds every
    //     fresh successor node with it, so it must resolve to a real concept. ---
    let top = {
        let mut c = Concept::new();
        c.set_concept_tag(1);
        c.set_operator_code(super::super::model::op::CCTOP);
        ctx.ontology_arenas_mut().alloc_concept(c)
    };
    ctx.processing_data_box_mut().ontology_top_concept = top;

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
        con_a, false, &mut root, TrackPointId::NONE, false, true, &mut env.ctx,
    );
    // add the implication concept — the NATURAL enqueue path pushes a real descriptor.
    env.algo.add_concept_to_individual(
        con_impl, false, &mut root, TrackPointId::NONE, false, true, &mut env.ctx,
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
        con_a, false, &mut root, TrackPointId::NONE, false, true, &mut env.ctx,
    );
    env.algo.add_concept_to_individual(
        con_impl_b, false, &mut root, TrackPointId::NONE, false, true, &mut env.ctx,
    );
    env.algo.add_concept_to_individual(
        con_impl_not_b, false, &mut root, TrackPointId::NONE, false, true, &mut env.ctx,
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
    assert!(succ.is_some(), "the successor must be registered in the node vector");
    succ
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
        all_rc, false, &mut root, TrackPointId::NONE, false, true, &mut env.ctx,
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
        all_not_c, false, &mut root, TrackPointId::NONE, false, true, &mut env.ctx,
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

// ===========================================================================
// W14-number: the SHIQ qualified-cardinality core (≥n R.C / ≤n R.C). ≥n builds
// n fresh PAIRWISE-DISTINCT successors each labelled C; ≤n merges or, when the
// successors are forced distinct, CLASHES. Drives end-to-end through
// `run_completion_on`.
// ===========================================================================

/// All distinct `role`-successor nodes of `node` (via the algorithm's live
/// role-successor link iterator).
fn role_successors(env: &SelfTestEnv, node: NodeId, role: super::super::model::RoleId) -> Vec<NodeId> {
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
    assert!(!env.ctx.has_pending_signal(), "no clash expected for ≥2 R.C");

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
        !env.algo.ht_individuals_mergeable(succs[0], succs[1], &env.ctx),
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
    assert_eq!(role_successors(&env, root, role_r).len(), 2, "two successors after ≥2");

    // run 2: ≤1 R.⊤ now sees two distinct R-successors over the bound ⇒ CLASH.
    seed_concept_on_queue(&mut env, root, atmost_1_top);
    seed_root_immediate(&mut env, root);
    let consistent2 = env.algo.run_completion_on(&mut env.ctx);

    assert!(
        !consistent2,
        "≥2 R.C ⊓ ≤1 R.⊤ is INCONSISTENT (two forced-distinct successors over the at-most bound)"
    );
    assert!(env.ctx.has_pending_signal(), "the at-most violation must raise a clash");
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
    assert_eq!(role_successors(&env, root, role_r).len(), 2, "two successors after ≥2");

    seed_concept_on_queue(&mut env, root, atmost_1_rc);
    seed_root_immediate(&mut env, root);
    let consistent2 = env.algo.run_completion_on(&mut env.ctx);

    assert!(
        !consistent2,
        "≥2 R.C ⊓ ≤1 R.C with the two successors distinct is INCONSISTENT"
    );
    assert!(env.ctx.has_pending_signal(), "the qualified at-most violation must clash");
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
        r.add_indirect_super_role_linker(NegLink { target: role_s, negated: false });
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
    env.ctx.ontology_arenas_mut().role_mut(role_rinv).set_inverse_role(role_r);

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
