//! `completion::classify_test` — the W13 CLASSIFICATION milestone: the ported
//! Konclude hypertableau completion engine doing the REAL KM reasoning task —
//! TBox classification reduced to consistency checking.
//!
//! Subsumption `A ⊑ B` w.r.t. a TBox holds IFF the concept `A ⊓ ¬B` is
//! UNSATISFIABLE w.r.t. that TBox. This is exactly Konclude's consistency-based
//! subsumption pattern: a concept-satisfiability test seeds a root node with the
//! probe concept (here `A ⊓ ¬B`) plus the TBox GCIs, runs the completion engine,
//! and reads the verdict off the pending clash signal — a Clash ⇒ unsatisfiable
//! ⇒ the subsumption holds.
//!
//! The reusable harness here ([`is_unsatisfiable`] / [`Env::entails_subsumption`])
//! builds a fresh per-thread context, seeds a root with the probe concepts and the
//! TBox implications, drives `run_completion_on` TO FIXPOINT, and returns whether a
//! Clash was raised. It reuses the SAME live machinery the W5-W12 selftests exercise
//! (AND / IMPL-unfold / clash) — nothing new in the calculus, only the classify
//! reduction wired on top.
//!
//! KONCLUDE-PORT-NOTE[reapply]: the condensed reapply queue
//! (`addConceptToReapplyQueue`) is W3-DEFER, so a GCI fires only when its trigger is
//! ALREADY present at the moment the implication is processed (see
//! `apply_implication_rule`, `u09.rs`). The concept-processing queue is LIFO at the
//! default priority, so a chain `A ⊑ B ⊑ C` may need the `B ⊑ C` implication
//! re-processed AFTER `B` has been derived. `is_unsatisfiable` therefore RE-DRIVES:
//! it re-enqueues every GCI and re-runs the completion until either a clash fires or
//! the root's concept-label-set count reaches a fixpoint. Each pass propagates at
//! least one further link of an acyclic GCI chain, so the fixpoint is reached in at
//! most `#GCIs` passes — this is the sound, terminating stand-in for the unported
//! reapply queue.

#![cfg(test)]

use super::super::model::concept::Concept;
use super::super::model::op;
use super::super::model::substrate::Id;
use super::super::model::ConceptId;
use super::super::process::descriptor::{
    ConceptDescriptor, ConceptProcessDescriptor, ConceptProcessPriority,
};
use super::super::process::node::IndividualProcessNode;
use super::super::process::queues::ConceptProcessingQueue;
use super::super::process::{NodeId, TrackPointId};
use super::algorithm::CompletionTaskHandleAlgorithm;
use super::context::CalculationAlgorithmContextBase;
use super::strategy::ConceptProcessingPriorityStrategy;

/// A constructed per-thread classification context: the completion algorithm + the
/// algorithm context (with the static terminology arena), plus a running individual
/// id so each probed root gets a fresh node-vector slot.
struct Env {
    algo: CompletionTaskHandleAlgorithm,
    ctx: CalculationAlgorithmContextBase,
    next_indi_id: i64,
}

/// Build the context and seed the ontology TOP concept (`create_new_individual`
/// labels every fresh successor with it, so it must resolve to a real concept).
fn new_env() -> Env {
    let algo = CompletionTaskHandleAlgorithm::new();
    let mut ctx = CalculationAlgorithmContextBase::new();
    ctx.base.used_concept_priority_strategy =
        Some(ConceptProcessingPriorityStrategy::new_concrete_operator());
    let top = {
        let mut c = Concept::new();
        c.set_concept_tag(1);
        c.set_operator_code(op::CCTOP);
        ctx.ontology_arenas_mut().alloc_concept(c)
    };
    ctx.processing_data_box_mut().ontology_top_concept = top;
    Env {
        algo,
        ctx,
        next_indi_id: 0,
    }
}

impl Env {
    /// Allocate a named atomic concept with the given tag (`CCATOM` ⇒ no tableau
    /// rule ⇒ it lands directly in a node's concept label set).
    fn atom(&mut self, tag: i64) -> ConceptId {
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op::CCATOM);
        self.ctx.ontology_arenas_mut().alloc_concept(c)
    }

    /// Allocate a conjunction concept `⊓ ops` (`CCAND`, all operands positive).
    fn conj(&mut self, tag: i64, ops: &[ConceptId]) -> ConceptId {
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op::CCAND);
        for &o in ops {
            c.add_operand_linker(o, false);
        }
        c.set_operand_count(ops.len() as i64);
        self.ctx.ontology_arenas_mut().alloc_concept(c)
    }

    /// Allocate a GCI `sub ⊑ head` (optionally a negated head) as the implication
    /// concept `¬sub ⊔ head` — `CCIMPL`, operands `[head(head_neg), ¬sub(trigger)]`.
    /// The rule fires when `sub` is present with the opposite polarity of the `¬sub`
    /// trigger linker, i.e. positive `sub`.
    fn gci(&mut self, tag: i64, sub: ConceptId, head: ConceptId, head_neg: bool) -> ConceptId {
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op::CCIMPL);
        c.add_operand_linker(head, head_neg); // implied head
        c.add_operand_linker(sub, true); // trigger ¬sub
        c.set_operand_count(2);
        self.ctx.ontology_arenas_mut().alloc_concept(c)
    }

    /// Allocate + register a fresh anonymous root node.
    fn make_root(&mut self) -> NodeId {
        let id = self.next_indi_id;
        self.next_indi_id += 1;
        let root = self
            .ctx
            .process_context_mut()
            .alloc_node(IndividualProcessNode::new(Id::NONE));
        self.ctx
            .process_context_mut()
            .node_mut(root)
            .set_individual_node_id(id);
        self.ctx
            .processing_data_box_mut()
            .individual_process_node_vector_mut()
            .set_local_data(id, root);
        root
    }

    /// `A ⊑ B` w.r.t. `gcis` holds IFF `A ⊓ ¬B` is unsatisfiable. Seeds a fresh root
    /// with positive `sub` and negated `super` and probes for a clash.
    fn entails_subsumption(
        &mut self,
        sub: ConceptId,
        super_: ConceptId,
        gcis: &[ConceptId],
    ) -> bool {
        is_unsatisfiable(self, &[(sub, false), (super_, true)], gcis)
    }
}

/// Seed `concept` onto `root`'s concept-processing queue at the immediate priority (8).
fn seed_concept_on_queue(env: &mut Env, root: NodeId, concept: ConceptId) {
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
fn seed_root_immediate(env: &mut Env, root: NodeId) {
    let iq = env.ctx.get_individual_immediately_processing_queue(true);
    env.ctx
        .process_context_mut()
        .indi_unsorted_proc_queue_mut(iq)
        .insert_indiviudal_process_node(root);
}

/// The reusable CONSISTENCY probe: build a fresh root, add the `seed` concepts
/// (`(concept, negated)`) to its label set, then RE-DRIVE the completion engine to a
/// fixpoint over the `gcis` (the TBox implications). Returns `true` iff a Clash was
/// raised — i.e. the seeded concept conjunction is UNSATISFIABLE w.r.t. the TBox.
fn is_unsatisfiable(env: &mut Env, seed: &[(ConceptId, bool)], gcis: &[ConceptId]) -> bool {
    // independent probe: clear any clash signal / branch state left by a prior probe
    // on this shared context (each subsumption test is its own consistency check).
    env.ctx.clear_pending_signal();
    env.algo.or_branch_stack.clear();

    let mut root = env.make_root();

    // add the probe concepts to the root label set; an immediate polarity clash here
    // (e.g. seeding A and ¬A directly) is already an unsatisfiability witness.
    for &(concept, negated) in seed {
        env.algo.add_concept_to_individual(
            concept,
            negated,
            &mut root,
            TrackPointId::NONE,
            false,
            true,
            &mut env.ctx,
        );
        if env.ctx.has_pending_signal() {
            return true;
        }
    }

    // re-drive to fixpoint: each pass re-enqueues every GCI and runs the completion;
    // a clash ⇒ unsatisfiable; a stable label-set count ⇒ saturated and consistent.
    let mut prev_count: i64 = -1;
    for _ in 0..256 {
        for &g in gcis {
            seed_concept_on_queue(env, root, g);
        }
        seed_root_immediate(env, root);
        let consistent = env.algo.run_completion_on(&mut env.ctx);
        if !consistent {
            return true;
        }
        let ls = env
            .ctx
            .process_context_mut()
            .node_reapply_concept_label_set(root);
        let count = env.ctx.process_context().label_set(ls).get_concept_count();
        if count == prev_count {
            break;
        }
        prev_count = count;
    }
    false
}

// ===========================================================================
// W13 classification selftests — real subsumption decided via consistency.
// ===========================================================================

/// `{A ⊑ B}` ⇒ `A ⊑ B` HOLDS (A ⊓ ¬B unsat) and `B ⊑ A` does NOT.
#[test]
fn subsumption_direct() {
    let mut env = new_env();
    let a = env.atom(101);
    let b = env.atom(102);
    let a_sub_b = env.gci(300, a, b, false);
    let tbox = [a_sub_b];

    assert!(
        env.entails_subsumption(a, b, &tbox),
        "A ⊑ B must hold under {{A ⊑ B}} (A ⊓ ¬B is unsatisfiable)"
    );
    assert!(
        !env.entails_subsumption(b, a, &tbox),
        "B ⊑ A must NOT hold under {{A ⊑ B}} (B ⊓ ¬A is satisfiable)"
    );
}

/// `{A ⊑ B, B ⊑ C}` ⇒ `A ⊑ C` HOLDS (the unfold chain derives C, clashing with ¬C),
/// while `C ⊑ A` does NOT.
#[test]
fn subsumption_transitive() {
    let mut env = new_env();
    let a = env.atom(101);
    let b = env.atom(102);
    let c = env.atom(103);
    let a_sub_b = env.gci(300, a, b, false);
    let b_sub_c = env.gci(301, b, c, false);
    let tbox = [a_sub_b, b_sub_c];

    assert!(
        env.entails_subsumption(a, c, &tbox),
        "A ⊑ C must hold under {{A ⊑ B, B ⊑ C}} via the unfold chain"
    );
    assert!(
        !env.entails_subsumption(c, a, &tbox),
        "C ⊑ A must NOT hold under {{A ⊑ B, B ⊑ C}}"
    );
}

/// `{A ⊑ B ⊓ C}` ⇒ `A ⊑ C` HOLDS (the implication adds the conjunction, the ⊓-rule
/// splits it to B and C, and C clashes with ¬C).
#[test]
fn subsumption_via_conjunction() {
    let mut env = new_env();
    let a = env.atom(101);
    let b = env.atom(102);
    let c = env.atom(103);
    let b_and_c = env.conj(200, &[b, c]);
    let a_sub_bc = env.gci(300, a, b_and_c, false);
    let tbox = [a_sub_bc];

    assert!(
        env.entails_subsumption(a, c, &tbox),
        "A ⊑ C must hold under {{A ⊑ B ⊓ C}} (the ⊓-rule exposes C)"
    );
    assert!(
        env.entails_subsumption(a, b, &tbox),
        "A ⊑ B must also hold under {{A ⊑ B ⊓ C}}"
    );
}

/// `{A ⊑ B, A ⊑ ¬B}` ⇒ `A` is UNSATISFIABLE (both implications fire from A and the
/// derived B / ¬B contradict).
#[test]
fn unsatisfiable_concept() {
    let mut env = new_env();
    let a = env.atom(101);
    let b = env.atom(102);
    let a_sub_b = env.gci(300, a, b, false);
    let a_sub_not_b = env.gci(301, a, b, true);
    let tbox = [a_sub_b, a_sub_not_b];

    assert!(
        is_unsatisfiable(&mut env, &[(a, false)], &tbox),
        "A must be unsatisfiable under {{A ⊑ B, A ⊑ ¬B}}"
    );
}
