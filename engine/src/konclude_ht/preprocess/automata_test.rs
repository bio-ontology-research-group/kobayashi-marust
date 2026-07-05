//! `preprocess::automata_test` — synthetic validation of the role-chain
//! automata preprocessor (`role_chain_automata.rs`) and its consumption by the
//! completion engine's automat rules (u03 dispatch, u05
//! `apply_automat_transactions`, u08 edge-triggered reapply).
//!
//! Two layers:
//!  1. STRUCTURE tests — build roles/chains/∀-concepts directly in an
//!     `OntologyArenas`, run `preprocess()`, and assert the exact automaton
//!     wiring Konclude produces (`CCAQCHOOCE` trigger, `CCAQSOME` generator,
//!     begin/end `CCAQAND` states, `CCAQALL` transitions, the transitive
//!     ε-loop end → begin, the transStart/transEnd chain gluing).
//!  2. END-TO-END tests — the same fixtures driven through
//!     `run_completion_on`: transitivity / role hierarchy / role chains must
//!     make multi-hop ∀-violations CLASH, and must NOT clash on the
//!     order-violating or role-disjoint controls.
//!
//! Fixture conventions mirror Konclude's build output
//! (`CSubroleTransformationPreProcess`): every role's indirect-super list
//! contains the role ITSELF (positive, first); any role super-sharing a chain
//! is complex and so are all its indirect supers; concept/role tags equal
//! their arena indices (`preprocess` allocates fresh tags from
//! `concept_count()`).

#![cfg(test)]

use super::super::completion::algorithm::CompletionTaskHandleAlgorithm;
use super::super::completion::context::CalculationAlgorithmContextBase;
use super::super::completion::strategy::ConceptProcessingPriorityStrategy;
use super::super::model::concept::Concept;
use super::super::model::individual::Individual;
use super::super::model::ontology::OntologyArenas;
use super::super::model::op;
use super::super::model::role::Role;
use super::super::model::role_chain::RoleChain;
use super::super::model::substrate::{Cint64, Id, NegLink};
use super::super::model::{ConceptId, RoleChainId, RoleId};
use super::super::process::descriptor::{
    ConceptDescriptor, ConceptProcessDescriptor, ConceptProcessPriority,
};
use super::super::process::node::IndividualProcessNode;
use super::super::process::queues::ConceptProcessingQueue;
use super::super::process::{NodeId, TrackPointId};
use super::role_chain_automata::RoleChainAutomataTransformationPreProcess;

// ===========================================================================
// fixture builders
// ===========================================================================

/// Seed the arenas with the tag-0 ⊥ and tag-1 ⊤ concepts and the tag-0/tag-1
/// placeholder roles (role tag 1 is the TOP-role sentinel in
/// `convert_automat_concept`; real fixture roles start at tag 2), keeping
/// tag == arena index throughout.
fn seed_arenas(arenas: &mut OntologyArenas) -> ConceptId {
    let bottom = {
        let mut c = Concept::new();
        c.set_concept_tag(0);
        c.set_operator_code(op::CCBOTTOM);
        arenas.alloc_concept(c)
    };
    let _ = bottom;
    let top = {
        let mut c = Concept::new();
        c.set_concept_tag(1);
        c.set_operator_code(op::CCTOP);
        arenas.alloc_concept(c)
    };
    for tag in 0..2 {
        let r = arenas.alloc_role(Role::new());
        arenas.role_mut(r).set_role_tag(tag);
    }
    top
}

/// A fresh role with tag == arena index and itself as the first (positive)
/// indirect super role, per the Konclude build convention.
fn mk_role(arenas: &mut OntologyArenas) -> RoleId {
    let r = arenas.alloc_role(Role::new());
    let tag = r.index() as Cint64;
    arenas.role_mut(r).set_role_tag(tag);
    arenas.role_mut(r).indirect_super_roles.push(NegLink {
        target: r,
        negated: false,
    });
    r
}

/// `sub ⊑ sup` — positive direct + indirect super linker.
fn add_super_role(arenas: &mut OntologyArenas, sub: RoleId, sup: RoleId) {
    arenas.role_mut(sub).super_roles.push(NegLink {
        target: sup,
        negated: false,
    });
    arenas.role_mut(sub).indirect_super_roles.push(NegLink {
        target: sup,
        negated: false,
    });
}

/// `elements[0] ∘ … ∘ elements[n-1] ⊑ super_role`: the chain object, the
/// super-sharing linker, and the complexity marking (the chain's super role
/// and all ITS indirect supers become complex, as
/// `CSubroleTransformationPreProcess` does).
fn add_chain(arenas: &mut OntologyArenas, elements: &[RoleId], super_role: RoleId) -> RoleChainId {
    let mut rc = RoleChain::new();
    for &e in elements {
        rc.append_role_chain_linker(e);
    }
    let id = arenas.alloc_role_chain(rc);
    let tag = id.index() as Cint64;
    arenas.role_chain_mut(id).set_role_chain_tag(tag);
    arenas
        .role_mut(super_role)
        .add_role_chain_super_sharing_linker(id);
    let sups: Vec<RoleId> = arenas
        .role(super_role)
        .indirect_super_roles
        .iter()
        .map(|l| l.target)
        .collect();
    for s in sups {
        arenas.role_mut(s).set_role_complexity(true);
    }
    arenas.role_mut(super_role).set_role_complexity(true);
    id
}

/// `Trans(r)` — the transitive flag plus the `r ∘ r ⊑ r` chain (Konclude
/// models transitivity as exactly this chain).
fn make_transitive(arenas: &mut OntologyArenas, r: RoleId) {
    arenas.role_mut(r).set_transitive(true);
    add_chain(arenas, &[r, r], r);
}

/// A fresh concept with tag == arena index.
fn alloc_con(arenas: &mut OntologyArenas, opcode: Cint64) -> ConceptId {
    let tag = arenas.concept_count();
    let mut c = Concept::new();
    c.set_concept_tag(tag);
    c.set_operator_code(opcode);
    arenas.alloc_concept(c)
}

fn atom(arenas: &mut OntologyArenas) -> ConceptId {
    alloc_con(arenas, op::CCATOM)
}

/// `∀role.(filler^neg)` / `∃role.(filler^neg)` by opcode.
fn quantified(
    arenas: &mut OntologyArenas,
    opcode: Cint64,
    role: RoleId,
    filler: ConceptId,
    neg: bool,
) -> ConceptId {
    let id = alloc_con(arenas, opcode);
    let c = arenas.concept_mut(id);
    c.set_role(role);
    c.add_operand_linker(filler, neg);
    c.set_operand_count(1);
    id
}

fn ops_of(arenas: &OntologyArenas, c: ConceptId) -> Vec<(ConceptId, bool)> {
    arenas
        .concept(c)
        .get_operand_list()
        .iter()
        .map(|l| (l.target, l.negated))
        .collect()
}

fn op_code(arenas: &OntologyArenas, c: ConceptId) -> Cint64 {
    arenas.concept(c).get_operator_code()
}

/// The single positive operand of `c` whose opcode is `code` (panics with
/// context otherwise).
fn the_operand_with_code(arenas: &OntologyArenas, c: ConceptId, code: Cint64) -> ConceptId {
    let hits: Vec<ConceptId> = ops_of(arenas, c)
        .into_iter()
        .filter(|&(t, n)| !n && op_code(arenas, t) == code)
        .map(|(t, _)| t)
        .collect();
    assert_eq!(
        hits.len(),
        1,
        "expected exactly one positive operand with opcode {} on concept {:?}, found {}",
        code,
        c,
        hits.len()
    );
    hits[0]
}

fn run_preprocess(arenas: &mut OntologyArenas) -> RoleChainAutomataTransformationPreProcess {
    let mut pre = RoleChainAutomataTransformationPreProcess::new();
    pre.preprocess(arenas);
    pre
}

// ===========================================================================
// STRUCTURE tests — the exact automaton Konclude builds
// ===========================================================================

/// `Trans(R)`, `∀R.C` — the pure-transitivity automaton: the concept becomes
/// `CCAQCHOOCE [(gen, ¬), (begin, +)]`; `gen` is `CCAQSOME R [(C, ¬)]`;
/// `begin` fires `CCAQALL R` into `end`; `end` carries `C` AND the ε-loop
/// operand `begin` (the `R ∘ R ⊑ R` chain reduces to end → begin).
#[test]
fn transitive_forall_builds_epsilon_loop() {
    let mut arenas = OntologyArenas::new();
    seed_arenas(&mut arenas);
    let r = mk_role(&mut arenas);
    make_transitive(&mut arenas, r);
    let c = atom(&mut arenas);
    let all_rc = quantified(&mut arenas, op::CCALL, r, c, false);

    let pre = run_preprocess(&mut arenas);
    assert_eq!(pre.stat_automate_transformed_concept_count, 1);

    assert_eq!(op_code(&arenas, all_rc), op::CCAQCHOOCE);
    let choose_ops = ops_of(&arenas, all_rc);
    assert_eq!(choose_ops.len(), 2, "CHOOCE carries generator + begin state");
    // generator appended first with !existNegation (= true for ∀).
    let (gen, gen_neg) = choose_ops[0];
    let (begin, begin_neg) = choose_ops[1];
    assert!(gen_neg, "the CCAQSOME generator operand is negated for a ∀");
    assert!(!begin_neg, "the begin state operand is positive for a ∀");
    assert_eq!(op_code(&arenas, gen), op::CCAQSOME);
    assert_eq!(arenas.concept(gen).get_role(), r);
    assert_eq!(
        ops_of(&arenas, gen),
        vec![(c, true)],
        "generator operands are the original fillers negated (opNeg ^ !existNeg)"
    );

    assert_eq!(op_code(&arenas, begin), op::CCAQAND);
    let prop = the_operand_with_code(&arenas, begin, op::CCAQALL);
    assert_eq!(arenas.concept(prop).get_role(), r);
    let end = the_operand_with_code(&arenas, prop, op::CCAQAND);
    let end_ops = ops_of(&arenas, end);
    assert_eq!(
        end_ops,
        vec![(c, false), (begin, false)],
        "end state = original filler + the transitive ε-loop back to begin"
    );
}

/// `R ∘ S ⊑ T`, `∀T.C` — the chain automaton: beginT fires `CCAQALL T`
/// directly into endT AND glues in the linear sub-automaton
/// beginT → subBeginR --R--> subEndR → subBeginS --S--> subEndS → endT.
#[test]
fn chain_forall_builds_linear_sub_automaton() {
    let mut arenas = OntologyArenas::new();
    seed_arenas(&mut arenas);
    let r = mk_role(&mut arenas);
    let s = mk_role(&mut arenas);
    let t = mk_role(&mut arenas);
    add_chain(&mut arenas, &[r, s], t);
    let c = atom(&mut arenas);
    let all_tc = quantified(&mut arenas, op::CCALL, t, c, false);

    run_preprocess(&mut arenas);

    assert_eq!(op_code(&arenas, all_tc), op::CCAQCHOOCE);
    let begin_t = {
        let ops = ops_of(&arenas, all_tc);
        assert_eq!(ops.len(), 2);
        ops[1].0
    };
    assert_eq!(op_code(&arenas, begin_t), op::CCAQAND);
    let begin_ops = ops_of(&arenas, begin_t);
    assert_eq!(
        begin_ops.len(),
        2,
        "beginT = the direct T transition + the glued chain entry subBeginR"
    );
    let prop_t = begin_ops[0].0;
    assert_eq!(op_code(&arenas, prop_t), op::CCAQALL);
    assert_eq!(arenas.concept(prop_t).get_role(), t);
    let end_t = the_operand_with_code(&arenas, prop_t, op::CCAQAND);
    assert_eq!(
        ops_of(&arenas, end_t),
        vec![(c, false)],
        "no ε-loop for a plain (non-transitive-super) chain"
    );

    // the glued chain: subBeginR --AQALL(R)--> subEndR --ε--> subBeginS
    //                  --AQALL(S)--> subEndS --ε--> endT.
    let sub_begin_r = begin_ops[1].0;
    assert_eq!(op_code(&arenas, sub_begin_r), op::CCAQAND);
    let prop_r = the_operand_with_code(&arenas, sub_begin_r, op::CCAQALL);
    assert_eq!(arenas.concept(prop_r).get_role(), r);
    let sub_end_r = the_operand_with_code(&arenas, prop_r, op::CCAQAND);
    let sub_begin_s = the_operand_with_code(&arenas, sub_end_r, op::CCAQAND);
    let prop_s = the_operand_with_code(&arenas, sub_begin_s, op::CCAQALL);
    assert_eq!(arenas.concept(prop_s).get_role(), s);
    let sub_end_s = the_operand_with_code(&arenas, prop_s, op::CCAQAND);
    assert_eq!(
        ops_of(&arenas, sub_end_s),
        vec![(end_t, false)],
        "the chain exit connects to endT"
    );
}

/// `S ∘ R ⊑ R` (last element == super role): the transEnd wiring loops the
/// chain THROUGH the begin state — begin += subBeginS and subEndS += begin.
#[test]
fn trans_end_chain_loops_through_begin() {
    let mut arenas = OntologyArenas::new();
    seed_arenas(&mut arenas);
    let r = mk_role(&mut arenas);
    let s = mk_role(&mut arenas);
    add_chain(&mut arenas, &[s, r], r);
    let c = atom(&mut arenas);
    let all_rc = quantified(&mut arenas, op::CCALL, r, c, false);

    run_preprocess(&mut arenas);

    let begin = ops_of(&arenas, all_rc)[1].0;
    let begin_ops = ops_of(&arenas, begin);
    assert_eq!(begin_ops.len(), 2, "begin = R transition + chain entry");
    let sub_begin_s = begin_ops[1].0;
    let prop_s = the_operand_with_code(&arenas, sub_begin_s, op::CCAQALL);
    assert_eq!(arenas.concept(prop_s).get_role(), s);
    let sub_end_s = the_operand_with_code(&arenas, prop_s, op::CCAQAND);
    assert_eq!(
        ops_of(&arenas, sub_end_s),
        vec![(begin, false)],
        "transEnd: after the S hop the automaton is back at begin (an R hop must follow)"
    );
}

/// `R ∘ S ⊑ R` (first element == super role): the transStart wiring hangs the
/// chain off the END state — end += subBeginS and subEndS += end.
#[test]
fn trans_start_chain_loops_through_end() {
    let mut arenas = OntologyArenas::new();
    seed_arenas(&mut arenas);
    let r = mk_role(&mut arenas);
    let s = mk_role(&mut arenas);
    add_chain(&mut arenas, &[r, s], r);
    let c = atom(&mut arenas);
    let all_rc = quantified(&mut arenas, op::CCALL, r, c, false);

    run_preprocess(&mut arenas);

    let begin = ops_of(&arenas, all_rc)[1].0;
    let prop_r = the_operand_with_code(&arenas, begin, op::CCAQALL);
    assert_eq!(arenas.concept(prop_r).get_role(), r);
    let end = the_operand_with_code(&arenas, prop_r, op::CCAQAND);
    let end_ops = ops_of(&arenas, end);
    assert_eq!(
        end_ops.len(),
        2,
        "end state = the filler + the transStart chain entry"
    );
    assert_eq!(end_ops[0], (c, false));
    let sub_begin_s = end_ops[1].0;
    let prop_s = the_operand_with_code(&arenas, sub_begin_s, op::CCAQALL);
    assert_eq!(arenas.concept(prop_s).get_role(), s);
    let sub_end_s = the_operand_with_code(&arenas, prop_s, op::CCAQAND);
    assert_eq!(
        ops_of(&arenas, sub_end_s),
        vec![(end, false)],
        "transStart: after the S hop the automaton re-reaches end"
    );
}

/// `∃R (CCSOME)` on a complex role gets the DUAL automaton: the generator is
/// appended POSITIVELY (existNegation = true ⇒ !existNegation = false) and the
/// begin state NEGATED; end-state fillers flip polarity.
#[test]
fn exists_on_complex_role_uses_dual_polarity() {
    let mut arenas = OntologyArenas::new();
    seed_arenas(&mut arenas);
    let r = mk_role(&mut arenas);
    make_transitive(&mut arenas, r);
    let c = atom(&mut arenas);
    let some_rc = quantified(&mut arenas, op::CCSOME, r, c, false);

    run_preprocess(&mut arenas);

    assert_eq!(op_code(&arenas, some_rc), op::CCAQCHOOCE);
    let ops = ops_of(&arenas, some_rc);
    let (gen, gen_neg) = ops[0];
    let (_begin, begin_neg) = ops[1];
    assert!(!gen_neg, "∃: the CCAQSOME generator operand is positive");
    assert!(begin_neg, "∃: the begin state operand is negated");
    assert_eq!(
        ops_of(&arenas, gen),
        vec![(c, false)],
        "∃ generator keeps the original filler polarity"
    );
}

/// `hasValue` (`CCVALUE`) on a complex role is rewritten to `∃R.{o}` — a
/// `CCSOME` over the individual's fresh `CCNOMINAL` concept — and then
/// converted by the ∀/∃ pass like any other `CCSOME`.
#[test]
fn has_value_on_complex_role_rewritten_to_nominal_exists() {
    let mut arenas = OntologyArenas::new();
    seed_arenas(&mut arenas);
    let r = mk_role(&mut arenas);
    make_transitive(&mut arenas, r);
    let ind = arenas.alloc_individual(Individual::new(7));
    let value_con = {
        let id = alloc_con(&mut arenas, op::CCVALUE);
        let c = arenas.concept_mut(id);
        c.set_role(r);
        c.set_nominal_individual(ind);
        id
    };

    run_preprocess(&mut arenas);

    // transform_value_restrictions turned it into ∃R.{o}, then the ∀/∃ pass
    // turned THAT into the CHOOCE automaton whose generator carries {o}.
    assert_eq!(op_code(&arenas, value_con), op::CCAQCHOOCE);
    let gen = ops_of(&arenas, value_con)[0].0;
    assert_eq!(op_code(&arenas, gen), op::CCAQSOME);
    let nom = ops_of(&arenas, gen)[0].0;
    assert_eq!(op_code(&arenas, nom), op::CCNOMINAL);
    assert_eq!(arenas.concept(nom).get_nominal_individual(), ind);
    assert_eq!(
        arenas.individual(ind).get_individual_nominal_concept(),
        nom,
        "the nominal concept is cached on the individual"
    );
}

/// A range concept on a chain super role `T` (with `R ∘ S ⊑ T`) creates the
/// chain-FIRST domain propagation: a `CCALL`-shaped `∀T.Rg` transition concept
/// installed in R's DOMAIN list, so the range constraint reaches paths that
/// only become T-edges through the chain.
#[test]
fn range_on_chain_super_role_creates_domain_propagation() {
    let mut arenas = OntologyArenas::new();
    seed_arenas(&mut arenas);
    let r = mk_role(&mut arenas);
    let s = mk_role(&mut arenas);
    let t = mk_role(&mut arenas);
    add_chain(&mut arenas, &[r, s], t);
    let rg = atom(&mut arenas);
    arenas.role_mut(t).add_range_concept_linker(NegLink {
        target: rg,
        negated: false,
    });

    let pre = run_preprocess(&mut arenas);
    assert!(pre.stat_created_range_propagation_count >= 1);

    let dom_list: Vec<(ConceptId, bool)> = arenas
        .role(r)
        .get_domain_concept_list()
        .iter()
        .map(|l| (l.target, l.negated))
        .collect();
    // The created ∀T.Rg is itself a CCALL on a COMPLEX role, so the final
    // transformFORALLPropagations pass converts IT into a CHOOCE automaton —
    // that ordering is the point of running dom/range propagation first.
    let prop = dom_list
        .iter()
        .find(|&&(dc, neg)| !neg && op_code(&arenas, dc) == op::CCAQCHOOCE)
        .map(|&(dc, _)| dc)
        .expect("the propagation concept (automaton-converted ∀T.Rg) must be in R's domain list");
    let begin = ops_of(&arenas, prop)[1].0;
    let prop_t = the_operand_with_code(&arenas, begin, op::CCAQALL);
    assert_eq!(arenas.concept(prop_t).get_role(), t);
    let end = the_operand_with_code(&arenas, prop_t, op::CCAQAND);
    assert!(
        ops_of(&arenas, end).contains(&(rg, false)),
        "the automaton's end state must carry the propagated range concept Rg"
    );
}

/// The PURE-transitivity case must create NO propagation: for `R ∘ R ⊑ R` the
/// chain's last/first element IS `R`, whose range/domain already carries the
/// concept — Konclude's `hasPropagatedConcept` dedup guard skips it.
#[test]
fn range_on_transitive_role_propagation_correctly_skipped() {
    let mut arenas = OntologyArenas::new();
    seed_arenas(&mut arenas);
    let r = mk_role(&mut arenas);
    make_transitive(&mut arenas, r);
    let rg = atom(&mut arenas);
    arenas.role_mut(r).add_range_concept_linker(NegLink {
        target: rg,
        negated: false,
    });

    let pre = run_preprocess(&mut arenas);
    assert_eq!(
        pre.stat_created_range_propagation_count, 0,
        "R∘R⊑R: the range is already on the last element's super (R itself)"
    );
    assert!(
        pre.stat_propagated_already_in_domain_range_count >= 1,
        "the skip must come from the hasPropagatedConcept dedup guard"
    );
}

// ===========================================================================
// END-TO-END tests — preprocessor output driven through the completion engine
// ===========================================================================

/// The classify_test-style per-test environment, with the specialized automat
/// rules ON (Konclude's production configuration for this machinery).
struct Env {
    algo: CompletionTaskHandleAlgorithm,
    ctx: CalculationAlgorithmContextBase,
    next_indi_id: i64,
}

fn build_env() -> Env {
    let mut algo = CompletionTaskHandleAlgorithm::new();
    algo.conf_specialized_automate_rules = true;
    let mut ctx = CalculationAlgorithmContextBase::new();
    ctx.base.used_concept_priority_strategy =
        Some(ConceptProcessingPriorityStrategy::new_concrete_operator());
    let top = seed_arenas(ctx.ontology_arenas_mut());
    ctx.processing_data_box_mut().ontology_top_concept = top;
    Env {
        algo,
        ctx,
        next_indi_id: 0,
    }
}

impl Env {
    fn arenas(&mut self) -> &mut OntologyArenas {
        self.ctx.ontology_arenas_mut()
    }

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

    /// Add `concept` to the node's label set + processing queue the natural way.
    fn add(&mut self, node: &mut NodeId, concept: ConceptId, negated: bool) {
        self.algo.add_concept_to_individual(
            concept,
            negated,
            node,
            TrackPointId::NONE,
            false,
            true,
            &mut self.ctx,
        );
    }

    fn seed_concept_on_queue(&mut self, root: NodeId, concept: ConceptId) {
        let queue = self
            .ctx
            .process_context_mut()
            .node_concept_processing_queue(root, true);
        let con_des = self
            .ctx
            .process_context_mut()
            .alloc_con_desc(ConceptDescriptor::new());
        self.ctx.process_context_mut().con_desc_mut(con_des).concept = concept;
        let mut cpd_val = ConceptProcessDescriptor::new();
        cpd_val.concept_des = con_des;
        cpd_val.priority = ConceptProcessPriority::new(8.0);
        let cpd = self.ctx.process_context_mut().alloc_con_proc_desc(cpd_val);
        ConceptProcessingQueue::insert_concept_process_descriptor(
            queue,
            cpd,
            self.ctx.process_context_mut(),
        );
    }

    fn seed_root_immediate(&mut self, root: NodeId) {
        let iq = self.ctx.get_individual_immediately_processing_queue(true);
        self.ctx
            .process_context_mut()
            .indi_unsorted_proc_queue_mut(iq)
            .insert_indiviudal_process_node(root);
    }

    fn run(&mut self) -> bool {
        self.algo.run_completion_on(&mut self.ctx)
    }
}

/// `Trans(R)`: `∀R.¬C ⊓ ∃R.∃R.C` is INCONSISTENT — the automaton must chase
/// the ∀ across TWO hops (the ε-loop re-arms the begin state on every
/// R-successor).
#[test]
fn e2e_transitive_forall_two_hop_clash() {
    let mut env = build_env();
    let r = mk_role(env.arenas());
    make_transitive(env.arenas(), r);
    let c = atom(env.arenas());
    let all_not_c = quantified(env.arenas(), op::CCALL, r, c, true);
    let some_rc = quantified(env.arenas(), op::CCSOME, r, c, false);
    let some_r_some_rc = quantified(env.arenas(), op::CCSOME, r, some_rc, false);
    let mut pre = RoleChainAutomataTransformationPreProcess::new();
    pre.preprocess(env.arenas());

    let mut root = env.make_root();
    env.add(&mut root, all_not_c, false);
    env.seed_concept_on_queue(root, some_r_some_rc);
    env.seed_root_immediate(root);

    let consistent = env.run();
    assert!(
        !consistent,
        "Trans(R): ∀R.¬C ⊓ ∃R.∃R.C must CLASH (¬C reaches the 2nd hop through the automaton)"
    );
}

/// Transitivity control: the second hop on an UNRELATED role stays out of the
/// automaton's reach — consistent.
#[test]
fn e2e_transitive_forall_unrelated_role_consistent() {
    let mut env = build_env();
    let r = mk_role(env.arenas());
    let s = mk_role(env.arenas());
    make_transitive(env.arenas(), r);
    let c = atom(env.arenas());
    let all_not_c = quantified(env.arenas(), op::CCALL, r, c, true);
    let some_sc = quantified(env.arenas(), op::CCSOME, s, c, false);
    let some_r_some_sc = quantified(env.arenas(), op::CCSOME, r, some_sc, false);
    let mut pre = RoleChainAutomataTransformationPreProcess::new();
    pre.preprocess(env.arenas());

    let mut root = env.make_root();
    env.add(&mut root, all_not_c, false);
    env.seed_concept_on_queue(root, some_r_some_sc);
    env.seed_root_immediate(root);

    let consistent = env.run();
    assert!(
        consistent,
        "∀R.¬C ⊓ ∃R.∃S.C (S unrelated) must stay consistent"
    );
}

/// Sub-role into transitive (`S ⊑ R`, `Trans(R)`): S-edges must count as
/// R-hops for the automaton — the hierarchy-resolved successor lookup / edge
/// reapply is on the critical path here.
#[test]
fn e2e_subrole_edges_feed_transitive_automaton() {
    let mut env = build_env();
    let r = mk_role(env.arenas());
    let s = mk_role(env.arenas());
    add_super_role(env.arenas(), s, r);
    make_transitive(env.arenas(), r);
    let c = atom(env.arenas());
    let all_not_c = quantified(env.arenas(), op::CCALL, r, c, true);
    let some_sc = quantified(env.arenas(), op::CCSOME, s, c, false);
    let some_s_some_sc = quantified(env.arenas(), op::CCSOME, s, some_sc, false);
    let mut pre = RoleChainAutomataTransformationPreProcess::new();
    pre.preprocess(env.arenas());

    let mut root = env.make_root();
    env.add(&mut root, all_not_c, false);
    env.seed_concept_on_queue(root, some_s_some_sc);
    env.seed_root_immediate(root);

    let consistent = env.run();
    assert!(
        !consistent,
        "S ⊑ R, Trans(R): ∀R.¬C ⊓ ∃S.∃S.C must CLASH (S-hops are R-hops)"
    );
}

/// Role chain `R ∘ S ⊑ T`: `∀T.¬C ⊓ ∃R.∃S.C` clashes — and ONLY in that
/// order: `∃S.∃R.C` (the control below) must stay consistent. This is the
/// order-sensitivity that separates a real chain automaton from a blanket
/// role-hierarchy hack.
#[test]
fn e2e_role_chain_order_sensitive_clash() {
    let mut env = build_env();
    let r = mk_role(env.arenas());
    let s = mk_role(env.arenas());
    let t = mk_role(env.arenas());
    add_chain(env.arenas(), &[r, s], t);
    let c = atom(env.arenas());
    let all_not_c = quantified(env.arenas(), op::CCALL, t, c, true);
    let some_sc = quantified(env.arenas(), op::CCSOME, s, c, false);
    let some_r_some_sc = quantified(env.arenas(), op::CCSOME, r, some_sc, false);
    let mut pre = RoleChainAutomataTransformationPreProcess::new();
    pre.preprocess(env.arenas());

    let mut root = env.make_root();
    env.add(&mut root, all_not_c, false);
    env.seed_concept_on_queue(root, some_r_some_sc);
    env.seed_root_immediate(root);

    let consistent = env.run();
    assert!(
        !consistent,
        "R∘S ⊑ T: ∀T.¬C ⊓ ∃R.∃S.C must CLASH (the chain composes to a T-edge)"
    );
}

/// The chain-order CONTROL: hops in the wrong order (`∃S.∃R.C`) do NOT
/// compose to a T-edge — must stay consistent.
#[test]
fn e2e_role_chain_wrong_order_consistent() {
    let mut env = build_env();
    let r = mk_role(env.arenas());
    let s = mk_role(env.arenas());
    let t = mk_role(env.arenas());
    add_chain(env.arenas(), &[r, s], t);
    let c = atom(env.arenas());
    let all_not_c = quantified(env.arenas(), op::CCALL, t, c, true);
    let some_rc = quantified(env.arenas(), op::CCSOME, r, c, false);
    let some_s_some_rc = quantified(env.arenas(), op::CCSOME, s, some_rc, false);
    let mut pre = RoleChainAutomataTransformationPreProcess::new();
    pre.preprocess(env.arenas());

    let mut root = env.make_root();
    env.add(&mut root, all_not_c, false);
    env.seed_concept_on_queue(root, some_s_some_rc);
    env.seed_root_immediate(root);

    let consistent = env.run();
    assert!(
        consistent,
        "R∘S ⊑ T: ∀T.¬C ⊓ ∃S.∃R.C (wrong hop order) must stay consistent"
    );
}

/// The ore_ont_14817 shape: `Trans(partOf)`, `regionalPartOf ⊑ partOf` —
/// `∀partOf.¬C ⊓ ∃regionalPartOf.∃partOf.C` must clash (a regionalPartOf hop
/// followed by a partOf hop IS a partOf path).
#[test]
fn e2e_part_of_shape_14817() {
    let mut env = build_env();
    let part_of = mk_role(env.arenas());
    let regional_part_of = mk_role(env.arenas());
    add_super_role(env.arenas(), regional_part_of, part_of);
    make_transitive(env.arenas(), part_of);
    let c = atom(env.arenas());
    let all_not_c = quantified(env.arenas(), op::CCALL, part_of, c, true);
    let some_pc = quantified(env.arenas(), op::CCSOME, part_of, c, false);
    let some_rp_some_pc = quantified(env.arenas(), op::CCSOME, regional_part_of, some_pc, false);
    let mut pre = RoleChainAutomataTransformationPreProcess::new();
    pre.preprocess(env.arenas());

    let mut root = env.make_root();
    env.add(&mut root, all_not_c, false);
    env.seed_concept_on_queue(root, some_rp_some_pc);
    env.seed_root_immediate(root);

    let consistent = env.run();
    assert!(
        !consistent,
        "14817 shape: ∀partOf.¬C ⊓ ∃regionalPartOf.∃partOf.C must CLASH"
    );
}

/// Existing-successors path (the AQALL arm of `apply_automat_transactions`
/// proper, not the edge-triggered reapply): grow the two-hop R-path FIRST,
/// then add the automaton — the state must propagate over the edges that are
/// already there.
#[test]
fn e2e_automaton_over_preexisting_successors() {
    let mut env = build_env();
    let r = mk_role(env.arenas());
    make_transitive(env.arenas(), r);
    let c = atom(env.arenas());
    let all_not_c = quantified(env.arenas(), op::CCALL, r, c, true);
    let some_rc = quantified(env.arenas(), op::CCSOME, r, c, false);
    let some_r_some_rc = quantified(env.arenas(), op::CCSOME, r, some_rc, false);
    let mut pre = RoleChainAutomataTransformationPreProcess::new();
    pre.preprocess(env.arenas());

    let mut root = env.make_root();
    // Pass 1: build the R-path root → n1 → n2 with C on n2. Consistent.
    env.seed_concept_on_queue(root, some_r_some_rc);
    env.seed_root_immediate(root);
    assert!(env.run(), "the bare ∃R.∃R.C path is consistent");

    // Pass 2: NOW add the ∀ automaton on the root — it must walk the
    // pre-existing edges to reach n2.
    env.add(&mut root, all_not_c, false);
    env.seed_root_immediate(root);
    let consistent = env.run();
    assert!(
        !consistent,
        "adding ∀R.¬C after the R-path exists must still CLASH via the AQALL successor walk"
    );
}
