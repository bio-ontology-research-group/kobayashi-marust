//! # Bridge: `TInput` (cb_to_ht HtClauses) → `OntologyArenas`
//!
//! The production-route input builder for `konclude_ht` — maps KM's
//! reverse-Skolemized HT clause form (`orchestrate::cb_to_ht::TInput`, the
//! same input the fast Ht consumes) onto Konclude-style concept structures
//! (`CCATOM`/`CCIMPL`/`CCOR`/`CCALL`/`CCSOME` operand trees): exactly the
//! encoding `completion::classify_test`'s `Env` builds programmatically, so
//! everything the completion engine already runs (implication unfolding, the
//! OR rule + the sound same-node backtrack, ∃/∀ successor rules) applies
//! unchanged to bridged ontologies.
//!
//! KEPT OUT OF THE PRODUCTION CLASSIFY PATH until verdict parity vs the
//! existing engines is established across the corpus — the bridge and its
//! driver are only reachable from tests today (nothing in `orchestrate` calls
//! them). Coverage is v1-PARTIAL and every clause the encoder cannot express
//! is COUNTED in [`Bridged::unsupported`]; a caller must treat
//! `unsupported > 0` as "the bridged ontology is an UNDER-approximation" —
//! satisfiable verdicts are then not trustworthy (missing constraints), while
//! clash verdicts remain sound (all encoded concepts are faithful).
//!
//! v1 clause coverage (one implication concept per clause, seeded per pass by
//! the re-drive loop exactly like the classify_test GCI harness):
//!   - concept-only clauses over the clause root variable:
//!     `C1 ∧ … ∧ Cn → D1 ∨ … ∨ Dm`  ⇒  `CCIMPL[ head, ¬C1, …, ¬Cn ]` with
//!     `head = Dm | CCOR[D1..Dm] | CCBOTTOM` (heads may be `Exist` ⇒ `CCSOME`);
//!   - single-role-body clauses `…C(0)… ∧ R(0,1) ∧ …D(1)… → …E(0)… ∨ …F(1)…`
//!     ⇒  `CCIMPL[ CCOR[E…, CCALL(R, CCOR[¬D…, F…])], ¬C… ]`
//!     (the standard `∀`-form of a guarded two-variable clause);
//!   - everything else (multiple role atoms, head role atoms / role
//!     hierarchy, `Eq`, body `Exist`, nominals, card_defs, chains) counts as
//!     unsupported in v1.
use std::collections::BTreeSet;

use super::completion::algorithm::CompletionTaskHandleAlgorithm;
use super::completion::context::CalculationAlgorithmContextBase;
use super::model::concept::Concept;
use super::model::op;
use super::model::role::Role;
use super::model::substrate::{Cint64, Id};
use super::model::{ConceptId, RoleId};
use super::process::descriptor::{
    ConceptDescriptor, ConceptProcessDescriptor, ConceptProcessPriority,
};
use super::process::node::IndividualProcessNode;
use super::process::queues::ConceptProcessingQueue;
use super::process::{NodeId, TrackPointId};
use crate::orchestrate::cb_to_ht::{HAtom, HtClause, TInput};

/// The bridged terminology: arena ids for the TInput's named concepts/roles
/// plus the per-clause implication concepts the probe driver re-seeds.
pub struct Bridged {
    /// `named[i]` = the `CCATOM` concept for `TInput.concepts[i]`.
    pub named: Vec<ConceptId>,
    /// `roles[i]` = the arena role for `TInput.roles[i]`.
    pub roles: Vec<RoleId>,
    /// One implication (`CCIMPL`) concept per encoded clause — the TBox the
    /// driver seeds on every re-drive pass (the classify_test GCI harness
    /// pattern; stands in for the unported condensed reapply queue).
    pub tbox: Vec<ConceptId>,
    /// Clauses the v1 encoder could NOT express. `> 0` ⇒ the bridged ontology
    /// under-approximates the input: "satisfiable" verdicts are unreliable.
    pub unsupported: usize,
    /// Implications absorbed onto their first positive trigger concept
    /// (`CCATOM` host promoted to `CCSUB`; see the attachment pass) — these
    /// are unfolded only in nodes whose label contains the trigger.
    pub absorbed: usize,
    /// Implications with no positive concept trigger, attached to the
    /// ontology TOP concept (scanned by EVERY node).
    pub top_attached: usize,
}

/// Tag base for bridged concepts (tag 1 is the ontology TOP sentinel).
const TAG_BASE: Cint64 = 10;

struct Builder<'a> {
    ctx: &'a mut CalculationAlgorithmContextBase,
    next_tag: Cint64,
}

impl<'a> Builder<'a> {
    fn fresh_tag(&mut self) -> Cint64 {
        let t = self.next_tag;
        self.next_tag += 1;
        t
    }
    fn atom(&mut self, tag: Cint64) -> ConceptId {
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op::CCATOM);
        self.ctx.ontology_arenas_mut().alloc_concept(c)
    }
    /// `CCOR` over `ops` — or the single operand itself (collapsed; the
    /// caller keeps the operand's negation in that case).
    fn or_of(&mut self, ops: &[(ConceptId, bool)]) -> (ConceptId, bool) {
        if ops.len() == 1 {
            return ops[0];
        }
        let tag = self.fresh_tag();
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op::CCOR);
        for &(o, n) in ops {
            c.add_operand_linker(o, n);
        }
        c.set_operand_count(ops.len() as i64);
        (self.ctx.ontology_arenas_mut().alloc_concept(c), false)
    }
    fn bottom(&mut self) -> ConceptId {
        let tag = self.fresh_tag();
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op::CCBOTTOM);
        self.ctx.ontology_arenas_mut().alloc_concept(c)
    }
    fn some(&mut self, role: RoleId, filler: (ConceptId, bool)) -> ConceptId {
        let tag = self.fresh_tag();
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op::CCSOME);
        c.set_role(role);
        c.add_operand_linker(filler.0, filler.1);
        c.set_operand_count(1);
        self.ctx.ontology_arenas_mut().alloc_concept(c)
    }
    fn all(&mut self, role: RoleId, filler: (ConceptId, bool)) -> ConceptId {
        let tag = self.fresh_tag();
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op::CCALL);
        c.set_role(role);
        c.add_operand_linker(filler.0, filler.1);
        c.set_operand_count(1);
        self.ctx.ontology_arenas_mut().alloc_concept(c)
    }
    /// `CCIMPL[ head, triggers… ]` — fires `head` once every trigger concept
    /// is present with the OPPOSITE polarity of its linker (see
    /// `apply_implication_rule`): a positive body atom becomes a NEGATED
    /// trigger linker.
    fn implication(&mut self, head: (ConceptId, bool), triggers: &[(ConceptId, bool)]) -> ConceptId {
        let tag = self.fresh_tag();
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op::CCIMPL);
        c.add_operand_linker(head.0, head.1);
        for &(t, body_neg) in triggers {
            // body atom `C` (body_neg=false) triggers on POSITIVE presence ⇒
            // linker negated=true (the `¬sub` convention); `¬C` the reverse.
            c.add_operand_linker(t, !body_neg);
        }
        c.set_operand_count(1 + triggers.len() as i64);
        self.ctx.ontology_arenas_mut().alloc_concept(c)
    }
}

/// Build the bridged terminology for `tin` into `ctx`'s ontology arenas.
///
/// The context must be freshly constructed (the bridge owns tag allocation
/// from [`TAG_BASE`]; the TOP sentinel at tag 1 is seeded by the caller
/// exactly as `classify_test::new_env` does).
pub fn bridge_tinput(ctx: &mut CalculationAlgorithmContextBase, tin: &TInput) -> Bridged {
    let mut b = Builder {
        ctx,
        next_tag: TAG_BASE + tin.concepts.len() as Cint64,
    };
    let named: Vec<ConceptId> = (0..tin.concepts.len())
        .map(|i| b.atom(TAG_BASE + i as Cint64))
        .collect();
    let roles: Vec<RoleId> = (0..tin.roles.len())
        .map(|i| {
            // distinct role tags (tag 1 is the TOP-role sentinel; see the
            // preprocess/automata port notes), offset clear of it.
            let mut r = Role::new();
            r.set_role_tag(100 + i as Cint64);
            b.ctx.ontology_arenas_mut().alloc_role(r)
        })
        .collect();
    // Every bridged role gets a wired inverse (both directions, the
    // `inverse_role_propagation` selftest pattern). Needed by the
    // absorption-shape rewrite below: a y-triggered guarded clause
    // `D(y) ∧ R(x,y) → E(x)` encodes as `D ⊑ ∀R⁻.E`.
    let inv_roles: Vec<RoleId> = (0..tin.roles.len())
        .map(|i| {
            let mut r = Role::new();
            r.set_role_tag(100 + (tin.roles.len() + i) as Cint64);
            r.set_inverse_role(roles[i]);
            let id = b.ctx.ontology_arenas_mut().alloc_role(r);
            b.ctx
                .ontology_arenas_mut()
                .role_mut(roles[i])
                .set_inverse_role(id);
            id
        })
        .collect();

    let mut tbox: Vec<ConceptId> = Vec::new();
    // Absorption bookkeeping (attached after the encode loop): an implication
    // with a positive concept trigger hangs off that trigger's concept; the
    // rest go to TOP.
    let mut absorbed_pairs: Vec<(ConceptId, ConceptId)> = Vec::new();
    let mut top_gcis: Vec<ConceptId> = Vec::new();
    let mut unsupported = 0usize;
    // Structures outside the v1 clause encoder count as unsupported input.
    unsupported += tin.card_defs.len() + tin.nominals.len() + tin.chains.len();
    // Inverse roles are not wired in the v1 bridge (the model supports them;
    // the TInput role-pair plumbing is a later wave) — an ontology carrying
    // them is under-constrained when bridged, so surface that.
    if tin.inverse {
        unsupported += 1;
    }

    // ---- pass 1: role hierarchy `R(x,y) → S(x,y)` --------------------------
    // Collected first and installed as (transitively closed) indirect-super-
    // role linkers on the sub-role — the exact structure the ∀/edge rules and
    // the u08 hierarchy-resolved edge reapply consume (see the
    // `role_hierarchy_forall` selftest and CSubroleTransformationPreProcess).
    let mut sub_super: Vec<Vec<usize>> = vec![Vec::new(); tin.roles.len()];
    let is_hierarchy = |cl: &HtClause| -> Option<(usize, usize)> {
        if cl.body.len() != 1 || cl.head.len() != 1 {
            return None;
        }
        if let (HAtom::Role { r: sr, s: ss, t: st }, HAtom::Role { r: hr, s: hs, t: ht }) =
            (&cl.body[0], &cl.head[0])
        {
            if ss == hs && st == ht && ss != st && sr != hr {
                return Some((*sr, *hr));
            }
        }
        None
    };
    for cl in &tin.clauses {
        if let Some((sub, sup)) = is_hierarchy(cl) {
            sub_super[sub].push(sup);
        }
    }
    // transitive closure per sub-role (small role counts; DFS per role)
    for sub in 0..sub_super.len() {
        let mut seen: BTreeSet<usize> = BTreeSet::new();
        let mut stack: Vec<usize> = sub_super[sub].clone();
        while let Some(s) = stack.pop() {
            if s != sub && seen.insert(s) {
                stack.extend(sub_super[s].iter().copied());
            }
        }
        for s in seen {
            b.ctx
                .ontology_arenas_mut()
                .role_mut(roles[sub])
                .add_indirect_super_role_linker(
                    super::model::substrate::NegLink {
                        target: roles[s],
                        negated: false,
                    },
                );
        }
    }

    'clause: for cl in &tin.clauses {
        // hierarchy clauses were consumed by pass 1
        if is_hierarchy(cl).is_some() {
            continue;
        }
        // ---- classify the clause's variable/role shape -------------------
        let mut body_roles: Vec<(usize, usize, usize)> = Vec::new(); // (r, s, t)
        for a in &cl.body {
            match a {
                HAtom::Role { r, s, t } => body_roles.push((*r, *s, *t)),
                HAtom::Eq { .. } | HAtom::Exist { .. } => {
                    unsupported += 1;
                    continue 'clause;
                }
                HAtom::Concept { .. } => {}
            }
        }
        for a in &cl.head {
            if matches!(a, HAtom::Role { .. } | HAtom::Eq { .. }) {
                unsupported += 1;
                continue 'clause;
            }
        }
        let vars: BTreeSet<usize> = cl
            .body
            .iter()
            .chain(cl.head.iter())
            .flat_map(|a| match a {
                HAtom::Concept { t, .. } | HAtom::Exist { t, .. } => vec![*t],
                HAtom::Role { s, t, .. } => vec![*s, *t],
                HAtom::Eq { s, t } => vec![*s, *t],
            })
            .collect();

        // literal → (concept, negated), positively as written
        let lit = |b: &mut Builder, a: &HAtom| -> (ConceptId, bool) {
            match a {
                HAtom::Concept { neg, c, .. } => (named[*c], *neg),
                HAtom::Exist { r, neg, c, .. } => (b.some(roles[*r], (named[*c], *neg)), false),
                _ => unreachable!("filtered above"),
            }
        };

        if body_roles.is_empty() && vars.iter().all(|&v| v == 0) {
            // ---- pure concept clause over the root variable --------------
            let triggers: Vec<(ConceptId, bool)> = cl
                .body
                .iter()
                .map(|a| match a {
                    HAtom::Concept { neg, c, .. } => (named[*c], *neg),
                    _ => unreachable!("role/eq bodies filtered"),
                })
                .collect();
            let heads: Vec<(ConceptId, bool)> =
                cl.head.iter().map(|a| lit(&mut b, a)).collect();
            let head = if heads.is_empty() {
                (b.bottom(), false)
            } else {
                b.or_of(&heads)
            };
            let imp = b.implication(head, &triggers);
            tbox.push(imp);
            match triggers.iter().find(|&&(_, neg)| !neg) {
                Some(&(host, _)) => absorbed_pairs.push((host, imp)),
                None => top_gcis.push(imp),
            }
            continue;
        }

        if body_roles.len() == 1 {
            // ---- guarded two-variable clause: R(x, y) --------------------
            let (r, s, t) = body_roles[0];
            if s != 0 || t == 0 || vars.iter().any(|&v| v != s && v != t) {
                unsupported += 1;
                continue;
            }
            let mut triggers: Vec<(ConceptId, bool)> = Vec::new(); // at x
            let mut succ_body: Vec<(ConceptId, bool)> = Vec::new(); // at y
            for a in &cl.body {
                if let HAtom::Concept { neg, c, t: at } = a {
                    if *at == 0 {
                        triggers.push((named[*c], *neg));
                    } else {
                        succ_body.push((named[*c], *neg));
                    }
                }
            }
            let mut head_x: Vec<(ConceptId, bool)> = Vec::new();
            let mut head_y: Vec<(ConceptId, bool)> = Vec::new();
            for a in &cl.head {
                let at = match a {
                    HAtom::Concept { t, .. } | HAtom::Exist { t, .. } => *t,
                    _ => unreachable!("filtered above"),
                };
                if at == 0 {
                    head_x.push(lit(&mut b, a));
                } else if matches!(a, HAtom::Exist { .. }) {
                    // nested ∃ under the ∀ — out of the v1 fragment
                    unsupported += 1;
                    continue 'clause;
                } else {
                    head_y.push(lit(&mut b, a));
                }
            }
            if !triggers.is_empty() {
                // ---- x-triggered: C ⊑ … ∨ ∀R.(¬D ∨ …) ---------------------
                // ∀R.( ¬D1 ∨ … ∨ F1 ∨ … ) — the y-side residue
                let mut y_ops: Vec<(ConceptId, bool)> = succ_body
                    .iter()
                    .map(|&(c, n)| (c, !n)) // body atoms flip polarity
                    .collect();
                y_ops.extend(head_y.iter().copied());
                let y_disj = if y_ops.is_empty() {
                    (b.bottom(), false)
                } else {
                    b.or_of(&y_ops)
                };
                let all = (b.all(roles[r], y_disj), false);
                let head = if head_x.is_empty() {
                    all
                } else {
                    let mut ops = head_x;
                    ops.push(all);
                    b.or_of(&ops)
                };
                let imp = b.implication(head, &triggers);
                tbox.push(imp);
                match triggers.iter().find(|&&(_, neg)| !neg) {
                    Some(&(host, _)) => absorbed_pairs.push((host, imp)),
                    None => top_gcis.push(imp),
                }
            } else if !succ_body.is_empty() {
                // ---- y-triggered (the absorption shape): ------------------
                // `D(y) ∧ R(x,y) → E(x) ∨ F(y)`  ≡  `D ⊑ F ∨ ∀R⁻.E`
                // (the cb_to_ht definer RECOGNITION direction). Encoded
                // trigger-less it would be a covering disjunction branching
                // on EVERY node (measured: unbounded successor chains); the
                // inverse-∀ form fires only on D-nodes and rides the ported
                // inverse-edge propagation (`inverse_role_propagation`
                // selftest). Konclude reaches the same behaviour through
                // absorption's backward implication triggers.
                let x_disj = if head_x.is_empty() {
                    (b.bottom(), false)
                } else {
                    b.or_of(&head_x)
                };
                let all_inv = (b.all(inv_roles[r], x_disj), false);
                let head = if head_y.is_empty() {
                    all_inv
                } else {
                    let mut ops = head_y;
                    ops.push(all_inv);
                    b.or_of(&ops)
                };
                let imp = b.implication(head, &succ_body);
                tbox.push(imp);
                match succ_body.iter().find(|&&(_, neg)| !neg) {
                    Some(&(host, _)) => absorbed_pairs.push((host, imp)),
                    None => top_gcis.push(imp),
                }
            } else {
                // no concept trigger on either side (`⊤ ⊑ …` over an edge) —
                // out of the v1 fragment (needs the covering-disjunction
                // machinery Konclude gets from absorption + branch triggers).
                unsupported += 1;
            }
            continue;
        }

        unsupported += 1;
    }

    // ---- attachment pass: absorption wiring (Konclude's CCSUB mechanism) ---
    // An implication with a positive concept trigger is attached as an
    // operand of that trigger's concept, whose opcode is promoted CCATOM →
    // CCSUB: positive CCSUB dispatches to the AND rule (mPosJumpFuncVec[CCSUB]
    // = applyANDRule; negated CCSUB is atomaric), so the implication is
    // unfolded ONLY in nodes whose label actually contains the trigger —
    // node-count-independent, exactly how absorbed GCIs hang off named
    // concepts in Konclude. This is what keeps per-node work flat: without it
    // every node scanned the whole TBox through TOP (measured on ore_ont_1016:
    // 388 nodes × 13k TOP impls = the 5M drive cap). Restricting assertion to
    // trigger-nodes is sound AND complete (in a trigger-free node the clause
    // is vacuous — the standard absorption argument; DL-clause bodies are
    // positive atoms). The retained ¬trigger linker inside the CCIMPL is then
    // trivially satisfied at unfold time and the remaining triggers ride the
    // condensed reapply queue (install-to-trigger).
    for &(host, imp) in &absorbed_pairs {
        let c = ctx.ontology_arenas_mut().concept_mut(host);
        if c.get_operator_code() == op::CCATOM {
            c.set_operator_code(op::CCSUB);
        }
        c.add_operand_linker(imp, false);
        c.inc_operand_count(1);
    }

    // Trigger-less implications go to the ontology TOP concept (Konclude's
    // universal-constraint attachment): `CCTOP` dispatches to the AND rule,
    // and `create_new_individual` labels every fresh successor with TOP — so
    // these reach EVERY node. The probe driver still re-seeds the FULL tbox
    // list on the ROOT each pass (root nodes are not created through
    // `create_new_individual`, so they never receive TOP; the re-drive also
    // remains the cross-drive safety net).
    let top = ctx.processing_data_box().ontology_top_concept();
    if top.is_some() {
        let n = top_gcis.len() as i64;
        let top_concept = ctx.ontology_arenas_mut().concept_mut(top);
        for &g in &top_gcis {
            top_concept.add_operand_linker(g, false);
        }
        let count = top_concept.get_operand_count();
        top_concept.set_operand_count(count + n);
    }

    Bridged {
        named,
        roles,
        tbox,
        unsupported,
        absorbed: absorbed_pairs.len(),
        top_attached: top_gcis.len(),
    }
}

// ---------------------------------------------------------------------------
// Probe driver — the classify_test re-drive harness over a bridged TBox.
// ---------------------------------------------------------------------------

/// Konclude's DEFAULT blocking configuration for a probe algorithm — the
/// cpp-constructor (115-118, 157) + `readCalculationConfig` default branch
/// (u31): optimized subset blocking searched through the anywhere linked
/// candidate hash, with lazy exact hashing; `saveCoreBlockingConceptsCandidates`
/// is coupled to the linked search (cpp 741). Without a blocking search the
/// completion NEVER blocks (`get_blocking_individual_node` returns NONE when
/// every search flag is off) and any ∃-cycle or DAG-unrolled successor tree
/// runs into the drive cap — measured on ore_ont_1016's Abdomen probe.
pub fn configure_default_blocking(algo: &mut CompletionTaskHandleAlgorithm) {
    algo.conf_optimized_sub_set_blocking = true;
    algo.conf_anywhere_blocking_linked_candidate_hash_search = true;
    algo.conf_anywhere_blocking_lazy_exact_hashing = true;
    algo.conf_save_core_blocking_concepts_candidates = true;
}

/// Seed `concept` onto `root`'s concept-processing queue at the immediate
/// priority (8) — the classify_test `seed_concept_on_queue`.
fn seed_concept_on_queue(
    ctx: &mut CalculationAlgorithmContextBase,
    root: NodeId,
    concept: ConceptId,
) {
    let queue = ctx
        .process_context_mut()
        .node_concept_processing_queue(root, true);
    let con_des = ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    ctx.process_context_mut().con_desc_mut(con_des).concept = concept;
    let mut cpd_val = ConceptProcessDescriptor::new();
    cpd_val.concept_des = con_des;
    cpd_val.priority = ConceptProcessPriority::new(8.0);
    let cpd = ctx.process_context_mut().alloc_con_proc_desc(cpd_val);
    ConceptProcessingQueue::insert_concept_process_descriptor(
        queue,
        cpd,
        ctx.process_context_mut(),
    );
}

/// A per-probe root/verdict driver over a bridged TBox. `seeds` are the probe
/// concepts (e.g. `[(A, false), (B, true)]` for the `A ⊑ B` unsat test).
/// Returns `Some(true)` iff the probe is UNSATISFIABLE (a genuine Clash),
/// `Some(false)` iff a saturated fixpoint was reached with no clash, and
/// `None` if the drive raised a STOP (e.g. the iteration safety cap) — an
/// UNKNOWN verdict a caller must never fold into either answer.
///
/// Mirrors `classify_test::is_unsatisfiable`: re-seeds the TBox implications
/// each pass (the stand-in for the unported condensed reapply queue) and
/// breaks only on a stable concept count with NO disjunction backtrack in the
/// pass (see `or_backtrack_count`).
pub fn bridged_unsat(
    algo: &mut CompletionTaskHandleAlgorithm,
    ctx: &mut CalculationAlgorithmContextBase,
    bridged: &Bridged,
    next_indi_id: &mut i64,
    seeds: &[(ConceptId, bool)],
) -> Option<bool> {
    ctx.clear_pending_signal();
    algo.or_branch_stack.clear();

    // fresh root node (the classify_test `make_root`)
    let id = *next_indi_id;
    *next_indi_id += 1;
    let mut root = ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    ctx.process_context_mut()
        .node_mut(root)
        .set_individual_node_id(id);
    ctx.processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(id, root);

    for &(concept, negated) in seeds {
        algo.add_concept_to_individual(
            concept,
            negated,
            &mut root,
            TrackPointId::NONE,
            false,
            true,
            ctx,
        );
        if ctx.has_pending_signal() {
            return Some(true);
        }
    }

    let mut prev_count: i64 = -1;
    for _ in 0..256 {
        for &g in &bridged.tbox {
            seed_concept_on_queue(ctx, root, g);
        }
        let iq = ctx.get_individual_immediately_processing_queue(true);
        ctx.process_context_mut()
            .indi_unsorted_proc_queue_mut(iq)
            .insert_indiviudal_process_node(root);
        let backtracks_before = algo.or_backtrack_count;
        let consistent = algo.run_completion_on(ctx);
        if !consistent {
            // A Clash is a genuine UNSAT; a Stop (iteration cap / task fork)
            // is an UNKNOWN — folding it into unsat would be UNSOUND, folding
            // it into sat would be INCOMPLETE.
            return match ctx.pending_signal() {
                super::completion::clash::CalcSignal::Clash(_) => Some(true),
                _ => None,
            };
        }
        let ls = ctx.process_context_mut().node_reapply_concept_label_set(root);
        let count = ctx.process_context().label_set(ls).get_concept_count();
        if count == prev_count && algo.or_backtrack_count == backtracks_before {
            break;
        }
        prev_count = count;
    }
    Some(false)
}

/// Model READ-OFF classification of one named concept.
///
/// Saturates `{named[subject]}` on a fresh root and reads the root label's
/// positive NAMED tags as `subject`'s subsumers — O(1) saturation per
/// concept instead of O(concepts) pairwise probes. VALID only when the
/// saturation is deterministic (`or_backtrack_count` unchanged): one
/// canonical model then captures every consequence, so a named concept in
/// the label IS a subsumer (Horn/EL read-off). On a NON-deterministic
/// subject the single branch is not authoritative — the caller must fall
/// back to pairwise `bridged_unsat` probes over the candidate set.
///
/// Returns `Some(subsumer_indices)` on a deterministic saturation (indices
/// into `bridged.named`, INCLUDING `subject` itself), `None` if the drive
/// STOPped or backtracked (read-off not authoritative). A clash means the
/// subject is unsatisfiable — every concept subsumes it — reported as the
/// full index range.
pub fn bridged_classify_subject(
    algo: &mut CompletionTaskHandleAlgorithm,
    ctx: &mut CalculationAlgorithmContextBase,
    bridged: &Bridged,
    next_indi_id: &mut i64,
    subject: usize,
    n_named: usize,
) -> Option<Vec<usize>> {
    ctx.clear_pending_signal();
    algo.or_branch_stack.clear();

    let id = *next_indi_id;
    *next_indi_id += 1;
    let mut root = ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    ctx.process_context_mut()
        .node_mut(root)
        .set_individual_node_id(id);
    ctx.processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(id, root);

    algo.add_concept_to_individual(
        bridged.named[subject],
        false,
        &mut root,
        TrackPointId::NONE,
        false,
        true,
        ctx,
    );
    if ctx.has_pending_signal() {
        // seed alone clashed ⇒ subject unsatisfiable
        return Some((0..n_named).collect());
    }

    let backtracks_before = algo.or_backtrack_count;
    let mut prev_count: i64 = -1;
    for _ in 0..256 {
        for &g in &bridged.tbox {
            seed_concept_on_queue(ctx, root, g);
        }
        let iq = ctx.get_individual_immediately_processing_queue(true);
        ctx.process_context_mut()
            .indi_unsorted_proc_queue_mut(iq)
            .insert_indiviudal_process_node(root);
        let consistent = algo.run_completion_on(ctx);
        if !consistent {
            return match ctx.pending_signal() {
                super::completion::clash::CalcSignal::Clash(_) => {
                    Some((0..n_named).collect())
                }
                _ => None, // STOP: not authoritative
            };
        }
        let ls = ctx.process_context_mut().node_reapply_concept_label_set(root);
        let count = ctx.process_context().label_set(ls).get_concept_count();
        if count == prev_count {
            break;
        }
        prev_count = count;
    }
    // Non-deterministic saturation ⇒ single branch is not authoritative.
    if algo.or_backtrack_count != backtracks_before {
        return None;
    }

    // Read off positive named tags from the root label.
    let ls = ctx.process_context_mut().node_reapply_concept_label_set(root);
    let mut subsumers: Vec<usize> = Vec::new();
    let entries: Vec<(Cint64, super::process::ConDescId)> = ctx
        .process_context()
        .label_set(ls)
        .concept_des_dep_map
        .iter()
        .map(|(tag, data)| (*tag, data.concept_descriptor))
        .collect();
    for (tag, cd) in entries {
        if tag < TAG_BASE || tag >= TAG_BASE + n_named as Cint64 {
            continue;
        }
        if cd.is_none() {
            continue;
        }
        if ctx.process_context().con_desc(cd).is_negated() {
            continue;
        }
        subsumers.push((tag - TAG_BASE) as usize);
    }
    subsumers.sort_unstable();
    subsumers.dedup();
    Some(subsumers)
}

// ---------------------------------------------------------------------------
// Tests: ofn text → frontend → cb_to_ht::convert → bridge → verdicts.
// ---------------------------------------------------------------------------
#[cfg(test)]
mod tests {
    use super::super::completion::strategy::ConceptProcessingPriorityStrategy;
    use super::*;

    struct BridgeEnv {
        tin: crate::orchestrate::cb_to_ht::TInput,
        con_id: std::collections::HashMap<String, usize>,
        // populated by the most recent probe (kept for diagnostics)
        ctx: Option<CalculationAlgorithmContextBase>,
        unsupported: usize,
    }

    /// Same as [`bridge_ofn`] but reads the ontology from a file path.
    fn bridge_ofn_path(path: &str) -> BridgeEnv {
        let text = std::fs::read_to_string(path).expect("readable ontology");
        bridge_ofn(&text)
    }

    /// ofn → clauses → TInput (the future production route input).
    fn bridge_ofn(text: &str) -> BridgeEnv {
        let fr = crate::frontend::ofn_to_clauses(text).expect("in fragment");
        let named: std::collections::HashSet<String> = fr.named.iter().cloned().collect();
        let tin = crate::orchestrate::cb_to_ht::convert(
            &fr.clauses,
            None,
            &named,
            &fr.cardinalities,
            false,
            &fr.rules,
            false,
        );
        let con_id = tin
            .concepts
            .iter()
            .enumerate()
            .map(|(i, n)| (n.clone(), i))
            .collect();
        BridgeEnv {
            tin,
            con_id,
            ctx: None,
            unsupported: 0,
        }
    }

    impl BridgeEnv {
        /// One probe = one fresh context + bridged terminology. Per-probe
        /// isolation: an UNSAT probe leaves clash-laden nodes + queued work
        /// behind, which would leak spurious clashes into the next probe.
        /// Konclude isolates probes via per-task databox COW (the unported
        /// Task layer); the v1 driver rebuilds instead — same verdicts,
        /// O(TBox) per probe.
        fn subsumes(&mut self, sub: &str, sup: &str) -> bool {
            let mut algo = CompletionTaskHandleAlgorithm::new();
            configure_default_blocking(&mut algo);
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
            let bridged = bridge_tinput(&mut ctx, &self.tin);
            self.unsupported = bridged.unsupported;
            let idx = |s: &str| -> usize {
                *self
                    .con_id
                    .get(s)
                    .unwrap_or_else(|| panic!("concept {s} not in TInput"))
            };
            let a = bridged.named[idx(sub)];
            let b = bridged.named[idx(sup)];
            let mut next_indi_id = 0i64;
            let r = bridged_unsat(
                &mut algo,
                &mut ctx,
                &bridged,
                &mut next_indi_id,
                &[(a, false), (b, true)],
            );
            self.ctx = Some(ctx);
            r.unwrap_or_else(|| panic!("probe {sub} ⊑ {sup} raised STOP (undecided)"))
        }
    }

    const PREFIX: &str = "Prefix(:=<http://km.test/>)\nOntology(<http://km.test/o>\n";

    #[test]
    fn bridge_subsumption_chain() {
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C))\n\
             SubClassOf(:A :B)\n\
             SubClassOf(:B :C)\n)"
        );
        let mut env = bridge_ofn(&ofn);
        assert!(env.subsumes("A", "B"), "A ⊑ B (direct)");
        assert_eq!(env.unsupported, 0, "chain TBox fully bridged");
        assert!(env.subsumes("A", "C"), "A ⊑ C (chained)");
        assert!(!env.subsumes("C", "A"), "C ⊑ A must NOT hold");
    }

    #[test]
    fn bridge_disjunction_by_cases() {
        // A ⊑ B ⊔ C, B ⊑ D, C ⊑ D ⇒ A ⊑ D — exercises the OR rule + the
        // sound same-node backtrack through the BRIDGED encoding.
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:A)) Declaration(Class(:B))\n\
             Declaration(Class(:C)) Declaration(Class(:D))\n\
             SubClassOf(:A ObjectUnionOf(:B :C))\n\
             SubClassOf(:B :D)\n\
             SubClassOf(:C :D)\n)"
        );
        let mut env = bridge_ofn(&ofn);
        assert!(env.subsumes("A", "D"), "A ⊑ D by reasoning by cases");
        assert!(!env.subsumes("D", "A"), "D ⊑ A must NOT hold");
    }

    #[test]
    fn bridge_disjunction_open_branch() {
        // Drop C ⊑ D: the C branch stays open ⇒ A ⊑ D must NOT hold (the
        // negative control that pinned the chronological-backtrack bug).
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:A)) Declaration(Class(:B))\n\
             Declaration(Class(:C)) Declaration(Class(:D))\n\
             SubClassOf(:A ObjectUnionOf(:B :C))\n\
             SubClassOf(:B :D)\n)"
        );
        let mut env = bridge_ofn(&ofn);
        assert!(!env.subsumes("A", "D"), "A ⊑ D must NOT hold (C branch open)");
    }

    /// Dump every node's label tags (diagnostic, used on failure only).
    fn dump_nodes(env: &mut BridgeEnv, label: &str) {
        let ctx = env.ctx.as_mut().expect("a probe ran");
        let n = ctx.process_context().node_count();
        eprintln!("DBG {label}: {n} nodes");
        for i in 0..n {
            let node = super::super::process::NodeId::new(i as Cint64);
            let ls = ctx.process_context_mut().node_reapply_concept_label_set(node);
            let mut tags: Vec<_> = ctx
                .process_context()
                .label_set(ls)
                .concept_des_dep_map
                .keys()
                .copied()
                .collect();
            tags.sort_unstable();
            eprintln!("DBG   node {i}: tags {tags:?}");
        }
    }

    #[test]
    fn bridge_exists_forall_clash() {
        // A ⊑ ∃R.B, A ⊑ ∀R.C, B ⊓ C ⊑ ⊥(via D/¬D)  ⇒ A unsatisfiable ⇒ A ⊑ E
        // for the probe; simpler direct check: A ⊑ ∃R.B and ∀R.¬B ⇒ A ⊓ that
        // ∀ is unsat. Encode as: A ⊑ ∃R.B, F ⊑ ∀R.C with B ⊓ C contradictory.
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C))\n\
             Declaration(ObjectProperty(:R))\n\
             SubClassOf(:A ObjectSomeValuesFrom(:R :B))\n\
             SubClassOf(:A ObjectAllValuesFrom(:R :C))\n\
             SubClassOf(:B ObjectComplementOf(:C))\n)"
        );
        let mut env = bridge_ofn(&ofn);
        // A forces an R-successor with B (∃), propagates C (∀), and B ⊑ ¬C
        // clashes on the successor ⇒ A is unsatisfiable ⇒ A ⊑ B holds
        // vacuously (any subsumption from an unsat concept).
        let holds = env.subsumes("A", "B");
        if !holds {
            dump_nodes(&mut env, "after A⊑B probe");
        }
        assert!(holds, "A unsat ⇒ A ⊑ B vacuously");
        let bc = env.subsumes("B", "C");
        if bc {
            // XXX-DBG: spurious unsat — show the TInput + the final graph
            for (i, n) in env.tin.concepts.iter().enumerate() {
                eprintln!("DBG concept {i} = {n}");
            }
            let show = |a: &HAtom| -> String {
                match a {
                    HAtom::Concept { neg, c, t } => format!("{}C{c}({t})", if *neg { "¬" } else { "" }),
                    HAtom::Role { r, s, t } => format!("R{r}({s},{t})"),
                    HAtom::Eq { s, t } => format!("eq({s},{t})"),
                    HAtom::Exist { r, neg, c, t } => {
                        format!("∃R{r}.{}C{c}({t})", if *neg { "¬" } else { "" })
                    }
                }
            };
            for (i, cl) in env.tin.clauses.iter().enumerate() {
                let b: Vec<String> = cl.body.iter().map(show).collect();
                let h: Vec<String> = cl.head.iter().map(show).collect();
                eprintln!("DBG clause {i}: {} -> {}", b.join(" ∧ "), h.join(" ∨ "));
            }
            dump_nodes(&mut env, "after B⊑C probe");
        }
        assert!(!bc, "B ⊑ C must NOT hold");
    }

    #[test]
    fn bridge_role_hierarchy_forall() {
        // R ⊑ S: A ⊑ ∃R.D, A ⊑ ∀S.C, D ⊑ ¬C — the ∀S restriction must reach
        // the R-successor via the hierarchy ⇒ A unsatisfiable. The bridged
        // counterpart of the `role_hierarchy_forall` selftest, driven from
        // real OWL through the indirect-super-role linkers pass.
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:A)) Declaration(Class(:C)) Declaration(Class(:D))\n\
             Declaration(ObjectProperty(:R)) Declaration(ObjectProperty(:S))\n\
             SubObjectPropertyOf(:R :S)\n\
             SubClassOf(:A ObjectSomeValuesFrom(:R :D))\n\
             SubClassOf(:A ObjectAllValuesFrom(:S :C))\n\
             SubClassOf(:D ObjectComplementOf(:C))\n)"
        );
        let mut env = bridge_ofn(&ofn);
        let holds = env.subsumes("A", "D");
        if !holds {
            dump_nodes(&mut env, "after A⊑D probe (hierarchy)");
        }
        assert!(holds, "A unsat via R⊑S hierarchy ⇒ A ⊑ D vacuously");
        assert!(!env.subsumes("D", "A"), "D ⊑ A must NOT hold");
    }

    #[test]
    fn bridge_exists_recognition_inverse() {
        // ∃R.B ⊑ Q (the definer-recognition / absorption shape, frontend-
        // clausified to `B(y) ∧ R(x,y) → Q(x)`, bridged as `B ⊑ ∀R⁻.Q`):
        // A ⊑ ∃R.B and Q ⊑ E ⊢ A ⊑ E — the Q lands on A through the
        // inverse-edge propagation, not through any forward unfold.
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:A)) Declaration(Class(:B))\n\
             Declaration(Class(:Q)) Declaration(Class(:E))\n\
             Declaration(ObjectProperty(:R))\n\
             SubClassOf(:A ObjectSomeValuesFrom(:R :B))\n\
             SubClassOf(ObjectSomeValuesFrom(:R :B) :Q)\n\
             SubClassOf(:Q :E)\n)"
        );
        let mut env = bridge_ofn(&ofn);
        let holds = env.subsumes("A", "E");
        if !holds {
            dump_nodes(&mut env, "after A⊑E probe (recognition)");
        }
        assert!(holds, "A ⊑ E via ∃R.B ⊑ Q recognition over the inverse edge");
        assert!(!env.subsumes("E", "A"), "E ⊑ A must NOT hold");
    }

    /// Scale smoke-test on a REAL ontology: bridge `KM_BRIDGE_ONT` and run
    /// satisfiability probes for the first `KM_BRIDGE_PROBES` (default 3)
    /// named non-internal concepts, timing each. Measures whether the ported
    /// engine + re-drive harness converge at real-TBox scale and what a probe
    /// costs — the data for the classify-driver design (per-task databox vs
    /// per-probe rebuild, reapply-queue priority). Diagnostic only.
    #[test]
    #[ignore]
    fn bridge_scale_probe() {
        let path = std::env::var("KM_BRIDGE_ONT").expect("set KM_BRIDGE_ONT=<ont path>");
        let n_probes: usize = std::env::var("KM_BRIDGE_PROBES")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(3);
        let text = std::fs::read_to_string(&path).expect("readable ontology");
        let fr = crate::frontend::ofn_to_clauses(&text).expect("in fragment");
        let named_set: std::collections::HashSet<String> = fr.named.iter().cloned().collect();
        let tin = crate::orchestrate::cb_to_ht::convert(
            &fr.clauses,
            None,
            &named_set,
            &fr.cardinalities,
            false,
            &fr.rules,
            false,
        );
        let subjects: Vec<usize> = tin
            .concepts
            .iter()
            .enumerate()
            .filter(|(_, n)| named_set.contains(*n))
            .map(|(i, _)| i)
            .take(n_probes)
            .collect();
        for &s in &subjects {
            let t0 = std::time::Instant::now();
            let mut algo = CompletionTaskHandleAlgorithm::new();
            configure_default_blocking(&mut algo);
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
            let bridged = bridge_tinput(&mut ctx, &tin);
            let t_bridge = t0.elapsed();
            let t1 = std::time::Instant::now();
            let mut next = 0i64;
            let verdict = bridged_unsat(
                &mut algo,
                &mut ctx,
                &bridged,
                &mut next,
                &[(bridged.named[s], false)],
            );
            eprintln!(
                "BRIDGE-PROBE {}: verdict={:?} bridge={:.0}ms probe={:.0}ms nodes={} backtracks={} absorbed={} top={}",
                tin.concepts[s],
                verdict,
                t_bridge.as_secs_f64() * 1e3,
                t1.elapsed().as_secs_f64() * 1e3,
                ctx.process_context().node_count(),
                algo.or_backtrack_count,
                bridged.absorbed,
                bridged.top_attached,
            );
        }
    }

    /// Verdict CORRECTNESS on a REAL ontology vs a gold classification.
    /// `KM_BRIDGE_ONT` = the .owl; `KM_BRIDGE_GOLD` = the `km classify` JSON
    /// output (`{"consistent":..,"subsumptions":[[sub_iri,sup_iri],..]}`,
    /// the validated production path). Samples the first `KM_BRIDGE_PROBES`
    /// (default 20) named subjects; for each, checks EVERY gold super
    /// (bridge must report subsumption) and an equal number of gold
    /// NON-supers (bridge must NOT). Reports missing (incomplete) / spurious
    /// (unsound) counts. Diagnostic; asserts only that unsound==0 when the
    /// bridge is fully covered (`unsupported==0`), since a clash verdict is
    /// sound even under-approximated.
    #[test]
    #[ignore]
    fn bridge_correctness_sample() {
        let path = std::env::var("KM_BRIDGE_ONT").expect("set KM_BRIDGE_ONT=<ont path>");
        let gold_path = std::env::var("KM_BRIDGE_GOLD").expect("set KM_BRIDGE_GOLD=<json>");
        let n_probes: usize = std::env::var("KM_BRIDGE_PROBES")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(20);
        let gold_text = std::fs::read_to_string(&gold_path).expect("readable gold");
        let gold: serde_json::Value = serde_json::from_str(&gold_text).expect("gold json");
        // local name after '#' or last '/'.
        let local = |iri: &str| -> String {
            iri.rsplit(['#', '/']).next().unwrap_or(iri).to_string()
        };
        // gold super-map: sub_local → set(sup_local); `gold_universe` = every
        // concept gold tracks (as sub or sup). Negatives are drawn ONLY from
        // this universe: cb_to_ht mints internal DEFINER concepts (Q_NNNN) that
        // are NOT named classes, so gold never lists them as supers — a subject
        // legitimately subsumed by an internal definer is correct, not unsound,
        // and must not be sampled as a negative.
        let mut supers: std::collections::HashMap<String, std::collections::HashSet<String>> =
            std::collections::HashMap::new();
        let mut gold_universe: std::collections::HashSet<String> = std::collections::HashSet::new();
        for pair in gold["subsumptions"].as_array().expect("subsumptions array") {
            let sub = local(pair[0].as_str().unwrap());
            let sup = local(pair[1].as_str().unwrap());
            gold_universe.insert(sub.clone());
            gold_universe.insert(sup.clone());
            supers.entry(sub).or_default().insert(sup);
        }

        let mut env = bridge_ofn_path(&path);
        // owned snapshot of the TInput concept names (avoids holding an
        // immutable borrow of env across the &mut env.subsumes() calls).
        let present: std::collections::HashSet<String> = env.con_id.keys().cloned().collect();
        // subjects: gold subjects that ARE present in the TInput (in-fragment).
        let mut subjects: Vec<String> = supers
            .keys()
            .filter(|s| present.contains(*s))
            .cloned()
            .collect();
        subjects.sort();
        subjects.truncate(n_probes);

        // deterministic "random" negatives: stride through the gold-known,
        // in-fragment concepts (excludes cb_to_ht internal definers).
        let mut all_concepts: Vec<String> = present
            .iter()
            .filter(|c| gold_universe.contains(*c))
            .cloned()
            .collect();
        all_concepts.sort();

        let mut missing = 0usize; // gold super the bridge did NOT derive (incomplete)
        let mut spurious = 0usize; // non-super the bridge DID derive (unsound)
        let mut checked_pos = 0usize;
        let mut checked_neg = 0usize;
        for sub in &subjects {
            let gold_sups = &supers[sub];
            for sup in gold_sups {
                if !present.contains(sup) || sup == sub {
                    continue;
                }
                checked_pos += 1;
                if !env.subsumes(sub, sup) {
                    missing += 1;
                    if missing <= 20 {
                        eprintln!("MISSING (incomplete): {sub} ⊑ {sup}");
                    }
                }
            }
            // negatives: same count of concepts NOT in the gold super-set.
            let want_neg = gold_sups.len().max(1);
            let mut got = 0usize;
            let step = (all_concepts.len() / want_neg.max(1)).max(1);
            let mut i = 0usize;
            while got < want_neg && i < all_concepts.len() {
                let cand = &all_concepts[i];
                i += step;
                if cand == sub || gold_sups.contains(cand) {
                    continue;
                }
                checked_neg += 1;
                got += 1;
                if env.subsumes(sub, cand) {
                    spurious += 1;
                    if spurious <= 20 {
                        eprintln!("SPURIOUS (unsound): {sub} ⊑ {cand}");
                    }
                }
            }
        }
        eprintln!(
            "BRIDGE-CORRECTNESS {path}: subjects={} pos_checked={} missing={} \
             neg_checked={} spurious={} unsupported={}",
            subjects.len(),
            checked_pos,
            missing,
            checked_neg,
            spurious,
            env.unsupported,
        );
        if env.unsupported == 0 {
            assert_eq!(spurious, 0, "clash verdicts must be sound");
        }
    }

    /// FULL model-read-off classification vs gold: saturate every named
    /// subject ONCE (`bridged_classify_subject`) and read its subsumers off
    /// the root label — O(concepts) saturations, the feasible classification
    /// path (naive pairwise on 1016 = ~2500² probes). Compares the WHOLE
    /// derived named-subsumption relation to the `km classify` gold
    /// (`KM_BRIDGE_GOLD`), reporting missing (incomplete) / spurious
    /// (unsound) / non-deterministic-subject counts. Diagnostic.
    #[test]
    #[ignore]
    fn bridge_classify_full() {
        let path = std::env::var("KM_BRIDGE_ONT").expect("set KM_BRIDGE_ONT=<ont path>");
        let gold_path = std::env::var("KM_BRIDGE_GOLD").expect("set KM_BRIDGE_GOLD=<json>");
        let gold_text = std::fs::read_to_string(&gold_path).expect("readable gold");
        let gold: serde_json::Value = serde_json::from_str(&gold_text).expect("gold json");
        let local = |iri: &str| -> String {
            iri.rsplit(['#', '/']).next().unwrap_or(iri).to_string()
        };
        let mut gold_pairs: std::collections::HashSet<(String, String)> =
            std::collections::HashSet::new();
        let mut gold_universe: std::collections::HashSet<String> = std::collections::HashSet::new();
        for pair in gold["subsumptions"].as_array().expect("subsumptions array") {
            let sub = local(pair[0].as_str().unwrap());
            let sup = local(pair[1].as_str().unwrap());
            gold_universe.insert(sub.clone());
            gold_universe.insert(sup.clone());
            gold_pairs.insert((sub, sup));
        }

        let text = std::fs::read_to_string(&path).expect("readable ontology");
        let fr = crate::frontend::ofn_to_clauses(&text).expect("in fragment");
        let named_set: std::collections::HashSet<String> = fr.named.iter().cloned().collect();
        let tin = crate::orchestrate::cb_to_ht::convert(
            &fr.clauses, None, &named_set, &fr.cardinalities, false, &fr.rules, false,
        );
        let n_named = tin.concepts.len();

        let mut algo = CompletionTaskHandleAlgorithm::new();
        configure_default_blocking(&mut algo);
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
        let bridged = bridge_tinput(&mut ctx, &tin);

        // subjects = gold-known, in-fragment named concepts.
        let subjects: Vec<usize> = (0..n_named)
            .filter(|&i| gold_universe.contains(&tin.concepts[i]))
            .collect();

        let mut derived: std::collections::HashSet<(String, String)> =
            std::collections::HashSet::new();
        let mut nondet = 0usize;
        let mut next = 0i64;
        let t0 = std::time::Instant::now();
        for &s in &subjects {
            // fresh ctx per subject (per-probe isolation; the databox-COW
            // reuse is the next wave). Rebuild is O(TBox).
            let mut algo2 = CompletionTaskHandleAlgorithm::new();
            configure_default_blocking(&mut algo2);
            let mut ctx2 = CalculationAlgorithmContextBase::new();
            ctx2.base.used_concept_priority_strategy =
                Some(ConceptProcessingPriorityStrategy::new_concrete_operator());
            let top2 = {
                let mut c = Concept::new();
                c.set_concept_tag(1);
                c.set_operator_code(op::CCTOP);
                ctx2.ontology_arenas_mut().alloc_concept(c)
            };
            ctx2.processing_data_box_mut().ontology_top_concept = top2;
            let bridged2 = bridge_tinput(&mut ctx2, &tin);
            let mut n2 = 0i64;
            match bridged_classify_subject(&mut algo2, &mut ctx2, &bridged2, &mut n2, s, n_named) {
                Some(subs) => {
                    for sup in subs {
                        if sup == s {
                            continue;
                        }
                        // only named-vs-named, gold-known targets
                        if gold_universe.contains(&tin.concepts[sup]) {
                            derived.insert((
                                tin.concepts[s].clone(),
                                tin.concepts[sup].clone(),
                            ));
                        }
                    }
                }
                None => nondet += 1,
            }
        }
        let elapsed = t0.elapsed();
        let _ = (&algo, &bridged, &mut next);

        // restrict gold to the same subject/target universe we classified.
        let subj_names: std::collections::HashSet<String> =
            subjects.iter().map(|&i| tin.concepts[i].clone()).collect();
        let gold_restricted: std::collections::HashSet<(String, String)> = gold_pairs
            .iter()
            .filter(|(sub, sup)| subj_names.contains(sub) && gold_universe.contains(sup))
            .cloned()
            .collect();
        let missing: Vec<_> = gold_restricted.difference(&derived).take(20).collect();
        let spurious: Vec<_> = derived.difference(&gold_restricted).take(20).collect();
        for m in &missing {
            eprintln!("MISSING (incomplete): {} ⊑ {}", m.0, m.1);
        }
        for sp in &spurious {
            eprintln!("SPURIOUS (unsound): {} ⊑ {}", sp.0, sp.1);
        }
        eprintln!(
            "BRIDGE-CLASSIFY {path}: subjects={} nondet={} derived={} gold={} \
             missing={} spurious={} elapsed={:.1}s unsupported={}",
            subjects.len(),
            nondet,
            derived.len(),
            gold_restricted.len(),
            gold_restricted.difference(&derived).count(),
            derived.difference(&gold_restricted).count(),
            elapsed.as_secs_f64(),
            bridged.unsupported,
        );
    }

    /// Fragment-coverage report on a REAL ontology: set `KM_BRIDGE_ONT` to an
    /// .owl/.ofn path and run with `-- --ignored --nocapture`. Reports how
    /// many TInput clauses the v1 bridge encodes vs counts as unsupported —
    /// the data that prioritises the next bridge wave (absorption, inverse,
    /// cardinality). Diagnostic only; asserts nothing about verdicts.
    #[test]
    #[ignore]
    fn bridge_coverage_report() {
        let path = std::env::var("KM_BRIDGE_ONT").expect("set KM_BRIDGE_ONT=<ont path>");
        let text = std::fs::read_to_string(&path).expect("readable ontology");
        let fr = crate::frontend::ofn_to_clauses(&text).expect("in fragment");
        let named: std::collections::HashSet<String> = fr.named.iter().cloned().collect();
        let tin = crate::orchestrate::cb_to_ht::convert(
            &fr.clauses,
            None,
            &named,
            &fr.cardinalities,
            false,
            &fr.rules,
            false,
        );
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
        let bridged = bridge_tinput(&mut ctx, &tin);
        eprintln!(
            "BRIDGE-COVERAGE {path}: concepts={} roles={} clauses={} encoded_impls={} \
             absorbed={} top_attached={} unsupported={} (inverse={} nominals={} card_defs={} chains={})",
            tin.concepts.len(),
            tin.roles.len(),
            tin.clauses.len(),
            bridged.tbox.len(),
            bridged.absorbed,
            bridged.top_attached,
            bridged.unsupported,
            tin.inverse,
            tin.nominals.len(),
            tin.card_defs.len(),
            tin.chains.len(),
        );
    }
}
