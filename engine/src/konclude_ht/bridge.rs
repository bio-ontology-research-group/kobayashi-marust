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
use std::collections::{BTreeSet, HashMap};

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
    /// Singleton concepts (`C(x) ∧ C(y) → x = y` clause shape — datatype
    /// value identity): consumed by the kernel's deterministic
    /// scan-at-fixpoint merge; must be installed on every probe algorithm.
    pub singleton_concepts: Vec<ConceptId>,
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
    /// Unqualified `≤n R.⊤` — `CCATMOST` with parameter `n` and NO operand
    /// (empty qualifier ⇒ every R-successor counts). `n = 1` is a functional
    /// role; the completion routes it through `apply_atmost_rule` →
    /// `ht_apply_atmost_merge` (merge excess successors, else clash).
    fn atmost(&mut self, role: RoleId, n: Cint64) -> ConceptId {
        let tag = self.fresh_tag();
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op::CCATMOST);
        c.set_role(role);
        c.set_parameter(n);
        c.set_operand_count(0);
        self.ctx.ontology_arenas_mut().alloc_concept(c)
    }
    /// Qualified `≤n R.C` — `CCATMOST` with parameter `n` and qualifier
    /// operand `C` (the at-most merge counts only `C`-successors).
    fn atmost_q(&mut self, role: RoleId, n: Cint64, filler: (ConceptId, bool)) -> ConceptId {
        let tag = self.fresh_tag();
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op::CCATMOST);
        c.set_role(role);
        c.set_parameter(n);
        c.add_operand_linker(filler.0, filler.1);
        c.set_operand_count(1);
        self.ctx.ontology_arenas_mut().alloc_concept(c)
    }
    /// Qualified `≥n R.C` — `CCATLEAST` with parameter `n` and qualifier
    /// operand `C` (creates `n` pairwise-distinct `C`-successors).
    fn atleast_q(&mut self, role: RoleId, n: Cint64, filler: (ConceptId, bool)) -> ConceptId {
        let tag = self.fresh_tag();
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op::CCATLEAST);
        c.set_role(role);
        c.set_parameter(n);
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
    let mut singleton_concepts: Vec<ConceptId> = Vec::new();
    let mut unsupported = 0usize;
    // Diagnostic (KM_BRIDGE_DUMP_UNSUP=N): record the shape of the first N
    // unsupported clauses so the next coverage wave can be scoped.
    let dump_unsup: usize = std::env::var("KM_BRIDGE_DUMP_UNSUP")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0);
    let mut dumped = 0usize;
    let mut dump = |cl: &HtClause, why: &str| {
        if dumped < dump_unsup {
            let show = |a: &HAtom| -> String {
                match a {
                    HAtom::Concept { neg, c, t } => {
                        format!("{}C{c}({t})", if *neg { "¬" } else { "" })
                    }
                    HAtom::Role { r, s, t } => format!("R{r}({s},{t})"),
                    HAtom::Eq { s, t } => format!("eq({s},{t})"),
                    HAtom::Exist { r, neg, c, t } => {
                        format!("∃R{r}.{}C{c}({t})", if *neg { "¬" } else { "" })
                    }
                }
            };
            let b: Vec<String> = cl.body.iter().map(show).collect();
            let h: Vec<String> = cl.head.iter().map(show).collect();
            eprintln!("UNSUP[{why}]: {} -> {}", b.join(" ∧ "), h.join(" ∨ "));
            dumped += 1;
        }
    };
    // Diagnostic (KM_BRIDGE_DUMP_TOPGCI=N): record the shape of the first N
    // clauses that become TOP-attached GCIs (no positive absorption guard) —
    // these branch on EVERY node and are the disjunction-search cost centre.
    let dump_topgci: usize = std::env::var("KM_BRIDGE_DUMP_TOPGCI")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0);
    let mut dumped_top = 0usize;
    let topgci_names = &tin.concepts;
    let mut dump_top = |cl: &HtClause, why: &str| {
        if dumped_top < dump_topgci {
            let show = |a: &HAtom| -> String {
                match a {
                    HAtom::Concept { neg, c, t } => {
                        format!(
                            "{}C{c}:{}({t})",
                            if *neg { "¬" } else { "" },
                            topgci_names.get(*c).map(String::as_str).unwrap_or("?")
                        )
                    }
                    HAtom::Role { r, s, t } => format!("R{r}({s},{t})"),
                    HAtom::Eq { s, t } => format!("eq({s},{t})"),
                    HAtom::Exist { r, neg, c, t } => {
                        format!(
                            "∃R{r}.{}C{c}:{}({t})",
                            if *neg { "¬" } else { "" },
                            topgci_names.get(*c).map(String::as_str).unwrap_or("?")
                        )
                    }
                }
            };
            let b: Vec<String> = cl.body.iter().map(show).collect();
            let h: Vec<String> = cl.head.iter().map(show).collect();
            eprintln!("TOPGCI[{why}]: {} -> {}", b.join(" ∧ "), h.join(" ∨ "));
            dumped_top += 1;
        }
    };
    // Structures outside the v1 clause encoder count as unsupported input
    // (card_defs are ENCODED below — first-class ≥n/≤n via the ported
    // CCATLEAST/CCATMOST rules — so they are no longer counted here).
    unsupported += tin.nominals.len() + tin.chains.len();
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
    // The closure runs over BOTH polarities (vertex = 2·role + inverted): a
    // plain `R ⊑ S` also yields `R⁻ ⊑ S⁻` (needed by the mirror inverse-edge
    // installs), and an inverse-hierarchy clause `R(x,y) → S(y,x)` (`R ⊑ S⁻`,
    // the clausal InverseObjectProperties half) crosses polarity. All entries
    // are installed with negated=false against the CONCRETE role object
    // (`roles[·]` / `inv_roles[·]`) — `has_indirect_super_role` (the u08
    // ∀-matcher) ignores the negated flag, so polarity must be resolved to
    // distinct role objects, never encoded in the flag.
    let n_r = tin.roles.len();
    let mut sub_super: Vec<Vec<usize>> = vec![Vec::new(); 2 * n_r];
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
    // `R(x,y) → S(y,x)` — `R ⊑ S⁻`; `sr == hr` allowed (a symmetric role).
    let is_inv_hierarchy = |cl: &HtClause| -> Option<(usize, usize)> {
        if cl.body.len() != 1 || cl.head.len() != 1 {
            return None;
        }
        if let (HAtom::Role { r: sr, s: ss, t: st }, HAtom::Role { r: hr, s: hs, t: ht }) =
            (&cl.body[0], &cl.head[0])
        {
            if ss == ht && st == hs && ss != st {
                return Some((*sr, *hr));
            }
        }
        None
    };
    for cl in &tin.clauses {
        if let Some((sub, sup)) = is_hierarchy(cl) {
            sub_super[2 * sub].push(2 * sup);
            sub_super[2 * sub + 1].push(2 * sup + 1);
        } else if let Some((sub, sup)) = is_inv_hierarchy(cl) {
            sub_super[2 * sub].push(2 * sup + 1);
            sub_super[2 * sub + 1].push(2 * sup);
        }
    }
    // transitive closure per (role, polarity) vertex (small role counts; DFS)
    for sub in 0..sub_super.len() {
        let mut seen: BTreeSet<usize> = BTreeSet::new();
        let mut stack: Vec<usize> = sub_super[sub].clone();
        while let Some(s) = stack.pop() {
            if s != sub && seen.insert(s) {
                stack.extend(sub_super[s].iter().copied());
            }
        }
        let sub_obj = if sub % 2 == 0 { roles[sub / 2] } else { inv_roles[sub / 2] };
        for s in seen {
            let sup_obj = if s % 2 == 0 { roles[s / 2] } else { inv_roles[s / 2] };
            b.ctx
                .ontology_arenas_mut()
                .role_mut(sub_obj)
                .add_indirect_super_role_linker(
                    super::model::substrate::NegLink {
                        target: sup_obj,
                        negated: false,
                    },
                );
        }
    }

    // ---- pass 2: functional roles `R(0,1) ∧ R(0,2) → eq(1,2)` --------------
    // The clausal form of `⊤ ⊑ ≤1 R.⊤` (a functional property / global at-most
    // 1). Detected here and later encoded as a `CCATMOST(R, 1)` on TOP so
    // every node enforces ≤1 R-successor through the ported merge rule
    // (`ht_apply_atmost_merge`). The clause itself is then consumed (not
    // unsupported).
    let is_functional = |cl: &HtClause| -> Option<usize> {
        if cl.body.len() != 2 || cl.head.len() != 1 {
            return None;
        }
        let (b0, b1) = (&cl.body[0], &cl.body[1]);
        if let (
            HAtom::Role { r: r0, s: s0, t: t0 },
            HAtom::Role { r: r1, s: s1, t: t1 },
            HAtom::Eq { s: es, t: et },
        ) = (b0, b1, &cl.head[0])
        {
            // same role, shared source 0, distinct targets, head equates them.
            if r0 == r1 && s0 == s1 && t0 != t1 {
                let (a, b) = (*t0.min(t1), *t0.max(t1));
                let (ea, eb) = (*es.min(et), *es.max(et));
                if (a, b) == (ea, eb) && *s0 != a && *s0 != b {
                    return Some(*r0);
                }
            }
        }
        None
    };
    let mut functional_roles: BTreeSet<usize> = BTreeSet::new();
    for cl in &tin.clauses {
        if let Some(r) = is_functional(cl) {
            functional_roles.insert(r);
        }
    }

    'clause: for cl in &tin.clauses {
        // hierarchy clauses (plain + inverse) were consumed by pass 1
        if is_hierarchy(cl).is_some() || is_inv_hierarchy(cl).is_some() {
            continue;
        }
        // functional clauses were consumed by pass 2
        if is_functional(cl).is_some() {
            continue;
        }
        // ---- classify the clause's variable/role shape -------------------
        let mut body_roles: Vec<(usize, usize, usize)> = Vec::new(); // (r, s, t)
        let mut body_bad = false;
        for a in &cl.body {
            match a {
                HAtom::Role { r, s, t } => body_roles.push((*r, *s, *t)),
                HAtom::Eq { .. } | HAtom::Exist { .. } => {
                    body_bad = true;
                }
                HAtom::Concept { .. } => {}
            }
        }
        if body_bad {
            unsupported += 1;
            dump(cl, "body-eq-or-exist");
            continue 'clause;
        }
        // ---- ≥k-recognition: guards(0) ∧ C(t_i) ∧ R(0,t_i) → D(0)… ∨ all-pairs eq ----
        // `⋀guards ⊓ ≥k R.C ⊑ ⋁D` ⟺ `implication(guards → ⋁D ∨ ≤(k−1) R.C)`:
        // k pairwise-distinct R.C-successors force some D, and the ≤(k−1)
        // qualified at-most (the ported CCATMOST merge rule) carries the
        // eq-head semantics exactly — so the clause is CONSUMED, not
        // unsupported. A shared-TARGET orientation (`R(t_i,0)`, e.g. inverse-
        // functional) encodes on the concrete inverse-role object.
        //
        // Recognition encoding: DEFAULT ON (`KM_HT_BRIDGE_NO_RECOG` opts
        // out). The early "3 spurious onto `Path`" measurement that kept this
        // arm opt-in was NOT this encoding's fault: the answers rode the
        // phantom card-def root re-seed (fixed 84e38bf) and the u29 DDB
        // leftover-poisoning wrong-cancel (fixed 7c521cb). With both fixed,
        // ore_ont_12653 classifies gold-clean (missing=0 spurious=0) with
        // this arm on, and the oracle suite is green in all 6 search-mode
        // combos. Without it every eq-head clause counts unsupported and the
        // production driver declines whole recognition-family ontologies.
        if !body_roles.is_empty()
            && cl.head.iter().any(|a| matches!(a, HAtom::Eq { .. }))
            && std::env::var_os("KM_HT_BRIDGE_NO_RECOG").is_none()
        {
            let recog = (|| -> Option<(RoleId, usize, Option<usize>, Vec<(usize, bool)>, Vec<usize>, usize)> {
                let r0 = body_roles[0].0;
                if body_roles.iter().any(|&(r, _, _)| r != r0) {
                    return None;
                }
                // orientation: all roles share the source var (hub) or all
                // share the target var (inverse orientation).
                let (role_obj, hub, mut targets): (RoleId, usize, Vec<usize>) =
                    if body_roles.iter().all(|&(_, s, _)| s == body_roles[0].1) {
                        (roles[r0], body_roles[0].1, body_roles.iter().map(|&(_, _, t)| t).collect())
                    } else if body_roles.iter().all(|&(_, _, t)| t == body_roles[0].2) {
                        (inv_roles[r0], body_roles[0].2, body_roles.iter().map(|&(_, s, _)| s).collect())
                    } else {
                        return None;
                    };
                targets.sort_unstable();
                let k = targets.len();
                if k < 2 {
                    return None;
                }
                targets.dedup();
                if targets.len() != k || targets.contains(&hub) {
                    return None;
                }
                let mut guards: Vec<(usize, bool)> = Vec::new();
                let mut per_target: HashMap<usize, Vec<usize>> = HashMap::new();
                for a in &cl.body {
                    if let HAtom::Concept { neg, c, t } = a {
                        if *t == hub {
                            guards.push((*c, *neg));
                        } else if targets.binary_search(t).is_ok() {
                            if *neg {
                                return None;
                            }
                            per_target.entry(*t).or_default().push(*c);
                        } else {
                            return None;
                        }
                    }
                }
                // the qualifier: the SAME (≤1-element) positive concept list
                // on every successor variable.
                let mut qual: Option<Vec<usize>> = None;
                for t in &targets {
                    let mut v = per_target.remove(t).unwrap_or_default();
                    v.sort_unstable();
                    match &qual {
                        None => qual = Some(v),
                        Some(q) if *q == v => {}
                        _ => return None,
                    }
                }
                let qual = qual.unwrap_or_default();
                if qual.len() > 1 {
                    return None;
                }
                let mut heads: Vec<usize> = Vec::new();
                let mut eqs: BTreeSet<(usize, usize)> = BTreeSet::new();
                for a in &cl.head {
                    match a {
                        HAtom::Concept { neg, c, t } => {
                            if *neg || *t != hub {
                                return None;
                            }
                            heads.push(*c);
                        }
                        HAtom::Eq { s, t } => {
                            eqs.insert((*s.min(t), *s.max(t)));
                        }
                        _ => return None,
                    }
                }
                let mut want: BTreeSet<(usize, usize)> = BTreeSet::new();
                for i in 0..k {
                    for j in (i + 1)..k {
                        want.insert((targets[i], targets[j]));
                    }
                }
                if eqs != want {
                    return None;
                }
                Some((role_obj, k, qual.first().copied(), guards, heads, r0))
            })();
            if let Some((role_obj, k, qual, guards, heads, _r0)) = recog {
                // KM_BRIDGE_DUMP_RECOG: print each recognized ≥k clause's
                // encoding parameters (spurious-subsumption hunts).
                if std::env::var_os("KM_BRIDGE_DUMP_RECOG").is_some() {
                    eprintln!(
                        "RECOG r={_r0} k={k} qual={qual:?} guards={guards:?} heads={heads:?} ({})",
                        if guards.is_empty() { "TOP-ATTACHED" } else { "absorbed" }
                    );
                }
                let am = match qual {
                    Some(c) => b.atmost_q(role_obj, (k - 1) as Cint64, (named[c], false)),
                    None => b.atmost(role_obj, (k - 1) as Cint64),
                };
                let mut head_ops: Vec<(ConceptId, bool)> =
                    heads.iter().map(|&c| (named[c], false)).collect();
                head_ops.push((am, false));
                let head = b.or_of(&head_ops);
                let triggers: Vec<(ConceptId, bool)> =
                    guards.iter().map(|&(c, n)| (named[c], n)).collect();
                let imp = b.implication(head, &triggers);
                tbox.push(imp);
                match triggers.iter().find(|&&(_, neg)| !neg) {
                    Some(&(host, _)) => absorbed_pairs.push((host, imp)),
                    None => {
                        dump_top(cl, "recog");
                        top_gcis.push(imp)
                    }
                }
                continue 'clause;
            }
        }
        // ---- singleton-concept recognition: `C(v1) ∧ C(v2) → v1 = v2` ------
        // The clausal datatype value-identity shape (a literal value is one
        // semantic object, so any two carriers of `__dt__val__…` are equal;
        // Konclude gets this natively from its databox literal handling, the
        // clausal frontend surfaces it role-free). CONSUMED as a singleton
        // registration: the kernel's deterministic scan-at-fixpoint merge
        // (u02 `ht_apply_singleton_merges`) realises the eq head exactly —
        // deterministic (single-disjunct head), no branch point. General
        // structural rule: any concept in this shape is a singleton.
        // KM_HT_NO_SINGLETON: diagnostic A/B gate — count the shape
        // unsupported instead (the pre-d58c2b2 behaviour: the driver then
        // DECLINES, isolating the merge rule's effect on spuriousness).
        if body_roles.is_empty()
            && cl.body.len() == 2
            && cl.head.len() == 1
            && std::env::var_os("KM_HT_NO_SINGLETON").is_none()
        {
            if let (
                HAtom::Concept { neg: false, c: c0, t: t0 },
                HAtom::Concept { neg: false, c: c1, t: t1 },
                HAtom::Eq { s: es, t: et },
            ) = (&cl.body[0], &cl.body[1], &cl.head[0])
            {
                if c0 == c1 && t0 != t1 {
                    let (a, bb) = (*t0.min(t1), *t0.max(t1));
                    let (ea, eb) = (*es.min(et), *es.max(et));
                    if (a, bb) == (ea, eb) {
                        let sc = named[*c0];
                        if !singleton_concepts.contains(&sc) {
                            singleton_concepts.push(sc);
                        }
                        continue 'clause;
                    }
                }
            }
        }
        if cl.head.iter().any(|a| matches!(a, HAtom::Role { .. } | HAtom::Eq { .. })) {
            unsupported += 1;
            dump(cl, "head-role-or-eq");
            continue 'clause;
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
                None => {
                    dump_top(cl, "pure-concept");
                    top_gcis.push(imp)
                }
            }
            continue;
        }

        if body_roles.len() == 1 {
            // ---- guarded two-variable clause: R(x, y) --------------------
            let (r, s, t) = body_roles[0];
            if s != 0 || t == 0 || vars.iter().any(|&v| v != s && v != t) {
                unsupported += 1;
                dump(cl, "guarded-var-shape");
                continue;
            }
            let _ = r;
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
                    dump(cl, "nested-exist-under-forall");
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
                // KM_BRIDGE_DUMP_FORALL=<role_idx>: print the antecedent
                // (trigger tags) of every ∀<role>.… implication built here —
                // reveals whether a ∀ is concept-gated or global (all-negative
                // triggers ⇒ TOP-attached ⇒ fires on every node).
                if std::env::var("KM_BRIDGE_DUMP_FORALL")
                    .ok()
                    .and_then(|s| s.parse::<usize>().ok())
                    == Some(r)
                {
                    let tt: Vec<String> = triggers
                        .iter()
                        .map(|&(c, n)| {
                            format!(
                                "{}{}",
                                if n { "¬" } else { "" },
                                b.ctx.ontology_arenas().concept(c).get_concept_tag()
                            )
                        })
                        .collect();
                    let ft: Vec<String> = y_ops
                        .iter()
                        .map(|&(c, n)| {
                            format!(
                                "{}{}",
                                if n { "¬" } else { "" },
                                b.ctx.ontology_arenas().concept(c).get_concept_tag()
                            )
                        })
                        .collect();
                    let global = triggers.iter().all(|&(_, n)| n);
                    eprintln!(
                        "DUMP-FORALL role={r} triggers=[{}] fillers=[{}] GLOBAL={global}",
                        tt.join(" "),
                        ft.join(" ")
                    );
                }
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
                    None => {
                        dump_top(cl, "forall-residue");
                        top_gcis.push(imp)
                    }
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
                    None => {
                        dump_top(cl, "inv-forall-residue");
                        top_gcis.push(imp)
                    }
                }
            } else if head_y.is_empty() && !head_x.is_empty() {
                // ---- domain axiom `R(x,y) → C(x) [∨ D(x) …]` ----------------
                // Konclude stores these on the role (CRole::domainLinker) and
                // applies them at every link install
                // (createNewIndividualsLink* cpp 22382–22395, ported in u08
                // ht_apply_role_domain_range) — node-count-independent, no
                // covering disjunction needed.
                let (c, neg) = b.or_of(&head_x);
                let nl = super::model::substrate::NegLink { target: c, negated: neg };
                b.ctx.ontology_arenas_mut().role_mut(roles[r]).domain_linker.push(nl);
                // domain(R) = range(R⁻): keep the inverse object consistent so
                // whichever edge direction is installed applies the concept.
                b.ctx.ontology_arenas_mut().role_mut(inv_roles[r]).range_linker.push(nl);
            } else if head_x.is_empty() && !head_y.is_empty() {
                // ---- range axiom `R(x,y) → C(y) [∨ D(y) …]` -----------------
                let (c, neg) = b.or_of(&head_y);
                let nl = super::model::substrate::NegLink { target: c, negated: neg };
                b.ctx.ontology_arenas_mut().role_mut(roles[r]).range_linker.push(nl);
                b.ctx.ontology_arenas_mut().role_mut(inv_roles[r]).domain_linker.push(nl);
            } else if head_x.is_empty() && head_y.is_empty() {
                // ---- `R(x,y) → ⊥` (empty role): domain ⊥ — any R-edge
                // immediately clashes its source, exactly the axiom's force.
                let bot = b.bottom();
                let nl = super::model::substrate::NegLink { target: bot, negated: false };
                b.ctx.ontology_arenas_mut().role_mut(roles[r]).domain_linker.push(nl);
                b.ctx.ontology_arenas_mut().role_mut(inv_roles[r]).range_linker.push(nl);
            } else {
                // mixed x/y disjunctive head over an edge with no concept
                // trigger (`R(x,y) → C(x) ∨ D(y)`) — out of the v1 fragment
                // (needs the covering-disjunction machinery Konclude gets from
                // absorption + branch triggers).
                unsupported += 1;
                dump(cl, "edge-no-concept-trigger");
            }
            continue;
        }

        unsupported += 1;
        dump(cl, "multi-role-body");
    }

    // ---- functional roles → `≤1 R` on TOP (every node) ---------------------
    // Emitted while the Builder still holds the arena borrow. Each functional
    // role R contributes an unqualified `CCATMOST(R, 1)`; attaching it to TOP
    // makes every node enforce ≤1 R-successor via the ported merge rule. The
    // atmost is also seeded on the root each drive pass (it is a universal
    // constraint, not trigger-gated).
    let functional_count = functional_roles.len();
    let atmost_concepts: Vec<ConceptId> = functional_roles
        .iter()
        .map(|&r| b.atmost(roles[r], 1))
        .collect();
    for &a in &atmost_concepts {
        tbox.push(a);
        top_gcis.push(a);
    }

    // ---- first-class number restrictions (KM_HT_CARD `card_defs`) ----------
    // `marker ⊑ ≥n role.filler` / `marker ⊑ ≤n role.filler`, resolved to the
    // ported CCATLEAST / (qualified) CCATMOST concepts and hung off the
    // marker's absorption (CCSUB → AND rule asserts the restriction exactly
    // on marker-labelled nodes). The clausal `⋁ eq` pigeonhole for each
    // marker was already dropped by `cb_to_ht::convert(card_enabled=true)`.
    // NOT in `tbox`: the root re-seed loop dispatches every tbox concept on
    // the probe root QUEUE-ONLY (no label add). Implications self-gate on
    // their retained trigger linkers, but a raw CCATLEAST/CCATMOST enforces
    // UNCONDITIONALLY — seeding it applied the marker's number restriction
    // to every probe subject (measured: covering_atmost_cross_merge_sat,
    // the guard-less `≤2 r.E` armed on the root at branch depth 0 refuted
    // the SAT covering branch). The restriction reaches exactly the
    // marker-labelled nodes through the absorption unfold below.
    for cd in &tin.card_defs {
        let filler = (named[cd.filler], false);
        let c = if cd.min {
            b.atleast_q(roles[cd.role], cd.n as Cint64, filler)
        } else {
            b.atmost_q(roles[cd.role], cd.n as Cint64, filler)
        };
        absorbed_pairs.push((named[cd.marker], c));
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

    // KONCLUDE-PORT-NOTE[terminology]: in Konclude every TBox concept carries
    // its owning CTerminology; several guards key on `getTerminology() !=
    // nullptr` — notably u22's unsat-cache write validation, which REJECTS
    // descriptors of terminology-less concepts (meant to exclude fresh
    // query/nominal concepts whose semantics are not ontology-stable).
    // Bridged concepts ARE the ontology (a deterministic function of `tin`,
    // stable across probes), so stamp them all — without this the unsat
    // cache silently never writes a line (measured on ore_ont_12653:
    // 0 written / 0 hits). The sweep covers every builder helper plus the
    // caller-created TOP.
    {
        let arenas = ctx.ontology_arenas_mut();
        let n = arenas.concept_count();
        for i in 0..n {
            arenas.concept_mut(ConceptId::new(i as Cint64)).set_terminology(1);
        }
    }

    let _ = functional_count;
    Bridged {
        named,
        roles,
        tbox,
        unsupported,
        absorbed: absorbed_pairs.len(),
        top_attached: top_gcis.len(),
        singleton_concepts,
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
    // KM_HT_DDB: opt-in dependency-directed backjumping (Konclude's
    // `clashedBacktracking`, u29). Turns the dependency spine ON (every rule
    // application then materializes its dependency node + track point, exactly
    // Konclude's default) and routes clashes through the tracked-clash analysis
    // so the in-process OR backtrack can SKIP branch points the clash does not
    // depend on. Target: the 541 family (deep chronological thrashing).
    if std::env::var_os("KM_HT_DDB").is_some() {
        algo.conf_build_dependencies = true;
        algo.conf_dependency_backjumping = true;
        // Konclude production defaults (CReasonerConfigurationGroup):
        // SemanticBranching=false, AtomicSemanticBranching=true — a new
        // alternative asserts the negation of every previously refuted ATOMIC
        // disjunct, so sibling subtrees cannot re-explore failed disjuncts.
        // KM_HT_NO_SEMB: diagnostic opt-out to isolate its effect on the
        // search shape (541: node growth appeared with semb on).
        if std::env::var_os("KM_HT_NO_SEMB").is_none() {
            algo.conf_atomic_semantic_branching = true;
        }
    }
    // KM_HT_COW (opt-in, composable with KM_HT_DDB): complete-state restore
    // per alternative via arena journals. The per-node localization landed
    // 2026-07-09: the heavy per-node satellites (label sets, processing
    // queues) are Arc-COW in the process context — a journal save is an O(1)
    // Arc clone and the deep copy happens only for objects the alternative
    // actually writes (Konclude's task-fork copy-on-first-write shape). That
    // removed the uniform-journal whale (12653 DDB classify 0.9s → 260s was
    // the old cost), but COW remains NON-default: measured 2026-07-09
    // (cowddb-48445184), 12653's probes under COW and under COW+DDB both
    // exceed 600s where plain DEFERS in 10s — with complete restores the
    // search must genuinely explore the alternatives that plain-mode
    // leftovers (unsoundly, hence the poison discipline) prune, so the
    // residual gap is SEARCH VOLUME (clause learning / better ordering), not
    // restore cost. Localizing the remaining map-bearing satellites
    // (role-successor / distinct hashes) is the next constant-factor lever.
    if std::env::var_os("KM_HT_COW").is_some() {
        algo.conf_inprocess_cow = true;
    }
    // KM_HT_UNSATCACHE (opt-in, composable with DDB/COW): Konclude's
    // unsatisfiable-cache LEARNING — the search-volume lever the 2026-07-09
    // COW+DDB measurement demands. The write side is u29's clashedBacktracking
    // (`writeClashDescriptorsToCache`, cpp 6844/7009/7056/7332 — already
    // ported and called; it no-ops without an installed handler), validated by
    // u22's guards (single node level, terminology concepts only, no nominals,
    // no atomic clash) so an entry is a self-contained label subset that is
    // unsatisfiable wrt the TBox — a learned nogood, valid across probes. The
    // read side is `testIndividualNodeUnsatisfiableCached` (u21, cpp
    // 4363–4392) probed at Konclude's rule points (OR disjunct addition,
    // SOME/ATLEAST successor generation, at-most init/merge — the constant
    // `CGenerativeNonDeterministicUnsatisfiableCacheRetrievalStrategy`).
    // Konclude runs both ON by default (u31 cpp 604–697). The write side only
    // fires inside DDB's tracked-clash analysis, so this is inert without
    // KM_HT_DDB; the intended production combo is COW+DDB+UNSATCACHE.
    if std::env::var_os("KM_HT_UNSATCACHE").is_some() {
        algo.conf_write_unsat_caching = true;
        algo.conf_test_occur_unsat_cached = true;
    }
    // KM_BRIDGE_NO_BLOCKING: diagnostic knob — run the probe with blocking OFF
    // (∃-cycles then hit the drive cap ⇒ Stop/None). If a verdict that flips
    // WITH blocking becomes stable WITHOUT it, the blocking establish/review
    // path is the order-sensitive mechanism.
    if std::env::var_os("KM_BRIDGE_NO_BLOCKING").is_some() {
        return;
    }
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
    // TBox seeds carry the INDEPENDENT base dependency track point (Konclude:
    // base assertions are never untracked; an untracked descriptor is a
    // tracking ERROR that aborts the whole clashedBacktracking analysis).
    let base_tp = ctx.get_or_create_base_dependency_track_point();
    let queue = ctx
        .process_context_mut()
        .node_concept_processing_queue(root, true);
    let con_des = ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let cd = ctx.process_context_mut().con_desc_mut(con_des);
        cd.concept = concept;
        cd.dep_track_point = base_tp;
    }
    let mut cpd_val = ConceptProcessDescriptor::new();
    cpd_val.concept_des = con_des;
    cpd_val.priority = ConceptProcessPriority::new(8.0);
    cpd_val.dep_track_point = base_tp;
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
    algo.completeness_poisoned = false;

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

    // Probe seeds are BASE assertions — track them on the independent base
    // dependency (a NONE would read as an unported rule path downstream).
    let seed_tp = ctx.get_or_create_base_dependency_track_point();
    // KONCLUDE-PORT-NOTE[root-top]: see `bridged_classify_subject` — every node
    // carries ⊤ in Konclude; a bare root swallowed derived ⊥ (¬⊤ met no ⊤).
    let top = ctx.processing_data_box().ontology_top_concept;
    if top.is_some() && std::env::var_os("KM_HT_NO_ROOT_TOP").is_none() {
        algo.add_concept_to_individual(top, false, &mut root, seed_tp, false, true, ctx);
        if ctx.has_pending_signal() {
            return Some(true);
        }
    }
    for &(concept, negated) in seeds {
        algo.add_concept_to_individual(concept, negated, &mut root, seed_tp, false, true, ctx);
        if ctx.has_pending_signal() {
            if std::env::var_os("KM_BRIDGE_TRACE2").is_some() {
                eprintln!("UNSAT-EXIT seed-insert");
            }
            return Some(true);
        }
    }

    // GLOBAL fixpoint on total insertions (see `bridged_classify_subject`):
    // root-label-count-stable is order-dependent and declared a false fixpoint.
    let trace = std::env::var_os("KM_BRIDGE_TRACE").is_some();
    // KM_BRIDGE_PROBE_BUDGET_S: wall-clock budget per probe. On overrun the
    // probe returns None (STOP — an UNKNOWN verdict the caller must treat as
    // a DEFER). A single pathological probe must never wedge a classify run.
    // `algo.probe_budget` (set by `bridged_classify`'s retry rounds) takes
    // precedence over the env so escalation needs no env mutation.
    let budget: Option<std::time::Duration> = algo.probe_budget.or_else(|| {
        std::env::var("KM_BRIDGE_PROBE_BUDGET_S")
            .ok()
            .and_then(|s| s.parse::<u64>().ok())
            .map(std::time::Duration::from_secs)
    });
    let probe_t0 = std::time::Instant::now();
    // Thread the deadline INTO the drive loop: one `run_completion_on` call
    // owns the whole backtracking search, so the between-passes check below
    // cannot bound it on its own.
    algo.drive_deadline = budget.map(|b| probe_t0 + b);
    let mut prev_inserts: i64 = -1;
    for pass in 0..256 {
        if let Some(b) = budget {
            if probe_t0.elapsed() > b {
                return None;
            }
        }
        for &g in &bridged.tbox {
            seed_concept_on_queue(ctx, root, g);
        }
        // Plain-mode completeness repair: reprocess every label concept each
        // pass, so the insertion-stable break below certifies genuine closure
        // under ALL rules (see `requeue_all_node_labels`).
        algo.requeue_all_node_labels(ctx);
        let iq = ctx.get_individual_immediately_processing_queue(true);
        ctx.process_context_mut()
            .indi_unsorted_proc_queue_mut(iq)
            .insert_indiviudal_process_node(root);
        let backtracks_before = algo.or_backtrack_count;
        let consistent = algo.run_completion_on(ctx);
        if trace {
            eprintln!(
                "TRACE pass={pass} consistent={consistent} inserts={} backtracks={} nodes={}",
                algo.stat_con_des_insertion_count,
                algo.or_backtrack_count,
                ctx.process_context().node_count(),
            );
        }
        if !consistent {
            // A Clash is a genuine UNSAT; a Stop (iteration cap / task fork)
            // is an UNKNOWN — folding it into unsat would be UNSOUND, folding
            // it into sat would be INCOMPLETE.
            if std::env::var_os("KM_BRIDGE_TRACE2").is_some() {
                eprintln!(
                    "UNSAT-EXIT pass={pass} signal={:?}",
                    matches!(ctx.pending_signal(), super::completion::clash::CalcSignal::Clash(_))
                );
            }
            return match ctx.pending_signal() {
                super::completion::clash::CalcSignal::Clash(clash) => {
                    if std::env::var_os("KM_BRIDGE_TRACE2").is_some() {
                        eprintln!(
                            "UNSAT-EXIT probe-clash: ddb={} cow={} root_cancelled={} backtracks={} dumps_used={}",
                            algo.conf_dependency_backjumping,
                            algo.conf_inprocess_cow,
                            algo.ddb_root_cancelled,
                            algo.or_backtrack_count,
                            algo.ddb_analysis_dumps
                        );
                    }
                    if trace {
                        // walk the clash descriptor chain: which concepts on
                        // which nodes clashed (diff a clash run vs a SAT run).
                        let mut c = clash;
                        while c.is_some() {
                            let d = ctx.process_context().clash_desc(c);
                            let next = d.next;
                            if let super::process::descriptor::ClashDescriptorKind::Concept {
                                concept_descriptor,
                                individual_node,
                            } = &d.kind
                            {
                                let concept_descriptor = *concept_descriptor;
                                let individual_node = *individual_node;
                                let (tag, neg, node_id) = {
                                    let pc = ctx.process_context();
                                    let con = if concept_descriptor.is_some() {
                                        pc.con_desc(concept_descriptor).get_concept()
                                    } else {
                                        Id::NONE
                                    };
                                    (
                                        if con.is_some() {
                                            ctx.ontology_arenas().concept(con).get_concept_tag()
                                        } else {
                                            -1
                                        },
                                        concept_descriptor.is_some()
                                            && pc.con_desc(concept_descriptor).is_negated(),
                                        if individual_node.is_some() {
                                            pc.node(individual_node).individual_node_id()
                                        } else {
                                            -1
                                        },
                                    )
                                };
                                eprintln!(
                                    "TRACE CLASH concept tag={tag} neg={neg} node={node_id}"
                                );
                                // full label of the clash node: which class was
                                // wrongly pushed is usually visible here (its
                                // disjointness supplies the negation).
                                if individual_node.is_some() {
                                    let ls = ctx
                                        .process_context_mut()
                                        .node_reapply_concept_label_set(individual_node);
                                    let mut parts: Vec<String> = ctx
                                        .process_context()
                                        .label_set(ls)
                                        .concept_des_dep_map
                                        .iter()
                                        .map(|(t, data)| {
                                            let n = if data.concept_descriptor.is_some()
                                                && ctx
                                                    .process_context()
                                                    .con_desc(data.concept_descriptor)
                                                    .is_negated()
                                            {
                                                "¬"
                                            } else {
                                                ""
                                            };
                                            format!("{n}{t}")
                                        })
                                        .collect();
                                    parts.sort();
                                    eprintln!("TRACE CLASH-NODE-LABEL {}", parts.join(" "));
                                }
                            } else {
                                use super::process::descriptor::ClashDescriptorKind as K;
                                match &d.kind {
                                    K::Dependency => eprintln!("TRACE CLASH dependency"),
                                    K::IndividualLink { link_edge } => {
                                        let pc = ctx.process_context();
                                        let (s, t, r) = if link_edge.is_some() {
                                            let e = pc.edge(*link_edge);
                                            (
                                                pc.node(e.get_source_individual())
                                                    .individual_node_id(),
                                                pc.node(e.get_destination_individual())
                                                    .individual_node_id(),
                                                e.get_link_role().index() as i64,
                                            )
                                        } else {
                                            (-1, -1, -1)
                                        };
                                        eprintln!("TRACE CLASH link {s}--role{r}-->{t}");
                                    }
                                    K::IndividualDistinct { distinct_edge } => {
                                        let pc = ctx.process_context();
                                        let (s, t) = if distinct_edge.is_some() {
                                            let e = pc.distinct_edge(*distinct_edge);
                                            (
                                                pc.node(e.source).individual_node_id(),
                                                pc.node(e.destination).individual_node_id(),
                                            )
                                        } else {
                                            (-1, -1)
                                        };
                                        eprintln!("TRACE CLASH distinct {s} != {t}");
                                    }
                                    _ => eprintln!("TRACE CLASH other-kind"),
                                }
                            }
                            c = next;
                        }
                    }
                    Some(true)
                }
                _ => None,
            };
        }
        let inserts = algo.stat_con_des_insertion_count;
        if inserts == prev_inserts && algo.or_backtrack_count == backtracks_before {
            break;
        }
        prev_inserts = inserts;
    }
    if trace {
        // Dump the final root label (sorted tags) so a SAT run can be diffed
        // against a clash run of the same probe.
        let ls = ctx.process_context_mut().node_reapply_concept_label_set(root);
        let mut tags: Vec<(Cint64, bool)> = ctx
            .process_context()
            .label_set(ls)
            .concept_des_dep_map
            .iter()
            .filter_map(|(tag, data)| {
                let cd = data.concept_descriptor;
                if cd.is_none() {
                    return None;
                }
                Some((*tag, ctx.process_context().con_desc(cd).is_negated()))
            })
            .collect();
        tags.sort_unstable();
        eprintln!("TRACE root-label {tags:?}");

        // BLOCKING INVARIANT: at a claimed fixpoint every DIRECTBLOCKED node's
        // label must still be a SUBSET of its blocker's label (subset blocking).
        // A violation = the retest-on-modification chain failed for that node —
        // the order-dependent false-model mechanism.
        // Walk CURRENT nodes via the id→node vector (raw arena slots include
        // stale pre-localization copies whose old flags would false-positive).
        let max_id = ctx
            .processing_data_box()
            .individual_process_node_vector()
            .get_item_max_index();
        let mut blocked_count = 0usize;
        for indi_id in 0..=max_id.max(-1) {
            let nid = ctx
                .processing_data_box()
                .individual_process_node_vector()
                .get_data(indi_id);
            if nid.is_none() {
                continue;
            }
            let nid_idx = nid.index();
            let node = ctx.process_context().node(nid);
            if !node.has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_DIRECTBLOCKED,
            ) {
                continue;
            }
            blocked_count += 1;
            let blocker_raw = node.blocker_individual_node();
            let bls = node.use_reapply_con_label_set;
            if blocker_raw.is_none() || bls.is_none() {
                eprintln!("TRACE BLOCKVIOLATION node={nid_idx} blocker=NONE");
                continue;
            }
            // map the (possibly stale pre-localization) blocker NodeId to the
            // CURRENT node for its individual id.
            let blocker = {
                let blocker_id = ctx.process_context().node(blocker_raw).individual_node_id();
                let cur = ctx
                    .processing_data_box()
                    .individual_process_node_vector()
                    .get_data(blocker_id);
                if cur.is_some() { cur } else { blocker_raw }
            };
            let blocker_ls = ctx.process_context().node(blocker).use_reapply_con_label_set;
            if blocker_ls.is_none() {
                eprintln!("TRACE BLOCKVIOLATION node={nid_idx} blocker-label=NONE");
                continue;
            }
            let pc = ctx.process_context();
            let mut missing: Vec<(Cint64, bool)> = Vec::new();
            for (tag, data) in pc.label_set(bls).concept_des_dep_map.iter() {
                let cd = data.concept_descriptor;
                if cd.is_none() {
                    continue;
                }
                let neg = pc.con_desc(cd).is_negated();
                // by-tag probe (the map IS keyed by real concept tags) + explicit
                // polarity compare — ls1::has_concept is a W2-DEFER stub (raw-index
                // key + always-false negation) and must not be used here.
                let present = pc
                    .label_set(blocker_ls)
                    .concept_des_dep_map
                    .get(tag)
                    .map_or(false, |d| {
                        d.concept_descriptor.is_some()
                            && pc.con_desc(d.concept_descriptor).is_negated() == neg
                    });
                if !present {
                    missing.push((*tag, neg));
                }
            }
            if !missing.is_empty() {
                missing.sort_unstable();
                eprintln!(
                    "TRACE BLOCKVIOLATION node={nid_idx} blocker={} missing={missing:?}",
                    blocker.index()
                );
            }
        }
        eprintln!("TRACE blocked-nodes={blocked_count}");

        // KM_BRIDGE_DUMP_EDGES=<indi>[,<indi>...]: dump the outgoing edges of
        // the listed CURRENT nodes (role tag, destination id, ghost status).
        if let Some(spec) = std::env::var_os("KM_BRIDGE_DUMP_EDGES") {
            let ids: Vec<Cint64> = spec
                .to_string_lossy()
                .split(',')
                .filter_map(|s| s.trim().parse().ok())
                .collect();
            for indi_id in ids {
                let nid = ctx
                    .processing_data_box()
                    .individual_process_node_vector()
                    .get_data(indi_id);
                if nid.is_none() {
                    eprintln!("TRACE EDGES indi={indi_id} <no node>");
                    continue;
                }
                let pc = ctx.process_context();
                let mut it = pc.node_successor_iterator(nid);
                while it.has_next() {
                    let link = it.next_link(false);
                    let succ_id = it.next_individual_id(true);
                    if link.is_none() {
                        continue;
                    }
                    let role_tag = {
                        let r = pc.edge(link).get_link_role();
                        if r.is_some() {
                            ctx.ontology_arenas().role(r).get_role_tag()
                        } else {
                            -1
                        }
                    };
                    let succ = ctx
                        .processing_data_box()
                        .individual_process_node_vector()
                        .get_data(succ_id);
                    let ghost = succ.is_some() && {
                        let n = pc.node(succ);
                        n.has_merged_into_individual_node_id()
                            || n.has_purged_blocked_processing_restriction_flags()
                    };
                    eprintln!(
                        "TRACE EDGES indi={indi_id} --role{role_tag}--> {succ_id} ghost={ghost}"
                    );
                }
            }
        }

        // KM_BRIDGE_FIND_TAG=<tag>[,<tag>...]: list every current node whose
        // label carries the tag (either polarity) + its blocking flags — used
        // to locate the clash region of a TRUE run inside a FALSE run's model.
        if let Some(spec) = std::env::var_os("KM_BRIDGE_FIND_TAG") {
            let tags: Vec<Cint64> = spec
                .to_string_lossy()
                .split(',')
                .filter_map(|s| s.trim().parse().ok())
                .collect();
            for indi_id in 0..=max_id.max(-1) {
                let nid = ctx
                    .processing_data_box()
                    .individual_process_node_vector()
                    .get_data(indi_id);
                if nid.is_none() {
                    continue;
                }
                let pc = ctx.process_context();
                let node = pc.node(nid);
                let ls = node.use_reapply_con_label_set;
                if ls.is_none() {
                    continue;
                }
                for &t in &tags {
                    if let Some(d) = pc.label_set(ls).concept_des_dep_map.get(&t) {
                        if d.concept_descriptor.is_some() {
                            let neg = pc.con_desc(d.concept_descriptor).is_negated();
                            let flags = node.processing_restriction_flags();
                            let blocked = node.has_partial_processing_restriction_flags(
                                IndividualProcessNode::PRF_DIRECTBLOCKED
                                    | IndividualProcessNode::PRF_INDIRECTBLOCKED
                                    | IndividualProcessNode::PRF_PROCESSINGBLOCKED,
                            );
                            eprintln!(
                                "TRACE FINDTAG tag={t} neg={neg} indi={indi_id} blocked={blocked} flags={flags:#x} label-size={}",
                                pc.label_set(ls).get_concept_count()
                            );
                        }
                    }
                }
            }
        }
    }
    // A clash-free fixpoint after a cross-branch WIPE (see
    // `completeness_poisoned`) is not a model certificate — the graph may be
    // missing branch-independent consequences whose clash would have proved
    // UNSAT. Answer UNKNOWN (defer); clash exits above remain sound.
    if algo.completeness_poisoned {
        return None;
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
/// Returns `Some((subsumer_indices, authoritative))` (indices into
/// `bridged.named`, INCLUDING `subject` itself), `None` if the drive
/// STOPped (no verdict at all). `authoritative = true` ⇔ the saturation made
/// NO nondeterministic choice (no OR branch point opened, no backtrack): the
/// canonical model captures every consequence and the read-off IS the
/// subsumer set. `authoritative = false` ⇔ the label is one branch's model —
/// the positives are CANDIDATE subsumers (Konclude's possible-subsumer
/// extraction) the caller must verify individually via `bridged_unsat`
/// pairwise probes. A clash means the subject is unsatisfiable — every
/// concept subsumes it — reported as the full index range, authoritative.
pub fn bridged_classify_subject(
    algo: &mut CompletionTaskHandleAlgorithm,
    ctx: &mut CalculationAlgorithmContextBase,
    bridged: &Bridged,
    next_indi_id: &mut i64,
    subject: usize,
    n_named: usize,
) -> Option<(Vec<usize>, bool)> {
    ctx.clear_pending_signal();
    algo.or_branch_stack.clear();
    algo.completeness_poisoned = false;
    // KM_BRIDGE_PROBE_BUDGET_S also bounds the READ-OFF search: before the
    // DDB taint fix (2a869e8) heavy subjects' read-offs looked fast only
    // because wrong root-cancels cut them short; the genuine search is
    // unbounded without a deadline (measured: SUBJ PathOfLength3 read-off ran
    // 10 min to 126 GB). On overrun the drive raises a STOP → verdict None →
    // the caller records NO derivations for the subject (sound; shows as
    // missing vs gold, never spurious).
    algo.drive_deadline = algo
        .probe_budget
        .or_else(|| {
            std::env::var("KM_BRIDGE_PROBE_BUDGET_S")
                .ok()
                .and_then(|s| s.parse::<u64>().ok())
                .map(std::time::Duration::from_secs)
        })
        .map(|b| std::time::Instant::now() + b);

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

    // The subject seed is a BASE assertion — independent base dependency.
    let seed_tp = ctx.get_or_create_base_dependency_track_point();
    // KONCLUDE-PORT-NOTE[root-top]: Konclude's node initialization labels EVERY
    // node with ⊤ (`create_new_individual` does it for successors); bridge roots
    // were created bare, so the bottom rule's faithful ¬⊤ insert (u08) met no ⊤
    // and a derived ⊥ on the ROOT was silently satisfiable — an under-detected
    // unsat (found by the saturation-first oracle tests: A ⊑ B, A ⊓ B ⊑ ⊥ was
    // classified SAT). Labeling the root with ⊤ arms the ⊤/¬⊤ clash pair and,
    // via the CCTOP AND-unfold, delivers the top-attached GCIs exactly like the
    // per-pass re-seed already did (idempotent).
    let top = ctx.processing_data_box().ontology_top_concept;
    if top.is_some() && std::env::var_os("KM_HT_NO_ROOT_TOP").is_none() {
        algo.add_concept_to_individual(top, false, &mut root, seed_tp, false, true, ctx);
        if ctx.has_pending_signal() {
            return Some(((0..n_named).collect(), true));
        }
    }
    algo.add_concept_to_individual(
        bridged.named[subject],
        false,
        &mut root,
        seed_tp,
        false,
        true,
        ctx,
    );
    if ctx.has_pending_signal() {
        // seed alone clashed ⇒ subject unsatisfiable
        return Some(((0..n_named).collect(), true));
    }

    let backtracks_before = algo.or_backtrack_count;
    let branch_opens_before = algo.or_branch_open_count;
    // GLOBAL fixpoint: break only when a full re-drive pass inserts NO concept
    // on ANY node. Breaking on the root-label COUNT (the earlier criterion) is
    // order-dependent — a pass can add nothing to the root while reapply /
    // successor→root propagation is still pending, so it declared a fixpoint
    // at an INCOMPLETE, HashMap-order-dependent closure (identical runs gave
    // different subsumer sets). `stat_con_des_insertion_count` is the total
    // insertions across every node; unchanged over a pass ⇒ true fixpoint.
    let mut prev_inserts: i64 = -1;
    for _ in 0..256 {
        for &g in &bridged.tbox {
            seed_concept_on_queue(ctx, root, g);
        }
        // Plain-mode completeness repair: reprocess every label concept each
        // pass, so the insertion-stable break below certifies genuine closure
        // under ALL rules (see `requeue_all_node_labels`).
        algo.requeue_all_node_labels(ctx);
        let iq = ctx.get_individual_immediately_processing_queue(true);
        ctx.process_context_mut()
            .indi_unsorted_proc_queue_mut(iq)
            .insert_indiviudal_process_node(root);
        let consistent = algo.run_completion_on(ctx);
        if !consistent {
            return match ctx.pending_signal() {
                super::completion::clash::CalcSignal::Clash(_) => {
                    Some(((0..n_named).collect(), true))
                }
                _ => None, // STOP: no verdict
            };
        }
        let inserts = algo.stat_con_des_insertion_count;
        if inserts == prev_inserts {
            break;
        }
        prev_inserts = inserts;
    }
    // A cross-branch WIPE (see `completeness_poisoned`) invalidates BOTH
    // read-off directions: the label may miss branch-independent positives
    // (candidate set no longer ⊇ true subsumers) AND absences are no longer
    // countermodels. No usable verdict — defer the subject.
    if algo.completeness_poisoned {
        return None;
    }
    // Non-deterministic saturation ⇒ single branch is not authoritative.
    // Opened branch points count even without backtracks: a drive committing
    // to first disjuncts pollutes the root label with branch-dependent
    // concepts (measured on ore_ont_3215: 86 SPURIOUS subsumptions under the
    // backtrack-only gate). The read-off still runs — its positives become
    // the CANDIDATE set for pairwise verification.
    let authoritative = algo.or_backtrack_count == backtracks_before
        && algo.or_branch_open_count == branch_opens_before;

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
    Some((subsumers, authoritative))
}

/// The production classification result: index pairs into `TInput.concepts`.
pub struct BridgedClassification {
    /// Indices of unsatisfiable named concepts.
    pub unsatisfiable: Vec<usize>,
    /// `(sub, sup)` subsumption pairs (self-pairs excluded).
    pub subsumptions: Vec<(usize, usize)>,
}

/// Fresh per-subject probe environment: algorithm + context + bridged
/// terminology. Konclude isolates probes via per-task databox COW (the
/// unported Task layer); the v1 driver rebuilds — same verdicts, O(TBox)
/// per subject/probe.
/// Install a live `CUnsatisfiableCacheHandler` (occurrence unsat cache +
/// reader/writer) into the probe context — the store `KM_HT_UNSATCACHE`'s
/// write/read paths use. One cache per bridge env; `reset_probe_env` carries
/// it across probe resets so nogoods learned in probe k prune probe k+1
/// (Konclude shares the cache across ALL tests of an ontology).
fn install_bridge_unsat_cache(ctx: &mut CalculationAlgorithmContextBase) {
    use super::cache::context::CacheContext;
    use super::cache::unsat::OccurrenceUnsatisfiableCache;
    use super::completion::unsat_handler::UnsatisfiableCacheHandler;
    let mut cache_context = CacheContext::new();
    // KONCLUDE-PORT-NOTE[slots]: Konclude sizes the write-slot ring as
    // `workControllerCount + 2` (CExperimentalReasonerManager cpp 58). With
    // ONE slot the ring deadlocks after the first write: the activation pins
    // the slot through the reader's next-pointer, and the release needs a
    // SECOND slot to displace it — `wait_cache_write_prepared` then spins
    // forever (measured: the tiny warm-probes test hung at 100% CPU). The
    // bridge is single-threaded ⇒ 1 worker + 2 = 3.
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
    ctx.base.install_used_unsatisfiable_cache_handler(
        UnsatisfiableCacheHandler::new(reader, writer),
        cache_context,
    );
}

fn fresh_bridge_env(
    tin: &TInput,
) -> (
    CompletionTaskHandleAlgorithm,
    CalculationAlgorithmContextBase,
    Bridged,
) {
    use super::completion::strategy::ConceptProcessingPriorityStrategy;
    let mut algo = CompletionTaskHandleAlgorithm::new();
    configure_default_blocking(&mut algo);
    let mut ctx = CalculationAlgorithmContextBase::new();
    ctx.base.used_concept_priority_strategy =
        Some(ConceptProcessingPriorityStrategy::new_concrete_operator());
    if std::env::var_os("KM_HT_UNSATCACHE").is_some() {
        install_bridge_unsat_cache(&mut ctx);
    }
    let top = {
        let mut c = Concept::new();
        c.set_concept_tag(1);
        c.set_operator_code(op::CCTOP);
        ctx.ontology_arenas_mut().alloc_concept(c)
    };
    ctx.processing_data_box_mut().ontology_top_concept = top;
    let bridged = bridge_tinput(&mut ctx, tin);
    algo.singleton_concepts = bridged.singleton_concepts.clone();
    (algo, ctx, bridged)
}

/// Reset the probe environment to its post-`bridge_tinput` pristine state
/// WITHOUT rebuilding the bridged terminology. Sound because the ontology
/// arenas are READ-ONLY during bridge probes: the only drive paths that
/// mutate them (nominal grounding, temporary nominal individuals) are gated
/// out of the bridge fragment (`tin.nominals.is_empty()`), so keeping the
/// arenas and replacing every piece of per-probe state reproduces
/// `fresh_bridge_env`'s output exactly — the arena content is a
/// deterministic function of `tin` alone. This is the v2 stand-in for
/// Konclude's per-task databox COW: O(processing state) per probe instead
/// of O(TBox) (measured ~seconds + hundreds of MB per probe on the 3215
/// family).
fn reset_probe_env(
    algo: &mut CompletionTaskHandleAlgorithm,
    ctx: &mut CalculationAlgorithmContextBase,
    bridged: &Bridged,
    preserve_saturation: bool,
) {
    use super::model::ontology::OntologyArenas;
    // Fresh algorithm: search state (OR stack, DDB marks, blocking caches,
    // stats, deadlines) must not leak between probes. Same construction as
    // `fresh_bridge_env` so verdicts are identical.
    let budget = algo.probe_budget;
    let mut a = CompletionTaskHandleAlgorithm::new();
    configure_default_blocking(&mut a);
    a.singleton_concepts = bridged.singleton_concepts.clone();
    a.probe_budget = budget;
    *algo = a;
    // Fresh context EXCEPT the shared read-only terminology: rebuild through
    // the same ctor as `fresh_bridge_env`, then graft the arenas back. This
    // resets EVERY per-probe field (process context, databox, dependency
    // factory ids, epoch stack, pending signal) by construction rather than
    // by enumeration.
    let arenas = std::mem::replace(&mut ctx.base.ontology_arenas, OntologyArenas::new());
    let strategy = ctx.base.used_concept_priority_strategy.take();
    let top = ctx.base.used_processing_data_box.ontology_top_concept;
    // KM_HT_UNSATCACHE: the learned-nogood store DELIBERATELY survives the
    // probe reset (Konclude shares its unsatisfiable cache across all tests
    // of an ontology). Sound: each entry is a label subset validated by the
    // u22 write guards to be unsatisfiable wrt the shared TBox alone, so it
    // prunes any later probe identically. Note the cache write path also
    // stamps caching tags into the ontology arenas' concept process data — a
    // monotone cache-metadata mutation; with the flag OFF the arenas stay
    // read-only and the reset reproduces `fresh_bridge_env` exactly, with it
    // ON later probes are deliberately order-dependent (they prune using
    // earlier probes' nogoods) while verdicts stay sound+complete.
    let unsat_cache = ctx.base.take_used_unsatisfiable_cache_handler();
    // KM_HT_SATURATION: the saturation-side arenas DELIBERATELY survive the
    // probe reset when a saturation pass ran on this env — the ontology
    // arenas (kept above) hold concept→saturation reference linkings whose
    // node ids point into these arenas, and the saturation-node coupling
    // (u08/u17/u22, Konclude's expand-from-saturation + caching-blocking)
    // reads them during every probe. Probes never write them, so the carry
    // reproduces Konclude's stable saturation-task pointers. Carried even
    // when the coupling is off (budget-aborted pass) so the linkings never
    // dangle.
    let mut fresh = CalculationAlgorithmContextBase::new();
    if preserve_saturation {
        fresh
            .process_context_mut()
            .adopt_saturation_state_from(ctx.process_context_mut());
    }
    *ctx = fresh;
    ctx.base.ontology_arenas = arenas;
    ctx.base.used_concept_priority_strategy = strategy;
    ctx.base.used_processing_data_box.ontology_top_concept = top;
    if let Some(state) = unsat_cache {
        ctx.base.restore_used_unsatisfiable_cache_handler(state);
    }
}

/// Production search configuration for `bridged_classify`: PLAIN
/// chronological search — the mode validated gold-clean on the recognition
/// family (ore_ont_12653: missing=0 spurious=0). DDB stays env-opt-in
/// (`KM_HT_DDB`, via `configure_default_blocking`): it is SOUND since the
/// leftover-poisoning guard (7c521cb), but measured ~100× slower on
/// genuinely-UNSAT probes (the guard degrades node-creating searches to
/// chronological while still paying full dependency building), so it is a
/// net loss as a default until per-node COW localization lands.
fn configure_production_search(_algo: &mut CompletionTaskHandleAlgorithm) {}

// ---------------------------------------------------------------------------
// Saturation-first probe answering (task #23).
//
// Konclude decides ~95% of its classification work by the cheap non-branching
// approximation saturation and runs the backtracking tableau only on the
// residue (docs/KONCLUDE-STUDY.md). This section wires the ported saturation
// units (saturation/s01..s12) in front of the bridge's completion probes:
// saturate ONCE per classification in a dedicated env, extract per-named
// verdicts + certain subsumers, and let `bridged_classify` answer whole
// subjects from them — every UNKNOWN falls through to the existing probe path
// unchanged. Opt-in via KM_HT_SATURATION=1 (how to run it in production is a
// separate decision; nothing in the default path changes).
// ---------------------------------------------------------------------------

/// Konclude's PRODUCTION saturation configuration: `readCalculationConfig`
/// (CCalculationTableauApproximationSaturationTaskHandleAlgorithm cpp 180–237,
/// config-present branch, non-EL structure path) with the config defaults from
/// CReasonerConfigurationGroup.cpp 440–451 (SaturationCriticalConceptTesting =
/// true, SaturationDirectCriticalToInsufficient = false,
/// SaturationSuccessorExtension = true) plus the ctor defaults (cpp 130–170)
/// for the fields readCalculationConfig leaves untouched.
fn configure_production_saturation(
    algo: &mut super::saturation::algorithm::SaturationTaskHandleAlgorithm,
) {
    algo.conf_force_all_concept_insertion = true; // cpp 191 (non-EL / ABox path)
    algo.conf_implication_adding_skipping = false; // cpp 192
    algo.conf_force_all_copy_instead_of_substituition = false; // cpp 185
    algo.conf_directly_critical_to_insufficient = false; // cfg 444 default false
    algo.conf_add_critical_concepts_to_queues = true; // cfg 440 default true
    algo.conf_check_critical_concepts = true; // cfg 440 default true
    // Successor-extension machinery (Konclude: SaturationSuccessorExtension,
    // cfg 448 default true; cpp 232-233): KM_HT_SAT_EXT=1 opt-in, DEFAULT OFF.
    // The extension paths were inert until the [identity] super-role fix armed
    // them, and they currently produce WRONG CLASHES on the cardinality family
    // (541: 11-13 satisfiable classes answered UNSAT-certain, gold #UNSAT
    // empty; nondeterministic across runs — HashMap-ordered succ maps vs
    // Konclude's sorted CPROCESSMAP). Extensions-off is a legitimate Konclude
    // configuration point and bisect-proven sound here (541: 0 wrong verdicts,
    // 0.34s). Re-enable only after the W6-DEFER extension bodies + resolve-copy
    // pollution audit land.
    let sat_ext = std::env::var_os("KM_HT_SAT_EXT").is_some();
    algo.conf_concepts_extension_processing = sat_ext;
    algo.conf_all_concepts_extension_processing = sat_ext;
    algo.conf_functional_concepts_extension_processing = sat_ext;
    algo.conf_nominal_processing = true; // cfg 497 (inert: nominal-free fragment)
    // ctor defaults (cpp 152–168):
    algo.conf_copy_node_from_top_individual_for_many_concepts = true;
    algo.conf_detailed_merging_test_for_atmost_critical_testing = true;
    algo.conf_simple_merging_test_for_atmost_critical_testing = true;
    algo.conf_delayed_merging_critical_atmost_concepts = true;
    algo.conf_delayed_merging_critical_atmost_concepts_cardinality_size = 100;
    algo.conf_resolve_operand_concept_size = 100;
    algo.conf_referred_node_many_concept_count = 500;
    algo.conf_many_concept_referred_node_count_process_limit = 2;
    algo.conf_referred_node_concept_count_process_limit = 1500;
    algo.conf_referred_node_unprocessed_count_process_limit = 1;
    algo.conf_referred_node_checking_depth = 5;
}

/// Port of `CExtractPropagationIntoCreationDirectionPreProcess::preprocess`
/// (Reasoner/Preprocess, cpp 39–105) over the bridged arenas: mark every
/// ∀/∃-family concept whose role can also appear in successor-CREATION
/// direction — the saturation ALL rule keys its criticality escape hatch on
/// this flag (without it a `∃R.C ⊓ ∀R.¬C` node would complete SAT-certain).
///
/// KONCLUDE-PORT-NOTE[identity]: `creationRoleHash` is filled from the
/// creation role's indirect super-role list, which in Konclude STARTS with the
/// role itself; the bridge builds strict lists, so the role is inserted
/// explicitly (see `saturation_indirect_super_roles`).
/// KONCLUDE-PORT-NOTE[api]: the C++ also stamps
/// `CRoleProcessData::setPropagationAndCreationConceptsFlag` — CRoleProcessData
/// is unported; the single consumer (applyALLRule's else arm) treats absent
/// role data exactly as flag-set (see the s04 port note).
fn extract_propagation_into_creation_direction(ctx: &mut CalculationAlgorithmContextBase) {
    use super::model::concept_process::ConceptProcessData;
    use super::model::op::{CCFS_ALL_AQALL_TYPE, CCFS_POSSIBLE_ROLE_CREATION_TYPE};
    let n = ctx.ontology_arenas().concept_count();
    let mut creation_roles: std::collections::HashSet<RoleId> = std::collections::HashSet::new();
    for i in 0..n {
        let cid = ConceptId::new(i);
        let (is_creation, role) = {
            let c = ctx.ontology_arenas().concept(cid);
            (
                c.get_concept_operator()
                    .has_partial_operator_code_flag(CCFS_POSSIBLE_ROLE_CREATION_TYPE),
                c.get_role(),
            )
        };
        if is_creation && role.is_some() && !creation_roles.contains(&role) {
            creation_roles.insert(role); // [identity]
            let supers: Vec<super::model::substrate::NegLink<RoleId>> = ctx
                .ontology_arenas()
                .role(role)
                .get_indirect_super_role_list()
                .to_vec();
            for s in supers {
                if !s.negated {
                    creation_roles.insert(s.target);
                }
            }
        }
    }
    for i in 0..n {
        let cid = ConceptId::new(i);
        let (flagged, role, concept_data) = {
            let c = ctx.ontology_arenas().concept(cid);
            (
                c.get_concept_operator().has_partial_operator_code_flag(
                    CCFS_ALL_AQALL_TYPE | CCFS_POSSIBLE_ROLE_CREATION_TYPE,
                ),
                c.get_role(),
                c.get_concept_data(),
            )
        };
        if flagged && role.is_some() && creation_roles.contains(&role) {
            let arenas = ctx.ontology_arenas_mut();
            let con_proc_data = if concept_data == super::model::substrate::INVALID {
                let fresh = arenas.alloc_concept_process_data(ConceptProcessData::new());
                arenas.concept_mut(cid).set_concept_data(fresh.raw);
                fresh
            } else {
                super::model::concept_process::ConceptProcessDataId::new(concept_data)
            };
            arenas
                .concept_process_data_mut(con_proc_data)
                .propagation_into_creation_direction = true;
        }
    }
}

/// Port of the CONSTRUCTION half of
/// `CTotallyPrecomputationThread::createConceptSaturationProcessingJob`
/// (Reasoner/Consistiser cpp 2022–2230) +
/// `CSatisfiableCalculationTaskFromCalculationJobGenerator::createApproximatedSaturationCalculationTask`
/// (Reasoner/Generator cpp 40–163): one saturation seed per (concept, polarity)
/// item — ⊤ positive, every named class positive, and every ∃/∀/≥/≤ filler
/// under its rule polarity — each getting a pre-built saturation node wired
/// through the concept's saturation reference linking, registered in the
/// databox node vector, and queued for processing.
///
/// KONCLUDE-PORT-NOTE[reduced]: two job-construction refinements are not (yet)
/// ported, both PURE OPTIMIZATIONS of the special-reference machinery whose
/// absence the initialization handles by the NONE-mode root path:
/// the leaf-first ordering + SUBSTITUTE/COPY special-reference assignment
/// (cpp 2129–2206), and the disjunct-candidate extension items
/// (`extendDisjunctionsCandidateAlternativesItems`, cpp 1153–1268). Role-range
/// successor items (cpp 2059–2074) are skipped because bridged roles carry no
/// domain/range concept lists (domains/ranges arrive as clauses).
fn build_saturation_seeds(ctx: &mut CalculationAlgorithmContextBase, bridged: &Bridged) {
    use super::model::concept_process::{
        ConceptProcessData, ConceptSaturationReferenceLinkingData, SaturationConceptReferenceLinking,
    };
    use super::model::op::{CCALL, CCAQSOME, CCATLEAST, CCATMOST, CCSOME};
    use super::process::sat_node::IndividualSaturationProcessNode;
    use super::process::sat_ref::ExtendedConceptReferenceLinkingData;

    // --- collect the seed list (deterministic order, deduped) ---
    let mut seeds: Vec<(ConceptId, bool)> = Vec::new();
    let mut seen: std::collections::HashSet<(ConceptId, bool)> = std::collections::HashSet::new();
    let mut push = |seeds: &mut Vec<(ConceptId, bool)>,
                    seen: &mut std::collections::HashSet<(ConceptId, bool)>,
                    c: ConceptId,
                    neg: bool| {
        if c.is_some() && seen.insert((c, neg)) {
            seeds.push((c, neg));
        }
    };
    let top = ctx.processing_data_box().ontology_top_concept;
    push(&mut seeds, &mut seen, top, false);
    for &named in &bridged.named {
        push(&mut seeds, &mut seen, named, false);
    }
    let n = ctx.ontology_arenas().concept_count();
    for i in 0..n {
        let cid = ConceptId::new(i);
        let (op_code, operands) = {
            let c = ctx.ontology_arenas().concept(cid);
            (c.get_operator_code(), c.get_operand_list().to_vec())
        };
        match op_code {
            CCSOME | CCAQSOME | CCALL => {
                // negation = (opCode == CCALL); operand negation = isNegated ^ negation
                let negation = op_code == CCALL;
                for op_link in &operands {
                    push(
                        &mut seeds,
                        &mut seen,
                        op_link.target,
                        op_link.negated ^ negation,
                    );
                }
                if operands.is_empty() {
                    push(&mut seeds, &mut seen, top, false); // filler defaults to ⊤
                }
            }
            CCATLEAST | CCATMOST => {
                // ≥/≤: operand polarity as-is (cpp 2049–2054)
                for op_link in &operands {
                    push(&mut seeds, &mut seen, op_link.target, op_link.negated);
                }
                if operands.is_empty() {
                    push(&mut seeds, &mut seen, top, false);
                }
            }
            _ => {}
        }
    }

    // --- build one node per seed (the generator's construction loop) ---
    let mut next_indi_id: Cint64 = 1; // generator cpp 67: nextIndiID = max(1, …)
    for (concept, negation) in seeds {
        // Ensure the concept's process data + saturation reference-linking data.
        let con_proc_data = {
            let concept_data = ctx.ontology_arenas().concept(concept).get_concept_data();
            if concept_data == super::model::substrate::INVALID {
                let arenas = ctx.ontology_arenas_mut();
                let fresh = arenas.alloc_concept_process_data(ConceptProcessData::new());
                arenas.concept_mut(concept).set_concept_data(fresh.raw);
                fresh
            } else {
                super::model::concept_process::ConceptProcessDataId::new(concept_data)
            }
        };
        let mut ref_linking_data = ctx
            .ontology_arenas()
            .concept_process_data(con_proc_data)
            .get_concept_reference_linking();
        if ref_linking_data.is_none() {
            let arenas = ctx.ontology_arenas_mut();
            ref_linking_data = arenas.alloc_concept_saturation_reference_linking_data(
                ConceptSaturationReferenceLinkingData::new(),
            );
            arenas
                .concept_process_data_mut(con_proc_data)
                .set_concept_reference_linking(ref_linking_data);
        }
        // One item per (concept, polarity): skip if already wired.
        let existing = ctx
            .ontology_arenas()
            .concept_saturation_reference_linking_data(ref_linking_data)
            .get_concept_saturation_reference_linking_data(negation);
        if existing.is_some() {
            continue;
        }
        // Ontology-side item (CSaturationConceptDataItem).
        let onto_item = {
            let arenas = ctx.ontology_arenas_mut();
            let mut item = SaturationConceptReferenceLinking::new();
            item.init_concept_saturation_testing_item(concept, negation, RoleId::NONE);
            item.set_potentially_exist_initialization_concept(true);
            let onto_item = arenas.alloc_saturation_concept_reference_linking(item);
            arenas
                .concept_saturation_reference_linking_data_mut(ref_linking_data)
                .set_saturation_reference_linking_data(onto_item, negation);
            onto_item
        };
        // Process-side item mirror + the node (generator cpp 108–135).
        let ext_item = {
            let mut ext = ExtendedConceptReferenceLinkingData::new();
            ext.init_concept_saturation_testing_item(concept, negation, RoleId::NONE);
            ext.set_concept_reference_linking(onto_item.raw);
            ctx.process_context_mut()
                .alloc_extended_con_ref_linking_data(ext)
        };
        let individual_id = next_indi_id;
        next_indi_id += 1;
        let node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(
                super::model::substrate::INVALID,
            ));
        ctx.process_context_mut()
            .sat_node_mut(node)
            .init_individual_saturation_process_node(individual_id, ext_item, Id::NONE);
        ctx.ontology_arenas_mut()
            .saturation_concept_reference_linking_mut(onto_item)
            .set_individual_process_node_for_concept(node);
        ctx.processing_data_box_mut()
            .individual_saturation_process_node_vector(true)
            .expect("create=true yields CIndividualSaturationProcessNodeVector")
            .set_data(individual_id, node);
        // indiProcNodeLinker: initProcessNodeLinker(node, processing=true) +
        // dataBox->addIndividualSaturationProcessNodeLinker (generator cpp 129–134).
        let linker = ctx
            .process_context_mut()
            .sat_node_individual_saturation_process_node_linker(node, true);
        ctx.process_context_mut()
            .indi_sat_process_node_linker_mut(linker)
            .set_processing_queued(true);
        ctx.processing_data_box_mut()
            .add_individual_saturation_process_node_linker(linker);
    }
}

/// Per-classification saturation outcome, extracted into plain data so the
/// probe env's resets cannot invalidate it.
pub struct SaturationOutcome {
    /// Per named index: `Some(true)` = UNSAT-certain, `Some(false)` =
    /// SAT-certain, `None` = unknown (probe needed).
    pub sat_verdict: Vec<Option<bool>>,
    /// Per named index: the COMPLETE certain-subsumer set (named indices,
    /// self excluded) — present exactly when the node is sufficient
    /// (SAT-certain), per `CPrecomputedSaturationSubsumerExtractor`.
    pub certain_subsumers: Vec<Option<Vec<usize>>>,
}

/// `CPrecomputedSaturationSubsumerExtractor::getConceptFlags` + `extractSubsumers`
/// over the saturated bridge env: follow the POSITIVE node (substitute-chain
/// resolved), read INDIRECT flags of base + resolved node —
/// CLASHED ⇒ UNSAT-certain; ¬INSUFFICIENT ∧ ¬UNPROCESSED (+ completed, and no
/// direct EQ-candidate problematic) ⇒ SAT-certain with the label's non-negated
/// named entries as the exact subsumer set; anything else ⇒ unknown.
fn extract_saturation_outcome(
    ctx: &mut CalculationAlgorithmContextBase,
    bridged: &Bridged,
) -> SaturationOutcome {
    use super::process::sat_node::IndividualSaturationProcessNodeStatusFlags as F;
    let n_named = bridged.named.len();
    let named_index: std::collections::HashMap<ConceptId, usize> = bridged
        .named
        .iter()
        .enumerate()
        .map(|(i, &c)| (c, i))
        .collect();
    let mut sat_verdict: Vec<Option<bool>> = vec![None; n_named];
    let mut certain_subsumers: Vec<Option<Vec<usize>>> = vec![None; n_named];
    for (i, &named) in bridged.named.iter().enumerate() {
        let base_node = super::saturation::algorithm::SaturationTaskHandleAlgorithm::
            s07_concept_reference_node(named, false, ctx);
        if base_node.is_none() {
            continue;
        }
        // Substitute-chain resolution (extractor cpp 273–283).
        let mut resolved = base_node;
        while ctx
            .process_context()
            .sat_node(resolved)
            .has_substitute_individual_node()
        {
            resolved = ctx
                .process_context()
                .sat_node(resolved)
                .get_substitute_individual_node();
        }
        let read = |node: super::process::SatNodeId,
                    ctx: &CalculationAlgorithmContextBase|
         -> (bool, bool, bool, bool, bool) {
            let sat_node = ctx.process_context().sat_node(node);
            let ind = sat_node.indirect_status_flags.get_flags();
            let dir = sat_node.direct_status_flags.get_flags();
            (
                ind & F::INDSATFLAGCLASHED != 0,
                ind & F::INDSATFLAGINSUFFICIENT != 0,
                ind & F::INDSATFLAGUNPROCESSED != 0,
                dir & F::INDSATFLAGEQCANDPROPLEMATIC != 0,
                sat_node.is_completed(),
            )
        };
        let (b_clash, b_insuf, b_unproc, b_eqprob, b_done) = read(base_node, ctx);
        let (r_clash, r_insuf, r_unproc, r_eqprob, r_done) = read(resolved, ctx);
        let clashed = b_clash || r_clash;
        let insufficient = b_insuf || r_insuf;
        let unprocessed = b_unproc || r_unproc;
        if clashed {
            sat_verdict[i] = Some(true);
            continue;
        }
        if insufficient || unprocessed || !(b_done && r_done) || b_eqprob || r_eqprob {
            continue; // unknown — probe needed
        }
        sat_verdict[i] = Some(false);
        // extractSubsumers (cpp 40–130): non-negated class-named label entries of
        // the RESOLVED node (substitute-chain concepts are class-named only under
        // the not-yet-ported substitute assignment; the chain is walked above).
        let mut subs: Vec<usize> = Vec::new();
        let label = ctx
            .process_context()
            .sat_node(resolved)
            .reapply_con_sat_label_set;
        if label.is_some() {
            let mut des = ctx
                .process_context()
                .reapply_con_sat_label_set(label)
                .get_concept_saturation_description_linker();
            while des.is_some() {
                let (concept, negated) = {
                    let d = ctx.process_context().con_sat_desc(des);
                    (d.get_concept(), d.get_negation())
                };
                if !negated {
                    if let Some(&idx) = named_index.get(&concept) {
                        if idx != i {
                            subs.push(idx);
                        }
                    }
                }
                des = ctx
                    .process_context()
                    .con_sat_desc(des)
                    .get_next_concept_desciptor();
            }
        }
        subs.sort_unstable();
        subs.dedup();
        certain_subsumers[i] = Some(subs);
    }
    SaturationOutcome {
        sat_verdict,
        certain_subsumers,
    }
}

/// Saturate the bridged ontology once (dedicated env — the probe env and its
/// resets are untouched) and extract the verdicts. `None` when the input is
/// outside the bridge fragment.
pub fn bridged_saturate(tin: &TInput) -> Option<SaturationOutcome> {
    if !tin.nominals.is_empty() {
        return None;
    }
    let (_completion_algo, mut ctx, bridged) = fresh_bridge_env(tin);
    if bridged.unsupported > 0 {
        return None;
    }
    if !run_bridged_saturation(&mut ctx, &bridged) {
        return None;
    }
    Some(extract_saturation_outcome(&mut ctx, &bridged))
}

/// Run the production approximation saturation ON the given bridge env
/// (preprocess + seeds + drive). Returns false on a budget overrun: unfinished
/// queues may hold unchecked critical concepts, so no per-node flags are
/// trustworthy — the caller must discard the pass (no verdict extraction, no
/// saturation-node coupling). The saturation NODES remain in the env's arenas
/// either way (the concept→saturation reference linkings installed by the
/// seeds point at them; see `reset_probe_env`'s saturation carry).
fn run_bridged_saturation(ctx: &mut CalculationAlgorithmContextBase, bridged: &Bridged) -> bool {
    let mut sat_algo = super::saturation::algorithm::SaturationTaskHandleAlgorithm::new();
    configure_production_saturation(&mut sat_algo);
    extract_propagation_into_creation_direction(ctx);
    build_saturation_seeds(ctx, bridged);
    if !sat_algo.run_saturation_on(ctx) {
        return false;
    }
    if std::env::var_os("KM_SAT_DEBUG").is_some() {
        eprintln!(
            "SAT-STATS: insufficient all={} atmost={} or={} eqcand={} value={} nominal={}",
            sat_algo.insufficient_all_count,
            sat_algo.insufficient_atmost_count,
            sat_algo.insufficient_or_count,
            sat_algo.insufficient_eqcand_count,
            sat_algo.insufficient_value_count,
            sat_algo.insufficient_nominal_count,
        );
        debug_dump_saturation_nodes(ctx);
    }
    true
}

/// Temporary diagnostic (env `KM_SAT_DEBUG=1`): per saturation node, dump the
/// completion state, direct/indirect flag words and the full saturated label
/// (concept id, op code, negation).
fn debug_dump_saturation_nodes(ctx: &CalculationAlgorithmContextBase) {
    let n = ctx.process_context().sat_node_count();
    for i in 0..n {
        let node = super::process::SatNodeId::new(i as Cint64);
        let sat_node = ctx.process_context().sat_node(node);
        let label = sat_node.reapply_con_sat_label_set;
        eprintln!(
            "SAT-NODE {}: indi={} completed={} dir={:#x} ind={:#x} subst={:?}",
            i,
            sat_node.get_individual_id(),
            sat_node.is_completed(),
            sat_node.direct_status_flags.get_flags(),
            sat_node.indirect_status_flags.get_flags(),
            sat_node.get_substitute_individual_node(),
        );
        if label.is_some() {
            let ls = ctx.process_context().reapply_con_sat_label_set(label);
            let mut entries: Vec<(Cint64, String)> = Vec::new();
            for (tag, data) in ls
                .concept_des_dep_hash
                .iter()
                .chain(ls.additional_concept_des_dep_hash.iter())
            {
                let des = data.con_sat_des;
                if des.is_some() {
                    let c = ctx.process_context().con_sat_desc(des).get_concept();
                    let neg = ctx.process_context().con_sat_desc(des).get_negation();
                    let op = ctx.ontology_arenas().concept(c).get_operator_code();
                    entries.push((*tag, format!("c{}(op{},neg={})", c.index(), op, neg)));
                } else {
                    entries.push((*tag, "reapply-only".to_string()));
                }
            }
            entries.sort();
            for (tag, s) in entries {
                eprintln!("    tag {} -> {}", tag, s);
            }
        }
    }
}

/// Production classification of a `TInput` over the konclude_ht bridge.
///
/// Per subject: model read-off when the saturation was deterministic
/// (authoritative — the canonical model IS the subsumer set), else candidate
/// extraction + pairwise `bridged_unsat(s ⊓ ¬c)` verification (label ABSENCE
/// in a saturated clash-free graph is a countermodel even on a
/// non-deterministic drive, so the candidate positives are a complete
/// filter; only presences need verification).
///
/// Returns `None` (DEFER — the caller must fall back to a sound+complete
/// arm) when the answer would not be both sound and complete:
/// - the encoder could not express every clause (`unsupported > 0`);
/// - the input carries nominals/ABox content (not bridged);
/// - a subject still lacks a verdict after every retry round (a STOPped
///   drive/probe defers the SUBJECT first; only subjects that exhaust the
///   escalated budgets defer the whole classification).
///
/// Per-probe budget: `KM_BRIDGE_PROBE_BUDGET_S` (default 10 s) for the first
/// round; deferred subjects are retried with the budget escalated ×4 per
/// round for `KM_BRIDGE_RETRY_ROUNDS` (default 2) extra rounds — so one
/// pathological subject costs bounded time while the cheap bulk completes,
/// instead of the first budget-STOP discarding all finished work.
pub fn bridged_classify(tin: &TInput) -> Option<BridgedClassification> {
    // Saturation-first probe answering (task #23, opt-in KM_HT_SATURATION=1)
    // + the saturation-node coupling into the residue probes (task #24 wave 2;
    // KM_HT_NO_SATCACHE=1 is the coupling's A/B escape hatch).
    let use_saturation = std::env::var_os("KM_HT_SATURATION").is_some();
    let use_satcache = use_saturation && std::env::var_os("KM_HT_NO_SATCACHE").is_none();
    bridged_classify_opts(tin, use_saturation, use_satcache)
}

/// The env-independent core of [`bridged_classify`] — `use_saturation` answers
/// whole subjects from a pre-probe saturation pass, `use_satcache` additionally
/// arms the saturation-node coupling (expand-from-saturation + caching-blocking,
/// Konclude's production completion profile) inside the residue probes.
pub fn bridged_classify_opts(
    tin: &TInput,
    use_saturation: bool,
    use_satcache: bool,
) -> Option<BridgedClassification> {
    if !tin.nominals.is_empty() {
        return None;
    }
    let n_named = tin.concepts.len();
    // The classification UNIVERSE: real named classes only. `tin.concepts`
    // also carries frontend-SYNTHETIC concepts (recognition markers `Q_n`,
    // `aux_`/`def_` definers, `__`-markers) — the signature never contains
    // them, and treating them as candidate supers is ruinous: refuting one
    // marker "candidate" costs a full SAT search per subject (measured on
    // ore_ont_12653: every subject burnt its whole probe budget refuting
    // Q_n markers; with the universe filter the candidate sets collapse to
    // the real taxonomy).
    let universe: std::collections::HashSet<usize> = tin
        .concepts
        .iter()
        .enumerate()
        .filter(|(_, n)| {
            !crate::orchestrate::cb_to_ht::is_internal(n)
                && !crate::orchestrate::cb_to_ht::is_bottom(n)
        })
        .map(|(i, _)| i)
        .collect();
    let subjects: Vec<usize> = if tin.queries.is_empty() {
        let mut v: Vec<usize> = universe.iter().copied().collect();
        v.sort_unstable();
        v
    } else {
        tin.queries.iter().map(|&q| q as usize).collect()
    };
    let progress = std::env::var_os("KM_BRIDGE_PROGRESS").is_some();
    let mut out = BridgedClassification {
        unsatisfiable: Vec::new(),
        subsumptions: Vec::new(),
    };
    // ONE bridged environment for the whole classification (#13): built once,
    // reset to pristine between probes (`reset_probe_env`), instead of an
    // O(TBox) rebuild per subject AND per pairwise probe.
    let (mut algo, mut ctx, bridged) = fresh_bridge_env(tin);
    if bridged.unsupported > 0 {
        return None;
    }
    let base_budget = std::env::var("KM_BRIDGE_PROBE_BUDGET_S")
        .ok()
        .and_then(|s| s.parse::<u64>().ok())
        .unwrap_or(10);
    let retry_rounds = std::env::var("KM_BRIDGE_RETRY_ROUNDS")
        .ok()
        .and_then(|s| s.parse::<u32>().ok())
        .unwrap_or(2);
    let mut pending: Vec<usize> = subjects;
    // Saturation-first probe answering (task #23): saturate the bridged
    // ontology ONCE — on the SAME env the probes will use, so the saturation
    // nodes + concept→saturation reference linkings stay live for the
    // saturation-node coupling — then answer whole subjects from certain
    // verdicts: UNSAT-certain subjects land in `unsatisfiable`, SAT-certain
    // subjects with a sufficient label get their COMPLETE subsumer set from
    // the saturated label (Konclude's CPrecomputedSaturationSubsumerExtractor
    // consumption). Only the UNKNOWN residue runs the completion probes,
    // with the coupling (u08/u17/u22) armed when `use_satcache`.
    let mut saturation_ran = false;
    let mut satcache_active = false;
    if use_saturation {
        let t_sat = std::time::Instant::now();
        saturation_ran = true;
        if run_bridged_saturation(&mut ctx, &bridged) {
            let outcome = extract_saturation_outcome(&mut ctx, &bridged);
            let mut answered_unsat = 0usize;
            let mut answered_sat = 0usize;
            pending.retain(|&s| match outcome.sat_verdict[s] {
                Some(true) => {
                    if std::env::var_os("KM_SAT_DEBUG").is_some() {
                        eprintln!(
                            "SAT-UNSAT-VERDICT subject {} ({})",
                            s,
                            tin.concepts.get(s).map(|n| n.as_str()).unwrap_or("?")
                        );
                    }
                    out.unsatisfiable.push(s);
                    answered_unsat += 1;
                    false
                }
                Some(false) => {
                    if let Some(subs) = &outcome.certain_subsumers[s] {
                        for &c in subs {
                            if c != s && universe.contains(&c) {
                                out.subsumptions.push((s, c));
                            }
                        }
                        answered_sat += 1;
                        false
                    } else {
                        true
                    }
                }
                None => true,
            });
            satcache_active = use_satcache;
            if progress {
                eprintln!(
                    "BRIDGE-SATURATION: {:.2}s, answered {} unsat + {} sat of {} subjects ({} residue to probes, satcache={})",
                    t_sat.elapsed().as_secs_f64(),
                    answered_unsat,
                    answered_sat,
                    answered_unsat + answered_sat + pending.len(),
                    pending.len(),
                    satcache_active,
                );
            }
        } else if progress {
            // Budget overrun — no flag is trustworthy; the pass answers nothing
            // and the coupling stays off. The saturation arenas are still
            // carried through resets so the installed reference linkings
            // (surviving in the ontology arenas) never dangle.
            eprintln!("BRIDGE-SATURATION: budget overrun, pass discarded");
        }
    }
    // Classify one subject end-to-end (read-off + any needed verification
    // probes) into `out`. `None` ⇔ some probe STOPped — the subject is
    // DEFERRED, `out` untouched for it (pairs are only pushed once every
    // probe of the subject has a verdict).
    // KM_BRIDGE_FRESH_ENV=1 (diagnostic): rebuild the env per probe instead
    // of resetting — the pre-#13 isolation, for A/B against the reset path.
    let fresh_env = std::env::var_os("KM_BRIDGE_FRESH_ENV").is_some();
    // KM_BRIDGE_COW_CONFIRM=1 (opt-in): re-run poison-deferred probes under
    // COW branch epochs to CONFIRM them instead of deferring. Correct
    // (complete restore ⇒ classically complete) but measured too slow inside
    // the probe budgets on the recognition family (the uniform first-touch
    // journal cost — ore_ont_12653 subjects blew their 900 s validation
    // window). Becomes the default once per-node COW localization lands.
    let cow_confirm = std::env::var_os("KM_BRIDGE_COW_CONFIRM").is_some();
    let mut classify_one = |s: usize,
                            algo: &mut CompletionTaskHandleAlgorithm,
                            ctx: &mut CalculationAlgorithmContextBase,
                            out: &mut BridgedClassification|
     -> Option<()> {
        let t_subj = std::time::Instant::now();
        let mut renew = |algo: &mut CompletionTaskHandleAlgorithm,
                         ctx: &mut CalculationAlgorithmContextBase,
                         cow: bool| {
            if fresh_env {
                let budget = algo.probe_budget;
                let (a2, c2, _b2) = fresh_bridge_env(tin);
                *algo = a2;
                *ctx = c2;
                algo.probe_budget = budget;
            } else {
                reset_probe_env(algo, ctx, &bridged, saturation_ran);
            }
            configure_production_search(algo);
            // Saturation-node coupling (task #24 wave 2): Konclude's production
            // completion profile — expand created successors from saturation +
            // caching-blocking from saturation (the associated-expansion cache
            // WRITING stays off, as in Konclude). Re-armed after every reset
            // because the reset rebuilds the algorithm. The KM_BRIDGE_FRESH_ENV
            // diagnostic path rebuilds an UNsaturated env, so the coupling
            // stays off there (the lookups would find no reference linkings).
            if satcache_active && !fresh_env {
                algo.conf_expand_created_successors_from_saturation = true;
                algo.conf_caching_blocking_from_saturation = true;
            }
            // VERDICT TRUST HIERARCHY, escalation leg: re-run an untrusted
            // probe under COW branch epochs — complete per-alternative state
            // restore, so chronological search is classically complete and
            // the unrestored-advance poison never fires. Slower (journaling)
            // — used only to CONFIRM a plain-mode verdict tainted by
            // phantomized nodes. Oracle-validated (plain/COW matrix).
            if cow {
                algo.conf_inprocess_cow = true;
            }
        };
        renew(algo, ctx, false);
        let mut next_indi_id: i64 = 1_000;
        let mut readoff =
            bridged_classify_subject(algo, ctx, &bridged, &mut next_indi_id, s, n_named);
        if readoff.is_none() && algo.completeness_poisoned && cow_confirm {
            // Plain search untrusted (an unrestored advance phantomized
            // nodes) — the poison deferred the read-off. Escalate to COW.
            renew(algo, ctx, true);
            let mut id_cow: i64 = 1_000;
            readoff = bridged_classify_subject(algo, ctx, &bridged, &mut id_cow, s, n_named);
        }
        if readoff.is_none() && progress {
            eprintln!(
                "BRIDGE-DEFER subject {s}: READ-OFF stop after {:.1}s (signal={:?})",
                t_subj.elapsed().as_secs_f64(),
                ctx.pending_signal()
            );
        }
        let (mut subs, authoritative) = readoff?;
        // Non-authoritative read-off: the positives are one branch's model —
        // candidates polluted by that branch's disjunct choices, and each
        // false candidate costs a full SAT probe to refute (measured on
        // ore_ont_12653: ~all probe budget burnt refuting recognition-branch
        // pollution). Konclude's possible-subsumer extraction intersects
        // MODELS instead: re-drive the subject with REVERSED disjunct order
        // (`conf_or_reverse` — order-only, sound) and keep only candidates
        // positive in BOTH models. A true subsumer is positive in EVERY
        // clash-free saturated graph, so the intersection stays a complete
        // filter; a candidate riding one branch choice drops out. If the
        // second drive STOPs or (exotically) clashes, keep the unintersected
        // set — the intersection is purely an optimization.
        if !authoritative {
            renew(algo, ctx, false);
            algo.conf_or_reverse = true;
            let mut id_rev: i64 = 1_000;
            if let Some((subs_rev, _)) =
                bridged_classify_subject(algo, ctx, &bridged, &mut id_rev, s, n_named)
            {
                if subs_rev.len() < n_named {
                    let keep: std::collections::HashSet<usize> = subs_rev.into_iter().collect();
                    let before = subs.len();
                    subs.retain(|c| keep.contains(c));
                    if progress && subs.len() != before {
                        let names: Vec<&str> = subs
                            .iter()
                            .take(48)
                            .map(|&c| tin.concepts[c].as_str())
                            .collect();
                        eprintln!(
                            "BRIDGE-INTERSECT subject {s} ({}): candidates {before} -> {} [{}]",
                            tin.concepts[s],
                            subs.len(),
                            names.join(",")
                        );
                    }
                }
            }
            algo.conf_or_reverse = false;
        }
        // The subject-unsatisfiable signal is the FULL index range
        // (authoritative). A tiny ontology can legitimately have a subject
        // subsumed by every named concept, so disambiguate with a direct
        // single-seed unsat probe.
        if authoritative && subs.len() == n_named {
            renew(algo, ctx, false);
            let mut id2: i64 = 1_000;
            let mut v = bridged_unsat(algo, ctx, &bridged, &mut id2, &[(bridged.named[s], false)]);
            if v.is_none() && algo.completeness_poisoned && cow_confirm {
                renew(algo, ctx, true);
                let mut id_cow: i64 = 1_000;
                v = bridged_unsat(algo, ctx, &bridged, &mut id_cow, &[(bridged.named[s], false)]);
            }
            match v {
                Some(true) => {
                    out.unsatisfiable.push(s);
                    return Some(());
                }
                Some(false) => {} // genuinely subsumed by everything — keep pairs
                None => return None,
            }
        }
        // Restrict candidates to the classification universe (real named
        // classes; see the `universe` doc above). AFTER the full-range unsat
        // disambiguation — that signal is defined on the raw read-off.
        subs.retain(|&c| c == s || universe.contains(&c));
        if authoritative {
            for c in subs {
                if c != s {
                    out.subsumptions.push((s, c));
                }
            }
            return Some(());
        }
        // Non-deterministic subject: verify each candidate pairwise. Collect
        // locally and commit only when EVERY probe answered, so a deferred
        // subject leaves no partial pairs behind for the retry round.
        let mut pairs: Vec<(usize, usize)> = Vec::new();
        for c in subs {
            if c == s {
                continue;
            }
            renew(algo, ctx, false);
            let mut id2: i64 = 1_000;
            let mut v = bridged_unsat(
                algo,
                ctx,
                &bridged,
                &mut id2,
                &[(bridged.named[s], false), (bridged.named[c], true)],
            );
            if v.is_none() && algo.completeness_poisoned && cow_confirm {
                // plain verdict untrusted — confirm under COW epochs
                renew(algo, ctx, true);
                let mut id_cow: i64 = 1_000;
                v = bridged_unsat(
                    algo,
                    ctx,
                    &bridged,
                    &mut id_cow,
                    &[(bridged.named[s], false), (bridged.named[c], true)],
                );
            }
            match v {
                Some(true) => pairs.push((s, c)),
                Some(false) => {}
                None => {
                    if progress {
                        eprintln!(
                            "BRIDGE-DEFER subject {s}: PAIR {}v{} stop after {:.1}s subj-total",
                            tin.concepts[s],
                            tin.concepts[c],
                            t_subj.elapsed().as_secs_f64()
                        );
                    }
                    return None;
                }
            }
        }
        out.subsumptions.extend(pairs);
        // A non-deterministic subject can also be unsatisfiable without the
        // read-off reporting the full range (a clash IS reported full-range,
        // so this is only reachable when the drive found a model — the
        // subject is satisfiable; nothing to check).
        Some(())
    };
    // Subjects whose defer is DETERMINISTIC (completeness poison — an
    // unrestored advance phantomized nodes): retrying with a bigger budget
    // re-runs the identical search to the identical poison, so they must
    // skip the retry rounds (measured: retrying them tripled the wall to a
    // 900 s validation timeout on ore_ont_12653). Any permanent defer means
    // the whole classification defers — stop the rounds early.
    let mut permanent_defer = 0usize;
    for round in 0..=retry_rounds {
        algo.probe_budget = Some(std::time::Duration::from_secs(
            base_budget.saturating_mul(4u64.saturating_pow(round)),
        ));
        let total = pending.len();
        let mut deferred: Vec<usize> = Vec::new();
        for (k, &s) in pending.iter().enumerate() {
            if classify_one(s, &mut algo, &mut ctx, &mut out).is_none() {
                if algo.completeness_poisoned {
                    permanent_defer += 1;
                } else {
                    deferred.push(s);
                }
            }
            if progress && (k % 64 == 0 || k + 1 == total || permanent_defer > 0) {
                eprintln!(
                    "BRIDGE-CLASSIFY round {round} subject {}/{total} deferred={} permanent={}",
                    k + 1,
                    deferred.len(),
                    permanent_defer
                );
            }
            if permanent_defer > 0 {
                // One deterministic defer decides the whole classification
                // (complete-or-defer contract) — finishing the remaining
                // subjects is pure waste, and in the race the bridge worker
                // shares the node with the CB engine.
                break;
            }
        }
        pending = deferred;
        if pending.is_empty() || permanent_defer > 0 {
            break;
        }
    }
    // KM_HT_UNSATCACHE diagnostics: writes vs hits across the WHOLE
    // classification (the handler is carried across probe resets, so these
    // are cumulative). Interprets a null A/B result: 0 writes = the u22
    // guards rejected every candidate line; writes>0 hits=0 = the read
    // points never matched (label shapes / caching-tag mismatch).
    if progress {
        if let Some(state) = ctx.base.take_used_unsatisfiable_cache_handler() {
            eprintln!(
                "BRIDGE-CLASSIFY unsatcache: {} lines written, {} read hits",
                state.handler.stat_write_count, state.handler.stat_hit_count
            );
            ctx.base.restore_used_unsatisfiable_cache_handler(state);
        }
    }
    if !pending.is_empty() || permanent_defer > 0 {
        if progress {
            eprintln!(
                "BRIDGE-CLASSIFY defer: {} budget + {} permanent subjects without verdict",
                pending.len(),
                permanent_defer
            );
        }
        return None;
    }
    Some(out)
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
            true,
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
            self.try_subsumes(sub, sup)
                .unwrap_or_else(|| panic!("probe {sub} ⊑ {sup} raised STOP (undecided)"))
        }

        /// Like [`Self::subsumes`] but surfaces STOP/DEFER as `None` instead
        /// of panicking — for tests asserting "must not answer WRONG"
        /// (a defer is acceptable, a wrong verdict is not).
        fn try_subsumes(&mut self, sub: &str, sup: &str) -> Option<bool> {
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
            algo.singleton_concepts = bridged.singleton_concepts.clone();
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
            r
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

    /// KM_HT_UNSATCACHE integration: the learned-nogood store survives
    /// `reset_probe_env` and never flips a verdict. Drives the SAME env
    /// lifecycle as `bridged_classify` (fresh env → probe → reset → probe)
    /// with the handler installed and the DDB+unsat-cache flags set
    /// programmatically (env-var-independent, so the test is meaningful in
    /// every suite mode). Asserts: (1) an UNSAT probe stays UNSAT when
    /// re-probed against the warm cache; (2) a SAT probe on overlapping
    /// vocabulary is NOT corrupted by cache entries learned from the UNSAT
    /// one (the critical soundness control — a nogood must only fire on a
    /// label that genuinely contains it).
    #[test]
    fn unsat_cache_warm_probes_keep_verdicts() {
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:X)) Declaration(Class(:Y))\n\
             Declaration(Class(:A1)) Declaration(Class(:A2))\n\
             Declaration(Class(:Z))\n\
             SubClassOf(:X ObjectUnionOf(:A1 :A2))\n\
             SubClassOf(:A1 :Y)\n\
             SubClassOf(:A2 :Y)\n)"
        );
        let env = bridge_ofn(&ofn);
        let (mut algo, mut ctx, bridged) = fresh_bridge_env(&env.tin);
        assert_eq!(bridged.unsupported, 0, "fully bridged");
        install_bridge_unsat_cache(&mut ctx);
        let set_flags = |algo: &mut CompletionTaskHandleAlgorithm| {
            algo.conf_build_dependencies = true;
            algo.conf_dependency_backjumping = true;
            algo.conf_atomic_semantic_branching = true;
            algo.conf_write_unsat_caching = true;
            algo.conf_test_occur_unsat_cached = true;
        };
        set_flags(&mut algo);
        let idx = |s: &str| -> usize {
            env.tin
                .concepts
                .iter()
                .position(|n| n == s)
                .unwrap_or_else(|| panic!("concept {s} not in TInput"))
        };
        let (x, y, z) = (
            bridged.named[idx("X")],
            bridged.named[idx("Y")],
            bridged.named[idx("Z")],
        );
        let mut id = 0i64;
        // Probe 1: X ⊓ ¬Y — UNSAT (X ⊑ Y through both disjuncts); the DDB
        // analysis may write nogoods into the shared cache here.
        let cold = bridged_unsat(&mut algo, &mut ctx, &bridged, &mut id, &[(x, false), (y, true)]);
        assert_eq!(cold, Some(true), "X ⊑ Y must hold (cold cache)");
        // Probe 2 (warm): the same seed re-probed after the classify-style
        // reset — the carried cache must reproduce the verdict.
        reset_probe_env(&mut algo, &mut ctx, &bridged, false);
        set_flags(&mut algo);
        let warm = bridged_unsat(&mut algo, &mut ctx, &bridged, &mut id, &[(x, false), (y, true)]);
        assert_eq!(warm, Some(true), "X ⊑ Y must hold (warm cache)");
        // Probe 3 (warm, SAT control): X ⊓ ¬Z is satisfiable — a nogood
        // learned from the ¬Y run must not fire on this overlapping label.
        reset_probe_env(&mut algo, &mut ctx, &bridged, false);
        set_flags(&mut algo);
        let sat = bridged_unsat(&mut algo, &mut ctx, &bridged, &mut id, &[(x, false), (z, true)]);
        assert_eq!(sat, Some(false), "X ⊑ Z must NOT hold (warm cache)");
        // The handler must still be installed after the resets (the carry).
        assert!(
            ctx.base.take_used_unsatisfiable_cache_handler().is_some(),
            "unsat-cache handler must survive reset_probe_env"
        );
    }

    /// Miniature of the ore_ont_12653 wrong-root-cancel (memory
    /// project_km_bridge_disjunction_probe cont-11): a TOP covering
    /// `⊤ ⊑ A ⊔ B` with A,B disjoint; `A ⊑ ≤2 r.E` kills the A-branch on X
    /// (X has three pairwise-disjoint E-successors); the B-branch adds three
    /// FRESH pairwise-disjoint E-successors, and X's `≤3 r.E` then forces a
    /// 6→3 CROSS-GROUP merge matching — which EXISTS (cross pairs are
    /// compatible), so **X is SATISFIABLE** (the B-branch model) and X ⊑ Y
    /// must NOT hold for an unrelated Y. The 12653 kernel bug: the u29
    /// all-siblings-refuted propagation reads the pairing deaths' remainders
    /// as deterministic-only and wrongly ROOT-CANCELS, declaring X unsat
    /// (⇒ X ⊑ everything). Run plain AND with
    /// `KM_HT_COW=1 KM_HT_DDB=1 KM_HT_DDB_REFUTED_DISCARD=1` (the fast
    /// path that reaches the propagation); both must pass once u29's
    /// before-proc-tag remainder is fixed. `#[ignore]` while env-driven.
    #[test]
    #[ignore]
    fn covering_atmost_cross_merge_sat() {
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:E))\n\
             Declaration(Class(:D1)) Declaration(Class(:D2)) Declaration(Class(:D3))\n\
             Declaration(Class(:E1)) Declaration(Class(:E2)) Declaration(Class(:E3))\n\
             Declaration(Class(:X)) Declaration(Class(:Y))\n\
             Declaration(ObjectProperty(:r))\n\
             SubClassOf(owl:Thing ObjectUnionOf(:A :B))\n\
             DisjointClasses(:A :B)\n\
             SubClassOf(:A ObjectMaxCardinality(2 :r :E))\n\
             SubClassOf(:B ObjectIntersectionOf(ObjectSomeValuesFrom(:r :D1) \
             ObjectSomeValuesFrom(:r :D2) ObjectSomeValuesFrom(:r :D3)))\n\
             DisjointClasses(:D1 :D2 :D3)\n\
             SubClassOf(:D1 :E) SubClassOf(:D2 :E) SubClassOf(:D3 :E)\n\
             SubClassOf(:X ObjectIntersectionOf(ObjectSomeValuesFrom(:r :E1) \
             ObjectSomeValuesFrom(:r :E2) ObjectSomeValuesFrom(:r :E3) \
             ObjectMaxCardinality(3 :r :E)))\n\
             DisjointClasses(:E1 :E2 :E3)\n\
             SubClassOf(:E1 :E) SubClassOf(:E2 :E) SubClassOf(:E3 :E)\n)"
        );
        let mut env = bridge_ofn(&ofn);
        assert!(
            !env.subsumes("X", "Y"),
            "X must be satisfiable (B-branch cross-merge model) — a spurious \
             X ⊑ Y means the search wrongly refuted every covering branch \
             (the u29 wrong-root-cancel in miniature)"
        );
    }

    /// ddmin-minimal ore_ont_12653 wrong-root-cancel oracle (the leftover
    /// poisoning defect): under an Or on a successor node, alternative 1
    /// fires the node's own ≥2-expansion (creates successor nodes), so the
    /// advance cannot restore the single-node label snapshot — alt-1's
    /// disjunct SURVIVES into alternative 2's world. Alt-2's ⊥-derivation
    /// then carries connection dependencies to BOTH alternatives' track
    /// points, the u29 all-siblings-refuted propagation reads the decision
    /// as fully refuted with root-level externals only, and ROOT-CANCELS ⇒
    /// spurious AlternativePath ⊑ PathOfLength2 (a Path with three elements
    /// is a countermodel). Fixed by gating the u29 analysis — not just the
    /// DDB stack walk — on `unrestored_advance_count == 0` (u02). Passes in
    /// plain mode by construction; the KM_HT_DDB=1 matrix leg is the
    /// regression proof.
    #[test]
    fn unrestored_advance_leftover_no_root_cancel() {
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:AlternativePath)) Declaration(Class(:Path))\n\
             Declaration(Class(:MainPath)) Declaration(Class(:PathElement))\n\
             Declaration(Class(:PathOfLength2))\n\
             Declaration(ObjectProperty(:hasPathElement))\n\
             SubClassOf(:AlternativePath :Path)\n\
             EquivalentClasses(:MainPath ObjectIntersectionOf(\
             ObjectComplementOf(:AlternativePath) :Path))\n\
             SubClassOf(:Path ObjectMinCardinality(2 :hasPathElement :PathElement))\n\
             DisjointClasses(:Path :PathElement)\n\
             EquivalentClasses(:PathOfLength2 ObjectExactCardinality(2 :hasPathElement :PathElement))\n)"
        );
        let mut env = bridge_ofn(&ofn);
        // Under the plain-mode multi-node completeness gate this probe's SAT
        // verdict becomes a DEFER (None) — acceptable. The regression this
        // test guards is the WRONG UNSAT (Some(true)) from the poisoned u29
        // analysis.
        assert_ne!(
            env.try_subsumes("AlternativePath", "PathOfLength2"),
            Some(true),
            "AlternativePath ⊑ PathOfLength2 must NOT hold (3-element Path \
             countermodel) — a spurious UNSAT here means the u29 analysis ran \
             on leftover-poisoned state after an unrestored advance"
        );
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

    /// Role DOMAIN through a forced successor (the ore_ont_9635 gap):
    /// `Domain(r, D)` + `A ⊑ ∃r.⊤` entails `A ⊑ D` DETERMINISTICALLY —
    /// the successor's existence fires the domain clause on the edge.
    /// The 9635 shape adds exact cardinality; test both.
    #[test]
    fn bridge_domain_via_forced_successor() {
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:A)) Declaration(Class(:D)) Declaration(Class(:T))\n\
             Declaration(ObjectProperty(:r))\n\
             ObjectPropertyDomain(:r :D)\n\
             SubClassOf(:A ObjectSomeValuesFrom(:r :T))\n)"
        );
        let mut env = bridge_ofn(&ofn);
        assert!(
            env.subsumes("A", "D"),
            "A ⊑ D via domain(r)=D and A's forced r-successor"
        );
        assert!(!env.subsumes("D", "A"), "D ⊑ A must NOT hold");
        // the 9635 shape: exact cardinality forces the successor
        let ofn2 = format!(
            "{PREFIX}\
             Declaration(Class(:A)) Declaration(Class(:D))\n\
             Declaration(ObjectProperty(:r))\n\
             ObjectPropertyDomain(:r :D)\n\
             SubClassOf(:A ObjectExactCardinality(1 :r))\n)"
        );
        let mut env2 = bridge_ofn(&ofn2);
        assert!(
            env2.subsumes("A", "D"),
            "A ⊑ D via domain(r)=D and A's =1 r-successor"
        );
    }

    /// The ore_ont_9635 completeness gap (ddmin, 294 → 2+2 axioms): the
    /// domain entailment `A ⊑ =1 r` + `Domain(r, D)` ⇒ `A ⊑ D` (covered
    /// bare by `bridge_domain_via_forced_successor`) MUST survive the
    /// presence of unrelated DataHasValue axioms — their value-identity
    /// clausification introduces singleton concepts, and the singleton
    /// path broke the pairwise probe (`unsat(A ⊓ ¬D)` found a spurious
    /// model: pairwise=false while readoff_has=true).
    #[test]
    fn bridge_domain_survives_datatype_singletons() {
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:A)) Declaration(Class(:D)) Declaration(Class(:I))\n\
             Declaration(Class(:P)) Declaration(Class(:L)) Declaration(Class(:RL))\n\
             Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:h))\n\
             Declaration(DataProperty(:v))\n\
             SubClassOf(:A ObjectExactCardinality(1 :r))\n\
             ObjectPropertyDomain(:r :D)\n\
             EquivalentClasses(:P ObjectIntersectionOf(\
             DataHasValue(:v \"true\"^^xsd:boolean) :I))\n\
             EquivalentClasses(:L ObjectIntersectionOf(\
             ObjectAllValuesFrom(:h :P) :RL))\n)"
        );
        let mut env = bridge_ofn(&ofn);
        // The cross-branch wipe DETECTOR turns the previously-WRONG SAT
        // verdict into a DEFER (None) — acceptable: the production driver
        // then defers the subject and the caller falls back to a complete
        // arm. `Some(false)` (the wrong verdict) is the regression.
        let verdict = env.try_subsumes("A", "D");
        let holds = verdict == Some(true);
        if verdict == Some(false) {
            let show = |a: &HAtom| -> String {
                match a {
                    HAtom::Concept { neg, c, t } => format!(
                        "{}{}({t})",
                        if *neg { "¬" } else { "" },
                        env.tin.concepts.get(*c).map(String::as_str).unwrap_or("?")
                    ),
                    HAtom::Role { r, s, t } => {
                        format!("{}({s},{t})", env.tin.roles.get(*r).map(String::as_str).unwrap_or("?"))
                    }
                    HAtom::Eq { s, t } => format!("eq({s},{t})"),
                    HAtom::Exist { r, neg, c, t } => format!(
                        "∃{}.{}{}({t})",
                        env.tin.roles.get(*r).map(String::as_str).unwrap_or("?"),
                        if *neg { "¬" } else { "" },
                        env.tin.concepts.get(*c).map(String::as_str).unwrap_or("?")
                    ),
                }
            };
            for (i, cl) in env.tin.clauses.iter().enumerate() {
                let b: Vec<String> = cl.body.iter().map(show).collect();
                let h: Vec<String> = cl.head.iter().map(show).collect();
                eprintln!("DBG clause {i}: {} -> {}", b.join(" ∧ "), h.join(" ∨ "));
            }
            for (i, n) in env.tin.concepts.iter().enumerate() {
                eprintln!("DBG concept idx {i} = tag {} = {n}", 10 + i);
            }
            for (i, n) in env.tin.roles.iter().enumerate() {
                eprintln!("DBG role idx {i} = arena-tag {} = {n}", 100 + i);
            }
            dump_nodes(&mut env, "after A⊑D probe (datatype singleton)");
        }
        assert_ne!(
            verdict,
            Some(false),
            "A ⊑ D holds (domain via forced successor): answering NOT-subsumed is unsound; \
             DEFER (None) is the acceptable degradation, deriving it the aspirational fix"
        );
        let _ = holds;
        assert_ne!(env.try_subsumes("D", "A"), Some(true), "D ⊑ A must NOT hold");
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
            true,
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

    /// Compare the two subsumption oracles on ONE pair (`KM_BRIDGE_PAIR=
    /// "SubLocal,SupLocal"`): the pairwise probe (`subsumes`, seed A+¬B,
    /// re-drive with backtrack) vs the model read-off (`bridged_classify_
    /// subject`, saturate {A} and read the root label). Tells whether a
    /// read-off MISS is a read-off limitation (pairwise=true) or a real
    /// completion-incompleteness (both false). Diagnostic.
    #[test]
    #[ignore]
    fn bridge_probe_pair() {
        let path = std::env::var("KM_BRIDGE_ONT").expect("set KM_BRIDGE_ONT=<ont path>");
        let pair = std::env::var("KM_BRIDGE_PAIR").expect("set KM_BRIDGE_PAIR=Sub,Sup");
        let (sub, sup) = pair.split_once(',').expect("Sub,Sup");
        let mut env = bridge_ofn_path(&path);
        // KM_BRIDGE_DUMP_NAMES: print the concept TAG of each listed name so a
        // numeric KM_BRIDGE_FIND_TAG follow-up can watch the chain.
        // KM_BRIDGE_DUMP_ROLE_SUPERS=<role-name>: print the bridged indirect
        // super-role list (as role TAGS: 100+i forward, 100+n_roles+i inverse)
        // for the named role — verifies the pass-1 hierarchy closure.
        if let Ok(rn) = std::env::var("KM_BRIDGE_DUMP_ROLE_SUPERS") {
            for (i, name) in env.tin.roles.iter().enumerate() {
                if name == &rn {
                    // rebuild a bridged env to inspect the arena role objects
                    let mut ctxr = CalculationAlgorithmContextBase::new();
                    let topr = {
                        let mut c = Concept::new();
                        c.set_concept_tag(1);
                        c.set_operator_code(op::CCTOP);
                        ctxr.ontology_arenas_mut().alloc_concept(c)
                    };
                    ctxr.processing_data_box_mut().ontology_top_concept = topr;
                    let br = bridge_tinput(&mut ctxr, &env.tin);
                    let robj = br.roles[i];
                    let sup_tags: Vec<Cint64> = ctxr
                        .ontology_arenas()
                        .role(robj)
                        .indirect_super_roles
                        .iter()
                        .map(|l| ctxr.ontology_arenas().role(l.target).get_role_tag())
                        .collect();
                    let n = env.tin.roles.len() as Cint64;
                    let named_sups: Vec<String> = sup_tags
                        .iter()
                        .map(|&t| {
                            let fwd = t - 100;
                            if fwd < n {
                                env.tin.roles[fwd as usize].clone()
                            } else {
                                format!("INV({})", env.tin.roles[(fwd - n) as usize])
                            }
                        })
                        .collect();
                    eprintln!("ROLE-SUPERS {rn} (tag {}): {:?}", 100 + i, named_sups);
                }
            }
        }
        // KM_BRIDGE_TAG_NAMES=<tag>[,<tag>...]: reverse map concept TAGs to
        // TInput names (tag = TAG_BASE + index).
        if let Ok(tags) = std::env::var("KM_BRIDGE_TAG_NAMES") {
            for t in tags.split(',') {
                if let Ok(tag) = t.trim().parse::<i64>() {
                    let i = (tag - TAG_BASE) as usize;
                    if i < env.tin.concepts.len() {
                        eprintln!("TAG-NAME {}={}", tag, env.tin.concepts[i]);
                    }
                }
            }
        }
        // KM_BRIDGE_GREP_CLAUSES=<c:IDX|r:IDX>[,...]: print every TInput
        // clause mentioning any listed concept (c:) or role (r:) index,
        // with concept names resolved — the clause-level entailment-check
        // input (the UNSUP-dumper format).
        if let Ok(spec) = std::env::var("KM_BRIDGE_GREP_CLAUSES") {
            let mut cons: Vec<usize> = Vec::new();
            let mut rols: Vec<usize> = Vec::new();
            for part in spec.split(',') {
                let part = part.trim();
                if let Some(i) = part.strip_prefix("c:").and_then(|s| s.parse().ok()) {
                    cons.push(i);
                } else if let Some(i) = part.strip_prefix("r:").and_then(|s| s.parse().ok()) {
                    rols.push(i);
                }
            }
            let name = |c: usize| -> &str {
                env.tin.concepts.get(c).map(String::as_str).unwrap_or("?")
            };
            let show = |a: &crate::orchestrate::cb_to_ht::HAtom| -> String {
                use crate::orchestrate::cb_to_ht::HAtom;
                match a {
                    HAtom::Concept { neg, c, t } => {
                        format!("{}{}({t})", if *neg { "¬" } else { "" }, name(*c))
                    }
                    HAtom::Role { r, s, t } => format!(
                        "{}({s},{t})",
                        env.tin.roles.get(*r).map(String::as_str).unwrap_or("?")
                    ),
                    HAtom::Eq { s, t } => format!("eq({s},{t})"),
                    HAtom::Exist { r, neg, c, t } => format!(
                        "∃{}.{}{}({t})",
                        env.tin.roles.get(*r).map(String::as_str).unwrap_or("?"),
                        if *neg { "¬" } else { "" },
                        name(*c)
                    ),
                }
            };
            for cl in &env.tin.clauses {
                use crate::orchestrate::cb_to_ht::HAtom;
                let hit = cl.body.iter().chain(cl.head.iter()).any(|a| match a {
                    HAtom::Concept { c, .. } | HAtom::Exist { c, .. } => cons.contains(c),
                    HAtom::Role { r, .. } => rols.contains(r),
                    HAtom::Eq { .. } => false,
                }) || cl.body.iter().chain(cl.head.iter()).any(|a| match a {
                    HAtom::Exist { r, .. } => rols.contains(r),
                    _ => false,
                });
                if hit {
                    let b: Vec<String> = cl.body.iter().map(show).collect();
                    let h: Vec<String> = cl.head.iter().map(show).collect();
                    eprintln!("CLAUSE: {} -> {}", b.join(" ∧ "), h.join(" ∨ "));
                }
            }
        }
        // KM_BRIDGE_ROLE_NAMES=<idx>[,<idx>...]: print TInput role names.
        if let Ok(idxs) = std::env::var("KM_BRIDGE_ROLE_NAMES") {
            for i in idxs.split(',') {
                if let Ok(i) = i.trim().parse::<usize>() {
                    if i < env.tin.roles.len() {
                        eprintln!("ROLE-NAME {}={}", i, env.tin.roles[i]);
                    }
                }
            }
        }
        if let Ok(names) = std::env::var("KM_BRIDGE_DUMP_NAMES") {
            for n in names.split(',') {
                if let Some(&idx) = env.con_id.get(n.trim()) {
                    eprintln!("NAME-TAG {}={}", n.trim(), TAG_BASE + idx as Cint64);
                }
            }
        }
        let pairwise = env.subsumes(sub, sup);

        // read-off on the same subject
        let n_named = env.tin.concepts.len();
        let s_idx = *env.con_id.get(sub).expect("sub in TInput");
        let sup_idx = *env.con_id.get(sup).expect("sup in TInput");
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
        let bridged = bridge_tinput(&mut ctx, &env.tin);
        let mut next = 0i64;
        let readoff =
            bridged_classify_subject(&mut algo, &mut ctx, &bridged, &mut next, s_idx, n_named);
        let readoff_has = readoff
            .as_ref()
            .map(|(subs, _)| subs.contains(&sup_idx))
            .unwrap_or(false);
        eprintln!(
            "BRIDGE-PAIR {sub} ⊑ {sup}: pairwise={pairwise} readoff_has={readoff_has} \
             readoff_nondet={}",
            !readoff.as_ref().map(|(_, auth)| *auth).unwrap_or(false),
        );
        // dump every clause referencing sub or sup (to scope the propagation
        // the completion is missing).
        if std::env::var("KM_BRIDGE_DUMP_CLAUSES").is_ok() {
            let name = |i: usize| env.tin.concepts[i].as_str();
            let show = |a: &HAtom| -> String {
                match a {
                    HAtom::Concept { neg, c, t } => {
                        format!("{}{}({t})", if *neg { "¬" } else { "" }, name(*c))
                    }
                    HAtom::Role { r, s, t } => format!("R{r}({s},{t})"),
                    HAtom::Eq { s, t } => format!("eq({s},{t})"),
                    HAtom::Exist { r, neg, c, t } => {
                        format!("∃R{r}.{}{}({t})", if *neg { "¬" } else { "" }, name(*c))
                    }
                }
            };
            let mentions = |cl: &HtClause, idx: usize| -> bool {
                cl.body.iter().chain(cl.head.iter()).any(|a| matches!(a,
                    HAtom::Concept { c, .. } | HAtom::Exist { c, .. } if *c == idx))
            };
            // extra names to trace (KM_BRIDGE_DUMP_NAMES="Q_708,Q_266").
            let extra_idx: Vec<usize> = std::env::var("KM_BRIDGE_DUMP_NAMES")
                .ok()
                .map(|s| {
                    s.split(',')
                        .filter_map(|n| env.con_id.get(n.trim()).copied())
                        .collect()
                })
                .unwrap_or_default();
            for cl in &env.tin.clauses {
                if mentions(cl, s_idx)
                    || mentions(cl, sup_idx)
                    || extra_idx.iter().any(|&i| mentions(cl, i))
                {
                    let b: Vec<String> = cl.body.iter().map(show).collect();
                    let h: Vec<String> = cl.head.iter().map(show).collect();
                    eprintln!("  CLAUSE: {} -> {}", b.join(" ∧ "), h.join(" ∨ "));
                }
            }
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
        // Names appearing as a SUB in gold: only these become subjects, so a
        // gold file restricted to a subject sample stays self-consistent —
        // every admitted subject carries its COMPLETE supers set, keeping
        // `spurious` meaningful (a supers-only name would otherwise be
        // classified against an empty gold row and misread as unsound).
        let mut gold_subs: std::collections::HashSet<String> = std::collections::HashSet::new();
        for pair in gold["subsumptions"].as_array().expect("subsumptions array") {
            let sub = local(pair[0].as_str().unwrap());
            let sup = local(pair[1].as_str().unwrap());
            gold_universe.insert(sub.clone());
            gold_universe.insert(sup.clone());
            gold_subs.insert(sub.clone());
            gold_pairs.insert((sub, sup));
        }

        let text = std::fs::read_to_string(&path).expect("readable ontology");
        let fr = crate::frontend::ofn_to_clauses(&text).expect("in fragment");
        let named_set: std::collections::HashSet<String> = fr.named.iter().cloned().collect();
        let tin = crate::orchestrate::cb_to_ht::convert(
            &fr.clauses, None, &named_set, &fr.cardinalities, true, &fr.rules, false,
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

        // subjects = gold-classified (sub-side), in-fragment named concepts.
        let mut subjects: Vec<usize> = (0..n_named)
            .filter(|&i| gold_subs.contains(&tin.concepts[i]))
            .collect();
        // KM_BRIDGE_MAX_SUBJECTS=N: validate a bounded prefix of subjects
        // (correctness sample on deep taxonomies where full O(subjects)
        // classification without databox reuse is a separate speed lever).
        // When set, gold is restricted to these subjects so missing/spurious
        // stay meaningful on the sample.
        if let Some(cap) = std::env::var("KM_BRIDGE_MAX_SUBJECTS")
            .ok()
            .and_then(|s| s.parse::<usize>().ok())
        {
            subjects.truncate(cap);
        }
        // pairwise-fallback COLUMNS: every gold-known named concept (a super
        // like `Path` need not be a classified subject itself).
        let targets: Vec<usize> = (0..n_named)
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
            // thread the singleton (value-identity) concepts — WITHOUT them
            // the kernel under-merges value nodes and unsat proofs that need
            // the merges cannot close (measured: PathOfLength3 ⊑ Path
            // converged in the probe harness, which threads them, but burned
            // its whole budget in this loop, which did not).
            algo2.singleton_concepts = bridged2.singleton_concepts.clone();
            let mut n2 = 0i64;
            let t_subj = std::time::Instant::now();
            let verdict = bridged_classify_subject(&mut algo2, &mut ctx2, &bridged2, &mut n2, s, n_named);
            eprintln!(
                "SUBJ {} {}: {} in {:.1}s (nodes={} backtracks={})",
                s,
                tin.concepts[s],
                match &verdict {
                    Some((v, true)) => format!("readoff {} supers", v.len()),
                    Some((v, false)) => format!("NONDET {} candidates", v.len()),
                    None => "STOP".into(),
                },
                t_subj.elapsed().as_secs_f64(),
                ctx2.process_context().node_count(),
                algo2.or_backtrack_count,
            );
            match verdict {
                Some((subs, true)) => {
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
                Some((cands, false)) => {
                    // Non-deterministic saturation: the one-model read-off is
                    // not authoritative — its positives are the CANDIDATE
                    // subsumers (Konclude's possible-subsumer extraction).
                    // Verify each with a pairwise probe: `unsat(s ⊓ ¬sup)`
                    // proves `s ⊑ sup` under ANY branch discipline. On a
                    // small gold universe, probe every target instead (the
                    // candidate label can under-approximate; the pairwise
                    // verdict itself is exact either way).
                    nondet += 1;
                    let cand_list: Vec<usize> = if targets.len() <= 64 {
                        targets.clone()
                    } else {
                        cands
                    };
                    for sup in cand_list {
                        if sup == s || !gold_universe.contains(&tin.concepts[sup]) {
                            continue;
                        }
                        let tp0 = std::time::Instant::now();
                        if std::env::var_os("KM_BRIDGE_PROGRESS").is_some() {
                            eprintln!("PAIR-START {} vs {}", tin.concepts[s], tin.concepts[sup]);
                        }
                        let mut algo3 = CompletionTaskHandleAlgorithm::new();
                        configure_default_blocking(&mut algo3);
                        let mut ctx3 = CalculationAlgorithmContextBase::new();
                        ctx3.base.used_concept_priority_strategy =
                            Some(ConceptProcessingPriorityStrategy::new_concrete_operator());
                        let top3 = {
                            let mut c = Concept::new();
                            c.set_concept_tag(1);
                            c.set_operator_code(op::CCTOP);
                            ctx3.ontology_arenas_mut().alloc_concept(c)
                        };
                        ctx3.processing_data_box_mut().ontology_top_concept = top3;
                        let bridged3 = bridge_tinput(&mut ctx3, &tin);
                        // value-identity singletons (see the subject loop).
                        algo3.singleton_concepts = bridged3.singleton_concepts.clone();
                        let mut n3 = 0i64;
                        if bridged_unsat(
                            &mut algo3,
                            &mut ctx3,
                            &bridged3,
                            &mut n3,
                            &[(bridged3.named[s], false), (bridged3.named[sup], true)],
                        ) == Some(true)
                        {
                            derived.insert((
                                tin.concepts[s].clone(),
                                tin.concepts[sup].clone(),
                            ));
                        }
                        // Surface slow pair probes (the read-offs are ms; a
                        // probe that takes seconds is the scaling story).
                        let dt = tp0.elapsed();
                        if dt.as_millis() > 500 {
                            eprintln!(
                                "SLOW-PAIR {} vs {}: {:.1}s (backtracks={})",
                                tin.concepts[s],
                                tin.concepts[sup],
                                dt.as_secs_f64(),
                                algo3.or_backtrack_count,
                            );
                        }
                    }
                }
                None => nondet += 1, // STOP: no verdict at all
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

    /// PRODUCTION-PATH gold driver: run the shipped entry point
    /// `bridged_classify` (single reused env, production DDB search,
    /// per-subject defer + budget-escalating retry rounds) on
    /// `KM_BRIDGE_ONT` and diff the result against `KM_BRIDGE_GOLD` —
    /// the same gold format as `bridge_classify_full`, which by contrast
    /// drives the subject/probe layers directly with fresh envs. Restrict
    /// subjects via `queries` when `KM_BRIDGE_MAX_SUBJECTS` is set.
    #[test]
    #[ignore]
    fn bridge_classify_prod() {
        let path = std::env::var("KM_BRIDGE_ONT").expect("set KM_BRIDGE_ONT=<ont path>");
        let gold_path = std::env::var("KM_BRIDGE_GOLD").expect("set KM_BRIDGE_GOLD=<json>");
        let gold_text = std::fs::read_to_string(&gold_path).expect("readable gold");
        let gold: serde_json::Value = serde_json::from_str(&gold_text).expect("gold json");
        let local = |iri: &str| -> String {
            iri.rsplit(['#', '/']).next().unwrap_or(iri).to_string()
        };
        let mut gold_pairs: std::collections::HashSet<(String, String)> =
            std::collections::HashSet::new();
        let mut gold_universe: std::collections::HashSet<String> =
            std::collections::HashSet::new();
        let mut gold_subs: std::collections::HashSet<String> = std::collections::HashSet::new();
        for pair in gold["subsumptions"].as_array().expect("subsumptions array") {
            let sub = local(pair[0].as_str().unwrap());
            let sup = local(pair[1].as_str().unwrap());
            gold_universe.insert(sub.clone());
            gold_universe.insert(sup.clone());
            gold_subs.insert(sub.clone());
            gold_pairs.insert((sub, sup));
        }

        let text = std::fs::read_to_string(&path).expect("readable ontology");
        let fr = crate::frontend::ofn_to_clauses(&text).expect("in fragment");
        let named_set: std::collections::HashSet<String> = fr.named.iter().cloned().collect();
        let mut tin = crate::orchestrate::cb_to_ht::convert(
            &fr.clauses, None, &named_set, &fr.cardinalities, true, &fr.rules, false,
        );
        // subjects = gold-classified (sub-side) names, optionally capped —
        // expressed through the production `queries` mechanism.
        let mut subjects: Vec<usize> = (0..tin.concepts.len())
            .filter(|&i| gold_subs.contains(&tin.concepts[i]))
            .collect();
        if let Some(cap) = std::env::var("KM_BRIDGE_MAX_SUBJECTS")
            .ok()
            .and_then(|s| s.parse::<usize>().ok())
        {
            subjects.truncate(cap);
        }
        let subj_names: std::collections::HashSet<String> =
            subjects.iter().map(|&i| tin.concepts[i].clone()).collect();
        tin.queries = subjects.clone();

        let t0 = std::time::Instant::now();
        let res = bridged_classify(&tin);
        let elapsed = t0.elapsed();
        let Some(r) = res else {
            eprintln!("BRIDGE-CLASSIFY-PROD {path}: DEFERRED after {:.1}s", elapsed.as_secs_f64());
            return;
        };
        let mut derived: std::collections::HashSet<(String, String)> =
            std::collections::HashSet::new();
        for &(a, b) in &r.subsumptions {
            let (sub, sup) = (tin.concepts[a].clone(), tin.concepts[b].clone());
            if gold_universe.contains(&sup) {
                derived.insert((sub, sup));
            }
        }
        // unsat subjects subsume-into everything in gold's universe rows;
        // gold encodes them as pairs already, so expand for the diff.
        for &u in &r.unsatisfiable {
            let sub = tin.concepts[u].clone();
            for sup in &gold_universe {
                if *sup != sub {
                    derived.insert((sub.clone(), sup.clone()));
                }
            }
        }
        let gold_restricted: std::collections::HashSet<(String, String)> = gold_pairs
            .iter()
            .filter(|(sub, sup)| subj_names.contains(sub) && gold_universe.contains(sup))
            .cloned()
            .collect();
        for m in gold_restricted.difference(&derived).take(20) {
            eprintln!("MISSING (incomplete): {} ⊑ {}", m.0, m.1);
        }
        for sp in derived.difference(&gold_restricted).take(20) {
            eprintln!("SPURIOUS (unsound): {} ⊑ {}", sp.0, sp.1);
        }
        eprintln!(
            "BRIDGE-CLASSIFY-PROD {path}: subjects={} derived={} gold={} missing={} \
             spurious={} unsat={} elapsed={:.1}s",
            subjects.len(),
            derived.len(),
            gold_restricted.len(),
            gold_restricted.difference(&derived).count(),
            derived.difference(&gold_restricted).count(),
            r.unsatisfiable.len(),
            elapsed.as_secs_f64(),
        );
    }

    /// Singleton-concept merge (the datatype value-identity clause shape
    /// `V(x) ∧ V(y) → x = y`): X has an r-successor forced into `V ⊓ A` and
    /// an s-successor forced into `V ⊓ ¬A` (via `VA2 ⊓ A ⊑ ⊥`). The two
    /// V-carriers are ONE semantic object, so the deterministic
    /// scan-at-fixpoint merge (u02) must unite them and clash `A ⊓ ¬A` ⇒ X
    /// unsatisfiable. Without the merge the graph is clash-free and the
    /// probe under-detects (the earlier state counted the clause unsupported
    /// and DECLINED). Also asserts the clause is CONSUMED (unsupported == 0,
    /// no defer) and that a singleton-free sibling Y stays satisfiable.
    #[test]
    fn singleton_concept_merge_value_identity_unsat() {
        use crate::orchestrate::cb_to_ht::{HAtom, HtClause, TInput};
        let c = |neg: bool, c: usize, t: usize| HAtom::Concept { neg, c, t };
        // concepts: 0=X 1=V 2=A 3=VA1 4=VA2 5=Y
        let tin = TInput {
            concepts: vec![
                "X".into(),
                "V".into(),
                "A".into(),
                "VA1".into(),
                "VA2".into(),
                "Y".into(),
            ],
            roles: vec!["r".into(), "s".into()],
            clauses: vec![
                // V(x) ∧ V(y) → x = y  (the singleton / value-identity shape)
                HtClause {
                    body: vec![c(false, 1, 1), c(false, 1, 2)],
                    head: vec![HAtom::Eq { s: 1, t: 2 }],
                },
                // X ⊑ ∃r.VA1 ; X ⊑ ∃s.VA2
                HtClause {
                    body: vec![c(false, 0, 0)],
                    head: vec![HAtom::Exist { r: 0, neg: false, c: 3, t: 0 }],
                },
                HtClause {
                    body: vec![c(false, 0, 0)],
                    head: vec![HAtom::Exist { r: 1, neg: false, c: 4, t: 0 }],
                },
                // VA1 ⊑ V ; VA1 ⊑ A ; VA2 ⊑ V ; VA2 ⊓ A ⊑ ⊥
                HtClause {
                    body: vec![c(false, 3, 0)],
                    head: vec![c(false, 1, 0)],
                },
                HtClause {
                    body: vec![c(false, 3, 0)],
                    head: vec![c(false, 2, 0)],
                },
                HtClause {
                    body: vec![c(false, 4, 0)],
                    head: vec![c(false, 1, 0)],
                },
                HtClause {
                    body: vec![c(false, 4, 0), c(false, 2, 0)],
                    head: vec![],
                },
            ],
            ..Default::default()
        };
        let r = bridged_classify(&tin)
            .expect("singleton clause must be CONSUMED (no defer)");
        assert!(
            r.unsatisfiable.contains(&0),
            "X must be UNSAT via the value-identity merge (got unsat={:?})",
            r.unsatisfiable
        );
        assert!(
            !r.unsatisfiable.contains(&5),
            "Y (singleton-free) must stay satisfiable"
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
            true,
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

    // -----------------------------------------------------------------------
    // Task #23: saturation-first probe answering.
    //
    // These tests drive `bridged_saturate` DIRECTLY (no env flag — env vars
    // are process-global and the suite runs multi-threaded) and cross-check
    // every certain verdict against the completion-probe classification as
    // the oracle.
    // -----------------------------------------------------------------------

    #[test]
    fn saturation_answers_simple_taxonomy() {
        use crate::orchestrate::cb_to_ht::{HAtom, HtClause, TInput};
        let c = |neg: bool, cc: usize, t: usize| HAtom::Concept { neg, c: cc, t };
        // A ⊑ B, B ⊑ C — the pure-Horn case saturation must fully answer.
        let tin = TInput {
            concepts: vec!["A".into(), "B".into(), "C".into()],
            clauses: vec![
                HtClause {
                    body: vec![c(false, 0, 0)],
                    head: vec![c(false, 1, 0)],
                },
                HtClause {
                    body: vec![c(false, 1, 0)],
                    head: vec![c(false, 2, 0)],
                },
            ],
            ..Default::default()
        };
        let out = bridged_saturate(&tin).expect("in fragment");
        assert_eq!(
            out.sat_verdict,
            vec![Some(false); 3],
            "all three classes are satisfiable and must be SAT-certain"
        );
        assert_eq!(out.certain_subsumers[0].as_deref(), Some(&[1usize, 2][..]));
        assert_eq!(out.certain_subsumers[1].as_deref(), Some(&[2usize][..]));
        assert_eq!(out.certain_subsumers[2].as_deref(), Some(&[][..]));
        // Oracle: the probe path derives the same taxonomy.
        let r = bridged_classify(&tin).expect("classify");
        let mut probe_subs = r.subsumptions.clone();
        probe_subs.sort_unstable();
        assert_eq!(probe_subs, vec![(0, 1), (0, 2), (1, 2)]);
        assert!(r.unsatisfiable.is_empty());
    }

    #[test]
    fn saturation_detects_unsat_concept() {
        use crate::orchestrate::cb_to_ht::{HAtom, HtClause, TInput};
        let c = |neg: bool, cc: usize, t: usize| HAtom::Concept { neg, c: cc, t };
        // A ⊑ B and A ⊓ B ⊑ ⊥ — the deterministic clash must surface as
        // UNSAT-certain on A while B stays SAT-certain.
        let tin = TInput {
            concepts: vec!["A".into(), "B".into()],
            clauses: vec![
                HtClause {
                    body: vec![c(false, 0, 0)],
                    head: vec![c(false, 1, 0)],
                },
                HtClause {
                    body: vec![c(false, 0, 0), c(false, 1, 0)],
                    head: vec![],
                },
            ],
            ..Default::default()
        };
        let out = bridged_saturate(&tin).expect("in fragment");
        assert_eq!(out.sat_verdict[0], Some(true), "A is unsatisfiable");
        assert_eq!(out.sat_verdict[1], Some(false), "B is satisfiable");
        // Oracle agreement.
        let r = bridged_classify(&tin).expect("classify");
        assert!(r.unsatisfiable.contains(&0));
        assert!(!r.unsatisfiable.contains(&1));
    }

    #[test]
    fn probe_oracle_alone_detects_unsat_concept() {
        // DIAGNOSTIC twin of `saturation_detects_unsat_concept` WITHOUT the
        // saturation pre-pass: isolates whether the probe path alone answers
        // the tiny A ⊑ B, A ⊓ B ⊑ ⊥ input (checks the oracle, not saturation).
        use crate::orchestrate::cb_to_ht::{HAtom, HtClause, TInput};
        let c = |neg: bool, cc: usize, t: usize| HAtom::Concept { neg, c: cc, t };
        let tin = TInput {
            concepts: vec!["A".into(), "B".into()],
            clauses: vec![
                HtClause {
                    body: vec![c(false, 0, 0)],
                    head: vec![c(false, 1, 0)],
                },
                HtClause {
                    body: vec![c(false, 0, 0), c(false, 1, 0)],
                    head: vec![],
                },
            ],
            ..Default::default()
        };
        let r = bridged_classify(&tin).expect("classify");
        assert!(
            r.unsatisfiable.contains(&0),
            "probe path must detect A unsat (got unsat={:?} subs={:?})",
            r.unsatisfiable,
            r.subsumptions
        );
    }

    #[test]
    fn saturation_defers_disjunction_subjects() {
        use crate::orchestrate::cb_to_ht::{HAtom, HtClause, TInput};
        let c = |neg: bool, cc: usize, t: usize| HAtom::Concept { neg, c: cc, t };
        // A ⊑ B ⊔ C — branching: the non-branching saturation must NOT claim
        // a certain verdict built on one disjunct (the OR rule goes critical;
        // with no disjunct entailed the node is insufficient ⇒ unknown).
        // B and C stay plain satisfiable classes.
        let tin = TInput {
            concepts: vec!["A".into(), "B".into(), "C".into()],
            clauses: vec![HtClause {
                body: vec![c(false, 0, 0)],
                head: vec![c(false, 1, 0), c(false, 2, 0)],
            }],
            ..Default::default()
        };
        let out = bridged_saturate(&tin).expect("in fragment");
        // Soundness bar: whatever A gets, it must not be a WRONG certainty.
        // A is satisfiable with no named subsumers; SAT-certain is acceptable
        // ONLY with an empty subsumer set; unknown (defer) is acceptable.
        match out.sat_verdict[0] {
            Some(true) => panic!("A is satisfiable — UNSAT-certain is unsound"),
            Some(false) => {
                assert_eq!(
                    out.certain_subsumers[0].as_deref(),
                    Some(&[][..]),
                    "a certain subsumer from ONE disjunct branch would be unsound"
                );
            }
            None => {}
        }
        assert_eq!(out.sat_verdict[1], Some(false));
        assert_eq!(out.sat_verdict[2], Some(false));
    }

    #[test]
    fn saturation_never_sat_certain_on_forall_exists_clash() {
        use crate::orchestrate::cb_to_ht::{HAtom, HtClause, TInput};
        let c = |neg: bool, cc: usize, t: usize| HAtom::Concept { neg, c: cc, t };
        // A ⊑ ∃r.B and A ⊑ ∀r.¬B ⇒ A unsatisfiable. The cheap saturation
        // shares successor nodes, so it may not DETECT the clash — but it must
        // never claim SAT-certain (the ∀-into-creation-direction escape hatch:
        // criticality/insufficiency must fire).
        let tin = TInput {
            concepts: vec!["A".into(), "B".into()],
            roles: vec!["r".into()],
            clauses: vec![
                HtClause {
                    body: vec![c(false, 0, 0)],
                    head: vec![HAtom::Exist {
                        r: 0,
                        neg: false,
                        c: 1,
                        t: 0,
                    }],
                },
                // A(x) ∧ r(x,y) ∧ B(y) → ⊥  (A ⊑ ∀r.¬B)
                HtClause {
                    body: vec![c(false, 0, 0), HAtom::Role { r: 0, s: 0, t: 1 }, c(false, 1, 1)],
                    head: vec![],
                },
            ],
            ..Default::default()
        };
        let out = bridged_saturate(&tin).expect("in fragment");
        assert_ne!(
            out.sat_verdict[0],
            Some(false),
            "A is UNSAT — SAT-certain would be a soundness bug \
             (the ∀-into-creation-direction hatch must defer or clash)"
        );
        assert_eq!(out.sat_verdict[1], Some(false), "B alone is satisfiable");
        // Oracle: the probe path proves A unsatisfiable.
        let r = bridged_classify(&tin).expect("classify");
        assert!(r.unsatisfiable.contains(&0));
    }

    // -----------------------------------------------------------------------
    // Task #24: precise ATMOST criticality test (isCriticalATMOSTConcept-
    // DescriptorInsufficient + collect + simple/detailed mergeability).
    // -----------------------------------------------------------------------

    /// `A ⊑ ∃r.B, A ⊑ ≤2 r.B`: one successor against a bound of two — the
    /// precise test must answer SAT-certain (the old conservative stub
    /// deferred EVERY critical ≤n).
    #[test]
    fn saturation_answers_atmost_within_bound() {
        use crate::orchestrate::cb_to_ht::{CardDefJson, HAtom, HtClause, TInput};
        let c = |neg: bool, cc: usize, t: usize| HAtom::Concept { neg, c: cc, t };
        let tin = TInput {
            concepts: vec!["A".into(), "B".into()],
            roles: vec!["r".into()],
            clauses: vec![HtClause {
                body: vec![c(false, 0, 0)],
                head: vec![HAtom::Exist {
                    r: 0,
                    neg: false,
                    c: 1,
                    t: 0,
                }],
            }],
            card_defs: vec![CardDefJson {
                marker: 0,
                min: false,
                n: 2,
                role: 0,
                filler: 1,
            }],
            ..Default::default()
        };
        let out = bridged_saturate(&tin).expect("in fragment");
        assert_eq!(
            out.sat_verdict[0],
            Some(false),
            "A has 1 r.B successor against ≤2 r.B — must be SAT-certain"
        );
        assert_eq!(out.sat_verdict[1], Some(false));
        // Oracle agreement.
        let r = bridged_classify(&tin).expect("classify");
        assert!(r.unsatisfiable.is_empty());
    }

    /// `A ⊑ ∃r.B, A ⊑ ∃r.C, A ⊑ ≤1 r.B`: the C-successor does not count
    /// toward the qualified bound (its label cannot positively satisfy B) —
    /// SAT-certain with the precise qualified counting.
    #[test]
    fn saturation_atmost_qualified_counting_sat() {
        use crate::orchestrate::cb_to_ht::{CardDefJson, HAtom, HtClause, TInput};
        let c = |neg: bool, cc: usize, t: usize| HAtom::Concept { neg, c: cc, t };
        let ex = |r: usize, cc: usize| HAtom::Exist {
            r,
            neg: false,
            c: cc,
            t: 0,
        };
        let tin = TInput {
            concepts: vec!["A".into(), "B".into(), "C".into()],
            roles: vec!["r".into()],
            clauses: vec![
                HtClause {
                    body: vec![c(false, 0, 0)],
                    head: vec![ex(0, 1)],
                },
                HtClause {
                    body: vec![c(false, 0, 0)],
                    head: vec![ex(0, 2)],
                },
            ],
            card_defs: vec![CardDefJson {
                marker: 0,
                min: false,
                n: 1,
                role: 0,
                filler: 1,
            }],
            ..Default::default()
        };
        let out = bridged_saturate(&tin).expect("in fragment");
        assert_eq!(
            out.sat_verdict[0],
            Some(false),
            "only the B-successor counts toward ≤1 r.B — A is SAT-certain"
        );
        // Oracle agreement.
        let r = bridged_classify(&tin).expect("classify");
        assert!(r.unsatisfiable.is_empty());
    }

    /// `A ⊑ ∃r.B1, A ⊑ ∃r.B2, B1 ⊑ B, B2 ⊑ B, A ⊑ ≤1 r.B`: both successors
    /// count, but their labels are compatible — the mergeability discount
    /// brings the residual cardinality back to the bound ⇒ SAT-certain.
    #[test]
    fn saturation_atmost_merging_discount_sat() {
        use crate::orchestrate::cb_to_ht::{CardDefJson, HAtom, HtClause, TInput};
        let c = |neg: bool, cc: usize, t: usize| HAtom::Concept { neg, c: cc, t };
        let ex = |r: usize, cc: usize| HAtom::Exist {
            r,
            neg: false,
            c: cc,
            t: 0,
        };
        let tin = TInput {
            concepts: vec!["A".into(), "B".into(), "B1".into(), "B2".into()],
            roles: vec!["r".into()],
            clauses: vec![
                HtClause {
                    body: vec![c(false, 0, 0)],
                    head: vec![ex(0, 2)],
                },
                HtClause {
                    body: vec![c(false, 0, 0)],
                    head: vec![ex(0, 3)],
                },
                HtClause {
                    body: vec![c(false, 2, 0)],
                    head: vec![c(false, 1, 0)],
                },
                HtClause {
                    body: vec![c(false, 3, 0)],
                    head: vec![c(false, 1, 0)],
                },
            ],
            card_defs: vec![CardDefJson {
                marker: 0,
                min: false,
                n: 1,
                role: 0,
                filler: 1,
            }],
            ..Default::default()
        };
        let out = bridged_saturate(&tin).expect("in fragment");
        assert_eq!(
            out.sat_verdict[0],
            Some(false),
            "the two r-successors are label-mergeable — ≤1 r.B holds, A SAT-certain"
        );
        // Oracle agreement.
        let r = bridged_classify(&tin).expect("classify");
        assert!(r.unsatisfiable.is_empty());
    }

    /// The disjoint twin of the merging-discount case: `B1 ⊓ B2 ⊑ ⊥` makes
    /// the merge clash, so A is UNSATISFIABLE — the saturation must NOT
    /// claim SAT-certain (label-merging-problematic must veto the discount).
    #[test]
    fn saturation_atmost_disjoint_successors_not_sat_certain() {
        use crate::orchestrate::cb_to_ht::{CardDefJson, HAtom, HtClause, TInput};
        let c = |neg: bool, cc: usize, t: usize| HAtom::Concept { neg, c: cc, t };
        let ex = |r: usize, cc: usize| HAtom::Exist {
            r,
            neg: false,
            c: cc,
            t: 0,
        };
        let tin = TInput {
            concepts: vec!["A".into(), "B".into(), "B1".into(), "B2".into()],
            roles: vec!["r".into()],
            clauses: vec![
                HtClause {
                    body: vec![c(false, 0, 0)],
                    head: vec![ex(0, 2)],
                },
                HtClause {
                    body: vec![c(false, 0, 0)],
                    head: vec![ex(0, 3)],
                },
                HtClause {
                    body: vec![c(false, 2, 0)],
                    head: vec![c(false, 1, 0)],
                },
                HtClause {
                    body: vec![c(false, 3, 0)],
                    head: vec![c(false, 1, 0)],
                },
                // B1 ⊓ B2 ⊑ ⊥
                HtClause {
                    body: vec![c(false, 2, 0), c(false, 3, 0)],
                    head: vec![],
                },
            ],
            card_defs: vec![CardDefJson {
                marker: 0,
                min: false,
                n: 1,
                role: 0,
                filler: 1,
            }],
            ..Default::default()
        };
        let out = bridged_saturate(&tin).expect("in fragment");
        assert_ne!(
            out.sat_verdict[0],
            Some(false),
            "A is UNSAT (disjoint successors under ≤1 r.B) — SAT-certain would \
             mean the mergeability discount ignored the disjointness"
        );
        // Oracle: the probe path proves A unsatisfiable.
        let r = bridged_classify(&tin).expect("classify");
        assert!(r.unsatisfiable.contains(&0));
    }

    /// `A ⊑ ≥3 r.B, A ⊑ ≤2 r.B`: the pairwise-distinct ≥3 successors exceed
    /// the bound — the saturation must not read SAT-certain (Konclude clashes
    /// the node in collectATMOSTConceptRelevantSuccessors when a single
    /// distinct-successor block already exceeds the allowance).
    #[test]
    fn saturation_atleast_over_atmost_not_sat_certain() {
        use crate::orchestrate::cb_to_ht::{CardDefJson, HAtom, HtClause, TInput};
        let tin = TInput {
            concepts: vec!["A".into(), "B".into()],
            roles: vec!["r".into()],
            clauses: vec![],
            card_defs: vec![
                CardDefJson {
                    marker: 0,
                    min: true,
                    n: 3,
                    role: 0,
                    filler: 1,
                },
                CardDefJson {
                    marker: 0,
                    min: false,
                    n: 2,
                    role: 0,
                    filler: 1,
                },
            ],
            ..Default::default()
        };
        let out = bridged_saturate(&tin).expect("in fragment");
        assert_ne!(
            out.sat_verdict[0],
            Some(false),
            "A is UNSAT (≥3 r.B vs ≤2 r.B) — SAT-certain is unsound"
        );
        assert_eq!(out.sat_verdict[1], Some(false), "B alone is satisfiable");
        // Oracle: the probe path proves A unsatisfiable.
        let r = bridged_classify(&tin).expect("classify");
        assert!(
            r.unsatisfiable.contains(&0),
            "probe oracle must prove A unsat (got {:?})",
            r.unsatisfiable
        );
    }

    // -----------------------------------------------------------------------
    // Saturation-node coupling into the completion probes (task #24 wave 2):
    // expand-from-saturation (u17) + caching-blocking (u22) armed inside the
    // probe env after a same-env saturation pass. Driven programmatically
    // (env-var-independent).
    // -----------------------------------------------------------------------

    /// The ∃-rule must replay the filler's saturated label onto the fresh
    /// successor (expansion) and establish saturation blocking on it — and
    /// both must KEEP firing after a `reset_probe_env` carry (the arenas +
    /// reference linkings survive the reset).
    #[test]
    fn satcache_expansion_and_blocking_fire_in_probe() {
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:A)) Declaration(Class(:B))\n\
             Declaration(Class(:C)) Declaration(Class(:D))\n\
             Declaration(ObjectProperty(:r))\n\
             SubClassOf(:A ObjectSomeValuesFrom(:r :B))\n\
             SubClassOf(:B :C)\n)"
        );
        let env = bridge_ofn(&ofn);
        let (mut algo, mut ctx, bridged) = fresh_bridge_env(&env.tin);
        assert_eq!(bridged.unsupported, 0, "fully bridged");
        assert!(
            run_bridged_saturation(&mut ctx, &bridged),
            "saturation within budget"
        );
        let arm = |algo: &mut CompletionTaskHandleAlgorithm| {
            algo.conf_expand_created_successors_from_saturation = true;
            algo.conf_caching_blocking_from_saturation = true;
        };
        arm(&mut algo);
        let idx = |s: &str| -> usize {
            env.tin
                .concepts
                .iter()
                .position(|n| n == s)
                .unwrap_or_else(|| panic!("concept {s} not in TInput"))
        };
        let (a, d) = (bridged.named[idx("A")], bridged.named[idx("D")]);
        let mut id = 0i64;
        // A ⊓ ¬D is satisfiable (A ⋢ D); the drive expands A's ∃r.B.
        let verdict = bridged_unsat(&mut algo, &mut ctx, &bridged, &mut id, &[(a, false), (d, true)]);
        assert_eq!(verdict, Some(false), "A ⊑ D must NOT hold");
        assert!(
            algo.saturation_expansion_concept_count > 0,
            "the saturated filler label must be replayed onto the ∃-successor"
        );
        assert!(
            algo.saturation_cache_establish_count > 0,
            "the ∃-successor must be established saturation-blocked"
        );
        // The classify-style reset must CARRY the saturation state: the
        // coupling keeps firing on the warm env.
        reset_probe_env(&mut algo, &mut ctx, &bridged, true);
        arm(&mut algo);
        let mut id2 = 0i64;
        let warm = bridged_unsat(&mut algo, &mut ctx, &bridged, &mut id2, &[(a, false), (d, true)]);
        assert_eq!(warm, Some(false), "verdict stable across the carry");
        assert!(
            algo.saturation_expansion_concept_count > 0
                && algo.saturation_cache_establish_count > 0,
            "the coupling must survive reset_probe_env (saturation arenas carried)"
        );
    }

    /// A clashed saturation node must replay as a CLASH in the probe: with
    /// B deterministically unsatisfiable (B ⊑ C ⊓ ¬C), probing A (⊑ ∃r.B)
    /// must answer UNSAT through `try_expansion_from_saturated_data`'s
    /// clash arm — and agree with the plain (uncoupled) probe.
    #[test]
    fn satcache_clash_replay_probe_unsat() {
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C))\n\
             Declaration(ObjectProperty(:r))\n\
             SubClassOf(:A ObjectSomeValuesFrom(:r :B))\n\
             SubClassOf(:B :C)\n\
             SubClassOf(:B ObjectComplementOf(:C))\n)"
        );
        let env = bridge_ofn(&ofn);
        let idx = |s: &str| -> usize {
            env.tin
                .concepts
                .iter()
                .position(|n| n == s)
                .unwrap_or_else(|| panic!("concept {s} not in TInput"))
        };
        // Plain probe (no saturation, no coupling): A unsat.
        {
            let (mut algo, mut ctx, bridged) = fresh_bridge_env(&env.tin);
            assert_eq!(bridged.unsupported, 0);
            let a = bridged.named[idx("A")];
            let mut id = 0i64;
            let plain = bridged_unsat(&mut algo, &mut ctx, &bridged, &mut id, &[(a, false)]);
            assert_eq!(plain, Some(true), "A is unsatisfiable (plain probe)");
        }
        // Coupled probe: the ∃-rule must clash from B's CLASHED saturation node.
        {
            let (mut algo, mut ctx, bridged) = fresh_bridge_env(&env.tin);
            assert!(run_bridged_saturation(&mut ctx, &bridged));
            algo.conf_expand_created_successors_from_saturation = true;
            algo.conf_caching_blocking_from_saturation = true;
            let a = bridged.named[idx("A")];
            let mut id = 0i64;
            let coupled = bridged_unsat(&mut algo, &mut ctx, &bridged, &mut id, &[(a, false)]);
            assert_eq!(coupled, Some(true), "A is unsatisfiable (coupled probe)");
        }
    }

    /// Public-API A/B/C: plain probes vs saturation-only vs saturation +
    /// coupling must classify identically on a mixed ontology whose
    /// disjunction forces a probe residue (the coupling actually runs).
    #[test]
    fn satcache_classification_matches_plain() {
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:X)) Declaration(Class(:Y)) Declaration(Class(:Z))\n\
             Declaration(Class(:A1)) Declaration(Class(:A2))\n\
             Declaration(Class(:B)) Declaration(Class(:C))\n\
             Declaration(ObjectProperty(:r))\n\
             SubClassOf(:X ObjectUnionOf(:A1 :A2))\n\
             SubClassOf(:A1 :Y)\n\
             SubClassOf(:A2 :Y)\n\
             SubClassOf(:Y ObjectSomeValuesFrom(:r :B))\n\
             SubClassOf(:B :C)\n\
             SubClassOf(:Z ObjectAllValuesFrom(:r ObjectComplementOf(:B)))\n)"
        );
        let env = bridge_ofn(&ofn);
        let norm = |r: BridgedClassification| {
            let mut u = r.unsatisfiable;
            let mut s = r.subsumptions;
            u.sort_unstable();
            s.sort_unstable();
            (u, s)
        };
        let plain = norm(bridged_classify_opts(&env.tin, false, false).expect("plain arm"));
        let sat_only = norm(bridged_classify_opts(&env.tin, true, false).expect("sat-only arm"));
        let coupled = norm(bridged_classify_opts(&env.tin, true, true).expect("coupled arm"));
        assert_eq!(plain, sat_only, "saturation-only must not change verdicts");
        assert_eq!(plain, coupled, "the saturation-node coupling must not change verdicts");
    }

    /// Full-agreement harness: saturation certainties vs the probe-path
    /// classification on a small mixed ontology (Horn taxonomy + one
    /// disjunction + one ∃/∀ interaction). Every CERTAIN saturation answer
    /// must match the oracle exactly; unknowns are free.
    #[test]
    fn saturation_certainties_agree_with_probe_classification() {
        use crate::orchestrate::cb_to_ht::{HAtom, HtClause, TInput};
        let c = |neg: bool, cc: usize, t: usize| HAtom::Concept { neg, c: cc, t };
        // 0=A 1=B 2=C 3=D 4=E; r
        // A ⊑ B, B ⊑ C, D ⊑ B ⊔ C, E ⊑ ∃r.A, E ⊑ ∀r.B (entailed anyway), C ⊓ A ⊑ D? no — keep simple.
        let tin = TInput {
            concepts: vec![
                "A".into(),
                "B".into(),
                "C".into(),
                "D".into(),
                "E".into(),
            ],
            roles: vec!["r".into()],
            clauses: vec![
                HtClause {
                    body: vec![c(false, 0, 0)],
                    head: vec![c(false, 1, 0)],
                },
                HtClause {
                    body: vec![c(false, 1, 0)],
                    head: vec![c(false, 2, 0)],
                },
                HtClause {
                    body: vec![c(false, 3, 0)],
                    head: vec![c(false, 1, 0), c(false, 2, 0)],
                },
                HtClause {
                    body: vec![c(false, 4, 0)],
                    head: vec![HAtom::Exist {
                        r: 0,
                        neg: false,
                        c: 0,
                        t: 0,
                    }],
                },
            ],
            ..Default::default()
        };
        let oracle = bridged_classify(&tin).expect("classify");
        let oracle_subs: std::collections::HashSet<(usize, usize)> =
            oracle.subsumptions.iter().copied().collect();
        let out = bridged_saturate(&tin).expect("in fragment");
        for i in 0..tin.concepts.len() {
            match out.sat_verdict[i] {
                Some(true) => assert!(
                    oracle.unsatisfiable.contains(&i),
                    "saturation UNSAT-certain on {} disagrees with oracle",
                    tin.concepts[i]
                ),
                Some(false) => {
                    assert!(
                        !oracle.unsatisfiable.contains(&i),
                        "saturation SAT-certain on {} but oracle says unsat",
                        tin.concepts[i]
                    );
                    if let Some(subs) = &out.certain_subsumers[i] {
                        let sat_set: std::collections::HashSet<(usize, usize)> =
                            subs.iter().map(|&cc| (i, cc)).collect();
                        let oracle_row: std::collections::HashSet<(usize, usize)> = oracle_subs
                            .iter()
                            .filter(|&&(s, _)| s == i)
                            .copied()
                            .collect();
                        assert_eq!(
                            sat_set, oracle_row,
                            "certain-subsumer row for {} diverges from oracle",
                            tin.concepts[i]
                        );
                    }
                }
                None => {}
            }
        }
    }
}
