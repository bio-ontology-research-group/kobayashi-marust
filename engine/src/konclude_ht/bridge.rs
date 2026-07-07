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
        // KM_HT_BRIDGE_RECOG (opt-in): measured on ore_ont_12653, enabling
        // this arm produced 3 spurious subsumptions onto `Path` (the ≤(k−1)
        // disjunct's qualified merge appears to over-clash, suspect: the
        // atleast-created successors' distinctness vs the qualifier check in
        // the merge). Until that is root-caused against gold, the arm stays
        // OFF and such clauses count unsupported (the production driver then
        // correctly DECLINES rather than answer unsoundly).
        if !body_roles.is_empty()
            && cl.head.iter().any(|a| matches!(a, HAtom::Eq { .. }))
            && std::env::var_os("KM_HT_BRIDGE_RECOG").is_some()
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
    // per alternative via arena journals + databox snapshots. Measured cost:
    // the uniform first-touch journal re-clones the alternative's touched
    // slot set on EVERY backtrack cycle — 12653 DDB classify 0.9s → 260s —
    // so this is NOT coupled to DDB. It targets flat-graph deep-backtracking
    // onts (the 541 family); the path to defaulting it on is per-node
    // localization (Konclude's task-fork shape), not uniform journaling.
    if std::env::var_os("KM_HT_COW").is_some() {
        algo.conf_inprocess_cow = true;
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
    let budget: Option<std::time::Duration> = std::env::var("KM_BRIDGE_PROBE_BUDGET_S")
        .ok()
        .and_then(|s| s.parse::<u64>().ok())
        .map(std::time::Duration::from_secs);
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
    // KM_BRIDGE_PROBE_BUDGET_S also bounds the READ-OFF search: before the
    // DDB taint fix (2a869e8) heavy subjects' read-offs looked fast only
    // because wrong root-cancels cut them short; the genuine search is
    // unbounded without a deadline (measured: SUBJ PathOfLength3 read-off ran
    // 10 min to 126 GB). On overrun the drive raises a STOP → verdict None →
    // the caller records NO derivations for the subject (sound; shows as
    // missing vs gold, never spurious).
    algo.drive_deadline = std::env::var("KM_BRIDGE_PROBE_BUDGET_S")
        .ok()
        .and_then(|s| s.parse::<u64>().ok())
        .map(|b| std::time::Instant::now() + std::time::Duration::from_secs(b));

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
/// - any subject drive or verification probe STOPped without a verdict.
pub fn bridged_classify(tin: &TInput) -> Option<BridgedClassification> {
    if !tin.nominals.is_empty() {
        return None;
    }
    let n_named = tin.concepts.len();
    let subjects: Vec<usize> = if tin.queries.is_empty() {
        (0..n_named).collect()
    } else {
        tin.queries.iter().map(|&q| q as usize).collect()
    };
    let progress = std::env::var_os("KM_BRIDGE_PROGRESS").is_some();
    let mut out = BridgedClassification {
        unsatisfiable: Vec::new(),
        subsumptions: Vec::new(),
    };
    for (k, &s) in subjects.iter().enumerate() {
        let (mut algo, mut ctx, bridged) = fresh_bridge_env(tin);
        if bridged.unsupported > 0 {
            return None;
        }
        let mut next_indi_id: i64 = 1_000;
        let (subs, authoritative) =
            bridged_classify_subject(&mut algo, &mut ctx, &bridged, &mut next_indi_id, s, n_named)?;
        if progress && (k % 64 == 0 || k + 1 == subjects.len()) {
            eprintln!(
                "BRIDGE-CLASSIFY subject {}/{} auth={} subs={}",
                k + 1,
                subjects.len(),
                authoritative,
                subs.len()
            );
        }
        // The subject-unsatisfiable signal is the FULL index range
        // (authoritative). A tiny ontology can legitimately have a subject
        // subsumed by every named concept, so disambiguate with a direct
        // single-seed unsat probe.
        if authoritative && subs.len() == n_named {
            let (mut a2, mut c2, b2) = fresh_bridge_env(tin);
            let mut id2: i64 = 1_000;
            match bridged_unsat(&mut a2, &mut c2, &b2, &mut id2, &[(b2.named[s], false)]) {
                Some(true) => {
                    out.unsatisfiable.push(s);
                    continue;
                }
                Some(false) => {} // genuinely subsumed by everything — keep pairs
                None => return None,
            }
        }
        if authoritative {
            for c in subs {
                if c != s {
                    out.subsumptions.push((s, c));
                }
            }
            continue;
        }
        // Non-deterministic subject: verify each candidate pairwise.
        for c in subs {
            if c == s {
                continue;
            }
            let (mut a2, mut c2, b2) = fresh_bridge_env(tin);
            let mut id2: i64 = 1_000;
            match bridged_unsat(
                &mut a2,
                &mut c2,
                &b2,
                &mut id2,
                &[(b2.named[s], false), (b2.named[c], true)],
            ) {
                Some(true) => out.subsumptions.push((s, c)),
                Some(false) => {}
                None => return None,
            }
        }
        // A non-deterministic subject can also be unsatisfiable without the
        // read-off reporting the full range (a clash IS reported full-range,
        // so this is only reachable when the drive found a model — the
        // subject is satisfiable; nothing to check).
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
}
