//! The disjunctive context calculus engine (single-threaded), a faithful port
//! of Sequoia's `context/Context.scala`, `context/Rules.scala`, and
//! `context/ContextState.scala`.
//!
//! Rules implemented: Core, Hyper, Pred, Succ, Eq, Ineq, Elim (redundancy).
//! Expansion strategy: a *pay-as-you-go* strategy — one successor context per
//! function symbol `f` (`successor_for`), instead of the trivial strategy's
//! single shared empty-core context for every anonymous successor.  Both are
//! sound and complete (the trivial one is Simančík et al.); the per-`f` variant
//! avoids piling every existential's successor into one context, which is what
//! blows up under disjunction (≈45× on a distinct-skolem disjunctive stress
//! test).  Soundness is re-checked per run by the Lean certificate checker;
//! completeness is validated against the HermiT oracle and scaffolded in
//! `lean/ContextCalculus/CompletenessStrategy.lean`.  Factor and full nominal
//! rules (Nom/Join/r-Succ/r-Pred of Table 3) are not implemented; clauses
//! requiring them are reported.

use std::collections::{HashMap, HashSet, VecDeque};

use crate::calc::*;
use crate::clause::*;

thread_local! {
    /// Hyper-call counter (only read under KM_STATS). Thread-local because
    /// `hyper` takes `&self`; reset per Engine run via `reset_hyper_calls`.
    static HYPER_CALLS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

// ----------------------------- substitutions -------------------------------

/// Central substitution used by Hyper: maps ontology variables (x, z_i) to
/// context terms.  `x -> x` always; function terms map to themselves.
#[derive(Clone)]
struct CentralSubst {
    map: HashMap<Term, Term>,
    /// Grounded Hyper (σ(x) ∈ Σo, arXiv:1805.01396): permitted only in the
    /// ground (nominal root) context — everywhere else the central variable
    /// maps to itself, as before. Binding x in one ground match and to X in
    /// another is rejected either way (a worked-off provider's residues are
    /// copied unsubstituted, so mixing the two would be unsound).
    allow_ground: bool,
}
impl CentralSubst {
    fn new(allow_ground: bool) -> Self {
        CentralSubst { map: HashMap::new(), allow_ground }
    }
    fn add(&mut self, i: Term, o: Term) -> bool {
        if is_central(i) {
            if o == X || (self.allow_ground && is_individual(o)) {
                return match self.map.get(&X) {
                    Some(&e) => e == o,
                    None => {
                        self.map.insert(X, o);
                        true
                    }
                };
            }
            return false;
        }
        match self.map.get(&i) {
            Some(&existing) => existing == o,
            None => {
                self.map.insert(i, o);
                true
            }
        }
    }
    fn apply(&self, v: Term) -> Term {
        if v == X {
            return *self.map.get(&X).unwrap_or(&X);
        }
        if is_function(v) {
            // f(x) under a grounded central becomes the composite f(o).
            if let Some(&b) = self.map.get(&X) {
                if b != X {
                    return comp_term(v, b);
                }
            }
            return v;
        }
        *self.map.get(&v).unwrap_or(&v)
    }
    fn get(&self, v: Term) -> Option<Term> {
        self.map.get(&v).copied()
    }
}

/// Symmetric-group pruning for the Hyper join: for each exchange-invariant
/// neighbour-variable group of `oc`, require the bound members' terms to be
/// sorted in group order (strictly when the head carries an equality for every
/// pair of the group — an equal-term assignment then makes some head equality
/// trivially true, a tautology `build_hyper_resolvent` would drop anyway).
/// Every pruned full assignment is a permutation of exactly one kept one and
/// produces the identical canonical resolvent, so the derived set is
/// unchanged; only duplicate (and tautological) enumeration is skipped.
/// Variables occurring in the side-clause body position are exempt: the side
/// clause is pinned to that position, so its binding is not interchangeable
/// with the worked-off candidates.
fn sym_groups_ok(oc: &OntologyClause, exempt: &[Term], sigma: &CentralSubst) -> bool {
    for (g, strict) in &oc.sym_groups {
        let mut prev: Option<Term> = None;
        for &v in g {
            if exempt.contains(&v) {
                continue;
            }
            let t = match sigma.get(v) {
                Some(t) => t,
                None => continue,
            };
            if let Some(p) = prev {
                if *strict {
                    // Ground context: an equal assignment to y is the Nom
                    // trigger (the head equality becomes y≈y, which the Nom
                    // rule replaces with the additional-nominal disjunction
                    // rather than dropping as a tautology), so the
                    // tautology-based strict pruning must not discard it.
                    if sigma.allow_ground && p == t && t == Y {
                        // keep
                    } else if p >= t {
                        return false;
                    }
                } else if p > t {
                    return false;
                }
            }
            prev = Some(t);
        }
    }
    true
}

/// Su^r detection (arXiv:1805.01396): a max-head atom about an individual —
/// `B(o)`, `S(x,o)`, `S(o,x)` — whose y-form (`B(o)`, `S(y,o)`, `S(o,y)`) is
/// pushed to the ground context by r-Succ, labelled by the individual.
fn root_succ_form(p: &Pred) -> Option<(Pred, Term)> {
    match *p {
        Pred::Concept { iri, t } if is_individual(t) => Some((Pred::Concept { iri, t }, t)),
        Pred::Role { iri, s, t } => {
            if is_central(s) && is_individual(t) {
                Some((Pred::Role { iri, s: Y, t }, t))
            } else if is_individual(s) && is_central(t) {
                Some((Pred::Role { iri, s, t: Y }, s))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Merge-form literal of the r-Succ side condition (*): `x ≈ o`, `y ≈ o`, or
/// `x ≈ y` (canonical `Lit::eq` puts the larger term first: individuals sit
/// above x above y).  A clause `Γ'' → Δ'' ∨ ⋁ L_i` of merge-form `L_i` with
/// `Γ'' ⊆ Γ`, `Δ'' ⊆ Δ` *blocks* the r-Succ push of `Γ → Δ ∨ Aσ`: the
/// context's element may itself be a nominal (or merge with its predecessor),
/// so the calculus defers to equality reasoning instead of creating the edge.
fn is_merge_lit(l: &Lit) -> bool {
    matches!(*l, Lit::Eq { s, t } if (is_individual(s) && (t == X || t == Y)) || (s == X && t == Y))
}

/// r-Succ side condition (*): the push of the maximal head atom `a` from
/// clause `c` (`Γ → Δ ∨ Aσ` with `Γ = c.body`, `Δ = c.head \ {Aσ}`) is
/// *blocked* when the context holds a clause `Γ'' → Δ'' ∨ ⋁ L_i` with
/// `Γ'' ⊆ Γ`, `Δ'' ⊆ Δ`, and every `L_i` a merge-form literal (≥ 1 of them) —
/// the element may itself be a nominal or merge with its predecessor, so the
/// calculus defers to equality reasoning instead of creating the edge.
fn rsucc_blocked(ctx: &Context, arena: &[ContextClause], c: &ContextClause, a: &Pred) -> bool {
    'cand: for &mi in &ctx.merge_clauses {
        let m = &arena[mi as usize];
        if !m.body.iter().all(|b| c.body.contains(b)) {
            continue;
        }
        let mut has_merge = false;
        for l in &m.head {
            if is_merge_lit(l) {
                has_merge = true;
                continue;
            }
            if *l == Lit::P(*a) || !c.head.contains(l) {
                continue 'cand;
            }
        }
        if has_merge {
            return true;
        }
    }
    false
}

/// `true` if the clause mentions the central variable x anywhere (such
/// ground-context clauses are instantiated per individual-labelled edge by the
/// Pred back-substitution, so they keep the per-edge propagation path).
fn cc_mentions_x(c: &ContextClause) -> bool {
    fn px(p: &Pred) -> bool {
        match *p {
            Pred::Concept { t, .. } => t == X,
            Pred::Role { s, t, .. } => s == X || t == X,
        }
    }
    c.body.iter().any(px)
        || c.head.iter().any(|l| match *l {
            Lit::P(p) => px(&p),
            Lit::Eq { s, t } | Lit::Ineq { s, t } => s == X || t == X,
        })
}

/// Collect the individuals mentioned by a predicate (decoding `f(o)`
/// composites) into `out`, deduplicated.
fn pred_inds(p: &Pred, out: &mut Vec<Term>) {
    fn push(t: Term, out: &mut Vec<Term>) {
        let t = if is_comp(t) { comp_parts(t).1 } else { t };
        if is_individual(t) && !out.contains(&t) {
            out.push(t);
        }
    }
    match *p {
        Pred::Concept { t, .. } => push(t, out),
        Pred::Role { s, t, .. } => {
            push(s, out);
            push(t, out);
        }
    }
}

fn lit_inds(l: &Lit, out: &mut Vec<Term>) {
    match l {
        Lit::P(p) => pred_inds(p, out),
        Lit::Eq { s, t } | Lit::Ineq { s, t } => {
            for &v in &[*s, *t] {
                let v = if is_comp(v) { comp_parts(v).1 } else { v };
                if is_individual(v) && !out.contains(&v) {
                    out.push(v);
                }
            }
        }
    }
}

/// Forward inter-context mapping for Succ: {f(x) -> x, x -> y}; for a
/// grounded edge labelled by a composite `f(o)` it is {f(o) -> x, o -> y}
/// (the parent of the `f(o)` element is the individual o, not the sender's
/// central element — arXiv:1805.01396 root-context Succ).
fn forwards(f: Term, v: Term) -> Term {
    if v == f {
        return X;
    }
    if is_comp(f) {
        let (_, o) = comp_parts(f);
        return if v == o { Y } else { v };
    }
    if v == X {
        Y
    } else {
        // neighbour/other terms do not occur in a succ trigger predicate
        v
    }
}
/// Backward inter-context substitution for Pred: {y -> x, x -> f(x)}; for a
/// grounded edge labelled `f(o)` it is {y -> o, x -> f(o)} — conclusions
/// about the parent are conclusions about the individual o, and they arrive
/// ground.
fn backwards(f: Term, v: Term) -> Term {
    if is_comp(f) {
        let (_, o) = comp_parts(f);
        return if v == Y {
            o
        } else if v == X {
            f
        } else {
            v
        };
    }
    if v == Y {
        X
    } else if v == X {
        f
    } else {
        v
    }
}

// ------------------------------- unification -------------------------------

fn can_unify(body: &Pred, head_max: &Pred) -> bool {
    // A central body term must match a central head term or — grounded Hyper
    // of the nominal calculus — an individual; a neighbour body term (e.g.
    // C(y) in `R(x,y) ∧ C(y) -> D(x)`) may bind to any head term, including a
    // function term C(f(x)).  (Pure syntactic unification — sound regardless
    // of the body term's role.)
    fn central_ok(b: Term, h: Term) -> bool {
        !is_central(b) || is_central(h) || is_individual(h)
    }
    match (body, head_max) {
        (Pred::Concept { iri: i1, t: t1 }, Pred::Concept { iri: i2, t: t2 }) => {
            i1 == i2 && central_ok(*t1, *t2)
        }
        (Pred::Role { iri: i1, s: s1, t: t1 }, Pred::Role { iri: i2, s: s2, t: t2 }) => {
            i1 == i2 && central_ok(*s1, *s2) && central_ok(*t1, *t2)
        }
        _ => false,
    }
}

fn unify(sigma: &mut CentralSubst, body: &Pred, head: &Pred) -> bool {
    match (body, head) {
        (Pred::Concept { iri: i1, t: t1 }, Pred::Concept { iri: i2, t: t2 }) => {
            i1 == i2 && sigma.add(*t1, *t2)
        }
        (Pred::Role { iri: i1, s: s1, t: t1 }, Pred::Role { iri: i2, s: s2, t: t2 }) => {
            i1 == i2 && sigma.add(*s1, *s2) && sigma.add(*t1, *t2)
        }
        _ => false,
    }
}

// -------------------------------- ontology ---------------------------------

#[derive(Default)]
struct Ontology {
    clauses: Vec<OntologyClause>,
    facts: Vec<usize>,               // indices of empty-body clauses (x-form only)
    /// Ground facts (empty-body clauses whose head mentions an individual),
    /// keyed by each individual they mention. Seeded fully into the ground
    /// context and on demand into a context that first derives an atom about
    /// that individual (docs/NOMINALS-CB.md); empty without nominal mode.
    ground_facts: HashMap<Term, Vec<usize>>,
    concept_clauses: HashMap<Iri, Vec<usize>>, // body Concept(iri,x)
    forward_role_clauses: HashMap<Iri, Vec<usize>>, // body Role(iri,x,_)
    backward_role_clauses: HashMap<Iri, Vec<usize>>, // body Role(iri,_,x)
    /// clauses with *any* body Concept(iri, _) (central or neighbour term)
    concept_body_any: HashMap<Iri, Vec<usize>>,
    /// clauses with *any* body Role(iri, _, _)
    role_body_any: HashMap<Iri, Vec<usize>>,
}

impl Ontology {
    /// Candidate ontology clauses that may resolve with a context-clause head
    /// predicate `max` (i.e. have a body atom that can unify with `max`).
    /// Over-approximates by predicate iri; `can_unify` filters precisely.
    fn clauses_cand(&self, max: &Pred) -> Vec<usize> {
        let mut v = match *max {
            Pred::Concept { iri, .. } => {
                self.concept_body_any.get(&iri).cloned().unwrap_or_default()
            }
            Pred::Role { iri, .. } => self.role_body_any.get(&iri).cloned().unwrap_or_default(),
        };
        v.sort_unstable();
        v.dedup();
        v
    }
}

// ------------------------------- contexts ----------------------------------

struct Context {
    id: usize,
    core: Vec<Pred>,
    root: bool,
    /// the query concept this root context classifies (if any)
    query: Option<Iri>,
    /// Worked-off clauses, as ids into the engine-level clause arena for this
    /// context's ordering domain (root / non-root).  The arena is content-
    /// interned and append-only, so identical clauses derived in thousands of
    /// contexts (notably the seeded shared closure) are stored once; ids are
    /// stable and ascend in work-off order.
    worked_off: Vec<u32>,
    /// Arena ids of the clauses currently in `worked_off` ∪ `todo` (the arena
    /// id IS the canonical content key, so this replaces the old full
    /// (body, head) copy used for duplicate detection).
    clause_keys: HashSet<u32>,
    /// Index from a head-predicate iri to the (ascending, de-duplicated)
    /// `worked_off` indices of clauses having a *maximal* head predicate with
    /// that iri.  Lets Hyper/Pred find resolution partners without scanning all
    /// of `worked_off`.  Concept and role iris live in separate namespaces, so
    /// they are indexed separately; `can_unify` / exact-predicate tests still
    /// filter precisely, so the candidate set (and its order) is unchanged.
    head_concept_index: HashMap<Iri, Vec<u32>>,
    head_role_index: HashMap<Iri, Vec<u32>>,
    /// Subsumption index over `worked_off`: each clause is recorded under every
    /// literal of its head.  A clause `c` can subsume `clause` only if
    /// `c.head ⊆ clause.head`, so every true subsumer with a non-empty head is
    /// found under some literal of `clause.head`; conversely `clause` can
    /// subsume only clauses that contain *all* of `clause.head`, i.e. those in
    /// the intersection of these lists.  Empty-head clauses (which subsume on
    /// the body alone) are tracked separately.  This replaces the per-`add`
    /// linear scan of `worked_off` for both forward and backward subsumption.
    head_lit_index: HashMap<Lit, Vec<u32>>,
    empty_head_wo: Vec<u32>,
    todo: VecDeque<u32>,
    /// pred clauses pushed in from successor contexts (already back-substituted),
    /// as ids into the engine-level `pred_interned` table.  The same substituted
    /// clause can arrive more than once (e.g. from a successor's pre- and
    /// post-growth contexts under the central strategy); `neighbor_pred_seen`
    /// dedups arrivals, which only skips re-deriving already-derived clauses.
    neighbor_pred: Vec<u32>,
    neighbor_pred_seen: HashSet<u32>,
    /// successor edges: function term -> successor context id
    successors: HashMap<Term, usize>,
    /// Central strategy: per function symbol, the full (raw, un-substituted)
    /// set of succ-trigger predicates pushed so far.  The successor context for
    /// `f` is keyed by the σ-image of this set (its core); when the set grows,
    /// the edge re-targets a new context with the larger core.
    trigger_sets: HashMap<Term, std::collections::BTreeSet<Pred>>,
    /// Central strategy: the subset of `trigger_sets[f]` whose triggers were
    /// derived as unit facts (`⊤ → p`, no body, no disjunction) in this
    /// context.  ONLY these enter the successor's core: a disjunctively
    /// derived trigger is not known to hold, so asserting it in the core
    /// would make every consequence the successor pushes back conditional on
    /// the WHOLE core at once (an n-way simultaneous cut no resolution step
    /// can perform), losing the per-disjunct refutations completeness needs
    /// (the ≥n min-cardinality recognition stall on ore_ont_16461).
    /// Non-fact triggers still travel as Succ messages and become hypothesis
    /// clauses `p → p` at the target, so their consequences come back
    /// conditioned on `p` alone.
    fact_trigger_sets: HashMap<Term, std::collections::BTreeSet<Pred>>,
    /// predecessor edges: (predecessor ctx id, function term) -> pushed predicates
    predecessors: HashMap<(usize, Term), HashSet<Pred>>,
    pushed_succ: HashSet<Pred>,
    /// per predecessor edge, the `pred_pool` indices already pushed back, to
    /// avoid resending.  Pool indices are stable (the pool is append-only), so
    /// they identify the clause without copying it; a re-added identical clause
    /// gets a fresh index and is resent, which the receiver's
    /// `neighbor_pred_seen` dedups.
    pushed_pred: HashMap<(usize, Term), HashSet<u32>>,
    /// Semi-naive Pred propagation: append-only pool of worked-off clauses that
    /// are Pred-eligible (function-free, predicate-only head).  Entries are never
    /// removed (a clause back-subsumed out of `worked_off` is still
    /// context-entailed, so pushing it stays sound), which lets `pred_hwm` be a
    /// stable high-water mark despite `worked_off` reshuffling under back-subsume.
    /// Entries are arena ids (the arena is append-only, so the referenced
    /// clause outlives any back-subsumption).
    pred_pool: Vec<u32>,
    /// number of `pred_pool` entries already cross-checked against every edge at
    /// that edge's `edge_seen` pushed-length in a prior `propagate`.
    pred_hwm: usize,
    /// per predecessor edge, the `pushed`-set length at which all of
    /// `pred_pool[..pred_hwm]` were last checked against it.  An edge whose
    /// current pushed-set is longer is "dirty" and forces a re-check of the old
    /// pool against it (a previously-failed covered-check can only flip when the
    /// edge gains a pushed predicate).
    edge_seen: HashMap<(usize, Term), usize>,
    /// Semi-naive Succ propagation: append-only pool of worked-off clauses with a
    /// function-headed (succ-trigger candidate) maximal head predicate, and the
    /// high-water mark of entries already scanned for Succ triggers.
    /// Entries are arena ids.
    succ_pool: Vec<u32>,
    succ_hwm: usize,
    /// Individuals whose ground ontology facts have been seeded into this
    /// context (demand-driven; see `Ontology::ground_facts`).
    seeded_inds: HashSet<Term>,
    /// Join rule (arXiv:1805.01396 Table 3): worked-off clauses indexed by
    /// each *ground* body atom (the verbatim-copied `C_i` of Pred/r-Pred),
    /// so a later-derived provider for that atom can resolve it.  Empty
    /// without individuals — the rule is inert on the SRIQ fragment.
    ground_body_index: HashMap<Pred, Vec<u32>>,
    /// Join case 3: body-empty clauses with a maximal head literal `x ≈ o`,
    /// keyed by the individual `o` (the bridge premise `Γ' → Δ'' ∨ x ≈ o`).
    bridge_index: HashMap<Term, Vec<u32>>,
    /// r-Succ side condition (*): worked-off clauses whose head contains a
    /// merge-form literal (`x ≈ o`, `y ≈ o`, `x ≈ y`) — the candidates that
    /// can block an r-Succ push (deferring to equality reasoning when this
    /// context's element may itself be a nominal or merge with its
    /// predecessor).
    merge_clauses: Vec<u32>,
    /// `true` if a new worked-off clause or a new predecessor edge/pushed
    /// predicate has appeared since the last `propagate`.  When `false`,
    /// `propagate` has no new Succ/Pred message to emit (the `pushed_succ` /
    /// `pushed_pred` sets already cover everything seen), so the full
    /// `worked_off` scan can be skipped.  Soundness/output are unchanged: a
    /// skipped scan would only have re-derived already-sent messages.
    dirty: bool,
}

impl Context {
    fn new(id: usize, core: Vec<Pred>, root: bool, query: Option<Iri>) -> Context {
        Context {
            id,
            core,
            root,
            query,
            worked_off: Vec::new(),
            clause_keys: HashSet::new(),
            head_concept_index: HashMap::new(),
            head_role_index: HashMap::new(),
            head_lit_index: HashMap::new(),
            empty_head_wo: Vec::new(),
            todo: VecDeque::new(),
            neighbor_pred: Vec::new(),
            neighbor_pred_seen: HashSet::new(),
            successors: HashMap::new(),
            trigger_sets: HashMap::new(),
            fact_trigger_sets: HashMap::new(),
            predecessors: HashMap::new(),
            pushed_succ: HashSet::new(),
            pushed_pred: HashMap::new(),
            pred_pool: Vec::new(),
            pred_hwm: 0,
            edge_seen: HashMap::new(),
            succ_pool: Vec::new(),
            succ_hwm: 0,
            seeded_inds: HashSet::new(),
            ground_body_index: HashMap::new(),
            bridge_index: HashMap::new(),
            merge_clauses: Vec::new(),
            dirty: true,
        }
    }

    /// Add the worked-off clause with arena id `cid` to the head-predicate
    /// index, recording `cid` once per distinct iri appearing among its maximal
    /// head predicates (the per-clause predicate list is re-scanned at lookup
    /// time, so a single entry per iri reproduces the original candidate
    /// sequence without duplicates).  Appending in work-off order keeps each
    /// list in candidate order.
    fn index_clause(&mut self, arena: &[ContextClause], cid: u32) {
        let c = &arena[cid as usize];
        let mut concept_iris: Vec<Iri> = Vec::new();
        let mut role_iris: Vec<Iri> = Vec::new();
        for (p, _) in c.max_head_predicates() {
            match p {
                Pred::Concept { iri, .. } => {
                    if !concept_iris.contains(&iri) {
                        concept_iris.push(iri);
                    }
                }
                Pred::Role { iri, .. } => {
                    if !role_iris.contains(&iri) {
                        role_iris.push(iri);
                    }
                }
            }
        }
        for iri in concept_iris {
            self.head_concept_index.entry(iri).or_default().push(cid);
        }
        for iri in role_iris {
            self.head_role_index.entry(iri).or_default().push(cid);
        }
        // subsumption index: record under every head literal (or the empty-head
        // list).
        if c.head.is_empty() {
            self.empty_head_wo.push(cid);
        } else {
            for &l in &c.head {
                self.head_lit_index.entry(l).or_default().push(cid);
            }
        }
        // nominal-calculus indexes (all empty without individuals)
        for p in &c.body {
            if p.is_ground() {
                let e = self.ground_body_index.entry(*p).or_default();
                if !e.contains(&cid) {
                    e.push(cid);
                }
            }
        }
        if c.body.is_empty() {
            for l in c.max_head() {
                if let Lit::Eq { s, t } = l {
                    if is_individual(s) && t == X {
                        self.bridge_index.entry(s).or_default().push(cid);
                    }
                }
            }
        }
        if c.head.iter().any(is_merge_lit) {
            self.merge_clauses.push(cid);
        }
    }

    /// Rebuild every `worked_off` index from scratch.  Called after
    /// back-subsumption physically removes clauses from `worked_off` (which
    /// shifts the indices the maps refer to); removals are comparatively rare,
    /// so a full rebuild keeps the common (append-only) path fast.
    fn rebuild_head_index(&mut self, arena: &[ContextClause]) {
        self.head_concept_index.clear();
        self.head_role_index.clear();
        self.head_lit_index.clear();
        self.empty_head_wo.clear();
        self.ground_body_index.clear();
        self.bridge_index.clear();
        self.merge_clauses.clear();
        for k in 0..self.worked_off.len() {
            let cid = self.worked_off[k];
            self.index_clause(arena, cid);
        }
    }

    /// Forward subsumption: is `clause` subsumed by some existing clause in
    /// `worked_off` or `todo`?  `worked_off` is consulted via the head-literal
    /// index (every non-empty-head subsumer shares a head literal with
    /// `clause`); `todo` is scanned linearly (it is the small work queue).
    /// The `(nb, nh)` length pre-filter skips clauses that cannot subsume.
    fn fwd_subsumed(&self, arena: &[ContextClause], clause: &ContextClause, nb: usize, nh: usize) -> bool {
        for &ci in &self.empty_head_wo {
            let c = &arena[ci as usize];
            if c.body.len() <= nb && c.test_strengthening(clause) == -1 {
                return true;
            }
        }
        for l in &clause.head {
            if let Some(cands) = self.head_lit_index.get(l) {
                for &ci in cands {
                    let c = &arena[ci as usize];
                    if c.body.len() <= nb && c.head.len() <= nh && c.test_strengthening(clause) == -1 {
                        return true;
                    }
                }
            }
        }
        for &ci in &self.todo {
            let c = &arena[ci as usize];
            if c.body.len() <= nb && c.head.len() <= nh && c.test_strengthening(clause) == -1 {
                return true;
            }
        }
        false
    }

    /// Backward subsumption: remove every existing clause that `clause`
    /// strengthens, from both `worked_off` and `todo`, dropping their keys.
    /// `worked_off` candidates come from the intersection of the head-literal
    /// lists (a clause strengthened by `clause` contains all of `clause.head`),
    /// approximated by the rarest such list and verified by `test_strengthening`;
    /// when `clause.head` is empty every clause is a candidate.  The common case
    /// removes nothing, so the expensive full `worked_off` scan and index
    /// rebuild are skipped entirely.  Same removed set and survivor order as a
    /// full linear scan, so the result is unchanged.
    fn back_subsume(&mut self, arena: &[ContextClause], clause: &ContextClause, nb: usize, nh: usize) {
        // The incoming clause must not remove an existing *identical* clause
        // (callers reject exact duplicates before back-subsuming, but the guard
        // mirrors the historical key check).
        let same = |c: &ContextClause| c.body == clause.body && c.head == clause.head;
        // ---- worked_off ----
        let mut remove_wo: Vec<u32> = Vec::new();
        if clause.head.is_empty() {
            for &ci in &self.worked_off {
                let c = &arena[ci as usize];
                if c.body.len() >= nb && c.head.len() >= nh && clause.test_strengthening(c) == -1 && !same(c) {
                    remove_wo.push(ci);
                }
            }
        } else {
            // smallest head-literal list (None if some head literal is absent,
            // in which case no clause contains all of `clause.head`).
            let mut best: Option<&Vec<u32>> = None;
            for l in &clause.head {
                match self.head_lit_index.get(l) {
                    None => {
                        best = None;
                        break;
                    }
                    Some(v) => {
                        if best.map_or(true, |b| v.len() < b.len()) {
                            best = Some(v);
                        }
                    }
                }
            }
            if let Some(cands) = best {
                for &ci in cands {
                    let c = &arena[ci as usize];
                    if c.body.len() >= nb && c.head.len() >= nh && clause.test_strengthening(c) == -1 && !same(c) {
                        remove_wo.push(ci);
                    }
                }
            }
        }
        if !remove_wo.is_empty() {
            let remove_set: HashSet<u32> = remove_wo.into_iter().collect();
            self.worked_off.retain(|ci| !remove_set.contains(ci));
            for ci in &remove_set {
                self.clause_keys.remove(ci);
            }
            self.rebuild_head_index(arena);
        }
        // ---- todo (not indexed) ----
        let mut removed_todo: Vec<u32> = Vec::new();
        let mut todo = std::mem::take(&mut self.todo);
        todo.retain(|&ci| {
            let c = &arena[ci as usize];
            if c.body.len() >= nb && c.head.len() >= nh && clause.test_strengthening(c) == -1 && !same(c) {
                removed_todo.push(ci);
                false
            } else {
                true
            }
        });
        self.todo = todo;
        for ci in removed_todo {
            self.clause_keys.remove(&ci);
        }
    }
}

/// A pred clause (substitution already applied): body and head over x / f(x),
/// plus — in nominal mode — ground atoms over individuals and the propagated
/// equality form `f(x) ≈ o` (image of a successor's `x ≈ o`, the Pr extension
/// of the ALCHOIQ calculus). Heads are full literals so those equalities
/// survive the crossing; without individuals only `Lit::P` heads ever enter
/// the pred pool, so this is representation-only for the SRIQ fragment.
#[derive(Clone, PartialEq, Eq, Hash)]
struct PredClause {
    body: Vec<Pred>,
    head: Vec<Lit>,
}

/// Content hash for interning (collisions are resolved by exact comparison,
/// never trusted on their own).
fn content_hash<T: std::hash::Hash>(t: &T) -> u64 {
    use std::hash::Hasher;
    let mut h = std::collections::hash_map::DefaultHasher::new();
    t.hash(&mut h);
    h.finish()
}

// ------------------------------- messages ----------------------------------

enum Msg {
    Succ {
        from: usize,
        f: Term,
        p: Pred, // already forward-substituted (over successor's x/y)
        target: usize,
    },
    /// A pushed-back clause, by reference into the sender's append-only
    /// `pred_pool` (both the pool entry and the sender's core are immutable
    /// once created, so resolving them at apply time reads exactly what a
    /// send-time snapshot would have carried).
    Pred {
        to: usize,
        from: usize,
        edge_label: Term,
        pool_idx: u32,
    },
}

// -------------------------------- engine -----------------------------------

pub struct Engine {
    pub sig: Sig,
    ont: Ontology,
    contexts: Vec<Context>,
    core_index: HashMap<Vec<Pred>, usize>,
    msgs: VecDeque<Msg>,
    /// The ground (nominal root) context `v_r`: the one context where Hyper
    /// may ground the central variable. Created lazily on the first r-Succ
    /// push or ground fact; None for ontologies without individuals.
    ground_ctx: Option<usize>,
    /// Pay-as-you-go expansion: one successor context per function symbol `f`,
    /// instead of a single shared empty-core context for every anonymous
    /// successor (the trivial strategy).  Successors generated by distinct
    /// existential skolems no longer pile into one context, which is what blows
    /// up under disjunction.  Sound and complete: the trivial strategy only
    /// tolerated mixing successors because conditional clause bodies prevent a
    /// consequence about one successor from being pushed back along another's
    /// edge; partitioning by `f` pushes exactly the same per-edge consequences.
    successor_ctxs: HashMap<Term, usize>,
    /// Central expansion strategy (default; KM_NO_CENTRAL restores the per-`f`
    /// empty-core pay-as-you-go strategy): successor contexts are keyed by their core
    /// = the σ-image of the predecessor's pushed trigger set for `f`.  Trigger
    /// atoms become *core* atoms (`-> p` by the Core rule) instead of
    /// conditional hypotheses (`p -> p`), so consequences that the empty-core
    /// strategy derives as clauses with ever-growing hypothesis conjunctions in
    /// the body (`Q1(x) ∧ ... ∧ Qk(x) -> D(x)`, the measured blow-up on
    /// disjunctive ontologies) collapse to unit clauses.  Predecessors with
    /// identical trigger sets share one successor context.  Strategy choice is
    /// within the calculus's soundness/completeness freedom (same rules, same
    /// ordering; only WHICH context a Succ message targets changes — cf. the
    /// trivial and pay-as-you-go strategies above); the Pred rule's
    /// `neighbour_core` back-substitution already conditions returned clauses
    /// on the successor's core, which is exactly the pushed trigger set.
    /// Kept separate from `core_index`: root contexts use the root ordering,
    /// so a successor core that happens to equal a root core must NOT be
    /// deduplicated into the root context.
    central_index: HashMap<Vec<Pred>, usize>,
    /// cached strategy flag: central (default) vs per-`f` pay-as-you-go (KM_NO_CENTRAL)
    central: bool,
    /// Context-independent closure: the worked-off clauses of an empty-core,
    /// non-root context saturated from the ontology facts + TBox alone (no Succ
    /// hypotheses, no incoming edges).  These consequences are entailed by the
    /// ontology and hold of *every* element, so they are valid in every
    /// successor context (all empty-core, non-root, same literal ordering).
    /// Computed once and seeded into each new successor context instead of
    /// re-deriving them per context — the measured cross-context duplication on
    /// disjunction/role-chain ontologies is 8-15x, almost all of it this shared
    /// TBox reasoning.  Sound + completeness-preserving (the seeded clauses are
    /// exactly those the context would re-derive), so the saturation fixpoint
    /// and output are unchanged; no Lean re-certification (a redundancy/sharing
    /// optimisation, not a calculus-rule change).
    /// (Arena ids in the non-root domain; seeding a context shares the arena
    /// entries instead of cloning the clauses.)
    shared_closure: Option<Vec<u32>>,
    /// Same idea as `shared_closure` but under the *root* literal ordering
    /// (`root=true`): the facts+TBox closure of an empty-core root context.
    /// Seeded into every query root context (core `{A(x)}`) so the shared TBox
    /// reasoning is computed once rather than per classified concept.  Root and
    /// non-root orderings differ (query concepts are mutually incomparable at a
    /// root), so the two closures are kept separate and never crossed.
    /// (Arena ids in the root domain.)
    shared_root_closure: Option<Vec<u32>>,
    equality: bool,
    /// Intern table for back-substituted pred clauses: one copy per distinct
    /// content, shared across all receiving contexts (`Context.neighbor_pred`
    /// stores ids).  The same clause shape recurs across thousands of contexts
    /// on role-chain ontologies, where the per-context copies dominated peak
    /// memory.  Append-only; ids are stable.
    pred_interned: Vec<PredClause>,
    /// content hash -> candidate ids (collisions resolved by exact comparison)
    pred_intern_idx: HashMap<u64, Vec<u32>>,
    /// Global content-interned clause arenas, one per ordering domain
    /// (`[non-root, root]` -- the same (body, head) has a different cached
    /// `max_head` under the root vs non-root literal ordering, so the domains
    /// are kept separate and never crossed).  Append-only; each distinct
    /// clause is stored once and contexts reference it by id, which collapses
    /// the per-context copies of the seeded shared closure and of clauses
    /// re-derived across contexts.
    cc_arena: [Vec<ContextClause>; 2],
    /// content hash -> candidate arena ids, per domain (exact-compare verified)
    cc_intern_idx: [HashMap<u64, Vec<u32>>; 2],
    pub dropped_unsupported: usize,
    /// Nom rule (arXiv:1805.01396 Table 3): `K`, where `K + 1` is the largest
    /// neighbour-variable index `i` (of `z_i`) over the whole ontology — the
    /// width of the additional-nominal disjunction `⋁_{i=1}^K y ≈ o'_{ρ·S^i}`.
    /// 0 when the ontology has at most one neighbour variable per clause (the
    /// Nom preconditions then cannot arise).
    nom_k: usize,
    /// Additional-nominal interner: (parent individual `o`, role `S`, edge
    /// orientation `S(o,y)` vs `S(y,o)`, index `1..=K`) → fresh individual id
    /// (the nominal label `ρ·S^i`).  Allocation order extends labels, so the
    /// id order satisfies the Def-3 label-monotonicity `o_ρ·σ > o_ρ`.
    /// Interior mutability: allocation happens inside the otherwise read-only
    /// Hyper resolvent build (single-threaded engine, never shared).
    nom_table: std::cell::RefCell<HashMap<(Term, Iri, bool, u16), Term>>,
    /// next fresh individual id (starts above every input individual)
    nom_next: std::cell::Cell<i32>,
    /// first additional-nominal id (= the initial `nom_next`): ids at or
    /// above this are Nom-introduced and exempt from the r-Pred
    /// announcement guard (no context can have announced them)
    nom_base: i32,
    /// Additional-nominal budget (`KM_NOM_BUDGET`, default 4096).  The Nom rule
    /// is the doubly-exponential source of the calculus; on exhaustion further
    /// Nom conclusions are dropped with an explicit warning (sound, possibly
    /// incomplete — never silent).
    nom_budget: usize,
    nom_truncated: std::cell::Cell<bool>,
    /// instrumentation counters (only read under KM_STATS)
    stat_propagate: u64,
    stat_pred_checks: u64,
    stat_succ_scans: u64,
    stat_saturate: u64,
}

impl Engine {
    pub fn new(sig: Sig, ont_clauses: Vec<OntologyClause>, dropped: usize) -> Engine {
        let mut sig = sig;
        let mut ont = Ontology::default();
        for c in ont_clauses {
            let idx = ont.clauses.len();
            if c.body.is_empty() {
                // Ground facts (heads mentioning an individual) seed the
                // ground context fully and other contexts on demand.
                let mut inds: Vec<Term> = Vec::new();
                for l in &c.head {
                    lit_inds(l, &mut inds);
                }
                if inds.is_empty() {
                    ont.facts.push(idx);
                } else {
                    for o in inds {
                        ont.ground_facts.entry(o).or_default().push(idx);
                    }
                }
            } else {
                // unsatisfiable predicate: single body pred, empty head
                if c.body.len() == 1 && c.head.is_empty() {
                    if let Pred::Concept { iri, .. } = c.body[0] {
                        if (iri as usize) < sig.nothing.len() {
                            sig.nothing[iri as usize] = true;
                        }
                    }
                }
                for b in &c.body {
                    match *b {
                        Pred::Concept { iri, t } => {
                            ont.concept_body_any.entry(iri).or_default().push(idx);
                            if is_central(t) {
                                sig.concept_succ_trigger[iri as usize] = true;
                                ont.concept_clauses.entry(iri).or_default().push(idx);
                            }
                        }
                        Pred::Role { iri, s, t } => {
                            ont.role_body_any.entry(iri).or_default().push(idx);
                            if is_central(s) {
                                sig.forward_role_succ_trigger[iri as usize] = true;
                                ont.forward_role_clauses.entry(iri).or_default().push(idx);
                            }
                            if is_central(t) {
                                sig.backward_role_succ_trigger[iri as usize] = true;
                                ont.backward_role_clauses.entry(iri).or_default().push(idx);
                            }
                        }
                    }
                }
            }
            ont.clauses.push(c);
        }
        // Nom-rule parameters: K + 1 = the largest z_i index over the ontology,
        // and fresh additional nominals are allocated above every input
        // individual id (so the term/label order extends allocation order).
        let mut max_z: i32 = 0;
        let mut max_ind: i32 = 0;
        {
            let mut see = |t: Term| {
                if is_neighbour(t) && t != Y {
                    max_z = max_z.max(-t - 1);
                } else if is_individual(t) {
                    max_ind = max_ind.max(t);
                } else if is_comp(t) {
                    max_ind = max_ind.max(comp_parts(t).1);
                }
            };
            for c in &ont.clauses {
                for p in &c.body {
                    match *p {
                        Pred::Concept { t, .. } => see(t),
                        Pred::Role { s, t, .. } => {
                            see(s);
                            see(t);
                        }
                    }
                }
                for l in &c.head {
                    match *l {
                        Lit::P(Pred::Concept { t, .. }) => see(t),
                        Lit::P(Pred::Role { s, t, .. }) => {
                            see(s);
                            see(t);
                        }
                        Lit::Eq { s, t } | Lit::Ineq { s, t } => {
                            see(s);
                            see(t);
                        }
                    }
                }
            }
        }
        let nom_budget = std::env::var("KM_NOM_BUDGET")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(4096);
        Engine {
            sig,
            ont,
            contexts: Vec::new(),
            core_index: HashMap::new(),
            ground_ctx: None,
            msgs: VecDeque::new(),
            successor_ctxs: HashMap::new(),
            central_index: HashMap::new(),
            central: std::env::var_os("KM_NO_CENTRAL").is_none(),
            shared_closure: None,
            shared_root_closure: None,
            equality: true,
            pred_interned: Vec::new(),
            pred_intern_idx: HashMap::new(),
            cc_arena: [Vec::new(), Vec::new()],
            cc_intern_idx: [HashMap::new(), HashMap::new()],
            dropped_unsupported: dropped,
            nom_k: (max_z - 1).max(0) as usize,
            nom_table: std::cell::RefCell::new(HashMap::new()),
            nom_next: std::cell::Cell::new(max_ind + 1),
            nom_base: max_ind + 1,
            nom_budget,
            nom_truncated: std::cell::Cell::new(false),
            stat_propagate: 0,
            stat_pred_checks: 0,
            stat_succ_scans: 0,
            stat_saturate: 0,
        }
    }

    /// Find the arena id of a clause with this exact (body, head) content in
    /// the given ordering domain, if it was ever interned.  The arena is
    /// content-unique, so at most one id matches.
    fn cc_find(&self, root: bool, c: &ContextClause) -> Option<u32> {
        let d = root as usize;
        let h = content_hash(&(&c.body, &c.head));
        self.cc_intern_idx[d].get(&h)?.iter().copied().find(|&i| {
            let a = &self.cc_arena[d][i as usize];
            a.body == c.body && a.head == c.head
        })
    }

    /// Intern a context clause in the given ordering domain, returning its
    /// stable arena id.
    fn intern_cc(&mut self, root: bool, c: ContextClause) -> u32 {
        if let Some(i) = self.cc_find(root, &c) {
            return i;
        }
        let d = root as usize;
        let h = content_hash(&(&c.body, &c.head));
        let id = self.cc_arena[d].len() as u32;
        self.cc_arena[d].push(c);
        self.cc_intern_idx[d].entry(h).or_default().push(id);
        id
    }

    /// Intern a back-substituted pred clause, returning its stable id.
    fn intern_pred(&mut self, pc: PredClause) -> u32 {
        let h = content_hash(&pc);
        if let Some(ids) = self.pred_intern_idx.get(&h) {
            for &i in ids {
                if self.pred_interned[i as usize] == pc {
                    return i;
                }
            }
        }
        let id = self.pred_interned.len() as u32;
        self.pred_interned.push(pc);
        self.pred_intern_idx.entry(h).or_default().push(id);
        id
    }

    fn get_or_create_context(
        &mut self,
        core: Vec<Pred>,
        root: bool,
        query: Option<Iri>,
    ) -> usize {
        if let Some(&id) = self.core_index.get(&core) {
            return id;
        }
        let id = self.contexts.len();
        let ctx = Context::new(id, core.clone(), root, query);
        self.contexts.push(ctx);
        self.core_index.insert(core, id);
        // Root contexts share the root-ordering facts+TBox closure: seed it and
        // add only the core rule (the facts live in the closure).  The empty-core
        // top context is itself the closure, so seeding it is a no-op-equivalent
        // (it adds no core clause and derives nothing further).
        if root && std::env::var_os("KM_NO_SHARE").is_none() {
            self.ensure_shared_root_closure();
            let closure = self.shared_root_closure.as_ref().unwrap().clone();
            for c in closure {
                self.seed_worked_off(id, c);
            }
            self.add_core(id);
        } else {
            self.init_context(id);
        }
        id
    }

    /// Compute the root-ordering facts+TBox closure once (see
    /// `shared_root_closure`).  A throwaway empty-core root context is saturated
    /// from facts+TBox alone and its worked-off snapshotted, then discarded.
    fn ensure_shared_root_closure(&mut self) {
        if self.shared_root_closure.is_some() {
            return;
        }
        let id = self.contexts.len();
        let ctx = Context::new(id, vec![], true, None);
        self.contexts.push(ctx);
        self.init_context(id);
        self.saturate(id);
        let closure = self.contexts[id].worked_off.clone();
        debug_assert_eq!(id, self.contexts.len() - 1);
        self.contexts.pop();
        self.shared_root_closure = Some(closure);
    }

    /// Core rule + facts for a freshly created context, then schedule saturation.
    fn init_context(&mut self, id: usize) {
        self.add_core(id);
        self.add_facts(id);
    }

    /// Core rule for context `id`: the empty clause if a core predicate is
    /// owl:Nothing, else one `-> p` clause per core predicate.
    fn add_core(&mut self, id: usize) {
        let root = self.contexts[id].root;
        let core = self.contexts[id].core.clone();
        if core.iter().any(|p| self.sig.is_nothing_pred(p)) {
            let c = ContextClause::new(vec![], vec![], root, &self.sig);
            self.add_clause(id, c);
        } else {
            for p in core {
                let c = ContextClause::new(vec![], vec![Lit::P(p)], root, &self.sig);
                self.add_clause(id, c);
            }
        }
    }

    /// Ontology facts (empty-body clauses) seeded into context `id`.  These are
    /// part of every context-independent closure, so a context seeded from a
    /// shared closure must NOT also call this (the facts are already present).
    fn add_facts(&mut self, id: usize) {
        let facts: Vec<usize> = self.ont.facts.clone();
        for fi in facts {
            self.seed_fact(id, fi);
        }
    }

    /// Seed one ontology fact (empty-body clause `fi`) into context `id`.
    fn seed_fact(&mut self, id: usize, fi: usize) {
        let root = self.contexts[id].root;
        let head = self.ont.clauses[fi].head.clone();
        // apply identity (facts have no neighbour vars); filter invalid eqs / nothing
        let head = self.filter_head(head);
        if let Some(head) = head {
            let c = ContextClause::new(vec![], head, root, &self.sig);
            self.add_clause(id, c);
        }
    }

    /// The ground (nominal root) context `v_r`, created on first use: empty
    /// core, fully pre-seeded with every ground ontology fact, and the only
    /// context where Hyper grounds the central variable.
    fn ground_context(&mut self) -> usize {
        if let Some(id) = self.ground_ctx {
            return id;
        }
        let id = self.contexts.len();
        let ctx = Context::new(id, vec![], false, None);
        self.contexts.push(ctx);
        self.ground_ctx = Some(id);
        let inds: Vec<Term> = self.ont.ground_facts.keys().copied().collect();
        self.contexts[id].seeded_inds.extend(inds);
        self.init_context(id);
        let mut fis: Vec<usize> = self.ont.ground_facts.values().flatten().copied().collect();
        fis.sort_unstable();
        fis.dedup();
        for fi in fis {
            self.seed_fact(id, fi);
        }
        self.saturate(id);
        id
    }

    /// Filter a head literal vector: apply the Ineq rule (drop `t != t`),
    /// drop valid equations `t == t` (makes clause a tautology -> None), and
    /// drop owl:Nothing predicates.  Returns None if the clause is tautological.
    fn filter_head(&self, head: Vec<Lit>) -> Option<Vec<Lit>> {
        let mut out = Vec::new();
        for l in head {
            if l.is_valid_equation() {
                return None; // s == s in head -> tautology
            }
            if l.is_invalid_equation() {
                continue; // Ineq rule: drop t != t
            }
            if let Lit::P(p) = l {
                if self.sig.is_nothing_pred(&p) {
                    continue;
                }
            }
            out.push(l);
        }
        Some(out)
    }

    /// Redundancy-aware clause addition (Elim): skip if subsumed; remove clauses
    /// it subsumes; enqueue to todo.  Returns true if added.
    fn add_clause(&mut self, id: usize, clause: ContextClause) -> bool {
        if clause.is_head_tautology() {
            return false;
        }
        let root = self.contexts[id].root;
        let d = root as usize;
        // Exact-duplicate check: the arena id is the canonical content key.
        let existing = self.cc_find(root, &clause);
        if let Some(cid) = existing {
            if self.contexts[id].clause_keys.contains(&cid) {
                return false;
            }
        }
        let (nb, nh) = (clause.body.len(), clause.head.len());
        let ctx = &self.contexts[id];
        let arena = &self.cc_arena[d];
        // Forward subsumption: skip if some existing clause subsumes `clause`.
        if ctx.fwd_subsumed(arena, &clause, nb, nh) {
            return false;
        }
        // Back-subsumption: drop existing clauses that `clause` strengthens.
        {
            let arena = &self.cc_arena[d];
            let ctx = &mut self.contexts[id];
            ctx.back_subsume(arena, &clause, nb, nh);
        }
        // Demand-driven ground-fact seeding (nominal mode): the first clause
        // mentioning an individual brings that individual's ground ontology
        // facts into this context (they are Hyper/Eq providers here). The
        // ground context is fully pre-seeded at creation.
        let mut new_inds: Vec<Term> = Vec::new();
        if !self.ont.ground_facts.is_empty() {
            let mut inds: Vec<Term> = Vec::new();
            for p in &clause.body {
                pred_inds(p, &mut inds);
            }
            for l in &clause.head {
                lit_inds(l, &mut inds);
            }
            let ctx = &mut self.contexts[id];
            for o in inds {
                if ctx.seeded_inds.insert(o) {
                    new_inds.push(o);
                }
            }
        }
        let cid = match existing {
            Some(c) => c,
            None => self.intern_cc(root, clause),
        };
        let ctx = &mut self.contexts[id];
        ctx.clause_keys.insert(cid);
        ctx.todo.push_back(cid);
        for o in new_inds {
            if let Some(fis) = self.ont.ground_facts.get(&o) {
                for fi in fis.clone() {
                    self.seed_fact(id, fi);
                }
            }
        }
        true
    }

    /// Saturate a single context (apply Hyper/Pred/Eq until todo is empty).
    fn saturate(&mut self, id: usize) {
        self.stat_saturate += 1;
        let trace_sat = std::env::var("KM_SAT").is_ok();
        let prof = std::env::var("KM_PROF").is_ok();
        let (mut iters, mut subsumed, mut nhyper, mut npred, mut neqp, mut neqe, mut nfact, mut nadded) =
            (0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64);
        let d = self.contexts[id].root as usize;
        loop {
            let cid = match self.contexts[id].todo.pop_front() {
                Some(c) => c,
                None => break,
            };
            // Transient working copy (the arena entry is shared across contexts
            // and rule code needs it while `self` is mutated).
            let clause = self.cc_arena[d][cid as usize].clone();
            if prof {
                iters += 1;
                if iters % 200_000 == 0 {
                    let ctx = &self.contexts[id];
                    eprintln!(
                        "KM_PROF ctx={} iters={} subsumed_at_workoff={} added={} todo={} wo={} | hyper_out={} pred_out={} eq_pred_out={} eq_eqn_out={} factor_out={}",
                        id, iters, subsumed, nadded, ctx.todo.len(), ctx.worked_off.len(),
                        nhyper, npred, neqp, neqe, nfact
                    );
                }
            }
            // Re-check forward subsumption at work-off time: a clause that was
            // not subsumed when enqueued may since have been subsumed by a
            // newly worked-off clause (back_subsume only scans worked_off, not
            // todo).  Skipping it here -- before it fires its rules -- prevents a
            // redundant clause from spawning a cascade of further redundant
            // consequences.  Sound (a subsumed clause is entailed by its
            // subsumer, so dropping it preserves completeness).
            {
                let ctx = &self.contexts[id];
                let arena = &self.cc_arena[d];
                let (nb, nh) = (clause.body.len(), clause.head.len());
                if ctx.fwd_subsumed(arena, &clause, nb, nh) {
                    self.contexts[id].clause_keys.remove(&cid);
                    if prof { subsumed += 1; }
                    continue;
                }
            }
            let root = self.contexts[id].root;
            // Fire rules per maximal head literal.
            let max_head: Vec<Lit> = clause.max_head().collect();
            for max in &max_head {
                match max {
                    Lit::P(p) => {
                        // Hyper fires on every maximal head predicate; the
                        // candidate ontology clauses are those with a body atom
                        // (central or neighbour) that can unify with `p`.
                        let results = self.hyper(id, &clause, *p, root);
                        if prof { nhyper += results.len() as u64; }
                        for r in results {
                            if self.add_clause(id, r) && prof { nadded += 1; }
                        }
                        if is_function(p.max_term()) {
                            let results = self.pred_local(id, &clause, *p, root);
                            if prof { npred += results.len() as u64; }
                            for r in results {
                                if self.add_clause(id, r) && prof { nadded += 1; }
                            }
                            if self.equality {
                                let results = self.eq_from_pred(id, &clause, *max, root);
                                if prof { neqp += results.len() as u64; }
                                for r in results {
                                    if self.add_clause(id, r) && prof { nadded += 1; }
                                }
                            }
                        } else if p.is_ground() {
                            // Join via the Pred pipeline (nominal calculus): a
                            // ground maximal head atom resolves the verbatim-
                            // copied ground body atoms (C_i) of neighbour pred
                            // clauses, which the function-term refire above
                            // never revisits.
                            let results = self.pred_local(id, &clause, *p, root);
                            if prof { npred += results.len() as u64; }
                            for r in results {
                                if self.add_clause(id, r) && prof { nadded += 1; }
                            }
                            if self.equality {
                                let results = self.eq_from_pred(id, &clause, *max, root);
                                if prof { neqp += results.len() as u64; }
                                for r in results {
                                    if self.add_clause(id, r) && prof { nadded += 1; }
                                }
                            }
                        }
                    }
                    Lit::Eq { .. } if self.equality => {
                        // This equality is the paramodulation source: rewrite
                        // matching literals of worked-off clauses.
                        let results = self.eq_from_equation(id, &clause, *max, root);
                        if prof { neqe += results.len() as u64; }
                        for r in results {
                            if self.add_clause(id, r) && prof { nadded += 1; }
                        }
                    }
                    Lit::Ineq { .. } if self.equality => {
                        // This inequality is a paramodulation target: rewrite it
                        // with worked-off equalities (the reverse direction, so
                        // the equality/inequality clash is found regardless of
                        // derivation order).
                        let results = self.eq_from_pred(id, &clause, *max, root);
                        if prof { neqp += results.len() as u64; }
                        for r in results {
                            if self.add_clause(id, r) && prof { nadded += 1; }
                        }
                    }
                    _ => {}
                }
            }
            // Factor rule: applies to clauses with two head equalities sharing a side.
            if self.equality && clause.head.iter().filter(|l| matches!(l, Lit::Eq { .. })).count() >= 2 {
                let results = self.factor(&clause, root);
                if prof { nfact += results.len() as u64; }
                for r in results {
                    if self.add_clause(id, r) && prof { nadded += 1; }
                }
            }
            // Join rule (nominal calculus): in-context resolution on ground
            // atoms; no-op (empty indexes) without individuals.
            {
                let results = self.join(id, &clause, root);
                for r in results {
                    if self.add_clause(id, r) && prof { nadded += 1; }
                }
            }
            // Feed the semi-naive propagation pools (append-only).  Pred-eligible:
            // function-free head of predicates plus (nominal mode) the Pr
            // equality forms `x ≈ o` / `y ≈ o` / `o ≈ o'` (canonical
            // `Eq{o, ·}` — individuals sit above x and y in the term order);
            // other equalities stay local, as before.  Succ-eligible: some
            // maximal head predicate is on a function term (succ-trigger
            // candidate) or is an Su^r ground form (r-Succ candidate).
            let pred_eligible = clause.head.iter().all(|l| {
                l.is_function_free()
                    && match l {
                        Lit::P(_) => true,
                        Lit::Eq { s, t } => {
                            is_individual(*s)
                                && (*t == X || *t == Y || is_individual(*t))
                        }
                        Lit::Ineq { .. } => false,
                    }
            });
            let succ_eligible = clause
                .max_head_predicates()
                .any(|(p, _)| is_function(p.max_term()) || root_succ_form(&p).is_some());
            {
                let arena = &self.cc_arena[d];
                let ctx = &mut self.contexts[id];
                if pred_eligible {
                    ctx.pred_pool.push(cid);
                }
                if succ_eligible {
                    ctx.succ_pool.push(cid);
                }
                ctx.worked_off.push(cid);
                ctx.index_clause(arena, cid);
                ctx.dirty = true;
            }
            if trace_sat {
                let c = &self.contexts[id];
                let arena = &self.cc_arena[d];
                let wl = c.worked_off.len();
                if wl % 10000 == 0 {
                    let maxb = c.worked_off.iter().map(|&ci| arena[ci as usize].body.len()).max().unwrap_or(0);
                    let maxh = c.worked_off.iter().map(|&ci| arena[ci as usize].head.len()).max().unwrap_or(0);
                    let nctx = self.contexts.len();
                    eprintln!(
                        "KM_SAT ctx={} root={} core_len={} todo={} wo={} max_body={} max_head={} ncontexts={} hyper={}",
                        id, c.root, c.core.len(), c.todo.len(), wl,
                        maxb, maxh, nctx, HYPER_CALLS.with(|x| x.get())
                    );
                }
            }
        }
    }

    /// Hyper rule.  `side` is the just-popped clause; `max` one of its maximal
    /// head predicates.
    fn hyper(&self, id: usize, side: &ContextClause, max: Pred, root: bool) -> Vec<ContextClause> {
        HYPER_CALLS.with(|c| c.set(c.get() + 1));
        let mut out = Vec::new();
        let ctx = &self.contexts[id];
        let arena = &self.cc_arena[root as usize];
        for oci in self.ont.clauses_cand(&max) {
            let oc = &self.ont.clauses[oci];
            let n = oc.body.len();
            // pick the first body position that can unify with `max` for the side condition
            let side_pos = match (0..n).find(|&i| can_unify(&oc.body[i], &max)) {
                Some(p) => p,
                None => continue,
            };
            // candidate (matched max-head-predicate) lists per body position
            let mut candidates: Vec<Vec<(usize, Pred)>> = Vec::with_capacity(n);
            let mut ok = true;
            for i in 0..n {
                if i == side_pos {
                    // side condition: its max-head-preds unifiable with body[i]
                    let mut v = Vec::new();
                    for (p, _) in side.max_head_predicates() {
                        if can_unify(&oc.body[i], &p) {
                            v.push((usize::MAX, p)); // usize::MAX marks the side clause
                        }
                    }
                    if v.is_empty() {
                        ok = false;
                        break;
                    }
                    candidates.push(v);
                } else {
                    let mut v = Vec::new();
                    let cand = match oc.body[i] {
                        Pred::Concept { iri, .. } => ctx.head_concept_index.get(&iri),
                        Pred::Role { iri, .. } => ctx.head_role_index.get(&iri),
                    };
                    if let Some(cand) = cand {
                        for &ci in cand {
                            for (p, _) in arena[ci as usize].max_head_predicates() {
                                if can_unify(&oc.body[i], &p) {
                                    v.push((ci as usize, p));
                                }
                            }
                        }
                    }
                    // Ground context: the side clause is also a candidate at
                    // non-side positions (given-clause semantics, S_v ∪ {C}).
                    // Elsewhere this self-pairing is provably redundant — two
                    // distinct max heads yield a resolvent the side clause
                    // subsumes, the same head twice instantiates a head
                    // equality to a tautology — but in the ground context the
                    // same-head pair `S(o,y), S(o,y)` instantiates `z_i ≈ z_j`
                    // to `y ≈ y`, the Nom-rule trigger, which must fire.
                    if self.ground_ctx == Some(id) {
                        for (p, _) in side.max_head_predicates() {
                            if can_unify(&oc.body[i], &p) {
                                v.push((usize::MAX, p));
                            }
                        }
                    }
                    if v.is_empty() {
                        ok = false;
                        break;
                    }
                    candidates.push(v);
                }
            }
            if !ok {
                continue;
            }
            // Enumerate the unifiable combinations by a backtracking *join* rather
            // than the full cartesian product: extend the central substitution one
            // body position at a time, and at each position only descend into the
            // candidates whose match is consistent with the bindings already made
            // (shared neighbour variables, e.g. `y` in `R(x,y) ∧ C(y)`).  This
            // yields exactly the same set of resolvents as iterating the product
            // and filtering by `unify` -- the failed combinations were precisely
            // those skipped here -- but never materialises the doomed branches,
            // which on number restrictions (`R(x,y1) ∧ C(y1) ∧ R(x,y2) ∧ C(y2)`)
            // is the difference between `(#successors)^k` and the number of
            // genuinely unifiable tuples.  Positions are visited fewest-candidates
            // first so the most constraining atoms bind earliest.
            let mut order: Vec<usize> = (0..n).collect();
            order.sort_by_key(|&i| candidates[i].len());
            let mut chosen = vec![0usize; n];
            let sigma = CentralSubst::new(self.ground_ctx == Some(id));
            // side-position variables are exempt from symmetric-group pruning
            let exempt: Vec<Term> = if oc.sym_groups.is_empty() {
                Vec::new()
            } else {
                match oc.body[side_pos] {
                    Pred::Concept { t, .. } => vec![t],
                    Pred::Role { s, t, .. } => vec![s, t],
                }
            };
            self.hyper_join(id, side, oc, &candidates, &order, 0, &sigma, &exempt, &mut chosen, root, &mut out);
        }
        out
    }

    /// Recursive backtracking enumeration helper for `hyper` (see its comment).
    /// `order[depth]` is the body position bound at this level; `chosen[pos]` is
    /// the index into `candidates[pos]` selected for the resolvent build.
    #[allow(clippy::too_many_arguments)]
    fn hyper_join(
        &self,
        id: usize,
        side: &ContextClause,
        oc: &OntologyClause,
        candidates: &[Vec<(usize, Pred)>],
        order: &[usize],
        depth: usize,
        sigma: &CentralSubst,
        exempt: &[Term],
        chosen: &mut Vec<usize>,
        root: bool,
        out: &mut Vec<ContextClause>,
    ) {
        if depth == order.len() {
            if let Some(c) = self.build_hyper_resolvent(id, side, oc, sigma, candidates, chosen, root) {
                out.push(c);
            }
            return;
        }
        let pos = order[depth];
        for (j, &(_ci, p)) in candidates[pos].iter().enumerate() {
            let mut s2 = sigma.clone();
            if unify(&mut s2, &oc.body[pos], &p)
                && (oc.sym_groups.is_empty() || sym_groups_ok(oc, exempt, &s2))
            {
                chosen[pos] = j;
                self.hyper_join(id, side, oc, candidates, order, depth + 1, &s2, exempt, chosen, root, out);
            }
        }
    }

    /// The additional nominal `o'_{ρ·S^k}` for parent individual `o` (label ρ),
    /// role `S`, edge orientation `fwd` (`S(o,y)` vs `S(y,o)`), and index `k`
    /// (Nom rule).  Interned: re-firing Nom with the same parameters reuses the
    /// same individual.  `None` when the budget (or the individual id range) is
    /// exhausted — reported once, never silent.
    fn nom_term(&self, o: Term, role: Iri, fwd: bool, k: u16) -> Option<Term> {
        let key = (o, role, fwd, k);
        if let Some(&t) = self.nom_table.borrow().get(&key) {
            return Some(t);
        }
        let next = self.nom_next.get();
        if self.nom_table.borrow().len() >= self.nom_budget || next >= FTERM_BASE {
            if !self.nom_truncated.replace(true) {
                eprintln!(
                    "WARNING: kobayashi-marust additional-nominal budget ({}) exhausted; \
                     further Nom conclusions dropped — classification may be incomplete.",
                    self.nom_budget
                );
            }
            return None;
        }
        self.nom_next.set(next + 1);
        let t = ind_term(next);
        self.nom_table.borrow_mut().insert(key, t);
        Some(t)
    }

    #[allow(clippy::too_many_arguments)]
    fn build_hyper_resolvent(
        &self,
        id: usize,
        side: &ContextClause,
        oc: &OntologyClause,
        sigma: &CentralSubst,
        candidates: &[Vec<(usize, Pred)>],
        idxs: &[usize],
        root: bool,
    ) -> Option<ContextClause> {
        // Nom rule (arXiv:1805.01396 Table 3): in the ground context with
        // σ(x) = o, head a-equalities instantiating to `y ≈ y` or `y ≈ f(o')`
        // constrain the *unnamed predecessors* of o (the premise clauses come
        // from different r-Succ senders).  Dropping `y ≈ y` as a tautology —
        // the pre-nominal behaviour — loses exactly that constraint; instead
        // the whole group is replaced by `⋁_{k=1}^K y ≈ o'_{ρ·S^k}` over fresh
        // additional nominals, where S is the role of a matched `S(o,y)` /
        // `S(y,o)` premise atom.  Only fires when nominals, inverse roles and
        // number restrictions interact; inert otherwise.
        let ground_o = if self.ground_ctx == Some(id) {
            sigma.get(X).filter(|t| is_individual(*t))
        } else {
            None
        };
        let subst = |t: Term| sigma.apply(t);
        // head: ontology head substituted, filtered
        let mut head: Vec<Lit> = Vec::new();
        let mut nom_pending = false;
        // Distinct `f(o')` right-hand terms among the replaced `y ≈ f(o')`
        // literals (K''): an anonymous predecessor may be pinned to any of
        // those values, and each needs its own additional nominal to cover
        // it.  The Table-3 statement uses K disjuncts and its soundness proof
        // K' = max(K, K''); the bound with a direct pigeonhole proof (any
        // n_y distinct candidates outside the pinned values violate the
        // counting clause, so |candidates| ≤ (n_y − 1) + K'' ≤ K + K'') is
        // the SUM, which is what the Lean certification proves — so the
        // engine emits K + K'' disjuncts (weaker conclusions are sound).
        let mut nom_rhs: Vec<Term> = Vec::new();
        for l in &oc.head {
            let ls = l.apply(&subst);
            if ground_o.is_some() {
                if let Lit::Eq { s, t } = ls {
                    if (s == Y && t == Y) || (is_comp(s) && t == Y) {
                        nom_pending = true;
                        if is_comp(s) && !nom_rhs.contains(&s) {
                            nom_rhs.push(s);
                        }
                        continue;
                    }
                }
            }
            if ls.is_valid_equation() {
                return None;
            }
            if ls.is_invalid_equation() {
                continue;
            }
            if let Lit::P(p) = ls {
                if self.sig.is_nothing_pred(&p) {
                    continue;
                }
            }
            head.push(ls);
        }
        if nom_pending {
            let o = ground_o.unwrap();
            let k_eff = self.nom_k + nom_rhs.len();
            // The matched premise atom S(o,y) / S(y,o) supplies the role label.
            let mut labelled = false;
            'outer: for i in 0..candidates.len() {
                let (_, matched) = candidates[i][idxs[i]];
                if let Pred::Role { iri, s, t } = matched {
                    let fwd = s == o && t == Y;
                    let bwd = t == o && s == Y;
                    if fwd || bwd {
                        for k in 1..=k_eff as u16 {
                            head.push(Lit::eq(Y, self.nom_term(o, iri, fwd, k)?));
                        }
                        labelled = true;
                        break 'outer;
                    }
                }
            }
            if !labelled {
                // No connecting role premise: the y-equality cannot be
                // expressed against additional nominals; the conclusion
                // degenerates to the pre-nominal tautology drop.
                return None;
            }
        }
        // plus each candidate clause's head minus the matched predicate
        let arena = &self.cc_arena[root as usize];
        let mut body: Vec<Pred> = Vec::new();
        for i in 0..candidates.len() {
            let (ci, matched) = candidates[i][idxs[i]];
            let clause = if ci == usize::MAX { side } else { &arena[ci] };
            for l in &clause.head {
                if *l != Lit::P(matched) {
                    head.push(*l);
                }
            }
            body.extend_from_slice(&clause.body);
        }
        Some(ContextClause::new(body, head, root, &self.sig))
    }

    /// Local Pred rule: resolve pred clauses (pushed from successors) whose body
    /// predicates are maximal in the head of clauses with the function term.
    /// Here `max` is a head predicate of `side` containing a function term; we
    /// resolve any neighbour pred clause whose body contains `max`.
    fn pred_local(&self, id: usize, side: &ContextClause, max: Pred, root: bool) -> Vec<ContextClause> {
        let mut out = Vec::new();
        let ctx = &self.contexts[id];
        let arena = &self.cc_arena[root as usize];
        for &pid in &ctx.neighbor_pred {
            let pc = &self.pred_interned[pid as usize];
            if !pc.body.iter().any(|b| *b == max) {
                continue;
            }
            // For each nonground body predicate, candidate clauses with that
            // predicate maximal in head; `max` is provided by `side`. Ground
            // body atoms (nominal mode) are copied to the resolvent body.
            let mut ground: Vec<Pred> = Vec::new();
            let mut candidates: Vec<Vec<(usize, Pred)>> = Vec::with_capacity(pc.body.len());
            let mut ok = true;
            for &bp in &pc.body {
                let mut v = Vec::new();
                if bp == max {
                    v.push((usize::MAX, bp));
                }
                let cand = match bp {
                    Pred::Concept { iri, .. } => ctx.head_concept_index.get(&iri),
                    Pred::Role { iri, .. } => ctx.head_role_index.get(&iri),
                };
                if let Some(cand) = cand {
                    for &ci in cand {
                        if arena[ci as usize].max_head_predicates().any(|(p, _)| p == bp) {
                            v.push((ci as usize, bp));
                        }
                    }
                }
                if v.is_empty() {
                    if bp.is_ground() {
                        ground.push(bp);
                        continue;
                    }
                    ok = false;
                    break;
                }
                candidates.push(v);
            }
            if !ok {
                continue;
            }
            let n = candidates.len();
            let mut idxs = vec![0usize; n];
            loop {
                if let Some(c) =
                    self.build_pred_resolvent(id, side, pc, &ground, &candidates, &idxs, root)
                {
                    out.push(c);
                }
                let mut k = 0;
                loop {
                    if k == n {
                        idxs[0] = usize::MAX;
                        break;
                    }
                    idxs[k] += 1;
                    if idxs[k] < candidates[k].len() {
                        break;
                    }
                    idxs[k] = 0;
                    k += 1;
                }
                if n == 0 || idxs[0] == usize::MAX {
                    break;
                }
            }
        }
        out
    }

    fn build_pred_resolvent(
        &self,
        id: usize,
        side: &ContextClause,
        pc: &PredClause,
        ground: &[Pred],
        candidates: &[Vec<(usize, Pred)>],
        idxs: &[usize],
        root: bool,
    ) -> Option<ContextClause> {
        let _ = id;
        let arena = &self.cc_arena[root as usize];
        let mut head: Vec<Lit> = pc.head.clone();
        let mut body: Vec<Pred> = ground.to_vec();
        for i in 0..candidates.len() {
            let (ci, matched) = candidates[i][idxs[i]];
            let clause = if ci == usize::MAX { side } else { &arena[ci] };
            for l in &clause.head {
                if *l != Lit::P(matched) {
                    head.push(*l);
                }
            }
            body.extend_from_slice(&clause.body);
        }
        let head = self.filter_head(head)?;
        Some(ContextClause::new(body, head, root, &self.sig))
    }

    /// Join cases 1+2 conclusion: resolve the ground body atom `a` of
    /// `consumer` against `provider` (which has `a` maximal in its head):
    /// `Γ ∧ Γ' → Δ ∨ Δ' ∨ Δ''`.
    fn join_resolvent(
        &self,
        consumer: &ContextClause,
        a: Pred,
        provider: &ContextClause,
        root: bool,
    ) -> Option<ContextClause> {
        let body: Vec<Pred> = consumer
            .body
            .iter()
            .filter(|p| **p != a)
            .chain(provider.body.iter())
            .copied()
            .collect();
        let mut head: Vec<Lit> = consumer.head.clone();
        for l in &provider.head {
            if *l != Lit::P(a) {
                head.push(*l);
            }
        }
        let head = self.filter_head(head)?;
        let c = ContextClause::new(body, head, root, &self.sig);
        if c.is_head_tautology() {
            return None;
        }
        Some(c)
    }

    /// Join case 3 conclusion: discharge the ground body atom `a = A'{x↦o}` of
    /// `consumer` via the body-empty `provider` (`⊤ → Δ' ∨ A'`) and the
    /// body-empty `bridge` (`⊤ → Δ'' ∨ x ≈ o`): `Γ → Δ ∨ Δ' ∨ Δ''`.
    fn join_resolvent3(
        &self,
        consumer: &ContextClause,
        a: Pred,
        provider: &ContextClause,
        aprime: Pred,
        bridge: &ContextClause,
        o: Term,
        root: bool,
    ) -> Option<ContextClause> {
        let body: Vec<Pred> = consumer.body.iter().filter(|p| **p != a).copied().collect();
        let mut head: Vec<Lit> = consumer.head.clone();
        for l in &provider.head {
            if *l != Lit::P(aprime) {
                head.push(*l);
            }
        }
        let bl = Lit::Eq { s: o, t: X };
        for l in &bridge.head {
            if *l != bl {
                head.push(*l);
            }
        }
        let head = self.filter_head(head)?;
        let c = ContextClause::new(body, head, root, &self.sig);
        if c.is_head_tautology() {
            return None;
        }
        Some(c)
    }

    /// Join case 3 firings for one ground body atom `a` of `consumer`: each
    /// way of writing `a = A'{x↦o}` (with `A'` a plain x-form, no composite
    /// terms) is tried against the indexed bridges `⊤ → Δ'' ∨ x ≈ o` and the
    /// body-empty providers with `A'` maximal.
    fn join_case3_for(
        &self,
        ctx: &Context,
        arena: &[ContextClause],
        consumer: &ContextClause,
        a: Pred,
        root: bool,
        out: &mut Vec<ContextClause>,
    ) {
        let mut variants: Vec<(Pred, Term)> = Vec::new();
        match a {
            Pred::Concept { iri, t } if is_individual(t) => {
                variants.push((Pred::Concept { iri, t: X }, t));
            }
            Pred::Role { iri, s, t } if is_individual(s) && is_individual(t) => {
                variants.push((Pred::Role { iri, s: X, t }, s));
                variants.push((Pred::Role { iri, s, t: X }, t));
                if s == t {
                    variants.push((Pred::Role { iri, s: X, t: X }, s));
                }
            }
            _ => {}
        }
        for (aprime, o) in variants {
            let bridges = match ctx.bridge_index.get(&o) {
                Some(b) => b,
                None => continue,
            };
            let cands = match aprime {
                Pred::Concept { iri, .. } => ctx.head_concept_index.get(&iri),
                Pred::Role { iri, .. } => ctx.head_role_index.get(&iri),
            };
            let cands = match cands {
                Some(c) => c,
                None => continue,
            };
            for &pi in cands {
                let pcl = &arena[pi as usize];
                if !pcl.body.is_empty() {
                    continue; // Γ' = ⊤ required
                }
                if !pcl.max_head_predicates().any(|(p, _)| p == aprime) {
                    continue;
                }
                for &bi in bridges {
                    if bi == pi {
                        continue;
                    }
                    let bcl = &arena[bi as usize];
                    if let Some(r) =
                        self.join_resolvent3(consumer, a, pcl, aprime, bcl, o, root)
                    {
                        out.push(r);
                    }
                }
            }
        }
    }

    /// Join rule (arXiv:1805.01396 Table 3): in-context resolution on a ground
    /// atom.  Cases 1+2 resolve a clause `A ∧ Γ → Δ` (ground body atom `A`,
    /// arising from the verbatim-copied `C_i` of Pred/r-Pred) against a clause
    /// with `A` maximal in its head; case 3 discharges `A = A'{x↦o}` via a
    /// provider over `x` and an `x ≈ o` bridge.  Fired at work-off from every
    /// arrival order (consumer, provider, or bridge last).  Inert without
    /// individuals: all the indexes involved are then empty.
    fn join(&self, id: usize, side: &ContextClause, root: bool) -> Vec<ContextClause> {
        let mut out = Vec::new();
        let ctx = &self.contexts[id];
        if ctx.ground_body_index.is_empty() && ctx.bridge_index.is_empty() {
            return out;
        }
        let arena = &self.cc_arena[root as usize];
        // (a) `side` as provider: a maximal ground head atom resolves the
        // ground body atom of every indexed consumer.
        for (p, _) in side.max_head_predicates() {
            if p.is_ground() {
                if let Some(consumers) = ctx.ground_body_index.get(&p) {
                    for &ci in consumers {
                        if let Some(r) = self.join_resolvent(&arena[ci as usize], p, side, root) {
                            out.push(r);
                        }
                    }
                }
            }
        }
        // (b) `side` as consumer: each ground body atom resolves against
        // worked-off providers with that atom maximal, or via case 3.
        for &a in side.body.iter().filter(|p| p.is_ground()) {
            let cands = match a {
                Pred::Concept { iri, .. } => ctx.head_concept_index.get(&iri),
                Pred::Role { iri, .. } => ctx.head_role_index.get(&iri),
            };
            if let Some(cands) = cands {
                for &ci in cands {
                    let c = &arena[ci as usize];
                    if c.max_head_predicates().any(|(p, _)| p == a) {
                        if let Some(r) = self.join_resolvent(side, a, c, root) {
                            out.push(r);
                        }
                    }
                }
            }
            self.join_case3_for(ctx, arena, side, a, root, &mut out);
        }
        // (c) `side` as a late-arriving case-3 bridge or provider.
        if side.body.is_empty() {
            for l in side.max_head() {
                match l {
                    Lit::Eq { s, t } if is_individual(s) && t == X => {
                        // bridge arrival: complete triples over individual s
                        let o = s;
                        for (atom, consumers) in &ctx.ground_body_index {
                            let mut inds: Vec<Term> = Vec::new();
                            pred_inds(atom, &mut inds);
                            if !inds.contains(&o) {
                                continue;
                            }
                            for &ci in consumers {
                                let consumer = &arena[ci as usize];
                                // re-run case 3 for this consumer/atom against
                                // all bridges (now including `side`, which is
                                // not yet indexed): inline the variant loop
                                // with `side` as the bridge.
                                let mut variants: Vec<(Pred, Term)> = Vec::new();
                                match *atom {
                                    Pred::Concept { iri, t } if t == o => {
                                        variants.push((Pred::Concept { iri, t: X }, o));
                                    }
                                    Pred::Role { iri, s: rs, t: rt }
                                        if is_individual(rs) && is_individual(rt) =>
                                    {
                                        if rs == o {
                                            variants.push((Pred::Role { iri, s: X, t: rt }, o));
                                        }
                                        if rt == o {
                                            variants.push((Pred::Role { iri, s: rs, t: X }, o));
                                        }
                                        if rs == o && rt == o {
                                            variants.push((Pred::Role { iri, s: X, t: X }, o));
                                        }
                                    }
                                    _ => {}
                                }
                                for (aprime, _) in variants {
                                    let pcands = match aprime {
                                        Pred::Concept { iri, .. } => {
                                            ctx.head_concept_index.get(&iri)
                                        }
                                        Pred::Role { iri, .. } => ctx.head_role_index.get(&iri),
                                    };
                                    if let Some(pcands) = pcands {
                                        for &pi in pcands {
                                            let pcl = &arena[pi as usize];
                                            if !pcl.body.is_empty()
                                                || !pcl
                                                    .max_head_predicates()
                                                    .any(|(p, _)| p == aprime)
                                            {
                                                continue;
                                            }
                                            if let Some(r) = self.join_resolvent3(
                                                consumer, *atom, pcl, aprime, side, o, root,
                                            ) {
                                                out.push(r);
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                    Lit::P(p) if !p.is_ground() && p.is_function_free() => {
                        // provider arrival: for each indexed bridge individual
                        // o, `p{x↦o}` may be a consumer's ground body atom.
                        let mentions_x = match p {
                            Pred::Concept { t, .. } => t == X,
                            Pred::Role { s, t, .. } => s == X || t == X,
                        };
                        if !mentions_x {
                            continue;
                        }
                        let bridge_os: Vec<Term> = ctx.bridge_index.keys().copied().collect();
                        for o in bridge_os {
                            let a = p.apply(&|t| if t == X { o } else { t });
                            if !a.is_ground() {
                                continue;
                            }
                            let consumers = match ctx.ground_body_index.get(&a) {
                                Some(c) => c,
                                None => continue,
                            };
                            for &bi in &ctx.bridge_index[&o] {
                                let bcl = &arena[bi as usize];
                                for &ci in consumers {
                                    let consumer = &arena[ci as usize];
                                    if let Some(r) = self
                                        .join_resolvent3(consumer, a, side, p, bcl, o, root)
                                    {
                                        out.push(r);
                                    }
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
        out
    }

    /// Factor rule (Table 2): from a clause whose head contains two equalities
    /// `s ≈ t` and `s ≈ t'` with the same maximal side `s`, derive the clause
    /// with `s ≈ t` replaced by `t ≉ t'`.  Sound: if `s = t` and `s ≠ t'` then
    /// `t ≠ t'`.  Needed for `≤ n` value-partition clashes.
    fn factor(&self, clause: &ContextClause, root: bool) -> Vec<ContextClause> {
        let mut out = Vec::new();
        let heads = &clause.head;
        for i in 0..heads.len() {
            let (s, t) = match heads[i] {
                Lit::Eq { s, t } => (s, t),
                _ => continue,
            };
            for j in 0..heads.len() {
                if i == j {
                    continue;
                }
                if let Lit::Eq { s: s2, t: t2 } = heads[j] {
                    if s2 == s && t2 != t {
                        // drop head[i] (= s≈t), keep head[j] (= s≈t'), add t≉t'
                        let mut newhead: Vec<Lit> = heads
                            .iter()
                            .enumerate()
                            .filter(|(k, _)| *k != i)
                            .map(|(_, l)| *l)
                            .collect();
                        newhead.push(Lit::ineq(t, t2));
                        if let Some(h) = self.filter_head(newhead) {
                            let c = ContextClause::new(clause.body.clone(), h, root, &self.sig);
                            if !c.is_head_tautology() {
                                out.push(c);
                            }
                        }
                    }
                }
            }
        }
        out
    }

    /// Eq rule where the max literal is a predicate containing a rewritable term,
    /// resolved against worked-off equality clauses.
    fn eq_from_pred(&self, id: usize, side: &ContextClause, max: Lit, root: bool) -> Vec<ContextClause> {
        let mut out = Vec::new();
        let ctx = &self.contexts[id];
        let arena = &self.cc_arena[root as usize];
        let mterm = max.max_term();
        for &ci in &ctx.worked_off {
            let c = &arena[ci as usize];
            for l in c.max_head() {
                if let Lit::Eq { s, t } = l {
                    if s == mterm && max.contains_at_rewrite_position(s) {
                        if let Some(res) = self.build_eq(side, max, c, s, t, l, root) {
                            out.push(res);
                        }
                    }
                }
            }
        }
        out
    }

    /// Eq rule where the max literal is itself an equality/inequality.
    fn eq_from_equation(&self, id: usize, side: &ContextClause, max: Lit, root: bool) -> Vec<ContextClause> {
        let mut out = Vec::new();
        let ctx = &self.contexts[id];
        let arena = &self.cc_arena[root as usize];
        let s = match max {
            Lit::Eq { s, .. } | Lit::Ineq { s, .. } => s,
            _ => return out,
        };
        for &ci in &ctx.worked_off {
            let c = &arena[ci as usize];
            for l in c.max_head() {
                if l.contains_at_rewrite_position(s) && l != max {
                    if let Lit::Eq { s: es, t: et } = max {
                        // side provides equality es==et, rewrite l
                        if let Some(res) = self.build_eq(c, l, side, es, et, max, root) {
                            out.push(res);
                        }
                    }
                }
            }
        }
        out
    }

    /// Build the Eq-rule conclusion rewriting `max` (in `clause`) using equality
    /// `s == t` (the max literal of `eq_clause`).
    #[allow(clippy::too_many_arguments)]
    fn build_eq(
        &self,
        clause: &ContextClause,
        max: Lit,
        eq_clause: &ContextClause,
        s: Term,
        t: Term,
        equality: Lit,
        root: bool,
    ) -> Option<ContextClause> {
        let mut head: Vec<Lit> = Vec::new();
        // rewrite max's s-occurrence to t
        match max {
            Lit::P(_) => {
                if let Some(r) = max.rewrite(s, t) {
                    head.push(r);
                }
            }
            Lit::Eq { s: ms, t: t2 } if ms == s => {
                if t == t2 {
                    return None; // redundant
                }
                if let Some(r) = max.rewrite(s, t) {
                    head.push(r);
                }
            }
            Lit::Ineq { s: ms, t: t2 } if ms == s => {
                if t != t2 {
                    if let Some(r) = max.rewrite(s, t) {
                        head.push(r);
                    }
                }
            }
            _ => return None,
        }
        for l in &clause.head {
            if *l != max {
                head.push(*l);
            }
        }
        for l in &eq_clause.head {
            if *l != equality {
                head.push(*l);
            }
        }
        let mut body = clause.body.clone();
        body.extend_from_slice(&eq_clause.body);
        let head = self.filter_head(head)?;
        let c = ContextClause::new(body, head, root, &self.sig);
        if c.is_head_tautology() {
            None
        } else {
            Some(c)
        }
    }

    // -------------------- inter-context propagation ------------------------

    /// The successor context for function symbol `f` (pay-as-you-go strategy).
    /// Each distinct `f` gets its own empty-core context, created lazily.  These
    /// are tracked in `successor_ctxs` rather than `core_index`, because every
    /// successor context shares the empty core and must not be deduplicated into
    /// one (that is precisely the trivial strategy this replaces).
    fn successor_for(&mut self, f: Term) -> usize {
        if let Some(&s) = self.successor_ctxs.get(&f) {
            return s;
        }
        // Disabled via KM_NO_SHARE for A/B measurement; default on.
        if std::env::var_os("KM_NO_SHARE").is_some() {
            let id = self.contexts.len();
            let ctx = Context::new(id, vec![], false, None);
            self.contexts.push(ctx);
            self.successor_ctxs.insert(f, id);
            self.init_context(id);
            return id;
        }
        self.ensure_shared_closure();
        let id = self.contexts.len();
        let ctx = Context::new(id, vec![], false, None);
        self.contexts.push(ctx);
        self.successor_ctxs.insert(f, id);
        // Seed the shared context-independent closure directly into worked-off
        // (already mutually saturated, so it fires no rules here).  This replaces
        // `init_context` for successor contexts: the ontology facts are part of
        // the closure, and the empty core contributes no core clauses.  The
        // hypothesis clause that arrives via the first Succ message (apply_succ)
        // then saturates against this seeded closure, deriving exactly the
        // context-specific consequences.
        let closure = self.shared_closure.as_ref().unwrap().clone();
        for c in closure {
            self.seed_worked_off(id, c);
        }
        id
    }

    /// Central strategy: the successor context whose core is exactly `core`
    /// (the σ-image of a pushed trigger set), created on first use.  Seeded
    /// with the shared non-root closure (facts+TBox consequences) plus the
    /// Core rule for its core atoms.
    fn central_successor_for_core(&mut self, core: Vec<Pred>) -> usize {
        if let Some(&id) = self.central_index.get(&core) {
            return id;
        }
        let id = self.contexts.len();
        let ctx = Context::new(id, core.clone(), false, None);
        self.contexts.push(ctx);
        self.central_index.insert(core, id);
        if std::env::var_os("KM_NO_SHARE").is_none() {
            self.ensure_shared_closure();
            let closure = self.shared_closure.as_ref().unwrap().clone();
            for c in closure {
                self.seed_worked_off(id, c);
            }
            self.add_core(id);
        } else {
            self.init_context(id);
        }
        id
    }

    /// Compute the context-independent closure once: saturate a throwaway
    /// empty-core, non-root context from the ontology facts + TBox alone, then
    /// snapshot its worked-off clauses and discard the context.  No messages are
    /// generated (propagation is never run on it), so the snapshot is purely the
    /// facts/TBox consequences shared by every successor context.
    fn ensure_shared_closure(&mut self) {
        if self.shared_closure.is_some() {
            return;
        }
        let id = self.contexts.len();
        let ctx = Context::new(id, vec![], false, None);
        self.contexts.push(ctx);
        self.init_context(id); // seeds empty-body ontology facts (no core)
        self.saturate(id);
        let closure = self.contexts[id].worked_off.clone();
        // Discard the throwaway: nothing references `id` (no edges, not in
        // `successor_ctxs`/`core_index`, no query), so popping it keeps the
        // context vector and counts clean.
        debug_assert_eq!(id, self.contexts.len() - 1);
        self.contexts.pop();
        self.shared_closure = Some(closure);
    }

    /// Place an already-derived clause into context `id`'s worked-off set without
    /// firing any rules: mirrors the bookkeeping tail of `saturate` (clause-key
    /// set, semi-naive Pred/Succ pools, head indexes, dirty flag) so the seeded
    /// clause participates in later resolution and propagation exactly as if it
    /// had been worked off normally.
    fn seed_worked_off(&mut self, id: usize, cid: u32) {
        let d = self.contexts[id].root as usize;
        let (pred_eligible, succ_eligible) = {
            let clause = &self.cc_arena[d][cid as usize];
            (
                clause
                    .head
                    .iter()
                    .all(|l| l.is_function_free() && matches!(l, Lit::P(_))),
                clause
                    .max_head_predicates()
                    .any(|(p, _)| is_function(p.max_term())),
            )
        };
        let arena = &self.cc_arena[d];
        let ctx = &mut self.contexts[id];
        if !ctx.clause_keys.insert(cid) {
            return;
        }
        if pred_eligible {
            ctx.pred_pool.push(cid);
        }
        if succ_eligible {
            ctx.succ_pool.push(cid);
        }
        ctx.worked_off.push(cid);
        ctx.index_clause(arena, cid);
        ctx.dirty = true;
    }

    /// `true` if context `sid` has derived concept `iri` on its central
    /// variable as an unconditional fact (`⊤ → iri(x)`).  Used by the
    /// redundant-trigger skip to detect a push-back the successor already knows.
    fn ctx_derives_central(&self, sid: usize, iri: Iri) -> bool {
        let ctx = &self.contexts[sid];
        let arena = &self.cc_arena[ctx.root as usize];
        if let Some(idxs) = ctx.head_concept_index.get(&iri) {
            for &ci in idxs {
                let c = &arena[ci as usize];
                if c.body.is_empty()
                    && c.head.len() == 1
                    && matches!(c.head[0], Lit::P(Pred::Concept { iri: i, t }) if i == iri && is_central(t))
                {
                    return true;
                }
            }
        }
        false
    }

    /// After saturating context `id`, generate Succ and Pred messages.
    fn propagate(&mut self, id: usize) {
        if !self.contexts[id].dirty {
            return;
        }
        self.stat_propagate += 1;
        self.contexts[id].dirty = false;
        // ---- Succ ---- (semi-naive: scan only pool entries added since the last
        // propagate; succ triggers only arise from new worked-off clauses, and
        // `pushed_succ` still dedups within and across scans).
        let mut new_succ: Vec<(Pred, bool)> = Vec::new();
        // r-Succ (nominal calculus): ground max-head atoms about an
        // individual push their y-form to the ground context, edge labelled
        // by the individual.
        let mut ground_succ: Vec<(Pred, Term)> = Vec::new();
        let succ_start = self.contexts[id].succ_hwm;
        self.stat_succ_scans += (self.contexts[id].succ_pool.len() - succ_start) as u64;
        {
            let ctx = &self.contexts[id];
            let arena = &self.cc_arena[ctx.root as usize];
            for &ci in &ctx.succ_pool[succ_start..] {
                let c = &arena[ci as usize];
                // Core-eligibility: a trigger may enter the successor core only
                // if it is the SOLE succ-trigger over its function term in this
                // clause's head.  A core atom is discharged by cutting it from
                // its source clause (residue literals accumulate in the
                // resolvent), which works for any single trigger — body
                // conditions and other-term disjuncts ride along.  But two
                // triggers over the same f from ONE head (e.g. the
                // `… → A2(f)|A3(f)|Q` of a min-card case split) cannot both be
                // cut from the same clause, so conditioning a push-back on both
                // at once loses the per-disjunct refutations completeness
                // needs; such triggers stay hypotheses (`p → p` at the target).
                let mut multi: Vec<Term> = Vec::new();
                {
                    let mut seen: Vec<Term> = Vec::new();
                    for l in &c.head {
                        if let Lit::P(p) = l {
                            let t = p.max_term();
                            if is_function(t) && p.is_succ_trigger(&self.sig) {
                                if seen.contains(&t) {
                                    if !multi.contains(&t) {
                                        multi.push(t);
                                    }
                                } else {
                                    seen.push(t);
                                }
                            }
                        }
                    }
                }
                for (p, _) in c.max_head_predicates() {
                    if is_function(p.max_term())
                        && p.is_succ_trigger(&self.sig)
                        && !ctx.pushed_succ.contains(&p)
                    {
                        new_succ.push((p, !multi.contains(&p.max_term())));
                    } else if Some(id) != self.ground_ctx {
                        if let Some((yform, o)) = root_succ_form(&p) {
                            if !ctx.pushed_succ.contains(&yform)
                                && !rsucc_blocked(ctx, arena, c, &p)
                            {
                                ground_succ.push((yform, o));
                            }
                        }
                    }
                }
            }
        }
        if !ground_succ.is_empty() {
            let target = self.ground_context();
            for (p, o) in ground_succ {
                if self.contexts[id].pushed_succ.insert(p) {
                    self.msgs.push_back(Msg::Succ { from: id, f: o, p, target });
                }
            }
        }
        self.contexts[id].succ_hwm = self.contexts[id].succ_pool.len();
        if !self.central {
            // Legacy pay-as-you-go strategy: one empty-core successor per `f`.
            for (p, _) in new_succ {
                let f = p.max_term();
                let target = self.successor_for(f);
                // forward map: f -> x, x -> y
                let psigma = p.apply(&|v| forwards(f, v));
                self.contexts[id].pushed_succ.insert(p);
                self.contexts[id].successors.insert(f, target);
                self.msgs.push_back(Msg::Succ {
                    from: id,
                    f,
                    p: psigma,
                    target,
                });
            }
        } else {
            // Central strategy: group the new triggers by `f`, extend each
            // trigger set, and (re-)target the successor context whose core is
            // the σ-image of the full set.  A grown set yields a new target and
            // the WHOLE set is re-sent there (the new context needs every
            // pushed predicate for its edge bookkeeping and hypotheses); the
            // previous (smaller-core) context simply stops receiving — its
            // earlier back-pushed consequences remain sound because apply_pred
            // conditions them on that context's own core.
            let mut grew: Vec<Term> = Vec::new();
            let mut new_by_f: HashMap<Term, Vec<Pred>> = HashMap::new();
            {
                // Redundant-trigger skip (KM_NO_TRIGSKIP to disable): a concept
                // trigger `C(f)` whose successor context for `f` already derives
                // `C` on its own central is a redundant push-back — growing `f`'s
                // core to `{filler, C}` would just duplicate the `{filler}`
                // context (C is derivable from the filler), so it adds churn with
                // no new consequence.  Skipping it keeps the successor mapped to
                // its existing context (whose edge already delivers every
                // consequence) and stops the grown-core cascade that otherwise
                // overruns the message budget on transitive/role-chain onts.
                // Genuinely-new concepts (not yet derived by the successor) still
                // grow the core, so completeness is preserved.
                let trigskip = std::env::var_os("KM_NO_TRIGSKIP").is_none();
                let mut redundant: Vec<Pred> = Vec::new();
                if trigskip {
                    for (p, _) in &new_succ {
                        if let Pred::Concept { iri, t } = *p {
                            let f = t;
                            if let Some(&sid) = self.contexts[id].successors.get(&f) {
                                if self.ctx_derives_central(sid, iri) {
                                    redundant.push(*p);
                                }
                            }
                        }
                    }
                }
                let ctx = &mut self.contexts[id];
                for (p, is_fact) in new_succ {
                    // Always mark pushed so we never re-process this trigger.
                    ctx.pushed_succ.insert(p);
                    if redundant.contains(&p) {
                        continue; // redundant push-back: do not grow the core
                    }
                    let f = p.max_term();
                    ctx.trigger_sets.entry(f).or_default().insert(p);
                    if is_fact {
                        ctx.fact_trigger_sets.entry(f).or_default().insert(p);
                    }
                    new_by_f.entry(f).or_default().push(p);
                    if !grew.contains(&f) {
                        grew.push(f);
                    }
                }
            }
            for f in grew {
                let raw: Vec<Pred> = self.contexts[id].trigger_sets[&f].iter().copied().collect();
                // The successor core is the σ-image of the FACT triggers only;
                // disjunctively/conditionally derived triggers stay hypotheses
                // (see `fact_trigger_sets`).
                let mut core: Vec<Pred> = self.contexts[id]
                    .fact_trigger_sets
                    .get(&f)
                    .map(|s| s.iter().map(|p| p.apply(&|v| forwards(f, v))).collect())
                    .unwrap_or_default();
                core.sort();
                core.dedup();
                let target = self.central_successor_for_core(core);
                let prev = self.contexts[id].successors.insert(f, target);
                if prev != Some(target) {
                    // New target (first push or fact-core growth): send the full
                    // set so the new context's edge records every pushed
                    // predicate.
                    for p in &raw {
                        self.msgs.push_back(Msg::Succ {
                            from: id,
                            f,
                            p: p.apply(&|v| forwards(f, v)),
                            target,
                        });
                    }
                } else {
                    // Same target (hypothesis-only growth): send just the new
                    // triggers so the target gains their edge bookkeeping and
                    // hypothesis clauses.
                    for p in &new_by_f[&f] {
                        self.msgs.push_back(Msg::Succ {
                            from: id,
                            f,
                            p: p.apply(&|v| forwards(f, v)),
                            target,
                        });
                    }
                }
            }
        }
        // ---- Pred ---- (semi-naive).  The Pred-eligible clauses live in
        // `pred_pool` (function-free, predicate-only head — built when a clause is
        // worked off, see `saturate`; pushing a back-subsumed pool entry stays
        // sound because it is still context-entailed).  A `(clause, edge)`
        // covered-check `c.body ⊆ pushed[edge]` can only flip from fail to pass
        // when `pushed[edge]` gains a predicate, so we re-check a pair only when
        // the clause is new (index ≥ `pred_hwm`) or the edge's pushed-set grew
        // since `edge_seen`.  `pushed_pred` still dedups actual sends.  This
        // replaces the per-propagate full `worked_off × predecessors` rescan that
        // dominated runtime on existential-rich ontologies.
        let mut to_send: Vec<((usize, Term), u32)> = Vec::new();
        let mut pred_checks = 0u64;
        let ground_sender = Some(id) == self.ground_ctx;
        let new_edge_seen: Vec<((usize, Term), usize)>;
        {
            let ctx = &self.contexts[id];
            let arena = &self.cc_arena[ctx.root as usize];
            let hwm = ctx.pred_hwm;
            // edges with a freshness flag (pushed-set grew since last scan)
            let edges: Vec<(&(usize, Term), &HashSet<Pred>, bool)> = ctx
                .predecessors
                .iter()
                .map(|(e, pushed)| {
                    let seen = *ctx.edge_seen.get(e).unwrap_or(&0);
                    (e, pushed, pushed.len() > seen)
                })
                .collect();
            // Distinct source contexts and per-source freshness for the
            // ground-sender (r-Pred) path: a source is dirty when any of its
            // individual-labelled edges gained a pushed predicate.
            let mut sources: Vec<(usize, Term, bool)> = Vec::new();
            if ground_sender {
                for (e, _, dirty) in &edges {
                    match sources.iter_mut().find(|(u, _, _)| *u == e.0) {
                        Some(s) => {
                            s.2 |= *dirty;
                            if e.1 < s.1 {
                                s.1 = e.1; // smallest label as the stable representative
                            }
                        }
                        None => sources.push((e.0, e.1, *dirty)),
                    }
                }
            }
            for (i, &ci) in ctx.pred_pool.iter().enumerate() {
                let c = &arena[ci as usize];
                let new_clause = i >= hwm;
                // r-Pred (ground sender, x-free clauses): each body atom may be
                // discharged over a DIFFERENT individual-labelled edge of the
                // same source u (the paper's ⟨u, v_r, o_i⟩ per A_i), or — when
                // ground — copied verbatim (the C_i) provided u announced its
                // individuals.  Head individuals (e.g. Nom's fresh additional
                // nominals) need no edge: requiring one made every Nom
                // conclusion undeliverable.  Clauses mentioning x keep the
                // per-edge path below: their x is instantiated by the edge
                // label, so each edge yields a different conclusion.
                if ground_sender && !cc_mentions_x(c) {
                    for &(u, label, dirty_u) in &sources {
                        if !new_clause && !dirty_u {
                            continue;
                        }
                        pred_checks += 1;
                        // Every body atom must be DISCHARGED over u's edge
                        // labelled by that atom's individual (the paper's
                        // ⟨u, v_r, o_i⟩ per A_i, multi-edge per source), and
                        // every individual the clause mentions must be one u
                        // has announced (an edge per individual) — EXCEPT
                        // additional nominals (id ≥ nom_base), which no
                        // context can have announced: they are exactly what
                        // the Nom conclusions carry back.  Without the
                        // announcement guard, body-empty ground facts pass
                        // the discharge check vacuously and spray to every
                        // context with any root edge (livelock on ABox-heavy
                        // ontologies: ore_ont_10594, ~1900 individuals).
                        // Looser variants tried and rejected: verbatim C_i
                        // copies (announced-only) and no head filter — both
                        // unbounded on 10594.
                        let mut ok = true;
                        for b in &c.body {
                            let mut inds: Vec<Term> = Vec::new();
                            pred_inds(b, &mut inds);
                            let discharged = inds.iter().any(|o| {
                                ctx.predecessors
                                    .get(&(u, *o))
                                    .map_or(false, |s| s.contains(b))
                            });
                            if !discharged {
                                ok = false;
                                break;
                            }
                        }
                        if ok {
                            let mut inds: Vec<Term> = Vec::new();
                            for p in &c.body {
                                pred_inds(p, &mut inds);
                            }
                            for l in &c.head {
                                lit_inds(l, &mut inds);
                            }
                            ok = inds.iter().all(|o| {
                                *o >= self.nom_base
                                    || ctx.predecessors.contains_key(&(u, *o))
                            });
                        }
                        if ok {
                            let edge = (u, label);
                            let sent = ctx
                                .pushed_pred
                                .get(&edge)
                                .map_or(false, |s| s.contains(&(i as u32)));
                            if !sent {
                                to_send.push((edge, i as u32));
                            }
                        }
                    }
                    continue;
                }
                for (edge, pushed, dirty_edge) in &edges {
                    // (old clause, unchanged edge): already checked at this
                    // edge's pushed-length — skip.
                    if !new_clause && !*dirty_edge {
                        continue;
                    }
                    pred_checks += 1;
                    // Every body atom must be backed by this edge's pushed set
                    // (for the ground context these are the r-Succ hypotheses
                    // — the paper's "same u for every o_i" condition); and a
                    // ground-context clause only flows to a context that has
                    // announced every individual it mentions (an edge per
                    // individual), which keeps ground conclusions from being
                    // sprayed across unrelated contexts.
                    if c.body.iter().all(|b| pushed.contains(b))
                        && (!ground_sender || {
                            let mut inds: Vec<Term> = Vec::new();
                            for p in &c.body {
                                pred_inds(p, &mut inds);
                            }
                            for l in &c.head {
                                lit_inds(l, &mut inds);
                            }
                            inds.iter().all(|o| ctx.predecessors.contains_key(&(edge.0, *o)))
                        })
                    {
                        let sent = ctx
                            .pushed_pred
                            .get(*edge)
                            .map_or(false, |s| s.contains(&(i as u32)));
                        if !sent {
                            to_send.push((**edge, i as u32));
                        }
                    }
                }
            }
            new_edge_seen = ctx
                .predecessors
                .iter()
                .map(|(e, pushed)| (*e, pushed.len()))
                .collect();
        }
        self.stat_pred_checks += pred_checks;
        self.contexts[id].pred_hwm = self.contexts[id].pred_pool.len();
        for (e, len) in new_edge_seen {
            self.contexts[id].edge_seen.insert(e, len);
        }
        for (edge, pool_idx) in to_send {
            self.contexts[id]
                .pushed_pred
                .entry(edge)
                .or_default()
                .insert(pool_idx);
            self.msgs.push_back(Msg::Pred {
                to: edge.0,
                from: id,
                edge_label: edge.1,
                pool_idx,
            });
        }
    }

    /// Apply a Succ message: record the edge and add the hypothesis clause,
    /// saturating the target.  Returns the target id; the caller propagates it
    /// (deferred, batched: many messages may target the same context, and
    /// propagating once after the whole batch -- rather than per message --
    /// avoids re-scanning the edge/pool sets thousands of times on
    /// disjunction/role-chain ontologies, without changing the fixpoint).
    fn apply_succ(&mut self, from: usize, f: Term, p: Pred, target: usize) -> usize {
        // record predecessor edge
        self.contexts[target]
            .predecessors
            .entry((from, f))
            .or_default()
            .insert(p);
        // a new edge / pushed predicate may let existing worked-off clauses be
        // pushed back to this predecessor, so the next propagate must re-scan.
        self.contexts[target].dirty = true;
        // Succ rule: add hypothesis clause  p -> p.  Saturate unconditionally:
        // under the central strategy a FACT trigger's hypothesis is subsumed by
        // the core's `-> p` (add_clause returns false), while a disjunctively
        // derived trigger's hypothesis is genuinely new and saturates — its
        // consequences come back conditioned on `p` alone, which is what the
        // per-disjunct cuts need.  Either way the core clauses seeded at
        // context creation still sit in `todo` and must be worked off.
        let root = self.contexts[target].root;
        let c = ContextClause::new(vec![p], vec![Lit::P(p)], root, &self.sig);
        self.add_clause(target, c);
        self.saturate(target);
        target
    }

    /// Apply a Pred message: back-substitute and add the resulting pred clause /
    /// resolvents, saturating `to`.  Returns `to`; the caller propagates it
    /// (deferred, batched -- see `apply_succ`).
    fn apply_pred(&mut self, to: usize, from: usize, edge_label: Term, pool_idx: u32) -> usize {
        let pc = self.pred_payload(from, edge_label, pool_idx);
        self.apply_pred_payload(to, pc)
    }

    /// The sender-side half of a Pred message: back-substitute the sender's
    /// pool entry + core into the pred clause that crosses the edge. Reads only
    /// the (immutable) sender context `from` — `&self`, no mutation — so it is
    /// safe to call for every batched message up front, before any target is
    /// mutated. Isolating this read is what lets `apply_pred_payload` run in
    /// parallel across distinct targets without a sender/target aliasing race on
    /// the sender's append-only `pred_pool`.
    fn pred_payload(&self, from: usize, edge_label: Term, pool_idx: u32) -> PredClause {
        // Back-substitute: y -> x, x -> f(x).  The sender's pool entry and core
        // are immutable once created, so resolving them here reads exactly the
        // snapshot a send-time copy would have carried.
        let from_ctx = &self.contexts[from];
        let arena = &self.cc_arena[from_ctx.root as usize];
        let clause = &arena[from_ctx.pred_pool[pool_idx as usize] as usize];
        let f = edge_label;
        let subst = |v: Term| backwards(f, v);
        let mut body: Vec<Pred> = clause.body.iter().map(|p| p.apply(&subst)).collect();
        for p in &from_ctx.core {
            body.push(p.apply(&subst));
        }
        // Full literals: pool-eligible heads are predicates plus (nominal
        // mode) the individual equality forms; `x ≈ o` crosses as
        // `f(x) ≈ o`, which the receiver's Eq rule then rewrites.
        let head: Vec<Lit> = clause.head.iter().map(|l| l.apply(&subst)).collect();
        PredClause { body, head }
    }

    /// The receiver-side half of a Pred message: intern the back-substituted
    /// clause, dedup against prior arrivals, fire the Pred rule against `to`'s
    /// worked-off clauses, and saturate `to`. Mutates only context `to` (plus
    /// the shared arena / intern tables). Returns `to`.
    fn apply_pred_payload(&mut self, to: usize, pc: PredClause) -> usize {
        let pid = self.intern_pred(pc);
        // Duplicate arrival (same substituted clause already received, e.g. from
        // a successor's pre- and post-growth contexts): everything it could
        // contribute was already derived, so skip the re-derivation.
        if !self.contexts[to].neighbor_pred_seen.insert(pid) {
            return to;
        }
        self.contexts[to].neighbor_pred.push(pid);
        // Apply Pred rule against worked-off clauses of `to`.
        let root = self.contexts[to].root;
        let results = {
            let pc = &self.pred_interned[pid as usize];
            self.pred_from_neighbor(to, pc, root)
        };
        for r in results {
            self.add_clause(to, r);
        }
        self.saturate(to);
        to
    }

    /// Pred rule for a freshly received neighbor pred clause: resolve its
    /// body predicates against worked-off clauses of context `id`. Ground
    /// body atoms (nominal mode) resolve like the others when a provider
    /// exists and are otherwise copied verbatim to the resolvent body (the
    /// C_i of arXiv:1805.01396 Pred / r-Pred).
    fn pred_from_neighbor(&self, id: usize, pc: &PredClause, root: bool) -> Vec<ContextClause> {
        let mut out = Vec::new();
        let ctx = &self.contexts[id];
        let arena = &self.cc_arena[root as usize];
        let mut ground: Vec<Pred> = Vec::new();
        let mut candidates: Vec<Vec<(usize, Pred)>> = Vec::with_capacity(pc.body.len());
        for &bp in &pc.body {
            let mut v = Vec::new();
            let cand = match bp {
                Pred::Concept { iri, .. } => ctx.head_concept_index.get(&iri),
                Pred::Role { iri, .. } => ctx.head_role_index.get(&iri),
            };
            if let Some(cand) = cand {
                for &ci in cand {
                    if arena[ci as usize].max_head_predicates().any(|(p, _)| p == bp) {
                        v.push((ci as usize, bp));
                    }
                }
            }
            if v.is_empty() {
                if bp.is_ground() {
                    ground.push(bp);
                    continue;
                }
                return out; // a body predicate has no provider: no resolvent
            }
            candidates.push(v);
        }
        let n = candidates.len();
        let mut idxs = vec![0usize; n];
        loop {
            // build resolvent (no side clause; all from worked-off)
            let mut head: Vec<Lit> = pc.head.clone();
            let mut body: Vec<Pred> = ground.clone();
            for i in 0..n {
                let (ci, matched) = candidates[i][idxs[i]];
                let clause = &arena[ci];
                for l in &clause.head {
                    if *l != Lit::P(matched) {
                        head.push(*l);
                    }
                }
                body.extend_from_slice(&clause.body);
            }
            if let Some(head) = self.filter_head(head) {
                out.push(ContextClause::new(body, head, root, &self.sig));
            }
            if n == 0 {
                break;
            }
            let mut k = 0;
            loop {
                if k == n {
                    idxs[0] = usize::MAX;
                    break;
                }
                idxs[k] += 1;
                if idxs[k] < candidates[k].len() {
                    break;
                }
                idxs[k] = 0;
                k += 1;
            }
            if idxs[0] == usize::MAX {
                break;
            }
        }
        out
    }

    // ------------------------------ driver ---------------------------------

    /// All named (non-internal, non-Nothing) concepts, i.e. the default query set.
    pub fn named_queries(&self) -> Vec<Iri> {
        (0..self.sig.concept_names.len() as Iri)
            .filter(|&i| !self.sig.is_internal(i) && !self.sig.is_nothing_concept(i))
            .collect()
    }

    pub fn run(&mut self) {
        let named = self.named_queries();
        self.run_for(&named);
    }

    /// Classify exactly the given query concepts (seed one root context each,
    /// then run the inter-context message fixpoint).  Each query's subsumptions
    /// are independent of which other queries are co-classified -- the shared
    /// successor context is only an optimisation -- so classifying a subset is
    /// sound and yields identical results for those concepts.  This is what lets
    /// classification be parallelised across disjoint concept chunks.
    pub fn run_for(&mut self, queries: &[Iri]) {
        let prof = std::env::var("KM_PROF").is_ok();
        // Ground (nominal root) context: eager when the ontology has ground
        // facts — a contradiction among the individuals alone (detected only
        // here) is global inconsistency, independent of any query.
        if !self.ont.ground_facts.is_empty() {
            let gid = self.ground_context();
            self.propagate(gid);
        }
        // Root contexts: one per named (query) concept.
        for (qi, &iri) in queries.iter().enumerate() {
            let core = vec![Pred::Concept { iri, t: X }];
            let id = self.get_or_create_context(core, true, Some(iri));
            self.saturate(id);
            self.propagate(id);
            if prof && (qi + 1) % 50 == 0 {
                eprintln!(
                    "KM_PROF seeding query {}/{} contexts={} msgs_pending={} saturate_calls={}",
                    qi + 1, queries.len(), self.contexts.len(), self.msgs.len(), self.stat_saturate
                );
            }
        }
        if prof {
            eprintln!(
                "KM_PROF seeded all {} queries; contexts={} msgs_pending={} saturate_calls={}",
                queries.len(), self.contexts.len(), self.msgs.len(), self.stat_saturate
            );
        }
        // Always seed the ⊤ (empty-core) context so a *global* inconsistency
        // (owl:Thing unsatisfiable) is detected regardless of which concepts are
        // named in the input (audit M2). It carries query=None, so `subsumptions`
        // skips it and it never contributes to the classification output.
        let top = self.get_or_create_context(vec![], true, None);
        self.saturate(top);
        self.propagate(top);
        // Process inter-context messages to fixpoint, *batched*: drain the whole
        // pending set, apply each message (which saturates its target but does
        // not propagate), recording the touched contexts, then propagate each
        // touched context exactly once.  Applying a message never enqueues new
        // messages (only `propagate` does), so a batch is self-contained and the
        // next batch is the propagation output.  Propagating once per batch --
        // instead of after every message -- avoids re-scanning each context's
        // predecessor-edge and Succ/Pred pools thousands of times on
        // disjunction/role-chain ontologies (the dominant cost there).  The
        // fixpoint is unchanged: saturation is monotone and confluent, so the
        // derived clause set is independent of the propagation schedule.
        let mut guard = 0usize;
        let (mut nsucc_msgs, mut npred_msgs) = (0u64, 0u64);
        let trace = std::env::var("KM_TRACE").is_ok();
        // Hard safety cap on the inter-context message fixpoint (backstop against
        // a runaway central-strategy core-growth cascade). Configurable via
        // KM_MSG_CAP; default 25M. Raising it trades time/memory for completeness
        // on heavy role-chain/transitive ontologies whose fixpoint is large but
        // finite -- e.g. ore_ont_9944 needs ~13.8M messages to converge (and
        // derives ~15k more subsumptions than the truncated 5M run); the per-run
        // time/memory limits remain the real guard for genuinely pathological
        // inputs, so honest convergence is preferred over silent truncation.
        let msg_cap: usize = std::env::var("KM_MSG_CAP")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(25_000_000);
        let mut truncated = false;
        while !self.msgs.is_empty() {
            let batch: Vec<Msg> = self.msgs.drain(..).collect();
            let mut touched: Vec<usize> = Vec::new();
            let mut seen: HashSet<usize> = HashSet::new();
            for msg in batch {
                guard += 1;
                if guard > msg_cap {
                    // Hard safety cap on the inter-context message fixpoint.
                    // Hitting it means the run was truncated, so the
                    // classification may be INCOMPLETE -- never silently: warn on
                    // stderr (audit L1/L2). Sound (only consequences are
                    // dropped), but completeness is not guaranteed for this run.
                    eprintln!(
                        "WARNING: kobayashi-marust message fixpoint hit the {} cap; \
                         classification may be incomplete (truncated). {} pending messages dropped.",
                        msg_cap, self.msgs.len()
                    );
                    truncated = true;
                    break;
                }
                if prof && guard % 20000 == 0 {
                    let gwo = self
                        .ground_ctx
                        .map(|g| self.contexts[g].worked_off.len())
                        .unwrap_or(0);
                    eprintln!(
                        "KM_PROF msgloop guard={} contexts={} msgs_pending={} saturate_calls={} succ={} pred={} ground_wo={}",
                        guard, self.contexts.len(), self.msgs.len(), self.stat_saturate,
                        nsucc_msgs, npred_msgs, gwo
                    );
                }
                if trace && guard % 200_000 == 0 {
                    let (mut maxb, mut totwo) = (0usize, 0usize);
                    // Head-size histogram (h1/h2/h3/h4plus) + max head, to tell a
                    // disjunctive-blowup (many incomparable multi-head clauses) from
                    // a Horn one. `topwo` = largest single-context worked_off.
                    let (mut h1, mut h2, mut h3, mut h4p, mut maxh, mut topwo) =
                        (0usize, 0usize, 0usize, 0usize, 0usize, 0usize);
                    for c in &self.contexts {
                        let arena = &self.cc_arena[c.root as usize];
                        totwo += c.worked_off.len();
                        if c.worked_off.len() > topwo { topwo = c.worked_off.len(); }
                        for &ci in &c.worked_off {
                            let cl = &arena[ci as usize];
                            if cl.body.len() > maxb { maxb = cl.body.len(); }
                            if cl.head.len() > maxh { maxh = cl.head.len(); }
                            match cl.head.len() {
                                0 | 1 => h1 += 1,
                                2 => h2 += 1,
                                3 => h3 += 1,
                                _ => h4p += 1,
                            }
                        }
                    }
                    eprintln!(
                        "KM_TRACE guard={} contexts={} msgs_pending={} worked_off_total={} \
                         max_body_len={} max_head_len={} top_ctx_wo={} head[<=1={} 2={} 3={} >=4={}]",
                        guard, self.contexts.len(), self.msgs.len(), totwo, maxb, maxh,
                        topwo, h1, h2, h3, h4p
                    );
                }
                let t = match msg {
                    Msg::Succ { from, f, p, target } => {
                        nsucc_msgs += 1;
                        self.apply_succ(from, f, p, target)
                    }
                    Msg::Pred {
                        to,
                        from,
                        edge_label,
                        pool_idx,
                    } => {
                        npred_msgs += 1;
                        self.apply_pred(to, from, edge_label, pool_idx)
                    }
                };
                if seen.insert(t) {
                    touched.push(t);
                }
            }
            if truncated {
                break;
            }
            for id in touched {
                self.propagate(id);
            }
        }
        if std::env::var("KM_DUMP_WO").is_ok() {
            let fmt_t = |t: Term| -> String {
                if t == X { "x".to_string() }
                else if t == Y { "y".to_string() }
                else if t < 0 { format!("z{}", -t - 1) }
                else { format!("f{}(x)", t) }
            };
            let fmt_p = |p: &Pred| -> String {
                match *p {
                    Pred::Concept { iri, t } => format!("{}({})", self.sig.concept_names[iri as usize], fmt_t(t)),
                    Pred::Role { iri, s, t } => format!("{}({},{})", self.sig.role_names[iri as usize], fmt_t(s), fmt_t(t)),
                }
            };
            let fmt_l = |l: &Lit| -> String {
                match *l {
                    Lit::P(p) => fmt_p(&p),
                    Lit::Eq { s, t } => format!("{}={}", fmt_t(s), fmt_t(t)),
                    Lit::Ineq { s, t } => format!("{}!={}", fmt_t(s), fmt_t(t)),
                }
            };
            for ctx in &self.contexts {
                let core: Vec<String> = ctx.core.iter().map(&fmt_p).collect();
                eprintln!("== ctx {} root={} query={:?} core=[{}] wo={}",
                    ctx.id, ctx.root,
                    ctx.query.map(|i| self.sig.concept_names[i as usize].clone()),
                    core.join(", "), ctx.worked_off.len());
                let arena = &self.cc_arena[ctx.root as usize];
                for &ci in &ctx.worked_off {
                    let c = &arena[ci as usize];
                    let b: Vec<String> = c.body.iter().map(&fmt_p).collect();
                    let h: Vec<String> = c.head.iter().map(&fmt_l).collect();
                    eprintln!("   {} -> {}",
                        if b.is_empty() { "T".to_string() } else { b.join(" & ") },
                        if h.is_empty() { "F".to_string() } else { h.join(" | ") });
                }
            }
        }
        if let Ok(pat) = std::env::var("KM_TRACE_C") {
            // Substring-filtered context dump: only contexts whose core or
            // worked-off set mentions a concept/role name containing any of the
            // comma-separated needles.  Keeps output tractable on full ORE onts
            // when tracing one query's reachability propagation.
            let needles: Vec<String> = pat.split(',').map(|s| s.to_string()).collect();
            let fmt_t = |t: Term| -> String {
                if t == X { "x".to_string() }
                else if t == Y { "y".to_string() }
                else if t < 0 { format!("z{}", -t - 1) }
                else { format!("f{}(x)", t) }
            };
            let nm_c = |iri: u32| self.sig.concept_names[iri as usize].clone();
            let nm_r = |iri: u32| self.sig.role_names[iri as usize].clone();
            let fmt_p = |p: &Pred| -> String {
                match *p {
                    Pred::Concept { iri, t } => format!("{}({})", nm_c(iri), fmt_t(t)),
                    Pred::Role { iri, s, t } => format!("{}({},{})", nm_r(iri), fmt_t(s), fmt_t(t)),
                }
            };
            let fmt_l = |l: &Lit| -> String {
                match *l {
                    Lit::P(p) => fmt_p(&p),
                    Lit::Eq { s, t } => format!("{}={}", fmt_t(s), fmt_t(t)),
                    Lit::Ineq { s, t } => format!("{}!={}", fmt_t(s), fmt_t(t)),
                }
            };
            let hit = |p: &Pred| -> bool {
                let n = match *p {
                    Pred::Concept { iri, .. } => nm_c(iri),
                    Pred::Role { iri, .. } => nm_r(iri),
                };
                needles.iter().any(|nd| n.contains(nd.as_str()))
            };
            for ctx in &self.contexts {
                let arena = &self.cc_arena[ctx.root as usize];
                let touch = ctx.core.iter().any(&hit)
                    || ctx.worked_off.iter().any(|&ci| {
                        let c = &arena[ci as usize];
                        c.body.iter().any(&hit)
                            || c.head.iter().any(|l| matches!(l, Lit::P(p) if hit(p)))
                    });
                if !touch { continue; }
                let core: Vec<String> = ctx.core.iter().map(&fmt_p).collect();
                eprintln!("== ctx {} root={} query={:?} core=[{}] preds={} wo={}",
                    ctx.id, ctx.root,
                    ctx.query.map(|i| nm_c(i)),
                    core.join(", "), ctx.predecessors.len(), ctx.worked_off.len());
                let mut succs: Vec<String> = ctx.successors.iter()
                    .map(|(f, sid)| format!("f{}->{}", f, sid)).collect();
                succs.sort();
                eprintln!("   SUCC: {}", succs.join(" "));
                let mut preds: Vec<String> = ctx.predecessors.keys()
                    .map(|(pid, f)| format!("{}@f{}", pid, f)).collect();
                preds.sort();
                eprintln!("   PRED-OF: {}", preds.join(" "));
                for &ci in &ctx.worked_off {
                    let c = &arena[ci as usize];
                    // only print clauses mentioning a needle (keeps it focused)
                    let rel = c.body.iter().any(&hit)
                        || c.head.iter().any(|l| matches!(l, Lit::P(p) if hit(p)));
                    if !rel { continue; }
                    let b: Vec<String> = c.body.iter().map(&fmt_p).collect();
                    let h: Vec<String> = c.head.iter().map(&fmt_l).collect();
                    eprintln!("   {} -> {}",
                        if b.is_empty() { "T".to_string() } else { b.join(" & ") },
                        if h.is_empty() { "F".to_string() } else { h.join(" | ") });
                }
            }
        }
        if std::env::var("KM_STATS").is_ok() {
            let nroot = self.contexts.iter().filter(|c| c.root).count();
            let nsucc = self.contexts.iter().filter(|c| !c.root).count();
            let root_wo: usize = self.contexts.iter().filter(|c| c.root).map(|c| c.worked_off.len()).sum();
            let succ_wo: usize = self.contexts.iter().filter(|c| !c.root).map(|c| c.worked_off.len()).sum();
            let top_wo = self.contexts.iter().find(|c| c.root && c.core.is_empty()).map(|c| c.worked_off.len()).unwrap_or(0);
            eprintln!(
                "KM_STATS contexts={} roots={} succs={} root_wo_total={} succ_wo_total={} top_wo={} avg_root_wo={:.0}",
                self.contexts.len(), nroot, nsucc, root_wo, succ_wo, top_wo,
                root_wo as f64 / nroot.max(1) as f64
            );
            eprintln!(
                "KM_STATS propagate={} pred_checks={} succ_scans={} hyper_calls={} saturate={}",
                self.stat_propagate, self.stat_pred_checks, self.stat_succ_scans,
                HYPER_CALLS.with(|c| c.get()), self.stat_saturate
            );
        }
        if std::env::var("KM_MEMSTATS").is_ok() {
            // Exact-ish accounting of where context memory sits (heap data via
            // capacity(); hash-table load factors not modelled, so map/set
            // figures are lower bounds). Diagnostics only -- no effect on
            // reasoning.
            use std::mem::size_of;
            let szp = size_of::<Pred>();
            let szl = size_of::<Lit>();
            let szcc = size_of::<ContextClause>();
            let cc_heap = |c: &ContextClause| {
                // max_head is now a u64 mask inside the struct (no heap).
                c.body.capacity() * szp + c.head.capacity() * szl
            };
            let mut cat: Vec<(&str, usize, usize)> = Vec::new(); // (name, count, bytes)
            let mut add = |name: &'static str, n: usize, b: usize| {
                if let Some(e) = cat.iter_mut().find(|e| e.0 == name) {
                    e.1 += n;
                    e.2 += b;
                } else {
                    cat.push((name, n, b));
                }
            };
            for ctx in &self.contexts {
                add("core", ctx.core.len(), ctx.core.capacity() * szp);
                add(
                    "worked_off(ids)",
                    ctx.worked_off.len(),
                    ctx.worked_off.capacity() * 4,
                );
                add(
                    "clause_keys(ids)",
                    ctx.clause_keys.len(),
                    ctx.clause_keys.len() * 12,
                );
                add(
                    "head_indexes",
                    ctx.head_concept_index.len() + ctx.head_role_index.len() + ctx.head_lit_index.len(),
                    ctx.head_concept_index.values().map(|v| 24 + 4 + v.capacity() * 4).sum::<usize>()
                        + ctx.head_role_index.values().map(|v| 24 + 4 + v.capacity() * 4).sum::<usize>()
                        + ctx.head_lit_index.values().map(|v| 24 + szl + v.capacity() * 4).sum::<usize>(),
                );
                add("todo", ctx.todo.len(), ctx.todo.capacity() * 4);
                add(
                    "neighbor_pred(ids)",
                    ctx.neighbor_pred.len(),
                    ctx.neighbor_pred.capacity() * 4 + ctx.neighbor_pred_seen.len() * 12,
                );
                add(
                    "trigger_sets",
                    ctx.trigger_sets.values().map(|s| s.len()).sum::<usize>()
                        + ctx.fact_trigger_sets.values().map(|s| s.len()).sum::<usize>(),
                    ctx.trigger_sets.values().map(|s| 24 + s.len() * (szp + 8)).sum::<usize>()
                        + ctx.fact_trigger_sets.values().map(|s| 24 + s.len() * (szp + 8)).sum::<usize>(),
                );
                add(
                    "predecessor_edges(pushed)",
                    ctx.predecessors.values().map(|s| s.len()).sum(),
                    ctx.predecessors.values().map(|s| 24 + s.len() * (szp + 8)).sum(),
                );
                add("pushed_succ", ctx.pushed_succ.len(), ctx.pushed_succ.len() * (szp + 8));
                add(
                    "pushed_pred(idx)",
                    ctx.pushed_pred.values().map(|s| s.len()).sum(),
                    ctx.pushed_pred.values().map(|s| 40 + s.len() * 12).sum(),
                );
                add("pred_pool(ids)", ctx.pred_pool.len(), ctx.pred_pool.capacity() * 4);
                add("succ_pool(ids)", ctx.succ_pool.len(), ctx.succ_pool.capacity() * 4);
                add(
                    "edges_misc",
                    ctx.successors.len() + ctx.edge_seen.len(),
                    ctx.successors.len() * 24 + ctx.edge_seen.len() * 32,
                );
            }
            add(
                "core_index(engine)",
                self.core_index.len(),
                self.core_index.keys().map(|k| 24 + k.capacity() * szp + 8).sum(),
            );
            add(
                "pred_interned(engine)",
                self.pred_interned.len(),
                self.pred_interned.capacity() * 48
                    + self.pred_interned.iter()
                        .map(|p| (p.body.capacity() + p.head.capacity()) * szp)
                        .sum::<usize>()
                    + self.pred_intern_idx.len() * 40
                    + self.pred_intern_idx.values().map(|v| v.capacity() * 4).sum::<usize>(),
            );
            add(
                "cc_arena(engine)",
                self.cc_arena[0].len() + self.cc_arena[1].len(),
                self.cc_arena.iter()
                    .map(|a| a.capacity() * szcc + a.iter().map(&cc_heap).sum::<usize>())
                    .sum::<usize>()
                    + self.cc_intern_idx.iter()
                        .map(|m| m.len() * 40 + m.values().map(|v| v.capacity() * 4).sum::<usize>())
                        .sum::<usize>(),
            );
            cat.sort_by(|a, b| b.2.cmp(&a.2));
            let total: usize = cat.iter().map(|e| e.2).sum();
            eprintln!(
                "KM_MEMSTATS sizeof Pred={} Lit={} ContextClause={} | contexts={} | accounted={:.1} MB",
                szp, szl, szcc, self.contexts.len(), total as f64 / 1e6
            );
            for (name, n, b) in &cat {
                eprintln!(
                    "KM_MEMSTATS {:>9.1} MB {:>5.1}% n={:<12} {}",
                    *b as f64 / 1e6,
                    100.0 * *b as f64 / total.max(1) as f64,
                    n,
                    name
                );
            }
        }
        if std::env::var("SROIQ_DEBUG").is_ok() {
            for ctx in &self.contexts {
                let arena = &self.cc_arena[ctx.root as usize];
                eprintln!(
                    "ctx {} root={} core={:?} #wo={}",
                    ctx.id, ctx.root, ctx.core, ctx.worked_off.len()
                );
                for &ci in &ctx.worked_off {
                    let c = &arena[ci as usize];
                    eprintln!("    {:?} -> {:?}", c.body, c.head);
                }
            }
        }
    }

    // ------------------------------ output ---------------------------------

    /// For each root context (core = {A(x)}), the entailed atomic subsumptions
    /// `A ⊑ B`: clauses `-> B(x)` (empty body, single head concept on x).
    pub fn subsumptions(&self) -> Vec<(String, Vec<String>)> {
        let mut out = Vec::new();
        for ctx in &self.contexts {
            if !ctx.root {
                continue;
            }
            let a = match ctx.query {
                Some(iri) => self.sig.concept_names[iri as usize].clone(),
                None => continue,
            };
            let arena = &self.cc_arena[ctx.root as usize];
            let mut supers: Vec<String> = Vec::new();
            let unsat = ctx.worked_off.iter().any(|&ci| {
                let c = &arena[ci as usize];
                c.body.is_empty() && c.head.is_empty()
            });
            if unsat {
                supers.push("owl:Nothing".to_string());
            }
            for &ci in &ctx.worked_off {
                let c = &arena[ci as usize];
                if c.body.is_empty() && c.head.len() == 1 {
                    if let Lit::P(Pred::Concept { iri, t }) = c.head[0] {
                        if is_central(t) {
                            let name = self.sig.concept_names[iri as usize].clone();
                            if name != a {
                                supers.push(name);
                            }
                        }
                    }
                }
            }
            supers.sort();
            supers.dedup();
            out.push((a, supers));
        }
        out.sort();
        out
    }

    pub fn inconsistent(&self) -> bool {
        // The ontology is inconsistent iff the ⊤ (empty-core) context derives the
        // empty clause: a generic element is forced into a contradiction, so there
        // is no model. Checking the ⊤ context (seeded in `run_for`) rather than a
        // concept literally named owl:Thing makes this independent of the input
        // vocabulary (the normaliser maps owl:Thing to an internal proxy, so the
        // old name-based check was effectively dead — audit M2).
        // The ground context derives the empty clause when the individuals
        // alone are contradictory (e.g. {o} ⊑ B, {o} ⊑ C, B ⊓ C ⊑ ⊥) — the
        // individuals exist in every model, so that too is global
        // inconsistency.
        let arena = &self.cc_arena[1];
        let top_bot = self.contexts.iter().any(|ctx| {
            ctx.root
                && ctx.core.is_empty()
                && ctx.worked_off.iter().any(|&ci| {
                    let c = &arena[ci as usize];
                    c.body.is_empty() && c.head.is_empty()
                })
        });
        if top_bot {
            return true;
        }
        if let Some(gid) = self.ground_ctx {
            let ctx = &self.contexts[gid];
            let arena = &self.cc_arena[ctx.root as usize];
            return ctx.worked_off.iter().any(|&ci| {
                let c = &arena[ci as usize];
                c.body.is_empty() && c.head.is_empty()
            });
        }
        false
    }

    pub fn num_contexts(&self) -> usize {
        self.contexts.len()
    }

}

#[cfg(test)]
mod tests {
    use super::*;

    fn cx(iri: Iri, t: Term) -> Pred {
        Pred::Concept { iri, t }
    }
    fn rl(iri: Iri, s: Term, t: Term) -> Pred {
        Pred::Role { iri, s, t }
    }

    fn supers_of(e: &Engine, name: &str) -> Vec<String> {
        e.subsumptions()
            .into_iter()
            .find(|(n, _)| n == name)
            .map(|(_, v)| v)
            .unwrap_or_default()
    }

    /// arXiv:1805.01396 Example 3 — the O+I+Q interaction that needs the Nom
    /// rule (additional nominals): A ⊑ ∃R.B1 ⊓ ∃R.B2, every B1/B2 element has
    /// an incoming S-edge from o, S is functional, ∃R.(B1⊓B2) ⊑ C.  Both
    /// anonymous R-successors of an A-element are S-successors of o, hence
    /// merged by functionality into one element (the additional nominal),
    /// which is then B1 ⊓ B2, so A ⊑ C.
    #[test]
    fn nom_rule_oiq_example3() {
        let mut sig = Sig::default();
        let a = sig.concept("A");
        let b1 = sig.concept("B1");
        let b2 = sig.concept("B2");
        let c = sig.concept("C");
        let rr = sig.role("R");
        let ss = sig.role("S");
        let o = ind_term(1);
        let f = fterm(1);
        let g = fterm(2);
        let clauses = vec![
            OntologyClause::new(vec![cx(a, X)], vec![Lit::P(rl(rr, X, f))]),
            OntologyClause::new(vec![cx(a, X)], vec![Lit::P(cx(b1, f))]),
            OntologyClause::new(vec![cx(a, X)], vec![Lit::P(rl(rr, X, g))]),
            OntologyClause::new(vec![cx(a, X)], vec![Lit::P(cx(b2, g))]),
            OntologyClause::new(vec![cx(b1, X)], vec![Lit::P(rl(ss, o, X))]),
            OntologyClause::new(vec![cx(b2, X)], vec![Lit::P(rl(ss, o, X))]),
            // functionality of S: S(x,z1) ∧ S(x,z2) → z1 ≈ z2
            OntologyClause::new(
                vec![rl(ss, X, zvar(1)), rl(ss, X, zvar(2))],
                vec![Lit::eq(zvar(1), zvar(2))],
            ),
            // ∃R.(B1 ⊓ B2) ⊑ C
            OntologyClause::new(
                vec![rl(rr, zvar(1), X), cx(b1, X), cx(b2, X)],
                vec![Lit::P(cx(c, zvar(1)))],
            ),
        ];
        let mut e = Engine::new(sig, clauses, 0);
        e.run_for(&[a]);
        let sups = supers_of(&e, "A");
        assert!(
            sups.contains(&"C".to_string()),
            "expected A ⊑ C via the Nom rule, got {:?}",
            sups
        );
        assert!(!e.inconsistent());
    }

    /// Negative control for Nom: without the functionality clause the two
    /// successors need not merge, so A ⊑ C must NOT be derived.
    #[test]
    fn nom_rule_no_counting_no_merge() {
        let mut sig = Sig::default();
        let a = sig.concept("A");
        let b1 = sig.concept("B1");
        let b2 = sig.concept("B2");
        let c = sig.concept("C");
        let rr = sig.role("R");
        let ss = sig.role("S");
        let o = ind_term(1);
        let f = fterm(1);
        let g = fterm(2);
        let clauses = vec![
            OntologyClause::new(vec![cx(a, X)], vec![Lit::P(rl(rr, X, f))]),
            OntologyClause::new(vec![cx(a, X)], vec![Lit::P(cx(b1, f))]),
            OntologyClause::new(vec![cx(a, X)], vec![Lit::P(rl(rr, X, g))]),
            OntologyClause::new(vec![cx(a, X)], vec![Lit::P(cx(b2, g))]),
            OntologyClause::new(vec![cx(b1, X)], vec![Lit::P(rl(ss, o, X))]),
            OntologyClause::new(vec![cx(b2, X)], vec![Lit::P(rl(ss, o, X))]),
            OntologyClause::new(
                vec![rl(rr, zvar(1), X), cx(b1, X), cx(b2, X)],
                vec![Lit::P(cx(c, zvar(1)))],
            ),
        ];
        let mut e = Engine::new(sig, clauses, 0);
        e.run_for(&[a]);
        let sups = supers_of(&e, "A");
        assert!(
            !sups.contains(&"C".to_string()),
            "A ⊑ C must not be derived without functionality, got {:?}",
            sups
        );
        assert!(!e.inconsistent());
    }

    /// Filler-merge through a nominal (the Phase-1 witness, engine-level):
    /// A ⊑ ∃r.({o}⊓B), A ⊑ ∃r.({o}⊓C), B⊓C ⊑ E, ∃r.E ⊑ G entails A ⊑ G.
    /// Clausified with individuals as constants (DL8 for the {o} conjuncts:
    /// the filler definers imply x ≈ o).
    #[test]
    fn nominal_filler_merge() {
        let mut sig = Sig::default();
        let a = sig.concept("A");
        let b = sig.concept("B");
        let c = sig.concept("C");
        let ee = sig.concept("E");
        let g = sig.concept("G");
        let d1 = sig.concept("__d1");
        let d2 = sig.concept("__d2");
        let r = sig.role("r");
        let o = ind_term(1);
        let f1 = fterm(1);
        let f2 = fterm(2);
        let clauses = vec![
            OntologyClause::new(vec![cx(a, X)], vec![Lit::P(rl(r, X, f1))]),
            OntologyClause::new(vec![cx(a, X)], vec![Lit::P(cx(d1, f1))]),
            OntologyClause::new(vec![cx(a, X)], vec![Lit::P(rl(r, X, f2))]),
            OntologyClause::new(vec![cx(a, X)], vec![Lit::P(cx(d2, f2))]),
            // definers: __d1 ⊑ {o} ⊓ B, __d2 ⊑ {o} ⊓ C
            OntologyClause::new(vec![cx(d1, X)], vec![Lit::eq(X, o)]),
            OntologyClause::new(vec![cx(d1, X)], vec![Lit::P(cx(b, X))]),
            OntologyClause::new(vec![cx(d2, X)], vec![Lit::eq(X, o)]),
            OntologyClause::new(vec![cx(d2, X)], vec![Lit::P(cx(c, X))]),
            OntologyClause::new(vec![cx(b, X), cx(c, X)], vec![Lit::P(cx(ee, X))]),
            OntologyClause::new(
                vec![rl(r, X, zvar(1)), cx(ee, zvar(1))],
                vec![Lit::P(cx(g, X))],
            ),
        ];
        let mut e = Engine::new(sig, clauses, 0);
        e.run_for(&[a]);
        let sups = supers_of(&e, "A");
        assert!(
            sups.contains(&"G".to_string()),
            "expected A ⊑ G via nominal filler merge, got {:?}",
            sups
        );
        assert!(!e.inconsistent());
    }

    /// ABox + nominal unsat: C(o) asserted, B ⊑ {o}, B ⊓ owl-disjoint with C
    /// via B(x) ∧ C(x) → ⊥, and A ⊑ ∃r.B forces the successor to BE o, which
    /// is both B and C — A is unsatisfiable.
    #[test]
    fn nominal_ground_clash() {
        let mut sig = Sig::default();
        let a = sig.concept("A");
        let b = sig.concept("B");
        let c = sig.concept("C");
        let r = sig.role("r");
        let o = ind_term(1);
        let f = fterm(1);
        let clauses = vec![
            OntologyClause::new(vec![], vec![Lit::P(cx(c, o))]),
            OntologyClause::new(vec![cx(a, X)], vec![Lit::P(rl(r, X, f))]),
            OntologyClause::new(vec![cx(a, X)], vec![Lit::P(cx(b, f))]),
            OntologyClause::new(vec![cx(b, X)], vec![Lit::eq(X, o)]),
            OntologyClause::new(vec![cx(b, X), cx(c, X)], vec![]),
        ];
        let mut e = Engine::new(sig, clauses, 0);
        e.run_for(&[a]);
        let sups = supers_of(&e, "A");
        assert!(
            sups.contains(&"owl:Nothing".to_string()),
            "expected A unsatisfiable (successor is o, which is C and B), got {:?}",
            sups
        );
    }
}
