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
}
impl CentralSubst {
    fn new() -> Self {
        CentralSubst { map: HashMap::new() }
    }
    fn add(&mut self, i: Term, o: Term) -> bool {
        if is_central(i) {
            return o == X;
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
        if v == X || is_function(v) {
            v
        } else {
            *self.map.get(&v).unwrap_or(&v)
        }
    }
}

/// Forward inter-context mapping for Succ: {f(x) -> x, x -> y}.
fn forwards(f: Term, v: Term) -> Term {
    if v == f {
        X
    } else if v == X {
        Y
    } else {
        // neighbour/other terms do not occur in a succ trigger predicate
        v
    }
}
/// Backward inter-context substitution for Pred: {y -> x, x -> f(x)}.
fn backwards(f: Term, v: Term) -> Term {
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
    match (body, head_max) {
        (Pred::Concept { iri: i1, t: t1 }, Pred::Concept { iri: i2, t: t2 }) => {
            // A central body term must match a central head term; a neighbour
            // body term (e.g. C(y) in `R(x,y) ∧ C(y) -> D(x)`) may bind to any
            // head term, including a function term C(f(x)).  (Pure syntactic
            // unification — sound regardless of the body term's role.)
            i1 == i2 && (!is_central(*t1) || is_central(*t2))
        }
        (Pred::Role { iri: i1, s: s1, t: t1 }, Pred::Role { iri: i2, s: s2, t: t2 }) => {
            i1 == i2
                && (!is_central(*s1) || is_central(*s2))
                && (!is_central(*t1) || is_central(*t2))
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
    facts: Vec<usize>,               // indices of empty-body clauses
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
    worked_off: Vec<ContextClause>,
    clause_keys: HashSet<(Vec<Pred>, Vec<Lit>)>,
    /// Index from a head-predicate iri to the (ascending, de-duplicated)
    /// `worked_off` indices of clauses having a *maximal* head predicate with
    /// that iri.  Lets Hyper/Pred find resolution partners without scanning all
    /// of `worked_off`.  Concept and role iris live in separate namespaces, so
    /// they are indexed separately; `can_unify` / exact-predicate tests still
    /// filter precisely, so the candidate set (and its order) is unchanged.
    head_concept_index: HashMap<Iri, Vec<usize>>,
    head_role_index: HashMap<Iri, Vec<usize>>,
    /// Subsumption index over `worked_off`: each clause is recorded under every
    /// literal of its head.  A clause `c` can subsume `clause` only if
    /// `c.head ⊆ clause.head`, so every true subsumer with a non-empty head is
    /// found under some literal of `clause.head`; conversely `clause` can
    /// subsume only clauses that contain *all* of `clause.head`, i.e. those in
    /// the intersection of these lists.  Empty-head clauses (which subsume on
    /// the body alone) are tracked separately.  This replaces the per-`add`
    /// linear scan of `worked_off` for both forward and backward subsumption.
    head_lit_index: HashMap<Lit, Vec<usize>>,
    empty_head_wo: Vec<usize>,
    todo: VecDeque<ContextClause>,
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
    pred_pool: Vec<ContextClause>,
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
    succ_pool: Vec<ContextClause>,
    succ_hwm: usize,
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
            predecessors: HashMap::new(),
            pushed_succ: HashSet::new(),
            pushed_pred: HashMap::new(),
            pred_pool: Vec::new(),
            pred_hwm: 0,
            edge_seen: HashMap::new(),
            succ_pool: Vec::new(),
            succ_hwm: 0,
            dirty: true,
        }
    }

    /// Add the `worked_off[idx]` clause to the head-predicate index, recording
    /// `idx` once per distinct iri appearing among its maximal head predicates
    /// (the per-clause predicate list is re-scanned at lookup time, so a single
    /// entry per iri reproduces the original candidate sequence without
    /// duplicates).  Appending in increasing `idx` keeps each list sorted.
    fn index_clause(&mut self, idx: usize) {
        let mut concept_iris: Vec<Iri> = Vec::new();
        let mut role_iris: Vec<Iri> = Vec::new();
        for (p, _) in self.worked_off[idx].max_head_predicates() {
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
            self.head_concept_index.entry(iri).or_default().push(idx);
        }
        for iri in role_iris {
            self.head_role_index.entry(iri).or_default().push(idx);
        }
        // subsumption index: record under every head literal (or the empty-head
        // list).  Heads are small, so the clone is cheap and avoids a borrow on
        // `self.worked_off` while mutating the maps.
        let head = self.worked_off[idx].head.clone();
        if head.is_empty() {
            self.empty_head_wo.push(idx);
        } else {
            for l in head {
                self.head_lit_index.entry(l).or_default().push(idx);
            }
        }
    }

    /// Rebuild every `worked_off` index from scratch.  Called after
    /// back-subsumption physically removes clauses from `worked_off` (which
    /// shifts the indices the maps refer to); removals are comparatively rare,
    /// so a full rebuild keeps the common (append-only) path fast.
    fn rebuild_head_index(&mut self) {
        self.head_concept_index.clear();
        self.head_role_index.clear();
        self.head_lit_index.clear();
        self.empty_head_wo.clear();
        for idx in 0..self.worked_off.len() {
            self.index_clause(idx);
        }
    }

    /// Forward subsumption: is `clause` subsumed by some existing clause in
    /// `worked_off` or `todo`?  `worked_off` is consulted via the head-literal
    /// index (every non-empty-head subsumer shares a head literal with
    /// `clause`); `todo` is scanned linearly (it is the small work queue).
    /// The `(nb, nh)` length pre-filter skips clauses that cannot subsume.
    fn fwd_subsumed(&self, clause: &ContextClause, nb: usize, nh: usize) -> bool {
        for &ci in &self.empty_head_wo {
            let c = &self.worked_off[ci];
            if c.body.len() <= nb && c.test_strengthening(clause) == -1 {
                return true;
            }
        }
        for l in &clause.head {
            if let Some(cands) = self.head_lit_index.get(l) {
                for &ci in cands {
                    let c = &self.worked_off[ci];
                    if c.body.len() <= nb && c.head.len() <= nh && c.test_strengthening(clause) == -1 {
                        return true;
                    }
                }
            }
        }
        for c in &self.todo {
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
    fn back_subsume(&mut self, clause: &ContextClause, nb: usize, nh: usize, key: &(Vec<Pred>, Vec<Lit>)) {
        // ---- worked_off ----
        let mut remove_wo: Vec<usize> = Vec::new();
        if clause.head.is_empty() {
            for ci in 0..self.worked_off.len() {
                let c = &self.worked_off[ci];
                if c.body.len() >= nb && c.head.len() >= nh && clause.test_strengthening(c) == -1 && &c.key() != key {
                    remove_wo.push(ci);
                }
            }
        } else {
            // smallest head-literal list (None if some head literal is absent,
            // in which case no clause contains all of `clause.head`).
            let mut best: Option<&Vec<usize>> = None;
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
                    let c = &self.worked_off[ci];
                    if c.body.len() >= nb && c.head.len() >= nh && clause.test_strengthening(c) == -1 && &c.key() != key {
                        remove_wo.push(ci);
                    }
                }
            }
        }
        if !remove_wo.is_empty() {
            let remove_set: HashSet<usize> = remove_wo.into_iter().collect();
            let old = std::mem::take(&mut self.worked_off);
            let mut new_wo = Vec::with_capacity(old.len() - remove_set.len());
            for (ci, c) in old.into_iter().enumerate() {
                if remove_set.contains(&ci) {
                    self.clause_keys.remove(&c.key());
                } else {
                    new_wo.push(c);
                }
            }
            self.worked_off = new_wo;
            self.rebuild_head_index();
        }
        // ---- todo (not indexed) ----
        let mut todo = std::mem::take(&mut self.todo);
        todo.retain(|c| {
            if c.body.len() >= nb && c.head.len() >= nh && clause.test_strengthening(c) == -1 && &c.key() != key {
                self.clause_keys.remove(&c.key());
                false
            } else {
                true
            }
        });
        self.todo = todo;
    }
}

/// A pred clause (substitution already applied): body and head over x / f(x).
#[derive(Clone, PartialEq, Eq, Hash)]
struct PredClause {
    body: Vec<Pred>,
    head: Vec<Pred>,
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
    shared_closure: Option<Vec<ContextClause>>,
    /// Same idea as `shared_closure` but under the *root* literal ordering
    /// (`root=true`): the facts+TBox closure of an empty-core root context.
    /// Seeded into every query root context (core `{A(x)}`) so the shared TBox
    /// reasoning is computed once rather than per classified concept.  Root and
    /// non-root orderings differ (query concepts are mutually incomparable at a
    /// root), so the two closures are kept separate and never crossed.
    shared_root_closure: Option<Vec<ContextClause>>,
    equality: bool,
    /// Intern table for back-substituted pred clauses: one copy per distinct
    /// content, shared across all receiving contexts (`Context.neighbor_pred`
    /// stores ids).  The same clause shape recurs across thousands of contexts
    /// on role-chain ontologies, where the per-context copies dominated peak
    /// memory.  Append-only; ids are stable.
    pred_interned: Vec<PredClause>,
    /// content hash -> candidate ids (collisions resolved by exact comparison)
    pred_intern_idx: HashMap<u64, Vec<u32>>,
    pub dropped_unsupported: usize,
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
                ont.facts.push(idx);
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
        Engine {
            sig,
            ont,
            contexts: Vec::new(),
            core_index: HashMap::new(),
            msgs: VecDeque::new(),
            successor_ctxs: HashMap::new(),
            central_index: HashMap::new(),
            central: std::env::var_os("KM_NO_CENTRAL").is_none(),
            shared_closure: None,
            shared_root_closure: None,
            equality: true,
            pred_interned: Vec::new(),
            pred_intern_idx: HashMap::new(),
            dropped_unsupported: dropped,
            stat_propagate: 0,
            stat_pred_checks: 0,
            stat_succ_scans: 0,
            stat_saturate: 0,
        }
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
        let root = self.contexts[id].root;
        let facts: Vec<usize> = self.ont.facts.clone();
        for fi in facts {
            let head = self.ont.clauses[fi].head.clone();
            // apply identity (facts have no neighbour vars); filter invalid eqs / nothing
            let head = self.filter_head(head);
            if let Some(head) = head {
                let c = ContextClause::new(vec![], head, root, &self.sig);
                self.add_clause(id, c);
            }
        }
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
        let key = clause.key();
        let ctx = &mut self.contexts[id];
        if ctx.clause_keys.contains(&key) {
            return false;
        }
        let (nb, nh) = (clause.body.len(), clause.head.len());
        // Forward subsumption: skip if some existing clause subsumes `clause`.
        if ctx.fwd_subsumed(&clause, nb, nh) {
            return false;
        }
        // Back-subsumption: drop existing clauses that `clause` strengthens.
        ctx.back_subsume(&clause, nb, nh, &key);
        ctx.clause_keys.insert(key);
        ctx.todo.push_back(clause);
        true
    }

    /// Saturate a single context (apply Hyper/Pred/Eq until todo is empty).
    fn saturate(&mut self, id: usize) {
        self.stat_saturate += 1;
        let trace_sat = std::env::var("KM_SAT").is_ok();
        let prof = std::env::var("KM_PROF").is_ok();
        let (mut iters, mut subsumed, mut nhyper, mut npred, mut neqp, mut neqe, mut nfact, mut nadded) =
            (0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64);
        loop {
            let clause = match self.contexts[id].todo.pop_front() {
                Some(c) => c,
                None => break,
            };
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
                let (nb, nh) = (clause.body.len(), clause.head.len());
                if ctx.fwd_subsumed(&clause, nb, nh) {
                    self.contexts[id].clause_keys.remove(&clause.key());
                    if prof { subsumed += 1; }
                    continue;
                }
            }
            let root = self.contexts[id].root;
            // Fire rules per maximal head literal.
            let max_head = clause.max_head.clone();
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
            let ctx = &mut self.contexts[id];
            let idx = ctx.worked_off.len();
            // Feed the semi-naive propagation pools (append-only).  Pred-eligible:
            // function-free, predicate-only head (mirrors the filter in
            // `propagate`'s Pred section).  Succ-eligible: some maximal head
            // predicate is on a function term (succ-trigger candidate).
            let pred_eligible = clause
                .head
                .iter()
                .all(|l| l.is_function_free() && matches!(l, Lit::P(_)));
            let succ_eligible = clause
                .max_head_predicates()
                .any(|(p, _)| is_function(p.max_term()));
            if pred_eligible {
                ctx.pred_pool.push(clause.clone());
            }
            if succ_eligible {
                ctx.succ_pool.push(clause.clone());
            }
            ctx.worked_off.push(clause);
            ctx.index_clause(idx);
            ctx.dirty = true;
            if trace_sat {
                let c = &self.contexts[id];
                let wl = c.worked_off.len();
                if wl % 10000 == 0 {
                    let maxb = c.worked_off.iter().map(|cl| cl.body.len()).max().unwrap_or(0);
                    let maxh = c.worked_off.iter().map(|cl| cl.head.len()).max().unwrap_or(0);
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
                            for (p, _) in ctx.worked_off[ci].max_head_predicates() {
                                if can_unify(&oc.body[i], &p) {
                                    v.push((ci, p));
                                }
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
            let sigma = CentralSubst::new();
            self.hyper_join(id, side, oc, &candidates, &order, 0, &sigma, &mut chosen, root, &mut out);
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
            if unify(&mut s2, &oc.body[pos], &p) {
                chosen[pos] = j;
                self.hyper_join(id, side, oc, candidates, order, depth + 1, &s2, chosen, root, out);
            }
        }
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
        let ctx = &self.contexts[id];
        let subst = |t: Term| sigma.apply(t);
        // head: ontology head substituted, filtered
        let mut head: Vec<Lit> = Vec::new();
        for l in &oc.head {
            let ls = l.apply(&subst);
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
        // plus each candidate clause's head minus the matched predicate
        let mut body: Vec<Pred> = Vec::new();
        for i in 0..candidates.len() {
            let (ci, matched) = candidates[i][idxs[i]];
            let clause = if ci == usize::MAX { side } else { &ctx.worked_off[ci] };
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
        for &pid in &ctx.neighbor_pred {
            let pc = &self.pred_interned[pid as usize];
            if !pc.body.iter().any(|b| *b == max) {
                continue;
            }
            // For each body predicate, candidate clauses with that predicate
            // maximal in head; `max` is provided by `side`.
            let n = pc.body.len();
            let mut candidates: Vec<Vec<(usize, Pred)>> = Vec::with_capacity(n);
            let mut ok = true;
            for i in 0..n {
                let bp = pc.body[i];
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
                        if ctx.worked_off[ci].max_head_predicates().any(|(p, _)| p == bp) {
                            v.push((ci, bp));
                        }
                    }
                }
                if v.is_empty() {
                    ok = false;
                    break;
                }
                candidates.push(v);
            }
            if !ok {
                continue;
            }
            let mut idxs = vec![0usize; n];
            loop {
                if let Some(c) = self.build_pred_resolvent(id, side, pc, &candidates, &idxs, root) {
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
        candidates: &[Vec<(usize, Pred)>],
        idxs: &[usize],
        root: bool,
    ) -> Option<ContextClause> {
        let ctx = &self.contexts[id];
        let mut head: Vec<Lit> = pc.head.iter().map(|p| Lit::P(*p)).collect();
        let mut body: Vec<Pred> = Vec::new();
        for i in 0..candidates.len() {
            let (ci, matched) = candidates[i][idxs[i]];
            let clause = if ci == usize::MAX { side } else { &ctx.worked_off[ci] };
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
        let mterm = max.max_term();
        for c in &ctx.worked_off {
            for l in &c.max_head {
                if let Lit::Eq { s, t } = *l {
                    if s == mterm && max.contains_at_rewrite_position(s) {
                        if let Some(res) = self.build_eq(side, max, c, s, t, *l, root) {
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
        let s = match max {
            Lit::Eq { s, .. } | Lit::Ineq { s, .. } => s,
            _ => return out,
        };
        for c in &ctx.worked_off {
            for l in &c.max_head {
                if l.contains_at_rewrite_position(s) && *l != max {
                    if let Lit::Eq { s: es, t: et } = max {
                        // side provides equality es==et, rewrite l
                        if let Some(res) = self.build_eq(c, *l, side, es, et, max, root) {
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
    fn seed_worked_off(&mut self, id: usize, clause: ContextClause) {
        let ctx = &mut self.contexts[id];
        let key = clause.key();
        if ctx.clause_keys.contains(&key) {
            return;
        }
        ctx.clause_keys.insert(key);
        let pred_eligible = clause
            .head
            .iter()
            .all(|l| l.is_function_free() && matches!(l, Lit::P(_)));
        let succ_eligible = clause
            .max_head_predicates()
            .any(|(p, _)| is_function(p.max_term()));
        if pred_eligible {
            ctx.pred_pool.push(clause.clone());
        }
        if succ_eligible {
            ctx.succ_pool.push(clause.clone());
        }
        let idx = ctx.worked_off.len();
        ctx.worked_off.push(clause);
        ctx.index_clause(idx);
        ctx.dirty = true;
    }

    /// `true` if context `sid` has derived concept `iri` on its central
    /// variable as an unconditional fact (`⊤ → iri(x)`).  Used by the
    /// redundant-trigger skip to detect a push-back the successor already knows.
    fn ctx_derives_central(&self, sid: usize, iri: Iri) -> bool {
        let ctx = &self.contexts[sid];
        if let Some(idxs) = ctx.head_concept_index.get(&iri) {
            for &ci in idxs {
                let c = &ctx.worked_off[ci];
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
        let mut new_succ: Vec<Pred> = Vec::new();
        let succ_start = self.contexts[id].succ_hwm;
        self.stat_succ_scans += (self.contexts[id].succ_pool.len() - succ_start) as u64;
        {
            let ctx = &self.contexts[id];
            for c in &ctx.succ_pool[succ_start..] {
                for (p, _) in c.max_head_predicates() {
                    if is_function(p.max_term())
                        && p.is_succ_trigger(&self.sig)
                        && !ctx.pushed_succ.contains(&p)
                    {
                        new_succ.push(p);
                    }
                }
            }
        }
        self.contexts[id].succ_hwm = self.contexts[id].succ_pool.len();
        if !self.central {
            // Legacy pay-as-you-go strategy: one empty-core successor per `f`.
            for p in new_succ {
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
                    for p in &new_succ {
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
                for p in new_succ {
                    // Always mark pushed so we never re-process this trigger.
                    ctx.pushed_succ.insert(p);
                    if redundant.contains(&p) {
                        continue; // redundant push-back: do not grow the core
                    }
                    let f = p.max_term();
                    ctx.trigger_sets.entry(f).or_default().insert(p);
                    if !grew.contains(&f) {
                        grew.push(f);
                    }
                }
            }
            for f in grew {
                let raw: Vec<Pred> = self.contexts[id].trigger_sets[&f].iter().copied().collect();
                let mut core: Vec<Pred> = raw.iter().map(|p| p.apply(&|v| forwards(f, v))).collect();
                core.sort();
                core.dedup();
                let target = self.central_successor_for_core(core);
                let prev = self.contexts[id].successors.insert(f, target);
                // New target (first push or grown set): send the full set so the
                // new context's edge records every pushed predicate.  (A new raw
                // trigger always changes the σ-image, so `prev == Some(target)`
                // only happens if nothing changed — nothing to send then.)
                if prev != Some(target) {
                    for p in &raw {
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
        let new_edge_seen: Vec<((usize, Term), usize)>;
        {
            let ctx = &self.contexts[id];
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
            for (i, c) in ctx.pred_pool.iter().enumerate() {
                let new_clause = i >= hwm;
                for (edge, pushed, dirty_edge) in &edges {
                    // (old clause, unchanged edge): already checked at this
                    // edge's pushed-length — skip.
                    if !new_clause && !*dirty_edge {
                        continue;
                    }
                    pred_checks += 1;
                    if c.body.iter().all(|b| pushed.contains(b)) {
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
        // under the central strategy the hypothesis is subsumed by the core's
        // `-> p` (so add_clause returns false), but the core clauses seeded at
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
        // Back-substitute: y -> x, x -> f(x).  The sender's pool entry and core
        // are immutable once created, so resolving them here reads exactly the
        // snapshot a send-time copy would have carried.
        let pc = {
            let from_ctx = &self.contexts[from];
            let clause = &from_ctx.pred_pool[pool_idx as usize];
            let f = edge_label;
            let subst = |v: Term| backwards(f, v);
            let mut body: Vec<Pred> = clause.body.iter().map(|p| p.apply(&subst)).collect();
            for p in &from_ctx.core {
                body.push(p.apply(&subst));
            }
            let head: Vec<Pred> = clause
                .head
                .iter()
                .filter_map(|l| match l {
                    Lit::P(p) => Some(p.apply(&subst)),
                    _ => None,
                })
                .collect();
            PredClause { body, head }
        };
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

    /// Pred rule for a freshly received neighbor pred clause: resolve all its
    /// body predicates against worked-off clauses of context `id`.
    fn pred_from_neighbor(&self, id: usize, pc: &PredClause, root: bool) -> Vec<ContextClause> {
        let mut out = Vec::new();
        let ctx = &self.contexts[id];
        let n = pc.body.len();
        let mut candidates: Vec<Vec<(usize, Pred)>> = Vec::with_capacity(n);
        for i in 0..n {
            let bp = pc.body[i];
            let mut v = Vec::new();
            let cand = match bp {
                Pred::Concept { iri, .. } => ctx.head_concept_index.get(&iri),
                Pred::Role { iri, .. } => ctx.head_role_index.get(&iri),
            };
            if let Some(cand) = cand {
                for &ci in cand {
                    if ctx.worked_off[ci].max_head_predicates().any(|(p, _)| p == bp) {
                        v.push((ci, bp));
                    }
                }
            }
            if v.is_empty() {
                return out; // a body predicate has no provider: no resolvent
            }
            candidates.push(v);
        }
        let mut idxs = vec![0usize; n];
        loop {
            // build resolvent (no side clause; all from worked-off)
            let mut head: Vec<Lit> = pc.head.iter().map(|p| Lit::P(*p)).collect();
            let mut body: Vec<Pred> = Vec::new();
            for i in 0..n {
                let (ci, matched) = candidates[i][idxs[i]];
                let clause = &ctx.worked_off[ci];
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
                    eprintln!(
                        "KM_PROF msgloop guard={} contexts={} msgs_pending={} saturate_calls={}",
                        guard, self.contexts.len(), self.msgs.len(), self.stat_saturate
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
                        totwo += c.worked_off.len();
                        if c.worked_off.len() > topwo { topwo = c.worked_off.len(); }
                        for cl in &c.worked_off {
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
                    Msg::Succ { from, f, p, target } => self.apply_succ(from, f, p, target),
                    Msg::Pred {
                        to,
                        from,
                        edge_label,
                        pool_idx,
                    } => self.apply_pred(to, from, edge_label, pool_idx),
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
                for c in &ctx.worked_off {
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
                let touch = ctx.core.iter().any(&hit)
                    || ctx.worked_off.iter().any(|c| {
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
                for c in &ctx.worked_off {
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
                c.body.capacity() * szp + c.head.capacity() * szl + c.max_head.capacity() * szl
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
                    "worked_off(body+head)",
                    ctx.worked_off.len(),
                    ctx.worked_off.capacity() * szcc
                        + ctx.worked_off.iter()
                            .map(|c| c.body.capacity() * szp + c.head.capacity() * szl)
                            .sum::<usize>(),
                );
                add(
                    "worked_off(max_head dup)",
                    ctx.worked_off.iter().map(|c| c.max_head.len()).sum(),
                    ctx.worked_off.iter().map(|c| c.max_head.capacity() * szl).sum(),
                );
                add(
                    "clause_keys(full copies)",
                    ctx.clause_keys.len(),
                    ctx.clause_keys.iter()
                        .map(|(b, h)| 48 + b.capacity() * szp + h.capacity() * szl + 8)
                        .sum(),
                );
                add(
                    "head_indexes",
                    ctx.head_concept_index.len() + ctx.head_role_index.len() + ctx.head_lit_index.len(),
                    ctx.head_concept_index.values().map(|v| 24 + 4 + v.capacity() * 8).sum::<usize>()
                        + ctx.head_role_index.values().map(|v| 24 + 4 + v.capacity() * 8).sum::<usize>()
                        + ctx.head_lit_index.values().map(|v| 24 + szl + v.capacity() * 8).sum::<usize>(),
                );
                add(
                    "todo",
                    ctx.todo.len(),
                    ctx.todo.capacity() * szcc + ctx.todo.iter().map(&cc_heap).sum::<usize>(),
                );
                add(
                    "neighbor_pred(ids)",
                    ctx.neighbor_pred.len(),
                    ctx.neighbor_pred.capacity() * 4 + ctx.neighbor_pred_seen.len() * 12,
                );
                add(
                    "trigger_sets",
                    ctx.trigger_sets.values().map(|s| s.len()).sum(),
                    ctx.trigger_sets.values().map(|s| 24 + s.len() * (szp + 8)).sum(),
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
                add(
                    "pred_pool(full copies)",
                    ctx.pred_pool.len(),
                    ctx.pred_pool.capacity() * szcc
                        + ctx.pred_pool.iter().map(&cc_heap).sum::<usize>(),
                );
                add(
                    "succ_pool(full copies)",
                    ctx.succ_pool.len(),
                    ctx.succ_pool.capacity() * szcc
                        + ctx.succ_pool.iter().map(&cc_heap).sum::<usize>(),
                );
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
                eprintln!(
                    "ctx {} root={} core={:?} #wo={}",
                    ctx.id, ctx.root, ctx.core, ctx.worked_off.len()
                );
                for c in &ctx.worked_off {
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
            let mut supers: Vec<String> = Vec::new();
            let unsat = ctx.worked_off.iter().any(|c| c.body.is_empty() && c.head.is_empty());
            if unsat {
                supers.push("owl:Nothing".to_string());
            }
            for c in &ctx.worked_off {
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
        self.contexts.iter().any(|ctx| {
            ctx.root
                && ctx.core.is_empty()
                && ctx
                    .worked_off
                    .iter()
                    .any(|c| c.body.is_empty() && c.head.is_empty())
        })
    }

    pub fn num_contexts(&self) -> usize {
        self.contexts.len()
    }

}
