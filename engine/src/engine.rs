//! The disjunctive context calculus engine (single-threaded), a faithful port
//! of Sequoia's `context/Context.scala`, `context/Rules.scala`, and
//! `context/ContextState.scala`.
//!
//! Rules implemented: Core, Hyper, Pred, Succ, Eq, Ineq, Elim (redundancy).
//! Expansion strategy: the *trivial* strategy (all successors share one context
//! with empty core), which is sound and complete (Simančík et al.); it is the
//! simplest strategy that preserves the calculus's guarantees, at the cost of
//! pay-as-you-go efficiency.  Factor and full nominal rules (Nom/Join/r-Succ/
//! r-Pred of Table 3) are not implemented; clauses requiring them are reported.

use std::collections::{HashMap, HashSet, VecDeque};

use crate::calc::*;
use crate::clause::*;

// ----------------------------- substitutions -------------------------------

/// Central substitution used by Hyper: maps ontology variables (x, z_i) to
/// context terms.  `x -> x` always; function terms map to themselves.
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
    todo: VecDeque<ContextClause>,
    /// pred clauses pushed in from successor contexts (already back-substituted)
    neighbor_pred: Vec<PredClause>,
    /// successor edges: function term -> successor context id
    successors: HashMap<Term, usize>,
    /// predecessor edges: (predecessor ctx id, function term) -> pushed predicates
    predecessors: HashMap<(usize, Term), HashSet<Pred>>,
    pushed_succ: HashSet<Pred>,
    /// (predecessor key, clause key) already pushed back, to avoid resending
    pushed_pred: HashSet<((usize, Term), (Vec<Pred>, Vec<Lit>))>,
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
            todo: VecDeque::new(),
            neighbor_pred: Vec::new(),
            successors: HashMap::new(),
            predecessors: HashMap::new(),
            pushed_succ: HashSet::new(),
            pushed_pred: HashSet::new(),
        }
    }
}

/// A pred clause (substitution already applied): body and head over x / f(x).
#[derive(Clone)]
struct PredClause {
    body: Vec<Pred>,
    head: Vec<Pred>,
}

// ------------------------------- messages ----------------------------------

enum Msg {
    Succ {
        from: usize,
        f: Term,
        p: Pred, // already forward-substituted (over successor's x/y)
        target: usize,
    },
    Pred {
        to: usize,
        edge_label: Term,
        neighbour_core: Vec<Pred>,
        clause: ContextClause,
    },
}

// -------------------------------- engine -----------------------------------

pub struct Engine {
    pub sig: Sig,
    ont: Ontology,
    contexts: Vec<Context>,
    core_index: HashMap<Vec<Pred>, usize>,
    msgs: VecDeque<Msg>,
    successor_ctx: Option<usize>, // shared trivial-strategy successor
    equality: bool,
    pub dropped_unsupported: usize,
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
            successor_ctx: None,
            equality: true,
            dropped_unsupported: dropped,
        }
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
        self.init_context(id);
        id
    }

    /// Core rule + facts for a freshly created context, then schedule saturation.
    fn init_context(&mut self, id: usize) {
        let root = self.contexts[id].root;
        // Core rule
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
        // Facts: ontology clauses with empty body.
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
        // subsumption check against worked_off and todo
        let subsumed = ctx
            .worked_off
            .iter()
            .chain(ctx.todo.iter())
            .any(|c| c.test_strengthening(&clause) == -1);
        if subsumed {
            return false;
        }
        // remove clauses that `clause` strengthens
        let removed: Vec<(Vec<Pred>, Vec<Lit>)> = ctx
            .worked_off
            .iter()
            .chain(ctx.todo.iter())
            .filter(|c| clause.test_strengthening(c) == -1 && c.key() != key)
            .map(|c| c.key())
            .collect();
        for rk in &removed {
            ctx.clause_keys.remove(rk);
        }
        ctx.worked_off.retain(|c| !removed.contains(&c.key()));
        ctx.todo.retain(|c| !removed.contains(&c.key()));
        ctx.clause_keys.insert(key);
        ctx.todo.push_back(clause);
        true
    }

    /// Saturate a single context (apply Hyper/Pred/Eq until todo is empty).
    fn saturate(&mut self, id: usize) {
        loop {
            let clause = match self.contexts[id].todo.pop_front() {
                Some(c) => c,
                None => break,
            };
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
                        for r in results {
                            self.add_clause(id, r);
                        }
                        if is_function(p.max_term()) {
                            let results = self.pred_local(id, &clause, *p, root);
                            for r in results {
                                self.add_clause(id, r);
                            }
                            if self.equality {
                                let results = self.eq_from_pred(id, &clause, *max, root);
                                for r in results {
                                    self.add_clause(id, r);
                                }
                            }
                        }
                    }
                    Lit::Eq { .. } if self.equality => {
                        // This equality is the paramodulation source: rewrite
                        // matching literals of worked-off clauses.
                        let results = self.eq_from_equation(id, &clause, *max, root);
                        for r in results {
                            self.add_clause(id, r);
                        }
                    }
                    Lit::Ineq { .. } if self.equality => {
                        // This inequality is a paramodulation target: rewrite it
                        // with worked-off equalities (the reverse direction, so
                        // the equality/inequality clash is found regardless of
                        // derivation order).
                        let results = self.eq_from_pred(id, &clause, *max, root);
                        for r in results {
                            self.add_clause(id, r);
                        }
                    }
                    _ => {}
                }
            }
            // Factor rule: applies to clauses with two head equalities sharing a side.
            if self.equality && clause.head.iter().filter(|l| matches!(l, Lit::Eq { .. })).count() >= 2 {
                let results = self.factor(&clause, root);
                for r in results {
                    self.add_clause(id, r);
                }
            }
            self.contexts[id].worked_off.push(clause);
        }
    }

    /// Hyper rule.  `side` is the just-popped clause; `max` one of its maximal
    /// head predicates.
    fn hyper(&self, id: usize, side: &ContextClause, max: Pred, root: bool) -> Vec<ContextClause> {
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
                    for (ci, c) in ctx.worked_off.iter().enumerate() {
                        for (p, _) in c.max_head_predicates() {
                            if can_unify(&oc.body[i], &p) {
                                v.push((ci, p));
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
            // cartesian product over candidates
            let mut idxs = vec![0usize; n];
            loop {
                // build substitution and resolvent for this combination
                let mut sigma = CentralSubst::new();
                let mut unifiable = true;
                for i in 0..n {
                    let (_ci, p) = candidates[i][idxs[i]];
                    if !unify(&mut sigma, &oc.body[i], &p) {
                        unifiable = false;
                        break;
                    }
                }
                if unifiable {
                    if let Some(c) = self.build_hyper_resolvent(id, side, oc, &sigma, &candidates, &idxs, root) {
                        out.push(c);
                    }
                }
                // increment
                let mut k = 0;
                loop {
                    if k == n {
                        // done
                        idxs[0] = usize::MAX; // sentinel handled below
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
        for pc in &ctx.neighbor_pred {
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
                for (ci, c) in ctx.worked_off.iter().enumerate() {
                    if c.max_head_predicates().any(|(p, _)| p == bp) {
                        v.push((ci, bp));
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

    fn shared_successor(&mut self) -> usize {
        if let Some(s) = self.successor_ctx {
            return s;
        }
        let id = self.get_or_create_context(vec![], false, None);
        self.successor_ctx = Some(id);
        id
    }

    /// After saturating context `id`, generate Succ and Pred messages.
    fn propagate(&mut self, id: usize) {
        // ---- Succ ----
        let mut new_succ: Vec<Pred> = Vec::new();
        {
            let ctx = &self.contexts[id];
            for c in &ctx.worked_off {
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
        for p in new_succ {
            let f = p.max_term();
            let target = self.shared_successor();
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
        // ---- Pred ----
        let mut to_send: Vec<((usize, Term), Vec<Pred>, ContextClause)> = Vec::new();
        {
            let ctx = &self.contexts[id];
            for c in &ctx.worked_off {
                // Push back clauses whose head is function-free (so after the
                // backward map y->x, x->f(x) they speak only about the
                // predecessor and the shared term f(x), never nested f(f(x))),
                // and whose body is covered by the predicates pushed on an edge.
                // This generalises Sequoia's pred-trigger-head restriction so
                // that consequences about the witness (e.g. C(f(x))) reach the
                // predecessor; it is sound (the body predicates discharge via
                // the Pred rule) and keeps successor terms bounded.
                if !c.head.iter().all(|l| l.is_function_free()) {
                    continue;
                }
                if c.head.is_empty() && c.body.is_empty() {
                    // empty clause: inconsistency under the pushed hypotheses;
                    // still propagate so the predecessor learns the clash.
                }
                for (edge, pushed) in &ctx.predecessors {
                    if c.body.iter().all(|b| pushed.contains(b)) {
                        let pk = (*edge, c.key());
                        if !ctx.pushed_pred.contains(&pk) {
                            to_send.push((*edge, ctx.core.clone(), c.clone()));
                        }
                    }
                }
            }
        }
        for (edge, core, clause) in to_send {
            self.contexts[id].pushed_pred.insert((edge, clause.key()));
            self.msgs.push_back(Msg::Pred {
                to: edge.0,
                edge_label: edge.1,
                neighbour_core: core,
                clause,
            });
        }
    }

    fn apply_succ(&mut self, from: usize, f: Term, p: Pred, target: usize) {
        // record predecessor edge
        self.contexts[target]
            .predecessors
            .entry((from, f))
            .or_default()
            .insert(p);
        // Succ rule: add hypothesis clause  p -> p
        let root = self.contexts[target].root;
        let c = ContextClause::new(vec![p], vec![Lit::P(p)], root, &self.sig);
        let added = self.add_clause(target, c);
        if added {
            self.saturate(target);
            self.propagate(target);
        } else {
            // even if not added, existing pred clauses may need pushing to the
            // (possibly new) edge: re-run propagate to flush worked-off pred clauses
            self.propagate(target);
        }
    }

    fn apply_pred(
        &mut self,
        to: usize,
        edge_label: Term,
        neighbour_core: Vec<Pred>,
        clause: ContextClause,
    ) {
        // Back-substitute: y -> x, x -> f(x)
        let f = edge_label;
        let subst = |v: Term| backwards(f, v);
        let mut body: Vec<Pred> = clause.body.iter().map(|p| p.apply(&subst)).collect();
        for p in &neighbour_core {
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
        let pc = PredClause { body, head };
        self.contexts[to].neighbor_pred.push(pc.clone());
        // Apply Pred rule against worked-off clauses of `to`.
        let root = self.contexts[to].root;
        let results = self.pred_from_neighbor(to, &pc, root);
        for r in results {
            self.add_clause(to, r);
        }
        self.saturate(to);
        self.propagate(to);
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
            for (ci, c) in ctx.worked_off.iter().enumerate() {
                if c.max_head_predicates().any(|(p, _)| p == bp) {
                    v.push((ci, bp));
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

    pub fn run(&mut self) {
        // Root contexts: one per named (query) concept.
        let named: Vec<Iri> = (0..self.sig.concept_names.len() as Iri)
            .filter(|&i| !self.sig.is_internal(i) && !self.sig.is_nothing_concept(i))
            .collect();
        for iri in named {
            let core = vec![Pred::Concept { iri, t: X }];
            let id = self.get_or_create_context(core, true, Some(iri));
            self.saturate(id);
            self.propagate(id);
        }
        // Process inter-context messages to fixpoint.
        let mut guard = 0usize;
        while let Some(msg) = self.msgs.pop_front() {
            guard += 1;
            if guard > 5_000_000 {
                break;
            }
            match msg {
                Msg::Succ { from, f, p, target } => self.apply_succ(from, f, p, target),
                Msg::Pred {
                    to,
                    edge_label,
                    neighbour_core,
                    clause,
                } => self.apply_pred(to, edge_label, neighbour_core, clause),
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
        // ontology inconsistent iff some root context derives the empty clause
        // for a satisfiable-by-assumption core, i.e. owl:Thing is unsatisfiable.
        // Conservative: any root context whose core single concept is forced to
        // Nothing AND that concept is owl:Thing.
        for ctx in &self.contexts {
            if !ctx.root {
                continue;
            }
            if let Some(iri) = ctx.query {
                let name = &self.sig.concept_names[iri as usize];
                let short = name.rsplit(['#', '/']).next().unwrap_or(name);
                if short == "Thing" || name == "owl:Thing" {
                    if ctx.worked_off.iter().any(|c| c.body.is_empty() && c.head.is_empty()) {
                        return true;
                    }
                }
            }
        }
        false
    }

    pub fn num_contexts(&self) -> usize {
        self.contexts.len()
    }
}
