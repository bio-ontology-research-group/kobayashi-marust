//! Classification of ontologies whose domain is covered by a few named
//! individuals (`⊤ ⊑ {o1, …, ok}`, k ≤ 4), by search over finite
//! interpretations (docs/V1.7.0-NOMINAL-COVER.md).
//!
//! Under the cover every model has at most `k` elements and each element is
//! the denotation of a cover individual. A model is fixed, up to isomorphism,
//! by (1) the partition of the cover individuals into elements, (2) the
//! element of every other individual, and (3) the extension of every class
//! and role name over those elements. For each partition of the cover this
//! module grounds the ontology over the `m ≤ k` elements into propositional
//! clauses and decides it with a small CDCL solver. A class `A` is subsumed
//! by `B` iff no model of any partition has an element in `A` and not in `B`;
//! the ontology is consistent iff some partition has a model.
//!
//! The route declines (returns `None`, and the existing routes answer) on any
//! construct it does not ground (data properties, datatypes, keys, rules, the
//! universal role, anonymous individuals, dropped source axioms), on covers of
//! more than `MAX_COVER` individuals, on inputs beyond the size bounds, and
//! when the solver exceeds its conflict budget. It never guesses.

use std::collections::{BTreeMap, HashMap};

use crate::frontend::iri::IriRegistry;
use crate::frontend::parse;
use crate::frontend::syntax::{Axiom, Concept, Role};

/// Largest cover handled (Bell(4) = 15 partitions).
const MAX_COVER: usize = 4;
/// Size bounds: individuals, class names, role names, ground clauses.
const MAX_INDIVIDUALS: usize = 400;
const MAX_CLASSES: usize = 20_000;
const MAX_ROLES: usize = 400;
const MAX_CLAUSES: usize = 3_000_000;
/// Longest role chain grounded (m^(n+1) clauses per chain).
const MAX_CHAIN: usize = 6;
/// Conflict budget over all solver calls of one classification.
const CONFLICT_BUDGET: u64 = 2_000_000;

// ---------------------------------------------------------------------------
// CDCL solver
// ---------------------------------------------------------------------------

/// Literal: `var << 1 | negated`.
type Lit = u32;

#[inline]
fn pos(v: u32) -> Lit {
    v << 1
}
#[inline]
fn neg(l: Lit) -> Lit {
    l ^ 1
}
#[inline]
fn var(l: Lit) -> usize {
    (l >> 1) as usize
}

const UNDEF: i8 = -1;

/// Binary max-heap of variables ordered by activity (VSIDS order).
struct VarHeap {
    heap: Vec<u32>,
    index: Vec<i32>,
}

impl VarHeap {
    fn contains(&self, v: usize) -> bool {
        self.index.get(v).is_some_and(|&i| i >= 0)
    }
    fn up(&mut self, mut i: usize, act: &[f64]) {
        let v = self.heap[i];
        while i > 0 {
            let p = (i - 1) / 2;
            if act[self.heap[p] as usize] >= act[v as usize] {
                break;
            }
            self.heap[i] = self.heap[p];
            self.index[self.heap[i] as usize] = i as i32;
            i = p;
        }
        self.heap[i] = v;
        self.index[v as usize] = i as i32;
    }
    fn down(&mut self, mut i: usize, act: &[f64]) {
        let v = self.heap[i];
        loop {
            let l = 2 * i + 1;
            if l >= self.heap.len() {
                break;
            }
            let r = l + 1;
            let c = if r < self.heap.len() && act[self.heap[r] as usize] > act[self.heap[l] as usize] { r } else { l };
            if act[self.heap[c] as usize] <= act[v as usize] {
                break;
            }
            self.heap[i] = self.heap[c];
            self.index[self.heap[i] as usize] = i as i32;
            i = c;
        }
        self.heap[i] = v;
        self.index[v as usize] = i as i32;
    }
    fn insert(&mut self, v: usize, act: &[f64]) {
        while self.index.len() <= v {
            self.index.push(-1);
        }
        if self.contains(v) {
            return;
        }
        self.heap.push(v as u32);
        let i = self.heap.len() - 1;
        self.index[v] = i as i32;
        self.up(i, act);
    }
    fn bumped(&mut self, v: usize, act: &[f64]) {
        if self.contains(v) {
            let i = self.index[v] as usize;
            self.up(i, act);
        }
    }
    fn pop(&mut self, act: &[f64]) -> Option<usize> {
        if self.heap.is_empty() {
            return None;
        }
        let top = self.heap[0] as usize;
        let last = self.heap.pop().unwrap();
        self.index[top] = -1;
        if !self.heap.is_empty() {
            self.heap[0] = last;
            self.index[last as usize] = 0;
            self.down(0, act);
        }
        Some(top)
    }
}

/// A plain CDCL solver: two watched literals, first-UIP learning, activity
/// ordering with phase saving, geometric restarts, solving under assumptions.
/// Learnt clauses are kept (the instances are small). Every clause it adds is
/// a resolvent of existing clauses, so `Unsat` is exact; `Sat` comes with a
/// total assignment that satisfies every clause.
struct Solver {
    clauses: Vec<Vec<Lit>>,
    watches: Vec<Vec<u32>>,
    assigns: Vec<i8>,
    level: Vec<u32>,
    reason: Vec<u32>,
    trail: Vec<Lit>,
    trail_lim: Vec<usize>,
    qhead: usize,
    activity: Vec<f64>,
    var_inc: f64,
    polarity: Vec<bool>,
    seen: Vec<bool>,
    order: VarHeap,
    ok: bool,
    conflicts: u64,
}

const NO_REASON: u32 = u32::MAX;

enum Outcome {
    Sat,
    Unsat,
    Budget,
}

impl Solver {
    fn new() -> Self {
        Solver {
            clauses: Vec::new(),
            watches: Vec::new(),
            assigns: Vec::new(),
            level: Vec::new(),
            reason: Vec::new(),
            trail: Vec::new(),
            trail_lim: Vec::new(),
            qhead: 0,
            activity: Vec::new(),
            var_inc: 1.0,
            polarity: Vec::new(),
            seen: Vec::new(),
            order: VarHeap { heap: Vec::new(), index: Vec::new() },
            ok: true,
            conflicts: 0,
        }
    }

    fn new_var(&mut self) -> u32 {
        let v = self.assigns.len() as u32;
        self.assigns.push(UNDEF);
        self.level.push(0);
        self.reason.push(NO_REASON);
        self.activity.push(0.0);
        self.polarity.push(false);
        self.seen.push(false);
        self.watches.push(Vec::new());
        self.watches.push(Vec::new());
        self.order.insert(v as usize, &self.activity);
        v
    }

    fn num_vars(&self) -> usize {
        self.assigns.len()
    }

    #[inline]
    fn value(&self, l: Lit) -> i8 {
        let a = self.assigns[var(l)];
        if a == UNDEF {
            UNDEF
        } else {
            a ^ (l & 1) as i8
        }
    }

    fn decision_level(&self) -> u32 {
        self.trail_lim.len() as u32
    }

    fn enqueue(&mut self, l: Lit, reason: u32) {
        let v = var(l);
        self.assigns[v] = 1 ^ (l & 1) as i8;
        self.level[v] = self.decision_level();
        self.reason[v] = reason;
        self.trail.push(l);
    }

    /// Add a clause at decision level 0.
    fn add_clause(&mut self, lits: &[Lit]) {
        debug_assert!(self.trail_lim.is_empty());
        if !self.ok {
            return;
        }
        let mut c: Vec<Lit> = Vec::with_capacity(lits.len());
        for &l in lits {
            match self.value(l) {
                1 => return,
                0 => continue,
                _ => {
                    if c.contains(&neg(l)) {
                        return;
                    }
                    if !c.contains(&l) {
                        c.push(l);
                    }
                }
            }
        }
        match c.len() {
            0 => self.ok = false,
            1 => {
                self.enqueue(c[0], NO_REASON);
                if self.propagate().is_some() {
                    self.ok = false;
                }
            }
            _ => {
                let cref = self.clauses.len() as u32;
                self.watches[c[0] as usize].push(cref);
                self.watches[c[1] as usize].push(cref);
                self.clauses.push(c);
            }
        }
    }

    /// Unit propagation; returns a conflicting clause.
    fn propagate(&mut self) -> Option<u32> {
        while self.qhead < self.trail.len() {
            let p = self.trail[self.qhead];
            self.qhead += 1;
            let false_lit = neg(p);
            let mut ws = std::mem::take(&mut self.watches[false_lit as usize]);
            let mut i = 0;
            let mut j = 0;
            let mut conflict = None;
            while i < ws.len() {
                let cref = ws[i];
                i += 1;
                let clause = &mut self.clauses[cref as usize];
                if clause[0] == false_lit {
                    clause.swap(0, 1);
                }
                let first = clause[0];
                let first_val = {
                    let a = self.assigns[var(first)];
                    if a == UNDEF { UNDEF } else { a ^ (first & 1) as i8 }
                };
                if first_val == 1 {
                    ws[j] = cref;
                    j += 1;
                    continue;
                }
                let mut moved = false;
                for k in 2..clause.len() {
                    let l = clause[k];
                    let a = self.assigns[var(l)];
                    let val = if a == UNDEF { UNDEF } else { a ^ (l & 1) as i8 };
                    if val != 0 {
                        clause.swap(1, k);
                        let w = clause[1];
                        self.watches[w as usize].push(cref);
                        moved = true;
                        break;
                    }
                }
                if moved {
                    continue;
                }
                ws[j] = cref;
                j += 1;
                if first_val == 0 {
                    conflict = Some(cref);
                    while i < ws.len() {
                        ws[j] = ws[i];
                        j += 1;
                        i += 1;
                    }
                } else {
                    self.enqueue(first, cref);
                }
            }
            ws.truncate(j);
            // Watches added to `false_lit` during the scan are impossible (a
            // new watch is never false), so the list can be put back whole.
            let added = std::mem::take(&mut self.watches[false_lit as usize]);
            ws.extend(added);
            self.watches[false_lit as usize] = ws;
            if conflict.is_some() {
                self.qhead = self.trail.len();
                return conflict;
            }
        }
        None
    }

    fn bump(&mut self, v: usize) {
        self.activity[v] += self.var_inc;
        if self.activity[v] > 1e100 {
            for a in &mut self.activity {
                *a *= 1e-100;
            }
            self.var_inc *= 1e-100;
        }
        self.order.bumped(v, &self.activity);
    }

    /// First-UIP conflict analysis: the learnt clause (asserting literal
    /// first) and the backtrack level.
    fn analyze(&mut self, mut confl: u32) -> (Vec<Lit>, u32) {
        let mut learnt: Vec<Lit> = vec![0];
        let mut path = 0usize;
        let mut p: Option<Lit> = None;
        let mut idx = self.trail.len();
        let current = self.decision_level();
        loop {
            let clause = self.clauses[confl as usize].clone();
            for &q in &clause {
                if Some(q) == p {
                    continue;
                }
                let v = var(q);
                if !self.seen[v] && self.level[v] > 0 {
                    self.seen[v] = true;
                    self.bump(v);
                    if self.level[v] >= current {
                        path += 1;
                    } else {
                        learnt.push(q);
                    }
                }
            }
            loop {
                idx -= 1;
                if self.seen[var(self.trail[idx])] {
                    break;
                }
            }
            let lit = self.trail[idx];
            p = Some(lit);
            self.seen[var(lit)] = false;
            path -= 1;
            if path == 0 {
                break;
            }
            confl = self.reason[var(lit)];
            debug_assert!(confl != NO_REASON);
        }
        learnt[0] = neg(p.unwrap());
        for &l in &learnt[1..] {
            self.seen[var(l)] = false;
        }
        let mut bt = 0;
        if learnt.len() > 1 {
            let mut max_i = 1;
            for i in 2..learnt.len() {
                if self.level[var(learnt[i])] > self.level[var(learnt[max_i])] {
                    max_i = i;
                }
            }
            learnt.swap(1, max_i);
            bt = self.level[var(learnt[1])];
        }
        self.var_inc *= 1.0 / 0.95;
        (learnt, bt)
    }

    fn cancel_until(&mut self, lvl: u32) {
        if self.decision_level() > lvl {
            let lim = self.trail_lim[lvl as usize];
            for i in (lim..self.trail.len()).rev() {
                let v = var(self.trail[i]);
                self.polarity[v] = self.trail[i] & 1 == 0;
                self.assigns[v] = UNDEF;
                self.reason[v] = NO_REASON;
                self.order.insert(v, &self.activity);
            }
            self.trail.truncate(lim);
            self.trail_lim.truncate(lvl as usize);
            self.qhead = lim;
        }
    }

    fn pick_branch(&mut self) -> Option<Lit> {
        while let Some(v) = self.order.pop(&self.activity) {
            if self.assigns[v] == UNDEF {
                return Some(if self.polarity[v] { pos(v as u32) } else { neg(pos(v as u32)) });
            }
        }
        None
    }

    /// Solve under assumptions. `budget` counts conflicts across calls.
    fn solve(&mut self, assumptions: &[Lit], budget: &mut u64) -> Outcome {
        if !self.ok {
            return Outcome::Unsat;
        }
        let mut restart_limit = 100u64;
        let mut since_restart = 0u64;
        let result = loop {
            if let Some(confl) = self.propagate() {
                self.conflicts += 1;
                since_restart += 1;
                if *budget == 0 {
                    break Outcome::Budget;
                }
                *budget -= 1;
                if self.decision_level() == 0 {
                    self.ok = false;
                    break Outcome::Unsat;
                }
                let (learnt, bt) = self.analyze(confl);
                self.cancel_until(bt);
                if learnt.len() == 1 {
                    self.enqueue(learnt[0], NO_REASON);
                } else {
                    let cref = self.clauses.len() as u32;
                    self.watches[learnt[0] as usize].push(cref);
                    self.watches[learnt[1] as usize].push(cref);
                    let first = learnt[0];
                    self.clauses.push(learnt);
                    self.enqueue(first, cref);
                }
                continue;
            }
            if since_restart >= restart_limit {
                since_restart = 0;
                restart_limit = restart_limit * 3 / 2;
                self.cancel_until(0);
                continue;
            }
            let dl = self.decision_level() as usize;
            if dl < assumptions.len() {
                let a = assumptions[dl];
                match self.value(a) {
                    1 => {
                        self.trail_lim.push(self.trail.len());
                        continue;
                    }
                    0 => break Outcome::Unsat,
                    _ => {
                        self.trail_lim.push(self.trail.len());
                        self.enqueue(a, NO_REASON);
                        continue;
                    }
                }
            }
            match self.pick_branch() {
                None => break Outcome::Sat,
                Some(l) => {
                    self.trail_lim.push(self.trail.len());
                    self.enqueue(l, NO_REASON);
                }
            }
        };
        result
    }

    /// The model of the last `Sat` answer (valid until the next call).
    fn model_value(&self, l: Lit) -> bool {
        self.value(l) == 1
    }

    fn reset(&mut self) {
        self.cancel_until(0);
    }
}

// ---------------------------------------------------------------------------
// Grounding
// ---------------------------------------------------------------------------

/// Why the route declined (diagnostic, `KM_TIMING`).
#[derive(Debug)]
pub(crate) struct Decline(pub String);

fn decline<T>(reason: impl Into<String>) -> Result<T, Decline> {
    Err(Decline(reason.into()))
}

/// Source constructs the grounding does not read. Checked on the functional
/// syntax text before parsing, because the parser maps several of them to
/// internal names or drops them.
const UNSUPPORTED_HEADS: &[&str] = &[
    "DataSomeValuesFrom(",
    "DataAllValuesFrom(",
    "DataHasValue(",
    "DataMinCardinality(",
    "DataMaxCardinality(",
    "DataExactCardinality(",
    "DataPropertyAssertion(",
    "NegativeDataPropertyAssertion(",
    "DataPropertyDomain(",
    "DataPropertyRange(",
    "SubDataPropertyOf(",
    "EquivalentDataProperties(",
    "DisjointDataProperties(",
    "FunctionalDataProperty(",
    "DataProperty(",
    "DatatypeDefinition(",
    "Datatype(",
    "HasKey(",
    "DLSafeRule(",
    "topObjectProperty",
    "bottomObjectProperty",
    "topDataProperty",
    "bottomDataProperty",
    "_:",
];

/// The ontology over one partition of the cover, grounded.
struct Grounding<'a> {
    solver: Solver,
    m: usize,
    t: Lit,
    /// Cover individual -> element.
    cover_elem: &'a HashMap<String, usize>,
    /// Other individual -> its element literals.
    ind_vars: HashMap<String, Vec<Lit>>,
    class_vars: HashMap<String, Vec<Lit>>,
    role_vars: HashMap<String, Vec<Lit>>,
    memo: HashMap<(Concept, usize), Lit>,
    clause_count: usize,
}

impl<'a> Grounding<'a> {
    fn lit_true(&self) -> Lit {
        self.t
    }
    fn lit_false(&self) -> Lit {
        neg(self.t)
    }

    fn fresh(&mut self) -> Lit {
        pos(self.solver.new_var())
    }

    fn clause(&mut self, lits: &[Lit]) -> Result<(), Decline> {
        self.clause_count += 1;
        if self.clause_count > MAX_CLAUSES {
            return decline("ground clause bound exceeded");
        }
        self.solver.add_clause(lits);
        Ok(())
    }

    fn class(&mut self, name: &str, d: usize) -> Lit {
        if !self.class_vars.contains_key(name) {
            let vars: Vec<Lit> = (0..self.m).map(|_| pos(self.solver.new_var())).collect();
            self.class_vars.insert(name.to_string(), vars);
        }
        self.class_vars[name][d]
    }

    fn role_name(&mut self, name: &str, d: usize, e: usize) -> Lit {
        if !self.role_vars.contains_key(name) {
            let n = self.m * self.m;
            let vars: Vec<Lit> = (0..n).map(|_| pos(self.solver.new_var())).collect();
            self.role_vars.insert(name.to_string(), vars);
        }
        self.role_vars[name][d * self.m + e]
    }

    fn role(&mut self, r: &Role, d: usize, e: usize) -> Result<Lit, Decline> {
        match r {
            Role::Name(n) => Ok(self.role_name(n, d, e)),
            Role::Inverse(n) => Ok(self.role_name(n, e, d)),
            Role::Universal => decline("universal role"),
        }
    }

    /// The element literals of an individual: `(element, literal)` pairs, one
    /// of which holds in every model.
    fn ind(&mut self, a: &str) -> Vec<(usize, Lit)> {
        if let Some(&d) = self.cover_elem.get(a) {
            return vec![(d, self.lit_true())];
        }
        if !self.ind_vars.contains_key(a) {
            let vars: Vec<Lit> = (0..self.m).map(|_| pos(self.solver.new_var())).collect();
            // exactly one element
            self.solver.add_clause(&vars);
            for i in 0..vars.len() {
                for j in (i + 1)..vars.len() {
                    self.solver.add_clause(&[neg(vars[i]), neg(vars[j])]);
                }
            }
            self.ind_vars.insert(a.to_string(), vars);
        }
        self.ind_vars[a].iter().enumerate().map(|(d, &l)| (d, l)).collect()
    }

    fn and(&mut self, lits: &[Lit]) -> Result<Lit, Decline> {
        if lits.iter().any(|&l| l == self.lit_false()) {
            return Ok(self.lit_false());
        }
        let lits: Vec<Lit> = lits.iter().copied().filter(|&l| l != self.lit_true()).collect();
        match lits.len() {
            0 => return Ok(self.lit_true()),
            1 => return Ok(lits[0]),
            _ => {}
        }
        let v = self.fresh();
        let mut big = vec![v];
        for &l in &lits {
            self.clause(&[neg(v), l])?;
            big.push(neg(l));
        }
        self.clause(&big)?;
        Ok(v)
    }

    fn or(&mut self, lits: &[Lit]) -> Result<Lit, Decline> {
        let negs: Vec<Lit> = lits.iter().map(|&l| neg(l)).collect();
        Ok(neg(self.and(&negs)?))
    }

    /// `#{e : R(d, e) ∧ C(e)} ≥ n`.
    fn at_least(&mut self, n: i64, r: &Role, c: &Concept, d: usize) -> Result<Lit, Decline> {
        if n <= 0 {
            return Ok(self.lit_true());
        }
        if n as usize > self.m {
            return Ok(self.lit_false());
        }
        let mut succ: Vec<Lit> = Vec::with_capacity(self.m);
        for e in 0..self.m {
            let re = self.role(r, d, e)?;
            let ce = self.eval(c, e)?;
            succ.push(self.and(&[re, ce])?);
        }
        let n = n as usize;
        let mut options: Vec<Lit> = Vec::new();
        let mut subset: Vec<usize> = Vec::new();
        fn subsets(start: usize, m: usize, n: usize, cur: &mut Vec<usize>, out: &mut Vec<Vec<usize>>) {
            if cur.len() == n {
                out.push(cur.clone());
                return;
            }
            for i in start..m {
                cur.push(i);
                subsets(i + 1, m, n, cur, out);
                cur.pop();
            }
        }
        let mut all: Vec<Vec<usize>> = Vec::new();
        subsets(0, self.m, n, &mut subset, &mut all);
        for s in all {
            let lits: Vec<Lit> = s.iter().map(|&i| succ[i]).collect();
            options.push(self.and(&lits)?);
        }
        self.or(&options)
    }

    /// The literal of `C` at element `d`, defined by equivalence.
    fn eval(&mut self, c: &Concept, d: usize) -> Result<Lit, Decline> {
        if let Some(&l) = self.memo.get(&(c.clone(), d)) {
            return Ok(l);
        }
        let l = match c {
            Concept::Top => self.lit_true(),
            Concept::Bottom => self.lit_false(),
            Concept::Name(n) => {
                if n.starts_with("__") {
                    return decline(format!("internal concept {n}"));
                }
                self.class(n, d)
            }
            Concept::Nominal(a) => {
                let lits = self.ind(a);
                lits.iter().find(|(e, _)| *e == d).map(|&(_, l)| l).unwrap_or(self.lit_false())
            }
            Concept::Not(x) => neg(self.eval(x, d)?),
            Concept::And(xs) => {
                let mut lits = Vec::with_capacity(xs.len());
                for x in xs {
                    lits.push(self.eval(x, d)?);
                }
                self.and(&lits)?
            }
            Concept::Or(xs) => {
                let mut lits = Vec::with_capacity(xs.len());
                for x in xs {
                    lits.push(self.eval(x, d)?);
                }
                self.or(&lits)?
            }
            Concept::Exists(r, x) => self.at_least(1, r, x, d)?,
            Concept::Forall(r, x) => {
                let not_x = Concept::Not(x.clone());
                neg(self.at_least(1, r, &not_x, d)?)
            }
            Concept::AtLeast(n, r, x) => self.at_least(*n, r, x, d)?,
            Concept::AtMost(n, r, x) => neg(self.at_least(n + 1, r, x, d)?),
            Concept::HasSelf(r) => self.role(r, d, d)?,
        };
        self.memo.insert((c.clone(), d), l);
        Ok(l)
    }

    fn role_chain(&mut self, chain: &[String], sup: &str) -> Result<(), Decline> {
        if chain.len() > MAX_CHAIN {
            return decline("role chain too long");
        }
        let m = self.m;
        let n = chain.len();
        // every path d0 .. dn
        let total = m.pow(n as u32 + 1);
        for code in 0..total {
            let mut path = Vec::with_capacity(n + 1);
            let mut c = code;
            for _ in 0..=n {
                path.push(c % m);
                c /= m;
            }
            let mut lits: Vec<Lit> = Vec::with_capacity(n + 1);
            for (i, r) in chain.iter().enumerate() {
                lits.push(neg(self.role_name(r, path[i], path[i + 1])));
            }
            lits.push(self.role_name(sup, path[0], path[n]));
            self.clause(&lits)?;
        }
        Ok(())
    }

    fn axiom(&mut self, ax: &Axiom) -> Result<(), Decline> {
        let m = self.m;
        match ax {
            Axiom::SubClassOf(c, d) => {
                for e in 0..m {
                    let a = self.eval(c, e)?;
                    let b = self.eval(d, e)?;
                    self.clause(&[neg(a), b])?;
                }
            }
            Axiom::EquivalentClasses(c, d) => {
                for e in 0..m {
                    let a = self.eval(c, e)?;
                    let b = self.eval(d, e)?;
                    self.clause(&[neg(a), b])?;
                    self.clause(&[a, neg(b)])?;
                }
            }
            Axiom::DisjointClasses(c, d) => {
                for e in 0..m {
                    let a = self.eval(c, e)?;
                    let b = self.eval(d, e)?;
                    self.clause(&[neg(a), neg(b)])?;
                }
            }
            Axiom::RoleInclusion(r, s) => {
                for d in 0..m {
                    for e in 0..m {
                        let a = self.role_name(r, d, e);
                        let b = self.role_name(s, d, e);
                        self.clause(&[neg(a), b])?;
                    }
                }
            }
            Axiom::RoleChain(chain, s) => self.role_chain(chain, s)?,
            Axiom::TransitiveRole(r) => self.role_chain(&[r.clone(), r.clone()], r)?,
            Axiom::SymmetricRole(r) => {
                for d in 0..m {
                    for e in 0..m {
                        let a = self.role_name(r, d, e);
                        let b = self.role_name(r, e, d);
                        self.clause(&[neg(a), b])?;
                    }
                }
            }
            Axiom::AsymmetricRole(r) => {
                for d in 0..m {
                    for e in 0..m {
                        let a = self.role_name(r, d, e);
                        let b = self.role_name(r, e, d);
                        self.clause(&[neg(a), neg(b)])?;
                    }
                }
            }
            Axiom::ReflexiveRole(r) => {
                for d in 0..m {
                    let a = self.role_name(r, d, d);
                    self.clause(&[a])?;
                }
            }
            Axiom::IrreflexiveRole(r) => {
                for d in 0..m {
                    let a = self.role_name(r, d, d);
                    self.clause(&[neg(a)])?;
                }
            }
            Axiom::InverseRoles(r, s) => {
                for d in 0..m {
                    for e in 0..m {
                        let a = self.role_name(r, d, e);
                        let b = self.role_name(s, e, d);
                        self.clause(&[neg(a), b])?;
                        self.clause(&[a, neg(b)])?;
                    }
                }
            }
            Axiom::FunctionalRole(r) | Axiom::InverseFunctionalRole(r) => {
                let inverse = matches!(ax, Axiom::InverseFunctionalRole(_));
                for d in 0..m {
                    for e1 in 0..m {
                        for e2 in (e1 + 1)..m {
                            let (a, b) = if inverse {
                                (self.role_name(r, e1, d), self.role_name(r, e2, d))
                            } else {
                                (self.role_name(r, d, e1), self.role_name(r, d, e2))
                            };
                            self.clause(&[neg(a), neg(b)])?;
                        }
                    }
                }
            }
            Axiom::DisjointRoles(r, s) => {
                for d in 0..m {
                    for e in 0..m {
                        let a = self.role_name(r, d, e);
                        let b = self.role_name(s, d, e);
                        self.clause(&[neg(a), neg(b)])?;
                    }
                }
            }
            Axiom::ConceptAssertion(c, a) => {
                for (d, l) in self.ind(a) {
                    let x = self.eval(c, d)?;
                    self.clause(&[neg(l), x])?;
                }
            }
            Axiom::RoleAssertion(r, a, b) | Axiom::NegativeRoleAssertion(r, a, b) => {
                let positive = matches!(ax, Axiom::RoleAssertion(..));
                let la = self.ind(a);
                let lb = self.ind(b);
                for &(d, x) in &la {
                    for &(e, y) in &lb {
                        let rl = self.role_name(r, d, e);
                        let head = if positive { rl } else { neg(rl) };
                        self.clause(&[neg(x), neg(y), head])?;
                    }
                }
            }
            Axiom::SameIndividual(a, b) | Axiom::DifferentIndividuals(a, b) => {
                let same = matches!(ax, Axiom::SameIndividual(..));
                let la = self.ind(a);
                let lb = self.ind(b);
                for &(d, x) in &la {
                    for &(e, y) in &lb {
                        if (d == e) != same {
                            self.clause(&[neg(x), neg(y)])?;
                        }
                    }
                }
            }
            Axiom::Rule(..) | Axiom::DataRule(..) => return decline("rules"),
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Cover detection and classification
// ---------------------------------------------------------------------------

/// The class tokens of `Declaration(Class(X))` in functional syntax.
fn declared_classes(text: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut rest = text;
    while let Some(i) = rest.find("Declaration(") {
        rest = &rest[i + "Declaration(".len()..];
        let body = rest.trim_start();
        if let Some(after) = body.strip_prefix("Class(") {
            let after = after.trim_start();
            if let Some(end) = after.find(|c: char| c == ')' || c.is_whitespace()) {
                out.push(after[..end].to_string());
            }
        }
    }
    out
}

/// The individuals of a cover axiom `⊤ ⊑ {o1 … ok}` (or its equivalence form).
fn cover_of(ax: &Axiom) -> Option<Vec<String>> {
    let rhs = match ax {
        Axiom::SubClassOf(Concept::Top, rhs) => rhs,
        Axiom::EquivalentClasses(Concept::Top, rhs) | Axiom::EquivalentClasses(rhs, Concept::Top) => rhs,
        _ => return None,
    };
    match rhs {
        Concept::Nominal(a) => Some(vec![a.clone()]),
        Concept::Or(xs) => {
            let mut out = Vec::new();
            for x in xs {
                match x {
                    Concept::Nominal(a) => out.push(a.clone()),
                    _ => return None,
                }
            }
            out.sort();
            out.dedup();
            Some(out)
        }
        _ => None,
    }
}

/// Every partition of `0..k` as a block index per member (restricted growth
/// strings).
fn partitions(k: usize) -> Vec<Vec<usize>> {
    fn go(i: usize, k: usize, cur: &mut Vec<usize>, max: usize, out: &mut Vec<Vec<usize>>) {
        if i == k {
            out.push(cur.clone());
            return;
        }
        for b in 0..=max + 1 {
            if i == 0 && b > 0 {
                break;
            }
            cur.push(b);
            go(i + 1, k, cur, if i == 0 { 0 } else { max.max(b) }, out);
            cur.pop();
        }
    }
    let mut out = Vec::new();
    if k == 0 {
        return out;
    }
    let mut cur = Vec::new();
    go(0, k, &mut cur, 0, &mut out);
    out
}

/// The answer of the route: consistency and, per class (by full IRI), its
/// named superclasses (`None`: unsatisfiable).
pub(crate) struct CoverAnswer {
    pub consistent: bool,
    pub supers: BTreeMap<String, Option<Vec<String>>>,
    pub partitions: usize,
    pub solves: usize,
}

/// Decide the classification of `text` (functional syntax) for the classes
/// `classes` (full IRIs), or decline.
pub(crate) fn classify_cover(text: &str) -> Result<CoverAnswer, Decline> {
    if text.contains("Declaration(Annotation") {
        return decline("annotated declarations");
    }
    for head in UNSUPPORTED_HEADS {
        if text.contains(head) {
            return decline(format!("unsupported construct {head}"));
        }
    }
    // The frontend's prefix expansion and builtin spellings, then its parser.
    let canonical = crate::frontend::builtin_aliases::canonicalize(text)
        .map_err(|e| Decline(format!("canonicalize: {e}")))?;
    let mut reg = IriRegistry::new();
    let ontology = parse::parse_axioms(&mut reg, &canonical).map_err(|e| Decline(format!("parse: {}", e.0)))?;
    if !ontology.dropped_source_axioms().is_empty() {
        return decline("dropped source axioms");
    }
    let axioms: Vec<&Axiom> = ontology.axioms_iter().collect();
    let mut cover: Option<Vec<String>> = None;
    for ax in &axioms {
        if let Some(c) = cover_of(ax) {
            if cover.as_ref().is_none_or(|old| c.len() < old.len()) {
                cover = Some(c);
            }
        }
    }
    let Some(cover) = cover else { return decline("no cover axiom") };
    if cover.is_empty() || cover.len() > MAX_COVER {
        return decline(format!("cover of {} individuals", cover.len()));
    }
    // Size bounds.
    let mut inds: std::collections::BTreeSet<&str> = std::collections::BTreeSet::new();
    let mut roles: std::collections::BTreeSet<&str> = std::collections::BTreeSet::new();
    for ax in &axioms {
        match ax {
            Axiom::ConceptAssertion(_, a) => {
                inds.insert(a);
            }
            Axiom::RoleAssertion(r, a, b) | Axiom::NegativeRoleAssertion(r, a, b) => {
                inds.insert(a);
                inds.insert(b);
                roles.insert(r);
            }
            Axiom::SameIndividual(a, b) | Axiom::DifferentIndividuals(a, b) => {
                inds.insert(a);
                inds.insert(b);
            }
            Axiom::Rule(..) | Axiom::DataRule(..) => return decline("rules"),
            _ => {}
        }
    }
    if inds.len() > MAX_INDIVIDUALS || roles.len() > MAX_ROLES {
        return decline("size bound");
    }
    // The classes: every class name of the parse and every declared class,
    // as internal names of this parse's registry (the same registry the
    // frontend builds from the same canonical text).
    let mut class_set: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    {
        fn walk(c: &Concept, out: &mut std::collections::BTreeSet<String>) {
            match c {
                Concept::Name(n) => {
                    out.insert(n.clone());
                }
                Concept::Not(x)
                | Concept::Exists(_, x)
                | Concept::Forall(_, x)
                | Concept::AtLeast(_, _, x)
                | Concept::AtMost(_, _, x) => walk(x, out),
                Concept::And(xs) | Concept::Or(xs) => xs.iter().for_each(|x| walk(x, out)),
                Concept::Top | Concept::Bottom | Concept::Nominal(_) | Concept::HasSelf(_) => {}
            }
        }
        for ax in &axioms {
            match ax {
                Axiom::SubClassOf(a, b) | Axiom::EquivalentClasses(a, b) | Axiom::DisjointClasses(a, b) => {
                    walk(a, &mut class_set);
                    walk(b, &mut class_set);
                }
                Axiom::ConceptAssertion(a, _) => walk(a, &mut class_set),
                _ => {}
            }
        }
    }
    for token in declared_classes(&canonical) {
        let short = reg.short(&token);
        if short != "owl:Thing" && short != "owl:Nothing" {
            class_set.insert(short);
        }
    }
    let class_names: Vec<String> = class_set.into_iter().collect();
    let classes: Vec<String> = class_names.iter().map(|n| reg.full_iri(n)).collect();
    if classes.len() > MAX_CLASSES {
        return decline("size bound");
    }
    let k = cover.len();
    let mut budget = CONFLICT_BUDGET;
    let mut consistent = false;
    // Candidate superclasses per class index (None: no model has an
    // instance yet).
    let nclass = classes.len();
    let mut cand: Vec<Option<Vec<bool>>> = vec![None; nclass];
    let mut solves = 0usize;
    let parts = partitions(k);
    let nparts = parts.len();
    for part in parts {
        let m = part.iter().max().map_or(0, |&b| b + 1);
        let cover_elem: HashMap<String, usize> =
            cover.iter().cloned().zip(part.iter().copied()).collect();
        let mut solver = Solver::new();
        let t = pos(solver.new_var());
        solver.add_clause(&[t]);
        let mut g = Grounding {
            solver,
            m,
            t,
            cover_elem: &cover_elem,
            ind_vars: HashMap::new(),
            class_vars: HashMap::new(),
            role_vars: HashMap::new(),
            memo: HashMap::new(),
            clause_count: 0,
        };
        for ax in &axioms {
            g.axiom(ax)?;
        }
        // Class literals per requested class and element (fresh classes get
        // unconstrained variables).
        let mut lits: Vec<Vec<Lit>> = Vec::with_capacity(nclass);
        for name in &class_names {
            lits.push((0..m).map(|d| g.class(name, d)).collect());
        }
        let mut solver = g.solver;
        let record = |solver: &Solver, cand: &mut Vec<Option<Vec<bool>>>| {
            for d in 0..m {
                let ty: Vec<bool> = (0..nclass).map(|i| solver.model_value(lits[i][d])).collect();
                for a in 0..nclass {
                    if !ty[a] {
                        continue;
                    }
                    match &mut cand[a] {
                        None => cand[a] = Some(ty.clone()),
                        Some(c) => {
                            for b in 0..nclass {
                                c[b] &= ty[b];
                            }
                        }
                    }
                }
            }
        };
        solves += 1;
        match solver.solve(&[], &mut budget) {
            Outcome::Budget => return decline("conflict budget"),
            Outcome::Unsat => continue,
            Outcome::Sat => {
                consistent = true;
                record(&solver, &mut cand);
                solver.reset();
            }
        }
        // Per class and element, under assumptions only (no clauses are
        // added): an instance `A(d)`, then for each remaining candidate `B`
        // a model with `A(d) ∧ ¬B(d)`. Every model found shrinks the
        // candidates of every class through `record`; an unsatisfiable call
        // proves `A(d) → B(d)` in this partition.
        for a in 0..nclass {
            for d in 0..m {
                // Instance check first: a class empty at `d` (a nominal probe
                // at another element) needs no candidate checks there.
                {
                    solves += 1;
                    match solver.solve(&[lits[a][d]], &mut budget) {
                        Outcome::Budget => return decline("conflict budget"),
                        Outcome::Unsat => {
                            solver.reset();
                            continue;
                        }
                        Outcome::Sat => {
                            record(&solver, &mut cand);
                            solver.reset();
                        }
                    }
                }
                let mut proven: Vec<bool> = vec![false; nclass];
                loop {
                    let next = {
                        let c = cand[a].as_ref().expect("an instance was recorded");
                        (0..nclass).find(|&b| b != a && c[b] && !proven[b])
                    };
                    let Some(b) = next else { break };
                    solves += 1;
                    match solver.solve(&[lits[a][d], neg(lits[b][d])], &mut budget) {
                        Outcome::Budget => return decline("conflict budget"),
                        Outcome::Unsat => {
                            proven[b] = true;
                            solver.reset();
                        }
                        Outcome::Sat => {
                            record(&solver, &mut cand);
                            solver.reset();
                        }
                    }
                }
            }
        }
        let _ = solver.num_vars();
    }
    let mut supers: BTreeMap<String, Option<Vec<String>>> = BTreeMap::new();
    for (a, full) in classes.iter().enumerate() {
        let entry = cand[a].as_ref().map(|c| {
            (0..nclass)
                .filter(|&b| b != a && c[b])
                .map(|b| classes[b].clone())
                .collect::<Vec<String>>()
        });
        supers.insert(full.clone(), entry);
    }
    Ok(CoverAnswer { consistent, supers, partitions: nparts, solves })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn partitions_are_bell_numbers() {
        assert_eq!(partitions(1).len(), 1);
        assert_eq!(partitions(2).len(), 2);
        assert_eq!(partitions(3).len(), 5);
        assert_eq!(partitions(4).len(), 15);
    }

    fn supers(text: &str, _classes: &[&str]) -> CoverAnswer {
        classify_cover(text).map_err(|d| d.0).expect("route answers")
    }

    #[test]
    fn singleton_cover_makes_inverse_minimum_unsatisfiable() {
        let text = "Ontology(\
            SubClassOf(owl:Thing ObjectOneOf(<http://e/a0>))\
            SubClassOf(<http://e/A> ObjectMinCardinality(2 ObjectInverseOf(<http://e/s1>)))\
            EquivalentClasses(<http://e/V0> ObjectHasValue(<http://e/s2> <http://e/a0>))\
            EquivalentClasses(<http://e/V1> ObjectHasValue(<http://e/s2> <http://e/a1>)))";
        let ans = supers(text, &["http://e/A", "http://e/V0", "http://e/V1"]);
        assert!(ans.consistent);
        assert_eq!(ans.supers["http://e/A"], None);
        assert_eq!(ans.supers["http://e/V0"], Some(vec!["http://e/V1".to_string()]));
        assert_eq!(ans.supers["http://e/V1"], Some(vec!["http://e/V0".to_string()]));
    }

    #[test]
    fn two_element_cover_keeps_open_merges_open() {
        // c1(a0, a0); a1 and a2 may be equal or not; nothing beyond the
        // assertion is entailed for the other individuals.
        let text = "Ontology(\
            SubClassOf(owl:Thing ObjectOneOf(<http://e/a1> <http://e/a2>))\
            ObjectPropertyAssertion(<http://e/c1> <http://e/a0> <http://e/a0>)\
            EquivalentClasses(<http://e/P0> ObjectOneOf(<http://e/a0>))\
            EquivalentClasses(<http://e/P1> ObjectOneOf(<http://e/a1>))\
            EquivalentClasses(<http://e/V3> ObjectHasValue(<http://e/c1> <http://e/a3>))\
            EquivalentClasses(<http://e/S0> ObjectHasSelf(<http://e/c1>)))";
        let ans = supers(
            text,
            &["http://e/P0", "http://e/P1", "http://e/V3", "http://e/S0"],
        );
        assert!(ans.consistent);
        // P0 = {a0} has the self loop.
        assert_eq!(ans.supers["http://e/P0"], Some(vec!["http://e/S0".to_string()]));
        assert_eq!(ans.supers["http://e/P1"], Some(vec![]));
        assert_eq!(ans.supers["http://e/V3"], Some(vec![]));
    }

    #[test]
    fn functional_role_and_cover_force_an_inconsistency() {
        let text = "Ontology(\
            SubClassOf(owl:Thing ObjectOneOf(<http://e/a> <http://e/b>))\
            DifferentIndividuals(<http://e/a> <http://e/b>)\
            SubClassOf(owl:Thing ObjectMinCardinality(2 <http://e/r>))\
            FunctionalObjectProperty(<http://e/r>))";
        let ans = supers(text, &[]);
        assert!(!ans.consistent);
    }

    #[test]
    fn declines_data_properties_and_large_covers() {
        let data = "Ontology(SubClassOf(owl:Thing ObjectOneOf(<http://e/a>))\
            DataPropertyAssertion(<http://e/d> <http://e/a> \"1\"))";
        assert!(classify_cover(data).is_err());
        let big = "Ontology(SubClassOf(owl:Thing ObjectOneOf(<http://e/a> <http://e/b> <http://e/c> <http://e/d> <http://e/e>)))";
        assert!(classify_cover(big).is_err());
        let none = "Ontology(SubClassOf(<http://e/A> <http://e/B>))";
        assert!(classify_cover(none).is_err());
    }

    #[test]
    fn chains_and_transitivity_over_the_cover() {
        let text = "Ontology(\
            SubClassOf(owl:Thing ObjectOneOf(<http://e/a> <http://e/b> <http://e/c>))\
            DifferentIndividuals(<http://e/a> <http://e/b>) DifferentIndividuals(<http://e/b> <http://e/c>) DifferentIndividuals(<http://e/a> <http://e/c>)\
            ObjectPropertyAssertion(<http://e/r> <http://e/a> <http://e/b>) ObjectPropertyAssertion(<http://e/r> <http://e/b> <http://e/c>)\
            TransitiveObjectProperty(<http://e/r>)\
            EquivalentClasses(<http://e/X> ObjectHasValue(<http://e/r> <http://e/c>))\
            EquivalentClasses(<http://e/Pa> ObjectOneOf(<http://e/a>)))";
        let ans = supers(text, &["http://e/X", "http://e/Pa"]);
        assert!(ans.consistent);
        assert_eq!(ans.supers["http://e/Pa"], Some(vec!["http://e/X".to_string()]));
    }
}
