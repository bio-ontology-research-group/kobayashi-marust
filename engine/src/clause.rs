//! Ontology clauses and context clauses for the disjunctive context calculus.

use crate::calc::*;

fn sort_dedup_pred(mut v: Vec<Pred>) -> Vec<Pred> {
    v.sort();
    v.dedup();
    v
}
fn sort_dedup_lit(mut v: Vec<Lit>) -> Vec<Lit> {
    v.sort();
    v.dedup();
    v
}

/// Is `a` a (sorted) subset of `b`?
fn subset_pred(a: &[Pred], b: &[Pred]) -> bool {
    let (mut i, mut j) = (0, 0);
    while i < a.len() && j < b.len() {
        match a[i].cmp(&b[j]) {
            std::cmp::Ordering::Greater => j += 1,
            std::cmp::Ordering::Equal => {
                i += 1;
                j += 1;
            }
            std::cmp::Ordering::Less => return false,
        }
    }
    i == a.len()
}
fn subset_lit(a: &[Lit], b: &[Lit]) -> bool {
    let (mut i, mut j) = (0, 0);
    while i < a.len() && j < b.len() {
        match a[i].cmp(&b[j]) {
            std::cmp::Ordering::Greater => j += 1,
            std::cmp::Ordering::Equal => {
                i += 1;
                j += 1;
            }
            std::cmp::Ordering::Less => return false,
        }
    }
    i == a.len()
}

/// A normalised ontology (DL-)clause `body -> head` (Table 1 normal forms).
#[derive(Clone, Debug)]
pub struct OntologyClause {
    pub body: Vec<Pred>,
    pub head: Vec<Lit>,
    /// Groups of ≥2 neighbour variables the clause is invariant under
    /// exchanging (sorted ascending), with `true` if the head holds an
    /// equality for EVERY pair of the group.  Number-restriction clauses
    /// (`r(x,y1) ∧ C(y1) ∧ ... ∧ r(x,yn) ∧ C(yn) → Δ ∨ ⋁ yi≈yj`) are fully
    /// symmetric: Hyper assignments that permute the group map to the same
    /// canonical resolvent, and (when the flag is set) equal-term assignments
    /// substitute some head equality to `t≈t`, a tautology.  The Hyper join
    /// uses this to enumerate only term-sorted assignments per group instead
    /// of all `k^n` tuples.
    pub sym_groups: Vec<(Vec<Term>, bool)>,
}

impl OntologyClause {
    pub fn new(body: Vec<Pred>, head: Vec<Lit>) -> OntologyClause {
        let body = sort_dedup_pred(body);
        let head = sort_dedup_lit(head);
        let sym_groups = sym_groups(&body, &head);
        OntologyClause { body, head, sym_groups }
    }
}

/// Compute the symmetric neighbour-variable groups of a clause: `u ~ v` iff
/// swapping `u` and `v` everywhere maps body and head to themselves (as sets).
/// Exchange-invariance is transitive over a chain of invariant pairs, so the
/// union-find of invariant PAIRS gives groups invariant under any permutation.
fn sym_groups(body: &[Pred], head: &[Lit]) -> Vec<(Vec<Term>, bool)> {
    let mut vars: Vec<Term> = Vec::new();
    for p in body {
        match *p {
            Pred::Concept { t, .. } => {
                if is_neighbour(t) && t != Y && !vars.contains(&t) {
                    vars.push(t);
                }
            }
            Pred::Role { s, t, .. } => {
                for u in [s, t] {
                    if is_neighbour(u) && u != Y && !vars.contains(&u) {
                        vars.push(u);
                    }
                }
            }
        }
    }
    if vars.len() < 2 {
        return Vec::new();
    }
    vars.sort();
    let swap = |a: Term, b: Term| move |t: Term| if t == a { b } else if t == b { a } else { t };
    let invariant = |a: Term, b: Term| -> bool {
        let s = swap(a, b);
        let mut b2: Vec<Pred> = body.iter().map(|p| p.apply(&s)).collect();
        b2.sort();
        let mut h2: Vec<Lit> = head.iter().map(|l| l.apply(&s)).collect();
        h2.sort();
        h2.dedup();
        b2 == body && h2 == head
    };
    // group by union-find over invariant pairs
    let n = vars.len();
    let mut parent: Vec<usize> = (0..n).collect();
    fn find(parent: &mut Vec<usize>, i: usize) -> usize {
        let mut r = i;
        while parent[r] != r {
            r = parent[r];
        }
        let mut c = i;
        while parent[c] != c {
            let next = parent[c];
            parent[c] = r;
            c = next;
        }
        r
    }
    for i in 0..n {
        for j in (i + 1)..n {
            if invariant(vars[i], vars[j]) {
                let (ri, rj) = (find(&mut parent, i), find(&mut parent, j));
                if ri != rj {
                    parent[rj] = ri;
                }
            }
        }
    }
    let mut groups: std::collections::HashMap<usize, Vec<Term>> = std::collections::HashMap::new();
    for i in 0..n {
        let r = find(&mut parent, i);
        groups.entry(r).or_default().push(vars[i]);
    }
    let has_eq = |a: Term, b: Term| -> bool {
        head.iter().any(|l| matches!(*l, Lit::Eq { s, t } if (s == a && t == b) || (s == b && t == a)))
    };
    let mut out: Vec<(Vec<Term>, bool)> = Vec::new();
    for (_, mut g) in groups {
        if g.len() < 2 {
            continue;
        }
        g.sort();
        let strict = (0..g.len())
            .all(|i| ((i + 1)..g.len()).all(|j| has_eq(g[i], g[j])));
        out.push((g, strict));
    }
    out.sort();
    out
}

/// A clause derived inside a context: `body -> head` with body a conjunction of
/// predicates and head a disjunction of literals.
#[derive(Clone, Debug)]
pub struct ContextClause {
    pub body: Vec<Pred>,
    pub head: Vec<Lit>,
    /// Cached maximal head literals under the context ordering.
    pub max_head: Vec<Lit>,
}

impl ContextClause {
    pub fn new(body: Vec<Pred>, head: Vec<Lit>, root: bool, sig: &Sig) -> ContextClause {
        let body = sort_dedup_pred(body);
        let head = sort_dedup_lit(head);
        let max_head = max_head_literals(&head, root, sig);
        ContextClause {
            body,
            head,
            max_head,
        }
    }

    pub fn is_horn(&self) -> bool {
        self.head.len() <= 1
    }
    /// `true` iff every head literal is a pred trigger (so this clause can be
    /// pushed back to predecessor contexts by the Pred rule).
    pub fn is_clause_head_for_pred(&self, sig: &Sig) -> bool {
        self.head.iter().all(|l| l.is_pred_trigger(sig))
    }
    /// Head tautology: contains `Eq(s,s)`, or both `Eq(s,t)` and `Ineq(s,t)`.
    pub fn is_head_tautology(&self) -> bool {
        for l in &self.head {
            if let Lit::Eq { s, t } = *l {
                if s == t {
                    return true;
                }
                if self
                    .head
                    .iter()
                    .any(|k| matches!(*k, Lit::Ineq { s: a, t: b } if a == s && b == t))
                {
                    return true;
                }
            }
        }
        false
    }
    /// Maximal head predicates (the predicate subset of `max_head`).
    pub fn max_head_predicates(&self) -> impl Iterator<Item = (Pred, Lit)> + '_ {
        self.max_head.iter().filter_map(|l| match l {
            Lit::P(p) => Some((*p, *l)),
            _ => None,
        })
    }

    /// Strengthening test: returns -1 if `self` strengthens `that` (or equal),
    /// +1 if `that` strengthens `self`, 0 otherwise. A clause `c1` strengthens
    /// `c2` iff `c1.body ⊆ c2.body` and `c1.head ⊆ c2.head`.
    pub fn test_strengthening(&self, that: &ContextClause) -> i32 {
        if subset_pred(&self.body, &that.body) && subset_lit(&self.head, &that.head) {
            -1
        } else if subset_pred(&that.body, &self.body) && subset_lit(&that.head, &self.head) {
            1
        } else {
            0
        }
    }

    pub fn key(&self) -> (Vec<Pred>, Vec<Lit>) {
        (self.body.clone(), self.head.clone())
    }
}

/// Compute the ordering-maximal head literals: `l` is maximal iff there is no
/// different `k` in the head with `l <= k`.
pub fn max_head_literals(head: &[Lit], root: bool, sig: &Sig) -> Vec<Lit> {
    head.iter()
        .copied()
        .filter(|l| head.iter().all(|k| k == l || !lteq(l, k, root, sig)))
        .collect()
}
