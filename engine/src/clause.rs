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
}

impl OntologyClause {
    pub fn new(body: Vec<Pred>, head: Vec<Lit>) -> OntologyClause {
        OntologyClause {
            body: sort_dedup_pred(body),
            head: sort_dedup_lit(head),
        }
    }
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
