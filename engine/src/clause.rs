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
        OntologyClause {
            body,
            head,
            sym_groups,
        }
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
    let swap = |a: Term, b: Term| {
        move |t: Term| {
            if t == a {
                b
            } else if t == b {
                a
            } else {
                t
            }
        }
    };
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
        head.iter()
            .any(|l| matches!(*l, Lit::Eq { s, t } if (s == a && t == b) || (s == b && t == a)))
    };
    let mut out: Vec<(Vec<Term>, bool)> = Vec::new();
    for (_, mut g) in groups {
        if g.len() < 2 {
            continue;
        }
        g.sort();
        let strict = (0..g.len()).all(|i| ((i + 1)..g.len()).all(|j| has_eq(g[i], g[j])));
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
    /// Bitmask over `head` positions of the ordering-maximal literals: bit `i`
    /// is set iff `head[i]` is maximal.  Replaces a cached `Vec<Lit>` copy of
    /// the maximal literals — one fewer heap allocation and no duplicated
    /// literals per clause (the dominant per-clause memory cost; see
    /// `max_head()`).  Heads with more than 64 literals (vanishingly rare) fall
    /// back to "all maximal", a sound over-approximation: Hyper firing on a
    /// non-maximal literal is sound, only less pruning.
    pub max_head_mask: u64,
}

impl ContextClause {
    pub fn new(body: Vec<Pred>, head: Vec<Lit>, root: bool, sig: &Sig) -> ContextClause {
        let body = sort_dedup_pred(body);
        let head = sort_dedup_lit(head);
        let max_head_mask = compute_max_head_mask(&head, root, sig);
        ContextClause {
            body,
            head,
            max_head_mask,
        }
    }

    /// Construct from vectors already in strict canonical order. Rule hot
    /// paths that merge canonical premises can avoid sorting the merged clause
    /// again. The public contract remains checked in debug/test builds.
    pub fn from_sorted_unique(
        body: Vec<Pred>,
        head: Vec<Lit>,
        root: bool,
        sig: &Sig,
    ) -> ContextClause {
        debug_assert!(body.windows(2).all(|pair| pair[0] < pair[1]));
        debug_assert!(head.windows(2).all(|pair| pair[0] < pair[1]));
        let max_head_mask = compute_max_head_mask(&head, root, sig);
        ContextClause {
            body,
            head,
            max_head_mask,
        }
    }

    /// Iterate the ordering-maximal head literals, decoded from
    /// `max_head_mask`.  Replaces the old cached `max_head: Vec<Lit>` field;
    /// yields `head[i]` for each set bit (or every head literal when the head
    /// exceeds 64 literals, the sound over-approximation).
    #[inline]
    pub fn max_head(&self) -> impl Iterator<Item = Lit> + '_ {
        let all = self.head.len() > 64;
        self.head.iter().enumerate().filter_map(move |(i, &l)| {
            if all || (self.max_head_mask >> i) & 1 == 1 {
                Some(l)
            } else {
                None
            }
        })
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
        self.max_head().filter_map(|l| match l {
            Lit::P(p) => Some((p, l)),
            _ => None,
        })
    }

    /// Does `self` strengthen (subsume) `that`?  A clause `c1` strengthens `c2`
    /// iff `c1.body ⊆ c2.body` and `c1.head ⊆ c2.head`.  This is exactly the
    /// `-1` case of `test_strengthening`, but computed without the reverse
    /// (`+1`-direction) subset scans.  The subsumption loops (`fwd_subsumed`,
    /// `back_subsume`) only ever ask this single direction, so evaluating the
    /// `+1`/`0` distinction there is wasted work: on the common case (a
    /// candidate that does NOT subsume) the old `test_strengthening` still paid
    /// two extra `subset_*` scans before returning `0`.  Same antichain, same
    /// fixpoint — just the one-directional predicate the callers actually use.
    #[inline]
    pub fn strengthens(&self, that: &ContextClause) -> bool {
        subset_pred(&self.body, &that.body) && subset_lit(&self.head, &that.head)
    }

    /// Strengthening test: returns -1 if `self` strengthens `that` (or equal),
    /// +1 if `that` strengthens `self`, 0 otherwise. A clause `c1` strengthens
    /// `c2` iff `c1.body ⊆ c2.body` and `c1.head ⊆ c2.head`.
    pub fn test_strengthening(&self, that: &ContextClause) -> i32 {
        if self.strengthens(that) {
            -1
        } else if that.strengthens(self) {
            1
        } else {
            0
        }
    }

    pub fn key(&self) -> (Vec<Pred>, Vec<Lit>) {
        (self.body.clone(), self.head.clone())
    }
}

/// splitmix64 finaliser: a cheap deterministic scrambler for the small integer
/// tuples a `Pred`/`Lit` is made of.  Only used to pick a signature bit, so
/// collisions cost recall in the filter, never correctness.
#[inline(always)]
fn mix64(mut x: u64) -> u64 {
    x ^= x >> 30;
    x = x.wrapping_mul(0xbf58_476d_1ce4_e5b9);
    x ^= x >> 27;
    x = x.wrapping_mul(0x94d0_49bb_1331_11eb);
    x ^= x >> 31;
    x
}

#[inline(always)]
fn pred_code(p: &Pred) -> u64 {
    match *p {
        Pred::Concept { iri, t } => mix64(((iri as u64) << 32) | (t as u64)),
        Pred::Role { iri, s, t } => {
            mix64(((iri as u64) << 32) | (s as u64)) ^ mix64(((t as u64) << 1) | 1)
        }
    }
}

#[inline(always)]
fn lit_code(l: &Lit) -> u64 {
    match *l {
        Lit::P(p) => pred_code(&p),
        Lit::Eq { s, t } => mix64(((s as u64) << 32) | (t as u64) | (1 << 63)),
        Lit::Ineq { s, t } => mix64(((s as u64) << 32) | (t as u64)) ^ 0x5bf0_3635_ca62_9163,
    }
}

/// Dense subsumption pre-filter for one interned context clause.
///
/// Both subsumption directions ask a pair of set inclusions, `c1.body ⊆
/// c2.body` and `c1.head ⊆ c2.head`.  Each field below records a *necessary*
/// condition for those inclusions: the multiset sizes, and a 64-bit Bloom
/// signature (one bit per literal, `1 << (code & 63)`).  `a ⊆ b` implies
/// `|a| <= |b|` and `sig(a) & !sig(b) == 0`, so a candidate failing either test
/// provably cannot subsume and is skipped without touching the clause itself.
///
/// The point is memory locality, not arithmetic: the signatures live in a flat
/// array parallel to the clause arena, so scanning a long posting list reads
/// 24 dense bytes per candidate instead of chasing the two heap vectors of a
/// `ContextClause`.  The surviving candidates still go through the exact
/// `strengthens` check, so the accepted set — hence the derived fixpoint — is
/// unchanged.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ClauseSig {
    pub body_len: u32,
    pub head_len: u32,
    pub body_sig: u64,
    pub head_sig: u64,
}

impl ClauseSig {
    pub fn of(c: &ContextClause) -> ClauseSig {
        let mut body_sig = 0u64;
        for p in &c.body {
            body_sig |= 1u64 << (pred_code(p) & 63);
        }
        let mut head_sig = 0u64;
        for l in &c.head {
            head_sig |= 1u64 << (lit_code(l) & 63);
        }
        ClauseSig {
            body_len: c.body.len() as u32,
            head_len: c.head.len() as u32,
            body_sig,
            head_sig,
        }
    }

    /// Necessary condition for `self`'s clause to strengthen `that`'s clause.
    /// `false` means "provably does not subsume"; `true` means "must run the
    /// exact `strengthens` check".
    #[inline(always)]
    pub fn may_strengthen(&self, that: &ClauseSig) -> bool {
        self.body_len <= that.body_len
            && self.head_len <= that.head_len
            && self.body_sig & !that.body_sig == 0
            && self.head_sig & !that.head_sig == 0
    }
}

#[cfg(test)]
mod strengthens_tests {
    use super::*;

    fn cc(body: Vec<Pred>, head: Vec<Lit>) -> ContextClause {
        ContextClause::new(body, head, false, &Sig::default())
    }
    fn cpt(iri: Iri, t: Term) -> Pred {
        Pred::Concept { iri, t }
    }

    /// Invariance guard for the one-directional `strengthens` predicate that the
    /// three subsumption call sites now use in place of
    /// `test_strengthening(..) == -1`.  On every ordered pair drawn from a
    /// spread of bodies and heads it must agree BOTH with the `-1` branch of
    /// `test_strengthening` (the function it replaces) AND with the naive
    /// set-subset definition it encodes.  Any divergence would change the
    /// derived antichain, so this is the fixpoint-preservation contract.
    #[test]
    fn strengthens_matches_test_strengthening_and_subset_oracle() {
        let (a, b, c) = (cpt(1, X), cpt(2, X), cpt(3, X));
        let (ha, hb, hc) = (
            Lit::P(cpt(10, X)),
            Lit::P(cpt(11, X)),
            Lit::P(cpt(12, X)),
        );
        let bodies = vec![
            vec![],
            vec![a],
            vec![b],
            vec![a, b],
            vec![b, c],
            vec![a, b, c],
        ];
        let heads = vec![
            vec![],
            vec![ha],
            vec![hb],
            vec![ha, hb],
            vec![hb, hc],
            vec![ha, hb, hc],
        ];
        let mut clauses = Vec::new();
        for body in &bodies {
            for head in &heads {
                clauses.push(cc(body.clone(), head.clone()));
            }
        }
        for x in &clauses {
            for y in &clauses {
                // strengthens == the -1 branch of test_strengthening.
                assert_eq!(
                    x.strengthens(y),
                    x.test_strengthening(y) == -1,
                    "strengthens vs test_strengthening==-1 diverge:\n x={x:?}\n y={y:?}"
                );
                // strengthens == naive set-subset (body ⊆ body ∧ head ⊆ head).
                let naive = x.body.iter().all(|p| y.body.contains(p))
                    && x.head.iter().all(|l| y.head.contains(l));
                assert_eq!(
                    x.strengthens(y),
                    naive,
                    "strengthens vs subset oracle diverge:\n x={x:?}\n y={y:?}"
                );
            }
        }
    }

    /// The refactor must leave `test_strengthening`'s three-way result
    /// unchanged, now expressed through `strengthens` on both directions.
    #[test]
    fn test_strengthening_three_way_still_consistent() {
        let (a, b) = (cpt(1, X), cpt(2, X));
        let x = cc(vec![a], vec![]); // body {a}
        let y = cc(vec![a, b], vec![]); // body {a,b} ⊋ {a}
        // Fewer body atoms strengthens: -1 from x, +1 from y.
        assert_eq!(x.test_strengthening(&y), -1);
        assert_eq!(y.test_strengthening(&x), 1);
        assert!(x.strengthens(&y));
        assert!(!y.strengthens(&x));
        // Equal clauses strengthen each other (the -1 case includes equality).
        assert_eq!(x.test_strengthening(&x), -1);
        assert!(x.strengthens(&x));
        // Incomparable bodies {a} vs {b}: 0, and neither strengthens.
        let z = cc(vec![b], vec![]);
        assert_eq!(x.test_strengthening(&z), 0);
        assert!(!x.strengthens(&z));
        assert!(!z.strengthens(&x));
    }
}

/// Compute the maximal-head bitmask: bit `i` set iff `head[i]` is maximal
/// (no different `k` in the head with `head[i] <= k`).  Heads longer than 64
/// literals get mask 0 and rely on the "all maximal" fallback in `max_head()`.
pub fn compute_max_head_mask(head: &[Lit], root: bool, sig: &Sig) -> u64 {
    if head.len() > 64 {
        return 0;
    }
    let mut mask = 0u64;
    for (i, l) in head.iter().enumerate() {
        if head.iter().all(|k| k == l || !lteq(l, k, root, sig)) {
            mask |= 1u64 << i;
        }
    }
    mask
}

#[cfg(test)]
mod maximal_head_tests {
    use super::*;

    #[test]
    fn incomparable_same_term_concepts_are_both_maximal() {
        let mut sig = Sig::default();
        let left = sig.concept("Left");
        let right = sig.concept("Right");
        let head = [
            Lit::P(Pred::Concept { iri: left, t: X }),
            Lit::P(Pred::Concept { iri: right, t: X }),
        ];
        assert_eq!(compute_max_head_mask(&head, true, &sig), 0b11);
    }
}
