//! Core data structures for the disjunctive context calculus of
//! Tena-Cucala, Cuenca Grau, and Horrocks (CB reasoning for ALCHOIQ / SROIQ),
//! as implemented in the Sequoia reasoner.
//!
//! Faithful Rust port of the term / predicate / literal / clause representation
//! and the *context literal ordering* (`clauses/package.scala`,
//! `clauses/Term.scala`).
//!
//! Term encoding (identical to Sequoia `clauses/Term.scala`):
//!   * central variable `x`        -> id  0
//!   * predecessor variable `y`    -> id -1
//!   * neighbour variable `z_i`    -> id -(i+1)   (i >= 1)
//!   * successor term `f_i(x)`     -> id +i       (i >= 1)
//! Term order is the integer order on ids, so  z_i < y < x < o_k < f_i(x)
//! < f_i(o_k); function terms are maximal, which orients paramodulation
//! downward. Individuals (nominal constants, ALCHOIQ calculus — see
//! docs/NOMINALS-CB.md) sit between x and the function terms: this total
//! order satisfies Def 3 of arXiv:1805.01396 given the pred-trigger-bottom
//! refinement in `pred_lteq` (its condition 6 only needs predecessor-trigger
//! atoms not to dominate non-trivial terms, which that refinement enforces).
//! Composite `f(o)` terms (root-context successors) live above all `f(x)`
//! terms and embed the (function, individual) pair order positionally so the
//! congruence condition `f(o1) ≻ f(o2) ⟺ o1 ≻ o2` holds on the raw ids.

use std::collections::HashMap;

/// A term is just its integer id (see module docs).
pub type Term = i32;

pub const X: Term = 0;
pub const Y: Term = -1;
/// Individuals occupy `1 .. FTERM_BASE`.
pub const FTERM_BASE: Term = 1 << 24;
/// `f(x)` Skolem terms occupy `FTERM_BASE .. COMP_BASE`.
pub const COMP_BASE: Term = 1 << 30;
/// Composite `f(o)` terms occupy `COMP_BASE ..`: `(f - FTERM_BASE)` in the
/// bits above `COMP_IND_BITS`, the individual id in the low bits.
pub const COMP_IND_BITS: u32 = 14;

#[inline]
pub fn zvar(i: i32) -> Term {
    debug_assert!(i >= 1);
    -(i + 1)
}
#[inline]
pub fn fterm(i: i32) -> Term {
    debug_assert!(i >= 1 && i < COMP_BASE - FTERM_BASE);
    FTERM_BASE + i
}
/// Individual (nominal constant) term, id `k >= 1`.
#[inline]
pub fn ind_term(k: i32) -> Term {
    debug_assert!(k >= 1 && k < FTERM_BASE);
    k
}
#[inline]
pub fn is_central(t: Term) -> bool {
    t == 0
}
#[inline]
pub fn is_pred_var(t: Term) -> bool {
    t == -1
}
#[inline]
pub fn is_neighbour(t: Term) -> bool {
    t < 0
}
#[inline]
pub fn is_var(t: Term) -> bool {
    t <= 0
}
#[inline]
pub fn is_individual(t: Term) -> bool {
    t >= 1 && t < FTERM_BASE
}
/// `true` for Skolem terms: both `f(x)` and root-context `f(o)` composites.
#[inline]
pub fn is_function(t: Term) -> bool {
    t >= FTERM_BASE
}
/// Composite `f(o)` term for `f = fterm(i)` and individual `o = ind_term(k)`.
/// Panics (never silently wraps) when the ontology exceeds the packed ranges;
/// nominal-mode scale limits are reported, not approximated.
#[inline]
pub fn comp_term(f: Term, o: Term) -> Term {
    debug_assert!(is_function(f) && f < COMP_BASE && is_individual(o));
    let fi = f - FTERM_BASE;
    assert!(
        fi < (1 << (30 - COMP_IND_BITS)) && o < (1 << COMP_IND_BITS),
        "nominal mode: f(o) term space exhausted (f id {fi}, individual {o})"
    );
    COMP_BASE + (fi << COMP_IND_BITS) + o
}
#[inline]
pub fn is_comp(t: Term) -> bool {
    t >= COMP_BASE
}
#[inline]
pub fn term_max(a: Term, b: Term) -> Term {
    a.max(b)
}

/// Interned IRI id with a flag for whether the concept/role is a *named*
/// (query-classifiable) symbol of the input ontology or an *internal*
/// auxiliary introduced by normalisation (e.g. the `Q_i` disjuncts).
pub type Iri = u32;

/// Predicate atom: `Concept(iri, t)` or `Role(iri, s, t)`.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum Pred {
    /// `iri(t)`
    Concept { iri: Iri, t: Term },
    /// `iri(s, t)`
    Role { iri: Iri, s: Term, t: Term },
}

impl Pred {
    #[inline]
    pub fn max_term(&self) -> Term {
        match *self {
            Pred::Concept { t, .. } => t,
            Pred::Role { s, t, .. } => term_max(s, t),
        }
    }
    #[inline]
    pub fn has_central_variable(&self) -> bool {
        match *self {
            Pred::Concept { t, .. } => is_central(t),
            Pred::Role { .. } => true,
        }
    }
    #[inline]
    pub fn is_function_free(&self) -> bool {
        match *self {
            Pred::Concept { t, .. } => !is_function(t),
            Pred::Role { s, t, .. } => !is_function(s) && !is_function(t),
        }
    }
    pub fn apply(&self, sigma: &dyn Fn(Term) -> Term) -> Pred {
        match *self {
            Pred::Concept { iri, t } => Pred::Concept { iri, t: sigma(t) },
            Pred::Role { iri, s, t } => Pred::Role {
                iri,
                s: sigma(s),
                t: sigma(t),
            },
        }
    }
}

/// Head literal: a predicate, or an (in)equality with `s >= t` in the term order.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum Lit {
    P(Pred),
    /// `s == t`, normalised so `s >= t`.
    Eq { s: Term, t: Term },
    /// `s != t`, normalised so `s >= t`.
    Ineq { s: Term, t: Term },
}

impl Lit {
    pub fn eq(a: Term, b: Term) -> Lit {
        if a >= b {
            Lit::Eq { s: a, t: b }
        } else {
            Lit::Eq { s: b, t: a }
        }
    }
    pub fn ineq(a: Term, b: Term) -> Lit {
        if a >= b {
            Lit::Ineq { s: a, t: b }
        } else {
            Lit::Ineq { s: b, t: a }
        }
    }
    #[inline]
    pub fn max_term(&self) -> Term {
        match *self {
            Lit::P(p) => p.max_term(),
            Lit::Eq { s, .. } | Lit::Ineq { s, .. } => s,
        }
    }
    #[inline]
    pub fn is_valid_equation(&self) -> bool {
        matches!(*self, Lit::Eq { s, t } if s == t)
    }
    #[inline]
    pub fn is_invalid_equation(&self) -> bool {
        matches!(*self, Lit::Ineq { s, t } if s == t)
    }
    #[inline]
    pub fn is_function_free(&self) -> bool {
        match *self {
            Lit::P(p) => p.is_function_free(),
            Lit::Eq { s, t } | Lit::Ineq { s, t } => !is_function(s) && !is_function(t),
        }
    }
    pub fn apply(&self, sigma: &dyn Fn(Term) -> Term) -> Lit {
        match *self {
            Lit::P(p) => Lit::P(p.apply(sigma)),
            Lit::Eq { s, t } => Lit::eq(sigma(s), sigma(t)),
            Lit::Ineq { s, t } => Lit::ineq(sigma(s), sigma(t)),
        }
    }
    /// Rewrite the maximal side `l` of this literal to `r` (paramodulation).
    pub fn rewrite(&self, l: Term, r: Term) -> Option<Lit> {
        match *self {
            Lit::P(Pred::Concept { iri, t }) if t == l => Some(Lit::P(Pred::Concept { iri, t: r })),
            Lit::P(Pred::Role { iri, s, t }) => {
                if s == l {
                    Some(Lit::P(Pred::Role { iri, s: r, t }))
                } else if t == l {
                    Some(Lit::P(Pred::Role { iri, s, t: r }))
                } else {
                    None
                }
            }
            Lit::Eq { s, t } if s == l => Some(Lit::eq(r, t)),
            Lit::Ineq { s, t } if s == l => Some(Lit::ineq(r, t)),
            _ => None,
        }
    }
    pub fn contains_at_rewrite_position(&self, l: Term) -> bool {
        match *self {
            Lit::P(Pred::Concept { t, .. }) => t == l,
            Lit::P(Pred::Role { s, t, .. }) => s == l || t == l,
            Lit::Eq { s, .. } | Lit::Ineq { s, .. } => s == l,
        }
    }
}

/// Global, immutable trigger / classification information about the ontology
/// signature, used to decide Succ/Pred triggers and the ordering.
#[derive(Default, Clone)]
pub struct Sig {
    /// `iri` of every concept name in interning order; reverse map for output.
    pub concept_names: Vec<String>,
    pub role_names: Vec<String>,
    pub concept_id: HashMap<String, Iri>,
    pub role_id: HashMap<String, Iri>,
    /// `true` if concept iri is an internal auxiliary (not a query concept).
    pub concept_internal: Vec<bool>,
    /// Su / Pr trigger sets (computed from ontology clause bodies).
    pub concept_succ_trigger: Vec<bool>,
    /// `true` if concept iri is a transitivity/role-chain *reachability*
    /// bookkeeping concept (`__trans__…` / `__chain__…`).  These never occur as
    /// existential fillers — they are only ever derived in clause heads on the
    /// central variable — so a `reach(f)` fact on a successor `f` is always a
    /// redundant push-back of what `f`'s own (sub-)context already derived
    /// natively.  Excluding them from Succ triggers keeps the successor's core
    /// from growing on pushed-back reachability (which otherwise spawns a
    /// combinatorial cascade of grown-core contexts that overruns the message
    /// budget and drops deep reachability), without losing any derivation.
    pub concept_reach: Vec<bool>,
    pub forward_role_succ_trigger: Vec<bool>,
    pub backward_role_succ_trigger: Vec<bool>,
    /// concept iris asserted unsatisfiable (body length 1, empty head).
    pub nothing: Vec<bool>,
    /// the special `owl:Nothing` concept id, if present.
    pub bottom: Option<Iri>,
}

impl Sig {
    pub fn concept(&mut self, name: &str) -> Iri {
        if let Some(&id) = self.concept_id.get(name) {
            return id;
        }
        let id = self.concept_names.len() as Iri;
        self.concept_names.push(name.to_string());
        self.concept_id.insert(name.to_string(), id);
        let internal = is_internal_concept(name);
        self.concept_internal.push(internal);
        self.concept_succ_trigger.push(false);
        self.concept_reach.push(is_reach_concept(name));
        self.nothing.push(false);
        id
    }
    pub fn role(&mut self, name: &str) -> Iri {
        if let Some(&id) = self.role_id.get(name) {
            return id;
        }
        let id = self.role_names.len() as Iri;
        self.role_names.push(name.to_string());
        self.role_id.insert(name.to_string(), id);
        self.forward_role_succ_trigger.push(false);
        self.backward_role_succ_trigger.push(false);
        id
    }
    #[inline]
    pub fn is_internal(&self, iri: Iri) -> bool {
        self.concept_internal
            .get(iri as usize)
            .copied()
            .unwrap_or(true)
    }
    #[inline]
    pub fn is_reach(&self, iri: Iri) -> bool {
        self.concept_reach.get(iri as usize).copied().unwrap_or(false)
    }
    #[inline]
    pub fn is_nothing_concept(&self, iri: Iri) -> bool {
        self.nothing.get(iri as usize).copied().unwrap_or(false)
            || self.bottom == Some(iri)
    }
    #[inline]
    pub fn is_nothing_pred(&self, p: &Pred) -> bool {
        matches!(*p, Pred::Concept { iri, .. } if self.is_nothing_concept(iri))
    }
}

/// Heuristic: concept names introduced by the moose normaliser as auxiliary
/// disjuncts/definers are internal (not query concepts). Everything else is a
/// named class to be classified.
pub fn is_internal_concept(name: &str) -> bool {
    // `Q_0`, `Q_12`, ... ; also any `owl:Nothing`/`owl:Thing` are special.
    let short = name.rsplit(['#', '/']).next().unwrap_or(name);
    if let Some(rest) = short.strip_prefix("Q_") {
        return rest.chars().all(|c| c.is_ascii_digit()) && !rest.is_empty();
    }
    // normaliser/preprocessing auxiliaries: nominal proxies (`__nom__o`),
    // transitivity reachability concepts (`__trans__…`), and definers.
    short.starts_with("__")
        || short.starts_with("_aux")
        || short.starts_with("aux_")
        || short.starts_with("def_")
}

/// `true` for the transitivity / role-chain *reachability* bookkeeping concepts
/// introduced by `preprocess` (`__trans__ROLE__C…`, `__chain__ROLE__C…`).  These
/// only ever appear in clause heads on the central variable, never as
/// existential fillers, so they are never a genuine "fresh hypothesis" on a
/// successor — see `Sig::concept_reach`.
pub fn is_reach_concept(name: &str) -> bool {
    let short = name.rsplit(['#', '/']).next().unwrap_or(name);
    short.starts_with("__trans__") || short.starts_with("__chain__")
}

// ----------------------------- triggers ------------------------------------

impl Pred {
    /// `true` iff this head predicate (with a function term) is a Succ trigger,
    /// i.e. it must be propagated to the successor context.
    ///
    /// We push every head predicate that mentions a function term and a central
    /// variable (concepts `C(f(x))` and roles `R(x,f(x))` / `R(f(x),x)` in
    /// either orientation).  Pushing the role edge in both orientations — rather
    /// than only when the role's trigger bit is set — is required so the
    /// successor learns its incoming edge and can discharge axioms such as
    /// `∃R.C ⊑ D` about its predecessor.  Over-pushing is sound (it only adds
    /// hypotheses to the successor).
    pub fn is_succ_trigger(&self, sig: &Sig) -> bool {
        match *self {
            // Reachability bookkeeping concepts (`__trans__`/`__chain__`) are
            // never existential fillers, so `reach(f)` on a successor is always a
            // redundant push-back of what `f`'s own context derived natively.
            // Pushing it back would grow `f`'s core and spawn grown-core context
            // churn; skip it (the fact still flows to predecessors via Pred).
            Pred::Concept { iri, t } => is_function(t) && !sig.is_reach(iri),
            Pred::Role { s, t, .. } => {
                (is_central(s) && is_function(t)) || (is_central(t) && is_function(s))
            }
        }
    }
    /// `true` iff this predicate is a Pred trigger (member of Pr).
    pub fn is_pred_trigger(&self, sig: &Sig) -> bool {
        match *self {
            Pred::Concept { t, .. } => is_pred_var(t),
            Pred::Role { iri, s, t } => {
                (is_central(s)
                    && is_pred_var(t)
                    && sig.backward_role_succ_trigger.get(iri as usize).copied().unwrap_or(false))
                    || (is_central(t)
                        && is_pred_var(s)
                        && sig.forward_role_succ_trigger.get(iri as usize).copied().unwrap_or(false))
            }
        }
    }
}

impl Lit {
    pub fn is_pred_trigger(&self, sig: &Sig) -> bool {
        match self {
            Lit::P(p) => p.is_pred_trigger(sig),
            _ => false,
        }
    }
}

// --------------------------- context ordering ------------------------------

/// The context literal ordering `lteq` (faithful port of
/// `ContextLiteralOrdering.lteq` in `clauses/package.scala`).
///
/// Returns `true` iff `o1 <= o2` in the (partial) context literal order.
/// `root` selects the root-context refinement (query concepts mutually
/// incomparable so that every entailed `A(x)` is retained).
pub fn lteq(o1: &Lit, o2: &Lit, root: bool, sig: &Sig) -> bool {
    use Lit::*;
    match (o1, o2) {
        (Eq { s: l1, t: r1 }, Eq { s: l2, t: r2 })
        | (Eq { s: l1, t: r1 }, Ineq { s: l2, t: r2 })
        | (Ineq { s: l1, t: r1 }, Ineq { s: l2, t: r2 }) => l1 < l2 || (l1 == l2 && r1 <= r2),
        (Ineq { s: l1, t: r1 }, Eq { s: l2, t: r2 }) => l1 < l2 || (l1 == l2 && r1 < r2),

        // equation vs predicate
        (eqn @ (Eq { .. } | Ineq { .. }), P(p)) => {
            let es = eqn_s(eqn);
            match p {
                Pred::Concept { t, .. } => es <= *t,
                Pred::Role { s, t, .. } => es <= *s || es <= *t,
            }
        }
        (P(p), eqn @ (Eq { .. } | Ineq { .. })) => {
            let es = eqn_s(eqn);
            match p {
                Pred::Concept { t, .. } => !(es <= *t),
                Pred::Role { s, t, .. } => !(es <= *s || es <= *t),
            }
        }

        (P(p1), P(p2)) => pred_lteq(p1, p2, root, sig),
    }
}

#[inline]
fn eqn_s(l: &Lit) -> Term {
    match *l {
        Lit::Eq { s, .. } | Lit::Ineq { s, .. } => s,
        _ => unreachable!(),
    }
}

fn pred_lteq(p1: &Pred, p2: &Pred, _root: bool, sig: &Sig) -> bool {
    // Pred-trigger cases (bottom of the order).
    let p1pt = p1.is_pred_trigger(sig);
    let p2pt = p2.is_pred_trigger(sig);
    if p2pt {
        return p1 == p2;
    }
    if p1pt && !p2pt {
        return true;
    }
    // Concept literals on the SAME term are mutually incomparable: each is a
    // maximal head literal, so Hyper fires on EVERY disjunct of a head
    // disjunction.  This is required for completeness of disjunctive case
    // analysis -- e.g. {C⊔D, C⊑E, D⊑E} ⊢ E needs both C and D resolved, and a
    // total tie-break (by iri, or internal-definer-low) would leave the
    // non-maximal disjunct stuck, losing the inference (probe: A⊑∃R.(C⊔D),
    // C⊑E, D⊑E, ∃R.E⊑G ⊬ A⊑G).  The Lean completeness proof models Hyper as
    // resolution on an arbitrary atom (`CompletenessProp.lean`), so resolving
    // on every same-term disjunct -- named or internal definer -- is exactly
    // what the proof certifies.  This generalises the old root-only query-concept
    // refinement to every context and every concept.
    if let (Pred::Concept { iri: i1, t: t1 }, Pred::Concept { iri: i2, t: t2 }) = (p1, p2) {
        if t1 == t2 {
            return i1 == i2;
        }
        // Different terms: term-major (a literal on the larger term is larger,
        // so it is kept by max-head selection and drives Succ).
        return t1 < t2;
    }
    // Term-major across the remaining (role / mixed) cases.  Comparing roles by
    // their source term alone (rather than max(s,t)) broke this for
    // role-vs-concept and role-vs-role (audit M1).
    let m1 = p1.max_term();
    let m2 = p2.max_term();
    if m1 != m2 {
        return m1 < m2;
    }
    match (p1, p2) {
        (Pred::Role { iri: i1, s: s1, t: t1 }, Pred::Role { iri: i2, s: s2, t: t2 }) => {
            s1 < s2 || (s1 == s2 && (t1 < t2 || (t1 == t2 && i1 <= i2)))
        }
        // Same-term concept pairs handled above; unreachable here.
        (Pred::Concept { iri: i1, .. }, Pred::Concept { iri: i2, .. }) => i1 <= i2,
        (Pred::Role { .. }, Pred::Concept { .. }) => false,
        (Pred::Concept { .. }, Pred::Role { .. }) => true,
    }
}
