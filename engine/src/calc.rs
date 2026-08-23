//! Core data structures for the disjunctive context calculus of
//! Tena-Cucala, Cuenca Grau, and Horrocks (CB reasoning for ALCHOIQ / SROIQ),
//! as implemented in the Sequoia reasoner.
//!
//! Faithful Rust port of the term / predicate / literal / clause representation
//! and the *context literal ordering* (`clauses/package.scala`,
//! `clauses/Term.scala`).
//!
//! Term encoding preserves Sequoia's integer term order in a `u32` layout:
//!   * neighbour variables `z_i`, predecessor `y`, and central `x` occupy the
//!     first 2^16 ids, in that order;
//!   * named individuals follow `x`;
//!   * successor terms `f_i(x)` start at `FTERM_BASE`;
//!   * grounded successors `f_i(o_k)` start at `COMP_BASE`.
//! Thus `z_i < y < x < o_k < f_i(x)`
//! < f_i(o_k); function terms are maximal, which orients paramodulation
//! downward. Individuals (nominal constants, ALCHOIQ calculus — see
//! docs/NOMINALS-CB.md) sit between x and the function terms: this total
//! order satisfies Def 3 of arXiv:1805.01396 given the pred-trigger-bottom
//! refinement in `pred_lteq` (its condition 6 only needs predecessor-trigger
//! atoms not to dominate non-trivial terms, which that refinement enforces).
//! Composite `f(o)` terms (root-context successors) live above all `f(x)`
//! terms and embed the (function, individual) pair order positionally so the
//! congruence condition `f(o1) ≻ f(o2) ⟺ o1 ≻ o2` holds on the raw ids. Using
//! the full unsigned 32-bit space avoids the old signed packing ceiling hit by
//! assertion-heavy ontologies while keeping every stored term four bytes.

use std::collections::HashMap;
use std::sync::OnceLock;

/// A term is just its ordered unsigned integer id (see module docs).
pub type Term = u32;

/// Leave 2^16 ordered slots for Sequoia's variables. In normalized OWL clauses
/// the actual neighbour-variable count is tiny, but the explicit guard in
/// `zvar` makes exhaustion fail loudly rather than wrap.
pub const X: Term = (1 << 16) - 1;
pub const Y: Term = X - 1;
const IND_BASE: Term = X;
/// Individuals occupy `X + 1 .. FTERM_BASE` (983,040 available ids).
pub const FTERM_BASE: Term = 1 << 20;
/// `f(x)` Skolem terms occupy `FTERM_BASE .. COMP_BASE`.
pub const COMP_BASE: Term = 1 << 22;
/// Composite `f(o)` terms occupy `COMP_BASE ..`: `(f - FTERM_BASE)` in the
/// bits above `COMP_IND_BITS`, the raw individual id in the low bits. The
/// The default 17/15 split covers 131,071 named individuals and 32,735 Skolem
/// functions simultaneously, including ORE 15846 (129,647 / 20,932). A worker
/// may select another split through `KM_COMP_IND_BITS` before saturation. The
/// orchestrator derives that value from exact normalized-clause symbol counts;
/// for example, 15/17 covers ORE 1194 (18,055 individuals / 130,303 normalized
/// Skolem functions).
pub const COMP_IND_BITS: u32 = 17;
static ACTIVE_COMP_IND_BITS: OnceLock<u32> = OnceLock::new();

#[inline]
fn comp_ind_bits() -> u32 {
    *ACTIVE_COMP_IND_BITS.get_or_init(|| {
        let bits = std::env::var("KM_COMP_IND_BITS")
            .ok()
            .and_then(|value| value.parse::<u32>().ok())
            .unwrap_or(COMP_IND_BITS);
        assert!((1..32).contains(&bits), "KM_COMP_IND_BITS must be in 1..32");
        bits
    })
}

/// Active low-bit width used by the packed `f(o)` representation.  Certificate
/// evidence records this value so its consumer can decode the exact terms that
/// participated in saturation instead of assuming the default layout.
#[inline]
pub(crate) fn active_comp_ind_bits() -> u32 {
    comp_ind_bits()
}

/// Pick a positional split that represents every dense function and
/// individual id. Prefer the established 17-bit individual layout whenever it
/// fits, preserving byte-for-byte term ordering for the normal case.
pub fn choose_comp_ind_bits(functions: u64, individuals: u64) -> Option<u32> {
    let fits = |bits: u32| {
        let individual_limit = 1u64 << bits;
        individuals < individual_limit
            && functions
                .checked_shl(bits)
                .and_then(|base| base.checked_add(individuals))
                .is_some_and(|packed| packed <= (Term::MAX - COMP_BASE) as u64)
    };
    if fits(COMP_IND_BITS) {
        return Some(COMP_IND_BITS);
    }
    let minimum = if individuals == 0 {
        1
    } else {
        (u64::BITS - individuals.leading_zeros()).max(1)
    };
    (minimum..32).find(|&bits| fits(bits))
}

/// Pick the smallest individual field that can represent a dense individual
/// domain when the frontend did not retain an exact normalized-function count.
///
/// Ordinary classification intentionally omits the expensive clause-profile
/// scan. Using the minimum lossless individual width leaves the largest
/// possible remainder of the `u32` space for functions. It cannot make a
/// representable `(function, individual)` pair unrepresentable: every wider
/// split has no more function capacity. The encoded order remains function
/// first and individual second.
pub fn choose_comp_ind_bits_unknown_functions(individuals: u64) -> Option<u32> {
    let minimum = if individuals == 0 {
        1
    } else {
        (u64::BITS - individuals.leading_zeros()).max(1)
    };
    (minimum < 32).then_some(minimum)
}

#[inline]
pub fn zvar(i: i32) -> Term {
    assert!(
        i >= 1 && (i as Term) < Y,
        "neighbour-variable term space exhausted"
    );
    Y - i as Term
}
#[inline]
pub fn fterm(i: i32) -> Term {
    assert!(
        i >= 1 && (i as Term) < COMP_BASE - FTERM_BASE,
        "Skolem-function term space exhausted"
    );
    FTERM_BASE + i as Term
}
/// Individual (nominal constant) term, id `k >= 1`.
#[inline]
pub fn ind_term(k: i32) -> Term {
    assert!(
        k >= 1 && (k as Term) < FTERM_BASE - IND_BASE,
        "named-individual term space exhausted"
    );
    IND_BASE + k as Term
}
/// Recover the dense named-individual id used by the frontend interner.
#[inline]
pub fn ind_id(t: Term) -> i32 {
    debug_assert!(is_individual(t));
    (t - IND_BASE) as i32
}
#[inline]
pub fn is_central(t: Term) -> bool {
    t == X
}
#[inline]
pub fn is_pred_var(t: Term) -> bool {
    t == Y
}
#[inline]
pub fn is_neighbour(t: Term) -> bool {
    t < X
}
#[inline]
pub fn is_var(t: Term) -> bool {
    t <= X
}
#[inline]
pub fn is_individual(t: Term) -> bool {
    t > IND_BASE && t < FTERM_BASE
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
    let oi = o - IND_BASE;
    let bits = comp_ind_bits();
    let packed = ((fi as u64) << bits) + oi as u64;
    assert!(
        (oi as u64) < (1u64 << bits) && packed <= (Term::MAX - COMP_BASE) as u64,
        "nominal mode: f(o) term space exhausted (f id {fi}, individual {})",
        ind_id(o)
    );
    COMP_BASE + packed as Term
}
#[inline]
pub fn is_comp(t: Term) -> bool {
    t >= COMP_BASE
}
/// Decompose a composite `f(o)` term into `(f, o)` (the `fterm` and the
/// individual).
#[inline]
pub fn comp_parts(t: Term) -> (Term, Term) {
    debug_assert!(is_comp(t));
    let v = t - COMP_BASE;
    let bits = comp_ind_bits();
    (FTERM_BASE + (v >> bits), IND_BASE + (v & ((1 << bits) - 1)))
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
    /// `true` iff every term is an individual or an `f(o)` composite — a
    /// ground atom of the nominal calculus (B(o), S(o,o'), …). Ground body
    /// atoms are copied verbatim by the Pred rule rather than resolved
    /// against the predecessor (arXiv:1805.01396 Table 2).
    pub fn is_ground(&self) -> bool {
        fn g(t: Term) -> bool {
            is_individual(t) || is_comp(t)
        }
        match *self {
            Pred::Concept { t, .. } => g(t),
            Pred::Role { s, t, .. } => g(s) && g(t),
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
    Eq {
        s: Term,
        t: Term,
    },
    /// `s != t`, normalised so `s >= t`.
    Ineq {
        s: Term,
        t: Term,
    },
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
    /// `KM_RSUCC`: enable the r-Succ forward push of predecessor central
    /// reachability facts (`__trans__`/`__chain__(x)`) to successor contexts as
    /// edge-conditioned neighbour predicates, closing the transitive+inverse
    /// reconstruction completeness gap (tests/completeness-gaps; 7914
    /// UBERON_0001373/0008977).  Default off — opt-in until corpus-swept.
    pub rsucc: bool,
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
        self.concept_reach
            .get(iri as usize)
            .copied()
            .unwrap_or(false)
    }
    #[inline]
    pub fn is_nothing_concept(&self, iri: Iri) -> bool {
        self.nothing.get(iri as usize).copied().unwrap_or(false) || self.bottom == Some(iri)
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
            // Reachability bookkeeping concepts (`__trans__`/`__chain__`): in the
            // PURE-FORWARD case `reach(f)` on a successor is a redundant push-back
            // of what `f`'s own context derives natively, so excluding it avoids
            // grown-core churn.  But under r-Succ (KM_RSUCC) the transitive+inverse
            // refutation derives `reach(f)` in the predecessor ONLY after the
            // round-trip (predecessor pushes its central `reach(x)` as a neighbour
            // fact → successor fires the transitivity clause across the inverse
            // back-edge → the conditioned conclusion returns via Pred → predecessor
            // derives `reach(f)`), and `f`'s own context cannot re-derive it
            // natively (it would need to read its predecessor's reach).  So with
            // rsucc the `reach(f)` push is the final, load-bearing step — pushing
            // it gives the successor `reach` about itself and fires the clash.
            Pred::Concept { iri, t } => is_function(t) && (sig.rsucc || !sig.is_reach(iri)),
            Pred::Role { s, t, .. } => {
                (is_central(s) && is_function(t))
                    || (is_central(t) && is_function(s))
                    // Grounded existentials (nominal calculus): the parent of
                    // an `f(o)` successor is the individual o, so role atoms
                    // `S(o, f(o))` / `S(f(o), o)` trigger Succ exactly like
                    // `S(x, f(x))` / `S(f(x), x)` do.
                    || (is_individual(s) && is_comp(t) && comp_parts(t).1 == s)
                    || (is_individual(t) && is_comp(s) && comp_parts(s).1 == t)
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
                    && sig
                        .backward_role_succ_trigger
                        .get(iri as usize)
                        .copied()
                        .unwrap_or(false))
                    || (is_central(t)
                        && is_pred_var(s)
                        && sig
                            .forward_role_succ_trigger
                            .get(iri as usize)
                            .copied()
                            .unwrap_or(false))
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

/// `KM_ROOT_ONLY_INCOMP=1`: same-term concept incomparability only at root
/// contexts (cached once — the env cannot change mid-run).
fn root_only_incomp() -> bool {
    use std::sync::OnceLock;
    static FLAG: OnceLock<bool> = OnceLock::new();
    *FLAG.get_or_init(|| std::env::var_os("KM_ROOT_ONLY_INCOMP").is_some())
}

/// `KM_ORDERED_ALL=1`: ordered resolution in EVERY context, root included.
/// Same-term concept literals are totally ordered by iri (Hyper fires only on
/// the ordering-maximal disjunct). Sequoia-style ordered-resolution experiment
/// targeting the live-disjunction blow-up class (10702, 9540, 1603, ...).
///
/// EMPIRICAL VERDICT (2026-06-13 A/B, jobs 6123/6125): INCOMPLETE, do NOT use
/// as a default. The naive total order STALLS the consequence readout — an
/// entailed unit `⊤ → B(x)` is lost when B is a non-maximal disjunct whose
/// maximal partner is unresolvable. Measured: recovers 12698/2313/5107 ST, but
/// 12698 miss=1, 5107 miss=5 (recovered-but-incomplete), and it regresses the
/// previously-passing 13383 (miss=1: `…WithoutChangingOfDimension ⊑ Unit`, both
/// named). Only 2313 was gold-complete. A complete ordered variant needs the
/// Sequoia residue / negative-literal-selection machinery (deep engine work +
/// full revalidation) — deferred. Flag kept gated/off as a documented artifact.
fn ordered_all() -> bool {
    use std::sync::OnceLock;
    static FLAG: OnceLock<bool> = OnceLock::new();
    *FLAG.get_or_init(|| std::env::var_os("KM_ORDERED_ALL").is_some())
}

/// `KM_SEQ_ORDER=1`: Sequoia-faithful literal ordering on same-term concepts.
/// The fix for the live-disjunction blow-up that `KM_ORDERED_ALL` got wrong.
///
/// `KM_ORDERED_ALL` totally ordered ALL same-term concepts by raw iri — named
/// included — which stalls the readout: an entailed unit `⊤ → B(x)` is hidden
/// when the named super B sits non-maximally behind a maximal sibling.  Sequoia
/// keys the order on NAMED vs AUXILIARY, not on raw iri:
///   * INTERNAL definers/disjuncts (`Sig::is_internal`: `Q_*`, `def_*`,
///     `__trans__*`, ...) are TOTALLY ordered (by iri) and sit ABOVE the named
///     concepts → Hyper fires only on the ordering-maximal definer = ordered
///     resolution (the `CompletenessOrdered` regime), which tames the
///     normaliser-introduced disjunction explosion.
///   * NAMED (query-classifiable) concepts stay MUTUALLY INCOMPARABLE at the
///     bottom → Hyper fires on every named disjunct (the `CompletenessProp`
///     unrestricted regime), so a forced named unit always surfaces and the
///     forward `⊤ → B(x)` readout stays complete.  This is exactly the shape of
///     Sequoia's `ContextLiteralOrdering` (query concepts incomparable + below;
///     everything else ordered above), which is published-complete for SROIQ
///     classification.  Unlike `KM_ORDERED_ALL` it never orders named concepts
///     against each other, so it does not regress 13383.
/// Effective seq-order state. `2` = undecided (router has not run yet); `1`/`0`
/// = on/off as decided by the auto-router or an env override. Stored as a
/// process-global atomic so the parallel workers (set up after the router runs
/// in `Reasoner::saturate`) all observe the same value with a single relaxed
/// load in the `pred_lteq` hot path.
static SEQ_ORDER: std::sync::atomic::AtomicU8 = std::sync::atomic::AtomicU8::new(2);

/// Auto-route `KM_SEQ_ORDER`: enable the Sequoia definer ordering iff the
/// ontology has a disjunctive head containing an internal definer (the
/// `DISJ_INT >= 1` rule — the only onts that benefit; pure-Horn / named-only-
/// disjunction onts pay the `is_internal` overhead with no gain, so they route
/// off). Validated across the full ORE corpus (results/seqorder-routing-*.txt):
/// keeps all +6 recoveries and the meaningful speedups, avoids 27/28 slowdowns.
/// Both orderings are complete (named concepts stay incomparable either way), so
/// this only selects the faster validated regime per ontology. Env still wins:
/// `KM_SEQ_ORDER` forces on, `KM_NO_SEQ_ORDER` forces off.
pub fn set_seq_order_auto(on: bool) {
    let eff = if std::env::var_os("KM_SEQ_ORDER").is_some() {
        true
    } else if std::env::var_os("KM_NO_SEQ_ORDER").is_some() {
        false
    } else {
        on
    };
    SEQ_ORDER.store(
        if eff { 1 } else { 0 },
        std::sync::atomic::Ordering::Relaxed,
    );
}

fn seq_order() -> bool {
    match SEQ_ORDER.load(std::sync::atomic::Ordering::Relaxed) {
        1 => true,
        0 => false,
        // Router has not run (e.g. a code path that orders before saturation):
        // fall back to the explicit env flag, preserving the prior behaviour.
        _ => std::env::var_os("KM_SEQ_ORDER").is_some(),
    }
}

thread_local! {
    /// Direction B (docs/DISJUNCTION-SPLITTING.md): when set, same-term concepts
    /// are TOTALLY ordered (an ordered-resolution, tame, terminating closure).
    /// The splitting driver (reasoner.rs) turns this ON while saturating a branch
    /// — the residual fact-disjunctions then become split points, and the driver
    /// recovers what the total order hides by branching on them — and turns it
    /// OFF for the complete-ordering FALLBACK run (a query whose closure carries
    /// a disjunction the propositional-on-x driver cannot split). Ordered
    /// resolution alone is incomplete (the `KM_ORDERED_ALL` verdict); ordered +
    /// splitting is complete (the split is exhaustive case analysis), and the
    /// fallback must therefore use the unordered (complete) regime — hence the
    /// per-run thread-local rather than a process-global flag.
    static BRANCH_ORDERED: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Set the Direction-B branch-ordered mode for the current thread (the
/// splitting driver toggles this around branch vs fallback runs).
pub fn set_branch_ordered(b: bool) {
    BRANCH_ORDERED.with(|c| c.set(b));
}

thread_local! {
    /// Direction A (docs/ROOT-ORDERED-RESOLUTION.md): `KM_ROOT_ORDERED` mode for
    /// the current thread. `0` = off (default; the complete incomparable
    /// regime). `1` = same-term concept literals TOTALLY ordered in ROOT
    /// contexts (internal definers above named concepts, iri tie-break within
    /// each block); non-root contexts unchanged. `2` = the same total order in
    /// EVERY context (the old `KM_ORDERED_ALL` regime). The total order alone
    /// is refutationally complete but loses the direct `⊤ → B(x)` subsumption
    /// readout (the KM_ORDERED_ALL verdict above); the driver in reasoner.rs
    /// restores readout completeness with the complement-guard refutation
    /// residue readout (`Engine::ordered_residue_repair`). Thread-local like
    /// `BRANCH_ORDERED`: the gated driver is single-threaded, and tests can
    /// toggle it without cross-test env races.
    static ROOT_ORDERED: std::cell::Cell<u8> = const { std::cell::Cell::new(0) };
}

/// Set the `KM_ROOT_ORDERED` mode for the current thread (0 = off, 1 = root
/// contexts, 2 = all contexts). Called by the reasoner driver and tests.
pub fn set_root_ordered(mode: u8) {
    ROOT_ORDERED.with(|c| c.set(mode));
}

/// Current thread's `KM_ROOT_ORDERED` mode (see `ROOT_ORDERED`).
#[inline]
pub fn root_ordered_mode() -> u8 {
    ROOT_ORDERED.with(|c| c.get())
}

/// `true` while the Direction-B splitting driver is saturating a branch (the
/// tame ordered regime + unit-propagation resolvent suppression). Read by the
/// engine's Hyper builder as well as the ordering.
#[inline]
pub fn branch_ordered() -> bool {
    BRANCH_ORDERED.with(|c| c.get())
}

#[inline]
fn eqn_s(l: &Lit) -> Term {
    match *l {
        Lit::Eq { s, .. } | Lit::Ineq { s, .. } => s,
        _ => unreachable!(),
    }
}

fn pred_lteq(p1: &Pred, p2: &Pred, root: bool, sig: &Sig) -> bool {
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
    //
    // KM_ROOT_ONLY_INCOMP (EXPERIMENT, default off): scope the
    // incomparability to ROOT contexts (Sequoia's shape) and totally order
    // same-term concepts elsewhere (iri tie-break) — ordered resolution in
    // successor contexts.  The unit extraction roots need stays intact;
    // successors push per-disjunct CONDITIONAL clauses back (the residues
    // expose the next-max disjunct for the following resolution step), so the
    // disjunct-by-disjunct consumption chain replaces the all-disjunct
    // case split there.  Validation: probe + corpus A/B before any default.
    if let (Pred::Concept { iri: i1, t: t1 }, Pred::Concept { iri: i2, t: t2 }) = (p1, p2) {
        if t1 == t2 {
            // KM_ROOT_ORDERED (Direction A, docs/ROOT-ORDERED-RESOLUTION.md):
            // total order on same-term concepts in root contexts (mode 1) or
            // everywhere (mode 2) — internal definers above named, iri
            // tie-break within each block. The driver pairs this with the
            // complement-guard refutation readout, which restores the
            // subsumption completeness that a bare total order loses.
            let rom = root_ordered_mode();
            if rom == 2 || (rom == 1 && root) {
                let in1 = sig.is_internal(*i1);
                let in2 = sig.is_internal(*i2);
                return match (in1, in2) {
                    (true, true) | (false, false) => i1 <= i2,
                    (false, true) => true,  // named ≤ internal
                    (true, false) => false, // internal not ≤ named
                };
            }
            // KM_ORDERED_ALL: total order among same-term concepts in EVERY
            // context (root included) — ordered resolution everywhere.
            // Direction B branches use the same total order (per-thread,
            // BRANCH_ORDERED) to keep each branch's closure tame; the splitting
            // driver restores completeness.
            if ordered_all() || branch_ordered() {
                return i1 <= i2;
            }
            // KM_SEQ_ORDER: Sequoia-faithful — internal definers totally
            // ordered ABOVE named concepts; named concepts incomparable at the
            // bottom.  Keys on is_internal (named vs auxiliary), not on root.
            if seq_order() {
                let in1 = sig.is_internal(*i1);
                let in2 = sig.is_internal(*i2);
                return match (in1, in2) {
                    (true, true) => i1 <= i2,   // ordered resolution on definers
                    (false, false) => i1 == i2, // incomparable named (complete readout)
                    (false, true) => true,      // named ≤ internal (named at bottom)
                    (true, false) => false,     // internal not ≤ named
                };
            }
            if root || !root_only_incomp() {
                return i1 == i2;
            }
            return i1 <= i2;
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
        (
            Pred::Role {
                iri: i1,
                s: s1,
                t: t1,
            },
            Pred::Role {
                iri: i2,
                s: s2,
                t: t2,
            },
        ) => s1 < s2 || (s1 == s2 && (t1 < t2 || (t1 == t2 && i1 <= i2))),
        // Same-term concept pairs handled above; unreachable here.
        (Pred::Concept { iri: i1, .. }, Pred::Concept { iri: i2, .. }) => i1 <= i2,
        (Pred::Role { .. }, Pred::Concept { .. }) => false,
        (Pred::Concept { .. }, Pred::Role { .. }) => true,
    }
}

#[cfg(test)]
mod term_encoding_tests {
    use super::*;

    #[test]
    fn unsigned_layout_preserves_sequoia_order_and_ore_15846_capacity() {
        assert_eq!(std::mem::size_of::<Term>(), 4);
        assert!(zvar(2) < zvar(1));
        assert!(zvar(1) < Y && Y < X);

        let o = ind_term(129_647);
        let f = fterm(20_932);
        let fo = comp_term(f, o);
        assert!(X < o && o < f && f < fo);
        assert_eq!(ind_id(o), 129_647);
        assert_eq!(comp_parts(fo), (f, o));

        // The documented 17/15 composite split uses the final u32 value
        // exactly; arithmetic must neither wrap nor leave an accidental gap.
        assert_eq!(comp_term(fterm(32_735), ind_term(131_071)), Term::MAX);
    }

    #[test]
    fn adaptive_composite_layout_covers_both_ore_extremes() {
        assert_eq!(choose_comp_ind_bits(20_932, 129_647), Some(17));
        assert_eq!(choose_comp_ind_bits(130_303, 18_055), Some(15));
        assert_eq!(choose_comp_ind_bits(1 << 20, 1 << 20), None);
        assert_eq!(choose_comp_ind_bits_unknown_functions(129_647), Some(17));
        assert_eq!(choose_comp_ind_bits_unknown_functions(18_055), Some(15));
    }
}
