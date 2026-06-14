//! Structural transformation: SROIQ axioms -> DL-clauses.
//!
//! Direct port of `moose.sroiq.normalisation`: `nnf`, the `_Clausifier`
//! (`mark_polarity` / `fresh` / `_nominal_name` / `_resolve_role` / `q` /
//! `_define` / `subclass_clauses`), and the `normalise` driver.
//!
//! Fresh-name spellings (`Q_<n>`, `f_<q>`, ...) need not byte-match Python: the
//! validation gate is `dump_clauses.canon`, which renames every internal symbol
//! under a global bijection. What MUST match is the *structure* and the
//! *sharing*: structurally equal subconcepts share one `Q`, and a `∀R.D` gets
//! its introduction clauses iff it occurs at negative polarity. The reification
//! cache and `needs_forall_intro` set are keyed on structural concept equality,
//! exactly like Python's frozen dataclasses.

use std::collections::{HashMap, HashSet};

use super::clauses::{clause, constraint, fact, var_x, var_y, Atom, DLClause, Term};
use super::syntax::{mk_and, mk_or, Axiom, Concept, Ontology, Role};

/// Side-channel hooks (nominal -> individual, role inverses). We only need the
/// fields that affect the emitted clause set / nominal preprocessing.
#[derive(Default)]
pub struct GroundHooks {
    /// Map `__nom__a -> a`. Order-insensitive; consumed by nominal preprocessing.
    pub nominal_to_individual: HashMap<String, String>,
    /// `(R, __inv__R)` / `(R, S)` inverse pairs. Each registered pair also gets
    /// the bridging clauses `R(x,y) -> S(y,x)` and `S(x,y) -> R(y,x)` emitted
    /// (see `link_inverse`), which carry the inverse-role semantics to the
    /// engine; this Vec additionally records the pairs for diagnostics.
    pub role_inverses: Vec<(String, String)>,
    /// Roles declared `SymmetricObjectProperty(R)`. Each also gets the
    /// self-bridge clause `R(x,y) -> R(y,x)` emitted; this Vec records the role
    /// names so the frontend can recognise an inert symmetric role (one whose
    /// reverse edges feed no concept) and route the ontology to the EL fast
    /// path instead of the CB engine.
    pub symmetric_roles: Vec<String>,
}

// ---------------------------------------------------------------------------
// NNF (port of `nnf`)
// ---------------------------------------------------------------------------

pub fn nnf(c: &Concept) -> Concept {
    match c {
        Concept::Name(_) | Concept::Top | Concept::Bottom | Concept::Nominal(_) => c.clone(),
        Concept::Not(b) => nnf_not(b),
        Concept::And(cs) => mk_and(cs.iter().map(nnf)),
        Concept::Or(cs) => mk_or(cs.iter().map(nnf)),
        Concept::Exists(r, f) => Concept::Exists(r.clone(), Box::new(nnf(f))),
        Concept::Forall(r, f) => Concept::Forall(r.clone(), Box::new(nnf(f))),
        Concept::AtLeast(n, r, f) => Concept::AtLeast(*n, r.clone(), Box::new(nnf(f))),
        Concept::AtMost(n, r, f) => Concept::AtMost(*n, r.clone(), Box::new(nnf(f))),
        Concept::HasSelf(_) => c.clone(),
    }
}

fn nnf_not(b: &Concept) -> Concept {
    match b {
        Concept::Top => Concept::Bottom,
        Concept::Bottom => Concept::Top,
        Concept::Not(inner) => nnf(inner),
        Concept::Name(_) | Concept::Nominal(_) => Concept::Not(Box::new(b.clone())),
        Concept::And(cs) => mk_or(cs.iter().map(|x| nnf(&Concept::Not(Box::new(x.clone()))))),
        Concept::Or(cs) => mk_and(cs.iter().map(|x| nnf(&Concept::Not(Box::new(x.clone()))))),
        Concept::Exists(r, f) => Concept::Forall(
            r.clone(),
            Box::new(nnf(&Concept::Not(Box::new((**f).clone())))),
        ),
        Concept::Forall(r, f) => Concept::Exists(
            r.clone(),
            Box::new(nnf(&Concept::Not(Box::new((**f).clone())))),
        ),
        Concept::AtLeast(n, r, f) => {
            if *n <= 0 {
                Concept::Bottom
            } else {
                Concept::AtMost(n - 1, r.clone(), Box::new(nnf(f)))
            }
        }
        Concept::AtMost(n, r, f) => Concept::AtLeast(n + 1, r.clone(), Box::new(nnf(f))),
        Concept::HasSelf(_) => Concept::Not(Box::new(b.clone())),
    }
}

// ---------------------------------------------------------------------------
// Clausifier (port of `_Clausifier`)
// ---------------------------------------------------------------------------

pub struct Clausifier {
    counter: u64,
    prefix: String,
    reified: HashMap<Concept, String>,
    pub clauses: Vec<DLClause>,
    pub hooks: GroundHooks,
    universal_role_emitted: bool,
    pub needs_forall_intro: HashSet<Concept>,
    /// Polarities at which each `AtLeast` concept occurs (from the pre-pass).
    /// The n ≥ 2 recognition clause is expensive (multi-variable body, all-
    /// pairs equality head), so it is emitted only when the concept may occur
    /// negatively: seen negative, or not seen by the pre-pass at all (the
    /// conservative default — only a pre-pass-PROVEN positive-only occurrence
    /// skips it, so unseen occurrences keep the complete behaviour).
    pub atleast_pos: HashSet<Concept>,
    pub atleast_neg: HashSet<Concept>,
    /// Same for `AtMost`: the recognition direction (`≤n r.F ⊑ Q` via
    /// excluded middle + n+1 distinct witnesses) is emitted only when the
    /// concept may occur negatively.
    pub atmost_pos: HashSet<Concept>,
    pub atmost_neg: HashSet<Concept>,
    /// Polarity-gated definitional clausification (KM_ABSORB, default off).
    /// For a reified And/Or/Not concept, emit the definition direction `Q → C`
    /// only when C occurs positively and the recognition direction `C → Q` only
    /// when C occurs negatively (Plaisted-Greenbaum). This drops the unguarded
    /// `⊤ → Q ∨ A` excluded-middle clause for a negation that never appears on a
    /// subclass LHS (e.g. a disjointness `X ⊑ ¬A`) and turns a disjunction on the
    /// LHS into Horn rules — both shrink the live-disjunction blow-up at source.
    /// Verdict-preserving (equisatisfiable), validated by classification result
    /// vs gold, not byte-identical output.
    absorb: bool,
    def_pos: HashSet<Concept>,
    def_neg: HashSet<Concept>,
}

impl Clausifier {
    pub fn new() -> Self {
        Clausifier {
            counter: 0,
            prefix: "Q_".to_string(),
            reified: HashMap::new(),
            clauses: Vec::new(),
            hooks: GroundHooks::default(),
            universal_role_emitted: false,
            needs_forall_intro: HashSet::new(),
            atleast_pos: HashSet::new(),
            atleast_neg: HashSet::new(),
            atmost_pos: HashSet::new(),
            atmost_neg: HashSet::new(),
            absorb: std::env::var("KM_ABSORB").map(|s| s != "0").unwrap_or(false),
            def_pos: HashSet::new(),
            def_neg: HashSet::new(),
        }
    }

    /// Which definitional directions to emit for a reified And/Or/Not concept:
    /// `(want_def, want_rec)` = (emit `Q → C`, emit `C → Q`). With absorption off,
    /// both (the full `Q ≡ C`). With it on: keyed on the polarity the pre-pass
    /// recorded — positive ⇒ def direction, negative ⇒ recognition direction. A
    /// concept the pre-pass never saw (e.g. introduced by an ABox assertion) is
    /// emitted both ways, so unseen occurrences keep the complete behaviour.
    fn want_dirs(&self, c: &Concept) -> (bool, bool) {
        if !self.absorb {
            return (true, true);
        }
        let p = self.def_pos.contains(c);
        let n = self.def_neg.contains(c);
        if !p && !n {
            (true, true) // unseen: conservative
        } else {
            (p, n)
        }
    }

    /// Port of `mark_polarity`. `c` is assumed NNF.
    pub fn mark_polarity(&mut self, c: &Concept, neg: bool) {
        // Record the polarity of every reified And/Or/Not concept for absorption
        // (`neg == false` ⇒ positive occurrence, `true` ⇒ negative). Mirrors the
        // existing AtLeast/AtMost recording below.
        if matches!(c, Concept::And(_) | Concept::Or(_) | Concept::Not(_)) {
            if neg {
                self.def_neg.insert(c.clone());
            } else {
                self.def_pos.insert(c.clone());
            }
        }
        match c {
            Concept::Forall(_, f) => {
                if neg {
                    self.needs_forall_intro.insert(c.clone());
                }
                self.mark_polarity(f, neg);
            }
            Concept::Exists(_, f) => self.mark_polarity(f, neg),
            Concept::And(cs) => {
                for d in cs {
                    self.mark_polarity(d, neg);
                }
            }
            Concept::Or(cs) => {
                for d in cs {
                    self.mark_polarity(d, neg);
                }
            }
            Concept::Not(b) => self.mark_polarity(b, !neg),
            Concept::AtLeast(_, _, f) | Concept::AtMost(_, _, f) => {
                let (pos, neg_set) = if matches!(c, Concept::AtLeast(..)) {
                    (&mut self.atleast_pos, &mut self.atleast_neg)
                } else {
                    (&mut self.atmost_pos, &mut self.atmost_neg)
                };
                if neg {
                    neg_set.insert(c.clone());
                } else {
                    pos.insert(c.clone());
                }
                self.mark_polarity(f, true);
                self.mark_polarity(f, false);
            }
            _ => {}
        }
    }

    fn fresh(&mut self) -> String {
        let name = format!("{}{}", self.prefix, self.counter);
        self.counter += 1;
        name
    }

    fn nominal_name(individual: &str) -> String {
        format!("__nom__{}", individual)
    }

    /// Emit the clauses carrying `InverseObjectProperties(r, s)` semantics:
    /// `r(x,y) -> s(y,x)` and `s(x,y) -> r(y,x)`. Same swapped-orientation
    /// clause shape as symmetric roles, which the engine already propagates.
    /// Registered pairs are deduped via `hooks.role_inverses`. Without these
    /// clauses the inverse axiom was silently dropped (the hook Vec had no
    /// consumer), losing e.g. range-of-superproperty-of-inverse subsumptions
    /// (the SWEET `temporalPartOf ⊑ subsetOf, inv(subsetOf)=supersetOf ⊑
    /// setRelation, range(setRelation)=Set` chain on ore_ont_14896 et al).
    fn link_inverse(&mut self, r: &str, s: &str) {
        let pair = (r.to_string(), s.to_string());
        let rev = (s.to_string(), r.to_string());
        if self.hooks.role_inverses.contains(&pair) || self.hooks.role_inverses.contains(&rev) {
            return;
        }
        self.hooks.role_inverses.push(pair);
        let x = var_x();
        let y = var_y();
        self.clauses.push(clause(
            [Atom::Role(r.to_string(), x.clone(), y.clone())],
            [Atom::Role(s.to_string(), y.clone(), x.clone())],
        ));
        self.clauses.push(clause(
            [Atom::Role(s.to_string(), x.clone(), y.clone())],
            [Atom::Role(r.to_string(), y.clone(), x)],
        ));
    }

    /// Port of `_resolve_role`.
    fn resolve_role(&mut self, r: &Role) -> String {
        match r {
            Role::Name(n) => n.clone(),
            Role::Inverse(base) => {
                let inv_name = format!("__inv__{}", base);
                self.link_inverse(base, &inv_name);
                inv_name
            }
            Role::Universal => {
                if !self.universal_role_emitted {
                    self.clauses
                        .push(fact([Atom::Role("__U__".to_string(), var_x(), var_y())]));
                    self.universal_role_emitted = true;
                }
                "__U__".to_string()
            }
        }
    }

    /// Port of `q`: return a concept name for `c`, introducing a fresh `Q_i`
    /// (and its defining clauses) for non-atomic `c`.
    pub fn q(&mut self, c: &Concept) -> String {
        if let Concept::Name(n) = c {
            return n.clone();
        }
        if let Some(existing) = self.reified.get(c) {
            return existing.clone();
        }
        if let Concept::Nominal(ind) = c {
            let q = Self::nominal_name(ind);
            self.reified.insert(c.clone(), q.clone());
            self.hooks
                .nominal_to_individual
                .insert(q.clone(), ind.clone());
            return q;
        }
        let q = self.fresh();
        self.reified.insert(c.clone(), q.clone());
        self.define(&q, c);
        q
    }

    /// Port of `_define`: emit the clauses asserting `q ≡ c`.
    fn define(&mut self, q: &str, c: &Concept) {
        let x = var_x();
        let y = var_y();
        let qx = Atom::Concept(q.to_string(), x.clone());
        // Absorption gating (And/Or/Not only): `want_def` = emit `Q → C`,
        // `want_rec` = emit `C → Q`. Both true unless absorption proved one
        // direction unneeded by polarity. (No effect on the other concept kinds.)
        let (want_def, want_rec) = self.want_dirs(c);

        match c {
            Concept::Top => {
                self.clauses.push(fact([qx]));
            }
            Concept::Bottom => {
                self.clauses.push(clause([qx], []));
            }
            Concept::Not(inner) => {
                if let Concept::HasSelf(role) = inner.as_ref() {
                    let role_name = self.resolve_role(role);
                    let proxy = self.fresh();
                    // proxy ↔ R(x,x)
                    self.clauses.push(clause(
                        [Atom::Concept(proxy.clone(), x.clone())],
                        [Atom::Role(role_name.clone(), x.clone(), x.clone())],
                    ));
                    self.clauses.push(clause(
                        [Atom::Role(role_name, x.clone(), x.clone())],
                        [Atom::Concept(proxy.clone(), x.clone())],
                    ));
                    let ax = Atom::Concept(proxy, x.clone());
                    if want_def {
                        self.clauses.push(clause([qx.clone(), ax.clone()], []));
                    }
                    if want_rec {
                        self.clauses.push(clause([], [qx, ax]));
                    }
                    return;
                }
                let ax = match inner.as_ref() {
                    Concept::Nominal(ind) => {
                        let nom_name = Self::nominal_name(ind);
                        self.hooks
                            .nominal_to_individual
                            .insert(nom_name.clone(), ind.clone());
                        Atom::Concept(nom_name, x.clone())
                    }
                    Concept::Name(n) => Atom::Concept(n.clone(), x.clone()),
                    _ => panic!("nested negation should have been removed by nnf()"),
                };
                // `Q ∧ A → ⊥` (def: Q ⊑ ¬A) and `⊤ → Q ∨ A` (rec: ¬A ⊑ Q). The
                // recognition clause is the unguarded excluded-middle disjunction
                // dropped when ¬A never occurs on a subclass LHS.
                if want_def {
                    self.clauses.push(clause([qx.clone(), ax.clone()], []));
                }
                if want_rec {
                    self.clauses.push(clause([], [qx, ax]));
                }
            }
            Concept::And(conjuncts) => {
                let atoms: Vec<Atom> = conjuncts
                    .iter()
                    .map(|d| {
                        let qn = self.q(d);
                        Atom::Concept(qn, x.clone())
                    })
                    .collect();
                // def: Q ⊑ Cᵢ (one per conjunct); rec: ⨅Cᵢ ⊑ Q. Both Horn.
                if want_def {
                    for a in &atoms {
                        self.clauses.push(clause([qx.clone()], [a.clone()]));
                    }
                }
                if want_rec {
                    self.clauses.push(clause(atoms, [qx]));
                }
            }
            Concept::Or(disjuncts) => {
                let atoms: Vec<Atom> = disjuncts
                    .iter()
                    .map(|d| {
                        let qn = self.q(d);
                        Atom::Concept(qn, x.clone())
                    })
                    .collect();
                // def: Q ⊑ ⨆Cᵢ (the disjunctive head — dropped when the Or never
                // occurs positively); rec: each Cᵢ ⊑ Q (Horn).
                if want_def {
                    self.clauses.push(clause([qx.clone()], atoms.clone()));
                }
                if want_rec {
                    for a in atoms {
                        self.clauses.push(clause([a], [qx.clone()]));
                    }
                }
            }
            Concept::Exists(role, filler) => {
                let role_name = self.resolve_role(role);
                let filler_name = self.q(filler);
                let f = format!("f_{}", q);
                let fx = Term::Fun(f, Box::new(x.clone()));
                self.clauses.push(clause(
                    [qx.clone()],
                    [Atom::Role(role_name.clone(), x.clone(), fx.clone())],
                ));
                self.clauses.push(clause(
                    [qx.clone()],
                    [Atom::Concept(filler_name.clone(), fx)],
                ));
                self.clauses.push(clause(
                    [
                        Atom::Role(role_name, x.clone(), y.clone()),
                        Atom::Concept(filler_name, y.clone()),
                    ],
                    [qx],
                ));
            }
            Concept::Forall(role, filler) => {
                let role_name = self.resolve_role(role);
                let filler_name = self.q(filler);
                // Propagation: Q(x) ∧ R(x,y) → D(y)
                self.clauses.push(clause(
                    [qx.clone(), Atom::Role(role_name.clone(), x.clone(), y.clone())],
                    [Atom::Concept(filler_name.clone(), y.clone())],
                ));
                // Introduction, only when this ∀R.D occurs negatively somewhere.
                if self.needs_forall_intro.contains(c) {
                    let nq = self.fresh();
                    let nd = self.fresh();
                    let nqx = Atom::Concept(nq.clone(), x.clone());
                    let fx = Term::Fun(format!("f_{}", nq), Box::new(x.clone()));
                    self.clauses.push(clause([], [qx.clone(), nqx.clone()]));
                    self.clauses.push(clause([qx, nqx.clone()], []));
                    self.clauses.push(clause(
                        [nqx.clone()],
                        [Atom::Role(role_name, x.clone(), fx.clone())],
                    ));
                    self.clauses
                        .push(clause([nqx], [Atom::Concept(nd.clone(), fx)]));
                    self.clauses.push(clause(
                        [
                            Atom::Concept(nd, x.clone()),
                            Atom::Concept(filler_name, x.clone()),
                        ],
                        [],
                    ));
                }
            }
            Concept::HasSelf(role) => {
                let role_name = self.resolve_role(role);
                self.clauses.push(clause(
                    [qx.clone()],
                    [Atom::Role(role_name.clone(), x.clone(), x.clone())],
                ));
                self.clauses
                    .push(clause([Atom::Role(role_name, x.clone(), x.clone())], [qx]));
            }
            Concept::Nominal(ind) => {
                self.hooks
                    .nominal_to_individual
                    .insert(q.to_string(), ind.clone());
            }
            Concept::AtLeast(n, role, filler) => {
                let role_name = self.resolve_role(role);
                let filler_name = self.q(filler);
                for i in 0..*n {
                    let f_name = format!("f_{}_{}", q, i);
                    let fxi = Term::Fun(f_name, Box::new(x.clone()));
                    self.clauses.push(clause(
                        [qx.clone()],
                        [Atom::Role(role_name.clone(), x.clone(), fxi.clone())],
                    ));
                    self.clauses.push(clause(
                        [qx.clone()],
                        [Atom::Concept(filler_name.clone(), fxi)],
                    ));
                }
                for i in 0..*n {
                    for j in (i + 1)..*n {
                        let fxi = Term::Fun(format!("f_{}_{}", q, i), Box::new(x.clone()));
                        let fxj = Term::Fun(format!("f_{}_{}", q, j), Box::new(x.clone()));
                        self.clauses
                            .push(clause([qx.clone(), Atom::Eq(fxi, fxj)], []));
                    }
                }
                if *n == 1 {
                    self.clauses.push(clause(
                        [
                            Atom::Role(role_name, x.clone(), y.clone()),
                            Atom::Concept(filler_name, y.clone()),
                        ],
                        [qx],
                    ));
                } else if *n == 0 || !self.atleast_pos.contains(c) || self.atleast_neg.contains(c) {
                    // Recognition for n != 1: the contrapositive ¬Q ⊑ ≤(n-1) r.F,
                    // i.e. n r-successors in F are either not all distinct or Q
                    // holds. Same clause shape as AtMost below. (n == 0 yields an
                    // empty body, making Q a fact: ≥0 r.F ≡ ⊤ — always emitted.)
                    // Skipped only when the polarity pre-pass PROVED the concept
                    // occurs positively only (then Q is never needed in a body
                    // and the clause is pure cost — the ore_ont_15672 blow-up).
                    let ys: Vec<Term> = (0..*n).map(|i| Term::Var(format!("y{}", i))).collect();
                    let mut body_atoms: Vec<Atom> = Vec::new();
                    for yi in &ys {
                        body_atoms.push(Atom::Role(role_name.clone(), x.clone(), yi.clone()));
                        body_atoms.push(Atom::Concept(filler_name.clone(), yi.clone()));
                    }
                    let mut head_atoms: Vec<Atom> = vec![qx];
                    for i in 0..ys.len() {
                        for j in (i + 1)..ys.len() {
                            head_atoms.push(Atom::Eq(ys[i].clone(), ys[j].clone()));
                        }
                    }
                    self.clauses.push(clause(body_atoms, head_atoms));
                }
            }
            Concept::AtMost(n, role, filler) => {
                let role_name = self.resolve_role(role);
                let filler_name = self.q(filler);
                let ys: Vec<Term> = (0..=*n).map(|i| Term::Var(format!("y{}", i))).collect();
                let mut body_atoms: Vec<Atom> = vec![qx.clone()];
                for yi in &ys {
                    body_atoms.push(Atom::Role(role_name.clone(), x.clone(), yi.clone()));
                    body_atoms.push(Atom::Concept(filler_name.clone(), yi.clone()));
                }
                let mut head_atoms: Vec<Atom> = Vec::new();
                for i in 0..ys.len() {
                    for j in (i + 1)..ys.len() {
                        head_atoms.push(Atom::Eq(ys[i].clone(), ys[j].clone()));
                    }
                }
                self.clauses.push(clause(body_atoms, head_atoms));
                // Recognition: `≤n r.F ⊑ Q` via excluded middle — NQ stands for
                // ¬Q ≡ ≥(n+1) r.F (n+1 pairwise-distinct witnesses), so a
                // context whose constraints refute the witnesses derives Q.
                // Emitted only when the AtMost may occur negatively (a LHS /
                // body position); the ⊤ → Q ∨ NQ split fires in every context,
                // so a pre-pass-proven positive-only occurrence skips it.
                if !self.atmost_pos.contains(c) || self.atmost_neg.contains(c) {
                    let nq = self.fresh();
                    let nqx = Atom::Concept(nq.clone(), x.clone());
                    self.clauses.push(clause([], [qx.clone(), nqx.clone()]));
                    self.clauses.push(clause([qx, nqx.clone()], []));
                    let g = |i: i64| Term::Fun(format!("f_{}_{}", nq, i), Box::new(x.clone()));
                    for i in 0..=*n {
                        self.clauses.push(clause(
                            [nqx.clone()],
                            [Atom::Role(role_name.clone(), x.clone(), g(i))],
                        ));
                        self.clauses.push(clause(
                            [nqx.clone()],
                            [Atom::Concept(filler_name.clone(), g(i))],
                        ));
                    }
                    for i in 0..=*n {
                        for j in (i + 1)..=*n {
                            self.clauses
                                .push(clause([nqx.clone(), Atom::Eq(g(i), g(j))], []));
                        }
                    }
                }
            }
            Concept::Name(_) => unreachable!("q() short-circuits ConceptName"),
        }
    }

    /// Port of `subclass_clauses`: emit `sub ⊑ sup` (after NNF).
    pub fn subclass_clauses(&mut self, sub: &Concept, sup: &Concept) {
        let q_sub = self.q(sub);
        let q_sup = self.q(sup);
        let x = var_x();
        self.clauses.push(clause(
            [Atom::Concept(q_sub, x.clone())],
            [Atom::Concept(q_sup, x)],
        ));
    }
}

impl Default for Clausifier {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `≥n r.F` (n ≥ 2) must get a recognition clause
    /// `r(x,y0) ∧ F(y0) ∧ ... ∧ r(x,y_{n-1}) ∧ F(y_{n-1}) → Q ∨ ⋁ yi≈yj`,
    /// otherwise a min-cardinality on the LHS of a subsumption can never fire
    /// (the ore_ont_16461 incompleteness).
    #[test]
    fn atleast_two_recognition_clause() {
        let mut cf = Clausifier::new();
        let c = Concept::AtLeast(
            2,
            Role::Name("r".to_string()),
            Box::new(Concept::Name("J".to_string())),
        );
        let q = cf.q(&c);
        let qx = Atom::Concept(q, var_x());
        let found = cf.clauses.iter().any(|cl| {
            cl.body.len() == 4
                && cl.head.len() == 2
                && cl.head.contains(&qx)
                && cl.head.iter().any(|a| matches!(a, Atom::Eq(_, _)))
                && cl.body.iter().filter(|a| matches!(a, Atom::Role(..))).count() == 2
                && cl.body.iter().filter(|a| matches!(a, Atom::Concept(..))).count() == 2
        });
        assert!(found, "missing ≥2 recognition clause; got {:#?}", cf.clauses);
    }

    /// Polarity gating: a pre-pass-proven positive-only `≥n` skips the
    /// recognition clause; a negative (or unseen) occurrence emits it.
    #[test]
    fn atleast_recognition_polarity_gated() {
        let mk = || {
            Concept::AtLeast(
                2,
                Role::Name("r".to_string()),
                Box::new(Concept::Name("J".to_string())),
            )
        };
        let has_recognition = |cf: &Clausifier| {
            cf.clauses
                .iter()
                .any(|cl| cl.body.len() == 4 && cl.head.iter().any(|a| matches!(a, Atom::Eq(_, _))))
        };
        // positive-only: skipped
        let mut cf = Clausifier::new();
        cf.mark_polarity(&mk(), false);
        cf.q(&mk());
        assert!(!has_recognition(&cf), "positive-only ≥2 must not emit recognition");
        // both polarities: emitted
        let mut cf = Clausifier::new();
        cf.mark_polarity(&mk(), false);
        cf.mark_polarity(&mk(), true);
        cf.q(&mk());
        assert!(has_recognition(&cf), "negative ≥2 must emit recognition");
    }

    /// AtMost recognition (`≤n r.F ⊑ Q` via excluded middle + n+1 distinct
    /// witnesses) is emitted for negative/unseen occurrences and skipped for
    /// proven positive-only ones.
    #[test]
    fn atmost_recognition_polarity_gated() {
        let mk = || {
            Concept::AtMost(
                1,
                Role::Name("r".to_string()),
                Box::new(Concept::Name("J".to_string())),
            )
        };
        // The excluded-middle clause `⊤ → Q ∨ NQ` marks the recognition.
        let has_recognition = |cf: &Clausifier| {
            cf.clauses
                .iter()
                .any(|cl| cl.body.is_empty() && cl.head.len() == 2
                    && cl.head.iter().all(|a| matches!(a, Atom::Concept(..))))
        };
        // positive-only: skipped
        let mut cf = Clausifier::new();
        cf.mark_polarity(&mk(), false);
        cf.q(&mk());
        assert!(!has_recognition(&cf), "positive-only ≤1 must not emit recognition");
        // negative: emitted (excluded middle + 2 witnesses + 1 distinctness)
        let mut cf = Clausifier::new();
        cf.mark_polarity(&mk(), true);
        cf.q(&mk());
        assert!(has_recognition(&cf), "negative ≤1 must emit recognition");
        // unseen (no pre-pass): emitted — the conservative default
        let mut cf = Clausifier::new();
        cf.q(&mk());
        assert!(has_recognition(&cf), "unseen ≤1 must emit recognition");
    }

    /// Absorption: a negation that occurs only positively (e.g. `X ⊑ ¬A`) keeps
    /// the constraint `Q ∧ A → ⊥` but drops the unguarded excluded-middle
    /// `⊤ → Q ∨ A`. Without absorption both are emitted; a negative occurrence
    /// re-enables the recognition clause.
    #[test]
    fn absorb_drops_positive_only_excluded_middle() {
        let not_a = || Concept::Not(Box::new(Concept::Name("A".to_string())));
        let excluded_middle = |cf: &Clausifier| {
            cf.clauses.iter().any(|cl| {
                cl.body.is_empty()
                    && cl.head.len() == 2
                    && cl.head.iter().all(|a| matches!(a, Atom::Concept(..)))
            })
        };
        let constraint_clause = |cf: &Clausifier| {
            cf.clauses
                .iter()
                .any(|cl| cl.head.is_empty() && cl.body.len() == 2)
        };
        // absorption OFF: positive-only negation still emits both.
        let mut cf = Clausifier::new();
        cf.mark_polarity(&not_a(), false);
        cf.q(&not_a());
        assert!(excluded_middle(&cf) && constraint_clause(&cf));
        // absorption ON, positive-only: constraint kept, excluded middle dropped.
        let mut cf = Clausifier::new();
        cf.absorb = true;
        cf.mark_polarity(&not_a(), false);
        cf.q(&not_a());
        assert!(constraint_clause(&cf), "def direction Q∧A→⊥ must remain");
        assert!(!excluded_middle(&cf), "positive-only ¬A must drop ⊤→Q∨A");
        // absorption ON, also negative: excluded middle re-enabled.
        let mut cf = Clausifier::new();
        cf.absorb = true;
        cf.mark_polarity(&not_a(), false);
        cf.mark_polarity(&not_a(), true);
        cf.q(&not_a());
        assert!(excluded_middle(&cf), "negative ¬A must re-emit ⊤→Q∨A");
    }
}

// ---------------------------------------------------------------------------
// Driver (port of `normalise`)
// ---------------------------------------------------------------------------

/// Returns `(tbox_clauses, abox_clauses, hooks)`.
pub fn normalise(ontology: &Ontology) -> (Vec<DLClause>, Vec<DLClause>, GroundHooks) {
    let mut clausifier = Clausifier::new();
    let x = var_x();
    let y = var_y();

    // Polarity pre-pass.
    for ax in ontology.tbox() {
        match ax {
            Axiom::SubClassOf(sub, sup) => {
                let s = nnf(sub);
                let p = nnf(sup);
                clausifier.mark_polarity(&s, true);
                clausifier.mark_polarity(&p, false);
            }
            Axiom::EquivalentClasses(l, r) => {
                for side in [nnf(l), nnf(r)] {
                    clausifier.mark_polarity(&side, true);
                    clausifier.mark_polarity(&side, false);
                }
            }
            Axiom::DisjointClasses(l, r) => {
                let conj = mk_and([nnf(l), nnf(r)]);
                clausifier.mark_polarity(&conj, true);
            }
            _ => {}
        }
    }

    // TBox.
    for ax in ontology.tbox() {
        match ax {
            Axiom::SubClassOf(sub, sup) => {
                let s = nnf(sub);
                let p = nnf(sup);
                clausifier.subclass_clauses(&s, &p);
            }
            Axiom::EquivalentClasses(l, r) => {
                let nl = nnf(l);
                let nr = nnf(r);
                clausifier.subclass_clauses(&nl, &nr);
                clausifier.subclass_clauses(&nr, &nl);
            }
            Axiom::DisjointClasses(l, r) => {
                let conj = mk_and([nnf(l), nnf(r)]);
                clausifier.subclass_clauses(&conj, &Concept::Bottom);
            }
            _ => {}
        }
    }

    // RBox.
    for ax in ontology.rbox() {
        match ax {
            Axiom::RoleInclusion(sub, sup) => {
                clausifier.clauses.push(clause(
                    [Atom::Role(sub.clone(), x.clone(), y.clone())],
                    [Atom::Role(sup.clone(), x.clone(), y.clone())],
                ));
            }
            Axiom::RoleChain(chain, sup) => {
                let k = chain.len();
                let xs: Vec<Term> = (0..=k).map(|i| Term::Var(format!("x{}", i))).collect();
                let body_atoms: Vec<Atom> = (0..k)
                    .map(|i| Atom::Role(chain[i].clone(), xs[i].clone(), xs[i + 1].clone()))
                    .collect();
                let head_atom = Atom::Role(sup.clone(), xs[0].clone(), xs[k].clone());
                clausifier.clauses.push(clause(body_atoms, [head_atom]));
            }
            Axiom::TransitiveRole(role) => {
                let z = Term::Var("z".to_string());
                clausifier.clauses.push(clause(
                    [
                        Atom::Role(role.clone(), x.clone(), y.clone()),
                        Atom::Role(role.clone(), y.clone(), z.clone()),
                    ],
                    [Atom::Role(role.clone(), x.clone(), z)],
                ));
            }
            Axiom::SymmetricRole(role) => {
                clausifier.hooks.symmetric_roles.push(role.clone());
                clausifier.clauses.push(clause(
                    [Atom::Role(role.clone(), x.clone(), y.clone())],
                    [Atom::Role(role.clone(), y.clone(), x.clone())],
                ));
            }
            Axiom::AsymmetricRole(role) => {
                clausifier.clauses.push(constraint([
                    Atom::Role(role.clone(), x.clone(), y.clone()),
                    Atom::Role(role.clone(), y.clone(), x.clone()),
                ]));
            }
            Axiom::IrreflexiveRole(role) => {
                clausifier
                    .clauses
                    .push(constraint([Atom::Role(role.clone(), x.clone(), x.clone())]));
            }
            Axiom::ReflexiveRole(role) => {
                clausifier
                    .clauses
                    .push(fact([Atom::Role(role.clone(), x.clone(), x.clone())]));
            }
            Axiom::FunctionalRole(role) => {
                let y0 = Term::Var("y0".to_string());
                let y1 = Term::Var("y1".to_string());
                clausifier.clauses.push(clause(
                    [
                        Atom::Role(role.clone(), x.clone(), y0.clone()),
                        Atom::Role(role.clone(), x.clone(), y1.clone()),
                    ],
                    [Atom::Eq(y0, y1)],
                ));
            }
            Axiom::InverseFunctionalRole(role) => {
                let y0 = Term::Var("y0".to_string());
                let y1 = Term::Var("y1".to_string());
                clausifier.clauses.push(clause(
                    [
                        Atom::Role(role.clone(), y0.clone(), x.clone()),
                        Atom::Role(role.clone(), y1.clone(), x.clone()),
                    ],
                    [Atom::Eq(y0, y1)],
                ));
            }
            Axiom::InverseRoles(role, inverse) => {
                clausifier.link_inverse(role, inverse);
            }
            Axiom::DisjointRoles(l, r) => {
                clausifier.clauses.push(constraint([
                    Atom::Role(l.clone(), x.clone(), y.clone()),
                    Atom::Role(r.clone(), x.clone(), y.clone()),
                ]));
            }
            _ => {}
        }
    }

    // ABox.
    let mut abox_clauses: Vec<DLClause> = Vec::new();
    for ax in ontology.abox() {
        match ax {
            Axiom::ConceptAssertion(concept, individual) => {
                let ind = Term::Ind(individual.clone());
                let nc = nnf(concept);
                let q = clausifier.q(&nc);
                abox_clauses.push(fact([Atom::Concept(q, ind)]));
            }
            Axiom::RoleAssertion(role, source, target) => {
                abox_clauses.push(fact([Atom::Role(
                    role.clone(),
                    Term::Ind(source.clone()),
                    Term::Ind(target.clone()),
                )]));
            }
            Axiom::SameIndividual(l, r) => {
                abox_clauses.push(fact([Atom::Eq(
                    Term::Ind(l.clone()),
                    Term::Ind(r.clone()),
                )]));
            }
            Axiom::DifferentIndividuals(l, r) => {
                abox_clauses.push(constraint([Atom::Eq(
                    Term::Ind(l.clone()),
                    Term::Ind(r.clone()),
                )]));
            }
            _ => {}
        }
    }

    (clausifier.clauses, abox_clauses, clausifier.hooks)
}
