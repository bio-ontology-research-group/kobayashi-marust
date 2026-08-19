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
use crate::json_io::DefinerKind;

/// Side-channel hooks (nominal -> individual, role inverses). We only need the
/// fields that affect the emitted clause set / nominal preprocessing.
#[derive(Default)]
pub struct GroundHooks {
    /// Map `__nom__a -> a`. Order-insensitive; consumed by nominal preprocessing.
    pub nominal_to_individual: HashMap<String, String>,
    /// Exact proxy mapping for named individuals seen only in source ABox
    /// axioms.  Kept separate from `nominal_to_individual`: ordinary nominal
    /// preprocessing must remain byte-identical, while the typed native-ABox
    /// channel still needs an authoritative collision-safe proxy name.
    pub abox_nominal_to_individual: HashMap<String, String>,
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
    /// KM_HT_CARD: first-class qualified number restrictions captured during
    /// clausification (`define`). Empty unless the frontend `KM_HT_CARD` flag is
    /// set, so the default clause/meta output is byte-identical. Consumed by
    /// cb_to_ht to install the Konclude `≥n`/`≤n` rules in place of the clausal
    /// `⋁ Eq` pigeonhole.
    pub cardinalities: Vec<crate::json_io::CardMeta>,
    /// Fresh-concept provenance for triggered GCI absorption. Empty unless
    /// `KM_TRIGGER_ABSORB` is enabled, preserving the default JSON contract.
    pub definers: Vec<crate::json_io::DefinerMeta>,
    /// Normalized source TBox consumed by Konclude-style pre-clausal
    /// absorption. Empty unless `KM_TRIGGER_ABSORB` is enabled.
    pub source_axioms: Vec<crate::json_io::SourceAxiomMeta>,
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
    /// KM_HT_CARD: when set, `define` records each `≥n`/`≤n` restriction (and the
    /// `≥(n+1)` recognition proxy) into `hooks.cardinalities` as a first-class
    /// `CardMeta`. The clausal expansion is still emitted unchanged (the CB engine
    /// consumes it); the metadata only lets the HT path swap it for the Konclude
    /// number rules. Default ON (opt out: KM_NO_HT_CARD). The clause set is
    /// byte-identical either way — this only populates the additive `cardinalities`
    /// side-data field, consumed solely by the card-routed HT path.
    card: bool,
    /// Compile structurally triggerable subclass antecedents directly into
    /// guarded DL-clause bodies and retain fresh-concept provenance.
    trigger_absorb: bool,
}

impl Clausifier {
    const MAX_TRIGGER_ALTERNATIVES: usize = 64;

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
            absorb: std::env::var("KM_ABSORB")
                .map(|s| s != "0")
                .unwrap_or(false),
            def_pos: HashSet::new(),
            def_neg: HashSet::new(),
            card: std::env::var_os("KM_NO_HT_CARD").is_none(),
            trigger_absorb: std::env::var_os("KM_TRIGGER_ABSORB").is_some(),
        }
    }

    fn record_definer(
        &mut self,
        marker: &str,
        kind: DefinerKind,
        operands: Vec<String>,
        role: Option<String>,
        n: Option<i64>,
    ) {
        if self.trigger_absorb {
            self.hooks.definers.push(crate::json_io::DefinerMeta {
                marker: marker.to_string(),
                kind,
                operands,
                role,
                n,
            });
        }
    }

    /// Whether `c(x)` has an exact finite positive trigger expansion. Negative
    /// atoms, universals, and general cardinalities need signed/status-aware
    /// machinery and deliberately fall back to the existing reification.
    fn structurally_triggerable(c: &Concept) -> bool {
        Self::trigger_alternative_count(c).is_some()
    }

    fn trigger_alternative_count(c: &Concept) -> Option<usize> {
        match c {
            Concept::Name(_) | Concept::Top | Concept::Nominal(_) | Concept::HasSelf(_) => Some(1),
            Concept::Bottom => Some(0),
            Concept::And(cs) => {
                let mut count = 1usize;
                for d in cs {
                    count = count.checked_mul(Self::trigger_alternative_count(d)?)?;
                    if count > Self::MAX_TRIGGER_ALTERNATIVES {
                        return None;
                    }
                }
                Some(count)
            }
            Concept::Or(cs) => {
                let mut count = 0usize;
                for d in cs {
                    count = count.checked_add(Self::trigger_alternative_count(d)?)?;
                    if count > Self::MAX_TRIGGER_ALTERNATIVES {
                        return None;
                    }
                }
                Some(count)
            }
            Concept::Exists(_, f) | Concept::AtLeast(1, _, f) => Self::trigger_alternative_count(f),
            Concept::AtLeast(0, _, _) => Some(1),
            Concept::Not(_) | Concept::Forall(..) | Concept::AtLeast(..) | Concept::AtMost(..) => {
                None
            }
        }
    }

    /// Return a DNF of positive, context-local trigger bodies equivalent to
    /// `c(root)`. Each alternative becomes one implication with the same head.
    ///
    /// Existential restrictions are deliberately represented by their local
    /// restriction marker, rather than by inlining `R(root, yi) ∧ C(yi)`. This
    /// is the propagated-trigger construction used by Konclude's
    /// `CTriggeredImplicationBinaryAbsorberPreProcess`: the restriction is
    /// recognised in one successor context, propagated to a concept at the
    /// predecessor, and only those predecessor-local concepts are joined.
    /// Inlining two existentials would create a body over two independent
    /// successor variables. Such a clause is first-order equivalent, but is
    /// outside the local DL-clause shape supported by KM's context calculus and
    /// caused the deterministic seven-pair loss on ORE ontology 703 whenever
    /// the trigger-absorbed CB worker won the bridge race.
    ///
    /// Expansion is capped to avoid distributing pathological nested unions in
    /// the frontend; exceeding the cap falls back to ordinary reification.
    fn structural_trigger_bodies(
        &mut self,
        c: &Concept,
        root: &Term,
        next_var: &mut usize,
    ) -> Option<Vec<Vec<Atom>>> {
        match c {
            Concept::Name(n) => Some(vec![vec![Atom::Concept(n.clone(), root.clone())]]),
            Concept::Top => Some(vec![Vec::new()]),
            Concept::Bottom => Some(Vec::new()),
            Concept::Nominal(ind) => {
                let n = Self::nominal_name(ind);
                self.hooks
                    .nominal_to_individual
                    .insert(n.clone(), ind.clone());
                Some(vec![vec![Atom::Concept(n, root.clone())]])
            }
            Concept::And(cs) => {
                let mut out = vec![Vec::new()];
                for d in cs {
                    let alternatives = self.structural_trigger_bodies(d, root, next_var)?;
                    let mut product = Vec::new();
                    for left in &out {
                        for right in &alternatives {
                            let mut body = left.clone();
                            body.extend(right.iter().cloned());
                            product.push(body);
                            if product.len() > Self::MAX_TRIGGER_ALTERNATIVES {
                                return None;
                            }
                        }
                    }
                    out = product;
                }
                Some(out)
            }
            Concept::Or(cs) => {
                let mut out = Vec::new();
                for d in cs {
                    out.extend(self.structural_trigger_bodies(d, root, next_var)?);
                    if out.len() > Self::MAX_TRIGGER_ALTERNATIVES {
                        return None;
                    }
                }
                Some(out)
            }
            Concept::Exists(..) | Concept::AtLeast(1, ..) => {
                // `q(c)` emits the standard local recognition rule
                //     R(x,y) ∧ F(y) -> Q_c(x)
                // (and the matching generation direction required when the
                // same restriction occurs positively elsewhere). Reusing that
                // exact restriction marker gives the same propagated-trigger
                // boundary as Konclude while retaining structural sharing.
                let marker = self.q(c);
                Some(vec![vec![Atom::Concept(marker, root.clone())]])
            }
            Concept::AtLeast(0, _, _) => Some(vec![Vec::new()]),
            Concept::HasSelf(role) => {
                let role_name = self.resolve_role(role);
                Some(vec![vec![Atom::Role(
                    role_name,
                    root.clone(),
                    root.clone(),
                )]])
            }
            Concept::Not(_) | Concept::Forall(..) | Concept::AtLeast(..) | Concept::AtMost(..) => {
                None
            }
        }
    }

    /// Choose an equivalent GCI orientation with a positive, structurally
    /// triggerable antecedent. Negative top-level RHS disjuncts are absorbed
    /// into the body first: `A -> not B or C` becomes `A and B -> C`.
    fn triggered_orientation(sub: &Concept, sup: &Concept) -> Option<(Concept, Concept)> {
        let mut guards = vec![sub.clone()];
        let mut residue = Vec::new();
        let disjuncts: Vec<Concept> = match sup {
            Concept::Or(cs) => cs.iter().cloned().collect(),
            other => vec![other.clone()],
        };
        for d in disjuncts {
            if let Concept::Not(inner) = &d {
                if Self::structurally_triggerable(inner) {
                    guards.push((**inner).clone());
                    continue;
                }
            }
            residue.push(d);
        }
        let direct_sub = mk_and(guards);
        if Self::structurally_triggerable(&direct_sub) {
            return Some((direct_sub, mk_or(residue)));
        }

        // If the original orientation has no positive trigger, try its exact
        // contrapositive `not sup -> not sub`.
        let contra_sub = nnf(&Concept::Not(Box::new(sup.clone())));
        if Self::structurally_triggerable(&contra_sub) {
            let contra_sup = nnf(&Concept::Not(Box::new(sub.clone())));
            return Some((contra_sub, contra_sup));
        }
        None
    }

    fn emit_structural_subclass(&mut self, sub: &Concept, sup: &Concept) -> bool {
        let mut next_var = 0;
        let Some(bodies) = self.structural_trigger_bodies(sub, &var_x(), &mut next_var) else {
            return false;
        };
        if matches!(sup, Concept::Top) {
            return true;
        }
        if matches!(sup, Concept::Bottom) {
            for body in bodies {
                self.clauses.push(clause(body, []));
            }
            return true;
        }
        let q_sup = self.q(sup);
        for body in bodies {
            self.clauses
                .push(clause(body, [Atom::Concept(q_sup.clone(), var_x())]));
        }
        true
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

    /// Record the normalizer's nominal spelling for an ABox endpoint without
    /// adding it to ordinary nominal preprocessing.  The input `individual`
    /// is an `IriRegistry`-owned collision-safe internal name; source symbols
    /// with generated-looking prefixes have already been escaped.
    fn register_abox_individual(&mut self, individual: &str) -> String {
        let proxy = Self::nominal_name(individual);
        self.hooks
            .abox_nominal_to_individual
            .insert(proxy.clone(), individual.to_string());
        proxy
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
                self.record_definer(q, DefinerKind::Top, Vec::new(), None, None);
                self.clauses.push(fact([qx]));
            }
            Concept::Bottom => {
                self.record_definer(q, DefinerKind::Bottom, Vec::new(), None, None);
                self.clauses.push(clause([qx], []));
            }
            Concept::Not(inner) => {
                if let Concept::HasSelf(role) = inner.as_ref() {
                    let role_name = self.resolve_role(role);
                    self.record_definer(
                        q,
                        DefinerKind::NotSelf,
                        Vec::new(),
                        Some(role_name.clone()),
                        None,
                    );
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
                let operand = match &ax {
                    Atom::Concept(name, _) => name.clone(),
                    _ => unreachable!(),
                };
                self.record_definer(q, DefinerKind::Not, vec![operand], None, None);
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
                let names: Vec<String> = conjuncts.iter().map(|d| self.q(d)).collect();
                self.record_definer(q, DefinerKind::And, names.clone(), None, None);
                let atoms: Vec<Atom> = names
                    .into_iter()
                    .map(|name| Atom::Concept(name, x.clone()))
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
                let names: Vec<String> = disjuncts.iter().map(|d| self.q(d)).collect();
                self.record_definer(q, DefinerKind::Or, names.clone(), None, None);
                let atoms: Vec<Atom> = names
                    .into_iter()
                    .map(|name| Atom::Concept(name, x.clone()))
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
                self.record_definer(
                    q,
                    DefinerKind::Exists,
                    vec![filler_name.clone()],
                    Some(role_name.clone()),
                    None,
                );
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
                self.record_definer(
                    q,
                    DefinerKind::Forall,
                    vec![filler_name.clone()],
                    Some(role_name.clone()),
                    None,
                );
                // Propagation: Q(x) ∧ R(x,y) → D(y)
                self.clauses.push(clause(
                    [
                        qx.clone(),
                        Atom::Role(role_name.clone(), x.clone(), y.clone()),
                    ],
                    [Atom::Concept(filler_name.clone(), y.clone())],
                ));
                // Introduction, only when this ∀R.D occurs negatively somewhere.
                if self.needs_forall_intro.contains(c) {
                    let nq = self.fresh();
                    let nd = self.fresh();
                    self.record_definer(&nq, DefinerKind::Not, vec![q.to_string()], None, None);
                    self.record_definer(
                        &nd,
                        DefinerKind::Not,
                        vec![filler_name.clone()],
                        None,
                        None,
                    );
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
                self.record_definer(
                    q,
                    DefinerKind::SelfRestriction,
                    Vec::new(),
                    Some(role_name.clone()),
                    None,
                );
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
                self.record_definer(
                    q,
                    DefinerKind::AtLeast,
                    vec![filler_name.clone()],
                    Some(role_name.clone()),
                    Some(*n),
                );
                if self.card {
                    // Definitional `q ⊑ ≥n role.filler` (Konclude applyATLEASTRule).
                    self.hooks.cardinalities.push(crate::json_io::CardMeta {
                        marker: q.to_string(),
                        min: true,
                        n: *n as u32,
                        role: role_name.clone(),
                        filler: filler_name.clone(),
                    });
                }
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
                self.record_definer(
                    q,
                    DefinerKind::AtMost,
                    vec![filler_name.clone()],
                    Some(role_name.clone()),
                    Some(*n),
                );
                if self.card {
                    // Definitional `q ⊑ ≤n role.filler` (Konclude applyATMOSTRule).
                    self.hooks.cardinalities.push(crate::json_io::CardMeta {
                        marker: q.to_string(),
                        min: false,
                        n: *n as u32,
                        role: role_name.clone(),
                        filler: filler_name.clone(),
                    });
                }
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
                    self.record_definer(&nq, DefinerKind::Not, vec![q.to_string()], None, None);
                    if self.card {
                        // Recognition proxy `NQ ≡ ¬q ≡ ≥(n+1) role.filler`: the
                        // n+1 pairwise-distinct witnesses below are the same
                        // applyATLEASTRule expansion, so route NQ through the
                        // first-class `≥(n+1)` rule too (else it re-explodes).
                        self.hooks.cardinalities.push(crate::json_io::CardMeta {
                            marker: nq.clone(),
                            min: true,
                            n: (*n + 1) as u32,
                            role: role_name.clone(),
                            filler: filler_name.clone(),
                        });
                    }
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
        if self.trigger_absorb {
            if let Some((trigger_sub, trigger_sup)) = Self::triggered_orientation(sub, sup) {
                if self.emit_structural_subclass(&trigger_sub, &trigger_sup) {
                    return;
                }
            }
        }
        let q_sub = self.q(sub);
        let q_sup = self.q(sup);
        let x = var_x();
        self.clauses.push(clause(
            [Atom::Concept(q_sub, x.clone())],
            [Atom::Concept(q_sup, x)],
        ));
    }

    fn mark_subclass_polarity(&mut self, sub: &Concept, sup: &Concept) {
        // The structural compiler expands Boolean antecedents directly and
        // reifies only existential restrictions. Those restriction definitions
        // are Horn and emit both directions independently of KM_ABSORB, so the
        // antecedent still needs no global polarity mark (which would recreate
        // excluded-middle clauses for unrelated Boolean definers).
        if self.trigger_absorb {
            if let Some((trigger_sub, trigger_sup)) = Self::triggered_orientation(sub, sup) {
                debug_assert!(Self::structurally_triggerable(&trigger_sub));
                self.mark_polarity(&trigger_sup, false);
                return;
            }
        }
        self.mark_polarity(sub, true);
        self.mark_polarity(sup, false);
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
                && cl
                    .body
                    .iter()
                    .filter(|a| matches!(a, Atom::Role(..)))
                    .count()
                    == 2
                && cl
                    .body
                    .iter()
                    .filter(|a| matches!(a, Atom::Concept(..)))
                    .count()
                    == 2
        });
        assert!(
            found,
            "missing ≥2 recognition clause; got {:#?}",
            cf.clauses
        );
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
        assert!(
            !has_recognition(&cf),
            "positive-only ≥2 must not emit recognition"
        );
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
            cf.clauses.iter().any(|cl| {
                cl.body.is_empty()
                    && cl.head.len() == 2
                    && cl.head.iter().all(|a| matches!(a, Atom::Concept(..)))
            })
        };
        // positive-only: skipped
        let mut cf = Clausifier::new();
        cf.mark_polarity(&mk(), false);
        cf.q(&mk());
        assert!(
            !has_recognition(&cf),
            "positive-only ≤1 must not emit recognition"
        );
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
        // `Clausifier::new` reads the process-wide production setting. Other
        // frontend tests intentionally exercise route bundles in parallel, so
        // make this unit test's requested mode explicit instead of depending
        // on ambient `KM_ABSORB` timing.
        cf.absorb = false;
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

    #[test]
    fn trigger_absorb_compiles_and_exists_antecedent() {
        let mut cf = Clausifier::new();
        cf.trigger_absorb = true;
        let sub = mk_and([
            Concept::Name("A".into()),
            Concept::Exists(Role::Name("r".into()), Box::new(Concept::Name("B".into()))),
        ]);
        cf.mark_subclass_polarity(&sub, &Concept::Name("C".into()));
        cf.subclass_clauses(&sub, &Concept::Name("C".into()));

        let implication = cf
            .clauses
            .iter()
            .find(|cl| cl.head == vec![Atom::Concept("C".into(), var_x())])
            .expect("trigger implication");
        assert!(implication
            .body
            .contains(&Atom::Concept("A".into(), var_x())));
        let exists_marker = implication
            .body
            .iter()
            .find_map(|a| match a {
                Atom::Concept(name, term) if term == &var_x() && name.starts_with("Q_") => {
                    Some(name.clone())
                }
                _ => None,
            })
            .expect("predecessor-local existential trigger");
        assert!(cf.clauses.iter().any(|cl| {
            cl.head == vec![Atom::Concept(exists_marker.clone(), var_x())]
                && cl
                    .body
                    .iter()
                    .any(|a| matches!(a, Atom::Role(r, _, _) if r == "r"))
                && cl
                    .body
                    .iter()
                    .any(|a| matches!(a, Atom::Concept(n, Term::Var(v)) if n == "B" && v == "y"))
        }));
        assert!(!implication.body.iter().any(|a| matches!(a, Atom::Role(..))));
        assert!(!cf
            .clauses
            .iter()
            .any(|c| c.body.is_empty() && c.head.len() > 1));
    }

    /// ORE 703 witness: two existential conjuncts must be recognised in their
    /// respective successor contexts and joined through local markers at x.
    /// A single body containing `r(x,y0)` and `r(x,y1)` is not an admissible
    /// context-calculus trigger even though it is first-order equivalent.
    #[test]
    fn trigger_absorb_localises_multiple_existential_antecedents() {
        let mut cf = Clausifier::new();
        cf.trigger_absorb = true;
        let sub = mk_and([
            Concept::Name("P".into()),
            Concept::Exists(Role::Name("r".into()), Box::new(Concept::Name("B".into()))),
            Concept::Exists(Role::Name("r".into()), Box::new(Concept::Name("D".into()))),
        ]);
        cf.mark_subclass_polarity(&sub, &Concept::Name("T".into()));
        cf.subclass_clauses(&sub, &Concept::Name("T".into()));

        let implication = cf
            .clauses
            .iter()
            .find(|cl| cl.head == vec![Atom::Concept("T".into(), var_x())])
            .expect("trigger implication");
        assert_eq!(implication.body.len(), 3);
        assert!(implication
            .body
            .iter()
            .all(|a| matches!(a, Atom::Concept(_, t) if t == &var_x())));
        assert_eq!(
            implication
                .body
                .iter()
                .filter(|a| matches!(a, Atom::Concept(n, _) if n.starts_with("Q_")))
                .count(),
            2
        );
        assert!(!cf.clauses.iter().any(|cl| {
            cl.body
                .iter()
                .filter_map(|a| match a {
                    Atom::Role(_, _, Term::Var(v)) if v.starts_with("__trig") => Some(v),
                    _ => None,
                })
                .collect::<HashSet<_>>()
                .len()
                > 1
        }));
    }

    #[test]
    fn trigger_absorb_distributes_union_antecedent() {
        let mut cf = Clausifier::new();
        cf.trigger_absorb = true;
        let sub = mk_or([Concept::Name("A".into()), Concept::Name("B".into())]);
        cf.subclass_clauses(&sub, &Concept::Name("C".into()));
        assert_eq!(cf.clauses.len(), 2);
        assert!(cf.clauses.iter().any(|c| {
            c.body == vec![Atom::Concept("A".into(), var_x())]
                && c.head == vec![Atom::Concept("C".into(), var_x())]
        }));
        assert!(cf.clauses.iter().any(|c| {
            c.body == vec![Atom::Concept("B".into(), var_x())]
                && c.head == vec![Atom::Concept("C".into(), var_x())]
        }));
    }

    #[test]
    fn trigger_absorb_moves_negative_rhs_disjunct_into_body() {
        let mut cf = Clausifier::new();
        cf.trigger_absorb = true;
        let sup = mk_or([
            Concept::Not(Box::new(Concept::Name("B".into()))),
            Concept::Name("C".into()),
        ]);
        cf.mark_subclass_polarity(&Concept::Name("A".into()), &sup);
        cf.subclass_clauses(&Concept::Name("A".into()), &sup);
        assert_eq!(cf.clauses.len(), 1);
        assert_eq!(
            cf.clauses[0].body,
            vec![
                Atom::Concept("A".into(), var_x()),
                Atom::Concept("B".into(), var_x())
            ]
        );
        assert_eq!(cf.clauses[0].head, vec![Atom::Concept("C".into(), var_x())]);
    }

    #[test]
    fn trigger_absorb_retains_definer_provenance() {
        let mut cf = Clausifier::new();
        cf.trigger_absorb = true;
        let c = Concept::Exists(Role::Name("r".into()), Box::new(Concept::Name("B".into())));
        let marker = cf.q(&c);
        assert!(cf.hooks.definers.iter().any(|d| {
            d.marker == marker
                && d.kind == DefinerKind::Exists
                && d.operands == vec!["B".to_string()]
                && d.role.as_deref() == Some("r")
        }));
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
                clausifier.mark_subclass_polarity(&s, &p);
            }
            Axiom::EquivalentClasses(l, r) => {
                let nl = nnf(l);
                let nr = nnf(r);
                clausifier.mark_subclass_polarity(&nl, &nr);
                clausifier.mark_subclass_polarity(&nr, &nl);
            }
            Axiom::DisjointClasses(l, r) => {
                let conj = mk_and([nnf(l), nnf(r)]);
                clausifier.mark_subclass_polarity(&conj, &Concept::Bottom);
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
                if clausifier.trigger_absorb {
                    clausifier
                        .hooks
                        .source_axioms
                        .push(crate::json_io::SourceAxiomMeta {
                            kind: crate::json_io::SourceAxiomKind::SubClass,
                            left: s.clone(),
                            right: p.clone(),
                        });
                }
                clausifier.subclass_clauses(&s, &p);
            }
            Axiom::EquivalentClasses(l, r) => {
                let nl = nnf(l);
                let nr = nnf(r);
                if clausifier.trigger_absorb {
                    clausifier
                        .hooks
                        .source_axioms
                        .push(crate::json_io::SourceAxiomMeta {
                            kind: crate::json_io::SourceAxiomKind::Equivalent,
                            left: nl.clone(),
                            right: nr.clone(),
                        });
                }
                clausifier.subclass_clauses(&nl, &nr);
                clausifier.subclass_clauses(&nr, &nl);
            }
            Axiom::DisjointClasses(l, r) => {
                let nl = nnf(l);
                let nr = nnf(r);
                if clausifier.trigger_absorb {
                    clausifier
                        .hooks
                        .source_axioms
                        .push(crate::json_io::SourceAxiomMeta {
                            kind: crate::json_io::SourceAxiomKind::Disjoint,
                            left: nl.clone(),
                            right: nr.clone(),
                        });
                }
                let conj = mk_and([nl, nr]);
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
                clausifier.clauses.push(constraint([Atom::Role(
                    role.clone(),
                    x.clone(),
                    x.clone(),
                )]));
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
                // KM_HT_CARD_FN (opt-in): functionality is `⊤ ⊑ ≤1 R.⊤`, i.e. a
                // first-class atmost anchored on every node (Konclude folds it with
                // applyATMOSTRule; the raw Eq-head clause above cannot fold the
                // model). Marker == filler == a fresh universal concept asserted as
                // a ⊤-fact: every node carries the marker (installs the ≤1) and
                // every R-successor carries the filler (counts toward the bound).
                // The Eq clause stays — the CB engine consumes it, and on the HT
                // it is redundant-but-sound alongside the card rule. Gated opt-in:
                // tagging makes EVERY functional-role ontology card-routable
                // (spawns the card HT arm + disables emelim there), which needs its
                // own corpus validation before any default flip.
                if clausifier.card && std::env::var_os("KM_HT_CARD_FN").is_some() {
                    let qf = format!("Q_fn_{}", role);
                    clausifier
                        .clauses
                        .push(fact([Atom::Concept(qf.clone(), x.clone())]));
                    clausifier
                        .hooks
                        .cardinalities
                        .push(crate::json_io::CardMeta {
                            marker: qf.clone(),
                            min: false,
                            n: 1,
                            role: role.clone(),
                            filler: qf,
                        });
                }
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
                clausifier.register_abox_individual(individual);
                let ind = Term::Ind(individual.clone());
                let nc = nnf(concept);
                let q = clausifier.q(&nc);
                abox_clauses.push(fact([Atom::Concept(q, ind)]));
            }
            Axiom::RoleAssertion(role, source, target) => {
                clausifier.register_abox_individual(source);
                clausifier.register_abox_individual(target);
                abox_clauses.push(fact([Atom::Role(
                    role.clone(),
                    Term::Ind(source.clone()),
                    Term::Ind(target.clone()),
                )]));
            }
            Axiom::NegativeRoleAssertion(role, source, target) => {
                // Exact ground constraint ¬R(a,b).  It enters the ordinary
                // clause set only under KM_NOMINALS (augment keeps ABox clauses
                // in that mode), so the default TBox stream stays unchanged.
                // The typed HT view removes this exact shape only after matching
                // it to the independently certified source payload.
                clausifier.register_abox_individual(source);
                clausifier.register_abox_individual(target);
                abox_clauses.push(constraint([Atom::Role(
                    role.clone(),
                    Term::Ind(source.clone()),
                    Term::Ind(target.clone()),
                )]));
            }
            Axiom::SameIndividual(l, r) => {
                clausifier.register_abox_individual(l);
                clausifier.register_abox_individual(r);
                abox_clauses.push(fact([Atom::Eq(Term::Ind(l.clone()), Term::Ind(r.clone()))]));
            }
            Axiom::DifferentIndividuals(l, r) => {
                clausifier.register_abox_individual(l);
                clausifier.register_abox_individual(r);
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
