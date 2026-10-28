//! SROIQ concept / role / axiom syntax (port of `moose.sroiq.syntax`).
//!
//! Concepts derive structural `Eq`/`Hash` so the clausifier's reification cache
//! and `needs_forall_intro` set key on structural equality exactly like Python's
//! frozen dataclasses. `And`/`Or` store a `BTreeSet` of operands to mirror the
//! frozenset (order-independent, de-duplicated) semantics of `mkAnd`/`mkOr`.

use std::collections::BTreeSet;

/// Role expression in a concept position. Port of `RoleName`/`InverseRole`/
/// `UniversalRole`.
#[derive(
    Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
pub enum Role {
    Name(String),
    Inverse(String),
    Universal,
}

/// SROIQ concept expression. `Ord` is derived for `BTreeSet` membership; its
/// exact order is irrelevant to semantics (only set membership matters).
#[derive(
    Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
pub enum Concept {
    Name(String),
    Top,
    Bottom,
    Nominal(String),
    Not(Box<Concept>),
    And(BTreeSet<Concept>),
    Or(BTreeSet<Concept>),
    Exists(Role, Box<Concept>),
    Forall(Role, Box<Concept>),
    AtLeast(i64, Role, Box<Concept>),
    AtMost(i64, Role, Box<Concept>),
    HasSelf(Role),
}

/// Port of `mkAnd`: flatten nested `And`, drop `Top`, collapse to `Bottom` if
/// any conjunct is `Bottom`, return the single element when only one remains.
pub fn mk_and<I: IntoIterator<Item = Concept>>(concepts: I) -> Concept {
    let mut flat: BTreeSet<Concept> = BTreeSet::new();
    for c in concepts {
        match c {
            Concept::Top => continue,
            Concept::Bottom => return Concept::Bottom,
            Concept::And(cs) => {
                flat.extend(cs);
            }
            other => {
                flat.insert(other);
            }
        }
    }
    if flat.is_empty() {
        return Concept::Top;
    }
    if flat.len() == 1 {
        return flat.into_iter().next().unwrap();
    }
    Concept::And(flat)
}

/// Port of `mkOr`: dual of `mk_and`.
pub fn mk_or<I: IntoIterator<Item = Concept>>(concepts: I) -> Concept {
    let mut flat: BTreeSet<Concept> = BTreeSet::new();
    for c in concepts {
        match c {
            Concept::Bottom => continue,
            Concept::Top => return Concept::Top,
            Concept::Or(cs) => {
                flat.extend(cs);
            }
            other => {
                flat.insert(other);
            }
        }
    }
    if flat.is_empty() {
        return Concept::Bottom;
    }
    if flat.len() == 1 {
        return flat.into_iter().next().unwrap();
    }
    Concept::Or(flat)
}

/// The filler of a data restriction, with a provably empty data range
/// replaced by `⊥` and a provably universal one (`rdfs:Literal` and its
/// equivalents) by `⊤`. Other fillers, including every value concept, are
/// returned unchanged. See `datatypes::extent`.
pub fn data_filler(filler: Concept) -> Concept {
    use super::datatypes::extent::{data_concept_extent, DataExtent};
    match &filler {
        Concept::Name(name) => match data_concept_extent(name) {
            Some(DataExtent::Empty) => Concept::Bottom,
            Some(DataExtent::Universal) => Concept::Top,
            None => filler,
        },
        _ => filler,
    }
}

/// `DataSomeValuesFrom(p R)`: `⊥` when `R` is empty, and the unqualified
/// `≥1 p` when `R` is universal (every data value lies in `R`, so the two
/// coincide; this is also the encoding of `DataMinCardinality(1 p)`).
pub fn data_some(role: Role, filler: Concept) -> Concept {
    match data_filler(filler) {
        Concept::Bottom => Concept::Bottom,
        Concept::Top => Concept::AtLeast(1, role, Box::new(Concept::Top)),
        filler => Concept::Exists(role, Box::new(filler)),
    }
}

/// `DataAllValuesFrom(p R)`: `⊤` when `R` is universal; `∀p.⊥` (p has no
/// value) when `R` is empty.
pub fn data_all(role: Role, filler: Concept) -> Concept {
    match data_filler(filler) {
        Concept::Top => Concept::Top,
        filler => Concept::Forall(role, Box::new(filler)),
    }
}

/// `DataMinCardinality(n p R)`: an empty `R` admits no successor, so the
/// restriction is `⊥` for `n ≥ 1` and `⊤` for `n = 0`.
pub fn data_at_least(n: i64, role: Role, filler: Concept) -> Concept {
    match data_filler(filler) {
        Concept::Bottom if n >= 1 => Concept::Bottom,
        Concept::Bottom => Concept::Top,
        filler => Concept::AtLeast(n, role, Box::new(filler)),
    }
}

/// `DataMaxCardinality(n p R)`: an empty `R` has no successor to count, so
/// the restriction is `⊤`.
pub fn data_at_most(n: i64, role: Role, filler: Concept) -> Concept {
    match data_filler(filler) {
        Concept::Bottom => Concept::Top,
        filler => Concept::AtMost(n, role, Box::new(filler)),
    }
}

/// SROIQ axiom (TBox / RBox / ABox). Port of the `syntax` axiom dataclasses.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Axiom {
    // TBox
    SubClassOf(Concept, Concept),
    EquivalentClasses(Concept, Concept),
    DisjointClasses(Concept, Concept),
    // RBox
    RoleInclusion(String, String),
    RoleChain(Vec<String>, String),
    TransitiveRole(String),
    SymmetricRole(String),
    AsymmetricRole(String),
    ReflexiveRole(String),
    IrreflexiveRole(String),
    InverseRoles(String, String),
    FunctionalRole(String),
    InverseFunctionalRole(String),
    DisjointRoles(String, String),
    // ABox
    ConceptAssertion(Concept, String),
    RoleAssertion(String, String, String),
    /// `NegativeObjectPropertyAssertion(R a b)` (an inverse spelling arrives
    /// argument-swapped). Not clausified (the CB core drops ABox negations —
    /// sound for subsumption); consumed by the `abox_consistency` precheck,
    /// where a matching positive assertion is a genuine global inconsistency.
    NegativeRoleAssertion(String, String, String),
    SameIndividual(String, String),
    DifferentIndividuals(String, String),
    // SWRL DL-safe rule: body ⟶ head (conjunction of atoms each side). Variables
    // range only over named individuals (DL-safety). Consumed by the HT path; a
    // rule whose atoms we cannot represent is dropped wholesale (sound: a dropped
    // constraint can lose an inconsistency, never invent one).
    Rule(Vec<RuleAtom>, Vec<RuleAtom>),
    /// Retained concrete-domain rule obligation. It must be lowered by an
    /// exact datatype backend before ordinary object-rule publication.
    DataRule(Vec<RuleAtom>, Vec<RuleAtom>),
}

/// A term inside a SWRL rule atom: either a rule variable or a named individual.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum RuleTerm {
    Var(String),
    Ind(String),
}

/// A preserved SWRL rule atom. Concrete-domain atoms are kept in `DataRule`
/// until an exact backend lowers them; they never enter the object-only worker.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum RuleAtom {
    Class(Concept, RuleTerm),
    Role(String, RuleTerm, RuleTerm),
    Same(RuleTerm, RuleTerm),
    Diff(RuleTerm, RuleTerm),
    Data(String, RuleTerm, RuleDataTerm),
    Builtin(String, Vec<RuleDataTerm>),
    DataRange(String, RuleDataTerm),
}

/// Keep literal spellings separate from object individuals. The value decoder
/// decides datatype membership/equality later; the parser does not coerce them.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum RuleDataTerm {
    Var(String),
    Literal(String),
    Iri(String),
}

impl Axiom {
    pub fn is_tbox(&self) -> bool {
        matches!(
            self,
            Axiom::SubClassOf(..) | Axiom::EquivalentClasses(..) | Axiom::DisjointClasses(..)
        )
    }
    pub fn is_rbox(&self) -> bool {
        matches!(
            self,
            Axiom::RoleInclusion(..)
                | Axiom::RoleChain(..)
                | Axiom::TransitiveRole(..)
                | Axiom::SymmetricRole(..)
                | Axiom::AsymmetricRole(..)
                | Axiom::ReflexiveRole(..)
                | Axiom::IrreflexiveRole(..)
                | Axiom::InverseRoles(..)
                | Axiom::FunctionalRole(..)
                | Axiom::InverseFunctionalRole(..)
                | Axiom::DisjointRoles(..)
        )
    }
    pub fn is_abox(&self) -> bool {
        matches!(
            self,
            Axiom::ConceptAssertion(..)
                | Axiom::RoleAssertion(..)
                | Axiom::NegativeRoleAssertion(..)
                | Axiom::SameIndividual(..)
                | Axiom::DifferentIndividuals(..)
        )
    }
}

/// Dedup-set entry: the axiom with its structural hash computed once, so the
/// set's growth rehashes a stored `u64` instead of re-walking every axiom.
/// Equality stays full structural equality, so the set holds exactly the
/// axioms the plain `Rc<Axiom>` set held.
struct SeenAxiom {
    hash: u64,
    axiom: std::rc::Rc<Axiom>,
}

impl SeenAxiom {
    /// `builder` must be the owning set's hasher, so equal axioms always get
    /// equal stored hashes.
    fn new(axiom: std::rc::Rc<Axiom>, builder: &crate::fxhash::FxBuild) -> Self {
        use std::hash::BuildHasher;
        SeenAxiom { hash: builder.hash_one(&*axiom), axiom }
    }
}

impl PartialEq for SeenAxiom {
    fn eq(&self, other: &Self) -> bool {
        self.hash == other.hash && *self.axiom == *other.axiom
    }
}

impl Eq for SeenAxiom {}

impl std::hash::Hash for SeenAxiom {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_u64(self.hash);
    }
}

/// Port of `Ontology`. Python stores axioms in a `set` and derives tbox/rbox/
/// abox partitions on access (each itself a set). The structural canonicaliser
/// in `dump_clauses.canon` is emission-order independent, so we keep insertion
/// order and de-duplicate, which is sufficient for canonical equality.
/// Axioms are stored once behind an `Rc`; the dedup set shares the same
/// allocation instead of cloning every axiom (which doubled the AST memory).
#[derive(Default)]
pub struct Ontology {
    axioms: Vec<std::rc::Rc<Axiom>>,
    seen: crate::fxhash::FxHashSet<SeenAxiom>,
    /// Positive `DataPropertyAssertion(p a v)` axioms carried as the
    /// equivalent `ClassAssertion(DataHasValue(p v) a)` (OWL 2 Direct
    /// Semantics: `(a, v) in p` iff `a in exists p.{v}`). Counted only when the
    /// class assertion was newly added, so the ABox coverage certificate can
    /// match it against the source data-assertion count.
    data_assertions_as_class: u64,
    /// Source axioms the parser does not represent and whose omission is not
    /// entailment-neutral (keys, unsupported data axioms, unparsed DL-safe
    /// rules, unknown axiom kinds), by functional-syntax head. Published as
    /// dropped axioms of a consistent answer.
    dropped_source_axioms: std::collections::BTreeMap<String, u64>,
    /// Class assertions the conversion added. Equals `data_assertions_as_class`
    /// except when the literal-profile abstraction maps two source assertions
    /// to one class assertion.
    data_assertion_class_axioms: u64,
    /// Converted data assertions of the current parse call, committed by
    /// [`Ontology::commit_data_assertions_as_class`] only when the conversion
    /// is enabled and the literal vocabulary stays within its cap.
    pending_data_assertions: Vec<(Axiom, String)>,
    /// Distinct literals of committed conversions.
    data_assertion_literals: crate::fxhash::FxHashSet<String>,
    /// A cap overflow declines the conversion for the whole ontology.
    data_assertions_declined: bool,
    /// The source has a construct the literal-profile abstraction cannot see
    /// in the parsed axioms (a key, which the parser drops).
    literal_abstraction_blocked: bool,
}

impl Ontology {
    pub fn new() -> Self {
        Ontology::default()
    }

    /// Replace every user datatype `D` (an `__dt__iri__` concept) that a
    /// `DatatypeDefinition(D R)` defines (frontend form: an equivalence of two
    /// `__dt__` concepts) by `R` in every axiom, and drop the definitions.
    /// Definitions are resolved transitively; a cyclic or repeated
    /// definition (not OWL 2 DL) leaves the ontology unchanged.
    pub fn inline_datatype_definitions(&mut self) {
        use std::collections::BTreeMap;
        let mut defs: BTreeMap<String, Concept> = BTreeMap::new();
        for axiom in &self.axioms {
            if let Axiom::EquivalentClasses(Concept::Name(left), right @ Concept::Name(target)) = axiom.as_ref() {
                if left.starts_with("__dt__iri__") && target.starts_with("__dt__") {
                    if defs.insert(left.clone(), right.clone()).is_some() {
                        return;
                    }
                }
            }
        }
        if defs.is_empty() {
            return;
        }
        // Resolve chains; give up on a cycle.
        let names: Vec<String> = defs.keys().cloned().collect();
        for name in names {
            let mut current = defs[&name].clone();
            let mut steps = 0;
            while let Concept::Name(next) = &current {
                match defs.get(next) {
                    Some(further) if steps < 64 => { current = further.clone(); steps += 1; }
                    Some(_) => return,
                    None => break,
                }
            }
            defs.insert(name, current);
        }
        // An inlined definition can be a provably empty or universal range
        // (`DatatypeDefinition(:E DataComplementOf(rdfs:Literal))`). The
        // restriction is then simplified exactly as a direct use of that
        // range is in `parse::cls`; the `data_*` constructors return the
        // ordinary restriction for every other filler. Only a `__dt__` name
        // occurs as a data filler, so object restrictions are untouched.
        fn is_data_name(concept: &Concept) -> bool {
            matches!(concept, Concept::Name(name) if name.starts_with("__dt__"))
        }
        fn trivial(concept: &Concept) -> bool {
            matches!(concept, Concept::Top | Concept::Bottom)
        }
        fn rewrite(concept: &Concept, defs: &BTreeMap<String, Concept>) -> Concept {
            match concept {
                Concept::Name(name) => defs.get(name).cloned().unwrap_or_else(|| concept.clone()),
                Concept::Not(inner) => Concept::Not(Box::new(rewrite(inner, defs))),
                Concept::And(items) => {
                    let items: BTreeSet<Concept> = items.iter().map(|c| rewrite(c, defs)).collect();
                    if items.iter().any(trivial) { mk_and(items) } else { Concept::And(items) }
                }
                Concept::Or(items) => {
                    let items: BTreeSet<Concept> = items.iter().map(|c| rewrite(c, defs)).collect();
                    if items.iter().any(trivial) { mk_or(items) } else { Concept::Or(items) }
                }
                Concept::Exists(role, filler) if is_data_name(filler) =>
                    data_some(role.clone(), rewrite(filler, defs)),
                Concept::Forall(role, filler) if is_data_name(filler) =>
                    data_all(role.clone(), rewrite(filler, defs)),
                Concept::AtLeast(n, role, filler) if is_data_name(filler) =>
                    data_at_least(*n, role.clone(), rewrite(filler, defs)),
                Concept::AtMost(n, role, filler) if is_data_name(filler) =>
                    data_at_most(*n, role.clone(), rewrite(filler, defs)),
                Concept::Exists(role, filler) => Concept::Exists(role.clone(), Box::new(rewrite(filler, defs))),
                Concept::Forall(role, filler) => Concept::Forall(role.clone(), Box::new(rewrite(filler, defs))),
                Concept::AtLeast(n, role, filler) => Concept::AtLeast(*n, role.clone(), Box::new(rewrite(filler, defs))),
                Concept::AtMost(n, role, filler) => Concept::AtMost(*n, role.clone(), Box::new(rewrite(filler, defs))),
                other => other.clone(),
            }
        }
        let old = std::mem::take(&mut self.axioms);
        self.seen.clear();
        for axiom in old {
            let rewritten = match axiom.as_ref() {
                Axiom::EquivalentClasses(Concept::Name(left), Concept::Name(target))
                    if defs.contains_key(left) && target.starts_with("__dt__") => continue,
                Axiom::SubClassOf(a, b) => Axiom::SubClassOf(rewrite(a, &defs), rewrite(b, &defs)),
                Axiom::EquivalentClasses(a, b) => Axiom::EquivalentClasses(rewrite(a, &defs), rewrite(b, &defs)),
                Axiom::DisjointClasses(a, b) => Axiom::DisjointClasses(rewrite(a, &defs), rewrite(b, &defs)),
                Axiom::ConceptAssertion(a, individual) => Axiom::ConceptAssertion(rewrite(a, &defs), individual.clone()),
                other => other.clone(),
            };
            self.add(rewritten);
        }
    }

    /// Mirror `Ontology.add` over a `set`: ignore duplicate axioms.
    pub fn add(&mut self, ax: Axiom) {
        self.add_new(ax);
    }

    /// `add`, reporting whether the axiom was not already present.
    pub fn add_new(&mut self, ax: Axiom) -> bool {
        let ax = std::rc::Rc::new(ax);
        let entry = SeenAxiom::new(ax.clone(), self.seen.hasher());
        if self.seen.insert(entry) {
            self.axioms.push(ax);
            true
        } else {
            false
        }
    }

    /// Record a `DataPropertyAssertion` converted to its `DataHasValue`
    /// class assertion; `literal` is the glued literal it introduces.
    pub fn defer_data_assertion_as_class(&mut self, axiom: Axiom, literal: String) {
        if !self.data_assertions_declined {
            self.pending_data_assertions.push((axiom, literal));
        }
    }

    /// Add the deferred conversions when the literal vocabulary stays within
    /// `cap` distinct values; otherwise drop them all and decline every later
    /// conversion, so the ontology is exactly the one built without them (the
    /// data assertions stay unsupported, as before). The datatype relation
    /// clauses are pairwise in the value vocabulary, so this bounds the
    /// frontend cost of the conversion.
    pub fn commit_data_assertions_as_class(&mut self, cap: usize) {
        let pending = std::mem::take(&mut self.pending_data_assertions);
        if pending.is_empty() || self.data_assertions_declined {
            return;
        }
        let mut literals = self.data_assertion_literals.clone();
        for (_, literal) in &pending {
            literals.insert(literal.clone());
        }
        if literals.len() > cap {
            // Above the cap, carry each literal as the representative of the
            // profile the TBox observes (`literal_profiles`), when no
            // construct observes more than profiles.
            match self.abstract_data_assertion_literals(&pending, cap) {
                Some(abstracted) => {
                    let mut originals: crate::fxhash::FxHashSet<Axiom> = Default::default();
                    for ((original, _), (axiom, literal)) in pending.into_iter().zip(abstracted) {
                        self.data_assertion_literals.insert(literal);
                        if self.add_new(axiom) {
                            self.data_assertion_class_axioms += 1;
                        }
                        // Each distinct source assertion is carried, even
                        // when its abstraction coincides with another one.
                        if originals.insert(original) {
                            self.data_assertions_as_class += 1;
                        }
                    }
                }
                None => self.data_assertions_declined = true,
            }
            return;
        }
        self.data_assertion_literals = literals;
        for (axiom, _) in pending {
            if self.add_new(axiom) {
                self.data_assertions_as_class += 1;
                self.data_assertion_class_axioms += 1;
            }
        }
    }

    /// Class assertions added by the data-assertion conversion.
    pub fn data_assertion_class_axioms(&self) -> u64 {
        self.data_assertion_class_axioms
    }

    /// Record that the source has a construct that blocks the literal-profile
    /// abstraction although the parsed axioms do not show it (a key).
    pub fn block_literal_abstraction(&mut self) {
        self.literal_abstraction_blocked = true;
    }

    /// The pending conversions with every literal replaced by the
    /// representative of its profile, or `None` when a construct observes
    /// more than profiles or the representatives still exceed `cap`.
    fn abstract_data_assertion_literals(
        &self,
        pending: &[(Axiom, String)],
        cap: usize,
    ) -> Option<Vec<(Axiom, String)>> {
        use super::literal_profiles as lp;
        if self.literal_abstraction_blocked || !self.data_assertion_literals.is_empty() {
            return None;
        }
        let axioms: Vec<&Axiom> = self.axioms.iter().map(|a| a.as_ref())
            .chain(pending.iter().map(|(axiom, _)| axiom))
            .collect();
        if lp::blocking_construct(&axioms).is_some() {
            return None;
        }
        let observed = lp::observables(&self.axioms.iter().map(|a| a.as_ref()).collect::<Vec<_>>());
        let mut order: Vec<String> = Vec::new();
        let mut seen: crate::fxhash::FxHashSet<&str> = Default::default();
        for (_, literal) in pending {
            if seen.insert(literal.as_str()) {
                order.push(literal.clone());
            }
        }
        let representative: std::collections::HashMap<&str, String> = order.iter()
            .map(String::as_str)
            .zip(lp::representatives(&order, &observed))
            .collect();
        let distinct: crate::fxhash::FxHashSet<&String> = representative.values().collect();
        if distinct.len() > cap {
            return None;
        }
        pending.iter().map(|(axiom, literal)| {
            let rep = representative[literal.as_str()].clone();
            let Axiom::ConceptAssertion(Concept::Exists(role, _), individual) = axiom else {
                return None;
            };
            Some((
                Axiom::ConceptAssertion(
                    Concept::Exists(role.clone(), Box::new(Concept::Name(format!("__dt__val__{rep}")))),
                    individual.clone(),
                ),
                rep,
            ))
        }).collect()
    }

    /// Record a source axiom the parser drops (see `dropped_source_axioms`).
    pub fn drop_source_axiom(&mut self, head: &str) {
        *self.dropped_source_axioms.entry(head.to_string()).or_default() += 1;
    }

    /// Dropped non-neutral source axioms by functional-syntax head.
    pub fn dropped_source_axioms(&self) -> &std::collections::BTreeMap<String, u64> {
        &self.dropped_source_axioms
    }

    pub fn data_assertions_as_class(&self) -> u64 {
        self.data_assertions_as_class
    }

    pub fn tbox(&self) -> impl Iterator<Item = &Axiom> {
        self.axioms
            .iter()
            .map(|a| a.as_ref())
            .filter(|a| a.is_tbox())
    }
    pub fn rbox(&self) -> impl Iterator<Item = &Axiom> {
        self.axioms
            .iter()
            .map(|a| a.as_ref())
            .filter(|a| a.is_rbox())
    }
    pub fn abox(&self) -> impl Iterator<Item = &Axiom> {
        self.axioms
            .iter()
            .map(|a| a.as_ref())
            .filter(|a| a.is_abox())
    }
    /// SWRL DL-safe rules (consumed by the HT path).
    pub fn rules(&self) -> impl Iterator<Item = &Axiom> {
        self.axioms
            .iter()
            .map(|a| a.as_ref())
            .filter(|a| matches!(a, Axiom::Rule(..)))
    }

    pub fn datatype_rules(&self) -> impl Iterator<Item = &Axiom> {
        self.axioms.iter().map(|a| a.as_ref())
            .filter(|a| matches!(a, Axiom::DataRule(..)))
    }

    /// Drop every axiom for which `keep` is false, returning how many went.
    ///
    /// The duplicate-suppression set is kept in step, so a later `add` of a
    /// removed axiom re-inserts it.
    pub fn retain_axioms(&mut self, keep: impl Fn(&Axiom) -> bool) -> usize {
        let before = self.axioms.len();
        self.axioms.retain(|ax| {
            if keep(ax) {
                return true;
            }
            let entry = SeenAxiom::new(ax.clone(), self.seen.hasher());
            self.seen.remove(&entry);
            false
        });
        before - self.axioms.len()
    }
}
