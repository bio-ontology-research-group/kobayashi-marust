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
    SameIndividual(String, String),
    DifferentIndividuals(String, String),
    // SWRL DL-safe rule: body ⟶ head (conjunction of atoms each side). Variables
    // range only over named individuals (DL-safety). Consumed by the HT path; a
    // rule whose atoms we cannot represent is dropped wholesale (sound: a dropped
    // constraint can lose an inconsistency, never invent one).
    Rule(Vec<RuleAtom>, Vec<RuleAtom>),
}

/// A term inside a SWRL rule atom: either a rule variable or a named individual.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum RuleTerm {
    Var(String),
    Ind(String),
}

/// A SWRL rule atom (the subset we represent: class membership, role edge, and
/// the (in)equality guards). Datatype/builtin atoms are not represented; a rule
/// containing one is dropped by the parser.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum RuleAtom {
    Class(Concept, RuleTerm),
    Role(String, RuleTerm, RuleTerm),
    Same(RuleTerm, RuleTerm),
    Diff(RuleTerm, RuleTerm),
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
                | Axiom::SameIndividual(..)
                | Axiom::DifferentIndividuals(..)
        )
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
    seen: std::collections::HashSet<std::rc::Rc<Axiom>>,
}

impl Ontology {
    pub fn new() -> Self {
        Ontology::default()
    }

    /// Mirror `Ontology.add` over a `set`: ignore duplicate axioms.
    pub fn add(&mut self, ax: Axiom) {
        let ax = std::rc::Rc::new(ax);
        if self.seen.insert(ax.clone()) {
            self.axioms.push(ax);
        }
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
}
