//! Abstraction of asserted data values to the profiles the TBox can observe.
//!
//! A positive `DataPropertyAssertion(p a v)` is carried as the class
//! assertion `a : ∃p.{v}` (`KM_DATA_ASSERTION_AS_CLASS`). The datatype
//! relation clauses are pairwise in the value vocabulary, so the conversion is
//! capped (`KM_DATA_ASSERTION_LITERAL_CAP`, 512 distinct literals); above the
//! cap the assertions used to stay uncarried and were published as dropped.
//!
//! Without data counting the TBox observes an asserted value `v` only
//! through its *profile*: whether it lies in each data range the ontology
//! mentions and whether it equals each value token it mentions. Two values
//! with one profile are interchangeable, so each asserted literal can be
//! replaced by one representative literal of its profile, which bounds the
//! value vocabulary by the number of profiles. The exactness argument, and
//! the constructs under which it fails (counting, disjoint or keyed data
//! properties, rules), are in `docs/DATA-ASSERTION-PROFILES.md`. When one of
//! those constructs is present, or a literal's profile is not decided by the
//! datatype oracle, nothing is abstracted (that literal, or the input).

use std::collections::BTreeSet;

use super::datatypes;
use super::syntax::{Axiom, Concept, Role};

/// Why the abstraction is not applied to this ontology.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Blocked {
    /// A construct that distinguishes values beyond their profile:
    /// counting, data-property disjointness, keys, or rules.
    Construct(&'static str),
}

/// What the TBox can observe about a data value: the data ranges and value
/// tokens it mentions (`__dt__` concept names, sorted).
#[derive(Debug, Default)]
pub struct Observables {
    pub names: Vec<String>,
}

/// Roles that are certainly object properties: they occur in an object
/// assertion, a role axiom only object properties have, as an inverse, or
/// with an object filler. Every other role is treated as a data property.
fn object_roles(axioms: &[&Axiom]) -> BTreeSet<String> {
    let mut object = BTreeSet::new();
    fn walk(concept: &Concept, object: &mut BTreeSet<String>) {
        match concept {
            Concept::Not(inner) => walk(inner, object),
            Concept::And(items) | Concept::Or(items) => items.iter().for_each(|c| walk(c, object)),
            Concept::Exists(role, filler)
            | Concept::Forall(role, filler)
            | Concept::AtLeast(_, role, filler)
            | Concept::AtMost(_, role, filler) => {
                match role {
                    Role::Inverse(name) => {
                        object.insert(name.clone());
                    }
                    Role::Name(name) => {
                        let data_filler = matches!(filler.as_ref(),
                            Concept::Name(n) if n.starts_with("__dt__"))
                            || matches!(filler.as_ref(), Concept::Top | Concept::Bottom);
                        if !data_filler {
                            object.insert(name.clone());
                        }
                    }
                    Role::Universal => {}
                }
                walk(filler, object);
            }
            Concept::HasSelf(Role::Name(name) | Role::Inverse(name)) => {
                object.insert(name.clone());
            }
            _ => {}
        }
    }
    for axiom in axioms {
        match axiom {
            Axiom::SubClassOf(a, b) | Axiom::EquivalentClasses(a, b) | Axiom::DisjointClasses(a, b) => {
                walk(a, &mut object);
                walk(b, &mut object);
            }
            Axiom::ConceptAssertion(c, _) => walk(c, &mut object),
            Axiom::RoleAssertion(role, ..) | Axiom::NegativeRoleAssertion(role, ..)
            | Axiom::TransitiveRole(role) | Axiom::SymmetricRole(role) | Axiom::AsymmetricRole(role)
            | Axiom::ReflexiveRole(role) | Axiom::IrreflexiveRole(role)
            | Axiom::InverseFunctionalRole(role) => {
                object.insert(role.clone());
            }
            Axiom::InverseRoles(a, b) => {
                object.insert(a.clone());
                object.insert(b.clone());
            }
            Axiom::RoleChain(chain, head) => {
                object.extend(chain.iter().cloned());
                object.insert(head.clone());
            }
            _ => {}
        }
    }
    object
}

/// The constructs that observe more than a value's profile, on a role that
/// is not certainly an object property: `≥n` with `n ≥ 2`, `≤n` with
/// `n ≥ 1` (also from exact cardinalities), functionality, and disjoint
/// properties; and any rule.
pub fn blocking_construct(axioms: &[&Axiom]) -> Option<Blocked> {
    let object = object_roles(axioms);
    let data = |role: &Role| match role {
        Role::Name(name) => !object.contains(name),
        _ => false,
    };
    fn counting(concept: &Concept, data: &dyn Fn(&Role) -> bool) -> bool {
        match concept {
            Concept::Not(inner) => counting(inner, data),
            Concept::And(items) | Concept::Or(items) => items.iter().any(|c| counting(c, data)),
            Concept::Exists(_, filler) | Concept::Forall(_, filler) => counting(filler, data),
            Concept::AtLeast(n, role, filler) => (*n >= 2 && data(role)) || counting(filler, data),
            Concept::AtMost(n, role, filler) => (*n >= 1 && data(role)) || counting(filler, data),
            _ => false,
        }
    }
    for axiom in axioms {
        match axiom {
            Axiom::SubClassOf(a, b) | Axiom::EquivalentClasses(a, b) | Axiom::DisjointClasses(a, b) => {
                if counting(a, &data) || counting(b, &data) {
                    return Some(Blocked::Construct("data cardinality"));
                }
            }
            Axiom::ConceptAssertion(c, _) if counting(c, &data) => {
                return Some(Blocked::Construct("data cardinality"));
            }
            Axiom::FunctionalRole(role) if !object.contains(role) => {
                return Some(Blocked::Construct("functional data property"));
            }
            Axiom::DisjointRoles(a, b) if !object.contains(a) || !object.contains(b) => {
                return Some(Blocked::Construct("disjoint data properties"));
            }
            Axiom::Rule(..) | Axiom::DataRule(..) => return Some(Blocked::Construct("rule")),
            _ => {}
        }
    }
    None
}

/// Every `__dt__` concept the axioms mention (data ranges and value tokens).
pub fn observables(axioms: &[&Axiom]) -> Observables {
    fn walk(concept: &Concept, out: &mut BTreeSet<String>) {
        match concept {
            Concept::Name(name) if name.starts_with("__dt__") => {
                out.insert(name.clone());
            }
            Concept::Not(inner) => walk(inner, out),
            Concept::And(items) | Concept::Or(items) => items.iter().for_each(|c| walk(c, out)),
            Concept::Exists(_, filler)
            | Concept::Forall(_, filler)
            | Concept::AtLeast(_, _, filler)
            | Concept::AtMost(_, _, filler) => walk(filler, out),
            _ => {}
        }
    }
    let mut names = BTreeSet::new();
    for axiom in axioms {
        match axiom {
            Axiom::SubClassOf(a, b) | Axiom::EquivalentClasses(a, b) | Axiom::DisjointClasses(a, b) => {
                walk(a, &mut names);
                walk(b, &mut names);
            }
            Axiom::ConceptAssertion(c, _) => walk(c, &mut names),
            _ => {}
        }
    }
    Observables { names: names.into_iter().collect() }
}

/// The profile of an asserted literal: its membership in every observed
/// range and its equality with every observed value token, or `None` when
/// the literal must keep its own identity (an undecided membership, an
/// opaque or ill-typed value, or a value equal to an observed token).
pub fn profile(literal: &str, observed: &Observables) -> Option<Vec<bool>> {
    let profile = datatypes::literal_value_profile(literal, &observed.names)?;
    let equals_token = observed.names.iter().zip(&profile)
        .any(|(name, &member)| member && name.starts_with("__dt__val__"));
    (!equals_token).then_some(profile)
}

/// Map every literal to its representative: the first literal (in the given
/// order) of its profile, or itself when it has no profile.
pub fn representatives(literals: &[String], observed: &Observables) -> Vec<String> {
    let mut first: std::collections::HashMap<Vec<bool>, String> = std::collections::HashMap::new();
    literals
        .iter()
        .map(|literal| match profile(literal, observed) {
            Some(key) => first.entry(key).or_insert_with(|| literal.clone()).clone(),
            None => literal.clone(),
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn observed(names: &[&str]) -> Observables {
        Observables { names: names.iter().map(|n| n.to_string()).collect() }
    }

    #[test]
    fn profiles_follow_observed_ranges_and_tokens() {
        let o = observed(&["__dt__integer", "__dt__string", "__dt__val__\"1\"^^xsd:integer"]);
        assert_eq!(profile("\"2\"^^xsd:integer", &o), Some(vec![true, false, false]));
        assert_eq!(profile("\"7\"^^xsd:integer", &o), Some(vec![true, false, false]));
        assert_eq!(profile("\"x\"^^xsd:string", &o), Some(vec![false, true, false]));
        assert_eq!(profile("\"x\"", &o), Some(vec![false, true, false]));
        // Equal to an observed token: keeps its identity, also in another spelling.
        assert_eq!(profile("\"1\"^^xsd:integer", &o), None);
        assert_eq!(profile("\"01\"^^xsd:integer", &o), None);
        // Ill-typed or opaque literals keep their identity.
        assert_eq!(profile("\"abc\"^^xsd:integer", &o), None);
        assert_eq!(profile("\"x\"^^<http://example.org/dt>", &o), None);
    }

    #[test]
    fn facet_and_complement_ranges_split_profiles() {
        let o = observed(&[
            "__dt__c__DatatypeRestriction(xsd:integer xsd:minInclusive \"18\"^^xsd:integer)",
            "__dt__c__DataComplementOf(xsd:integer)",
        ]);
        assert_eq!(profile("\"20\"^^xsd:integer", &o), Some(vec![true, false]));
        assert_eq!(profile("\"3\"^^xsd:integer", &o), Some(vec![false, false]));
        assert_eq!(profile("\"x\"^^xsd:string", &o), Some(vec![false, true]));
    }

    #[test]
    fn unknown_ranges_keep_identity() {
        let o = observed(&["__dt__iri__4_74657374"]);
        assert_eq!(profile("\"2\"^^xsd:integer", &o), None);
    }

    #[test]
    fn representatives_are_the_first_literal_of_each_profile() {
        let o = observed(&["__dt__integer", "__dt__val__\"1\"^^xsd:integer"]);
        let literals: Vec<String> = ["\"5\"^^xsd:integer", "\"x\"", "\"6\"^^xsd:integer",
            "\"1\"^^xsd:integer", "\"y\"", "\"abc\"^^xsd:integer"]
            .iter().map(|s| s.to_string()).collect();
        assert_eq!(representatives(&literals, &o), vec![
            "\"5\"^^xsd:integer", "\"x\"", "\"5\"^^xsd:integer",
            "\"1\"^^xsd:integer", "\"x\"", "\"abc\"^^xsd:integer",
        ]);
        // No observed range or token: every typed value has the empty profile.
        let none = observed(&[]);
        assert_eq!(representatives(&literals[..3], &none), vec![
            "\"5\"^^xsd:integer", "\"5\"^^xsd:integer", "\"5\"^^xsd:integer"]);
    }

    fn name(s: &str) -> Concept { Concept::Name(s.into()) }
    fn role(s: &str) -> Role { Role::Name(s.into()) }

    #[test]
    fn counting_on_data_properties_blocks_the_abstraction() {
        let dt = || Box::new(name("__dt__integer"));
        let functional = Axiom::FunctionalRole("u".into());
        assert!(blocking_construct(&[&functional]).is_some());
        let max = Axiom::SubClassOf(name("A"), Concept::AtMost(1, role("u"), Box::new(Concept::Top)));
        assert!(blocking_construct(&[&max]).is_some());
        let min2 = Axiom::SubClassOf(name("A"), Concept::AtLeast(2, role("u"), dt()));
        assert!(blocking_construct(&[&min2]).is_some());
        let disjoint = Axiom::DisjointRoles("u".into(), "w".into());
        assert!(blocking_construct(&[&disjoint]).is_some());
        // Existence, universal and min-1 restrictions observe profiles only.
        let some = Axiom::SubClassOf(name("A"), Concept::Exists(role("u"), dt()));
        let all = Axiom::SubClassOf(name("A"), Concept::Forall(role("u"), dt()));
        let min1 = Axiom::SubClassOf(name("A"), Concept::AtLeast(1, role("u"), dt()));
        let max0 = Axiom::SubClassOf(name("A"), Concept::AtMost(0, role("u"), dt()));
        assert!(blocking_construct(&[&some, &all, &min1, &max0]).is_none());
        // Counting on certain object properties does not block.
        let object_functional = Axiom::FunctionalRole("r".into());
        let assertion = Axiom::RoleAssertion("r".into(), "a".into(), "b".into());
        let object_max = Axiom::SubClassOf(name("A"), Concept::AtMost(1, role("s"), Box::new(name("B"))));
        assert!(blocking_construct(&[&object_functional, &assertion, &object_max]).is_none());
        // A functional property of unknown sort blocks (it may be a data property).
        let unknown = Axiom::FunctionalRole("q".into());
        assert!(blocking_construct(&[&assertion, &unknown]).is_some());
    }
}
