//! Object-sort guard for the data-node abstraction.
//!
//! The frontend represents a data value as an ordinary node and a data range as
//! a `__dt__` concept. An axiom that constrains every object (`owl:Thing ⊑ {a}`,
//! `¬A ⊑ B`, `∀r.C ⊑ D`) would then constrain data nodes as well, which the OWL 2
//! direct semantics does not. This pass finds exactly those axioms and guards
//! their left side with the private class [`OBJ`].
//!
//! The rule and both model-transfer directions are stated and checked in
//! `lean/ContextCalculus/SortedDataAbstraction.lean`: [`sort_shape`] is
//! `sortShape`, the guard rule is `canonical_axiom`, and the typing axioms are
//! the `typed` hypothesis of `abstract_axiom`. See
//! `docs/SORTED-DATA-ABSTRACTION.md`.
//!
//! When no axiom needs a guard the ontology is left untouched.

use std::collections::BTreeSet;

use super::syntax::{mk_and, Axiom, Concept, Ontology, Role};

/// Private class holding the object sort. The `__` prefix keeps it out of the
/// published taxonomy, and source IRIs with that prefix are escaped by
/// `IriRegistry`, so it cannot collide with a source class.
pub const OBJ: &str = "__km_obj";

/// Shape of a class expression at a data node of the canonical model.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Shape {
    /// False at every data node: the expression anchors its subject in the
    /// object sort.
    pub anchored: bool,
    /// True at every data node.
    pub vacuous: bool,
}

const ANCHORED: Shape = Shape { anchored: true, vacuous: false };
const VACUOUS: Shape = Shape { anchored: false, vacuous: true };

/// Why the guard pass cannot treat an ontology exactly.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Unsupported {
    /// The universal role reaches data nodes from every object.
    UniversalRole,
    /// A reflexive role puts an object-role edge on every node, data nodes
    /// included, so the shape analysis no longer holds.
    ReflexiveRole(String),
    /// A data range occurs where a class is expected.
    DataRangeAsClass(String),
}

impl std::fmt::Display for Unsupported {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Unsupported::UniversalRole => write!(f, "universal role with data properties"),
            Unsupported::ReflexiveRole(r) => write!(f, "reflexive role {r} with data properties"),
            Unsupported::DataRangeAsClass(n) => write!(f, "data range {n} in a class position"),
        }
    }
}

fn is_data_range(name: &str) -> bool {
    name.starts_with("__dt__")
}

/// Lean `sortShape`. Every expression has exactly one of the two shapes, since
/// its truth value at a data node follows from its structure alone. Fillers are
/// never inspected: each quantifier already fixes the shape, because a data node
/// has no outgoing edge.
pub fn sort_shape(concept: &Concept) -> Result<Shape, Unsupported> {
    Ok(match concept {
        Concept::Name(name) if is_data_range(name) => {
            return Err(Unsupported::DataRangeAsClass(name.clone()))
        }
        Concept::Name(_) | Concept::Bottom | Concept::Nominal(_) => ANCHORED,
        Concept::Top => VACUOUS,
        Concept::Not(inner) => {
            let s = sort_shape(inner)?;
            Shape { anchored: s.vacuous, vacuous: s.anchored }
        }
        Concept::And(parts) => {
            let mut shape = Shape { anchored: false, vacuous: true };
            for part in parts {
                let s = sort_shape(part)?;
                shape.anchored |= s.anchored;
                shape.vacuous &= s.vacuous;
            }
            shape
        }
        Concept::Or(parts) => {
            let mut shape = Shape { anchored: true, vacuous: false };
            for part in parts {
                let s = sort_shape(part)?;
                shape.anchored &= s.anchored;
                shape.vacuous |= s.vacuous;
            }
            shape
        }
        Concept::Exists(role, _) | Concept::HasSelf(role) => {
            reject_universal(role)?;
            ANCHORED
        }
        Concept::Forall(role, _) | Concept::AtMost(_, role, _) => {
            reject_universal(role)?;
            VACUOUS
        }
        Concept::AtLeast(n, role, _) => {
            reject_universal(role)?;
            if *n > 0 { ANCHORED } else { VACUOUS }
        }
    })
}

fn reject_universal(role: &Role) -> Result<(), Unsupported> {
    match role {
        Role::Universal => Err(Unsupported::UniversalRole),
        _ => Ok(()),
    }
}

/// An inclusion holds at every data node without a guard when its left side is
/// false there or its right side is true there.
fn inclusion_is_safe(sub: &Concept, sup: &Concept) -> Result<bool, Unsupported> {
    Ok(sort_shape(sub)?.anchored || sort_shape(sup)?.vacuous)
}

fn guarded(sub: &Concept) -> Concept {
    mk_and([Concept::Name(OBJ.to_string()), sub.clone()])
}

/// Result of the pass.
#[derive(Default, Debug, PartialEq, Eq)]
pub struct Outcome {
    /// Number of inclusions that received the guard.
    pub guarded: usize,
    /// Typing axioms added (`A ⊑ Obj`, `Obj ⊑ ∀r.Obj`, `Obj(a)`).
    pub typing: usize,
}

fn collect_names(
    concept: &Concept,
    classes: &mut BTreeSet<String>,
    individuals: &mut BTreeSet<String>,
    roles: &mut BTreeSet<Role>,
) {
    match concept {
        Concept::Name(name) => {
            if !is_data_range(name) {
                classes.insert(name.clone());
            }
        }
        Concept::Nominal(individual) => {
            individuals.insert(individual.clone());
        }
        Concept::Top | Concept::Bottom => {}
        Concept::Not(inner) => collect_names(inner, classes, individuals, roles),
        Concept::And(parts) | Concept::Or(parts) => {
            for part in parts {
                collect_names(part, classes, individuals, roles);
            }
        }
        Concept::Exists(role, filler)
        | Concept::Forall(role, filler)
        | Concept::AtLeast(_, role, filler)
        | Concept::AtMost(_, role, filler) => {
            roles.insert(role.clone());
            collect_names(filler, classes, individuals, roles);
        }
        Concept::HasSelf(role) => {
            roles.insert(role.clone());
        }
    }
}

/// Guard every inclusion a data node could violate and, when at least one guard
/// was needed, add the typing axioms that keep object-role successors, named
/// classes and individuals inside the object sort.
///
/// `data_roles` holds the internal names of the data properties; every other
/// role name is an object role. `declared_classes` are the classes that will be
/// queried even if no axiom mentions them. Call this only for an ontology that
/// uses data properties: a reflexive role is declined here because it breaks the
/// shape analysis at data nodes, and that refusal is pointless without data.
pub fn apply(
    ontology: &mut Ontology,
    data_roles: &BTreeSet<String>,
    declared_classes: &BTreeSet<String>,
) -> Result<Outcome, Unsupported> {
    let mut replacements: Vec<(Axiom, Vec<Axiom>)> = Vec::new();
    for axiom in ontology.tbox() {
        match axiom {
            Axiom::SubClassOf(sub, sup) => {
                if !inclusion_is_safe(sub, sup)? {
                    replacements.push((
                        axiom.clone(),
                        vec![Axiom::SubClassOf(guarded(sub), sup.clone())],
                    ));
                }
            }
            Axiom::EquivalentClasses(left, right) => {
                let forward = inclusion_is_safe(left, right)?;
                let backward = inclusion_is_safe(right, left)?;
                if !(forward && backward) {
                    let side = |safe: bool, sub: &Concept, sup: &Concept| {
                        Axiom::SubClassOf(if safe { sub.clone() } else { guarded(sub) }, sup.clone())
                    };
                    replacements.push((
                        axiom.clone(),
                        vec![side(forward, left, right), side(backward, right, left)],
                    ));
                }
            }
            Axiom::DisjointClasses(left, right) => {
                if !(sort_shape(left)?.anchored || sort_shape(right)?.anchored) {
                    replacements.push((
                        axiom.clone(),
                        vec![Axiom::SubClassOf(
                            mk_and([Concept::Name(OBJ.to_string()), left.clone(), right.clone()]),
                            Concept::Bottom,
                        )],
                    ));
                }
            }
            _ => {}
        }
    }
    for axiom in ontology.rbox() {
        if let Axiom::ReflexiveRole(role) = axiom {
            return Err(Unsupported::ReflexiveRole(role.clone()));
        }
    }
    if replacements.is_empty() {
        return Ok(Outcome::default());
    }

    let mut classes = declared_classes.clone();
    let mut individuals = BTreeSet::new();
    let mut roles = BTreeSet::new();
    for axiom in ontology.tbox().chain(ontology.abox()) {
        match axiom {
            Axiom::SubClassOf(a, b) | Axiom::EquivalentClasses(a, b) | Axiom::DisjointClasses(a, b) => {
                collect_names(a, &mut classes, &mut individuals, &mut roles);
                collect_names(b, &mut classes, &mut individuals, &mut roles);
            }
            Axiom::ConceptAssertion(concept, individual) => {
                collect_names(concept, &mut classes, &mut individuals, &mut roles);
                individuals.insert(individual.clone());
            }
            Axiom::RoleAssertion(role, a, b) | Axiom::NegativeRoleAssertion(role, a, b) => {
                roles.insert(Role::Name(role.clone()));
                individuals.insert(a.clone());
                individuals.insert(b.clone());
            }
            Axiom::SameIndividual(a, b) | Axiom::DifferentIndividuals(a, b) => {
                individuals.insert(a.clone());
                individuals.insert(b.clone());
            }
            _ => {}
        }
    }
    // RBox axioms relate role names; an inverse used anywhere makes both
    // directions of that role reachable from an expression.
    let mut inverse_used = roles.iter().any(|role| matches!(role, Role::Inverse(_)));
    for axiom in ontology.rbox() {
        match axiom {
            Axiom::RoleInclusion(a, b) | Axiom::InverseRoles(a, b) | Axiom::DisjointRoles(a, b) => {
                roles.insert(Role::Name(a.clone()));
                roles.insert(Role::Name(b.clone()));
                inverse_used |= matches!(axiom, Axiom::InverseRoles(..));
            }
            Axiom::RoleChain(chain, sup) => {
                roles.extend(chain.iter().cloned().map(Role::Name));
                roles.insert(Role::Name(sup.clone()));
            }
            Axiom::TransitiveRole(r)
            | Axiom::AsymmetricRole(r)
            | Axiom::IrreflexiveRole(r)
            | Axiom::FunctionalRole(r) => {
                roles.insert(Role::Name(r.clone()));
            }
            Axiom::SymmetricRole(r) | Axiom::InverseFunctionalRole(r) => {
                roles.insert(Role::Name(r.clone()));
                inverse_used = true;
            }
            _ => {}
        }
    }
    let object_roles: BTreeSet<String> = roles
        .into_iter()
        .filter_map(|role| match role {
            Role::Name(name) | Role::Inverse(name) => Some(name),
            Role::Universal => None,
        })
        .filter(|name| !data_roles.contains(name))
        .collect();

    let mut outcome = Outcome { guarded: replacements.len(), typing: 0 };
    let removed: std::collections::HashSet<Axiom> =
        replacements.iter().map(|(old, _)| old.clone()).collect();
    ontology.retain_axioms(|axiom| !removed.contains(axiom));
    for (_, new) in replacements {
        for axiom in new {
            ontology.add(axiom);
        }
    }
    let obj = || Concept::Name(OBJ.to_string());
    for class in classes {
        if class != OBJ {
            ontology.add(Axiom::SubClassOf(Concept::Name(class), obj()));
            outcome.typing += 1;
        }
    }
    for role in object_roles {
        ontology.add(Axiom::SubClassOf(
            obj(),
            Concept::Forall(Role::Name(role.clone()), Box::new(obj())),
        ));
        outcome.typing += 1;
        if inverse_used {
            ontology.add(Axiom::SubClassOf(
                obj(),
                Concept::Forall(Role::Inverse(role), Box::new(obj())),
            ));
            outcome.typing += 1;
        }
    }
    for individual in individuals {
        ontology.add(Axiom::ConceptAssertion(obj(), individual));
        outcome.typing += 1;
    }
    Ok(outcome)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn name(n: &str) -> Concept {
        Concept::Name(n.to_string())
    }
    fn role(n: &str) -> Role {
        Role::Name(n.to_string())
    }
    fn not(c: Concept) -> Concept {
        Concept::Not(Box::new(c))
    }

    #[test]
    fn shapes_follow_the_lean_definition() {
        assert_eq!(sort_shape(&name("A")).unwrap(), ANCHORED);
        assert_eq!(sort_shape(&Concept::Top).unwrap(), VACUOUS);
        assert_eq!(sort_shape(&Concept::Bottom).unwrap(), ANCHORED);
        assert_eq!(sort_shape(&not(name("A"))).unwrap(), VACUOUS);
        assert_eq!(sort_shape(&not(Concept::Top)).unwrap(), ANCHORED);
        let exists = Concept::Exists(role("r"), Box::new(Concept::Top));
        let forall = Concept::Forall(role("r"), Box::new(name("A")));
        assert_eq!(sort_shape(&exists).unwrap(), ANCHORED);
        assert_eq!(sort_shape(&forall).unwrap(), VACUOUS);
        assert_eq!(sort_shape(&Concept::AtLeast(0, role("r"), Box::new(Concept::Top))).unwrap(), VACUOUS);
        assert_eq!(sort_shape(&Concept::AtLeast(2, role("r"), Box::new(Concept::Top))).unwrap(), ANCHORED);
        assert_eq!(sort_shape(&Concept::AtMost(1, role("r"), Box::new(Concept::Top))).unwrap(), VACUOUS);
        // A conjunction is anchored by one conjunct; a disjunction needs all.
        let mixed_and = mk_and([name("A"), forall.clone()]);
        assert_eq!(sort_shape(&mixed_and).unwrap(), ANCHORED);
        let mixed_or = super::super::syntax::mk_or([name("A"), forall]);
        assert_eq!(sort_shape(&mixed_or).unwrap(), VACUOUS);
        let anchored_by_bottom = mk_and([not(name("A")), not(Concept::Top)]);
        assert_eq!(sort_shape(&anchored_by_bottom).unwrap(), ANCHORED);
        // One true disjunct makes a disjunction true at a data node.
        let covering = super::super::syntax::mk_or([not(name("A")), name("B")]);
        assert_eq!(sort_shape(&covering).unwrap(), VACUOUS);
        let all_true = mk_and([not(name("A")), Concept::AtMost(1, role("r"), Box::new(Concept::Top))]);
        assert_eq!(sort_shape(&all_true).unwrap(), VACUOUS);
    }

    #[test]
    fn anchored_ontology_is_untouched() {
        let mut ontology = Ontology::new();
        ontology.add(Axiom::SubClassOf(name("A"), Concept::Exists(role("p"), Box::new(name("__dt__string")))));
        ontology.add(Axiom::SubClassOf(Concept::Top, Concept::Forall(role("r"), Box::new(name("B")))));
        ontology.add(Axiom::DisjointClasses(name("A"), not(name("B"))));
        let before: Vec<Axiom> = ontology.tbox().cloned().collect();
        let data: BTreeSet<String> = ["p".to_string()].into();
        let outcome = apply(&mut ontology, &data, &BTreeSet::new()).unwrap();
        assert_eq!(outcome, Outcome::default());
        assert_eq!(before, ontology.tbox().cloned().collect::<Vec<_>>());
    }

    #[test]
    fn bounded_object_domain_is_guarded_and_typed() {
        // owl:Thing ≡ {a}: the two-sort counterexample. Only the inclusion
        // whose left side is owl:Thing may receive the guard.
        let mut ontology = Ontology::new();
        ontology.add(Axiom::EquivalentClasses(Concept::Top, Concept::Nominal("a".into())));
        ontology.add(Axiom::ConceptAssertion(
            Concept::Exists(role("p"), Box::new(name("__dt__val__\"0\"^^xsd:integer"))),
            "a".into(),
        ));
        ontology.add(Axiom::RoleAssertion("r".into(), "a".into(), "b".into()));
        let data: BTreeSet<String> = ["p".to_string()].into();
        let declared: BTreeSet<String> = ["C".to_string()].into();
        let outcome = apply(&mut ontology, &data, &declared).unwrap();
        assert_eq!(outcome.guarded, 1);
        let tbox: Vec<Axiom> = ontology.tbox().cloned().collect();
        assert!(tbox.contains(&Axiom::SubClassOf(name(OBJ), Concept::Nominal("a".into()))));
        assert!(tbox.contains(&Axiom::SubClassOf(Concept::Nominal("a".into()), Concept::Top)));
        assert!(tbox.contains(&Axiom::SubClassOf(name("C"), name(OBJ))));
        // Object role r is typed; data role p is not.
        assert!(tbox.contains(&Axiom::SubClassOf(
            name(OBJ),
            Concept::Forall(role("r"), Box::new(name(OBJ)))
        )));
        assert!(!tbox.iter().any(|axiom| matches!(axiom,
            Axiom::SubClassOf(_, Concept::Forall(Role::Name(p), _)) if p == "p")));
        let abox: Vec<Axiom> = ontology.abox().cloned().collect();
        assert!(abox.contains(&Axiom::ConceptAssertion(name(OBJ), "a".into())));
        assert!(abox.contains(&Axiom::ConceptAssertion(name(OBJ), "b".into())));
    }

    #[test]
    fn complement_and_universal_left_sides_are_guarded() {
        let mut ontology = Ontology::new();
        ontology.add(Axiom::SubClassOf(not(name("A")), name("B")));
        ontology.add(Axiom::SubClassOf(Concept::Forall(role("r"), Box::new(name("A"))), name("B")));
        ontology.add(Axiom::DisjointClasses(not(name("A")), not(name("B"))));
        let outcome = apply(&mut ontology, &BTreeSet::new(), &BTreeSet::new()).unwrap();
        assert_eq!(outcome.guarded, 3);
        let tbox: Vec<Axiom> = ontology.tbox().cloned().collect();
        assert!(tbox.contains(&Axiom::SubClassOf(mk_and([name(OBJ), not(name("A"))]), name("B"))));
        assert!(tbox.contains(&Axiom::SubClassOf(
            mk_and([name(OBJ), not(name("A")), not(name("B"))]),
            Concept::Bottom
        )));
    }

    #[test]
    fn reflexive_and_universal_roles_are_declined() {
        let mut ontology = Ontology::new();
        ontology.add(Axiom::ReflexiveRole("r".into()));
        assert_eq!(
            apply(&mut ontology, &BTreeSet::new(), &BTreeSet::new()),
            Err(Unsupported::ReflexiveRole("r".into()))
        );
        let mut ontology = Ontology::new();
        ontology.add(Axiom::SubClassOf(
            name("A"),
            Concept::Exists(Role::Universal, Box::new(name("B"))),
        ));
        assert_eq!(
            apply(&mut ontology, &BTreeSet::new(), &BTreeSet::new()),
            Err(Unsupported::UniversalRole)
        );
    }
}
