//! Fail-closed recovery of the normalized typed CB source.
//!
//! This module recognizes the exact clause shapes emitted by the Rust OWL
//! normalizer. It deliberately returns `None` on every near miss. Publication
//! will only consume the resulting source after Lean re-encodes it and checks
//! byte-structural equality with the production ontology.

use crate::json_io::{JAtom, JClause, JTerm};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NamedRoleAxiom {
    Symmetric(String),
    Asymmetric(String),
    Reflexive(String),
    Irreflexive(String),
    InverseFunctional(String),
    Disjoint(String, String),
}

fn variable(term: &JTerm) -> Option<&str> {
    match term {
        JTerm::Var { name } => Some(name),
        _ => None,
    }
}

fn role(atom: &JAtom) -> Option<(&str, &str, &str)> {
    match atom {
        JAtom::Role {
            role,
            source,
            target,
        } => Some((role, variable(source)?, variable(target)?)),
        _ => None,
    }
}

fn equality(atom: &JAtom) -> Option<(&str, &str)> {
    match atom {
        JAtom::Eq { left, right } => Some((variable(left)?, variable(right)?)),
        _ => None,
    }
}

/// Recover one direct normalized role axiom. Symmetry is intentionally
/// recognized separately from a two-clause inverse-role definition; the latter
/// is grouped by the source-clause compiler.
pub fn direct_role_axiom(clause: &JClause) -> Option<NamedRoleAxiom> {
    match (clause.body.as_slice(), clause.head.as_slice()) {
        ([premise], [conclusion]) => {
            let (left_role, x, y) = role(premise)?;
            let (right_role, y2, x2) = role(conclusion)?;
            (left_role == right_role && x == x2 && y == y2 && x != y)
                .then(|| NamedRoleAxiom::Symmetric(left_role.to_string()))
        }
        ([first, second], []) => {
            let (first_role, x, y) = role(first)?;
            let (second_role, source, target) = role(second)?;
            if first_role == second_role && source == y && target == x && x != y {
                Some(NamedRoleAxiom::Asymmetric(first_role.to_string()))
            } else if source == x && target == y && x != y {
                Some(NamedRoleAxiom::Disjoint(
                    first_role.to_string(),
                    second_role.to_string(),
                ))
            } else {
                None
            }
        }
        ([], [fact]) => {
            let (role, source, target) = role(fact)?;
            (source == target).then(|| NamedRoleAxiom::Reflexive(role.to_string()))
        }
        ([premise], []) => {
            let (role, source, target) = role(premise)?;
            (source == target).then(|| NamedRoleAxiom::Irreflexive(role.to_string()))
        }
        ([first, second], [conclusion]) => {
            let (first_role, y, x) = role(first)?;
            let (second_role, z, x2) = role(second)?;
            let (left, right) = equality(conclusion)?;
            (first_role == second_role
                && x == x2
                && y == left
                && z == right
                && x != y
                && x != z
                && y != z)
                .then(|| NamedRoleAxiom::InverseFunctional(first_role.to_string()))
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn var(name: &str) -> JTerm {
        JTerm::Var {
            name: name.to_string(),
        }
    }

    fn r(name: &str, source: &str, target: &str) -> JAtom {
        JAtom::Role {
            role: name.to_string(),
            source: var(source),
            target: var(target),
        }
    }

    fn eq(left: &str, right: &str) -> JAtom {
        JAtom::Eq {
            left: var(left),
            right: var(right),
        }
    }

    #[test]
    fn recognizes_every_direct_normalized_role_axiom() {
        let cases = [
            (
                JClause {
                    body: vec![r("R", "x", "y")],
                    head: vec![r("R", "y", "x")],
                },
                NamedRoleAxiom::Symmetric("R".into()),
            ),
            (
                JClause {
                    body: vec![r("R", "x", "y"), r("R", "y", "x")],
                    head: vec![],
                },
                NamedRoleAxiom::Asymmetric("R".into()),
            ),
            (
                JClause {
                    body: vec![],
                    head: vec![r("R", "x", "x")],
                },
                NamedRoleAxiom::Reflexive("R".into()),
            ),
            (
                JClause {
                    body: vec![r("R", "x", "x")],
                    head: vec![],
                },
                NamedRoleAxiom::Irreflexive("R".into()),
            ),
            (
                JClause {
                    body: vec![r("R", "y0", "x"), r("R", "y1", "x")],
                    head: vec![eq("y0", "y1")],
                },
                NamedRoleAxiom::InverseFunctional("R".into()),
            ),
            (
                JClause {
                    body: vec![r("R", "x", "y"), r("S", "x", "y")],
                    head: vec![],
                },
                NamedRoleAxiom::Disjoint("R".into(), "S".into()),
            ),
        ];
        for (clause, expected) in cases {
            assert_eq!(direct_role_axiom(&clause), Some(expected));
        }
    }

    #[test]
    fn rejects_near_misses_instead_of_approximating() {
        let cases = [
            JClause {
                body: vec![r("R", "x", "y")],
                head: vec![r("S", "y", "x")],
            },
            JClause {
                body: vec![r("R", "x", "y"), r("S", "x", "z")],
                head: vec![],
            },
            JClause {
                body: vec![],
                head: vec![r("R", "x", "y")],
            },
            JClause {
                body: vec![r("R", "y0", "x"), r("S", "y1", "x")],
                head: vec![eq("y0", "y1")],
            },
        ];
        for clause in cases {
            assert_eq!(direct_role_axiom(&clause), None);
        }
    }

    #[test]
    fn recognizes_the_actual_normalizer_output() {
        use crate::frontend::{clauses::clause_to_json, iri::IriRegistry, normalise, parse};

        let cases: [(&str, fn(&NamedRoleAxiom) -> bool); 6] = [
            ("SymmetricObjectProperty(<R>)", |value| {
                matches!(value, NamedRoleAxiom::Symmetric(_))
            }),
            ("AsymmetricObjectProperty(<R>)", |value| {
                matches!(value, NamedRoleAxiom::Asymmetric(_))
            }),
            ("ReflexiveObjectProperty(<R>)", |value| {
                matches!(value, NamedRoleAxiom::Reflexive(_))
            }),
            ("IrreflexiveObjectProperty(<R>)", |value| {
                matches!(value, NamedRoleAxiom::Irreflexive(_))
            }),
            ("InverseFunctionalObjectProperty(<R>)", |value| {
                matches!(value, NamedRoleAxiom::InverseFunctional(_))
            }),
            ("DisjointObjectProperties(<R> <S>)", |value| {
                matches!(value, NamedRoleAxiom::Disjoint(_, _))
            }),
        ];
        for (source_axiom, expected) in cases {
            let source = format!("Ontology({source_axiom})");
            let mut registry = IriRegistry::new();
            let ontology = parse::parse_axioms(&mut registry, &source).expect("parse role axiom");
            let (clauses, _, _) = normalise::normalise(&ontology);
            let recovered = clauses
                .iter()
                .map(clause_to_json)
                .filter_map(|clause| direct_role_axiom(&clause))
                .collect::<Vec<_>>();
            assert_eq!(recovered.len(), 1, "{source_axiom}: {recovered:?}");
            assert!(expected(&recovered[0]), "{source_axiom}: {recovered:?}");
        }
    }

    #[test]
    fn nary_disjoint_object_properties_expands_to_every_pair() {
        use crate::frontend::{clauses::clause_to_json, iri::IriRegistry, normalise, parse};

        let mut registry = IriRegistry::new();
        let ontology = parse::parse_axioms(
            &mut registry,
            "Ontology(DisjointObjectProperties(<R> <S> <T>))",
        )
        .expect("parse n-ary disjoint roles");
        let (clauses, _, _) = normalise::normalise(&ontology);
        let recovered = clauses
            .iter()
            .map(clause_to_json)
            .filter_map(|clause| direct_role_axiom(&clause))
            .collect::<Vec<_>>();
        assert_eq!(recovered.len(), 3, "{recovered:?}");
        assert!(recovered
            .iter()
            .all(|axiom| matches!(axiom, NamedRoleAxiom::Disjoint(_, _))));
    }
}
