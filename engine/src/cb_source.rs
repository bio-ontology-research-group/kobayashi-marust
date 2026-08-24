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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NamedRoleChain {
    pub body: Vec<String>,
    pub sup: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NamedSourceClause {
    Gci {
        body: Vec<String>,
        head: Vec<String>,
    },
    ExR {
        source: String,
        role: String,
        filler: String,
        function: String,
    },
    AllR {
        source: String,
        role: String,
        filler: String,
    },
    ExL {
        role: String,
        filler: String,
        conclusion: String,
    },
    SubR {
        sub: String,
        sup: String,
    },
    Inverse {
        role: String,
        inverse: String,
    },
    Functional {
        role: String,
    },
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

fn concept(atom: &JAtom) -> Option<(&str, &str)> {
    match atom {
        JAtom::Concept { concept, term } => Some((concept, variable(term)?)),
        _ => None,
    }
}

fn unary_function(term: &JTerm) -> Option<(&str, &str)> {
    match term {
        JTerm::Fun { function, arg } => Some((function, variable(arg)?)),
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

/// Recover an exact normalized role-chain clause. The normalizer emits a
/// simple directed path with pairwise distinct path variables and a head edge
/// between the path endpoints. Longer OWL chains are represented by several
/// such binary clauses over fresh roles; each clause is retained exactly.
pub fn role_chain(clause: &JClause) -> Option<NamedRoleChain> {
    let [head] = clause.head.as_slice() else {
        return None;
    };
    let (sup, path_start, path_end) = role(head)?;
    if clause.body.len() < 2 || path_start == path_end {
        return None;
    }
    let mut body = Vec::with_capacity(clause.body.len());
    let mut path_variables = Vec::with_capacity(clause.body.len() + 1);
    for (index, atom) in clause.body.iter().enumerate() {
        let (body_role, source, target) = role(atom)?;
        if index == 0 {
            if source != path_start {
                return None;
            }
            path_variables.push(source);
        } else if path_variables.last().copied() != Some(source) {
            return None;
        }
        path_variables.push(target);
        body.push(body_role.to_string());
    }
    if path_variables.last().copied() != Some(path_end) {
        return None;
    }
    let mut distinct = std::collections::BTreeSet::new();
    if !path_variables
        .iter()
        .all(|variable| distinct.insert(*variable))
    {
        return None;
    }
    Some(NamedRoleChain {
        body,
        sup: sup.to_string(),
    })
}

/// Recover one constructor whose verified encoding is exactly one production
/// clause. Callers must try direct role axioms and role chains first because
/// those constructors intentionally overlap with the broad role-only grammar.
pub fn single_source_clause(clause: &JClause) -> Option<NamedSourceClause> {
    if direct_role_axiom(clause).is_some() || role_chain(clause).is_some() {
        return None;
    }

    if clause.body.iter().all(|atom| concept(atom).is_some())
        && clause.head.iter().all(|atom| concept(atom).is_some())
    {
        let mut common_variable = None;
        let mut body = Vec::with_capacity(clause.body.len());
        let mut head = Vec::with_capacity(clause.head.len());
        for (target, atom) in [(&mut body, &clause.body), (&mut head, &clause.head)] {
            for item in atom {
                let (name, variable) = concept(item)?;
                if let Some(common) = common_variable {
                    if common != variable {
                        return None;
                    }
                } else {
                    common_variable = Some(variable);
                }
                target.push(name.to_string());
            }
        }
        return Some(NamedSourceClause::Gci { body, head });
    }

    match (clause.body.as_slice(), clause.head.as_slice()) {
        ([trigger, edge], [result]) => {
            if let (
                Some((trigger_concept, trigger_variable)),
                Some((role_name, edge_source, edge_target)),
                Some((result_concept, result_variable)),
            ) = (concept(trigger), role(edge), concept(result))
            {
                if trigger_variable == edge_source
                    && edge_target == result_variable
                    && edge_source != edge_target
                {
                    return Some(NamedSourceClause::AllR {
                        source: trigger_concept.to_string(),
                        role: role_name.to_string(),
                        filler: result_concept.to_string(),
                    });
                }
                if trigger_variable == edge_target
                    && edge_source == result_variable
                    && edge_source != edge_target
                {
                    return Some(NamedSourceClause::ExL {
                        role: role_name.to_string(),
                        filler: trigger_concept.to_string(),
                        conclusion: result_concept.to_string(),
                    });
                }
                return None;
            }
            if let (Some((first_role, x, y)), Some((second_role, x2, z)), Some((left, right))) =
                (role(trigger), role(edge), equality(result))
            {
                return (first_role == second_role
                    && x == x2
                    && y == left
                    && z == right
                    && x != y
                    && x != z
                    && y != z)
                    .then(|| NamedSourceClause::Functional {
                        role: first_role.to_string(),
                    });
            }
            None
        }
        ([premise], [conclusion]) => {
            let (sub, x, y) = role(premise)?;
            let (sup, x2, y2) = role(conclusion)?;
            (x == x2 && y == y2 && x != y).then(|| NamedSourceClause::SubR {
                sub: sub.to_string(),
                sup: sup.to_string(),
            })
        }
        _ => None,
    }
}

/// Recover a normalized constructor represented by exactly two adjacent
/// production clauses. Clause order and term spelling are checked exactly;
/// swapping either member therefore fails closed.
pub fn paired_source_clause(first: &JClause, second: &JClause) -> Option<NamedSourceClause> {
    if let ([first_trigger], [first_result], [second_trigger], [second_result]) = (
        first.body.as_slice(),
        first.head.as_slice(),
        second.body.as_slice(),
        second.head.as_slice(),
    ) {
        if let (
            Some((source, x)),
            JAtom::Role {
                role: role_name,
                source: role_source,
                target: role_target,
            },
            Some((source2, x2)),
            JAtom::Concept {
                concept: filler,
                term: filler_target,
            },
        ) = (
            concept(first_trigger),
            first_result,
            concept(second_trigger),
            second_result,
        ) {
            let role_source = variable(role_source)?;
            let (function, function_arg) = unary_function(role_target)?;
            let (filler_function, filler_arg) = unary_function(filler_target)?;
            if source == source2
                && x == x2
                && x == role_source
                && function == filler_function
                && function_arg == x
                && filler_arg == x
            {
                return Some(NamedSourceClause::ExR {
                    source: source.to_string(),
                    role: role_name.to_string(),
                    filler: filler.to_string(),
                    function: function.to_string(),
                });
            }
        }

        if let (
            Some((role_name, x, y)),
            Some((inverse, y2, x2)),
            Some((inverse2, x3, y3)),
            Some((role2, y4, x4)),
        ) = (
            role(first_trigger),
            role(first_result),
            role(second_trigger),
            role(second_result),
        ) {
            if role_name == role2
                && inverse == inverse2
                && x == x2
                && y == y2
                && x == x3
                && y == y3
                && x == x4
                && y == y4
                && x != y
            {
                return Some(NamedSourceClause::Inverse {
                    role: role_name.to_string(),
                    inverse: inverse.to_string(),
                });
            }
        }
    }
    None
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

    #[test]
    fn recognizes_role_chain_and_transitivity_normalizer_output() {
        use crate::frontend::{clauses::clause_to_json, iri::IriRegistry, normalise, parse};

        for (source_axiom, expected_chains) in [
            ("TransitiveObjectProperty(<R>)", 1),
            ("SubObjectPropertyOf(ObjectPropertyChain(<R> <S>) <T>)", 1),
            (
                "SubObjectPropertyOf(ObjectPropertyChain(<R> <S> <T> <U>) <V>)",
                3,
            ),
        ] {
            let mut registry = IriRegistry::new();
            let source = format!("Ontology({source_axiom})");
            let ontology = parse::parse_axioms(&mut registry, &source).expect("parse role chain");
            let (clauses, _, _) = normalise::normalise(&ontology);
            let recovered = clauses
                .iter()
                .map(clause_to_json)
                .filter_map(|clause| role_chain(&clause))
                .collect::<Vec<_>>();
            assert_eq!(recovered.len(), expected_chains, "{source_axiom}");
            assert!(recovered.iter().all(|chain| chain.body.len() == 2));
        }
    }

    #[test]
    fn role_chain_rejects_broken_paths_and_non_role_atoms() {
        let concept = JAtom::Concept {
            concept: "C".into(),
            term: var("x"),
        };
        let cases = [
            JClause {
                body: vec![r("R", "x", "y"), r("S", "z", "w")],
                head: vec![r("T", "x", "w")],
            },
            JClause {
                body: vec![r("R", "x", "y"), r("S", "y", "z")],
                head: vec![r("T", "q", "z")],
            },
            JClause {
                body: vec![r("R", "x", "y"), concept],
                head: vec![r("T", "x", "y")],
            },
            JClause {
                body: vec![r("R", "x", "y"), r("S", "y", "x")],
                head: vec![r("T", "x", "x")],
            },
        ];
        for clause in cases {
            assert_eq!(role_chain(&clause), None);
        }
    }

    #[test]
    fn recognizes_actual_single_clause_source_constructors() {
        use crate::frontend::{clauses::clause_to_json, iri::IriRegistry, normalise, parse};

        let cases: [(&str, fn(&NamedSourceClause) -> bool); 5] = [
            ("SubClassOf(<A> <B>)", |value| {
                matches!(value, NamedSourceClause::Gci { .. })
            }),
            ("SubClassOf(<A> ObjectAllValuesFrom(<R> <B>))", |value| {
                matches!(value, NamedSourceClause::AllR { .. })
            }),
            ("SubClassOf(ObjectSomeValuesFrom(<R> <A>) <B>)", |value| {
                matches!(value, NamedSourceClause::ExL { .. })
            }),
            ("SubObjectPropertyOf(<R> <S>)", |value| {
                matches!(value, NamedSourceClause::SubR { .. })
            }),
            ("FunctionalObjectProperty(<R>)", |value| {
                matches!(value, NamedSourceClause::Functional { .. })
            }),
        ];
        for (source_axiom, expected) in cases {
            let mut registry = IriRegistry::new();
            let source = format!("Ontology({source_axiom})");
            let ontology =
                parse::parse_axioms(&mut registry, &source).expect("parse source clause");
            let (clauses, _, _) = normalise::normalise(&ontology);
            let recovered = clauses
                .iter()
                .map(clause_to_json)
                .filter_map(|clause| single_source_clause(&clause))
                .collect::<Vec<_>>();
            assert!(
                recovered.iter().any(expected),
                "{source_axiom}: {recovered:?}; normalized={}",
                serde_json::to_string(&clauses.iter().map(clause_to_json).collect::<Vec<_>>())
                    .expect("serialize normalized clauses")
            );
        }
    }

    #[test]
    fn single_clause_recovery_rejects_variable_and_role_mismatches() {
        let cases = [
            JClause {
                body: vec![JAtom::Concept {
                    concept: "A".into(),
                    term: var("x"),
                }],
                head: vec![JAtom::Concept {
                    concept: "B".into(),
                    term: var("y"),
                }],
            },
            JClause {
                body: vec![
                    JAtom::Concept {
                        concept: "A".into(),
                        term: var("x"),
                    },
                    r("R", "z", "y"),
                ],
                head: vec![JAtom::Concept {
                    concept: "B".into(),
                    term: var("y"),
                }],
            },
            JClause {
                body: vec![r("R", "x", "y"), r("S", "x", "z")],
                head: vec![eq("y", "z")],
            },
        ];
        for clause in cases {
            assert_eq!(single_source_clause(&clause), None);
        }
    }

    #[test]
    fn recognizes_actual_paired_source_constructors() {
        use crate::frontend::{clauses::clause_to_json, iri::IriRegistry, normalise, parse};

        for (source_axiom, expected) in [
            ("SubClassOf(<A> ObjectSomeValuesFrom(<R> <B>))", "exR"),
            ("InverseObjectProperties(<R> <S>)", "inverse"),
        ] {
            let mut registry = IriRegistry::new();
            let source = format!("Ontology({source_axiom})");
            let ontology = parse::parse_axioms(&mut registry, &source).expect("parse paired axiom");
            let (clauses, _, _) = normalise::normalise(&ontology);
            let clauses = clauses.iter().map(clause_to_json).collect::<Vec<_>>();
            let recovered = clauses
                .windows(2)
                .filter_map(|pair| paired_source_clause(&pair[0], &pair[1]))
                .collect::<Vec<_>>();
            assert!(
                recovered.iter().any(|clause| matches!(
                    (expected, clause),
                    ("exR", NamedSourceClause::ExR { .. })
                        | ("inverse", NamedSourceClause::Inverse { .. })
                )),
                "{source_axiom}: {}",
                serde_json::to_string(&clauses).expect("serialize paired clauses")
            );
        }
    }

    #[test]
    fn paired_source_rejects_crossed_existential_witnesses() {
        let trigger = JAtom::Concept {
            concept: "A".into(),
            term: var("x"),
        };
        let fun = |name: &str| JTerm::Fun {
            function: name.into(),
            arg: Box::new(var("x")),
        };
        let first = JClause {
            body: vec![trigger.clone()],
            head: vec![JAtom::Role {
                role: "R".into(),
                source: var("x"),
                target: fun("f"),
            }],
        };
        let second = JClause {
            body: vec![trigger],
            head: vec![JAtom::Concept {
                concept: "B".into(),
                term: fun("g"),
            }],
        };
        assert_eq!(paired_source_clause(&first, &second), None);
    }
}
