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
    Nominal {
        concept: String,
        individual: String,
    },
    GuardedAtMost {
        source: String,
        cardinality: usize,
        role: String,
        concept: String,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecoveredSource {
    pub clauses: Vec<NamedSourceClause>,
    pub chains: Vec<NamedRoleChain>,
    pub role_axioms: Vec<NamedRoleAxiom>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecoveryError {
    pub production_index: usize,
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

    if let Some(cardinality) = guarded_at_most(clause) {
        return Some(cardinality);
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

fn guarded_at_most(clause: &JClause) -> Option<NamedSourceClause> {
    let mut edges = Vec::new();
    let mut concepts = Vec::new();
    for atom in &clause.body {
        match atom {
            JAtom::Role {
                role,
                source,
                target,
            } => edges.push((role.as_str(), variable(source)?, variable(target)?)),
            JAtom::Concept { concept, term } => concepts.push((concept.as_str(), variable(term)?)),
            JAtom::Eq { .. } => return None,
        }
    }
    if edges.is_empty() || concepts.len() != edges.len() + 1 {
        return None;
    }
    let role_name = edges[0].0;
    let source_variable = edges[0].1;
    let targets = edges.iter().map(|edge| edge.2).collect::<Vec<_>>();
    if edges.iter().any(|&(role, source, target)| {
        role != role_name || source != source_variable || target == source_variable
    }) {
        return None;
    }
    let mut distinct_targets = std::collections::BTreeSet::new();
    if !targets
        .iter()
        .all(|target| distinct_targets.insert(*target))
    {
        return None;
    }
    let source_concepts = concepts
        .iter()
        .copied()
        .filter(|(_, variable)| *variable == source_variable)
        .map(|(concept, _)| concept)
        .collect::<Vec<_>>();
    if source_concepts.len() != 1 {
        return None;
    }
    let filler_concepts = concepts
        .iter()
        .copied()
        .filter(|(_, variable)| *variable != source_variable)
        .collect::<Vec<_>>();
    if filler_concepts.len() != targets.len() {
        return None;
    }
    let filler = filler_concepts.first()?.0;
    if targets.iter().any(|target| {
        filler_concepts
            .iter()
            .filter(|(concept, variable)| *concept == filler && *variable == *target)
            .count()
            != 1
    }) {
        return None;
    }
    let expected_pairs = targets.len() * (targets.len() - 1) / 2;
    if clause.head.len() != expected_pairs {
        return None;
    }
    let mut expected = std::collections::BTreeSet::new();
    for left in 0..targets.len() {
        for right in (left + 1)..targets.len() {
            expected.insert((targets[left], targets[right]));
        }
    }
    let actual = clause
        .head
        .iter()
        .map(equality)
        .collect::<Option<std::collections::BTreeSet<_>>>()?;
    if actual != expected {
        return None;
    }
    Some(NamedSourceClause::GuardedAtMost {
        source: source_concepts[0].to_string(),
        cardinality: targets.len() - 1,
        role: role_name.to_string(),
        concept: filler.to_string(),
    })
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
    if let ([], [first_result], [second_trigger], [second_result]) = (
        first.body.as_slice(),
        first.head.as_slice(),
        second.body.as_slice(),
        second.head.as_slice(),
    ) {
        if let (
            JAtom::Concept {
                concept,
                term: fact_term,
            },
            JAtom::Concept {
                concept: concept2,
                term: concept_term,
            },
            JAtom::Eq { left, right },
        ) = (first_result, second_trigger, second_result)
        {
            let x = variable(concept_term)?;
            let left_variable = variable(left)?;
            let (right_individual, fact_individual) = match (right, fact_term) {
                (JTerm::Ind { name: right }, JTerm::Ind { name: fact }) => {
                    (right.as_str(), fact.as_str())
                }
                _ => return None,
            };
            if concept == concept2 && x == left_variable && right_individual == fact_individual {
                return Some(NamedSourceClause::Nominal {
                    concept: concept.to_string(),
                    individual: right_individual.to_string(),
                });
            }
        }
    }
    None
}

/// Recover the complete supported typed source from one production clause
/// stream. Every production clause must be consumed exactly once. Multi-clause
/// constructors are consumed atomically and all unsupported or malformed
/// shapes report their first production index.
pub fn recover_source(clauses: &[JClause]) -> Result<RecoveredSource, RecoveryError> {
    let mut recovered = RecoveredSource {
        clauses: Vec::new(),
        chains: Vec::new(),
        role_axioms: Vec::new(),
    };
    let mut index = 0;
    while index < clauses.len() {
        if let Some(next) = clauses.get(index + 1) {
            if let Some(source) = paired_source_clause(&clauses[index], next) {
                recovered.clauses.push(source);
                index += 2;
                continue;
            }
        }
        if let Some(source) = single_source_clause(&clauses[index]) {
            recovered.clauses.push(source);
            index += 1;
            continue;
        }
        if let Some(chain) = role_chain(&clauses[index]) {
            recovered.chains.push(chain);
            index += 1;
            continue;
        }
        if let Some(axiom) = direct_role_axiom(&clauses[index]) {
            recovered.role_axioms.push(axiom);
            index += 1;
            continue;
        }
        return Err(RecoveryError {
            production_index: index,
        });
    }
    Ok(recovered)
}

fn production_term(term: crate::calc::Term) -> serde_json::Value {
    use crate::calc::{COMP_BASE, FTERM_BASE, X, Y};
    if term == X {
        serde_json::json!({"var": {"index": 0}})
    } else if term <= Y {
        serde_json::json!({"var": {"index": i64::from(term) - i64::from(X)}})
    } else if term < FTERM_BASE {
        serde_json::json!({"constant": {"individual": term - X}})
    } else if term < COMP_BASE {
        serde_json::json!({"app": {
            "function": term - FTERM_BASE,
            "argument": {"var": {"index": 0}}
        }})
    } else {
        // Input clauses never contain runtime-composed f(o) terms.
        serde_json::Value::Null
    }
}

fn production_predicate(predicate: crate::calc::Pred) -> serde_json::Value {
    match predicate {
        crate::calc::Pred::Concept { iri, t } => serde_json::json!({"predicate": {
            "predicate": {"concept": {"concept": iri, "term": production_term(t)}}
        }}),
        crate::calc::Pred::Role { iri, s, t } => serde_json::json!({"predicate": {
            "predicate": {"role": {
                "role": iri, "source": production_term(s), "target": production_term(t)
            }}
        }}),
    }
}

fn production_literal(literal: crate::calc::Lit) -> serde_json::Value {
    match literal {
        crate::calc::Lit::P(predicate) => production_predicate(predicate),
        crate::calc::Lit::Eq { s, t } => serde_json::json!({"equality": {
            "left": production_term(s), "right": production_term(t)
        }}),
        crate::calc::Lit::Ineq { s, t } => serde_json::json!({"inequality": {
            "left": production_term(s), "right": production_term(t)
        }}),
    }
}

/// Compile a fully recovered source into the exact version-2 Lean wire. The
/// production parser state comes from `reasoner::Builder` itself, so concept,
/// role, function, individual, variable, ordering, and equality conventions
/// cannot drift from the worker. Unsupported streams fail closed.
pub(crate) fn typed_source_candidate(clauses: &[JClause]) -> Result<serde_json::Value, String> {
    let recovered = recover_source(clauses).map_err(|error| {
        format!(
            "normalized clause {} has no certified typed-source constructor",
            error.production_index
        )
    })?;
    let production = crate::reasoner::cb_production_input(clauses);
    if production.dropped != 0 {
        return Err(format!(
            "production parser dropped {} clauses while compiling the typed source",
            production.dropped
        ));
    }
    let concepts = production
        .concept_names
        .iter()
        .enumerate()
        .map(|(index, name)| (name.as_str(), index))
        .collect::<std::collections::HashMap<_, _>>();
    let roles = production
        .role_names
        .iter()
        .enumerate()
        .map(|(index, name)| (name.as_str(), index))
        .collect::<std::collections::HashMap<_, _>>();
    let concept_id = |name: &str| {
        concepts
            .get(name)
            .copied()
            .ok_or_else(|| format!("recovered source concept {name} was not interned"))
    };
    let role_id = |name: &str| {
        roles
            .get(name)
            .copied()
            .ok_or_else(|| format!("recovered source role {name} was not interned"))
    };
    let individual_id = |name: &str| {
        production
            .individual_ids
            .get(name)
            .copied()
            .and_then(|value| usize::try_from(value).ok())
            .ok_or_else(|| format!("recovered source individual {name} was not interned"))
    };

    let mut source_clauses = Vec::with_capacity(recovered.clauses.len());
    let function_count = production
        .function_ids
        .values()
        .copied()
        .max()
        .and_then(|value| usize::try_from(value).ok())
        .map_or(0, |maximum| maximum + 1);
    let mut allocation = Vec::with_capacity(recovered.clauses.len());
    for (index, clause) in recovered.clauses.iter().enumerate() {
        let (wire, function) = match clause {
            NamedSourceClause::Gci { body, head } => (
                serde_json::json!({"gci": {
                    "body": body.iter().map(|name| concept_id(name)).collect::<Result<Vec<_>, _>>()?,
                    "head": head.iter().map(|name| concept_id(name)).collect::<Result<Vec<_>, _>>()?
                }}),
                None,
            ),
            NamedSourceClause::ExR {
                source,
                role,
                filler,
                function,
            } => (
                serde_json::json!({"exR": {
                    "source": concept_id(source)?, "role": role_id(role)?,
                    "filler": concept_id(filler)?
                }}),
                Some(function.as_str()),
            ),
            NamedSourceClause::AllR {
                source,
                role,
                filler,
            } => (
                serde_json::json!({"allR": {
                    "source": concept_id(source)?, "role": role_id(role)?,
                    "filler": concept_id(filler)?
                }}),
                None,
            ),
            NamedSourceClause::ExL {
                role,
                filler,
                conclusion,
            } => (
                serde_json::json!({"exL": {
                    "role": role_id(role)?, "filler": concept_id(filler)?,
                    "conclusion": concept_id(conclusion)?
                }}),
                None,
            ),
            NamedSourceClause::SubR { sub, sup } => (
                serde_json::json!({"subR": {"sub": role_id(sub)?, "sup": role_id(sup)?}}),
                None,
            ),
            NamedSourceClause::Inverse { role, inverse } => (
                serde_json::json!({"inverse": {
                    "role": role_id(role)?, "inverse": role_id(inverse)?
                }}),
                None,
            ),
            NamedSourceClause::Functional { role } => (
                serde_json::json!({"functional": {"role": role_id(role)?}}),
                None,
            ),
            NamedSourceClause::Nominal {
                concept,
                individual,
            } => (
                serde_json::json!({"nominal": {
                    "concept": concept_id(concept)?, "individual": individual_id(individual)?
                }}),
                None,
            ),
            NamedSourceClause::GuardedAtMost {
                source,
                cardinality,
                role,
                concept,
            } => (
                serde_json::json!({"guardedAtMost": {
                    "source": concept_id(source)?, "cardinality": cardinality,
                    "role": role_id(role)?, "concept": concept_id(concept)?
                }}),
                None,
            ),
        };
        source_clauses.push(wire);
        allocation.push(if let Some(function) = function {
            production
                .function_ids
                .get(function)
                .copied()
                .and_then(|value| usize::try_from(value).ok())
                .ok_or_else(|| format!("existential function {function} was not interned"))?
        } else {
            function_count + index
        });
    }

    let role_chains = recovered
        .chains
        .iter()
        .map(|chain| {
            Ok(serde_json::json!({
                "body": chain.body.iter().map(|name| role_id(name)).collect::<Result<Vec<_>, String>>()?,
                "sup": role_id(&chain.sup)?
            }))
        })
        .collect::<Result<Vec<_>, String>>()?;
    let role_axioms = recovered
        .role_axioms
        .iter()
        .map(|axiom| match axiom {
            NamedRoleAxiom::Symmetric(role) => {
                Ok(serde_json::json!({"symmetric": {"role": role_id(role)?}}))
            }
            NamedRoleAxiom::Asymmetric(role) => {
                Ok(serde_json::json!({"asymmetric": {"role": role_id(role)?}}))
            }
            NamedRoleAxiom::Reflexive(role) => {
                Ok(serde_json::json!({"reflexive": {"role": role_id(role)?}}))
            }
            NamedRoleAxiom::Irreflexive(role) => {
                Ok(serde_json::json!({"irreflexive": {"role": role_id(role)?}}))
            }
            NamedRoleAxiom::InverseFunctional(role) => Ok(serde_json::json!({
                "inverseFunctional": {"role": role_id(role)?}
            })),
            NamedRoleAxiom::Disjoint(left, right) => Ok(serde_json::json!({"disjoint": {
                "left": role_id(left)?, "right": role_id(right)?
            }})),
        })
        .collect::<Result<Vec<_>, String>>()?;
    let ontology = production
        .clauses
        .iter()
        .map(|clause| {
            serde_json::json!({
                "body": clause.body.iter().copied().map(production_predicate).collect::<Vec<_>>(),
                "head": clause.head.iter().copied().map(production_literal).collect::<Vec<_>>()
            })
        })
        .collect::<Vec<_>>();
    let individual_count = production
        .individual_ids
        .values()
        .copied()
        .max()
        .and_then(|value| usize::try_from(value).ok())
        .map_or(1, |maximum| maximum + 1);
    Ok(serde_json::json!({
        "version": 2,
        "concept_count": production.concept_names.len(),
        "role_count": production.role_names.len(),
        "function_count": function_count,
        "individual_count": individual_count,
        "source_clauses": source_clauses,
        "role_chains": role_chains,
        "role_axioms": role_axioms,
        "ontology": ontology,
        "function_allocation": {
            "version": 1,
            "canonical_count": recovered.clauses.len(),
            "production_count": function_count,
            "allocation": allocation
        }
    }))
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

    fn c(name: &str, term: &str) -> JAtom {
        JAtom::Concept {
            concept: name.to_string(),
            term: var(term),
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
    fn recognizes_actual_guarded_max_cardinality_clause() {
        use crate::frontend::{clauses::clause_to_json, iri::IriRegistry, normalise, parse};

        let mut registry = IriRegistry::new();
        let ontology = parse::parse_axioms(
            &mut registry,
            "Ontology(SubClassOf(<A> ObjectMaxCardinality(2 <R> <B>)))",
        )
        .expect("parse guarded maximum cardinality");
        let (clauses, _, _) = normalise::normalise(&ontology);
        let recovered = clauses
            .iter()
            .map(clause_to_json)
            .filter_map(|clause| single_source_clause(&clause))
            .collect::<Vec<_>>();
        assert!(
            recovered.iter().any(|clause| matches!(
                clause,
                NamedSourceClause::GuardedAtMost { cardinality: 2, .. }
            )),
            "normalized={}; recovered={recovered:?}",
            serde_json::to_string(&clauses.iter().map(clause_to_json).collect::<Vec<_>>())
                .expect("serialize guarded maximum cardinality clauses")
        );
    }

    #[test]
    fn guarded_max_cardinality_rejects_incomplete_or_repeated_witness_sets() {
        let body = vec![
            c("A", "x"),
            r("R", "x", "y0"),
            c("B", "y0"),
            r("R", "x", "y1"),
            c("B", "y1"),
            r("R", "x", "y2"),
            c("B", "y2"),
        ];
        let missing_pair = JClause {
            body: body.clone(),
            head: vec![eq("y0", "y1"), eq("y0", "y2")],
        };
        let repeated_target = JClause {
            body: vec![
                c("A", "x"),
                r("R", "x", "y0"),
                c("B", "y0"),
                r("R", "x", "y0"),
                c("B", "y0"),
            ],
            head: vec![eq("y0", "y0")],
        };
        assert_eq!(single_source_clause(&missing_pair), None);
        assert_eq!(single_source_clause(&repeated_target), None);
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

    #[test]
    fn recovers_a_complete_mixed_normalizer_stream() {
        use crate::frontend::{clauses::clause_to_json, iri::IriRegistry, normalise, parse};

        let mut registry = IriRegistry::new();
        let ontology = parse::parse_axioms(
            &mut registry,
            "Ontology(
                SubClassOf(<A> <B>)
                InverseObjectProperties(<R> <S>)
                SubClassOf(<B> ObjectSomeValuesFrom(<R> <C>))
                SubObjectPropertyOf(ObjectPropertyChain(<R> <S>) <T>)
                IrreflexiveObjectProperty(<T>)
            )",
        )
        .expect("parse mixed source");
        let (clauses, _, _) = normalise::normalise(&ontology);
        let clauses = clauses.iter().map(clause_to_json).collect::<Vec<_>>();
        let recovered = recover_source(&clauses).expect("recover every normalized clause");
        assert!(recovered
            .clauses
            .iter()
            .any(|clause| matches!(clause, NamedSourceClause::Gci { .. })));
        assert!(recovered
            .clauses
            .iter()
            .any(|clause| matches!(clause, NamedSourceClause::Inverse { .. })));
        assert!(recovered
            .clauses
            .iter()
            .any(|clause| matches!(clause, NamedSourceClause::ExR { .. })));
        assert_eq!(recovered.chains.len(), 1);
        assert_eq!(recovered.role_axioms.len(), 1);
    }

    #[test]
    fn recovers_production_order_nominal_pair() {
        let individual = JTerm::Ind { name: "i".into() };
        let clauses = vec![
            JClause {
                body: vec![],
                head: vec![JAtom::Concept {
                    concept: "N".into(),
                    term: individual.clone(),
                }],
            },
            JClause {
                body: vec![JAtom::Concept {
                    concept: "N".into(),
                    term: var("x"),
                }],
                head: vec![JAtom::Eq {
                    left: var("x"),
                    right: individual,
                }],
            },
        ];
        assert_eq!(
            recover_source(&clauses).expect("recover nominal").clauses,
            vec![NamedSourceClause::Nominal {
                concept: "N".into(),
                individual: "i".into(),
            }]
        );
    }

    #[test]
    fn complete_recovery_reports_first_uncovered_clause() {
        let clauses = vec![
            JClause {
                body: vec![JAtom::Concept {
                    concept: "A".into(),
                    term: var("x"),
                }],
                head: vec![JAtom::Concept {
                    concept: "B".into(),
                    term: var("x"),
                }],
            },
            JClause {
                body: vec![r("R", "x", "y")],
                head: vec![eq("x", "y"), eq("y", "x")],
            },
        ];
        assert_eq!(
            recover_source(&clauses),
            Err(RecoveryError {
                production_index: 1
            })
        );
    }
}
