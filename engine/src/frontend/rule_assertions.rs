//! Sound positive ABox consequences. This is an optimization, not a replacement
//! for rule-aware query reasoning: all original rules and axioms stay present.
use super::syntax::{Axiom, Concept, Ontology, RuleAtom, RuleTerm};
use std::collections::{HashMap, HashSet};

fn compatible(term: &RuleTerm, value: &str, binding: &HashMap<String, String>) -> bool {
    match term {
        RuleTerm::Ind(name) => name == value,
        RuleTerm::Var(name) => binding.get(name).is_none_or(|bound| bound == value),
    }
}

fn bind(term: &RuleTerm, value: &str, binding: &mut HashMap<String, String>) -> bool {
    match term {
        RuleTerm::Ind(name) => name == value,
        RuleTerm::Var(name) => match binding.get(name) {
            Some(bound) => bound == value,
            None => { binding.insert(name.clone(), value.to_owned()); true }
        },
    }
}
fn value(term: &RuleTerm, binding: &HashMap<String, String>) -> Option<String> {
    match term {
        RuleTerm::Ind(name) => Some(name.clone()),
        RuleTerm::Var(name) => binding.get(name).cloned(),
    }
}

pub(super) fn materialize(ontology: &mut Ontology) -> usize {
    let mut concepts = HashSet::new();
    let mut roles = HashSet::new();
    let mut inclusions = Vec::new();
    let mut rules = Vec::new();
    let v = |index: usize| RuleTerm::Var(format!("__closure_{index}"));
    let edge = |role: &str, left: usize, right: usize|
        RuleAtom::Role(role.to_owned(), v(left), v(right));
    for axiom in ontology.tbox().chain(ontology.rbox()).chain(ontology.abox()).chain(ontology.rules()) {
        match axiom {
            Axiom::ConceptAssertion(c, a) => { concepts.insert((c.clone(), a.clone())); }
            Axiom::RoleAssertion(r, a, b) => { roles.insert((r.clone(), a.clone(), b.clone())); }
            Axiom::SubClassOf(a, b) => inclusions.push((a.clone(), b.clone())),
            Axiom::EquivalentClasses(a, b) => {
                inclusions.push((a.clone(), b.clone()));
                inclusions.push((b.clone(), a.clone()));
            }
            Axiom::RoleInclusion(left, right) => {
                rules.push((vec![edge(left, 0, 1)], vec![edge(right, 0, 1)]));
            }
            Axiom::InverseRoles(left, right) => {
                rules.push((vec![edge(left, 0, 1)], vec![edge(right, 1, 0)]));
                rules.push((vec![edge(right, 0, 1)], vec![edge(left, 1, 0)]));
            }
            Axiom::SymmetricRole(role) => {
                rules.push((vec![edge(role, 0, 1)], vec![edge(role, 1, 0)]));
            }
            Axiom::TransitiveRole(role) => {
                rules.push((vec![edge(role, 0, 1), edge(role, 1, 2)], vec![edge(role, 0, 2)]));
            }
            Axiom::RoleChain(body, head) if !body.is_empty() => {
                rules.push((body.iter().enumerate().map(|(i, role)| edge(role, i, i + 1)).collect(),
                    vec![edge(head, 0, body.len())]));
            }
            Axiom::Rule(body, head) if body.iter().chain(head).all(|atom|
                matches!(atom, RuleAtom::Class(_, _) | RuleAtom::Role(_, _, _))) => {
                rules.push((body.clone(), head.clone()));
            }
            _ => {}
        }
    }
    let initial_concepts = concepts.clone();
    let initial_roles = roles.clone();
    loop {
        let previous = concepts.len() + roles.len();
        // Exact asserted expressions imply their inclusions. No negation by
        // absence, datatype coercion, unique-name assumption, or model guessing.
        let snapshot: Vec<_> = concepts.iter().cloned().collect();
        for (concept, individual) in snapshot {
            if let Concept::And(parts) = &concept {
                for part in parts { concepts.insert((part.clone(), individual.clone())); }
            }
            for (left, right) in &inclusions {
                if &concept == left { concepts.insert((right.clone(), individual.clone())); }
            }
        }
        // Snapshot indexes: conclusions from this round become premises in the
        // next round. This changes scheduling only; the monotone fixpoint is
        // unchanged when the optional resource bound does not stop expansion.
        // Indexing avoids scanning unrelated predicates per binding.
        let mut concept_index: HashMap<Concept, Vec<String>> = HashMap::new();
        for (concept, individual) in &concepts {
            concept_index.entry(concept.clone()).or_default().push(individual.clone());
        }
        let mut role_index: HashMap<String, Vec<(String, String)>> = HashMap::new();
        for (role, left, right) in &roles {
            role_index.entry(role.clone()).or_default().push((left.clone(), right.clone()));
        }
        for (body, head) in &rules {
            let mut remaining: Vec<_> = body.iter().collect();
            let mut ordered = Vec::with_capacity(body.len());
            let mut bound = HashSet::new();
            while !remaining.is_empty() {
                let is_bound = |term: &RuleTerm| match term {
                    RuleTerm::Ind(_) => true,
                    RuleTerm::Var(name) => bound.contains(name),
                };
                let best = remaining.iter().enumerate().min_by_key(|(_, atom)| match atom {
                    RuleAtom::Class(c, term) => {
                        let count = concept_index.get(c).map_or(0, Vec::len);
                        if is_bound(term) { count.min(1) } else { count }
                    }
                    RuleAtom::Role(r, left, right) => {
                        let count = role_index.get(r).map_or(0, Vec::len);
                        match (is_bound(left), is_bound(right)) {
                            (true, true) => count.min(1),
                            (true, false) | (false, true) => count.min(4),
                            (false, false) => count,
                        }
                    }
                    _ => unreachable!("screened complete positive rule"),
                }).unwrap().0;
                let atom = remaining.remove(best);
                let mut mark = |term: &RuleTerm| {
                    if let RuleTerm::Var(name) = term { bound.insert(name.clone()); }
                };
                match atom {
                    RuleAtom::Class(_, term) => mark(term),
                    RuleAtom::Role(_, left, right) => { mark(left); mark(right); }
                    _ => unreachable!("screened complete positive rule"),
                }
                ordered.push(atom);
            }
            let mut bindings = vec![HashMap::new()];
            for atom in ordered {
                let mut next = Vec::new();
                for binding in &bindings {
                    match atom {
                        RuleAtom::Class(wanted, term) => {
                            for individual in concept_index.get(wanted).into_iter().flatten() {
                                if !compatible(term, individual, binding) { continue; }
                                let mut candidate = binding.clone();
                                if bind(term, individual, &mut candidate) { next.push(candidate); }
                            }
                        }
                        RuleAtom::Role(wanted, left, right) => {
                            for (a, b) in role_index.get(wanted).into_iter().flatten() {
                                if !compatible(left, a, binding) || !compatible(right, b, binding) { continue; }
                                let mut candidate = binding.clone();
                                if bind(left, a, &mut candidate) && bind(right, b, &mut candidate) {
                                    next.push(candidate);
                                }
                            }
                        }
                        _ => unreachable!("screened complete rule"),
                    }
                }
                // Resource bound limits only optional consequences; original
                // rules remain authoritative and are never counted as handled.
                if next.len() > 100_000 { next.clear(); }
                bindings = next;
                if bindings.is_empty() { break; }
            }
            for binding in &bindings {
                for atom in head {
                    match atom {
                        RuleAtom::Class(c, term) => {
                            if let Some(a) = value(term, binding) { concepts.insert((c.clone(), a)); }
                        }
                        RuleAtom::Role(r, left, right) => {
                            if let (Some(a), Some(b)) = (value(left, binding), value(right, binding)) {
                                roles.insert((r.clone(), a, b));
                            }
                        }
                        _ => unreachable!("screened complete rule"),
                    }
                }
            }
        }
        if concepts.len() + roles.len() == previous || concepts.len() + roles.len() > 100_000 { break; }
    }
    let mut conclusions: Vec<_> = concepts.difference(&initial_concepts).cloned().collect();
    conclusions.sort();
    let mut edges: Vec<_> = roles.difference(&initial_roles).cloned().collect();
    edges.sort();
    let count = conclusions.len() + edges.len();
    for (c, a) in conclusions { ontology.add(Axiom::ConceptAssertion(c, a)); }
    for (r, a, b) in edges { ontology.add(Axiom::RoleAssertion(r, a, b)); }
    count
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn repeated_role_variables_require_one_shared_binding() {
        let mut registry = super::super::iri::IriRegistry::new();
        let mut ontology = super::super::parse::parse_axioms(&mut registry, r#"Ontology(
            ObjectPropertyAssertion(<r> <a> <b>)
            ObjectPropertyAssertion(<r> <c> <c>)
            DLSafeRule(Body(ObjectPropertyAtom(<r> Variable(<x>) Variable(<x>))) Head(ClassAtom(<Self> Variable(<x>))))
        )"#).unwrap();
        assert_eq!(materialize(&mut ontology), 1);
        assert!(ontology.abox().any(|a| matches!(a, Axiom::ConceptAssertion(Concept::Name(c), i) if c == "Self" && i == "c")));
        assert!(!ontology.abox().any(|a| matches!(a, Axiom::ConceptAssertion(Concept::Name(c), i) if c == "Self" && (i == "a" || i == "b"))));
    }
    #[test]
    fn rule_premises_include_inferred_inverse_chain_and_transitive_edges() {
        let mut registry = super::super::iri::IriRegistry::new();
        let mut ontology = super::super::parse::parse_axioms(&mut registry, r#"Ontology(
            ObjectPropertyAssertion(<r> <b> <a>)
            ObjectPropertyAssertion(<s> <b> <c>)
            ObjectPropertyAssertion(<t> <c> <d>)
            InverseObjectProperties(<r> <ri>)
            SubObjectPropertyOf(ObjectPropertyChain(<ri> <s>) <t>)
            TransitiveObjectProperty(<t>)
            DLSafeRule(Body(ObjectPropertyAtom(<t> <a> Variable(<y>))) Head(ClassAtom(<Good> Variable(<y>))))
        )"#).unwrap();
        materialize(&mut ontology);
        assert!(ontology.abox().any(|a| matches!(a, Axiom::ConceptAssertion(Concept::Name(c), i) if c == "Good" && i == "d")));
        assert!(ontology.abox().any(|a| matches!(a, Axiom::RoleAssertion(r, a, b) if r == "t" && a == "a" && b == "d")));
        assert_eq!(ontology.rules().count(), 1);
        assert_eq!(ontology.rbox().count(), 3);
    }
    #[test]
    fn closure_preserves_rules_and_requires_every_positive_premise() {
        let mut registry = super::super::iri::IriRegistry::new();
        let mut ontology = super::super::parse::parse_axioms(&mut registry, r#"Ontology(
            ClassAssertion(<P> <a>) ObjectPropertyAssertion(<r> <a> <b>)
            EquivalentClasses(<P> <Q>)
            DLSafeRule(Body(ClassAtom(<Q> Variable(<x>)) ObjectPropertyAtom(<r> Variable(<x>) Variable(<y>))) Head(ClassAtom(<Good> Variable(<y>))))
            DLSafeRule(Body(ClassAtom(<Missing> Variable(<x>))) Head(ClassAtom(<Bad> Variable(<x>))))
        )"#).unwrap();
        let original_rules = ontology.rules().count();
        assert_eq!(materialize(&mut ontology), 2);
        assert_eq!(ontology.rules().count(), original_rules);
        assert!(ontology.abox().any(|a| matches!(a, Axiom::ConceptAssertion(Concept::Name(c), i) if c == "Good" && i == "b")));
        assert!(!ontology.abox().any(|a| matches!(a, Axiom::ConceptAssertion(Concept::Name(c), _) if c == "Bad")));
        assert_eq!(materialize(&mut ontology), 0);
    }
}
