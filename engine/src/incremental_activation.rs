//! Conservative predicate activation for positive Horn incremental inputs.
//! Roles, equality, and term identities are forgotten (treated as available).
//! A clause can add a concept only after every concept premise is available.
//! The union of both revisions overapproximates both executions. A query whose
//! closure cannot activate any changed clause keeps the same relevant theory.

use std::collections::{BTreeSet, HashMap, VecDeque};
use crate::json_io::{JAtom, JClause};

/// Returns None when the bounded analysis should use the established fallback.
/// Callers must account for all typed initial facts and enforce the source
/// fragment boundary; this function alone does not authorize taxonomy reuse.
pub(crate) fn affected(
    old: &[JClause], new: &[JClause], changed: &[JClause],
    queries: &[String], global: &[String],
) -> Option<BTreeSet<String>> {
    if old.len().saturating_add(new.len()) > 500_000
        || old.iter().chain(new).any(|c| c.head.len() > 1) {
        return None;
    }
    let mut ids = HashMap::<&str, usize>::new();
    for atom in old.iter().chain(new).chain(changed).flat_map(|c| c.body.iter().chain(&c.head)) {
        if let JAtom::Concept { concept, .. } = atom {
            let next = ids.len(); ids.entry(concept.as_str()).or_insert(next);
        }
    }
    for name in queries.iter().chain(global) {
        let next = ids.len(); ids.entry(name.as_str()).or_insert(next);
    }
    let words = queries.len().div_ceil(64);
    if ids.len().checked_mul(words)?.checked_mul(8)? > 64 * 1024 * 1024 { return None; }
    let concepts = |atoms: &[JAtom]| -> Vec<usize> {
        atoms.iter().filter_map(|a| match a {
            JAtom::Concept { concept, .. } => Some(ids[concept.as_str()]), _ => None,
        }).collect::<BTreeSet<_>>().into_iter().collect()
    };
    let rules: Vec<_> = old.iter().chain(new)
        .map(|c| (concepts(&c.body), concepts(&c.head))).collect();
    let mut users = vec![Vec::new(); ids.len()];
    for (index, (body, _)) in rules.iter().enumerate() {
        for &id in body { users[id].push(index); }
    }
    let mut values = vec![vec![0u64; words]; ids.len()];
    for (index, name) in queries.iter().enumerate() {
        values[ids[name.as_str()]][index / 64] |= 1 << (index % 64);
    }
    for (&name, &id) in &ids {
        if matches!(name, "owl:Thing" | "http://www.w3.org/2002/07/owl#Thing" | "⊤") {
            values[id].fill(u64::MAX);
        }
    }
    for name in global { values[ids[name.as_str()]].fill(u64::MAX); }
    let mut queue: VecDeque<_> = (0..rules.len()).collect();
    let mut queued = vec![true; rules.len()];
    let mut mask = vec![0u64; words];
    while let Some(index) = queue.pop_front() {
        queued[index] = false;
        let (body, head) = &rules[index];
        if head.is_empty() { continue; }
        mask.fill(u64::MAX);
        for &id in body {
            for (word, premise) in mask.iter_mut().zip(&values[id]) { *word &= premise; }
        }
        for &id in head {
            let mut grew = false;
            for (word, add) in values[id].iter_mut().zip(&mask) {
                let next = *word | add; grew |= next != *word; *word = next;
            }
            if grew {
                for &dependent in &users[id] {
                    if !queued[dependent] { queued[dependent] = true; queue.push_back(dependent); }
                }
            }
        }
    }
    let mut affected = vec![0u64; words];
    for clause in changed {
        mask.fill(u64::MAX);
        for id in concepts(&clause.body) {
            for (word, premise) in mask.iter_mut().zip(&values[id]) { *word &= premise; }
        }
        for (word, add) in affected.iter_mut().zip(&mask) { *word |= add; }
    }
    Some(queries.iter().enumerate().filter(|(i, _)| affected[i / 64] & (1 << (i % 64)) != 0)
        .map(|(_, name)| name.clone()).collect())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::json_io::JTerm;
    fn clause(body: &[usize], head: &[usize]) -> JClause {
        let atoms = |xs: &[usize]| xs.iter().map(|i| JAtom::Concept {
            concept: format!("C{i}"), term: JTerm::Var { name: "x".into() },
        }).collect();
        JClause { body: atoms(body), head: atoms(head) }
    }
    fn theory(clauses: &[JClause], q: usize) -> (bool, Vec<bool>) {
        let models: Vec<_> = (0usize..16).filter(|bits| {
            let holds = |atom: &JAtom| match atom {
                JAtom::Concept { concept, .. } => bits & (1 << concept[1..].parse::<usize>().unwrap()) != 0,
                _ => unreachable!(),
            };
            bits & (1 << q) != 0 && clauses.iter().all(|c|
                !c.body.iter().all(&holds) || c.head.iter().any(&holds))
        }).collect();
        (!models.is_empty(), (0..4).map(|c| models.iter().all(|bits| bits & (1 << c) != 0)).collect())
    }
    #[test]
    fn unchanged_queries_preserve_all_entailments_in_exhaustive_horn_models() {
        let palette = [clause(&[], &[0]), clause(&[0], &[1]), clause(&[1], &[2]),
            clause(&[0, 2], &[3]), clause(&[3], &[0]), clause(&[1, 3], &[]),
            clause(&[2], &[1]), clause(&[2, 3], &[0])];
        let queries: Vec<_> = (0..4).map(|i| format!("C{i}")).collect();
        for mask in 0usize..256 {
            let old: Vec<_> = palette.iter().enumerate().filter(|(i, _)| mask & (1 << i) != 0)
                .map(|(_, c)| c.clone()).collect();
            for changed in 0..8 {
                let next = mask ^ (1 << changed);
                let new: Vec<_> = palette.iter().enumerate().filter(|(i, _)| next & (1 << i) != 0)
                    .map(|(_, c)| c.clone()).collect();
                let impacted = affected(&old, &new, &[palette[changed].clone()], &queries, &[]).unwrap();
                for q in 0..4 {
                    if !impacted.contains(&queries[q]) {
                        assert_eq!(theory(&old, q), theory(&new, q), "mask={mask} change={changed} q={q}");
                    }
                }
            }
        }
    }
    #[test]
    fn activation_crosses_word_boundaries_without_marking_other_queries() {
        let queries: Vec<_> = (0..130).map(|i| format!("C{i}")).collect();
        let old = vec![clause(&[63], &[64]), clause(&[64], &[129])];
        let delta = clause(&[129], &[]);
        let mut new = old.clone(); new.push(delta.clone());
        assert_eq!(affected(&old, &new, &[delta], &queries, &[]).unwrap(),
            BTreeSet::from(["C63".into(), "C64".into(), "C129".into()]));
    }

    #[test]
    fn conjunction_does_not_connect_unrelated_queries_and_global_seeds_are_respected() {
        let old = vec![clause(&[0], &[1]), clause(&[1, 2], &[3])];
        let delta = clause(&[3], &[]); let mut new = old.clone(); new.push(delta.clone());
        let queries = vec!["C0".into(), "C3".into()];
        assert_eq!(affected(&old, &new, &[delta.clone()], &queries, &[]).unwrap(), BTreeSet::from(["C3".into()]));
        assert_eq!(affected(&old, &new, &[delta], &queries, &["C2".into()]).unwrap(), queries.into_iter().collect());
    }
}
