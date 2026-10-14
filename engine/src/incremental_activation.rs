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

/// Source-expression abstraction for the locality theorem. Typed side-state
/// identity and complete source coverage must be established by the caller.
pub(crate) fn source_affected(
    old: &[crate::json_io::SourceAxiomMeta], new: &[crate::json_io::SourceAxiomMeta],
    queries: &[String], global: &[String],
) -> Option<BTreeSet<String>> {
    use crate::frontend::syntax::Concept;
    use crate::json_io::SourceAxiomKind;
    struct Lowering {
        ids: HashMap<Concept, usize>,
        structural: Vec<(Vec<usize>, usize)>,
    }
    fn clause(body: &[usize], head: usize) -> (Vec<usize>, usize) {
        (body.to_vec(), head)
    }
    impl Lowering {
        fn expression(&mut self, expression: &Concept, depth: usize) -> Option<usize> {
            if depth > 64 || self.ids.len() >= 100_000 { return None; }
            if let Some(id) = self.ids.get(expression) { return Some(*id); }
            let id = self.ids.len();
            self.ids.insert(expression.clone(), id);
            match expression {
                Concept::Name(_) | Concept::Bottom => {},
                Concept::Top => self.structural.push(clause(&[], id)),
                Concept::And(children) => {
                    let children = children.iter().map(|child| self.expression(child, depth + 1))
                        .collect::<Option<Vec<_>>>()?;
                    self.structural.push(clause(&children, id));
                    for child in children { self.structural.push(clause(&[id], child)); }
                },
                Concept::Exists(_, filler) => {
                    let child = self.expression(filler, depth + 1)?;
                    // All roles remain fixed in the locality model transfer.
                    // Forgetting their availability conservatively activates
                    // an existential whenever its filler is active.
                    self.structural.push(clause(&[id], child));
                    self.structural.push(clause(&[child], id));
                },
                _ => return None,
            }
            Some(id)
        }
    }
    if old.len().saturating_add(new.len()) > 100_000 { return None; }
    let mut lower = Lowering { ids: HashMap::new(), structural: Vec::new() };
    let mut snapshots = Vec::new();
    for axioms in [old, new] {
        let mut rules = BTreeSet::new();
        for axiom in axioms {
            let a = lower.expression(&axiom.left, 0)?;
            let b = lower.expression(&axiom.right, 0)?;
            match axiom.kind {
                SourceAxiomKind::SubClass => { rules.insert((vec![a], b)); },
                SourceAxiomKind::Equivalent => {
                    rules.insert((vec![a], b)); rules.insert((vec![b], a));
                },
                SourceAxiomKind::Disjoint => {
                    let bottom = lower.expression(&Concept::Bottom, 0)?;
                    let mut body = vec![a,b]; body.sort_unstable(); body.dedup();
                    rules.insert((body, bottom));
                },
            }
        }
        snapshots.push(rules);
    }
    let query_ids = queries.iter().map(|name| lower.expression(&Concept::Name(name.clone()), 0))
        .collect::<Option<Vec<_>>>()?;
    let global_ids = global.iter().map(|name| lower.expression(&Concept::Name(name.clone()), 0))
        .collect::<Option<Vec<_>>>()?;
    let changed: Vec<_> = snapshots[0].symmetric_difference(&snapshots[1]).cloned().collect();
    // Preserve the same union abstraction and symmetric source-rule difference
    // as the clause-based implementation, without string or JSON atom materialization.
    let mut rules = lower.structural;
    rules.extend(snapshots.into_iter().flatten());
    let words = queries.len().div_ceil(64);
    if rules.len() > 500_000
        || lower.ids.len().checked_mul(words)?.checked_mul(8)? > 64 * 1024 * 1024 {
        return None;
    }
    let mut users = vec![Vec::new(); lower.ids.len()];
    for (index, (body, _)) in rules.iter().enumerate() {
        for &id in body { users[id].push(index); }
    }
    let mut values = vec![vec![0u64; words]; lower.ids.len()];
    for (index, id) in query_ids.into_iter().enumerate() {
        values[id][index / 64] |= 1 << (index % 64);
    }
    for id in global_ids { values[id].fill(u64::MAX); }
    let mut queue: VecDeque<_> = (0..rules.len()).collect();
    let mut queued = vec![true; rules.len()];
    let mut mask = vec![0u64; words];
    while let Some(index) = queue.pop_front() {
        queued[index] = false;
        let (body, head) = &rules[index];
        mask.fill(u64::MAX);
        for &id in body {
            for (word, premise) in mask.iter_mut().zip(&values[id]) { *word &= premise; }
        }
        let mut grew = false;
        for (word, add) in values[*head].iter_mut().zip(&mask) {
            let next = *word | add; grew |= next != *word; *word = next;
        }
        if grew { for &dependent in &users[*head] {
            if !queued[dependent] { queued[dependent] = true; queue.push_back(dependent); }
        }}
    }
    let mut changed_queries = vec![0u64; words];
    for (body, _) in changed {
        mask.fill(u64::MAX);
        for id in body {
            for (word, premise) in mask.iter_mut().zip(&values[id]) { *word &= premise; }
        }
        for (word, add) in changed_queries.iter_mut().zip(&mask) { *word |= add; }
    }
    Some(queries.iter().enumerate()
        .filter(|(i, _)| changed_queries[i / 64] & (1 << (i % 64)) != 0)
        .map(|(_, name)| name.clone()).collect())
}

#[cfg(test)]
fn legacy_source_affected(
    old: &[crate::json_io::SourceAxiomMeta], new: &[crate::json_io::SourceAxiomMeta],
    queries: &[String], global: &[String],
) -> Option<BTreeSet<String>> {
    use crate::frontend::syntax::Concept;
    use crate::json_io::{JTerm, SourceAxiomKind};
    struct Lowering {
        ids: HashMap<Concept, usize>,
        structural: Vec<JClause>,
    }
    fn clause(body: &[usize], head: usize) -> JClause {
        let atom = |id| JAtom::Concept {
            concept: format!("source_{id}"), term: JTerm::Var { name: "x".into() },
        };
        JClause { body: body.iter().map(|id| atom(*id)).collect(), head: vec![atom(head)] }
    }
    impl Lowering {
        fn expression(&mut self, expression: &Concept, depth: usize) -> Option<usize> {
            if depth > 64 || self.ids.len() >= 100_000 { return None; }
            if let Some(id) = self.ids.get(expression) { return Some(*id); }
            let id = self.ids.len();
            self.ids.insert(expression.clone(), id);
            match expression {
                Concept::Name(_) | Concept::Bottom => {},
                Concept::Top => self.structural.push(clause(&[], id)),
                Concept::And(children) => {
                    let children = children.iter().map(|child| self.expression(child, depth + 1))
                        .collect::<Option<Vec<_>>>()?;
                    self.structural.push(clause(&children, id));
                    for child in children { self.structural.push(clause(&[id], child)); }
                },
                Concept::Exists(_, filler) => {
                    let child = self.expression(filler, depth + 1)?;
                    // All roles remain fixed in the locality model transfer.
                    // Forgetting their availability conservatively activates
                    // an existential whenever its filler is active.
                    self.structural.push(clause(&[id], child));
                    self.structural.push(clause(&[child], id));
                },
                _ => return None,
            }
            Some(id)
        }
    }
    if old.len().saturating_add(new.len()) > 100_000 { return None; }
    let mut lower = Lowering { ids: HashMap::new(), structural: Vec::new() };
    let mut snapshots = Vec::new();
    for axioms in [old, new] {
        let mut rules = BTreeSet::new();
        for axiom in axioms {
            let a = lower.expression(&axiom.left, 0)?;
            let b = lower.expression(&axiom.right, 0)?;
            match axiom.kind {
                SourceAxiomKind::SubClass => { rules.insert((vec![a], b)); },
                SourceAxiomKind::Equivalent => {
                    rules.insert((vec![a], b)); rules.insert((vec![b], a));
                },
                SourceAxiomKind::Disjoint => {
                    let bottom = lower.expression(&Concept::Bottom, 0)?;
                    let mut body = vec![a,b]; body.sort_unstable(); body.dedup();
                    rules.insert((body, bottom));
                },
            }
        }
        snapshots.push(rules);
    }
    let query_ids = queries.iter().map(|name| lower.expression(&Concept::Name(name.clone()), 0)
        .map(|id| format!("source_{id}"))).collect::<Option<Vec<_>>>()?;
    let global_ids = global.iter().map(|name| lower.expression(&Concept::Name(name.clone()), 0)
        .map(|id| format!("source_{id}"))).collect::<Option<Vec<_>>>()?;
    let changed: Vec<_> = snapshots[0].symmetric_difference(&snapshots[1])
        .map(|(body, head)| clause(body, *head)).collect();
    // Structural rules from both snapshots are always present in the union
    // abstraction. Only changed source inclusions invalidate query rows.
    let mut prior = lower.structural;
    prior.extend(snapshots[0].iter().map(|(body, head)| clause(body, *head)));
    let after: Vec<_> = snapshots[1].iter().map(|(body, head)| clause(body, *head)).collect();
    let changed_queries = affected(&prior, &after, &changed, &query_ids, &global_ids)?;
    Some(queries.iter().zip(query_ids).filter(|(_, id)| changed_queries.contains(id))
        .map(|(name, _)| name.clone()).collect())
}

/// Select source axioms whose antecedents activate for at least one requested
/// query. Each query has its own bit: conjuncts reached by different queries
/// must not combine. All role/background constraints remain the caller's
/// responsibility, as with `source_affected`.
pub(crate) fn source_module_indices(
    axioms: &[crate::json_io::SourceAxiomMeta], queries: &[String], global: &[String],
) -> Option<Vec<usize>> {
    use crate::frontend::syntax::Concept;
    use crate::json_io::SourceAxiomKind;
    struct Graph {
        ids: HashMap<Concept, usize>,
        rules: Vec<(Vec<usize>, usize)>,
    }
    impl Graph {
        fn expression(&mut self, expression: &Concept, depth: usize) -> Option<usize> {
            if depth > 64 || self.ids.len() >= 100_000 { return None; }
            if let Some(&id) = self.ids.get(expression) { return Some(id); }
            let id = self.ids.len();
            self.ids.insert(expression.clone(), id);
            match expression {
                Concept::Name(_) | Concept::Bottom => {},
                Concept::Top => self.rules.push((Vec::new(), id)),
                Concept::And(children) => {
                    let mut children = children.iter().map(|child| self.expression(child, depth + 1))
                        .collect::<Option<Vec<_>>>()?;
                    children.sort_unstable(); children.dedup();
                    for &child in &children { self.rules.push((vec![id], child)); }
                    self.rules.push((children, id));
                },
                Concept::Exists(_, filler) => {
                    let child = self.expression(filler, depth + 1)?;
                    self.rules.push((vec![id], child));
                    self.rules.push((vec![child], id));
                },
                _ => return None,
            }
            Some(id)
        }
    }
    if axioms.len() > 100_000 { return None; }
    let mut graph = Graph { ids: HashMap::new(), rules: Vec::new() };
    let mut source_rules = Vec::with_capacity(axioms.len());
    for axiom in axioms {
        let left = graph.expression(&axiom.left, 0)?;
        let right = graph.expression(&axiom.right, 0)?;
        let rules = match axiom.kind {
            SourceAxiomKind::SubClass => vec![(vec![left], right)],
            SourceAxiomKind::Equivalent => vec![(vec![left], right), (vec![right], left)],
            SourceAxiomKind::Disjoint => {
                let bottom = graph.expression(&Concept::Bottom, 0)?;
                let mut body = vec![left, right]; body.sort_unstable(); body.dedup();
                vec![(body, bottom)]
            },
        };
        let mut positions = Vec::new();
        for rule in rules { positions.push(graph.rules.len()); graph.rules.push(rule); }
        source_rules.push(positions);
    }
    let query_ids = queries.iter().map(|name| graph.expression(&Concept::Name(name.clone()), 0))
        .collect::<Option<Vec<_>>>()?;
    let global_ids = global.iter().map(|name| graph.expression(&Concept::Name(name.clone()), 0))
        .collect::<Option<Vec<_>>>()?;
    let words = queries.len().div_ceil(64);
    if graph.rules.len() > 500_000
        || graph.ids.len().checked_mul(words)?.checked_mul(8)? > 64 * 1024 * 1024 {
        return None;
    }
    let mut values = vec![vec![0u64; words]; graph.ids.len()];
    for (q, id) in query_ids.into_iter().enumerate() { values[id][q / 64] |= 1 << (q % 64); }
    let mut full = vec![u64::MAX; words];
    if queries.len() % 64 != 0 { *full.last_mut()? = (1 << (queries.len() % 64)) - 1; }
    for id in global_ids { values[id].clone_from(&full); }
    let mut users = vec![Vec::new(); graph.ids.len()];
    for (i, (body, _)) in graph.rules.iter().enumerate() {
        for &id in body { users[id].push(i); }
    }
    let mut queue: VecDeque<_> = (0..graph.rules.len()).collect();
    let mut queued = vec![true; graph.rules.len()];
    let mut mask = full.clone();
    while let Some(i) = queue.pop_front() {
        queued[i] = false;
        let (body, head) = &graph.rules[i];
        mask.clone_from(&full);
        for &id in body {
            for (word, premise) in mask.iter_mut().zip(&values[id]) { *word &= premise; }
        }
        let mut grew = false;
        for (word, add) in values[*head].iter_mut().zip(&mask) {
            let next = *word | add; grew |= next != *word; *word = next;
        }
        if grew { for &dependent in &users[*head] {
            if !queued[dependent] { queued[dependent] = true; queue.push_back(dependent); }
        }}
    }
    Some(source_rules.into_iter().enumerate().filter_map(|(axiom, rules)| {
        let active = rules.into_iter().any(|i| {
            mask.clone_from(&full);
            for &id in &graph.rules[i].0 {
                for (word, premise) in mask.iter_mut().zip(&values[id]) { *word &= premise; }
            }
            mask.iter().any(|word| *word != 0)
        });
        active.then_some(axiom)
    }).collect())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::json_io::JTerm;

    #[test]
    fn source_locality_preserves_finite_relational_models() {
        use crate::frontend::syntax::Concept;
        use crate::json_io::{SourceAxiomMeta, SourceAxiomKind::*};
        let name = |n| Concept::Name(format!("C{n}"));
        let some = Concept::Exists(crate::frontend::syntax::Role::Name("r".into()), Box::new(name(1)));
        let ax = |kind, left, right| SourceAxiomMeta { kind, left, right };
        let palette = [ax(SubClass, name(0), some.clone()),
            ax(SubClass, some, name(2)),
            ax(SubClass, Concept::And(BTreeSet::from([name(0),name(1)])), name(2)),
            ax(Equivalent, name(1), name(2)), ax(Disjoint, name(0), name(2)),
            ax(SubClass, Concept::Top, name(1))];
        fn holds(c: &Concept, x: usize, classes: usize, roles: usize) -> bool {
            match c {
                Concept::Name(n) => classes & (1 << (2*n[1..].parse::<usize>().unwrap()+x)) != 0,
                Concept::Top => true, Concept::Bottom => false,
                Concept::And(children) => children.iter().all(|c| holds(c,x,classes,roles)),
                Concept::Exists(_,filler) => (0..2).any(|y|
                    roles & (1 << (2*x+y)) != 0 && holds(filler,y,classes,roles)),
                _ => unreachable!(),
            }
        }
        let theories: Vec<Vec<_>> = (0usize..64).map(|mask| palette.iter().enumerate()
            .filter(|(i,_)| mask & (1 << i) != 0).map(|(_,ax)| ax.clone()).collect()).collect();
        let mut outcomes = Vec::new();
        for theory in &theories {
            let mut entails = [[true; 3]; 3];
            let mut satisfiable = [false; 3];
            for classes in 0..64 { for roles in 0..16 {
                let valid = theory.iter().all(|ax| (0..2).all(|x| {
                    let left=holds(&ax.left,x,classes,roles);
                    let right=holds(&ax.right,x,classes,roles);
                    match ax.kind { SubClass => !left || right,
                        Equivalent => left == right, Disjoint => !(left && right) }
                }));
                if !valid { continue; }
                for q in 0..3 { for x in 0..2 {
                    if holds(&name(q),x,classes,roles) {
                        satisfiable[q]=true;
                        for target in 0..3 {
                            entails[q][target] &= holds(&name(target),x,classes,roles);
                        }
                    }
                }}
            }}
            outcomes.push((satisfiable,entails));
        }
        let queries: Vec<_> = (0..3).map(|i| format!("C{i}")).collect();
        for (mask, theory) in theories.iter().enumerate() { for q in 0..3 {
            let selected = source_module_indices(theory, &[queries[q].clone()], &[]).unwrap();
            let module: Vec<_> = selected.into_iter().map(|i| theory[i].clone()).collect();
            let module_mask = theories.iter().position(|t| *t == module).unwrap();
            assert_eq!(outcomes[mask].0[q], outcomes[module_mask].0[q], "module satisfiability {mask}/{q}");
            assert_eq!(outcomes[mask].1[q], outcomes[module_mask].1[q], "module subsumption {mask}/{q}");
        }}
        for mask in 0..64 { for edit in 0..6 {
            let next=mask ^ (1 << edit);
            let changed=source_affected(&theories[mask],&theories[next],&queries,&[]).unwrap();
            assert_eq!(Some(changed.clone()), legacy_source_affected(
                &theories[mask], &theories[next], &queries, &[]));
            for q in 0..3 { if !changed.contains(&queries[q]) {
                assert_eq!(outcomes[mask].0[q],outcomes[next].0[q],"satisfiability {mask}/{edit}/{q}");
                assert_eq!(outcomes[mask].1[q],outcomes[next].1[q],"subsumption {mask}/{edit}/{q}");
            }}
        }}
    }

    #[test]
    fn source_locality_keeps_structural_rules_out_of_the_edit_and_rejects_negation() {
        use crate::frontend::syntax::Concept;
        use crate::json_io::{SourceAxiomMeta, SourceAxiomKind};
        let ax = SourceAxiomMeta { kind: SourceAxiomKind::SubClass,
            left: Concept::Name("A".into()), right: Concept::Exists(crate::frontend::syntax::Role::Name("r".into()),
                Box::new(Concept::Name("B".into()))) };
        let queries = vec!["A".into(),"B".into(),"C".into()];
        assert_eq!(source_affected(&[], &[ax.clone()], &queries, &[]).unwrap(),
            BTreeSet::from(["A".into()]));
        assert!(source_affected(&[ax.clone()], &[ax.clone(),ax.clone()], &queries, &[]).unwrap().is_empty());
        assert_eq!(source_affected(&[], &[ax.clone()], &queries, &["A".into()]).unwrap(),
            queries.iter().cloned().collect());
        let mut outside = ax; outside.right = Concept::Not(Box::new(Concept::Name("B".into())));
        assert!(source_affected(&[], &[outside], &queries, &[]).is_none());
    }

    #[test]
    fn numeric_source_activation_matches_clause_oracle_with_globals_and_word_boundaries() {
        use crate::frontend::syntax::{Concept, Role};
        use crate::json_io::{SourceAxiomMeta, SourceAxiomKind::*};
        let name = |n| Concept::Name(format!("C{n}"));
        let palette = [
            SourceAxiomMeta { kind: SubClass, left: name(63), right: name(64) },
            SourceAxiomMeta { kind: Equivalent, left: name(64), right: name(129) },
            SourceAxiomMeta { kind: SubClass, left: Concept::Top, right: name(2) },
            SourceAxiomMeta { kind: Disjoint, left: name(63), right: name(2) },
            SourceAxiomMeta { kind: SubClass, left: Concept::And(BTreeSet::from([name(2), name(129)])), right: name(0) },
            SourceAxiomMeta { kind: SubClass, left: name(0), right: Concept::Exists(Role::Inverse("r".into()), Box::new(name(1))) },
        ];
        for count in [0, 1, 64, 65, 130] {
            let queries: Vec<_> = (0..count).map(|i| format!("C{i}")).collect();
            for mask in 0..64 {
                let old: Vec<_> = palette.iter().enumerate().filter(|(i,_)| mask & (1 << i) != 0)
                    .map(|(_,a)| a.clone()).collect();
                let new: Vec<_> = palette.iter().enumerate().filter(|(i,_)| (mask ^ 21) & (1 << i) != 0)
                    .map(|(_,a)| a.clone()).collect();
                for globals in [vec![], vec!["C63".into()], vec!["C2".into(), "C129".into()]] {
                    assert_eq!(source_affected(&old,&new,&queries,&globals),
                        legacy_source_affected(&old,&new,&queries,&globals), "{count}/{mask}/{globals:?}");
                }
            }
        }
    }

    #[test]
    fn source_activation_optional_differential_timing() {
        let Some(output) = std::env::var_os("KM_SOURCE_ACTIVATION_COMPARE") else { return; };
        let read = |key| serde_json::from_slice::<crate::orchestrate::cb_to_ht::TInput>(
            &std::fs::read(std::env::var_os(key).expect("paired input")).unwrap()).unwrap();
        let old = read("KM_SOURCE_ACTIVATION_OLD"); let new = read("KM_SOURCE_ACTIVATION_NEW");
        let queries: Vec<_> = old.queries.iter().map(|q| old.concepts[*q].clone()).collect();
        let globals: Vec<_> = [&old,&new].into_iter().flat_map(|input|
            input.role_domains.iter().chain(&input.role_ranges)
                .map(|(_,c)| input.concepts[*c].clone())).collect();
        let mut records = Vec::new();
        for repeat in 0..8 {
            let mut answers = Vec::new();
            for legacy in if repeat % 2 == 0 { [false,true] } else { [true,false] } {
                let start = std::time::Instant::now();
                let answer = if legacy { legacy_source_affected(&old.source_axioms,&new.source_axioms,&queries,&globals) }
                    else { source_affected(&old.source_axioms,&new.source_axioms,&queries,&globals) }.unwrap();
                records.push(serde_json::json!({"repeat":repeat,"legacy":legacy,"seconds":start.elapsed().as_secs_f64(),"affected":answer.len()}));
                answers.push(answer);
            }
            assert_eq!(answers[0],answers[1]);
        }
        std::fs::write(output,serde_json::to_vec_pretty(&records).unwrap()).unwrap();
    }

    #[test]
    fn source_locality_optional_frozen_input_probe() {
        let Some(old_path) = std::env::var_os("KM_SOURCE_ACTIVATION_OLD") else { return; };
        let new_path = std::env::var_os("KM_SOURCE_ACTIVATION_NEW").expect("paired source probe");
        let read = |path| serde_json::from_slice::<crate::orchestrate::cb_to_ht::TInput>(
            &std::fs::read(path).unwrap()).unwrap();
        let old=read(old_path); let new=read(new_path);
        let queries: Vec<_> = old.queries.iter().map(|q| old.concepts[*q].clone()).collect();
        let globals: Vec<_> = [&old,&new].into_iter().flat_map(|input|
            input.role_domains.iter().chain(&input.role_ranges)
                .map(|(_,c)| input.concepts[*c].clone())).collect();
        let start=std::time::Instant::now();
        let result=source_affected(&old.source_axioms,&new.source_axioms,&queries,&globals).unwrap();
        eprintln!("source-locality queries={} affected={} reusable={} analysis_s={}",
            queries.len(),result.len(),queries.len()-result.len(),start.elapsed().as_secs_f64());
        if let Some(path)=std::env::var_os("KM_SOURCE_ACTIVATION_OUTPUT") {
            std::fs::write(path,serde_json::to_vec(&result).unwrap()).unwrap();
        }
    }

    #[test]
    fn source_module_keeps_queries_separate_and_handles_global_and_top_seeds() {
        use crate::frontend::syntax::Concept;
        use crate::json_io::{SourceAxiomMeta, SourceAxiomKind};
        let name = |s: &str| Concept::Name(s.into());
        let conjunction = Concept::And(BTreeSet::from([name("A"), name("B")]));
        let ax = SourceAxiomMeta { kind: SourceAxiomKind::SubClass, left: conjunction, right: name("C") };
        let queries = vec!["A".into(), "B".into()];
        assert!(source_module_indices(&[ax.clone()], &queries, &[]).unwrap().is_empty());
        assert_eq!(source_module_indices(&[ax.clone()], &queries, &["B".into()]), Some(vec![0]));
        let top = SourceAxiomMeta { kind: SourceAxiomKind::SubClass, left: Concept::Top, right: name("B") };
        assert_eq!(source_module_indices(&[ax.clone(), top.clone()], &queries, &[]), Some(vec![0, 1]));
        assert!(source_module_indices(&[top], &[], &[]).unwrap().is_empty());
        let mut unsupported = ax;
        unsupported.right = Concept::Not(Box::new(name("C")));
        assert!(source_module_indices(&[unsupported], &queries, &[]).is_none());
        let many: Vec<_> = (0..130).map(|i| format!("C{i}")).collect();
        let axioms: Vec<_> = [63, 64, 129, 130].into_iter().map(|i| SourceAxiomMeta {
            kind: SourceAxiomKind::SubClass, left: name(&format!("C{i}")), right: name("D"),
        }).collect();
        assert_eq!(source_module_indices(&axioms, &many, &[]), Some(vec![0, 1, 2]));
    }

    #[test]
    fn source_module_optional_frozen_input_probe() {
        let Some(path) = std::env::var_os("KM_SOURCE_MODULE_INPUT") else { return; };
        let input: crate::orchestrate::cb_to_ht::TInput = serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap();
        let focus = std::env::var_os("KM_SOURCE_MODULE_FOCUS").expect("module focus file");
        let focus: serde_json::Value = serde_json::from_slice(&std::fs::read(focus).unwrap()).unwrap();
        let queries: Vec<String> = serde_json::from_value(focus["affected_names"].clone()).unwrap();
        let globals: Vec<_> = input.role_domains.iter().chain(&input.role_ranges)
            .map(|(_,c)| input.concepts[*c].clone()).collect();
        let start = std::time::Instant::now();
        let selected = source_module_indices(&input.source_axioms, &queries, &globals).unwrap();
        let elapsed = start.elapsed().as_secs_f64();
        let axioms: Vec<_> = selected.iter().map(|i| &input.source_axioms[*i]).collect();
        let result = serde_json::json!({"selected_indices": selected, "selected_axioms": axioms, "analysis_s": elapsed});
        let output = std::env::var_os("KM_SOURCE_MODULE_OUTPUT").expect("module output file");
        std::fs::write(output, serde_json::to_vec(&result).unwrap()).unwrap();
        eprintln!("source-module queries={} axioms={} analysis_s={elapsed}", queries.len(), axioms.len());
    }

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
