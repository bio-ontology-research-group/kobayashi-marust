//! Experimental deletion-only reproof of previously exact taxonomy rows.
//! The caller must establish complete source coverage, an unchanged background
//! and public signature. Every derived inclusion is a source implication,
//! conjunction rule, same-role existential monotonicity, or a consequence of
//! typed role domains/chains (including transitivity). Unlike the
//! locality abstraction, this graph never identifies an existential with its
//! filler. The semantic argument is IncrementalDeletionSupport.lean; executable
//! source/proof binding is still outside the runtime certification boundary.
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use crate::frontend::syntax::{Concept, Role};
use crate::incremental::IncrementalResult;
use crate::json_io::{SourceAxiomKind, SourceAxiomMeta};

const MAX_RULES: usize = 500_000;
struct Graph {
    ids: HashMap<Concept, usize>,
    rules: Vec<(Vec<usize>, usize)>,
    parents: Vec<Vec<(Role, usize)>>,
    existentials: Vec<Option<(Role, usize)>>,
}
impl Graph {
    fn expression(&mut self, expression: &Concept, depth: usize) -> Option<usize> {
        if depth > 64 || self.ids.len() >= 25_000 { return None; }
        if let Some(&id) = self.ids.get(expression) { return Some(id); }
        let id = self.ids.len();
        self.ids.insert(expression.clone(), id);
        self.parents.push(Vec::new());
        self.existentials.push(None);
        match expression {
            Concept::Name(_) | Concept::Bottom => {},
            Concept::Top => self.rules.push((vec![], id)),
            Concept::And(children) => {
                let children = children.iter().map(|c| self.expression(c, depth + 1))
                    .collect::<Option<Vec<_>>>()?;
                for &child in &children { self.rules.push((vec![id], child)); }
                self.rules.push((children, id));
            },
            Concept::Exists(role, filler) => {
                let filler = self.expression(filler, depth + 1)?;
                self.parents[filler].push((role.clone(), id));
                self.existentials[id] = Some((role.clone(), filler));
            },
            _ => return None,
        }
        Some(id)
    }
}

/// Sound support is intentionally incomplete. None, unsupported expressions or
/// exhausted analysis bounds leave every original invalidation in force.
pub(crate) fn supported_rows_with_background(
    old: &[SourceAxiomMeta], new: &[SourceAxiomMeta], queries: &[String],
    affected: &BTreeSet<String>, previous: &IncrementalResult,
    background: Option<&crate::orchestrate::cb_to_ht::TInput>,
) -> Option<BTreeSet<String>> {
    if previous.inconsistent || previous.dropped != 0 || !previous.unresolved.is_empty()
        || old.len().saturating_add(new.len()) > 100_000 { return None; }
    fn key(a: &SourceAxiomMeta) -> (u8, &Concept, &Concept) { (match a.kind {
        SourceAxiomKind::SubClass => 0, SourceAxiomKind::Equivalent => 1,
        SourceAxiomKind::Disjoint => 2,
    }, &a.left, &a.right) }
    let prior: BTreeSet<_> = old.iter().map(key).collect();
    if new.iter().any(|a| !prior.contains(&key(a))) { return None; }
    let mut graph = Graph { ids: HashMap::new(), rules: Vec::new(), parents: Vec::new(), existentials: Vec::new() };
    let query_ids = queries.iter().map(|q| graph.expression(&Concept::Name(q.clone()), 0))
        .collect::<Option<Vec<_>>>()?;
    let bottom = graph.expression(&Concept::Bottom, 0)?;
    graph.expression(&Concept::Top, 0)?;
    for ax in new {
        let left = graph.expression(&ax.left, 0)?;
        let right = graph.expression(&ax.right, 0)?;
        match ax.kind {
            SourceAxiomKind::SubClass => graph.rules.push((vec![left], right)),
            SourceAxiomKind::Equivalent => {
                graph.rules.push((vec![left], right)); graph.rules.push((vec![right], left));
            },
            SourceAxiomKind::Disjoint => graph.rules.push((vec![left, right], bottom)),
        }
    }
    // An existential with an impossible filler is itself impossible.
    for (_, parent) in &graph.parents[bottom] { graph.rules.push((vec![*parent], bottom)); }
    let mut chains: HashMap<(Role,Role), Vec<Role>> = HashMap::new();
    if let Some(input) = background {
        let role = |id: usize| input.roles.get(id).map(|name| Role::Name(name.clone()));
        for &(r,s,t) in &input.chains {
            chains.entry((role(r)?,role(s)?)).or_default().push(role(t)?);
        }
        for &r in &input.transitive {
            chains.entry((role(r)?,role(r)?)).or_default().push(role(r)?);
        }
        for &(r,c) in &input.role_domains {
            let r = role(r)?;
            let target = graph.expression(&Concept::Name(input.concepts.get(c)?.clone()),0)?;
            for (id, expression) in graph.existentials.iter().enumerate() {
                if expression.as_ref().is_some_and(|(s,_)| *s == r) {
                    if graph.rules.len() >= MAX_RULES { return None; }
                    graph.rules.push((vec![id],target));
                }
            }
        }
        // The reflexive inclusion of an existential filler supplies the
        // literal nested-existential instance of a role-chain consequence.
        for (inner, expression) in graph.existentials.iter().enumerate() {
            let Some((s,filler)) = expression else { continue; };
            for (r,left) in &graph.parents[inner] {
                let Some(target_roles) = chains.get(&(r.clone(),s.clone())) else { continue; };
                for (t,right) in &graph.parents[*filler] {
                    if target_roles.contains(t) {
                        if graph.rules.len() >= MAX_RULES { return None; }
                        graph.rules.push((vec![*left],*right));
                    }
                }
            }
        }
    }
    let count = graph.ids.len(); let words = count.div_ceil(64);
    if graph.rules.len() > MAX_RULES || count.checked_mul(words)?.checked_mul(8)? > 64*1024*1024 {
        return None;
    }
    // Each bit is a global expression subsumption, not a fact at a shared
    // individual. That distinction is required for existential monotonicity.
    let mut values = vec![vec![0u64; words]; count];
    for (id, value) in values.iter_mut().enumerate() { value[id/64] |= 1 << (id%64); }
    let mut fillers = vec![0u64; words];
    for (id, parents) in graph.parents.iter().enumerate() {
        if !parents.is_empty() { fillers[id/64] |= 1 << (id%64); }
    }
    let mut users = vec![Vec::new(); count];
    for (i,(body,_)) in graph.rules.iter().enumerate() { for &id in body { users[id].push(i); } }
    let mut queue: VecDeque<_> = (0..graph.rules.len()).collect();
    let mut queued = vec![true; graph.rules.len()];
    let mut mask = vec![0u64; words]; let mut delta = vec![0u64; words];
    let mut lifted = HashSet::new();
    while let Some(i) = queue.pop_front() {
        queued[i] = false;
        let (body, head) = &graph.rules[i]; let head = *head;
        mask.fill(u64::MAX);
        // Do not manufacture roots past the end of the expression universe.
        if count % 64 != 0 { *mask.last_mut()? = (1 << (count % 64)) - 1; }
        for &id in body {
            for (word, premise) in mask.iter_mut().zip(&values[id]) { *word &= premise; }
        }
        let mut grew = false;
        for ((word, add), change) in values[head].iter_mut().zip(&mask).zip(&mut delta) {
            *change = *add & !*word; grew |= *change != 0; *word |= *add;
        }
        if !grew { continue; }
        for &dependent in &users[head] {
            if !queued[dependent] { queued[dependent] = true; queue.push_back(dependent); }
        }
        if graph.parents[head].is_empty() && head != bottom
            && graph.existentials[head].is_none() { continue; }
        let mut edges = Vec::new();
        for (word_index, (&change, &is_filler)) in delta.iter().zip(&fillers).enumerate() {
            let mut changed = change & is_filler;
            while changed != 0 {
                let sub = word_index*64 + changed.trailing_zeros() as usize;
                changed &= changed - 1;
                for (role, left) in &graph.parents[sub] {
                    if head == bottom { edges.push((*left,bottom)); }
                    else { for (other_role, right) in &graph.parents[head] {
                        if role == other_role { edges.push((*left,*right)); }
                    }}
                    if let Some((inner_role,filler)) = &graph.existentials[head] {
                        if let Some(target_roles) = chains.get(&(role.clone(),inner_role.clone())) {
                            for (target_role,right) in &graph.parents[*filler] {
                                if target_roles.contains(target_role) { edges.push((*left,*right)); }
                            }
                        }
                    }
                    if edges.len() >= MAX_RULES { return None; }
                }
            }
        }
        for (left, right) in edges {
            if left == right || !lifted.insert((left,right)) { continue; }
            if graph.rules.len() >= MAX_RULES { return None; }
            let index = graph.rules.len(); graph.rules.push((vec![left],right));
            users[left].push(index); queued.push(true); queue.push_back(index);
        }
    }
    let named: BTreeMap<_,_> = graph.ids.iter().filter_map(|(expression,id)| {
        if let Concept::Name(name) = expression { Some((name.as_str(),*id)) } else { None }
    }).collect();
    let mut supported = BTreeSet::new();
    for (query, &id) in queries.iter().zip(&query_ids) {
        if !affected.contains(query) { continue; }
        let Some(row) = previous.subsumptions.get(query) else { continue; };
        let proves = |target: usize| values[target][id/64] & (1 << (id%64)) != 0;
        if row.iter().all(|target| {
            if target == "owl:Nothing" { proves(bottom) }
            else { named.get(target.as_str()).is_some_and(|&target| proves(target)) }
        }) { supported.insert(query.clone()); }
    }
    Some(supported)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn supported_rows(old: &[SourceAxiomMeta], new: &[SourceAxiomMeta], queries: &[String],
        affected: &BTreeSet<String>, previous: &IncrementalResult) -> Option<BTreeSet<String>> {
        supported_rows_with_background(old,new,queries,affected,previous,None)
    }
    fn name(s: &str) -> Concept { Concept::Name(s.into()) }
    fn ax(left: Concept, right: Concept) -> SourceAxiomMeta {
        SourceAxiomMeta { kind: SourceAxiomKind::SubClass, left, right }
    }
    fn result(rows: &[(&str, &[&str])]) -> IncrementalResult {
        IncrementalResult { subsumptions: rows.iter().map(|(q,ts)|
            (q.to_string(),ts.iter().map(|t| t.to_string()).collect())).collect(),
            inconsistent: false, dropped: 0, unresolved: vec![] }
    }
    #[test]
    fn retains_reproved_rows_but_rejects_additions_and_missing_answers() {
        let new = vec![ax(name("A"),name("C")),ax(name("C"),name("B"))];
        let mut old = new.clone(); old.push(ax(name("A"),name("B")));
        let queries = vec!["A".into(),"B".into(),"C".into()];
        let affected = queries.iter().cloned().collect();
        let previous = result(&[("A",&["B","C"]),("B",&[]),("C",&["B"])]);
        assert_eq!(supported_rows(&old,&new,&queries,&affected,&previous),Some(affected.clone()));
        assert!(supported_rows(&new,&old,&queries,&affected,&previous).is_none());
        let missing = result(&[("A",&["B","D"])]);
        assert!(supported_rows(&old,&new,&queries,&affected,&missing).unwrap().is_empty());
        let mut bad = previous; bad.inconsistent = true;
        assert!(supported_rows(&old,&new,&queries,&affected,&bad).is_none());
        bad.inconsistent = false; bad.dropped = 1;
        assert!(supported_rows(&old,&new,&queries,&affected,&bad).is_none());
    }
    #[test]
    fn existential_lifting_does_not_identify_fillers_with_successors() {
        let some = |c| Concept::Exists(Role::Inverse("r".into()),Box::new(c));
        let new = vec![ax(name("A"),some(name("B"))),ax(name("B"),name("C")),
            ax(some(name("C")),name("D"))];
        let mut old = new.clone(); old.push(ax(name("A"),name("D")));
        let queries = vec!["A".into()]; let affected = queries.iter().cloned().collect();
        let previous = result(&[("A",&["D"])]);
        assert_eq!(supported_rows(&old,&new,&queries,&affected,&previous),Some(affected.clone()));
        // Losing the actual existential witness invalidates A's D answer.
        assert!(supported_rows(&old,&new[1..],&queries,&affected,&previous).unwrap().is_empty());
        // B's filler membership alone never entails an r-successor in C.
        assert!(supported_rows(&old,&new,&["B".into()],&BTreeSet::from(["B".into()]),
            &result(&[("B",&["D"])] )).unwrap().is_empty());
    }
    #[test]
    fn role_background_proves_domains_and_chains_without_reversing_them() {
        let some=|r:&str,c| Concept::Exists(Role::Name(r.into()),Box::new(c));
        let new=vec![ax(name("A"),some("r",name("B"))),
            ax(name("B"),some("s",name("C"))),ax(some("t",name("C")),name("D"))];
        let mut old=new.clone();old.push(ax(name("A"),name("D")));
        let queries=vec!["A".into()];let affected=queries.iter().cloned().collect();
        let previous=result(&[("A",&["D","Domain"])]);
        let mut input=crate::orchestrate::cb_to_ht::TInput::default();
        input.roles=vec!["r".into(),"s".into(),"t".into()];
        input.concepts=vec!["Domain".into()];input.role_domains=vec![(0,0)];
        input.chains=vec![(0,1,2)];
        assert_eq!(supported_rows_with_background(&old,&new,&queries,&affected,&previous,Some(&input)),Some(affected.clone()));
        input.chains=vec![(1,0,2)];
        assert!(supported_rows_with_background(&old,&new,&queries,&affected,&previous,Some(&input)).unwrap().is_empty());
        input.chains=vec![(0,1,99)];
        assert!(supported_rows_with_background(&old,&new,&queries,&affected,&previous,Some(&input)).is_none());
        input.roles=vec!["r".into()];input.chains.clear();input.transitive=vec![0];
        let new=vec![ax(name("A"),some("r",name("B"))),
            ax(name("B"),some("r",name("C"))),ax(some("r",name("C")),name("D"))];
        assert_eq!(supported_rows_with_background(&new,&new,&queries,&affected,&previous,Some(&input)),Some(affected));
    }

    #[test]
    fn retained_unsatisfiability_needs_a_new_bottom_proof() {
        let clash = SourceAxiomMeta { kind: SourceAxiomKind::Disjoint, left: name("B"), right: name("C") };
        let new = vec![ax(name("A"),name("B")),ax(name("A"),name("C")),clash];
        let mut old = new.clone(); old.push(ax(name("A"),Concept::Bottom));
        let queries = vec!["A".into()];let affected=queries.iter().cloned().collect();
        let previous=result(&[("A",&["owl:Nothing"])]);
        assert_eq!(supported_rows(&old,&new,&queries,&affected,&previous),Some(affected.clone()));
        assert!(supported_rows(&old,&new[1..],&queries,&affected,&previous).unwrap().is_empty());
        let unsupported=vec![ax(name("A"),Concept::Not(Box::new(name("B"))))];
        assert!(supported_rows(&unsupported,&unsupported,&queries,&affected,&previous).is_none());
    }
    #[test]
    fn supported_rows_preserve_exhaustive_finite_model_answers_after_deletion() {
        let c=|i| name(&format!("C{i}"));
        let some=Concept::Exists(Role::Name("r".into()),Box::new(c(1)));
        let palette=[ax(c(0),some.clone()),ax(some,c(2)),
            ax(Concept::And(BTreeSet::from([c(0),c(1)])),c(2)),
            SourceAxiomMeta{kind:SourceAxiomKind::Equivalent,left:c(1),right:c(2)},
            SourceAxiomMeta{kind:SourceAxiomKind::Disjoint,left:c(0),right:c(2)},
            ax(Concept::Top,c(1))];
        fn holds(c:&Concept,x:usize,classes:usize,roles:usize)->bool {
            match c {
                Concept::Name(n)=>classes & (1 << (2*n[1..].parse::<usize>().unwrap()+x))!=0,
                Concept::Top=>true,Concept::Bottom=>false,
                Concept::And(cs)=>cs.iter().all(|c|holds(c,x,classes,roles)),
                Concept::Exists(_,c)=>(0..2).any(|y|roles & (1 << (2*x+y))!=0 && holds(c,y,classes,roles)),
                _=>unreachable!(),
            }
        }
        let queries:Vec<_>=(0..3).map(|i|format!("C{i}")).collect();
        let affected=queries.iter().cloned().collect();
        let theories:Vec<Vec<_>>=(0usize..64).map(|mask|palette.iter().enumerate()
            .filter(|(i,_)|mask & (1<<i)!=0).map(|(_,a)|a.clone()).collect()).collect();
        let mut answers=Vec::new();
        for theory in &theories {
            let mut sat=[false;3];let mut entails=[[true;3];3];let mut consistent=false;
            for classes in 0..64 { for roles in 0..16 {
                if !theory.iter().all(|a|(0..2).all(|x|{
                    let l=holds(&a.left,x,classes,roles);let r=holds(&a.right,x,classes,roles);
                    match a.kind {SourceAxiomKind::SubClass=>!l||r,SourceAxiomKind::Equivalent=>l==r,
                        SourceAxiomKind::Disjoint=>!(l&&r)}
                })) {continue;}
                consistent=true;
                for q in 0..3 { for x in 0..2 { if holds(&c(q),x,classes,roles) {
                    sat[q]=true;for t in 0..3 {entails[q][t]&=holds(&c(t),x,classes,roles);}
                }}}
            }}
            answers.push(IncrementalResult { inconsistent:!consistent,dropped:0,unresolved:vec![],
                subsumptions:queries.iter().enumerate().map(|(q,n)|(n.clone(),if !sat[q] {
                    vec!["owl:Nothing".into()]
                } else {(0..3).filter(|t|*t!=q && entails[q][*t]).map(|t|queries[t].clone()).collect()})).collect() });
        }
        for mask in 0..64 { for edit in 0..6 {
            if mask & (1<<edit)==0 || answers[mask].inconsistent {continue;}
            let next=mask & !(1<<edit);
            for q in supported_rows(&theories[mask],&theories[next],&queries,&affected,&answers[mask]).unwrap() {
                assert_eq!(answers[mask].subsumptions[&q],answers[next].subsumptions[&q],"{mask}/{edit}/{q}");
            }
        }}
    }
}
