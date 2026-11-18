//! Exact endpoint grounding of DL-safe object-role paths and rooted trees.
//! A private class denotes precisely the original named-object domain. Every
//! rolled intermediate variable is guarded by that class; anonymous paths do
//! not fire the source rule. Arbitrary graphs remain with the general compiler.
use super::syntax::{mk_and, Axiom, Concept, Role, RuleAtom, RuleTerm};
use std::collections::{BTreeMap, BTreeSet};

pub(super) struct PathPlan {
    pub rules: Vec<Axiom>,
    pub axioms: Vec<Axiom>,
    pub domain: Option<String>,
    pub instances: usize,
}

#[derive(Clone)]
struct RootedTree {
    body: Vec<RuleAtom>,
    head: Vec<RuleAtom>,
    root: String,
    fixed: Vec<String>,
}

fn path(rule: &Axiom) -> Option<(Vec<Role>, String)> {
    let Axiom::Rule(body, head) = rule else { return None };
    let [RuleAtom::Role(head_role, RuleTerm::Var(start), RuleTerm::Var(end))] = head.as_slice() else { return None };
    if start == end || body.is_empty() { return None; }
    let edges = body.iter().map(|atom| match atom {
        RuleAtom::Role(r, RuleTerm::Var(a), RuleTerm::Var(b)) if a != b => Some((r,a,b)),
        _ => None,
    }).collect::<Option<Vec<_>>>()?;
    let mut remaining: Vec<_> = (0..edges.len()).collect();
    let mut seen = BTreeSet::from([start.as_str()]);
    let mut current = start.as_str();
    let mut roles = Vec::new();
    while !remaining.is_empty() {
        let incident: Vec<_> = remaining.iter().copied().filter(|&i| {
            edges[i].1 == current || edges[i].2 == current
        }).collect();
        let [index] = incident.as_slice() else { return None };
        let (role,a,b) = edges[*index];
        let (next, step) = if a == current { (b.as_str(), Role::Name(role.clone())) }
            else { (a.as_str(), Role::Inverse(role.clone())) };
        if !seen.insert(next) { return None; }
        roles.push(step);
        remaining.retain(|i| i != index);
        current = next;
    }
    (current == end).then(|| (roles, head_role.clone()))
}

fn atom_vars(atom: &RuleAtom) -> Option<Vec<&str>> {
    match atom {
        RuleAtom::Class(_, RuleTerm::Var(a)) => Some(vec![a.as_str()]),
        RuleAtom::Role(_, RuleTerm::Var(a), RuleTerm::Var(b))
        | RuleAtom::Same(RuleTerm::Var(a), RuleTerm::Var(b))
        | RuleAtom::Diff(RuleTerm::Var(a), RuleTerm::Var(b)) => Some(vec![a.as_str(), b.as_str()]),
        _ => None,
    }
}

fn anchor_fixed_len(body: &[RuleAtom], head: &[RuleAtom], total_vars: usize) -> usize {
    if !body.iter().all(|a| matches!(a, RuleAtom::Class(..) | RuleAtom::Role(..))) {
        return total_vars;
    }
    let mut fixed = BTreeSet::new();
    for atom in head {
        let Some(vars) = atom_vars(atom) else { return total_vars; };
        for v in vars { fixed.insert(v.to_owned()); }
    }
    let mut edges = Vec::new();
    for atom in body {
        if let RuleAtom::Role(_, RuleTerm::Var(a), RuleTerm::Var(b)) = atom {
            if a == b { return total_vars; }
            edges.push((a.clone(), b.clone()));
        }
    }
    loop {
        let mut parent: BTreeMap<String, String> = BTreeMap::new();
        fn find(parent: &BTreeMap<String, String>, v: &str) -> String {
            let mut x = v;
            while let Some(p) = parent.get(x) { x = p; }
            x.to_owned()
        }
        let mut cyclic = false;
        let mut degrees: BTreeMap<String, usize> = BTreeMap::new();
        for (a, b) in &edges {
            if fixed.contains(a) || fixed.contains(b) { continue; }
            *degrees.entry(a.clone()).or_default() += 1;
            *degrees.entry(b.clone()).or_default() += 1;
            let ra = find(&parent, a);
            let rb = find(&parent, b);
            if ra == rb { cyclic = true; } else { parent.insert(ra, rb); }
        }
        if !cyclic { return fixed.len(); }
        let Some((next, _)) = degrees.into_iter().max_by_key(|(v, n)| (*n, v.clone())) else {
            return total_vars;
        };
        fixed.insert(next);
    }
}

fn valid_rooted_tree(body: &[RuleAtom], head: &[RuleAtom], all_vars: &BTreeSet<&str>,
    root: &str, fixed: &BTreeSet<&str>) -> bool {
    if fixed.is_empty() || fixed.contains(root) { return false; }
    // Validate head: every atom either mentions `root` directly or mentions a
    // fixed variable `u` linked to `root` by a direct head Role atom.
    let mut head_linked_fixed = BTreeSet::new();
    let mut has_direct_head = false;
    for atom in head {
        match atom {
            RuleAtom::Class(_, RuleTerm::Var(a)) if a == root => has_direct_head = true,
            RuleAtom::Role(_, RuleTerm::Var(a), RuleTerm::Var(b)) if a == root && fixed.contains(b.as_str()) => {
                has_direct_head = true;
                head_linked_fixed.insert(b.as_str());
            }
            RuleAtom::Role(_, RuleTerm::Var(a), RuleTerm::Var(b)) if b == root && fixed.contains(a.as_str()) => {
                has_direct_head = true;
                head_linked_fixed.insert(a.as_str());
            }
            RuleAtom::Same(RuleTerm::Var(a), RuleTerm::Var(b))
            | RuleAtom::Diff(RuleTerm::Var(a), RuleTerm::Var(b))
                if (a == root && fixed.contains(b.as_str())) || (b == root && fixed.contains(a.as_str())) =>
            {
                has_direct_head = true;
            }
            _ => {}
        }
    }
    if !has_direct_head { return false; }
    for atom in head {
        let Some(vars) = atom_vars(atom) else { return false; };
        if vars.contains(&root) {
            if !vars.iter().all(|&v| v == root || fixed.contains(v)) { return false; }
            if matches!(atom, RuleAtom::Role(_, RuleTerm::Var(a), RuleTerm::Var(b))
                | RuleAtom::Same(RuleTerm::Var(a), RuleTerm::Var(b))
                | RuleAtom::Diff(RuleTerm::Var(a), RuleTerm::Var(b)) if a == b)
            {
                return false;
            }
        } else {
            if !vars.iter().all(|&v| fixed.contains(v)) { return false; }
            if !vars.iter().any(|&v| head_linked_fixed.contains(v)) { return false; }
        }
    }
    // Validate body: free variables must form a single connected acyclic tree
    // containing `root`; `Same`/`Diff` may not connect two free variables; and
    // any fixed-only body atom must touch a fixed variable adjacent to the tree.
    let free_vars: BTreeSet<&str> = all_vars.iter().copied().filter(|v| !fixed.contains(v)).collect();
    if !free_vars.contains(root) { return false; }
    let mut tree_edges: Vec<(&str, &str)> = Vec::new();
    let mut body_linked_fixed = BTreeSet::new();
    for atom in body {
        match atom {
            RuleAtom::Class(_, RuleTerm::Var(_)) => {}
            RuleAtom::Role(_, RuleTerm::Var(a), RuleTerm::Var(b)) => {
                if a == b { return false; }
                let (fa, fb) = (!fixed.contains(a.as_str()), !fixed.contains(b.as_str()));
                if fa && fb {
                    tree_edges.push((a.as_str(), b.as_str()));
                } else if fa && !fb {
                    body_linked_fixed.insert(b.as_str());
                } else if !fa && fb {
                    body_linked_fixed.insert(a.as_str());
                }
            }
            RuleAtom::Same(RuleTerm::Var(a), RuleTerm::Var(b))
            | RuleAtom::Diff(RuleTerm::Var(a), RuleTerm::Var(b)) => {
                if a == b { return false; }
                if !fixed.contains(a.as_str()) && !fixed.contains(b.as_str()) {
                    return false;
                }
            }
            _ => return false,
        }
    }
    for atom in body {
        let Some(vars) = atom_vars(atom) else { return false; };
        if vars.iter().all(|&v| fixed.contains(v))
            && !vars.iter().any(|&v| body_linked_fixed.contains(v))
        {
            return false;
        }
    }
    if tree_edges.len() + 1 != free_vars.len() { return false; }
    let mut visited = BTreeSet::from([root]);
    let mut queue = std::collections::VecDeque::from([root]);
    while let Some(curr) = queue.pop_front() {
        for &(a, b) in &tree_edges {
            let next = if a == curr { Some(b) } else if b == curr { Some(a) } else { None };
            if let Some(n) = next {
                if visited.insert(n) { queue.push_back(n); }
            }
        }
    }
    visited.len() == free_vars.len()
}

fn choose_subsets<'a>(pool: &[&'a str], k: usize, start: usize, current: &mut Vec<&'a str>,
    f: &mut impl FnMut(&[&'a str]) -> bool) -> bool {
    if current.len() == k { return f(current); }
    for i in start..pool.len() {
        if pool.len() - i < k - current.len() { break; }
        current.push(pool[i]);
        if choose_subsets(pool, k, i + 1, current, f) { return true; }
        current.pop();
    }
    false
}

fn rooted_tree(rule: &Axiom, named_len: usize, tree_threshold: usize) -> Option<RootedTree> {
    let Axiom::Rule(body, head) = rule else { return None };
    if body.is_empty() || head.is_empty() { return None; }
    let mut all_vars: BTreeSet<&str> = BTreeSet::new();
    let mut head_vars: BTreeSet<&str> = BTreeSet::new();
    for atom in body {
        for v in atom_vars(atom)? { all_vars.insert(v); }
    }
    for atom in head {
        for v in atom_vars(atom)? {
            all_vars.insert(v);
            head_vars.insert(v);
        }
    }
    if all_vars.len() > 16 { return None; }
    let has_eq_or_diff = body.iter().chain(head).any(|a| matches!(a, RuleAtom::Same(..) | RuleAtom::Diff(..)));
    let anchor_len = anchor_fixed_len(body, head, all_vars.len());
    let anchor_instances = (0..anchor_len).try_fold(
        if named_len == 0 && !all_vars.is_empty() { 0usize } else { 1usize },
        |n, _| n.checked_mul(named_len),
    ).unwrap_or(usize::MAX);
    if !has_eq_or_diff && anchor_instances <= tree_threshold {
        return None;
    }
    let max_fixed = if has_eq_or_diff { all_vars.len().saturating_sub(1) } else { anchor_len.saturating_sub(1) };
    let mut best: Option<(usize, String, Vec<String>)> = None;
    for &root in &head_vars {
        let base_fixed: BTreeSet<&str> = head_vars.iter().copied().filter(|&v| v != root).collect();
        if base_fixed.len() > max_fixed { continue; }
        let extra_pool: Vec<&str> = all_vars.iter().copied()
            .filter(|&v| v != root && !base_fixed.contains(v))
            .collect();
        let max_extra = (max_fixed - base_fixed.len()).min(extra_pool.len());
        for k in 0..=max_extra {
            let total_k = base_fixed.len() + k;
            if total_k == 0 { continue; }
            if best.as_ref().is_some_and(|(best_len, _, _)| total_k >= *best_len) { break; }
            let mut current = Vec::new();
            let mut found = None;
            choose_subsets(&extra_pool, k, 0, &mut current, &mut |chosen| {
                let mut fixed = base_fixed.clone();
                fixed.extend(chosen.iter().copied());
                if valid_rooted_tree(body, head, &all_vars, root, &fixed) {
                    found = Some(fixed.into_iter().map(str::to_owned).collect::<Vec<_>>());
                    return true;
                }
                false
            });
            if let Some(fixed_vec) = found {
                best = Some((total_k, root.to_owned(), fixed_vec));
                break;
            }
        }
    }
    let (_, root, fixed) = best?;
    Some(RootedTree { body: body.clone(), head: head.clone(), root, fixed })
}

fn expand_rooted_tree(tree: &RootedTree, binding: &BTreeMap<&str, &str>, guard: &Concept) -> Axiom {
    let is_free = |v: &str| !binding.contains_key(v);
    let mut fixed_body_extras: BTreeMap<&str, Vec<Concept>> = BTreeMap::new();
    let mut linked_in_body: BTreeSet<&str> = BTreeSet::new();
    for atom in &tree.body {
        if let RuleAtom::Role(_, RuleTerm::Var(a), RuleTerm::Var(b)) = atom {
            if is_free(a) && !is_free(b) { linked_in_body.insert(b.as_str()); }
            else if !is_free(a) && is_free(b) { linked_in_body.insert(a.as_str()); }
        }
    }
    for atom in &tree.body {
        let vars = atom_vars(atom).unwrap();
        if !vars.iter().all(|&v| !is_free(v)) { continue; }
        let owner = vars.iter().copied().find(|v| linked_in_body.contains(v)).unwrap();
        let concept = match atom {
            RuleAtom::Class(c, _) => c.clone(),
            RuleAtom::Role(r, RuleTerm::Var(a), RuleTerm::Var(b)) => {
                if a == owner {
                    Concept::Exists(Role::Name(r.clone()), Box::new(Concept::Nominal(binding[b.as_str()].to_owned())))
                } else {
                    Concept::Exists(Role::Inverse(r.clone()), Box::new(Concept::Nominal(binding[a.as_str()].to_owned())))
                }
            }
            RuleAtom::Same(RuleTerm::Var(a), RuleTerm::Var(b)) => {
                let other = if a == owner { b.as_str() } else { a.as_str() };
                Concept::Nominal(binding[other].to_owned())
            }
            RuleAtom::Diff(RuleTerm::Var(a), RuleTerm::Var(b)) => {
                let other = if a == owner { b.as_str() } else { a.as_str() };
                Concept::Not(Box::new(Concept::Nominal(binding[other].to_owned())))
            }
            _ => unreachable!(),
        };
        fixed_body_extras.entry(owner).or_default().push(concept);
    }
    fn build_body<'a>(
        v: &'a str,
        parent_edge: Option<usize>,
        body: &'a [RuleAtom],
        binding: &BTreeMap<&'a str, &'a str>,
        guard: &Concept,
        fixed_extras: &mut BTreeMap<&'a str, Vec<Concept>>,
    ) -> Concept {
        let is_free = |x: &str| !binding.contains_key(x);
        let mut parts = vec![guard.clone()];
        for (i, atom) in body.iter().enumerate() {
            if parent_edge == Some(i) { continue; }
            match atom {
                RuleAtom::Class(c, RuleTerm::Var(x)) if x == v => parts.push(c.clone()),
                RuleAtom::Same(RuleTerm::Var(a), RuleTerm::Var(b)) => {
                    if a == v && !is_free(b) {
                        parts.push(Concept::Nominal(binding[b.as_str()].to_owned()));
                    } else if b == v && !is_free(a) {
                        parts.push(Concept::Nominal(binding[a.as_str()].to_owned()));
                    }
                }
                RuleAtom::Diff(RuleTerm::Var(a), RuleTerm::Var(b)) => {
                    if a == v && !is_free(b) {
                        parts.push(Concept::Not(Box::new(Concept::Nominal(binding[b.as_str()].to_owned()))));
                    } else if b == v && !is_free(a) {
                        parts.push(Concept::Not(Box::new(Concept::Nominal(binding[a.as_str()].to_owned()))));
                    }
                }
                RuleAtom::Role(r, RuleTerm::Var(a), RuleTerm::Var(b)) => {
                    let (other, role) = if a == v {
                        (b.as_str(), Role::Name(r.clone()))
                    } else if b == v {
                        (a.as_str(), Role::Inverse(r.clone()))
                    } else {
                        continue;
                    };
                    let filler = if is_free(other) {
                        build_body(other, Some(i), body, binding, guard, fixed_extras)
                    } else {
                        let mut fparts = vec![Concept::Nominal(binding[other].to_owned())];
                        if let Some(extras) = fixed_extras.remove(other) {
                            fparts.extend(extras);
                        }
                        mk_and(fparts)
                    };
                    parts.push(Concept::Exists(role, Box::new(filler)));
                }
                _ => {}
            }
        }
        mk_and(parts)
    }
    let premise = build_body(&tree.root, None, &tree.body, binding, guard, &mut fixed_body_extras);
    let mut head_linked: BTreeSet<&str> = BTreeSet::new();
    for atom in &tree.head {
        if let RuleAtom::Role(_, RuleTerm::Var(a), RuleTerm::Var(b)) = atom {
            if a == &tree.root && !is_free(b) { head_linked.insert(b.as_str()); }
            else if b == &tree.root && !is_free(a) { head_linked.insert(a.as_str()); }
        }
    }
    let mut head_extras: BTreeMap<&str, Vec<Concept>> = BTreeMap::new();
    for atom in &tree.head {
        let vars = atom_vars(atom).unwrap();
        if vars.contains(&tree.root.as_str()) { continue; }
        let owner = vars.iter().copied().find(|v| head_linked.contains(v)).unwrap();
        let concept = match atom {
            RuleAtom::Class(c, _) => c.clone(),
            RuleAtom::Role(r, RuleTerm::Var(a), RuleTerm::Var(b)) => {
                if a == owner {
                    Concept::Exists(Role::Name(r.clone()), Box::new(Concept::Nominal(binding[b.as_str()].to_owned())))
                } else {
                    Concept::Exists(Role::Inverse(r.clone()), Box::new(Concept::Nominal(binding[a.as_str()].to_owned())))
                }
            }
            RuleAtom::Same(RuleTerm::Var(a), RuleTerm::Var(b)) => {
                let other = if a == owner { b.as_str() } else { a.as_str() };
                Concept::Nominal(binding[other].to_owned())
            }
            RuleAtom::Diff(RuleTerm::Var(a), RuleTerm::Var(b)) => {
                let other = if a == owner { b.as_str() } else { a.as_str() };
                Concept::Not(Box::new(Concept::Nominal(binding[other].to_owned())))
            }
            _ => unreachable!(),
        };
        head_extras.entry(owner).or_default().push(concept);
    }
    let mut head_parts = Vec::new();
    for atom in &tree.head {
        let vars = atom_vars(atom).unwrap();
        if !vars.contains(&tree.root.as_str()) { continue; }
        match atom {
            RuleAtom::Class(c, _) => head_parts.push(c.clone()),
            RuleAtom::Same(RuleTerm::Var(a), RuleTerm::Var(b)) => {
                let other = if a == &tree.root { b.as_str() } else { a.as_str() };
                head_parts.push(Concept::Nominal(binding[other].to_owned()));
            }
            RuleAtom::Diff(RuleTerm::Var(a), RuleTerm::Var(b)) => {
                let other = if a == &tree.root { b.as_str() } else { a.as_str() };
                head_parts.push(Concept::Not(Box::new(Concept::Nominal(binding[other].to_owned()))));
            }
            RuleAtom::Role(r, RuleTerm::Var(a), RuleTerm::Var(b)) => {
                let (other, role) = if a == &tree.root {
                    (b.as_str(), Role::Name(r.clone()))
                } else {
                    (a.as_str(), Role::Inverse(r.clone()))
                };
                let mut fparts = vec![Concept::Nominal(binding[other].to_owned())];
                if let Some(extras) = head_extras.remove(other) {
                    fparts.extend(extras);
                }
                head_parts.push(Concept::Exists(role, Box::new(mk_and(fparts))));
            }
            _ => unreachable!(),
        }
    }
    Axiom::SubClassOf(premise, mk_and(head_parts))
}

pub(super) fn plan(rules: &[Axiom], named: &BTreeSet<String>, occupied: &BTreeSet<String>,
    max_instances: usize) -> Result<PathPlan, &'static str> {
    plan_with_threshold(rules, named, occupied, max_instances, 256)
}

fn plan_with_threshold(rules: &[Axiom], named: &BTreeSet<String>, occupied: &BTreeSet<String>,
    max_instances: usize, tree_threshold: usize) -> Result<PathPlan, &'static str> {
    let mut rest = Vec::new();
    let mut paths = Vec::new();
    let mut trees = Vec::new();
    for rule in rules {
        if let Some(p) = path(rule) {
            paths.push(p);
        } else if let Some(t) = rooted_tree(rule, named.len(), tree_threshold) {
            trees.push(t);
        } else {
            rest.push(rule.clone());
        }
    }
    if paths.is_empty() && trees.is_empty() {
        return Ok(PathPlan { rules: rest, axioms: vec![], domain: None, instances: 0 });
    }
    let mut instances = paths.len().checked_mul(named.len())
        .ok_or("path grounding instance budget exceeded")?;
    let mut tree_counts = Vec::with_capacity(trees.len());
    for tree in &trees {
        let count = (0..tree.fixed.len()).try_fold(1usize, |n, _| n.checked_mul(named.len()))
            .ok_or("path grounding instance budget exceeded")?;
        instances = instances.checked_add(count)
            .ok_or("path grounding instance budget exceeded")?;
        tree_counts.push(count);
    }
    if instances > max_instances {
        return Err("path grounding instance budget exceeded");
    }
    let domain = (0usize..).map(|i| format!("__ground_path_domain_{i}"))
        .find(|s| !occupied.contains(s) && !named.contains(s)).unwrap();
    let guard = Concept::Name(domain.clone());
    let members = if named.is_empty() { Concept::Bottom } else {
        Concept::Or(named.iter().cloned().map(Concept::Nominal).collect())
    };
    let mut axioms = vec![Axiom::SubClassOf(guard.clone(), members.clone()),
        Axiom::SubClassOf(members, guard.clone())];
    for (steps, head_role) in paths {
        for endpoint in named {
            let mut body = Concept::Nominal(endpoint.clone());
            for step in steps.iter().rev() {
                body = mk_and([guard.clone(), Concept::Exists(step.clone(), Box::new(body))]);
            }
            axioms.push(Axiom::SubClassOf(body, Concept::Exists(Role::Name(head_role.clone()),
                Box::new(Concept::Nominal(endpoint.clone())))));
        }
    }
    let names: Vec<_> = named.iter().collect();
    for (tree, count) in trees.into_iter().zip(tree_counts) {
        for index in 0..count {
            let mut rem = index;
            let binding: BTreeMap<&str, &str> = tree.fixed.iter().map(|v| {
                let name = names[rem % names.len()];
                rem /= names.len();
                (v.as_str(), name.as_str())
            }).collect();
            axioms.push(expand_rooted_tree(&tree, &binding, &guard));
        }
    }
    Ok(PathPlan { rules: rest, axioms, domain: Some(domain), instances })
}

#[cfg(test)]
mod tests {
    use super::*;
    fn v(s:&str)->RuleTerm {RuleTerm::Var(s.into())}
    fn edge(r:&str,a:&str,b:&str)->RuleAtom {RuleAtom::Role(r.into(),v(a),v(b))}
    fn cls(c:&str,a:&str)->RuleAtom {RuleAtom::Class(Concept::Name(c.into()),v(a))}
    #[test]
    fn paths_match_all_two_element_models_including_aliases_and_unnamed_objects() {
        let _test_env = crate::test_env::read();
        let named=BTreeSet::from(["a".into(),"b".into()]);
        for reverse in [false,true] {
            let rule=Axiom::Rule(vec![edge("r","x","y"), if reverse {edge("s","z","y")} else {edge("s","y","z")}],vec![edge("t","x","z")]);
            let p=plan(&[rule],&named,&named,2).unwrap();
            assert!(p.rules.is_empty()); assert_eq!(p.instances,2);
            fn eval(c:&Concept,x:usize,names:[usize;2],domain:&str,rs:[u8;3])->bool {
                let individual=|n:&str| if n=="a" {names[0]} else if n=="b" {names[1]} else {panic!("unknown name")};
                let role=|r:&Role,a:usize,b:usize| {
                    let (n,a,b)=match r {Role::Name(n)=>(n,a,b),Role::Inverse(n)=>(n,b,a),Role::Universal=>panic!("unexpected universal role")};
                    let i=match n.as_str(){"r"=>0,"s"=>1,"t"=>2,_=>panic!("unknown role")};rs[i]&(1<<(2*a+b))!=0
                };
                match c {
                    Concept::Name(n) if n==domain=>names.contains(&x),
                    Concept::Nominal(n)=>individual(n)==x,
                    Concept::And(cs)=>cs.iter().all(|c|eval(c,x,names,domain,rs)),
                    Concept::Or(cs)=>cs.iter().any(|c|eval(c,x,names,domain,rs)),
                    Concept::Exists(r,c)=>(0..2).any(|y|role(r,x,y)&&eval(c,y,names,domain,rs)),
                    Concept::Bottom=>false,
                    _=>panic!("unexpected concept"),
                }
            }
            for a in 0..2 {for b in 0..2 {for r in 0..16u8 {for s in 0..16u8 {for t in 0..16u8 {
                let names=[a,b];let has=|mask:u8,x:usize,y:usize|mask&(1<<(2*x+y))!=0;
                let original=names.iter().all(|&x|names.iter().all(|&y|names.iter().all(|&z|
                    !(has(r,x,y)&&if reverse {has(s,z,y)}else{has(s,y,z)})||has(t,x,z))));
                let compiled=p.axioms.iter().all(|ax| match ax {Axiom::SubClassOf(l,u)=>(0..2).all(|x|
                    !eval(l,x,names,p.domain.as_ref().unwrap(),[r,s,t])||eval(u,x,names,p.domain.as_ref().unwrap(),[r,s,t])),_=>panic!("unexpected axiom")});
                assert_eq!(original,compiled,"reverse={reverse}, names={names:?}, relations={r},{s},{t}");
            }}}}}
        }
    }
    #[test]
    fn rooted_trees_with_diff_and_multi_atom_heads_match_two_element_models() {
        let _test_env = crate::test_env::read();
        let named = BTreeSet::from(["a".into(), "b".into()]);
        // Shape 1: ore_ont_8250 rule 2 shape (4 vars, Diff in body, unary head).
        let diff_rule = Axiom::Rule(
            vec![
                cls("A", "hyp"),
                RuleAtom::Diff(v("hyp"), v("htype")),
                edge("r", "m", "hyp"),
                edge("s", "m", "dom"),
                edge("t", "dom", "htype"),
            ],
            vec![cls("B", "m")],
        );
        let p = plan(&[diff_rule], &named, &named, 2).unwrap();
        assert!(p.rules.is_empty());
        assert_eq!(p.instances, 2);
        fn eval(c: &Concept, x: usize, names: [usize; 2], domain: &str, ca: u8, cb: u8, rs: [u8; 3]) -> bool {
            let individual = |n: &str| if n == "a" { names[0] } else if n == "b" { names[1] } else { panic!("unknown") };
            let role = |r: &Role, a: usize, b: usize| {
                let (n, a, b) = match r {
                    Role::Name(n) => (n, a, b),
                    Role::Inverse(n) => (n, b, a),
                    Role::Universal => panic!("unexpected universal role"),
                };
                let i = match n.as_str() { "r" => 0, "s" => 1, "t" => 2, _ => panic!("unknown role") };
                rs[i] & (1 << (2 * a + b)) != 0
            };
            match c {
                Concept::Name(n) if n == domain => names.contains(&x),
                Concept::Name(n) if n == "A" => ca & (1 << x) != 0,
                Concept::Name(n) if n == "B" => cb & (1 << x) != 0,
                Concept::Nominal(n) => individual(n) == x,
                Concept::Not(inner) => !eval(inner, x, names, domain, ca, cb, rs),
                Concept::And(cs) => cs.iter().all(|c| eval(c, x, names, domain, ca, cb, rs)),
                Concept::Or(cs) => cs.iter().any(|c| eval(c, x, names, domain, ca, cb, rs)),
                Concept::Exists(r, c) => (0..2).any(|y| role(r, x, y) && eval(c, y, names, domain, ca, cb, rs)),
                Concept::Bottom => false,
                _ => panic!("unexpected concept"),
            }
        }
        for a in 0..2 { for b in 0..2 { for ca in 0..4u8 { for cb in 0..4u8 {
            for r in 0..16u8 { for s in 0..16u8 { for t in 0..16u8 {
                let names = [a, b];
                let has = |mask: u8, x: usize, y: usize| mask & (1 << (2 * x + y)) != 0;
                let has_c = |mask: u8, x: usize| mask & (1 << x) != 0;
                let original = names.iter().all(|&m| names.iter().all(|&dom|
                    names.iter().all(|&hyp| names.iter().all(|&htype|
                        !(has_c(ca, hyp) && hyp != htype && has(r, m, hyp) && has(s, m, dom) && has(t, dom, htype))
                            || has_c(cb, m)
                    ))
                ));
                let compiled = p.axioms.iter().all(|ax| match ax {
                    Axiom::SubClassOf(l, u) => (0..2).all(|x|
                        !eval(l, x, names, p.domain.as_ref().unwrap(), ca, cb, [r, s, t])
                            || eval(u, x, names, p.domain.as_ref().unwrap(), ca, cb, [r, s, t])
                    ),
                    _ => panic!("unexpected axiom"),
                });
                assert_eq!(original, compiled);
            }}}
        }}}}
    }
    #[test]
    fn ore_ont_8250_and_6615_rules_compile_with_minimal_fixed_sets() {
        let _test_env = crate::test_env::read();
        let named62: BTreeSet<String> = (0..62).map(|i| format!("ind_{i}")).collect();
        let r8250_1 = Axiom::Rule(
            vec![
                edge("hasSource", "pcon", "pint2"),
                edge("hasDisk", "dom", "vdisk"),
                cls("StorageVolume", "vol"),
                edge("hostedByStorage", "vdisk", "vol"),
                edge("exports", "san", "vol"),
                edge("hasInterface", "san", "pint1"),
                edge("connects", "pcon", "pint1"),
                edge("hasConnection", "net", "pcon"),
                edge("hasTarget", "pcon", "pint2"),
                cls("Network", "net"),
            ],
            vec![edge("reachesSource", "vdisk", "pint2")],
        );
        let r8250_2 = Axiom::Rule(
            vec![
                cls("Virtualization", "hyp"),
                RuleAtom::Diff(v("hyp"), v("htype")),
                edge("runsOn", "m", "hyp"),
                edge("hasDomain", "m", "dom"),
                edge("compatibleWith", "dom", "htype"),
            ],
            vec![cls("MachineHostingUnsupportedDomain", "m")],
        );
        let p8250 = plan(&[r8250_1, r8250_2], &named62, &named62, 200).unwrap();
        assert!(p8250.rules.is_empty());
        assert_eq!(p8250.instances, 124);

        let named16: BTreeSet<String> = (0..16).map(|i| format!("i_{i}")).collect();
        let r6615 = Axiom::Rule(
            vec![
                cls("Protected", "ac"),
                edge("abstract", "tc", "op1"),
                edge("access", "op1", "ac"),
                edge("instance", "sc", "op2"),
                edge("instance", "tc", "tm"),
                edge("inherits", "sc", "tc"),
                edge("invokes", "tm", "op1"),
                edge("overrides", "op2", "op1"),
            ],
            vec![
                cls("Template", "tm"),
                edge("concrete", "tm", "sc"),
                edge("template", "tm", "tc"),
            ],
        );
        let p6615 = plan(&[r6615], &named16, &named16, 300).unwrap();
        assert!(p6615.rules.is_empty());
        assert_eq!(p6615.instances, 256);
    }
    #[test]
    fn cyclic_parallel_and_disconnected_rules_keep_general_grounding() {
        let _test_env = crate::test_env::read();
        for body in [vec![edge("r","x","y"),edge("s","y","x")],
            vec![edge("r","x","y"),edge("s","x","y")],
            vec![edge("r","x","y"),edge("s","z","w")]] {
            let rule=Axiom::Rule(body,vec![edge("t","x","y")]);
            let p=plan(&[rule.clone()],&BTreeSet::new(),&BTreeSet::new(),0).unwrap();
            assert_eq!(p.rules,vec![rule]);assert!(p.domain.is_none());
        }
    }
}
