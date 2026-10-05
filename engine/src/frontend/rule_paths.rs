//! Exact endpoint grounding of DL-safe object-role paths.
//! A private class denotes precisely the original named-object domain. Every
//! rolled intermediate variable is guarded by that class; anonymous paths do
//! not fire the source rule. Arbitrary graphs remain with the general compiler.
use super::syntax::{mk_and, Axiom, Concept, Role, RuleAtom, RuleTerm};
use std::collections::BTreeSet;

pub(super) struct PathPlan {
    pub rules: Vec<Axiom>,
    pub axioms: Vec<Axiom>,
    pub domain: Option<String>,
    pub instances: usize,
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

pub(super) fn plan(rules: &[Axiom], named: &BTreeSet<String>, occupied: &BTreeSet<String>,
    max_instances: usize) -> Result<PathPlan, &'static str> {
    let mut rest = Vec::new();
    let mut paths = Vec::new();
    for rule in rules {
        if let Some(p) = path(rule) { paths.push(p); } else { rest.push(rule.clone()); }
    }
    if paths.is_empty() {
        return Ok(PathPlan { rules: rest, axioms: vec![], domain: None, instances: 0 });
    }
    let instances = paths.len().checked_mul(named.len()).filter(|n| *n <= max_instances)
        .ok_or("path grounding instance budget exceeded")?;
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
    Ok(PathPlan { rules: rest, axioms, domain: Some(domain), instances })
}

#[cfg(test)]
mod tests {
    use super::*;
    fn v(s:&str)->RuleTerm {RuleTerm::Var(s.into())}
    fn edge(r:&str,a:&str,b:&str)->RuleAtom {RuleAtom::Role(r.into(),v(a),v(b))}
    #[test]
    fn paths_match_all_two_element_models_including_aliases_and_unnamed_objects() {
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
    fn cyclic_parallel_and_disconnected_rules_keep_general_grounding() {
        for body in [vec![edge("r","x","y"),edge("s","y","x")],
            vec![edge("r","x","y"),edge("s","x","y")],
            vec![edge("r","x","y"),edge("s","z","w")]] {
            let rule=Axiom::Rule(body,vec![edge("t","x","y")]);
            let p=plan(&[rule.clone()],&BTreeSet::new(),&BTreeSet::new(),0).unwrap();
            assert_eq!(p.rules,vec![rule]);assert!(p.domain.is_none());
        }
    }
}
