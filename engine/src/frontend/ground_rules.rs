//! Exact finite named-object grounding into ordinary nominal axioms.
//!
//! This planning API requires the complete source named-object domain and all
//! occupied source symbols. It does not authorize a classifier or erase source
//! rules: the caller must establish coverage and a complete backend separately.
use super::syntax::{mk_and, Axiom, Concept, Ontology, Role, RuleAtom, RuleTerm};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug)]
pub struct GroundRulePlan {
    pub anchor: String,
    pub cover: Option<String>,
    pub links: BTreeMap<String, String>,
    pub axioms: Vec<Axiom>,
    pub instances: usize,
}

/// Apply a plan only after matching the complete logical source-rule count.
/// The count must come from a source observer, before any unsupported rule can
/// be omitted by parsing. Already-normalized data rules require their own
/// coverage evidence; this entry deliberately does not infer it from a count
/// of whatever happened to survive parsing.
pub fn lower_object_rules(ontology: &mut Ontology, named: &BTreeSet<String>,
    occupied: &BTreeSet<String>, source_rules: u64, observer_rules: u64,
    max_instances: usize) -> Result<GroundRulePlan, &'static str> {
    if ontology.datatype_rules().next().is_some() {
        return Err("concrete source rules have not been normalized");
    }
    let rules: Vec<_> = ontology.rules().cloned().collect();
    if (rules.len() as u64).checked_add(observer_rules) != Some(source_rules) {
        return Err("source/parsed rule coverage mismatch");
    }
    let plan = plan(&rules, named, occupied, max_instances)?;
    // Nothing before this point mutates the ontology. A failure cannot leave
    // some rules removed, partially grounded, or weakened to their ABox closure.
    ontology.retain_axioms(|axiom| !matches!(axiom, Axiom::Rule(..)));
    for axiom in &plan.axioms { ontology.add(axiom.clone()); }
    Ok(plan)
}

fn terms(atom: &RuleAtom) -> Result<Vec<&RuleTerm>, &'static str> {
    match atom {
        RuleAtom::Class(_, a) => Ok(vec![a]),
        RuleAtom::Role(_, a, b) | RuleAtom::Same(a, b) | RuleAtom::Diff(a, b) => Ok(vec![a, b]),
        _ => Err("concrete rule atom requires exact normalization before grounding"),
    }
}

// Remove head variables and enough feedback vertices to leave a forest.
// Each remaining variable is existential only in the premise. Disconnected
// components have independent witnesses; multiple edges count as a cycle.
fn forest_grounding(body: &[RuleAtom], head: &[RuleAtom]) -> Option<BTreeSet<String>> {
    if !body.iter().all(|a| matches!(a, RuleAtom::Class(..) | RuleAtom::Role(..))) {
        return None;
    }
    let mut fixed = BTreeSet::new();
    for atom in head {
        for term in terms(atom).ok()? {
            if let RuleTerm::Var(v) = term { fixed.insert(v.clone()); }
        }
    }
    let mut edges = Vec::new();
    for atom in body {
        if let RuleAtom::Role(_, RuleTerm::Var(a), RuleTerm::Var(b)) = atom {
            if a == b { return None; }
            edges.push((a.clone(), b.clone()));
        }
    }
    loop {
        let mut parent: BTreeMap<String,String> = BTreeMap::new();
        fn find(parent: &BTreeMap<String,String>, v: &str) -> String {
            let mut x=v;
            while let Some(p)=parent.get(x) { x=p; }
            x.to_owned()
        }
        let mut cyclic = false;
        let mut degrees: BTreeMap<String,usize> = BTreeMap::new();
        for (a,b) in &edges {
            if fixed.contains(a) || fixed.contains(b) { continue; }
            *degrees.entry(a.clone()).or_default()+=1;
            *degrees.entry(b.clone()).or_default()+=1;
            let ra=find(&parent,a); let rb=find(&parent,b);
            if ra==rb {cyclic=true;} else {parent.insert(ra,rb);}
        }
        if !cyclic {return Some(fixed);}
        let next=degrees.into_iter().max_by_key(|(v,n)|(*n,v.clone()))?.0;
        fixed.insert(next);
    }
}

fn forest_components(body: &[RuleAtom], binding: &BTreeMap<&str,&str>,
    guard: &Concept) -> Vec<Concept> {
    fn is_free(t: &RuleTerm,binding: &BTreeMap<&str,&str>) -> bool {
        matches!(t,RuleTerm::Var(v) if !binding.contains_key(v.as_str()))
    }
    fn visit(v:&str, parent:Option<usize>, body:&[RuleAtom],
        binding:&BTreeMap<&str,&str>, guard:&Concept, seen:&mut BTreeSet<String>) -> Concept {
        assert!(seen.insert(v.to_owned()), "forest planner retained a cycle");
        let mut parts=vec![guard.clone()];
        for (i,atom) in body.iter().enumerate() {
            match atom {
                RuleAtom::Class(c,RuleTerm::Var(x)) if x==v => parts.push(c.clone()),
                RuleAtom::Role(r,a,b) if parent!=Some(i) => {
                    let (other,role)=if matches!(a,RuleTerm::Var(x) if x==v) {
                        (b,Role::Name(r.clone()))
                    } else if matches!(b,RuleTerm::Var(x) if x==v) {
                        (a,Role::Inverse(r.clone()))
                    } else {continue};
                    let filler=match other {
                        RuleTerm::Var(x) if is_free(other,binding) => visit(x,Some(i),body,binding,guard,seen),
                        RuleTerm::Var(x)=>Concept::Nominal(binding[x.as_str()].to_owned()),
                        RuleTerm::Ind(x)=>Concept::Nominal(x.clone()),
                    };
                    parts.push(Concept::Exists(role,Box::new(filler)));
                }
                _=>{}
            }
        }
        mk_and(parts)
    }
    let mut seen=BTreeSet::new(); let mut components=Vec::new();
    for atom in body {
        for term in terms(atom).expect("validated atoms") {
            if let RuleTerm::Var(v)=term {
                if is_free(term,binding) && !seen.contains(v) {
                    components.push(visit(v,None,body,binding,guard,&mut seen));
                }
            }
        }
    }
    components
}

/// Fail atomically if any rule, term, or size bound is unsupported. Names are
/// grounding representatives, not distinct domain elements: no UNA is added.
pub fn plan(rules: &[Axiom], named: &BTreeSet<String>, occupied: &BTreeSet<String>,
    max_instances: usize) -> Result<GroundRulePlan, &'static str> {
    let mut specifications = Vec::new();
    let mut total = 0usize;
    for rule in rules {
        let Axiom::Rule(body, head) = rule else { return Err("not an object rule") };
        let mut variables = BTreeSet::new();
        for atom in body.iter().chain(head) {
            for term in terms(atom)? {
                match term {
                    RuleTerm::Var(v) => { variables.insert(v.clone()); }
                    RuleTerm::Ind(i) if !named.contains(i) => return Err("rule constant missing from named domain"),
                    RuleTerm::Ind(_) => {}
                }
            }
        }
        let grounding = forest_grounding(body, head).unwrap_or_else(|| variables.clone());
        let rolled = grounding.len() < variables.len();
        let count = (0..grounding.len()).try_fold(
            if named.is_empty() && !variables.is_empty() {0usize} else {1usize},
            |n, _| n.checked_mul(named.len()))
            .ok_or("grounding size overflow")?;
        total = total.checked_add(count).filter(|n| *n <= max_instances)
            .ok_or("grounding instance budget exceeded")?;
        specifications.push((body, head, grounding.into_iter().collect::<Vec<_>>(), count, rolled));
    }
    let mut used = occupied.clone();
    used.extend(named.iter().cloned());
    // Defend against a caller omitting rule symbols from the occupied set too.
    for rule in rules {
        if let Axiom::Rule(body, head) = rule {
            for atom in body.iter().chain(head) {
                match atom {
                    RuleAtom::Role(r, _, _) => { used.insert(r.clone()); }
                    RuleAtom::Class(c, _) => collect_concept_names(c, &mut used),
                    _ => {}
                }
            }
        }
    }
    let mut counter = 0usize;
    let mut fresh = || loop {
        let name = format!("__ground_rule_{counter}"); counter += 1;
        if used.insert(name.clone()) { break name; }
    };
    let anchor = fresh();
    let links: BTreeMap<_, _> = named.iter().map(|name| (name.clone(), fresh())).collect();
    let cover = specifications.iter().any(|s| s.4).then(&mut fresh);
    let guard = if named.is_empty() { Concept::Bottom } else {
        Concept::Or(named.iter().cloned().map(Concept::Nominal).collect())
    };
    let mut axioms = Vec::new();
    for (name, link) in &links {
        axioms.push(Axiom::RoleAssertion(link.clone(), anchor.clone(), name.clone()));
        axioms.push(Axiom::ConceptAssertion(
            Concept::Forall(Role::Name(link.clone()), Box::new(Concept::Nominal(name.clone()))),
            anchor.clone()));
    }
    if let Some(role) = &cover {
        for name in named { axioms.push(Axiom::RoleAssertion(role.clone(),anchor.clone(),name.clone())); }
        axioms.push(Axiom::ConceptAssertion(Concept::Forall(Role::Name(role.clone()),
            Box::new(guard.clone())),anchor.clone()));
    }
    let names: Vec<_> = named.iter().collect();
    for (body, head, variables, count, rolled) in specifications {
        for index in 0..count {
            let mut rest = index;
            let binding: BTreeMap<_, _> = variables.iter().map(|variable| {
                let name = names[rest % names.len()]; rest /= names.len();
                (variable.as_str(), name.as_str())
            }).collect();
            let subject = |term: &RuleTerm| match term {
                RuleTerm::Ind(name) => name.as_str(),
                RuleTerm::Var(name) => binding[name.as_str()],
            }.to_owned();
            let lift = |name: String, concept| Concept::Exists(
                Role::Name(links[&name].clone()), Box::new(concept));
            let atom = |atom: &RuleAtom| match atom {
                RuleAtom::Class(c, a) => lift(subject(a), c.clone()),
                RuleAtom::Role(r, a, b) => lift(subject(a), Concept::Exists(
                    Role::Name(r.clone()), Box::new(Concept::Nominal(subject(b))))),
                RuleAtom::Same(a, b) => lift(subject(a), Concept::Nominal(subject(b))),
                RuleAtom::Diff(a, b) => lift(subject(a), Concept::Not(Box::new(Concept::Nominal(subject(b))))),
                _ => unreachable!("validated before allocating the plan"),
            };
            let fixed_atoms = body.iter().filter(|a| terms(a).unwrap().iter().all(|t|
                !matches!(t,RuleTerm::Var(v) if !binding.contains_key(v.as_str()))));
            let mut premise_parts = vec![Concept::Nominal(anchor.clone())];
            premise_parts.extend(fixed_atoms.map(&atom));
            if rolled {
                premise_parts.extend(forest_components(body,&binding,&guard).into_iter().map(|c|
                    Concept::Exists(Role::Name(cover.as_ref().unwrap().clone()),Box::new(c))));
            }
            let premise = mk_and(premise_parts);
            let conclusion = if head.is_empty() { Concept::Bottom }
                else { mk_and(head.iter().map(&atom)) };
            axioms.push(Axiom::SubClassOf(premise, conclusion));
        }
    }
    Ok(GroundRulePlan { anchor, cover, links, axioms, instances: total })
}

fn collect_concept_names(concept: &Concept, names: &mut BTreeSet<String>) {
    match concept {
        Concept::Name(n) | Concept::Nominal(n) => { names.insert(n.clone()); }
        Concept::Not(c) => collect_concept_names(c, names),
        Concept::And(cs) | Concept::Or(cs) => for c in cs { collect_concept_names(c, names); },
        Concept::Exists(r,c) | Concept::Forall(r,c) | Concept::AtLeast(_,r,c) | Concept::AtMost(_,r,c) => {
            if let Role::Name(n) | Role::Inverse(n) = r { names.insert(n.clone()); }
            collect_concept_names(c,names);
        }
        Concept::HasSelf(Role::Name(n) | Role::Inverse(n)) => { names.insert(n.clone()); }
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn var(n: &str) -> RuleTerm { RuleTerm::Var(n.into()) }
    #[test]
    fn source_coverage_and_budget_failures_leave_original_ontology_intact() {
        let names = BTreeSet::from(["a".into(), "b".into()]);
        let source = Axiom::SubClassOf(Concept::Name("C".into()),Concept::Nominal("b".into()));
        let rule = Axiom::Rule(vec![RuleAtom::Class(Concept::Name("C".into()),var("x"))],
            vec![RuleAtom::Class(Concept::Name("Bad".into()),var("x"))]);
        let mut ontology = Ontology::new();
        ontology.add(source.clone()); ontology.add(rule.clone());
        assert!(lower_object_rules(&mut ontology,&names,&names,2,0,4).is_err());
        assert!(lower_object_rules(&mut ontology,&names,&names,1,0,1).is_err());
        assert_eq!(ontology.rules().collect::<Vec<_>>(),vec![&rule]);
        assert_eq!(ontology.tbox().collect::<Vec<_>>(),vec![&source]);
        let result = lower_object_rules(&mut ontology,&names,&names,1,0,2).unwrap();
        assert_eq!(result.instances,2);
        assert_eq!(ontology.rules().count(),0);
        assert!(ontology.tbox().any(|a|a==&source));
        assert_eq!(ontology.abox().count(),4);
    }
    #[test]
    fn grounding_preserves_all_bindings_and_fresh_symbols() {
        let names = BTreeSet::from(["a".into(), "b".into()]);
        let occupied = BTreeSet::from(["__ground_rule_0".into()]);
        let rule = Axiom::Rule(vec![RuleAtom::Role("r".into(),var("x"),var("y"))],
            vec![RuleAtom::Class(Concept::Name("C".into()),var("y"))]);
        let plan = plan(&[rule.clone()], &names, &occupied, 4).unwrap();
        assert_eq!(plan.instances,2);
        assert!(!occupied.contains(&plan.anchor));
        assert_eq!(plan.links.len(),2);
        assert_eq!(plan.axioms.len(),9);
        assert!(super::plan(&[rule], &names, &occupied, 1).is_err());
    }
    #[test]
    fn empty_named_domain_and_ground_rules_are_distinguished() {
        let names = BTreeSet::new();
        let vacuous = Axiom::Rule(vec![RuleAtom::Class(Concept::Top,var("x"))],vec![]);
        assert_eq!(plan(&[vacuous],&names,&names,0).unwrap().instances,0);
        assert_eq!(plan(&[Axiom::Rule(vec![],vec![])],&names,&names,1).unwrap().instances,1);
        let missing = Axiom::Rule(vec![RuleAtom::Class(Concept::Top,RuleTerm::Ind("a".into()))],vec![]);
        assert!(plan(&[missing],&names,&names,1).is_err());
    }
    #[test]
    fn cyclic_template_rule_needs_only_head_assignments() {
        let names=(0..16).map(|i|format!("i{i}")).collect::<BTreeSet<_>>();
        let edge=|r:&str,a:&str,b:&str|RuleAtom::Role(r.into(),var(a),var(b));
        let rule=Axiom::Rule(vec![
            RuleAtom::Class(Concept::Name("Protected".into()),var("ac")),
            edge("abstract","tc","op1"),edge("access","op1","ac"),
            edge("instance","sc","op2"),edge("instance","tc","tm"),
            edge("inherits","sc","tc"),edge("invokes","tm","op1"),
            edge("overrides","op2","op1")],vec![
            RuleAtom::Class(Concept::Name("Template".into()),var("tm")),
            edge("concrete","tm","sc"),edge("template","tm","tc")]);
        let p=plan(&[rule],&names,&names,4096).unwrap();
        assert_eq!(p.instances,4096);
        assert!(p.cover.is_some());
    }

    #[test]
    fn ground_implications_match_two_element_models_without_unique_names() {
        let names = BTreeSet::from(["a".into(), "b".into()]);
        let class = |name: &str, v: &str| RuleAtom::Class(Concept::Name(name.into()),var(v));
        let candidates = vec![
            Axiom::Rule(vec![class("A","x"),RuleAtom::Role("r".into(),var("x"),var("y"))],vec![class("B","y")]),
            Axiom::Rule(vec![RuleAtom::Same(var("x"),var("y")),class("A","x")],vec![class("B","y")]),
            Axiom::Rule(vec![class("A","x"),class("B","y")],vec![RuleAtom::Diff(var("x"),var("y"))]),
            Axiom::Rule(vec![RuleAtom::Diff(var("x"),var("y"))],vec![class("A","x"),class("B","y")]),
            Axiom::Rule(vec![class("A","x")],vec![]),
            Axiom::Rule(vec![RuleAtom::Role("r".into(),var("x"),var("y")),
                RuleAtom::Role("r".into(),var("y"),var("z")),
                RuleAtom::Role("r".into(),var("z"),var("x"))],vec![class("B","x")]),
            Axiom::Rule(vec![RuleAtom::Role("r".into(),var("x"),var("y")),
                class("A","z")],vec![class("B","x")]),
            Axiom::Rule(vec![RuleAtom::Role("r".into(),var("x"),var("y")),
                RuleAtom::Role("r".into(),var("y"),var("x"))],vec![class("B","z")]),
        ];
        struct Model<'a> { plan: &'a GroundRulePlan, names: [usize;2], anchor: usize, a: u8, b: u8, r: u8 }
        impl Model<'_> {
            fn individual(&self,n: &str) -> usize {
                if n==self.plan.anchor {self.anchor} else if n=="a" {self.names[0]} else if n=="b" {self.names[1]} else {panic!("unknown individual")}
            }
            fn role(&self,n: &str,x:usize,y:usize)->bool {
                if n=="r" {return self.r & (1 << (2*x+y)) != 0}
                if self.plan.cover.as_deref()==Some(n) {return x==self.anchor && self.names.contains(&y)}
                let (name,_) = self.plan.links.iter().find(|(_,link)|link.as_str()==n).unwrap();
                x==self.anchor && y==self.individual(name)
            }
            fn concept(&self,c:&Concept,x:usize)->bool {
                match c {
                    Concept::Top=>true, Concept::Bottom=>false,
                    Concept::Name(n)=> (if n=="A" {self.a} else if n=="B" {self.b} else {panic!("unknown class")}) & (1<<x)!=0,
                    Concept::Nominal(n)=>self.individual(n)==x,
                    Concept::Not(c)=>!self.concept(c,x),
                    Concept::And(cs)=>cs.iter().all(|c|self.concept(c,x)),
                    Concept::Or(cs)=>cs.iter().any(|c|self.concept(c,x)),
                    Concept::Exists(Role::Name(r),c)=>(0..2).any(|y|self.role(r,x,y)&&self.concept(c,y)),
                    Concept::Exists(Role::Inverse(r),c)=>(0..2).any(|y|self.role(r,y,x)&&self.concept(c,y)),
                    Concept::Forall(Role::Name(r),c)=>(0..2).all(|y|!self.role(r,x,y)||self.concept(c,y)),
                    _=>panic!("unexpected generated expression"),
                }
            }
            fn atom(&self,a:&RuleAtom,x:usize,y:usize,z:usize)->bool {
                let term=|t:&RuleTerm| match t {RuleTerm::Var(n) if n=="x"=>x,RuleTerm::Var(n) if n=="y"=>y,RuleTerm::Var(_)=>z,RuleTerm::Ind(n)=>self.individual(n)};
                match a {
                    RuleAtom::Class(c,a)=>self.concept(c,term(a)),
                    RuleAtom::Role(r,a,b)=>self.role(r,term(a),term(b)),
                    RuleAtom::Same(a,b)=>term(a)==term(b),
                    RuleAtom::Diff(a,b)=>term(a)!=term(b),
                    _=>panic!("not an object atom"),
                }
            }
        }
        for rule in candidates {
            let plan=plan(&[rule.clone()],&names,&names,8).unwrap();
            let Axiom::Rule(body,head)=rule else {unreachable!()};
            for identity in 0..4 { for anchor in 0..2 { for a in 0..4 { for b in 0..4 { for r in 0..16 {
                let m=Model{plan:&plan,names:[identity&1,identity>>1],anchor,a,b,r};
                let original=m.names.iter().all(|&x|m.names.iter().all(|&y|m.names.iter().all(|&z|
                    !body.iter().all(|atom|m.atom(atom,x,y,z)) || (!head.is_empty()&&head.iter().all(|atom|m.atom(atom,x,y,z))))));
                let generated=plan.axioms.iter().all(|axiom| match axiom {
                    Axiom::SubClassOf(left,right)=>(0..2).all(|x|!m.concept(left,x)||m.concept(right,x)),
                    Axiom::ConceptAssertion(c,i)=>m.concept(c,m.individual(i)),
                    Axiom::RoleAssertion(r,a,b)=>m.role(r,m.individual(a),m.individual(b)),
                    _=>panic!("unexpected generated axiom"),
                });
                assert_eq!(original,generated,"identity={identity} anchor={anchor} A={a} B={b} R={r}");
            }}}}}
        }
    }

}
