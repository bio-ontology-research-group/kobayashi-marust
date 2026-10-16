//! Optional positive object-ABox clash proposals, never certificates.
//! Every returned original support must be independently classified by the caller.
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use crate::frontend::sexpr::{Node, Parser};
use crate::source_locality::{fingerprint, Scan};

const MAX_SOURCE: usize = 8 << 20;
const MAX_STATEMENTS: usize = 100_000;
const MAX_NODE: usize = 32_768;
const MAX_LISTS: usize = 256;
const MAX_BODY: usize = 24;
const MAX_RULES: usize = 2_048;
const MAX_FACTS: usize = 50_000;
const MAX_SUPPORT: usize = 64;
const MAX_WORK: usize = 250_000;
type Support = BTreeSet<u128>;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Pred { Class(String), Value(String, String) }
struct Rule { body: Vec<Pred>, head: Vec<Pred>, hash: u128 }
#[derive(Default)]
struct Program {
    initial: Vec<(String, Pred, u128)>, rules: Vec<Rule>,
    domains: BTreeMap<String, Vec<(Vec<Pred>, u128)>>,
    disjoint: BTreeMap<String, Vec<(String, u128)>>,
    functional: BTreeMap<String, u128>,
    different: BTreeMap<String, Vec<(String, u128)>>,
    constraints: usize,
}

fn iri(node: &Node<'_>, prefixes: &BTreeMap<String, String>) -> Option<String> {
    let raw = node.as_atom()?;
    if raw.starts_with("_:") || raw.contains('\\') || raw.starts_with('"') { return None; }
    if let Some(full) = raw.strip_prefix('<').and_then(|s| s.strip_suffix('>')) {
        return (!full.is_empty() && full.contains(':')).then(|| full.to_owned());
    }
    let (prefix, local) = raw.split_once(':')?;
    let base = prefixes.get(&format!("{prefix}:"))?;
    (!local.is_empty()).then(|| format!("{base}{local}"))
}
fn role(node: &Node<'_>, prefixes: &BTreeMap<String, String>) -> Option<String> {
    let name = iri(node, prefixes)?;
    // Universal/fixed-empty roles are unnecessary for this optional fragment.
    (!matches!(name.as_str(), "http://www.w3.org/2002/07/owl#topObjectProperty"
        | "http://www.w3.org/2002/07/owl#bottomObjectProperty")).then_some(name)
}
fn expression(node: &Node<'_>, prefixes: &BTreeMap<String, String>) -> Option<Vec<Pred>> {
    let mut result = match node {
        Node::Atom(_) => vec![Pred::Class(iri(node, prefixes)?)],
        Node::List("ObjectHasValue", args) if args.len() == 2 =>
            vec![Pred::Value(role(&args[0], prefixes)?, iri(&args[1], prefixes)?)],
        Node::List("ObjectIntersectionOf", args) if (2..=MAX_BODY).contains(&args.len()) => {
            let mut out = Vec::new();
            for arg in args { out.extend(expression(arg, prefixes)?); if out.len() > MAX_BODY { return None; } }
            out
        },
        _ => return None,
    };
    result.sort(); result.dedup();
    (!result.is_empty() && result.len() <= MAX_BODY).then_some(result)
}
impl Program {
    fn collect(&mut self, node: &Node<'_>, hash: u128, prefixes: &BTreeMap<String, String>) -> Option<()> {
        let Node::List(head, args) = node else { return Some(()); };
        match (*head, args.as_slice()) {
            ("ClassAssertion", [class @ Node::Atom(_), owner]) => {
                if let (Some(owner), Some(class)) = (iri(owner, prefixes), iri(class, prefixes)) {
                    self.initial.push((owner, Pred::Class(class), hash));
                }
            },
            ("ObjectPropertyAssertion", [property, owner, value]) => {
                if let (Some(owner), Some(property), Some(value)) =
                    (iri(owner, prefixes), role(property, prefixes), iri(value, prefixes)) {
                    self.initial.push((owner, Pred::Value(property, value), hash));
                }
            },
            ("SubClassOf", [left, right]) => {
                if let (Some(body), Some(head)) = (expression(left, prefixes), expression(right, prefixes)) {
                    self.rules.push(Rule { body, head, hash });
                }
            },
            ("EquivalentClasses", items) if (2..=16).contains(&items.len()) => {
                // Skip the whole axiom if any expression is outside this fragment.
                if let Some(forms) = items.iter().map(|n| expression(n, prefixes)).collect::<Option<Vec<_>>>() {
                    for form in forms.iter().skip(1) {
                        self.rules.push(Rule { body: forms[0].clone(), head: form.clone(), hash });
                        self.rules.push(Rule { body: form.clone(), head: forms[0].clone(), hash });
                    }
                }
            },
            ("ObjectPropertyDomain", [property, domain]) => {
                if let (Some(property), Some(domain)) = (role(property, prefixes), expression(domain, prefixes)) {
                    self.domains.entry(property).or_default().push((domain, hash)); self.constraints += 1;
                }
            },
            ("FunctionalObjectProperty", [property]) => {
                if let Some(property) = role(property, prefixes) {
                    self.functional.entry(property).or_insert(hash); self.constraints += 1;
                }
            },
            ("DifferentIndividuals", items) if (2..=64).contains(&items.len()) => {
                if let Some(names) = items.iter().map(|n| iri(n, prefixes)).collect::<Option<Vec<_>>>() {
                    for (i, left) in names.iter().enumerate() { for right in &names[i+1..] {
                        self.constraints += 1; if self.constraints > MAX_RULES { return None; }
                        self.different.entry(left.clone()).or_default().push((right.clone(), hash));
                        self.different.entry(right.clone()).or_default().push((left.clone(), hash));
                    } }
                }
            },
            ("DisjointClasses", items) if (2..=64).contains(&items.len()) => {
                if let Some(names) = items.iter().map(|n| iri(n, prefixes)).collect::<Option<Vec<_>>>() {
                    for (i, left) in names.iter().enumerate() { for right in &names[i+1..] {
                        self.constraints += 1; if self.constraints > MAX_RULES { return None; }
                        self.disjoint.entry(left.clone()).or_default().push((right.clone(), hash));
                        self.disjoint.entry(right.clone()).or_default().push((left.clone(), hash));
                    } }
                }
            },
            _ => {},
        }
        (self.initial.len() <= MAX_FACTS && self.rules.len() <= MAX_RULES
            && self.constraints <= MAX_RULES).then_some(())
    }
}
fn spend(work: &mut usize) -> Option<()> { *work = work.checked_sub(1)?; Some(()) }
fn add(facts: &mut BTreeMap<String, BTreeMap<Pred, Support>>,
    queue: &mut VecDeque<(String, Pred)>, count: &mut usize,
    owner: &str, pred: Pred, support: Support) -> Option<()>
{
    if support.len() > MAX_SUPPORT { return None; }
    let row = facts.entry(owner.to_owned()).or_default();
    if !row.contains_key(&pred) {
        *count += 1; if *count > MAX_FACTS { return None; }
        row.insert(pred.clone(), support); queue.push_back((owner.to_owned(), pred));
    }
    Some(())
}
fn derive(program: &Program) -> Option<Support> {
    let mut watchers: BTreeMap<Pred, Vec<usize>> = BTreeMap::new();
    for (id, rule) in program.rules.iter().enumerate() {
        for pred in &rule.body { watchers.entry(pred.clone()).or_default().push(id); }
    }
    let mut facts = BTreeMap::new(); let mut queue = VecDeque::new(); let mut count = 0;
    for (owner, pred, hash) in &program.initial {
        add(&mut facts, &mut queue, &mut count, owner, pred.clone(), BTreeSet::from([*hash]))?;
    }
    let mut work = MAX_WORK;
    while let Some((owner, pred)) = queue.pop_front() {
        spend(&mut work)?;
        let proof = facts.get(&owner)?.get(&pred)?.clone();
        if let Pred::Class(class) = &pred {
            for (other, hash) in program.disjoint.get(class).into_iter().flatten() {
                spend(&mut work)?;
                if let Some(right) = facts.get(&owner)?.get(&Pred::Class(other.clone())) {
                    let mut support = proof.clone(); support.extend(right); support.insert(*hash);
                    return (support.len() <= MAX_SUPPORT).then_some(support);
                }
            }
        }
        if let Pred::Value(property, value) = &pred {
            if let Some(functional) = program.functional.get(property) {
                // Only an explicit inequality can contradict functionality.
                // Distinct names alone never entail distinct individuals.
                for (other, inequality) in program.different.get(value).into_iter().flatten() {
                    spend(&mut work)?;
                    if let Some(right) = facts.get(&owner)?.get(&Pred::Value(property.clone(), other.clone())) {
                        let mut support = proof.clone(); support.extend(right);
                        support.extend([*functional, *inequality]);
                        return (support.len() <= MAX_SUPPORT).then_some(support);
                    }
                }
            }
            for (heads, hash) in program.domains.get(property).into_iter().flatten() {
                for head in heads {
                    spend(&mut work)?; let mut support = proof.clone(); support.insert(*hash);
                    add(&mut facts, &mut queue, &mut count, &owner, head.clone(), support)?;
                }
            }
        }
        for id in watchers.get(&pred).into_iter().flatten() {
            let rule = &program.rules[*id]; let mut support = Support::from([rule.hash]); let mut ready = true;
            for body in &rule.body {
                spend(&mut work)?;
                if let Some(proof) = facts.get(&owner)?.get(body) { support.extend(proof); }
                else { ready = false; break; }
            }
            if ready {
                for head in &rule.head {
                    spend(&mut work)?;
                    add(&mut facts, &mut queue, &mut count, &owner, head.clone(), support.clone())?;
                }
            }
        }
    }
    None
}

pub(super) fn propose(text: &str, scan: &Scan) -> Option<Vec<u128>> {
    if text.len() > MAX_SOURCE || scan.statements.len() > MAX_STATEMENTS { return None; }
    let mut prefixes: BTreeMap<String, String> = [
        ("owl:", "http://www.w3.org/2002/07/owl#"), ("rdf:", "http://www.w3.org/1999/02/22-rdf-syntax-ns#"),
        ("rdfs:", "http://www.w3.org/2000/01/rdf-schema#"), ("xsd:", "http://www.w3.org/2001/XMLSchema#"),
    ].into_iter().map(|(a,b)| (a.into(),b.into())).collect();
    let mut seen_prefixes = BTreeSet::new();
    for (prefix, iri) in &scan.prefixes {
        if !seen_prefixes.insert(prefix) { return None; } prefixes.insert(prefix.clone(), iri.clone());
    }
    let mut originals = BTreeMap::new(); let mut program = Program::default();
    for statement in &scan.statements {
        let slice = text.get(statement.start..statement.end)?;
        if fingerprint(slice.as_bytes()) != statement.hash { return None; }
        if originals.insert(statement.hash, slice).is_some_and(|old| old != slice) { return None; }
        // The legacy byte tokenizer/parser sees only small ASCII trees.
        if !slice.is_ascii() || slice.len() > MAX_NODE || slice.bytes().filter(|b| *b==b'(').count() > MAX_LISTS { continue; }
        let mut parser = Parser::new(slice);
        if !matches!(parser.peek(), Some("ClassAssertion" | "ObjectPropertyAssertion" | "SubClassOf"
            | "EquivalentClasses" | "ObjectPropertyDomain" | "DisjointClasses"
            | "FunctionalObjectProperty" | "DifferentIndividuals")) { continue; }
        let Ok(node) = parser.parse() else { continue; };
        if parser.peek().is_some() { continue; }
        program.collect(&node, statement.hash, &prefixes)?;
    }
    let support = derive(&program)?;
    let mut seen = BTreeSet::new();
    Some(scan.statements.iter().filter_map(|st|
        (support.contains(&st.hash) && seen.insert(st.hash)).then_some(st.hash)).collect())
}

#[cfg(test)]
mod tests {
    use super::*;
    fn candidate(body: &str) -> Option<Vec<String>> {
        let text = format!("Prefix(:=<urn:object#>) Ontology({body})");
        let scan = crate::source_locality::scan(&text).unwrap();
        propose(&text, &scan).map(|ids| ids.into_iter().map(|id| {
            let st=scan.statements.iter().find(|s|s.hash==id).unwrap(); text[st.start..st.end].to_owned()
        }).collect())
    }
    const BODY: &str = "ClassAssertion(:Seed :a) SubClassOf(:Seed :Left) SubClassOf(:Seed ObjectHasValue(:p :b)) ObjectPropertyDomain(:p :Base) EquivalentClasses(:Joined ObjectIntersectionOf(:Base ObjectHasValue(:p :b))) EquivalentClasses(:Target ObjectIntersectionOf(:Left :Joined)) SubClassOf(:Target :Bad) SubClassOf(:Bad :Edible) SubClassOf(:Base :Liquid) DisjointClasses(:Edible :Liquid)";
    #[test] fn conjunctive_has_value_domain_support_and_repairs() {
        let support=candidate(BODY).unwrap(); assert_eq!(support.len(),10);
        for axiom in &support { assert!(BODY.contains(axiom)); }
        assert!(candidate(&BODY.replace("SubClassOf(:Target :Bad)", "")).is_none());
        assert!(candidate(&BODY.replace("DisjointClasses(:Edible :Liquid)", "")).is_none());
        assert!(candidate(&BODY.replace("ObjectPropertyDomain(:p :Base)", "")).is_none());
        assert!(candidate(&BODY.replace("ObjectHasValue(:p :b)))", "ObjectHasValue(:p :c)))")).is_none());
    }
    #[test] fn aliases_and_asserted_role_domain_are_original_supports() {
        let body="ObjectPropertyAssertion(:p :a :b) ObjectPropertyDomain(:p :A) ClassAssertion(<urn:object#B> :a) DisjointClasses(:A :B)";
        assert_eq!(candidate(body).unwrap().len(),4);
        assert!(candidate(&body.replace("<urn:object#B> :a", "<urn:object#B> :c")).is_none());
    }
    #[test] fn unsupported_annotated_anonymous_and_distinct_individuals_do_not_certify() {
        assert!(candidate("ClassAssertion(:A :a) ClassAssertion(:B :b) DisjointClasses(:A :B)").is_none());
        assert!(candidate("ClassAssertion(:A :a) SubClassOf(:A ObjectUnionOf(:B :C)) DisjointClasses(:A :B)").is_none());
        assert!(candidate("ClassAssertion(Annotation(:note \"x\") :A :a) ClassAssertion(:B :a) DisjointClasses(:A :B)").is_none());
        assert!(candidate("ClassAssertion(:A _:a) ClassAssertion(:B _:a) DisjointClasses(:A :B)").is_none());
    }
    #[test] fn functional_values_require_explicit_inequality_and_exact_supports() {
        let body="ClassAssertion(:Seed :a) SubClassOf(:Seed :Red) EquivalentClasses(:Red ObjectIntersectionOf(:Wine ObjectHasValue(:p :r))) SubClassOf(:Red :White) SubClassOf(:White ObjectHasValue(:p :w)) FunctionalObjectProperty(:p) DifferentIndividuals(:r :w)";
        let support=candidate(body).unwrap(); assert_eq!(support.len(),7);
        for axiom in &support { assert!(body.contains(axiom)); }
        assert!(candidate(&body.replace("DifferentIndividuals(:r :w)", "")).is_none());
        assert!(candidate(&body.replace("FunctionalObjectProperty(:p)", "")).is_none());
        assert!(candidate(&body.replace("SubClassOf(:Red :White)", "")).is_none());
        assert!(candidate(&body.replace("DifferentIndividuals(:r :w)", "DifferentIndividuals(:r :x)")).is_none());
        assert!(candidate(&body.replace("FunctionalObjectProperty(:p)", "FunctionalObjectProperty(:q)")).is_none());
    }
    #[test] fn asserted_inequality_resolves_aliases_without_unique_names() {
        let body="ObjectPropertyAssertion(:p :a :r) ObjectPropertyAssertion(:p :a :w) FunctionalObjectProperty(:p) DifferentIndividuals(<urn:object#r> :w)";
        assert_eq!(candidate(body).unwrap().len(),4);
        assert!(candidate(&body.replace("DifferentIndividuals(<urn:object#r> :w)", "")).is_none());
        assert!(candidate(&body.replace("DifferentIndividuals(<urn:object#r> :w)", "SameIndividual(:r :w)")).is_none());
    }
    #[test] fn duplicate_source_and_collision_control() {
        let text=format!("Prefix(:=<urn:object#>) Ontology({BODY} ClassAssertion(:Seed :a))");
        let mut scan=crate::source_locality::scan(&text).unwrap();
        let ids=propose(&text,&scan).unwrap();assert_eq!(ids.iter().copied().collect::<BTreeSet<_>>().len(),ids.len());
        scan.statements[0].hash=scan.statements[1].hash;assert!(propose(&text,&scan).is_none());
    }
    #[test] fn bounded_unsupported_nodes_decline_without_legacy_parser() {
        assert!(candidate("ClassAssertion(:\u{120} :a) ClassAssertion(:B :a) DisjointClasses(:A :B)").is_none());
        let deep=format!("SubClassOf(:A {}:B{})", "ObjectIntersectionOf(:A ".repeat(300), ")".repeat(300));
        assert!(candidate(&deep).is_none());
        assert!(candidate(&format!("ClassAssertion(:{} :a)","A".repeat(MAX_NODE))).is_none());
        let mut facts=BTreeMap::new();let mut q=VecDeque::new();let mut count=MAX_FACTS;
        assert!(add(&mut facts,&mut q,&mut count,"x",Pred::Class("A".into()),Support::from([1])).is_none());
        let mut count=0;assert!(add(&mut BTreeMap::new(),&mut VecDeque::new(),&mut count,"x",Pred::Class("A".into()),(0..=MAX_SUPPORT as u128).collect()).is_none());
        assert!(spend(&mut 0).is_none());
    }
}
