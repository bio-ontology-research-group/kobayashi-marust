//! Whole-source admission and sparse value closure for finite data membership.
//! This plan is deliberately separate from parser/routing activation: callers
//! must install every binding and every constraint before clearing coverage.
use std::collections::{BTreeMap, BTreeSet};
use super::{ground_data::{in_range, literal_value, ordinary_iri, Value}, parse, sexpr::Node};

#[derive(Default)]
pub(super) struct Scan<'a> {
    values: BTreeMap<&'a str, BTreeSet<Value<'a>>>,
    supers: BTreeSet<(&'a str, &'a str)>,
    domains: Vec<(&'a str, Node<'a>)>,
    ranges: Vec<(&'a str, Node<'a>)>,
    functional: BTreeSet<&'a str>,
    disjoint: BTreeSet<(&'a str, &'a str)>,
    facts: Vec<(&'a str, &'a str, Value<'a>, bool)>,
    bindings: BTreeMap<(&'a str, String), Value<'a>>,
    object_mentions: BTreeSet<&'a str>,
    has_value: bool,
    refused: bool,
}

#[cfg(test)]
mod tests {
    use super::*;
    fn plan(source: &str) -> Option<Plan<'_>> {
        let mut scan = Scan::default();
        parse::for_each_ontology_child(source, |n| { scan.observe(n); Ok(()) }).ok()?;
        scan.finish(source)
    }

    #[test]
    fn source_individual_labels_and_top_data_tautologies_are_exactly_admitted() {
        let base = r#"ClassAssertion(DataHasValue(<http://e/p> "v") _:genid95)"#;
        for extra in [
            "SubDataPropertyOf(<http://e/p> owl:topDataProperty)",
            "SubDataPropertyOf(<http://e/p> <http://www.w3.org/2002/07/owl#topDataProperty>)",
            "ClassAssertion(ObjectHasValue(<http://e/r> _:genid95) <http://e/a>)",
            "ClassAssertion(ObjectOneOf(_:genid95 <http://e/a>) <http://e/b>)",
            "ObjectPropertyAssertion(<http://e/r> _:genid95 _:genid96)",
            "NegativeObjectPropertyAssertion(<http://e/r> _:genid95 _:genid96)",
            "SameIndividual(_:genid95 <http://e/a>)",
            "DifferentIndividuals(_:genid95 _:genid96)",
            "NegativeDataPropertyAssertion(<http://e/p> _:genid95 \"v\")",
        ] { assert!(plan(&format!("Ontology({base} {extra})")).is_some(), "{extra}"); }
        for extra in [
            "SubDataPropertyOf(owl:topDataProperty <http://e/p>)",
            "DataPropertyRange(owl:topDataProperty xsd:string)",
            "ClassAssertion(DataHasValue(owl:topDataProperty \"v\") <http://e/a>)",
            "SubClassOf(_:genid95 <http://e/A>)",
            "ObjectPropertyAssertion(_:genid95 <http://e/a> <http://e/b>)",
            "ClassAssertion(<http://e/A> e:Unexpanded)",
            "ClassAssertion(<http://e/A> _:)",
        ] { assert!(plan(&format!("Ontology({base} {extra})")).is_none(), "{extra}"); }
        assert!(plan(&format!("Prefix(owl:=<http://wrong/>) Ontology({base} SubDataPropertyOf(<http://e/p> owl:topDataProperty))")).is_none());
    }

    #[test]
    fn canonical_membership_closes_cycles_and_inherited_functionality() {
        let source = r#"Ontology(
          SubClassOf(<http://e/A> DataHasValue(<http://e/p> "+01"^^xsd:int))
          SubClassOf(DataHasValue(<http://e/p> "1"^^xsd:integer) <http://e/B>)
          EquivalentDataProperties(<http://e/p> <http://e/q>)
          SubDataPropertyOf(<http://e/q> <http://e/r>)
          FunctionalDataProperty(<http://e/r>)
          DataPropertyAssertion(<http://e/q> <http://e/a> "2"^^xsd:int)
          NegativeDataPropertyAssertion(<http://e/r> <http://e/a> "1"^^xsd:int))"#;
        let p = plan(source).unwrap();
        assert_eq!(p.members.len(), 6);
        assert_eq!(p.bindings.len(), 2);
        assert_eq!(p.bindings.values().collect::<BTreeSet<_>>().len(), 1);
        assert_eq!(p.inclusions.len(), 6);
        assert_eq!(p.bits.len(), 2);
        assert_eq!(p.disjoint.len(), 1);
        assert_eq!(p.facts.iter().map(|f| f.2).collect::<Vec<_>>(), [true, false]);
    }

    #[test]
    fn negative_context_domains_ranges_and_disjoint_properties_are_retained() {
        let source = r#"Ontology(
          SubClassOf(<http://e/A> ObjectComplementOf(DataHasValue(<http://e/p> "yes")))
          DataPropertyDomain(<http://e/p> DataHasValue(<http://e/q> "yes"))
          DataPropertyRange(<http://e/p> DataOneOf("no"))
          DisjointDataProperties(<http://e/p> <http://e/q>)
          NegativeDataPropertyAssertion(<http://e/q> <http://e/a> "yes"))"#;
        let p = plan(source).unwrap();
        assert_eq!(p.members.len(), 2);
        assert_eq!(p.domains.len(), 1);
        assert_eq!(p.empty.len(), 1);
        assert_eq!(p.disjoint.len(), 1);
        assert!(!p.facts[0].2);
    }

    #[test]
    fn whole_source_admission_refuses_unrepresented_interactions() {
        let base = r#"SubClassOf(<http://e/A> DataHasValue(<http://e/p> "yes"))"#;
        for extra in [
            "SubClassOf(<http://e/B> DataSomeValuesFrom(<http://e/q> xsd:string))",
            "HasKey(<http://e/A> () (<http://e/p>))",
            "DLSafeRule(Body() Head())", "Import(<http://e/external>)",
            "DataPropertyRange(<http://e/p> xsd:decimal)",
            "DataPropertyAssertion(<http://e/q> <http://e/a> \"x\"^^<http://e/unknown>)",
            "ObjectPropertyAssertion(<http://e/p> <http://e/a> <http://e/b>)",
            "ClassAssertion(e:Alias <http://e/a>)",
        ] { assert!(plan(&format!("Ontology({base} {extra})")).is_none(), "{extra}"); }
        assert!(plan(&format!("Prefix(xsd:=<http://wrong/>) Ontology({base})")).is_none());
        assert!(plan("Ontology(AnnotationAssertion(<http://e/n> <http://e/a> \"DataHasValue\"))").is_none());
    }
}

pub(super) struct Plan<'a> {
    pub members: BTreeMap<(&'a str, Value<'a>), String>,
    pub bindings: BTreeMap<(&'a str, String), String>,
    pub inclusions: Vec<(String, String)>,
    pub domains: Vec<(String, Node<'a>)>,
    pub empty: BTreeSet<String>,
    pub disjoint: BTreeSet<(String, String)>,
    /// Membership entails a bit marker; opposed bit markers are disjoint.
    pub bits: Vec<(String, String)>,
    pub facts: Vec<(&'a str, String, bool)>,
}

// A conservative subset of OWL anonymous-individual labels. These are source
// identities, not prefixes. Keep them out of the class/property alias check;
// the existing collision-safe registry gives each label one shared identity.
fn anonymous_individual(atom: &str) -> bool {
    atom.strip_prefix("_:").is_some_and(|label| {
        !label.is_empty() && !label.ends_with('.')
            && label.bytes().next().is_some_and(|b| b.is_ascii_alphanumeric() || b == b'_')
            && label.bytes().all(|b| b.is_ascii_alphanumeric() || matches!(b, b'_' | b'-' | b'.'))
    })
}

impl<'a> Scan<'a> {
    fn individual(&mut self, node: &Node<'a>) -> Option<&'a str> {
        let atom = node.as_atom()?;
        (ordinary_iri(atom) || anonymous_individual(atom)).then_some(atom)
    }
    fn property(&mut self, node: &Node<'a>) -> Option<&'a str> {
        let p = node.as_atom().filter(|p| ordinary_iri(p))?;
        self.values.entry(p).or_default();
        Some(p)
    }

    fn expression(&mut self, node: &Node<'a>) -> Option<()> {
        match node {
            Node::Atom(atom) => { self.object_mentions.insert(atom); }
            Node::List("Annotation", _) => {}
            Node::List("ObjectHasValue", args) => {
                let refs = parse::strip_annotations(args);
                if refs.len() != 2 { return None; }
                self.expression(refs[0])?;
                self.individual(refs[1])?;
            }
            Node::List("ObjectOneOf", args) => {
                let refs = parse::strip_annotations(args);
                if refs.is_empty() { return None; }
                for individual in refs { self.individual(individual)?; }
            }
            Node::List("DataHasValue", args) => {
                let refs = parse::strip_annotations(args);
                let p = self.property(refs.first()?)?;
                let v = literal_value(&refs[1..])?;
                let (lexical, used) = parse::glue_literal(&refs, 1)?;
                if used + 1 != refs.len() { return None; }
                self.values.entry(p).or_default().insert(v.clone());
                self.bindings.insert((p, lexical), v);
                self.has_value = true;
            }
            Node::List(head, _) if head.starts_with("Data")
                || matches!(*head, "HasKey" | "DLSafeRule" | "Import"
                    | "FunctionalDataProperty" | "NegativeDataPropertyAssertion"
                    | "EquivalentDataProperties" | "DisjointDataProperties"
                    | "SubDataPropertyOf") => return None,
            Node::List(_, args) => { for arg in args { self.expression(arg)?; } }
        }
        Some(())
    }

    fn observe_checked(&mut self, node: &Node<'a>) -> Option<()> {
        let Node::List(head, children) = node else { return Some(()); };
        let args = parse::strip_annotations(children);
        match *head {
            "Annotation" | "AnnotationAssertion" => {}
            "Declaration" if args.first().is_some_and(|n| n.head() == Some("DataProperty")) => {
                if args.len() != 1 { return None; }
                let Node::List(_, p) = args[0] else { return None; };
                if p.len() != 1 { return None; }
                self.property(&p[0])?;
            }
            "ClassAssertion" => {
                if args.len() != 2 { return None; }
                self.expression(args[0])?;
                self.individual(args[1])?;
            }
            "ObjectPropertyAssertion" | "NegativeObjectPropertyAssertion" => {
                if args.len() != 3 { return None; }
                self.expression(args[0])?;
                self.individual(args[1])?;
                self.individual(args[2])?;
            }
            "SameIndividual" | "DifferentIndividuals" => {
                if args.len() < 2 { return None; }
                for individual in args { self.individual(individual)?; }
            }
            "FunctionalDataProperty" => {
                if args.len() != 1 { return None; }
                let p = self.property(args[0])?;
                self.functional.insert(p);
            }
            "DataPropertyDomain" | "DataPropertyRange" => {
                if args.len() != 2 { return None; }
                let p = self.property(args[0])?;
                if *head == "DataPropertyDomain" {
                    self.expression(args[1])?;
                    self.domains.push((p, args[1].clone()));
                } else { self.ranges.push((p, args[1].clone())); }
            }
            "SubDataPropertyOf" | "EquivalentDataProperties" | "DisjointDataProperties" => {
                if args.len() < 2 || (*head == "SubDataPropertyOf" && args.len() != 2) { return None; }
                if *head == "SubDataPropertyOf" && matches!(args[1].as_atom(),
                    Some("owl:topDataProperty" | "<http://www.w3.org/2002/07/owl#topDataProperty>")) {
                    // Every ordinary data relation is a subset of O x D. This
                    // tautology introduces no value demand or propagation edge.
                    // Other uses of top remain refused; finish checks owl binding.
                    self.property(args[0])?;
                    return Some(());
                }
                let ps: Vec<_> = args.iter().map(|n| self.property(n)).collect::<Option<_>>()?;
                if *head == "SubDataPropertyOf" { self.supers.insert((ps[0], ps[1])); }
                else {
                    for i in 0..ps.len() { for j in i+1..ps.len() {
                        if *head == "EquivalentDataProperties" {
                            self.supers.insert((ps[i], ps[j]));
                            self.supers.insert((ps[j], ps[i]));
                        } else { self.disjoint.insert((ps[i], ps[j])); }
                    }}
                }
            }
            "DataPropertyAssertion" | "NegativeDataPropertyAssertion" => {
                if args.len() < 3 { return None; }
                let p = self.property(args[0])?;
                let owner = self.individual(args[1])?;
                let value = literal_value(&args[2..])?;
                self.values.entry(p).or_default().insert(value.clone());
                self.facts.push((p, owner, value, *head == "DataPropertyAssertion"));
            }
            _ => self.expression(node)?,
        }
        Some(())
    }

    pub fn observe(&mut self, node: &Node<'a>) {
        if self.observe_checked(node).is_none() { self.refused = true; }
    }

    pub fn finish(mut self, source: &str) -> Option<Plan<'a>> {
        if self.refused || !self.has_value { return None; }
        // Full source IRIs avoid aliasing through an unexpanded custom prefix.
        if self.object_mentions.iter().any(|atom| atom.contains(':')
            && !atom.starts_with('<') && !atom.starts_with('"')
            && !matches!(*atom, "owl:Thing" | "owl:Nothing"
                | "owl:topObjectProperty" | "owl:bottomObjectProperty")) { return None; }
        if self.values.keys().any(|p| self.object_mentions.contains(p)) { return None; }
        let mut tokens = super::sexpr::tokens(source);
        while let Some(token) = tokens.next() {
            if token != "Prefix" { continue; }
            let mut binding = String::new();
            for part in tokens.by_ref() { binding.push_str(part); if part == ")" { break; } }
            for (prefix, iri) in [("xsd", "http://www.w3.org/2001/XMLSchema#"),
                ("rdfs", "http://www.w3.org/2000/01/rdf-schema#"),
                ("owl", "http://www.w3.org/2002/07/owl#")] {
                if binding.starts_with(&format!("({prefix}:"))
                    && binding != format!("({prefix}:=<{iri}>)") { return None; }
            }
        }
        loop {
            let mut changed = false;
            for (p, q) in &self.supers {
                let from = self.values[p].clone();
                let to = self.values.get_mut(q)?;
                let before = to.len();
                to.extend(from);
                changed |= before != to.len();
            }
            if !changed { break; }
        }
        let mut plan = Plan { members: BTreeMap::new(), bindings: BTreeMap::new(),
            inclusions: vec![], domains: vec![], empty: BTreeSet::new(),
            disjoint: BTreeSet::new(), bits: vec![], facts: vec![] };
        for (pid, (p, values)) in self.values.iter().enumerate() {
            for (vid, value) in values.iter().enumerate() {
                let name = format!("__km_data_member_p{pid}_v{vid}");
                plan.members.insert((*p, value.clone()), name.clone());
                if self.functional.contains(p) && values.len() > 1 {
                    let width = usize::BITS - (values.len() - 1).leading_zeros();
                    for bit in 0..width {
                        let prefix = format!("__km_data_member_p{pid}_b{bit}");
                        plan.bits.push((name.clone(), format!("{prefix}_{}", (vid >> bit) & 1)));
                        plan.disjoint.insert((format!("{prefix}_0"), format!("{prefix}_1")));
                    }
                }
            }
        }
        for ((p, text), v) in self.bindings {
            plan.bindings.insert((p, text), plan.members[&(p, v)].clone());
        }
        for (p, q) in self.supers {
            for v in &self.values[p] {
                plan.inclusions.push((plan.members[&(p, v.clone())].clone(), plan.members[&(q, v.clone())].clone()));
            }
        }
        for (p, domain) in self.domains {
            for v in &self.values[p] { plan.domains.push((plan.members[&(p, v.clone())].clone(), domain.clone())); }
        }
        for (p, range) in self.ranges {
            for v in &self.values[p] {
                if !in_range(v, &range)? { plan.empty.insert(plan.members[&(p, v.clone())].clone()); }
            }
        }
        for (p, q) in self.disjoint {
            for v in self.values[p].intersection(&self.values[q]) {
                plan.disjoint.insert((plan.members[&(p, v.clone())].clone(), plan.members[&(q, v.clone())].clone()));
            }
        }
        for (p, owner, v, positive) in self.facts {
            plan.facts.push((owner, plan.members[&(p, v)].clone(), positive));
        }
        Some(plan)
    }
}
