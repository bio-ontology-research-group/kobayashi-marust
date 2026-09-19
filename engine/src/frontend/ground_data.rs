//! Exact elimination of ground, non-functional string-valued data properties.
//! The projected object ontology retains every entailed property-domain fact.
//! A model extends by giving each data property exactly its asserted pairs,
//! closed under the source subproperty relation. No literal becomes an object.
use std::collections::{HashMap, HashSet};
use super::{parse, sexpr::Node};

#[derive(Default)]
pub(super) struct Scan<'a> {
    domains: HashMap<&'a str, Vec<Node<'a>>>,
    ranges: HashMap<&'a str, Vec<Node<'a>>>,
    supers: HashMap<&'a str, Vec<&'a str>>,
    facts: Vec<(&'a str, &'a str, &'a str)>,
    object_mentions: HashSet<&'a str>,
    refused: bool,
}

fn ordinary_iri(s: &str) -> bool {
    s.starts_with('<') && s.ends_with('>') && !s.contains('\\')
        && s[1..s.len()-1].contains(':')
        && !s.starts_with("<http://www.w3.org/2002/07/owl#")
}
fn string_value<'a>(args: &[&Node<'a>]) -> Option<&'a str> {
    let token = args.first()?.as_atom()?;
    let value = token.strip_prefix('"')?.strip_suffix('"')?;
    // Equality of admitted strings is literal equality. Escaped lexical forms
    // are deliberately outside this first decoder, not silently canonicalized.
    if value.contains(['\\', '"']) { return None; }
    match args.get(1).map(|n| n.as_atom()) {
        None if args.len() == 1 => Some(value),
        Some(Some("^^xsd:string" | "^^<http://www.w3.org/2001/XMLSchema#string>"))
            if args.len() == 2 => Some(value),
        _ => None,
    }
}
fn in_range(value: &str, range: &Node<'_>) -> bool {
    match range {
        Node::Atom("xsd:string" | "rdfs:Literal"
            | "<http://www.w3.org/2001/XMLSchema#string>"
            | "<http://www.w3.org/2000/01/rdf-schema#Literal>") => true,
        Node::List("DataOneOf", values) => {
            let mut i = 0;
            let mut found = false;
            while i < values.len() {
                let n = if values.get(i + 1).and_then(Node::as_atom)
                    .is_some_and(|s| s.starts_with("^^") || s.starts_with('@')) { 2 } else { 1 };
                let refs: Vec<_> = values[i..i+n].iter().collect();
                let Some(candidate) = string_value(&refs) else { return false; };
                found |= candidate == value;
                i += n;
            }
            found
        }
        _ => false,
    }
}
fn has_data_use(node: &Node<'_>) -> bool {
    match node {
        Node::Atom(_) => false,
        Node::List(head, args) => head.starts_with("Data")
            || matches!(*head, "HasKey" | "DLSafeRule" | "FunctionalDataProperty"
                | "NegativeDataPropertyAssertion" | "EquivalentDataProperties"
                | "DisjointDataProperties" | "SubDataPropertyOf")
            || args.iter().any(has_data_use),
    }
}
fn collect_atoms<'a>(node: &Node<'a>, atoms: &mut HashSet<&'a str>) {
    match node {
        Node::Atom(atom) => { atoms.insert(atom); }
        Node::List("Annotation", _) => {},
        Node::List(_, args) => { for arg in args { collect_atoms(arg, atoms); } }
    }
}
impl<'a> Scan<'a> {
    pub fn observe(&mut self, node: &Node<'a>) {
        let Node::List(head, children) = node else { return; };
        let args = parse::strip_annotations(children);
        match *head {
            "Declaration" if args.first().is_some_and(|n| n.head() == Some("DataProperty")) => {},
            "DataPropertyDomain" | "DataPropertyRange" => {
                if args.len() != 2 { self.refused = true; return; }
                let Some(p) = args[0].as_atom().filter(|p| ordinary_iri(p)) else {
                    self.refused = true; return;
                };
                if *head == "DataPropertyDomain" {
                    self.refused |= has_data_use(args[1]);
                    collect_atoms(args[1], &mut self.object_mentions);
                    self.domains.entry(p).or_default().push(args[1].clone());
                } else {
                    self.ranges.entry(p).or_default().push(args[1].clone());
                }
            }
            "SubDataPropertyOf" => {
                if args.len() != 2 { self.refused = true; return; }
                match (args[0].as_atom(), args[1].as_atom()) {
                    (Some(p), Some(q)) if ordinary_iri(p) && ordinary_iri(q) => {
                        self.supers.entry(p).or_default().push(q);
                    }
                    _ => self.refused = true,
                }
            }
            "DataPropertyAssertion" => {
                if args.len() < 3 { self.refused = true; return; }
                match (args[0].as_atom(), args[1].as_atom(), string_value(&args[2..])) {
                    (Some(p), Some(i), Some(v)) if ordinary_iri(p) && ordinary_iri(i) => {
                        self.facts.push((p, i, v));
                    }
                    _ => self.refused = true,
                }
            }
            // Annotation values cannot constrain the data-property extension.
            "AnnotationAssertion" | "Annotation" => {},
            "Import" => self.refused = true,
            _ => {
                self.refused |= has_data_use(node);
                collect_atoms(node, &mut self.object_mentions);
            }
        }
    }

    pub fn project(&self, source: &str, expected: u64) -> Option<Vec<Node<'a>>> {
        if self.refused || expected == 0 || self.facts.len() as u64 != expected {
            return None;
        }
        // Builtin abbreviated datatype tokens may not have been rebound.
        let mut tokens = super::sexpr::tokens(source);
        while let Some(token) = tokens.next() {
            if token != "Prefix" { continue; }
            let mut binding = String::new();
            for part in tokens.by_ref() {
                binding.push_str(part);
                if part == ")" { break; }
            }
            for (prefix, iri) in [("xsd", "http://www.w3.org/2001/XMLSchema#"),
                ("rdfs", "http://www.w3.org/2000/01/rdf-schema#"),
                ("owl", "http://www.w3.org/2002/07/owl#")] {
                if binding.starts_with(&format!("({prefix}:"))
                    && binding != format!("({prefix}:=<{iri}>)") { return None; }
            }
        }
        // Source object/data names must not alias through an unexpanded
        // custom prefix. The existing registry uses raw tokens, so admit only
        // full IRIs and the standard OWL builtins in object-side expressions.
        if self.object_mentions.iter().any(|atom| atom.contains(':')
            && !atom.starts_with('<') && !atom.starts_with('"')
            && !matches!(*atom, "owl:Thing" | "owl:Nothing"
                | "owl:topObjectProperty" | "owl:bottomObjectProperty")) {
            return None;
        }
        if self.facts.iter().any(|(p, _, _)| self.object_mentions.contains(p))
            || self.domains.keys().chain(self.ranges.keys()).chain(self.supers.keys())
                .chain(self.supers.values().flatten()).any(|p| self.object_mentions.contains(p)) {
            return None;
        }
        let mut assertions = Vec::new();
        for &(property, individual, value) in &self.facts {
            let mut todo = vec![property];
            let mut seen = HashSet::new();
            while let Some(p) = todo.pop() {
                if !seen.insert(p) { continue; }
                if let Some(ranges) = self.ranges.get(p) {
                    if !ranges.iter().all(|r| in_range(value, r)) { return None; }
                }
                if let Some(domains) = self.domains.get(p) {
                    for domain in domains {
                        assertions.push(Node::List("ClassAssertion",
                            vec![domain.clone(), Node::Atom(individual)]));
                    }
                }
                if let Some(supers) = self.supers.get(p) { todo.extend(supers.iter().copied()); }
            }
        }
        Some(assertions)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn project(source: &str, expected: u64) -> Option<Vec<Node<'_>>> {
        let mut scan = Scan::default();
        parse::for_each_ontology_child(source, |node| { scan.observe(node); Ok(()) }).ok()?;
        scan.project(source, expected)
    }
    #[test]
    fn ground_data_inherits_union_domains_and_finite_string_ranges() {
        let source = r#"Ontology(
          DataPropertyAssertion(<http://e/p> <http://e/a> "yes")
          SubDataPropertyOf(<http://e/p> <http://e/q>)
          SubDataPropertyOf(<http://e/q> <http://e/p>)
          DataPropertyRange(<http://e/q> DataOneOf("yes"^^xsd:string "no"))
          DataPropertyDomain(<http://e/q> ObjectUnionOf(<http://e/A> <http://e/B>)))"#;
        let assertions = project(source, 1).unwrap();
        assert_eq!(assertions.len(), 1);
        assert_eq!(assertions[0].head(), Some("ClassAssertion"));
        assert!(project(source, 2).is_none());
        assert!(project(&source.replace("\"yes\")", "\"other\")"), 1).is_none());
    }
    #[test]
    fn ground_data_rejects_every_unrepresented_interaction() {
        let base = r#"DataPropertyAssertion(<http://e/p> <http://e/a> "v")"#;
        for extra in [
            "FunctionalDataProperty(<http://e/p>)",
            "NegativeDataPropertyAssertion(<http://e/p> <http://e/a> \"v\")",
            "SubClassOf(<http://e/A> DataSomeValuesFrom(<http://e/p> xsd:string))",
            "HasKey(<http://e/A> () (<http://e/p>))",
            "DLSafeRule(Body() Head())",
            "Import(<http://e/other>)",
            "ClassAssertion(e:Alias <http://e/a>)",
            "ObjectPropertyAssertion(<http://e/p> <http://e/a> <http://e/b>)",
        ] {
            assert!(project(&format!("Ontology({base} {extra})"), 1).is_none(), "{extra}");
        }
        assert!(project(&format!("Prefix(xsd:=<http://wrong/>) Ontology({base})"), 1).is_none());
        assert!(project(&format!("Ontology({})", base.replace("<http://e/p>", "<http://www.w3.org/2002/07/owl#topDataProperty>")), 1).is_none());
    }
}
