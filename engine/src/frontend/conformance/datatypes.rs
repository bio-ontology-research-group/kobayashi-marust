//! Datatype-definition constraints from OWL 2 Structural Specification 11.2.
use std::collections::{BTreeMap, BTreeSet};
use super::{expand, Node};

pub(super) fn builtin(name: &str) -> bool {
    if let Some(local) = name.strip_prefix("http://www.w3.org/2001/XMLSchema#") {
        return matches!(local, "decimal" | "integer" | "nonNegativeInteger" | "nonPositiveInteger"
            | "positiveInteger" | "negativeInteger" | "long" | "int" | "short" | "byte"
            | "unsignedLong" | "unsignedInt" | "unsignedShort" | "unsignedByte"
            | "double" | "float" | "string" | "normalizedString" | "token" | "language"
            | "Name" | "NCName" | "NMTOKEN" | "boolean" | "hexBinary" | "base64Binary"
            | "anyURI" | "dateTime" | "dateTimeStamp");
    }
    matches!(name, "http://www.w3.org/2002/07/owl#real" | "http://www.w3.org/2002/07/owl#rational"
        | "http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral"
        | "http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral"
        | "http://www.w3.org/2000/01/rdf-schema#Literal")
}

fn dependencies(node: &Node<'_>, prefixes: &BTreeMap<String, String>, out: &mut BTreeSet<String>) {
    match node {
        Node::Atom(name) => { out.insert(expand(name, prefixes)); }
        Node::List("DatatypeRestriction", args) => {
            if let Some(first) = args.first() { dependencies(first, prefixes, out); }
        }
        Node::List("DataIntersectionOf" | "DataUnionOf" | "DataComplementOf", args) => {
            for arg in args { dependencies(arg, prefixes, out); }
        }
        // DataOneOf operands are literals, not datatype expressions.
        _ => {}
    }
}

fn canonical(node: &Node<'_>, prefixes: &BTreeMap<String, String>) -> String {
    match node {
        Node::Atom(name) => expand(name, prefixes),
        Node::List(head, args) => {
            let mut parts: Vec<_> = args.iter().map(|arg| canonical(arg, prefixes)).collect();
            if matches!(*head, "DataUnionOf" | "DataIntersectionOf") {
                parts.sort();
                parts.dedup();
            }
            format!("{head}({})", parts.join(" "))
        }
    }
}

#[derive(Default)]
struct Definitions {
    used: BTreeSet<String>,
    restricted: BTreeSet<String>,
    definitions: BTreeMap<String, BTreeMap<String, BTreeSet<String>>>,
}
impl Definitions {
    fn observe(&mut self, node: &Node<'_>, prefixes: &BTreeMap<String, String>) {
        let Node::List(head, args) = node else { return };
        if matches!(*head, "Annotation" | "AnnotationAssertion" | "Declaration") { return; }
        let logical: Vec<_> = args.iter().filter(|n| n.head() != Some("Annotation")).collect();
        match (*head, logical.as_slice()) {
            ("DatatypeRestriction", [Node::Atom(name), ..]) => {
                self.restricted.insert(expand(name, prefixes));
            }
            ("DatatypeDefinition", [Node::Atom(name), range]) => {
                let name = expand(name, prefixes);
                let mut deps = BTreeSet::new();
                dependencies(range, prefixes, &mut deps);
                self.used.extend(deps.iter().cloned());
                self.definitions.entry(name).or_default().insert(canonical(range, prefixes), deps);
            }
            ("DataPropertyRange", [_,range]) | ("DataRangeAtom", [range,..]) => dependencies(range, prefixes, &mut self.used),
            ("DataSomeValuesFrom" | "DataAllValuesFrom", _) => {
                if let Some(range) = logical.last() { dependencies(range, prefixes, &mut self.used); }
            }
            ("DataMinCardinality" | "DataMaxCardinality" | "DataExactCardinality", [_,_,range]) => dependencies(range, prefixes, &mut self.used),
            _ => {}
        }
        for arg in args { self.observe(arg, prefixes); }
    }
    fn finish(&self) -> Result<(), String> {
        for (name, definitions) in &self.definitions {
            if builtin(name) { return Err(format!("invalid OWL 2 DL input: datatype definition redefines built-in <{name}>")); }
            if ["http://www.w3.org/2001/XMLSchema#", "http://www.w3.org/2002/07/owl#", "http://www.w3.org/2000/01/rdf-schema#", "http://www.w3.org/1999/02/22-rdf-syntax-ns#"].iter().any(|ns| name.starts_with(ns)) {
                return Err(format!("invalid OWL 2 DL input: custom datatype <{name}> uses reserved vocabulary"));
            }
            if definitions.len() != 1 { return Err(format!("invalid OWL 2 DL input: datatype <{name}> has multiple definitions")); }
            let mut pending: Vec<_> = definitions.values().flat_map(|v| v.iter().cloned()).collect();
            let mut seen = BTreeSet::new();
            while let Some(dependency) = pending.pop() {
                if dependency == *name { return Err(format!("invalid OWL 2 DL input: cyclic datatype definition involving <{name}>")); }
                if !seen.insert(dependency.clone()) { continue; }
                if let Some(next) = self.definitions.get(&dependency) {
                    pending.extend(next.values().flat_map(|v| v.iter().cloned()));
                }
            }
        }
        for name in &self.restricted {
            if self.definitions.contains_key(name) {
                return Err(format!("invalid OWL 2 DL input: defined datatype <{name}> supports no facets and cannot be the base of DatatypeRestriction"));
            }
        }
        for name in &self.used {
            if !builtin(name) && !self.definitions.contains_key(name) {
                return Err(format!("invalid OWL 2 DL input: data range <{name}> is outside the OWL 2 datatype map and has no datatype definition"));
            }
        }
        Ok(())
    }
}

pub(super) fn check(text: &str, prefixes: &BTreeMap<String, String>) -> Result<(), String> {
    let mut definitions = Definitions::default();
    crate::frontend::parse::for_each_ontology_child(text, |node| {
        check_top_property(node, prefixes).map_err(crate::frontend::parse::OutOfFragment)?;
        check_arity(node).map_err(crate::frontend::parse::OutOfFragment)?;
        super::facets::check(node, prefixes).map_err(crate::frontend::parse::OutOfFragment)?;
        definitions.observe(node, prefixes);
        Ok(())
    }).map_err(|e| e.0)?;
    definitions.finish()
}

/// Every datatype and data-range constructor in the OWL 2 map is unary.
/// The functional grammar's multiple-property forms are extension hooks, not
/// permission to use a unary range as a relation over a tuple of values.
fn check_arity(node: &Node<'_>) -> Result<(), String> {
    let Node::List(head, args) = node else { return Ok(()) };
    if matches!(*head, "DataSomeValuesFrom" | "DataAllValuesFrom") && args.len() != 2 {
        return Err(format!("invalid OWL 2 DL input: {head} has {} data properties but its data range is unary; the number of properties must equal the range arity (1)",
            args.len().saturating_sub(1)));
    }
    for arg in args { check_arity(arg)?; }
    Ok(())
}

/// Section 11.2 restricts topDataProperty in logical axioms to the superproperty
/// position of SubDataPropertyOf. Declarations and annotation content impose no
/// logical constraints. This check follows the normative rule even though
/// OWLAPI 4.5's profile checker does not report every violating use.
fn check_top_property(node: &Node<'_>, prefixes: &BTreeMap<String, String>) -> Result<(), String> {
    match node {
        Node::Atom(name) if expand(name, prefixes) == "http://www.w3.org/2002/07/owl#topDataProperty" =>
            Err("invalid OWL 2 DL input: owl:topDataProperty may occur in logical axioms only as the superproperty of SubDataPropertyOf".into()),
        Node::List("Declaration" | "Annotation" | "AnnotationAssertion" | "AnnotationPropertyDomain" | "AnnotationPropertyRange" | "SubAnnotationPropertyOf", _) => Ok(()),
        Node::List("SubDataPropertyOf", args) => {
            let logical: Vec<_> = args.iter().filter(|n| n.head() != Some("Annotation")).collect();
            if let [sub, _sup] = logical.as_slice() { check_top_property(sub, prefixes) }
            else { for arg in args { check_top_property(arg, prefixes)?; } Ok(()) }
        }
        Node::List(_, args) => { for arg in args { check_top_property(arg, prefixes)?; } Ok(()) }
        _ => Ok(()),
    }
}

#[cfg(test)]
mod tests {
    use super::super::check_source;
    #[test]
    fn unary_data_ranges_cannot_constrain_multiple_properties() {
        for constructor in ["DataSomeValuesFrom", "DataAllValuesFrom"] {
            for range in ["xsd:string", "DataUnionOf(xsd:string xsd:integer)",
                "DataComplementOf(xsd:integer)", "DataOneOf(\"a\" \"b\")",
                "DatatypeRestriction(xsd:string xsd:minLength \"1\"^^xsd:integer)"] {
                let invalid = format!("Ontology(SubClassOf(:A ObjectSomeValuesFrom(:r {constructor}(:p :q {range}))))");
                assert!(check_source(&invalid).unwrap_err().contains("range arity"), "{invalid}");
                check_source(&format!("Ontology(SubClassOf(:A {constructor}(:p {range})))")).unwrap();
            }
        }
        assert!(check_source("Ontology(DatatypeDefinition(:D xsd:string) SubClassOf(:A DataAllValuesFrom(:p :q :D)))").unwrap_err().contains("range arity"));
    }

    #[test]
    fn defined_datatypes_cannot_be_restricted_even_when_their_base_supports_facets() {
        for axioms in [
            "DatatypeDefinition(:D xsd:integer) DataPropertyRange(:p DatatypeRestriction(:D xsd:minInclusive 1))",
            "DataPropertyRange(:p DatatypeRestriction(:D xsd:minInclusive 1)) DatatypeDefinition(:D xsd:integer)",
            "DatatypeDefinition(:D xsd:integer) DLSafeRule(Body(DataRangeAtom(DatatypeRestriction(:D xsd:minInclusive 1) Variable(:x))) Head(ClassAtom(:A :a)))",
        ] {
            // Functional syntax uses explicitly typed literals, not bare numbers.
            let source = format!("Ontology({axioms})").replace(" 1)", " \"1\"^^xsd:integer)");
            assert!(check_source(&source).unwrap_err().contains("supports no facets"), "{source}");
        }
        check_source("Ontology(DatatypeDefinition(:D DatatypeRestriction(xsd:integer xsd:minInclusive \"1\"^^xsd:integer)) DataPropertyRange(:p :D))").unwrap();
    }
    #[test]
    fn datatype_definitions_must_be_acyclic_and_unique() {
        for axioms in ["DatatypeDefinition(:D :D)",
            "DatatypeDefinition(:D :E) DatatypeDefinition(:E DataUnionOf(:D xsd:string))",
            "DatatypeDefinition(:D xsd:string) DatatypeDefinition(:D xsd:integer)",
            "DatatypeDefinition(xsd:string xsd:integer)"] {
            assert!(check_source(&format!("Ontology({axioms})")).is_err(), "{axioms}");
        }
    }
    #[test]
    fn used_datatypes_need_definitions_but_declarations_alone_do_not() {
        assert!(check_source("Ontology(Declaration(Datatype(:D)))").is_ok());
        assert!(check_source("Ontology(DataPropertyRange(:p :D))").unwrap_err().contains("no datatype definition"));
        assert!(check_source("Ontology(DatatypeDefinition(:D xsd:string) DataPropertyRange(:p :D))").is_ok());
        assert!(check_source("Ontology(DatatypeDefinition(:D xsd:string) DatatypeDefinition(:D xsd:string))").is_ok());
        assert!(check_source("Ontology(SubClassOf(:A DataSomeValuesFrom(:p :D)))").is_err());
        assert!(check_source("Ontology(DLSafeRule(Body(DataRangeAtom(:D Variable(:x))) Head(ClassAtom(:A :a))))").is_err());
    }
    #[test]
    fn reordered_datatype_unions_are_the_same_definition() {
        assert!(check_source("Ontology(DatatypeDefinition(:D DataUnionOf(xsd:string xsd:integer)) DatatypeDefinition(:D DataUnionOf(xsd:integer xsd:string)))").is_ok());
    }
    #[test]
    fn top_data_property_is_restricted_to_superproperty_position() {
        for axiom in ["DataPropertyRange(owl:topDataProperty xsd:string)",
            "SubDataPropertyOf(owl:topDataProperty :p)",
            "DataPropertyAssertion(owl:topDataProperty :a \"x\")",
            "SubClassOf(:A DataSomeValuesFrom(owl:topDataProperty xsd:string))"] {
            assert!(check_source(&format!("Ontology({axiom})")).unwrap_err().contains("superproperty"));
        }
        assert!(check_source("Ontology(Declaration(DataProperty(owl:topDataProperty)) SubDataPropertyOf(:p owl:topDataProperty))").is_ok());
    }
}
