//! Source obligations for model-preserving finite concrete-rule grounding.
//! The gate rejects data-value generators, imports, keys, negative data facts,
//! property hierarchies and unrecognized syntax. It does not publish rules.
use super::sexpr::{Node, Parser};
use std::collections::BTreeSet;

/// Source vocabulary, before object and data properties share the worker's
/// role table. Keep full names so local-name collisions cannot change sorts.
#[derive(Default)]
pub(super) struct PropertyKinds {
    pub(super) object: BTreeSet<String>,
    pub(super) data: BTreeSet<String>,
    invalid: bool,
}
impl PropertyKinds {
    fn name(token: &str) -> Option<String> {
        if let Some(name) = token.strip_prefix('<').and_then(|s| s.strip_suffix('>')) {
            return (!name.is_empty()).then(|| name.to_owned());
        }
        // General CURIE expansion is not provided by this frontend. Only
        // builtin properties have a spelling-independent interpretation here.
        if !matches!(token, "owl:topObjectProperty" | "owl:bottomObjectProperty"
            | "owl:topDataProperty" | "owl:bottomDataProperty") { return None; }
        for (prefix, base) in [("owl:", "http://www.w3.org/2002/07/owl#"),
            ("rdf:", "http://www.w3.org/1999/02/22-rdf-syntax-ns#"),
            ("rdfs:", "http://www.w3.org/2000/01/rdf-schema#"),
            ("xsd:", "http://www.w3.org/2001/XMLSchema#")] {
            if let Some(local) = token.strip_prefix(prefix) { return Some(format!("{base}{local}")); }
        }
        None
    }
    fn role(node: &Node<'_>, names: &mut BTreeSet<String>) -> bool {
        match node {
            Node::Atom(token) => match Self::name(token) {
                Some(name) => { names.insert(name); true }
                None => false,
            },
            Node::List("ObjectInverseOf", args) if args.len() == 1 => Self::role(&args[0], names),
            Node::List("ObjectPropertyChain", args) if args.len() >= 2 => args.iter().all(|n| Self::role(n, names)),
            _ => false,
        }
    }
    fn observe(&mut self, node: &Node<'_>) {
        let Node::List(kind, arguments) = node else { return; };
        if matches!(*kind, "Annotation" | "AnnotationAssertion") { return; }
        let args = super::parse::strip_annotations(arguments);
        let object_all = matches!(*kind, "SubObjectPropertyOf" | "EquivalentObjectProperties"
            | "InverseObjectProperties" | "DisjointObjectProperties");
        let object_first = matches!(*kind, "ObjectProperty" | "ObjectPropertyAssertion"
            | "NegativeObjectPropertyAssertion" | "ObjectPropertyDomain" | "ObjectPropertyRange"
            | "FunctionalObjectProperty" | "InverseFunctionalObjectProperty"
            | "TransitiveObjectProperty" | "SymmetricObjectProperty" | "AsymmetricObjectProperty"
            | "ReflexiveObjectProperty" | "IrreflexiveObjectProperty" | "ObjectPropertyAtom"
            | "ObjectSomeValuesFrom" | "ObjectAllValuesFrom" | "ObjectHasValue" | "ObjectHasSelf");
        if object_all {
            self.invalid |= args.len() < 2 || !args.iter().all(|n| Self::role(n, &mut self.object));
        } else if object_first {
            self.invalid |= args.first().is_none_or(|n| !Self::role(n, &mut self.object));
        } else if matches!(*kind, "ObjectMinCardinality" | "ObjectMaxCardinality" | "ObjectExactCardinality") {
            self.invalid |= args.get(1).is_none_or(|n| !Self::role(n, &mut self.object));
        } else if matches!(*kind, "DataProperty" | "DataPropertyAssertion" | "DataPropertyDomain"
            | "DataPropertyRange" | "FunctionalDataProperty" | "DataPropertyAtom") {
            self.invalid |= args.first().and_then(|n| n.as_atom()).and_then(Self::name)
                .map(|name| { self.data.insert(name); }).is_none();
        }
        for arg in args { self.observe(arg); }
    }
}

fn render_node(node: &Node<'_>) -> String {
    match node {
        Node::Atom(token) => (*token).to_owned(),
        Node::List(kind, args) => format!("{}({})", kind,
            args.iter().map(render_node).collect::<Vec<_>>().join(" ")),
    }
}

pub(super) struct Scan {
    valid: bool,
    fresh_object_safe: bool,
    property_kinds: PropertyKinds,
    pub(super) values: Vec<String>,
    classes: BTreeSet<String>,
    class_axioms: Vec<String>,
    object_assertions: Vec<String>,
    object_properties: Vec<String>,
    data_axioms: Vec<String>,
    rules: Vec<String>,
}
impl Scan {
    pub(super) fn new(text: &str) -> Self {
        let mut parser = Parser::new(text);
        let mut valid = true;
        while parser.peek() == Some("Prefix") {
            let Ok(Node::List("Prefix", args)) = parser.parse() else { valid = false; break; };
            let Some(parts): Option<Vec<_>> = args.iter().map(Node::as_atom).collect() else { valid = false; break; };
            valid &= matches!(parts.concat().as_str(),
                "owl:=<http://www.w3.org/2002/07/owl#>"
                | "rdf:=<http://www.w3.org/1999/02/22-rdf-syntax-ns#>"
                | "rdfs:=<http://www.w3.org/2000/01/rdf-schema#>"
                | "xsd:=<http://www.w3.org/2001/XMLSchema#>"
                | "xml:=<http://www.w3.org/XML/1998/namespace>");
        }
        valid &= parser.peek() == Some("Ontology");
        Self { valid, fresh_object_safe: true, property_kinds: PropertyKinds::default(), values: Vec::new(), classes: BTreeSet::new(), class_axioms: Vec::new(), object_assertions: Vec::new(), object_properties: Vec::new(), data_axioms: Vec::new(), rules: Vec::new() }
    }
    pub(super) fn observe(&mut self, node: &Node<'_>) {
        let Node::List(kind, arguments) = node else {
            self.valid &= matches!(node, Node::Atom(s) if s.starts_with('<') && s.ends_with('>'));
            return;
        };
        if matches!(*kind, "Annotation" | "AnnotationAssertion") { return; }
        self.property_kinds.observe(node);
        if matches!(*kind, "ClassAssertion" | "ObjectPropertyAssertion" |
            "NegativeObjectPropertyAssertion" | "SameIndividual" | "DifferentIndividuals") {
            self.object_assertions.push(render_node(node));
        }
        if matches!(*kind, "SubObjectPropertyOf" | "EquivalentObjectProperties" |
            "InverseObjectProperties" | "DisjointObjectProperties" | "ObjectPropertyDomain" |
            "ObjectPropertyRange" | "FunctionalObjectProperty" | "InverseFunctionalObjectProperty" |
            "TransitiveObjectProperty" | "SymmetricObjectProperty" | "AsymmetricObjectProperty" |
            "ReflexiveObjectProperty" | "IrreflexiveObjectProperty") {
            self.object_properties.push(render_node(node));
        }
        if matches!(*kind, "DataPropertyAssertion" | "DataPropertyDomain" |
            "DataPropertyRange" | "FunctionalDataProperty") {
            self.data_axioms.push(render_node(node));
        }
        if *kind == "DLSafeRule" { self.rules.push(render_node(node)); }
        self.observe_classes(node);
        // A class-query witness may have an arbitrary class valuation but no
        // incident object/data edges. Only propositional class constraints
        // survive that construction without additional model obligations.
        // Keep this separate from finite-data grounding: grounding itself can
        // be sound for sources whose taxonomy cannot be projected this way.
        fn fresh_safe(node: &Node<'_>) -> bool {
            match node {
                Node::Atom(name) => !matches!(*name,
                    "owl:topObjectProperty" | "owl:topDataProperty"
                    | "<http://www.w3.org/2002/07/owl#topObjectProperty>"
                    | "<http://www.w3.org/2002/07/owl#topDataProperty>"),
                Node::List(kind, args) => !matches!(*kind,
                    "ObjectSomeValuesFrom" | "ObjectAllValuesFrom" | "ObjectHasValue"
                    | "ObjectHasSelf" | "ObjectOneOf" | "ObjectMinCardinality"
                    | "ObjectMaxCardinality" | "ObjectExactCardinality"
                    | "ReflexiveObjectProperty") && args.iter().all(fresh_safe),
            }
        }
        fn exact_named_terms(node: &Node<'_>) -> bool {
            fn iri(node: &Node<'_>) -> bool {
                matches!(node, Node::Atom(name) if name.starts_with('<') && name.ends_with('>'))
            }
            fn term(node: &Node<'_>) -> bool {
                iri(node) || matches!(node, Node::List("Variable", args) if args.len() == 1 && iri(&args[0]))
            }
            let Node::List(kind, raw) = node else { return true; };
            if matches!(*kind, "Annotation" | "AnnotationAssertion") { return true; }
            let args = super::parse::strip_annotations(raw);
            let exact = match *kind {
                "NamedIndividual" | "Variable" => args.len() == 1 && iri(args[0]),
                "ClassAssertion" | "DataPropertyAssertion" => args.get(1).is_some_and(|n| iri(n)),
                "ObjectPropertyAssertion" | "NegativeObjectPropertyAssertion" =>
                    args.len() == 3 && iri(args[1]) && iri(args[2]),
                "SameIndividual" | "DifferentIndividuals" => args.iter().all(|n| iri(n)),
                "ClassAtom" | "DataPropertyAtom" => args.get(1).is_some_and(|n| term(n)),
                "ObjectPropertyAtom" => args.len() == 3 && term(args[1]) && term(args[2]),
                "SameIndividualAtom" | "DifferentIndividualsAtom" => args.iter().all(|n| term(n)),
                _ => true,
            };
            exact && args.iter().all(|n| exact_named_terms(n))
        }
        self.fresh_object_safe &= fresh_safe(node) && exact_named_terms(node);
        self.valid &= matches!(*kind,
            "Declaration" | "SubClassOf" | "EquivalentClasses" | "DisjointClasses"
            | "DisjointUnion" | "ClassAssertion" | "ObjectPropertyAssertion"
            | "NegativeObjectPropertyAssertion" | "SameIndividual" | "DifferentIndividuals"
            | "SubObjectPropertyOf" | "EquivalentObjectProperties" | "InverseObjectProperties"
            | "ObjectPropertyDomain" | "ObjectPropertyRange" | "FunctionalObjectProperty"
            | "InverseFunctionalObjectProperty" | "TransitiveObjectProperty"
            | "SymmetricObjectProperty" | "AsymmetricObjectProperty" | "ReflexiveObjectProperty"
            | "IrreflexiveObjectProperty" | "DisjointObjectProperties" | "DataPropertyAssertion"
            | "DataPropertyDomain" | "DataPropertyRange" | "FunctionalDataProperty" | "DLSafeRule");
        let args = super::parse::strip_annotations(arguments);
        fn safe(node: &Node<'_>) -> bool {
            match node {
                Node::Atom(_) => true,
                Node::List(kind, args) => matches!(*kind,
                    "Class" | "ObjectProperty" | "DataProperty" | "NamedIndividual" | "Datatype"
                    | "ObjectIntersectionOf" | "ObjectUnionOf" | "ObjectComplementOf"
                    | "ObjectSomeValuesFrom" | "ObjectAllValuesFrom" | "ObjectHasValue"
                    | "ObjectHasSelf" | "ObjectOneOf" | "ObjectMinCardinality"
                    | "ObjectMaxCardinality" | "ObjectExactCardinality" | "ObjectInverseOf"
                    | "ObjectPropertyChain" | "Body" | "Head" | "ClassAtom" | "ObjectPropertyAtom"
                    | "DataPropertyAtom" | "SameIndividualAtom" | "DifferentIndividualsAtom"
                    | "BuiltInAtom" | "Variable") && args.iter().all(safe),
            }
        }
        self.valid &= args.iter().all(|node| safe(node));
        if *kind == "DataPropertyAssertion" {
            let literal = (|| {
                if !args.first()?.as_atom()?.starts_with('<') || !args.get(1)?.as_atom()?.starts_with('<') { return None; }
                let (value, used) = super::parse::glue_literal(&args, 2)?;
                if args.len() != 2 + used || !super::data_rules::exact_rule_literal(&value) { return None; }
                Some(value)
            })();
            if let Some(value) = literal { self.values.push(value); }
            else { self.valid = false; }
        }
    }
    fn observe_classes(&mut self, node: &Node<'_>) {
        fn expression(node: &Node<'_>, classes: &mut BTreeSet<String>) {
            match node {
                Node::Atom(name) => { classes.insert((*name).to_owned()); }
                Node::List("ObjectIntersectionOf" | "ObjectUnionOf" | "ObjectComplementOf", args) => {
                    for arg in args { expression(arg, classes); }
                }
                _ => {}
            }
        }
        let Node::List(kind, raw) = node else { return; };
        let args = super::parse::strip_annotations(raw);
        match *kind {
            "SubClassOf" | "EquivalentClasses" | "DisjointClasses" | "DisjointUnion" => {
                for arg in &args { expression(arg, &mut self.classes); }
                self.class_axioms.push(format!("{}({})", kind, args.iter().map(|arg| render_node(arg)).collect::<Vec<_>>().join(" ")));
            }
            "Class" | "ClassAssertion" | "ClassAtom" => {
                if let Some(arg) = args.first() { expression(arg, &mut self.classes); }
            }
            "ObjectPropertyDomain" | "ObjectPropertyRange" | "DataPropertyDomain" => {
                if let Some(arg) = args.get(1) { expression(arg, &mut self.classes); }
            }
            "Declaration" | "DLSafeRule" | "Body" | "Head" => {
                for arg in args { self.observe_classes(arg); }
            }
            _ => {}
        }
    }

    /// Candidate only: publish its taxonomy only after the complete original
    /// source has a checked model and the source-extension obligations hold.
    pub(super) fn class_projection(&self) -> Option<String> {
        if !self.fresh_class_witness_candidate() { return None; }
        let mut source = String::from("Ontology(\n");
        for name in &self.classes {
            source.push_str(&format!("Declaration(Class({name}))\n"));
        }
        for axiom in &self.class_axioms { source.push_str(axiom); source.push('\n'); }
        source.push(')');
        Some(source)
    }
    pub(super) fn object_abox_source(&self) -> Option<String> {
        self.fresh_class_witness_candidate().then(||
            format!("Ontology(\n{}\n)", self.object_assertions.join("\n")))
    }
    pub(super) fn object_property_source(&self) -> Option<String> {
        self.fresh_class_witness_candidate().then(||
            format!("Ontology(\n{}\n)", self.object_properties.join("\n")))
    }
    pub(super) fn data_source(&self) -> Option<String> {
        self.fresh_class_witness_candidate().then(||
            format!("Ontology(\n{}\n)", self.data_axioms.join("\n")))
    }
    pub(super) fn rule_source(&self) -> Option<String> {
        self.fresh_class_witness_candidate().then(||
            format!("Ontology(\n{}\n)", self.rules.join("\n")))
    }
    pub(super) fn certified(&self) -> bool { self.valid }
    /// Structural prerequisite only. A complete named-graph consistency
    /// certificate and preservation of each remaining source axiom are still
    /// required before publishing a projected taxonomy.
    pub(super) fn fresh_class_witness_candidate(&self) -> bool {
        self.valid && self.fresh_object_safe && self.classes.iter().all(|name|
            (name.starts_with('<') && name.ends_with('>')) || matches!(name.as_str(), "owl:Thing" | "owl:Nothing"))
            && !self.property_kinds.invalid
            && self.property_kinds.object.is_disjoint(&self.property_kinds.data)
    }
    pub(super) fn property_kinds(&self) -> Option<&PropertyKinds> {
        self.fresh_class_witness_candidate().then_some(&self.property_kinds)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn scan(source: &str) -> Scan {
        let mut scan = Scan::new(source);
        let mut registry = super::super::iri::IriRegistry::new();
        if super::super::parse::parse_axioms_observed(&mut registry, source, |node| scan.observe(node)).is_err() {
            scan.valid = false;
        }
        scan
    }
    #[test]
    fn projection_rejects_unexpanded_named_entity_aliases() {
        for source in [
            "Ontology(SubClassOf(owl:A <http://www.w3.org/2002/07/owl#A>))",
            "Ontology(DifferentIndividuals(owl:a <http://www.w3.org/2002/07/owl#a>))",
            "Ontology(ObjectPropertyDomain(owl:r owl:Nothing))",
        ] { assert!(scan(source).class_projection().is_none(), "{source}"); }
        assert!(scan("Ontology(SubClassOf(owl:Thing <A>))").class_projection().is_some());
    }

    #[test]
    fn class_projection_retains_boolean_theory_and_all_query_classes() {
        let source = scan(r#"Ontology(
            SubClassOf(ObjectUnionOf(<A> <B>) ObjectComplementOf(<C>))
            ClassAssertion(<OnlyAssertion> <a>)
            ObjectPropertyDomain(<r> <OnlyDomain>)
            ObjectPropertyRange(<r> <OnlyRange>)
            DataPropertyDomain(<p> <OnlyDataDomain>)
            DLSafeRule(Body(ClassAtom(<OnlyRule> Variable(<x>)))
                Head(ClassAtom(<C> Variable(<x>)))))"#);
        let projected = source.class_projection().unwrap();
        let mut registry = super::super::iri::IriRegistry::new();
        let parsed = super::super::parse::parse_axioms(&mut registry, &projected).unwrap();
        assert_eq!(parsed.tbox().count(), 1);
        for name in ["A", "B", "C", "OnlyAssertion", "OnlyDomain", "OnlyRange", "OnlyDataDomain", "OnlyRule"] {
            assert!(projected.contains(&format!("Declaration(Class(<{name}>))")), "lost query class {name}");
        }
        assert!(matches!(parsed.tbox().next().unwrap(),
            super::super::syntax::Axiom::SubClassOf(_, _)));
        assert!(!projected.contains("ObjectPropertyDomain"));
        assert!(!projected.contains("DLSafeRule"));
    }

    #[test]
    fn class_projection_declines_non_boolean_sources() {
        for source in [
            "Ontology(SubClassOf(<A> ObjectSomeValuesFrom(<r> <B>)))",
            "Ontology(SubClassOf(<A> ObjectOneOf(<a>)))",
            "Ontology(ReflexiveObjectProperty(<r>))",
            "Ontology(Import(<other>))",
        ] { assert!(scan(source).class_projection().is_none(), "{source}"); }
    }

    #[test]
    fn graph_source_is_restriction_closed_and_every_concrete_rule_has_a_plan() {
        let source = include_str!("../../tests/fixtures/graph_data_rules.ofn");
        let scan = scan(source);
        assert!(scan.certified());
        assert_eq!(scan.values.len(), 81);
        let mut registry = super::super::iri::IriRegistry::new();
        let ontology = super::super::parse::parse_axioms(&mut registry, source).unwrap();
        assert_eq!(ontology.datatype_rules().count(), 3);
        assert_eq!(ontology.rules().count(), 1);
        for rule in ontology.datatype_rules() {
            let plan = super::super::data_rules::finite_data_rule_plan(rule, &scan.values, 10_000).expect("complete graph rule plan");
            assert!(!plan.is_empty());
        }
    }
    #[test]
    fn rejects_value_generators_unknown_axioms_and_redefined_prefixes() {
        for axiom in [
            "SubClassOf(<A> DataSomeValuesFrom(<p> xsd:integer))",
            "SubClassOf(<A> DataHasValue(<p> \"1\"^^xsd:int))",
            "SubClassOf(<A> DataAllValuesFrom(<p> xsd:integer))",
            "SubClassOf(<A> DataMinCardinality(1 <p>))",
            "SubDataPropertyOf(<p> <q>)", "Import(<other>)",
            "HasKey(<A> () (<p>))", "Unknown(<A>)",
            "NegativeDataPropertyAssertion(<p> <a> \"1\"^^xsd:int)",
        ] {
            assert!(!scan(&format!("Ontology({axiom})")).certified(), "{axiom}");
        }
        assert!(!scan("Prefix(xsd:=<http://example.org/>) Ontology()").certified());
    }
    #[test]
    fn graph_source_allows_an_edge_free_class_witness() {
        let source = include_str!("../../tests/fixtures/graph_data_rules.ofn");
        assert!(scan(source).fresh_class_witness_candidate());
        // Grounding remains admitted, but these source axioms couple class
        // queries to edges or named individuals and prohibit this projection.
        for axiom in [
            "SubClassOf(<A> ObjectSomeValuesFrom(<r> <B>))",
            "SubClassOf(<A> ObjectAllValuesFrom(<r> <B>))",
            "SubClassOf(<A> ObjectOneOf(<a>))",
            "SubClassOf(<A> ObjectHasSelf(<r>))",
            "SubClassOf(<A> ObjectHasValue(<r> <a>))",
            "SubClassOf(<A> ObjectMinCardinality(1 <r> <B>))",
            "SubClassOf(<A> ObjectMaxCardinality(1 <r> <B>))",
            "SubClassOf(<A> ObjectExactCardinality(1 <r> <B>))",
            "ReflexiveObjectProperty(<r>)",
            "SubObjectPropertyOf(owl:topObjectProperty <r>)",
        ] {
            let source = format!("Ontology({axiom})");
            assert!(scan(&source).certified(), "grounding prerequisite: {axiom}");
            assert!(!scan(&source).fresh_class_witness_candidate(), "{axiom}");
        }
        assert!(scan("Ontology(SubClassOf(ObjectIntersectionOf(<A> <B>) ObjectUnionOf(<C> ObjectComplementOf(<D>))))").fresh_class_witness_candidate());
        assert!(!scan("Ontology(Unknown(<A>))").fresh_class_witness_candidate());
    }
    #[test]
    fn property_sorts_retain_full_source_names_and_rule_uses() {
        let graph = scan(include_str!("../../tests/fixtures/graph_data_rules.ofn"));
        let kinds = graph.property_kinds().unwrap();
        assert_eq!(kinds.object.len(), 20);
        assert_eq!(kinds.data.len(), 16);
        assert!(kinds.object.contains("http://ontology.dumontierlab.com/hasPart"));
        assert!(kinds.data.contains("http://ontology.dumontierlab.com/hasValue"));
        let source = scan(r#"Ontology(
            ObjectPropertyAssertion(<http://object.example/p> <a> <b>)
            DataPropertyAssertion(<http://data.example/p> <a> "x"^^xsd:string)
            SubObjectPropertyOf(ObjectPropertyChain(ObjectInverseOf(<r>) <s>) <t>)
            DLSafeRule(Body(DataPropertyAtom(<q> Variable(<x>) "x"^^xsd:string))
                Head(ObjectPropertyAtom(<u> Variable(<x>) <a>))))"#);
        let kinds = source.property_kinds().unwrap();
        assert!(kinds.object.contains("http://object.example/p"));
        assert!(kinds.data.contains("http://data.example/p"));
        for role in ["r", "s", "t", "u"] { assert!(kinds.object.contains(role)); }
        assert!(kinds.data.contains("q"));
        let overlap = scan("Ontology(Declaration(ObjectProperty(owl:p)) Declaration(DataProperty(<http://www.w3.org/2002/07/owl#p>)))");
        assert!(overlap.property_kinds().is_none());
        assert!(scan("Ontology(Declaration(ObjectProperty(<p>)) Declaration(DataProperty(<p>)))").property_kinds().is_none());
    }
}
