//! OWL 2 DL entity typing constraints. Class/individual and class/property
//! punning are legal; class/datatype and distinct property kinds are not.
use std::collections::{BTreeMap, BTreeSet};
use super::{expand, Node};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Kind { Class, Datatype, ObjectProperty, DataProperty, AnnotationProperty, Individual }

#[derive(Default)]
struct Types(BTreeMap<String, BTreeSet<Kind>>, BTreeMap<String, BTreeSet<Kind>>);
impl Types {
    fn mark(&mut self, node: &Node<'_>, kind: Kind, prefixes: &BTreeMap<String, String>) {
        match node {
            Node::Atom(name) if !name.starts_with('"') && !name.starts_with("_:") => {
                self.0.entry(expand(name, prefixes)).or_default().insert(kind);
            }
            Node::List("", args) if matches!(kind, Kind::ObjectProperty | Kind::DataProperty) => {
                for arg in args { self.mark(arg, kind, prefixes); }
            }
            Node::List("ObjectInverseOf", args) if kind == Kind::ObjectProperty => {
                for arg in args { self.mark(arg, kind, prefixes); }
            }
            _ => {}
        }
    }
    fn observe(&mut self, node: &Node<'_>, prefixes: &BTreeMap<String, String>) {
        use Kind::*;
        let Node::List(head, children) = node else { return };
        let args: Vec<_> = children.iter().filter(|n| n.head() != Some("Annotation")).collect();
        if *head == "Declaration" {
            for entity in &args {
                if let Node::List(kind, value) = entity {
                    let kind = match *kind {
                        "Class"=>Some(Class), "Datatype"=>Some(Datatype), "ObjectProperty"=>Some(ObjectProperty),
                        "DataProperty"=>Some(DataProperty), "AnnotationProperty"=>Some(AnnotationProperty),
                        "NamedIndividual"=>Some(Individual), _=>None,
                    };
                    if let (Some(kind), [Node::Atom(name)]) = (kind, value.as_slice()) {
                        self.1.entry(expand(name,prefixes)).or_default().insert(kind);
                    }
                }
            }
        }
        let mut at = |index: usize, kind| {
            if let Some(arg) = args.get(index) { self.mark(arg, kind, prefixes); }
        };
        match *head {
            "HasKey" => { at(0, Class); at(1, ObjectProperty); at(2, DataProperty); }
            "Class" => at(0, Class), "Datatype" => at(0, Datatype),
            "ObjectProperty" => at(0, ObjectProperty), "DataProperty" => at(0, DataProperty),
            "AnnotationProperty" => at(0, AnnotationProperty), "NamedIndividual" => at(0, Individual),
            "SubClassOf" | "EquivalentClasses" | "DisjointClasses" | "DisjointUnion"
                | "ObjectIntersectionOf" | "ObjectUnionOf" | "ObjectComplementOf" =>
                for i in 0..args.len() { at(i, Class); },
            "SubObjectPropertyOf" | "EquivalentObjectProperties" | "DisjointObjectProperties"
                | "InverseObjectProperties" | "ObjectPropertyChain" | "ObjectInverseOf"
                | "TransitiveObjectProperty" | "SymmetricObjectProperty" | "AsymmetricObjectProperty"
                | "IrreflexiveObjectProperty" | "ReflexiveObjectProperty" | "FunctionalObjectProperty"
                | "InverseFunctionalObjectProperty" | "ObjectHasSelf" =>
                for i in 0..args.len() { at(i, ObjectProperty); },
            "ObjectSomeValuesFrom" | "ObjectAllValuesFrom" | "ObjectPropertyDomain" | "ObjectPropertyRange" => {
                at(0, ObjectProperty); at(1, Class);
            }
            "ObjectMinCardinality" | "ObjectMaxCardinality" | "ObjectExactCardinality" => {
                at(1, ObjectProperty); at(2, Class);
            }
            "DataMinCardinality" | "DataMaxCardinality" | "DataExactCardinality" => {
                at(1, DataProperty); at(2, Datatype);
            }
            "DataSomeValuesFrom" | "DataAllValuesFrom" => {
                for i in 0..args.len().saturating_sub(1) { at(i, DataProperty); }
                if !args.is_empty() { at(args.len()-1, Datatype); }
            }
            "DataPropertyDomain" => { at(0, DataProperty); at(1, Class); }
            "DataPropertyRange" => { at(0, DataProperty); at(1, Datatype); }
            "SubDataPropertyOf" | "EquivalentDataProperties" | "DisjointDataProperties"
                | "FunctionalDataProperty" => for i in 0..args.len() { at(i, DataProperty); },
            "DatatypeDefinition" | "DataUnionOf" | "DataIntersectionOf" | "DataComplementOf" =>
                for i in 0..args.len() { at(i, Datatype); },
            "DatatypeRestriction" | "DataRangeAtom" => at(0, Datatype),
            "ClassAssertion" | "ClassAtom" => { at(0, Class); at(1, Individual); }
            "ObjectHasValue" => { at(0, ObjectProperty); at(1, Individual); }
            "DataHasValue" => at(0, DataProperty),
            "ObjectPropertyAssertion" | "NegativeObjectPropertyAssertion" | "ObjectPropertyAtom" => {
                at(0, ObjectProperty); at(1, Individual); at(2, Individual);
            }
            "DataPropertyAssertion" | "NegativeDataPropertyAssertion" | "DataPropertyAtom" => {
                at(0, DataProperty); at(1, Individual);
            }
            "SameIndividual" | "DifferentIndividuals" | "ObjectOneOf" | "SameIndividualAtom" | "DifferentIndividualsAtom" =>
                for i in 0..args.len() { at(i, Individual); },
            "Annotation" | "AnnotationAssertion" | "AnnotationPropertyDomain" | "AnnotationPropertyRange" => at(0, AnnotationProperty),
            "SubAnnotationPropertyOf" => { at(0, AnnotationProperty); at(1, AnnotationProperty); }
            _ => {}
        }
        for child in children { self.observe(child, prefixes); }
    }
    fn finish(self) -> Result<(), String> {
        use Kind::*;
        for (name, kinds) in self.0 {
            let reserved = ["http://www.w3.org/2002/07/owl#", "http://www.w3.org/1999/02/22-rdf-syntax-ns#",
                "http://www.w3.org/2000/01/rdf-schema#", "http://www.w3.org/2001/XMLSchema#"]
                .iter().any(|ns| name.starts_with(ns));
            if reserved {
                for kind in &kinds {
                    let allowed = match kind {
                        Class => matches!(name.as_str(), "http://www.w3.org/2002/07/owl#Thing" | "http://www.w3.org/2002/07/owl#Nothing"),
                        ObjectProperty => matches!(name.as_str(), "http://www.w3.org/2002/07/owl#topObjectProperty" | "http://www.w3.org/2002/07/owl#bottomObjectProperty"),
                        DataProperty => matches!(name.as_str(), "http://www.w3.org/2002/07/owl#topDataProperty" | "http://www.w3.org/2002/07/owl#bottomDataProperty"),
                        Datatype => super::datatypes::builtin(&name),
                        AnnotationProperty => matches!(name.as_str(), "http://www.w3.org/2000/01/rdf-schema#label"
                            | "http://www.w3.org/2000/01/rdf-schema#comment" | "http://www.w3.org/2000/01/rdf-schema#seeAlso"
                            | "http://www.w3.org/2000/01/rdf-schema#isDefinedBy" | "http://www.w3.org/2002/07/owl#deprecated"
                            | "http://www.w3.org/2002/07/owl#versionInfo" | "http://www.w3.org/2002/07/owl#priorVersion"
                            | "http://www.w3.org/2002/07/owl#backwardCompatibleWith" | "http://www.w3.org/2002/07/owl#incompatibleWith"),
                        Individual => false,
                    };
                    if !allowed { return Err(format!("invalid OWL 2 DL input: reserved IRI <{name}> cannot be used as {kind:?}")); }
                }
            }
            if (kinds.contains(&Class) && kinds.contains(&Datatype))
                || [ObjectProperty, DataProperty, AnnotationProperty].iter().filter(|k| kinds.contains(k)).count() > 1 {
                return Err(format!("invalid OWL 2 DL input: IRI <{name}> is used with incompatible entity types {kinds:?}"));
            }
        }
        Ok(())
    }
    fn declarations(&self) -> Result<(), String> {
        for (name,kinds) in &self.0 {
            // Built-in declarations are implicit. Their allowed entity kinds
            // are checked separately by finish().
            let builtin = ["http://www.w3.org/2002/07/owl#", "http://www.w3.org/1999/02/22-rdf-syntax-ns#",
                "http://www.w3.org/2000/01/rdf-schema#", "http://www.w3.org/2001/XMLSchema#"]
                .iter().any(|ns|name.starts_with(ns));
            for kind in kinds {
                if *kind != Kind::Individual && !builtin && !self.1.get(name).is_some_and(|types|types.contains(kind)) {
                    return Err(format!("invalid OWL 2 DL input: <{name}> is used as {kind:?} but has no matching declaration"));
                }
            }
        }
        Ok(())
    }
}

pub(super) fn check_declarations(text: &str, prefixes: &BTreeMap<String,String>) -> Result<(),String> {
    let mut types = Types::default();
    crate::frontend::parse::for_each_ontology_child(text, |node| {types.observe(node,prefixes); Ok(())}).map_err(|e|e.0)?;
    types.declarations()?;
    types.finish()
}

pub(super) fn check(text: &str, prefixes: &BTreeMap<String, String>) -> Result<(), String> {
    let mut types = Types::default();
    crate::frontend::parse::for_each_ontology_child(text, |node| {
        check_key(node).map_err(crate::frontend::parse::OutOfFragment)?;
        types.observe(node, prefixes); Ok(())
    }).map_err(|e| e.0)?;
    types.finish()
}

// OWL 2 Structural Specification 9.5 requires at least one key property.
fn check_key(node: &Node<'_>) -> Result<(), String> {
    if let Node::List("HasKey", children) = node {
        let args: Vec<_> = children.iter().filter(|n| n.head() != Some("Annotation")).collect();
        if let [_, Node::List("", objects), Node::List("", data)] = args.as_slice() {
            if objects.is_empty() && data.is_empty() {
                return Err("invalid OWL 2 DL input: HasKey must contain at least one object or data property".into());
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::super::check_source;
    #[test]
    fn keys_require_properties_and_preserve_entity_types() {
        for key in ["HasKey(:A () ())", "HasKey(Annotation(rdfs:comment \"empty\") :A () ())"] {
            assert!(check_source(&format!("Ontology({key})")).unwrap_err().contains("at least one"));
        }
        for key in ["HasKey(:A (:p) ())", "HasKey(:A (ObjectInverseOf(:p)) ())", "HasKey(:A () (:d))"] {
            check_source(&format!("Ontology({key})")).unwrap();
        }
        for key in ["HasKey(:A (:p) (:p))", "HasKey(:A (ObjectInverseOf(:p)) (:p))"] {
            assert!(check_source(&format!("Ontology({key})")).unwrap_err().contains("incompatible entity types"));
        }
        let check = super::super::check_declarations;
        assert!(check("Ontology(Declaration(Class(:A)) HasKey(:A (:p) ()))").unwrap_err().contains("no matching declaration"));
        check("Ontology(Declaration(Class(:A)) Declaration(ObjectProperty(:p)) HasKey(:A (ObjectInverseOf(:p)) ()))").unwrap();
    }
    #[test]
    fn incompatible_property_kinds_are_rejected_with_or_without_declarations() {
        for axioms in ["Declaration(ObjectProperty(:p)) Declaration(DataProperty(:p))",
            "ObjectPropertyAssertion(:p :a :b) DataPropertyAssertion(:p :a \"value\")",
            "Declaration(AnnotationProperty(:p)) SubClassOf(:A ObjectSomeValuesFrom(:p :B))"] {
            assert!(check_source(&format!("Ontology({axioms})")).unwrap_err().contains("incompatible entity types"));
        }
    }
    #[test]
    fn class_datatype_punning_is_rejected_but_class_individual_punning_is_legal() {
        assert!(check_source("Ontology(Declaration(Class(:A)) Declaration(Datatype(:A)))").unwrap_err().contains("incompatible entity types"));
        assert!(check_source("Ontology(Declaration(Class(:A)) Declaration(NamedIndividual(:A)) ClassAssertion(:A :A))").is_ok());
        assert!(check_source("Ontology(Declaration(Class(:p)) Declaration(ObjectProperty(:p)))").is_ok());
    }
    #[test]
    fn reserved_names_are_allowed_only_for_their_builtin_entity_kinds() {
        for axiom in ["Declaration(Class(owl:Class))", "Declaration(ObjectProperty(rdf:type))",
            "Declaration(NamedIndividual(owl:Thing))", "Declaration(AnnotationProperty(owl:Thing))"] {
            assert!(check_source(&format!("Ontology({axiom})")).unwrap_err().contains("reserved IRI"));
        }
        assert!(check_source("Ontology(Annotation(rdfs:label \"valid\") Declaration(Class(owl:Thing)))").is_ok());
    }
    #[test]
    fn required_entity_declarations_do_not_require_named_individual_declarations() {
        let check = super::super::check_declarations;
        assert!(check("Ontology(Declaration(Class(:A)) ClassAssertion(:A :a))").is_ok());
        assert!(check("Ontology(SubClassOf(:A owl:Thing))").unwrap_err().contains("no matching declaration"));
        assert!(check("Ontology(Declaration(ObjectProperty(:p)) ObjectPropertyAssertion(:p :a :b))").is_ok());
        assert!(check("Ontology(DataPropertyAssertion(:p :a \"x\"))").is_err());
        assert!(check("Ontology(Annotation(rdfs:label \"x\"))").is_ok());
    }
}
