//! Model-extension obligations for DL-safe rules on isolated source names.
//! The frontend uses this sufficient certificate to project inactive rules
//! while retaining source counts and separate classification provenance.
use std::collections::BTreeSet;
use super::{sexpr::Node, syntax::{Axiom, Concept, Ontology, Role, RuleAtom, RuleTerm}};

pub(super) struct Scan<'a> {
    invalid: bool,
    asserted_properties: BTreeSet<&'a str>,
    constrained_atoms: BTreeSet<&'a str>,
}
fn atoms<'a>(node: &Node<'a>, result: &mut BTreeSet<&'a str>) {
    match node {
        Node::Atom(s) => { result.insert(s); }
        Node::List(_, args) => for node in args { atoms(node, result); },
    }
}
impl<'a> Scan<'a> {
    pub(super) fn new(text: &str) -> Self {
        let mut parser = super::sexpr::Parser::new(text);
        let mut valid = true;
        while parser.peek() == Some("Prefix") {
            let Ok(Node::List("Prefix", args)) = parser.parse() else { valid = false; break; };
            let Some(parts): Option<Vec<_>> = args.iter().map(Node::as_atom).collect() else { valid = false; break; };
            let definition = parts.concat();
            valid &= matches!(definition.as_str(),
                "owl:=<http://www.w3.org/2002/07/owl#>"
                | "rdf:=<http://www.w3.org/1999/02/22-rdf-syntax-ns#>"
                | "rdfs:=<http://www.w3.org/2000/01/rdf-schema#>"
                | "xsd:=<http://www.w3.org/2001/XMLSchema#>"
                | "xml:=<http://www.w3.org/XML/1998/namespace>");
        }
        valid &= parser.peek() == Some("Ontology");
        Self { invalid: !valid, asserted_properties: BTreeSet::new(), constrained_atoms: BTreeSet::new() }
    }
    pub(super) fn observe(&mut self, node: &Node<'a>) {
        let Node::List(kind, arguments) = node else {
            // Ontology identifiers are metadata, not constraints.
            self.invalid |= !matches!(node, Node::Atom(s) if s.starts_with('<'));
            return;
        };
        let args = super::parse::strip_annotations(arguments);
        match *kind {
            "Declaration" | "Annotation" => {},
            "DLSafeRule" => atoms(node, &mut self.constrained_atoms),
            "ClassAssertion" => {
                self.invalid |= !matches!(args.as_slice(), [Node::Atom("owl:Thing" | "<http://www.w3.org/2002/07/owl#Thing>"), Node::Atom(name)] if name.starts_with('<'));
            }
            "DataPropertyAssertion" => {
                let valid = (|| {
                    let property = args.first()?.as_atom()?;
                    if property.contains('\\') || !property.starts_with('<') || !args.get(1)?.as_atom()?.starts_with('<') { return None; }
                    let (literal, consumed) = super::parse::glue_literal(&args, 2)?;
                    if args.len() != 2 + consumed
                        || super::datatypes::exact_literal_value_equal(&literal, &literal) != Some(true) { return None; }
                    self.asserted_properties.insert(property);
                    Some(())
                })();
                self.invalid |= valid.is_none();
            }
            "SubClassOf" | "EquivalentClasses" | "DisjointClasses"
            | "SubObjectPropertyOf" | "EquivalentObjectProperties" | "InverseObjectProperties"
            | "ObjectPropertyDomain" | "ObjectPropertyRange" | "FunctionalObjectProperty"
            | "InverseFunctionalObjectProperty" | "TransitiveObjectProperty"
            | "SymmetricObjectProperty" | "AsymmetricObjectProperty" | "IrreflexiveObjectProperty"
            | "DisjointObjectProperties" | "SubDataPropertyOf" | "EquivalentDataProperties"
            | "DataPropertyDomain" | "DataPropertyRange" | "FunctionalDataProperty"
            | "DisjointDataProperties" => atoms(node, &mut self.constrained_atoms),
            _ => self.invalid = true,
        }
    }
    /// A sufficient extension certificate, never an asserted-only rule evaluator.
    pub(super) fn candidate(&self, ontology: &Ontology, source_rules: u64, observers: u64) -> bool {
        if self.invalid || source_rules <= observers
            || !self.asserted_properties.is_disjoint(&self.constrained_atoms) { return false; }
        // Restrict source constraints to full IRIs and standard prefixed names.
        // This prevents a user-prefix alias hiding a constrained assertion role.
        if self.constrained_atoms.iter().any(|s| universal_name(s) || (s.starts_with('<') && s.contains('\\'))) { return false; }
        // Built-in namespace assertion properties could be spelled through
        // standard aliases in constraints; require unambiguous custom IRIs.
        if self.asserted_properties.iter().any(|s| ["<http://www.w3.org/2002/07/owl#", "<http://www.w3.org/1999/02/22-rdf-syntax-ns#", "<http://www.w3.org/2000/01/rdf-schema#", "<http://www.w3.org/2001/XMLSchema#"].iter().any(|prefix| s.starts_with(prefix))) { return false; }
        if self.constrained_atoms.iter().any(|s| s.contains(':') && !s.starts_with('<')
            && !s.starts_with('"') && !["owl:", "rdf:", "rdfs:", "xsd:"].iter().any(|p| s.strip_prefix("^^").unwrap_or(s).starts_with(p))) { return false; }
        if ontology.tbox().any(|axiom| match axiom {
            Axiom::SubClassOf(left, right) => match (empty_point(left), empty_point(right)) {
                (Some(left), Some(right)) => left && !right,
                _ => true,
            },
            Axiom::EquivalentClasses(left, right) => match (empty_point(left), empty_point(right)) {
                (Some(left), Some(right)) => left != right,
                _ => true,
            },
            Axiom::DisjointClasses(left, right) => match (empty_point(left), empty_point(right)) {
                (Some(left), Some(right)) => left && right,
                _ => true,
            },
            _ => true,
        }) { return false; }
        if ontology.rbox().any(|axiom| matches!(axiom, Axiom::ReflexiveRole(_)) || matches!(axiom, Axiom::RoleChain(roles, _) if roles.is_empty())) { return false; }
        let rules: Vec<_> = ontology.rules().chain(ontology.datatype_rules()).collect();
        if rules.len() as u64 + observers != source_rules { return false; }
        rules.into_iter().all(|rule| {
            let (Axiom::Rule(body, head) | Axiom::DataRule(body, head)) = rule else { return false; };
            let variable = |term: &RuleTerm| matches!(term, RuleTerm::Var(_));
            let object_variables = |atom: &RuleAtom| match atom {
                RuleAtom::Class(_, term) | RuleAtom::Data(_, term, _) => variable(term),
                RuleAtom::Role(_, left, right) | RuleAtom::Same(left, right) | RuleAtom::Diff(left, right) => variable(left) && variable(right),
                _ => true,
            };
            body.iter().chain(head).all(object_variables) && body.iter().any(|atom| match atom {
                RuleAtom::Class(concept, _) => empty_point(concept) == Some(false),
                RuleAtom::Role(role, _, _) => !universal_name(role),
                RuleAtom::Data(property, _, _) => !universal_name(property),
                _ => false,
            })
        })
    }
}
fn universal_name(name: &str) -> bool {
    matches!(name, "topObjectProperty" | "topDataProperty" | "owl:topObjectProperty" | "owl:topDataProperty"
        | "<http://www.w3.org/2002/07/owl#topObjectProperty>" | "<http://www.w3.org/2002/07/owl#topDataProperty>")
}
fn empty_role(role: &Role) -> bool {
    match role { Role::Universal => false, Role::Name(name) | Role::Inverse(name) => !universal_name(name) }
}
/// Truth at a new object point with all named classes and role edges empty.
fn empty_point(concept: &Concept) -> Option<bool> {
    Some(match concept {
        Concept::Top => true,
        Concept::Bottom | Concept::Name(_) => false,
        Concept::Nominal(_) => return None,
        Concept::Not(inner) => !empty_point(inner)?,
        Concept::And(parts) => { let mut result = true; for part in parts { result &= empty_point(part)?; } result },
        Concept::Or(parts) => { let mut result = false; for part in parts { result |= empty_point(part)?; } result },
        Concept::HasSelf(role) if empty_role(role) => false,
        Concept::Exists(role, filler) if empty_role(role) => { empty_point(filler)?; false },
        Concept::Forall(role, filler) if empty_role(role) => { empty_point(filler)?; true },
        Concept::AtLeast(n, role, filler) if *n >= 0 && empty_role(role) => { empty_point(filler)?; *n == 0 },
        Concept::AtMost(n, role, filler) if *n >= 0 && empty_role(role) => { empty_point(filler)?; true },
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    fn candidate(text: &str) -> bool {
        let mut scan = Scan::new(text);
        let mut count = 0;
        super::super::parse::for_each_ontology_child(text, |node| {
            if matches!(node, Node::List("DLSafeRule", _)) { count += 1; }
            scan.observe(node); Ok(())
        }).unwrap();
        let mut registry = super::super::iri::IriRegistry::new();
        let Ok(ontology) = super::super::parse::parse_axioms(&mut registry, text) else { return false; };
        scan.candidate(&ontology, count, 0)
    }
    #[test]
    fn checks_actual_714_isolated_name_extension_obligations() {
        let text = include_str!("../../tests/fixtures/isolated_list_rules.ofn");
        assert!(candidate(text));
        assert!(!candidate(&text.replace("owl:=<http://www.w3.org/2002/07/owl#>", "owl:=<http://example.org/alias#>")));
    }
    #[test]
    fn source_constraints_prevent_unsafe_isolated_extensions() {
        let rule = "DLSafeRule(Body(ObjectPropertyAtom(<http://example.org/r> Variable(<http://example.org/x>) Variable(<http://example.org/y>))) Head(DataPropertyAtom(<http://example.org/error> Variable(<http://example.org/x>) \"error\")))";
        assert!(candidate(&format!("Ontology(DataPropertyAssertion(<http://example.org/author> <http://example.org/a> \"author\") {rule})")));
        for extra in [
            "ClassAssertion(<http://example.org/Person> <http://example.org/a>)",
            "ObjectPropertyAssertion(<http://example.org/r> <http://example.org/a> <http://example.org/a>)",
            "ReflexiveObjectProperty(<http://example.org/r>)",
            "SubClassOf(owl:Thing <http://example.org/Person>)",
            "SubClassOf(<http://example.org/Person> ObjectSomeValuesFrom(<http://example.org/r> ObjectOneOf(<http://example.org/a>)))",
            "DataPropertyDomain(<http://example.org/author> <http://example.org/Person>)",
            "SubClassOf(<http://example.org/Person> ObjectSomeValuesFrom(owl:topObjectProperty <http://example.org/Person>))",
            "Import(<http://example.org/import>)",
        ] {
            assert!(!candidate(&format!("Ontology(DataPropertyAssertion(<http://example.org/author> <http://example.org/a> \"author\") {extra} {rule})")), "{extra}");
        }
    }
}
