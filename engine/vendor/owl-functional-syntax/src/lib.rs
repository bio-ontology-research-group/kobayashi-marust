//! Grammar-only validation; see README.md for upstream provenance and license.
use pest::Parser;
use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "grammars/bcp47.pest"]
#[grammar = "grammars/rfc3987.pest"]
#[grammar = "grammars/sparql.pest"]
#[grammar = "grammars/ofn.pest"]
struct FunctionalSyntax;

pub fn validate(source: &str) -> Result<(), String> {
    let parsed = FunctionalSyntax::parse(Rule::OntologyDocument, source)
        .map_err(|error| format!("invalid OWL 2 DL input: {error}"))?;
    for pair in parsed.flatten() {
        if matches!(pair.as_rule(), Rule::DGRule | Rule::DGAxiom) {
            return Err("invalid OWL 2 DL input: description-graph extensions are outside OWL 2 DL plus DL-safe SWRL".into());
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    mod original {
        use pest_derive::Parser;
        #[derive(Parser)]
        #[grammar = "upstream-grammars/bcp47.pest"]
        #[grammar = "upstream-grammars/rfc3987.pest"]
        #[grammar = "upstream-grammars/sparql.pest"]
        #[grammar = "upstream-grammars/ofn.pest"]
        pub struct Original;
    }
    #[test]
    fn compact_grammar_preserves_upstream_acceptance() {
        let cases = [
            "Ontology()", "Ontology(Declaration(Class(<urn:A>)))",
            "Prefix(:=<urn:test:>) Ontology(SubClassOf(:A :B))",
            "Ontology(SubClassOf(<urn:A> ObjectMinCardinality(999999999999999999999 <urn:r>)))",
            "Ontology(DLSafeRule(Body(ClassAtom(<urn:A> Variable(<urn:x>))) Head(ClassAtom(<urn:B> Variable(<urn:x>)))))",
            "Ontology(Annotation(<urn:p> \"hello\"@en-GB))",
            "Ontology(Annotation(<urn:p> \"hello\"^^<urn:t>))",
            "Ontology(SubClassOf(<urn:A>))", "Ontology() trailing", "Ontology() Ontology()",
            "Ontology(Declaration(Class(<urn:space here>)))", "Ontology(",
            "Ontology(Annotation(<urn:p> \"unterminated))",
        ];
        for case in cases {
            for text in [case.to_owned(), case.replace(' ', " \n # comment\n ")] {
                assert_eq!(FunctionalSyntax::parse(Rule::OntologyDocument, &text).is_ok(),
                    original::Original::parse(original::Rule::OntologyDocument, &text).is_ok(), "{text}");
            }
        }
    }
    #[test]
    fn data_property_atoms_use_individual_subjects_and_data_objects() {
        for subject in ["<urn:a>", "Variable(<urn:x>)"] {
            for object in ["\"value\"", "Variable(<urn:v>)"] {
                validate(&format!("Ontology(DLSafeRule(Body(DataPropertyAtom(<urn:p> {subject} {object})) Head()))")).unwrap();
            }
        }
        for (subject, object) in [("\"literal-subject\"", "Variable(<urn:v>)"),
            ("<urn:a>", "<urn:individual-object>")] {
            assert!(validate(&format!("Ontology(DLSafeRule(Body(DataPropertyAtom(<urn:p> {subject} {object})) Head()))")).is_err());
        }
    }

    #[test]
    fn absolute_iris_allow_empty_paths_without_accepting_relative_iris() {
        for iri in ["urn:", "urn:#fragment", "urn:?query", "test:", "test:?q#f"] {
            validate(&format!("Prefix(:=<{iri}>) Ontology(Declaration(Class(:A)))")).unwrap();
            validate(&format!("Ontology(Declaration(Class(<{iri}>)))")).unwrap();
        }
        for iri in ["", ":", "#fragment", "?query", "urn: space", "urn:%"] {
            assert!(validate(&format!("Ontology(Declaration(Class(<{iri}>)))")).is_err(), "{iri}");
        }
    }

    #[test]
    fn iri_characters_do_not_accumulate_parse_tree_nodes() {
        let iri = format!("urn:{}", "a".repeat(100_000));
        let source = format!("Ontology(Declaration(Class(<{iri}>)))");
        let count = FunctionalSyntax::parse(Rule::OntologyDocument, &source).unwrap().flatten().count();
        assert!(count < 20, "validation retained {count} pairs for one IRI");
    }
}
