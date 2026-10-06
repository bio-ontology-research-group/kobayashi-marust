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
    if std::env::var_os("KM_FAST_IRI_GRAMMAR").is_some() {
        return validate_iri_cached(source);
    }
    validate_original(source)
}

fn validate_original(source: &str) -> Result<(), String> {
    let parsed = FunctionalSyntax::parse(Rule::OntologyDocument, source)
        .map_err(|error| format!("invalid OWL 2 DL input: {error}"))?;
    for pair in parsed.flatten() {
        if matches!(pair.as_rule(), Rule::DGRule | Rule::DGAxiom) {
            return Err("invalid OWL 2 DL input: description-graph extensions are outside OWL 2 DL plus DL-safe SWRL".into());
        }
    }
    Ok(())
}

mod iri_cached {
    use pest_derive::Parser;
    #[derive(Parser)]
    #[grammar = "grammars/bcp47.pest"]
    #[grammar = "grammars/rfc3987.pest"]
    #[grammar = "grammars/sparql.pest"]
    #[grammar = "grammars/ofn-iri-cached.pest"]
    pub struct Syntax;
}

/// Experimental two-stage validation. The structural grammar still emits every
/// full IRI, including those in prefixes, annotations and datatype suffixes.
/// Every distinct spelling is checked with the SAME original FullIRI rule.
/// The cache is local to this document and contains only successful checks.
pub fn validate_iri_cached(source: &str) -> Result<(), String> {
    let parsed = match iri_cached::Syntax::parse(iri_cached::Rule::OntologyDocument, source) {
        Ok(parsed) => parsed,
        Err(_) => return validate_original(source),
    };
    let mut validated = std::collections::HashSet::new();
    for pair in parsed.flatten() {
        match pair.as_rule() {
            iri_cached::Rule::DGRule | iri_cached::Rule::DGAxiom => {
                return validate_original(source);
            }
            iri_cached::Rule::FullIRI => {
                let iri = pair.as_str();
                if !validated.contains(iri) {
                    let checked = FunctionalSyntax::parse(Rule::FullIRI, iri);
                    let valid = checked.is_ok_and(|mut pairs| pairs.next()
                        .is_some_and(|p| p.as_span().end() == iri.len()));
                    if !valid {
                        // Preserve the original error text and source location.
                        // This slower path is reached only for an invalid IRI.
                        return validate_original(source);
                    }
                    validated.insert(iri);
                }
            }
            _ => {}
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn cached_iri_grammar_changes_only_full_iri_recognition() {
        let original = include_str!("../grammars/ofn.pest");
        let cached = include_str!("../grammars/ofn-iri-cached.pest");
        assert_eq!(cached.replace(
            "FullIRI        = @{ LCHEVRON ~ (!RCHEVRON ~ ANY)* ~ RCHEVRON }",
            "FullIRI        = @{ LCHEVRON ~ RFC3987_Iri ~ RCHEVRON }"), original);
    }

    #[test]
    fn cached_iri_validation_matches_original_in_all_iri_positions() {
        let iris = ["urn:A", "urn:", "urn:?q#f", "https://example.org/a%20b?q=x#f",
            "urn:é", "urn:漢字", "urn:🙂", "http://[::1]/a", "", "relative",
            "urn: space", "urn:\nnewline", "urn:\ttab", "urn:%", "urn:%0",
            "urn:%GG", "urn:<nested", "urn:bad|pipe", "urn:\"quote", "urn:\\backslash"];
        for iri in iris {
            let atom = format!("<{iri}>");
            let documents = [
                format!("Prefix(:={atom}) Ontology(Declaration(Class(:A)))"),
                format!("Ontology({atom} Declaration(Class(<urn:A>)))"),
                format!("Ontology(Declaration(Class({atom})) SubClassOf({atom} <urn:B>))"),
                format!("Ontology(Annotation({atom} {atom}))"),
                format!("Ontology(Annotation(<urn:p> \"value\"^^{atom}))"),
                format!("Ontology(DLSafeRule(Body(ClassAtom({atom} Variable(<urn:x>))) Head()))"),
                format!("Ontology(SubClassOf(<urn:A> ObjectSomeValuesFrom({atom} <urn:B>)))"),
            ];
            for source in documents {
                let old = validate_original(&source);
                let new = validate_iri_cached(&source);
                assert_eq!(old, new, "{source}");
            }
        }
        for source in ["Ontology(", "Ontology() trailing", "Ontology() Ontology()",
            "Ontology(SubClassOf(<urn:A>))", "Ontology(Annotation(<urn:p> \"<not an IRI>\"))",
            "# <not an IRI>\nOntology()"] {
            assert_eq!(validate_original(source), validate_iri_cached(source), "{source}");
        }
    }
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
