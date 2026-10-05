//! Source conformance checks shared by public classification and the frontend.
//! Grammar validation includes DL-safe SWRL. This is not yet a complete OWL 2
//! DL profile checker: remaining global restrictions still require audit.
//! User-entry APIs enforce declarations separately from generated documents.
use std::collections::{BTreeMap, BTreeSet};
use std::cell::RefCell;
use super::sexpr::{tokens, Node, Parser};

mod roles;
mod anonymous;
mod datatypes;
mod facets;
mod pattern;
mod entities;
mod lexical;
mod xml_literal;

/// Imports must be resolved before validating the axiom closure. The current
/// standalone loader expects a self-contained document; refusal is a loading
/// limitation, not evidence that the imported ontology is outside OWL 2 DL.
pub fn has_imports(text: &str) -> Result<bool, String> {
    let mut found = false;
    super::parse::for_each_ontology_child(text, |node| {
        found |= node.head() == Some("Import");
        Ok(())
    }).map_err(|e|e.0)?;
    Ok(found)
}

/// Check declarations at user-input boundaries, separately from generated documents.
/// Named-individual declarations are optional under OWL 2 DL.
pub fn check_declarations(text: &str) -> Result<(), String> {
    entities::check_declarations(text, &prefixes(text)?)
}

/// Resolve every abbreviated IRI at user-input boundaries. Literal contents,
/// full IRIs and anonymous-individual node IDs are not abbreviated IRIs.
/// Grammar validation must run first.
pub fn check_iri_prefixes(text: &str) -> Result<(), String> {
    let mut parser = Parser::new(text);
    let mut declared = BTreeSet::new();
    while parser.peek() == Some("Prefix") {
        let Node::List(_, args) = parser.parse()? else {
            return Err("invalid OWL 2 input: malformed prefix declaration".into());
        };
        let definition = args.iter().filter_map(Node::as_atom).collect::<String>();
        let Some((prefix, iri)) = definition.split_once(":=") else {
            return Err("invalid OWL 2 input: malformed prefix declaration".into());
        };
        if !declared.insert(prefix.to_owned()) {
            return Err(format!("invalid OWL 2 input: prefix {prefix}: is declared more than once"));
        }
        if let Some((_, standard)) = STANDARD_PREFIXES.iter().find(|(name, _)| *name == prefix) {
            // Common serializers emit redundant standard declarations. Accept
            // those identical bindings; never let them redefine vocabulary.
            if iri.strip_prefix('<').and_then(|s| s.strip_suffix('>')) != Some(*standard) {
                return Err(format!("invalid OWL 2 input: standard prefix {prefix}: cannot be rebound to {iri}; its namespace is <{standard}>"));
            }
        }
    }
    let prefixes = prefixes(text)?;
    let mut in_ontology = false;
    for token in tokens(text) {
        if !in_ontology {
            in_ontology = token == "Ontology";
            continue;
        }
        let token = token.strip_prefix("^^").unwrap_or(token);
        if token.starts_with(['<', '"', '@']) || token.starts_with("_:") { continue; }
        if let Some((prefix, _)) = token.split_once(':') {
            if !prefixes.contains_key(prefix) {
                let offset = token.as_ptr() as usize - text.as_ptr() as usize;
                let line = text[..offset].bytes().filter(|b| *b==b'\n').count()+1;
                return Err(format!("invalid OWL 2 DL input at line {line}: abbreviated IRI {token} uses undeclared prefix {prefix}:"));
            }
        }
    }
    Ok(())
}

const STANDARD_PREFIXES: [(&str, &str); 4] = [
    ("rdfs", "http://www.w3.org/2000/01/rdf-schema#"),
    ("owl", "http://www.w3.org/2002/07/owl#"),
    ("xsd", "http://www.w3.org/2001/XMLSchema#"),
    ("rdf", "http://www.w3.org/1999/02/22-rdf-syntax-ns#"),
];

fn prefixes(text: &str) -> Result<BTreeMap<String, String>, String> {
    let mut prefixes: BTreeMap<_, _> = STANDARD_PREFIXES.iter()
        .map(|(name, iri)| ((*name).to_owned(), (*iri).to_owned())).collect();
    let mut parser = Parser::new(text);
    while parser.peek() == Some("Prefix") {
        let Node::List(_, args) = parser.parse()? else {
            return Err("invalid OWL 2 DL input: expected Prefix(...) declaration".into());
        };
        let parts: Option<Vec<_>> = args.iter().map(Node::as_atom).collect();
        if let Some(parts) = parts {
            let definition = parts.concat();
            if let Some((prefix, iri)) = definition.split_once(":=") {
                if let Some(iri) = iri.strip_prefix('<').and_then(|s| s.strip_suffix('>')) {
                    prefixes.insert(prefix.to_owned(), iri.to_owned());
                }
            }
        }
    }
    Ok(prefixes)
}

fn expand(datatype: &str, prefixes: &BTreeMap<String, String>) -> String {
    if let Some(iri) = datatype.strip_prefix('<').and_then(|s| s.strip_suffix('>')) {
        iri.to_owned()
    } else if let Some((prefix, local)) = datatype.split_once(':') {
        prefixes.get(prefix).map(|base| format!("{base}{local}")).unwrap_or_else(|| datatype.to_owned())
    } else { datatype.to_owned() }
}

/// Check the implemented source constraints, retaining DL-safe rule axioms.
/// Passing this function is not yet a complete OWL 2 DL profile certificate.
const VALIDATED_SOURCE_CACHE_LIMIT: usize = 8 * 1024 * 1024;

thread_local! {
    // One exact successful document per calling thread. No hash collision or
    // caller-supplied admission flag can authorize a different source.
    static VALIDATED_SOURCE: RefCell<Option<String>> = const { RefCell::new(None) };
}

pub fn check_source(text: &str) -> Result<(), String> {
    let timing = std::env::var_os("KM_CONFORMANCE_TIMING").is_some();
    let start = timing.then(std::time::Instant::now);
    let mut reused = false;
    let result = if std::env::var_os("KM_CACHE_CONFORMANCE").is_some() {
        VALIDATED_SOURCE.with(|cache| {
            let mut cache = cache.borrow_mut();
            reused = cache.as_deref() == Some(text);
            check_source_cached(text, &mut cache)
        })
    } else {
        check_source_uncached(text)
    };
    if let Some(start) = start {
        eprintln!("CONFORMANCE seconds={:.6} bytes={} reused={} ok={}",
            start.elapsed().as_secs_f64(), text.len(), reused, result.is_ok());
    }
    result
}

fn check_source_cached(text: &str, cache: &mut Option<String>) -> Result<(), String> {
    if cache.as_deref() == Some(text) {
        return Ok(());
    }
    check_source_uncached(text)?;
    if text.len() <= VALIDATED_SOURCE_CACHE_LIMIT {
        *cache = Some(text.to_owned());
    }
    Ok(())
}

fn check_source_uncached(text: &str) -> Result<(), String> {
    check_literal_datatypes(text)?;
    km_owl_functional_syntax::validate(text)?;
    let prefixes = prefixes(text)?;
    roles::check(text, &prefixes)?;
    anonymous::check(text, &prefixes)?;
    entities::check(text, &prefixes)?;
    datatypes::check(text, &prefixes)
}

/// Reject use of the top data range as a literal datatype. OWL 2 Direct
/// Semantics excludes rdfs:Literal from the lexical datatype map. Its use as
/// a range is legal; assigning it a lexical-to-value map would invent semantics.
/// Scan tokens so literals in DL-safe rules receive the same check as assertions.
pub fn check_literal_datatypes(text: &str) -> Result<(), String> {
    let prefixes = prefixes(text)?;
    let mut stream = tokens(text).peekable();
    while let Some(literal) = stream.next() {
        if !literal.starts_with('"') { continue; }
        // Validate the characters and functional-syntax escapes even for
        // untyped and language-tagged literals, including annotation values.
        lexical::check(literal, "http://www.w3.org/2001/XMLSchema#string")?;
        let Some(suffix) = stream.peek().copied() else { continue };
        if let Some(tag) = suffix.strip_prefix('@') {
            oxilangtag::LanguageTag::parse(tag).map_err(|error|
                format!("invalid OWL 2 DL input: malformed language tag @{tag}: {error}"))?;
            stream.next();
            continue;
        }
        let Some(datatype) = suffix.strip_prefix("^^") else { continue };
        stream.next();
        let datatype = if datatype.is_empty() { stream.next().unwrap_or("") } else { datatype };
        let expanded = expand(datatype, &prefixes);
        if expanded == "http://www.w3.org/2000/01/rdf-schema#Literal" {
            let offset = literal.as_ptr() as usize - text.as_ptr() as usize;
            let line = text[..offset].bytes().filter(|b| *b == b'\n').count() + 1;
            return Err(format!("invalid OWL 2 DL input at line {line}: literal {literal}^^{datatype} uses rdfs:Literal, which has no lexical space or lexical-to-value mapping. rdfs:Literal is allowed as a data range, not as a literal datatype. Use the intended concrete datatype (for text, xsd:string); KM will not rewrite this automatically."));
        }
        if !datatypes::builtin(&expanded) || expanded == "http://www.w3.org/2002/07/owl#real" {
            return Err(format!("invalid OWL 2 DL input: literal {literal}^^{datatype} has no lexical interpretation in the OWL 2 datatype map; custom datatype definitions specify data ranges, not new literal lexical mappings"));
        }
        lexical::check(literal, &expanded)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn exact_validation_cache_preserves_rejections_after_valid_input() {
        let valid = "Ontology(Declaration(Class(<urn:A>)))";
        let mut cache = None;
        check_source_cached(valid, &mut cache).unwrap();
        check_source_cached(valid, &mut cache).unwrap();
        for invalid in [
            "Ontology(Declaration(Class(<urn:A>))) trailing",
            "Ontology(Annotation(<urn:p> \"x\"^^rdfs:Literal))",
            "Ontology(TransitiveObjectProperty(<urn:r>) SubClassOf(<urn:A> ObjectMaxCardinality(1 <urn:r>)))",
        ] {
            let expected = check_source_uncached(invalid);
            assert!(expected.is_err());
            assert_eq!(check_source_cached(invalid, &mut cache), expected);
            assert_eq!(cache.as_deref(), Some(valid));
        }
        let replacement = "Ontology(Declaration(Class(<urn:B>)))";
        check_source_cached(replacement, &mut cache).unwrap();
        assert_eq!(cache.as_deref(), Some(replacement));
        check_source_cached(valid, &mut cache).unwrap();
    }

    #[test]
    fn exact_validation_cache_does_not_retain_oversized_sources() {
        let source = format!("Ontology(){}", " ".repeat(VALIDATED_SOURCE_CACHE_LIMIT));
        let mut cache = None;
        check_source_cached(&source, &mut cache).unwrap();
        assert!(cache.is_none());
    }

    #[test]
    fn public_prefix_declarations_are_unique_and_cannot_rebind_standard_names() {
        for source in [
            "Prefix(:=<urn:a:>) Prefix(:=<urn:b:>) Ontology()",
            "Prefix(p:=<urn:a:>) Prefix(p:=<urn:a:>) Ontology()",
        ] {
            assert!(check_iri_prefixes(source).unwrap_err().contains("more than once"));
        }
        for prefix in ["rdf", "rdfs", "xsd", "owl"] {
            let source = format!("Prefix({prefix}:=<urn:other:>) Ontology()");
            assert!(check_iri_prefixes(&source).unwrap_err().contains("cannot be rebound"));
        }
        check_iri_prefixes("Prefix(owl:=<http://www.w3.org/2002/07/owl#>) Prefix(:=<urn:a:>) Ontology(Declaration(Class(:A)))").unwrap();
        check_iri_prefixes("Prefix(a:=<urn:a:>) Prefix(b:=<urn:b:>) Ontology(SubClassOf(a:A b:B))").unwrap();
    }

    #[test]
    fn user_prefix_checks_cover_entity_and_rule_iris_without_scanning_literal_contents() {
        for source in [
            "Ontology(Declaration(Class(missing:A)))",
            "Ontology(Declaration(Class(:A)))",
            "Ontology(Annotation(rdfs:label missing:value))",
            "Ontology(DLSafeRule(Body(ClassAtom(owl:Thing Variable(missing:x))) Head(ClassAtom(owl:Thing <urn:a>))))",
            "Ontology(DataPropertyAssertion(<urn:p> <urn:a> \"1\"^^missing:integer))",
        ] {
            assert!(check_iri_prefixes(source).unwrap_err().contains("undeclared prefix"));
        }
        for source in [
            "Ontology(Declaration(Class(owl:Thing)))",
            "Prefix(:=<urn:test:>) Ontology(Declaration(Class(:A)) ClassAssertion(:A _:anonymous))",
            "Ontology(Annotation(rdfs:label \"missing:prefix\") Annotation(rdfs:label <urn:missing:prefix>))",
            "Ontology(DataPropertyAssertion(<urn:p> <urn:a> \"1\"^^ xsd:integer))",
        ] { check_iri_prefixes(source).unwrap(); }
        let error = check_iri_prefixes("Ontology(\n Declaration(Class(missing:A)))").unwrap_err();
        assert!(error.contains("line 2"));
    }

    #[test]
    fn grammar_rejects_wrong_arity_without_numeric_model_limits() {
        for source in ["Ontology(SubClassOf(:A))", "Ontology(ObjectPropertyAssertion(:p :a))",
            "Ontology(SubClassOf(:A ObjectComplementOf(:B :C)))"] {
            assert!(check_source(source).is_err(), "accepted {source}");
        }
        check_source("Ontology(SubClassOf(:A ObjectMinCardinality(4294967296 :r)))").unwrap();
        check_source("Ontology(SubObjectPropertyOf(ObjectPropertyChain(ObjectInverseOf(:r) :s) :t))").unwrap();
        check_source("Ontology(HasKey(:A (:r ObjectInverseOf(:s)) (:d)))").unwrap();
    }
    #[test]
    fn document_boundaries_cannot_silently_drop_input() {
        for text in ["", "garbage", "Ontology() garbage", "Ontology() Ontology()",
            "Ontology(", "Ontology(bare)", "Ontology(Ontology())", "Prefix Ontology()",
            "Ontology(Declaration(Class(:A)) <urn:late>)"] {
            assert!(check_source(text).is_err(), "accepted {text:?}");
        }
        for text in ["Ontology()", "Ontology(<urn:ontology>)",
            "Ontology(<urn:ontology> <urn:version>)", "# comment\nOntology() # trailing comment",
            "Prefix(:=<urn:example:>) Ontology(:ontology :version)"] {
            check_source(text).unwrap();
        }
    }
    #[test]
    fn source_validation_preserves_dl_safe_rules_and_top_data_ranges() {
        let source = r#"Prefix(:=<urn:conformance:>)
Ontology(
 Declaration(Class(:Patient))
 Declaration(DataProperty(:reasonForVisit))
 DataPropertyRange(:reasonForVisit rdfs:Literal)
 DataPropertyAssertion(:reasonForVisit :patient "Diabetes"^^xsd:string)
 DLSafeRule(
  Body(DataPropertyAtom(:reasonForVisit Variable(:x) "Diabetes"^^xsd:string))
  Head(ClassAtom(:Patient Variable(:x))))
)"#;
        check_source(source).unwrap();
        check_declarations(source).unwrap();
        let invalid = source.replace("\"Diabetes\"^^xsd:string", "\"Diabetes\"^^rdfs:Literal");
        assert!(check_source(&invalid).unwrap_err().contains("no lexical space"));
    }
    #[test]
    fn rejects_top_typed_literals_in_assertions_and_rules() {
        for datatype in ["rdfs:Literal", "<http://www.w3.org/2000/01/rdf-schema#Literal>", "top:Literal"] {
            for separator in ["^^", "^^ ", " ^^ "] {
                for axiom in [format!("DataPropertyAssertion(:p :a \"Diabetes\"{separator}{datatype})"),
                    format!("DLSafeRule(Body(DataPropertyAtom(:p Variable(:x) \"Diabetes\"{separator}{datatype})) Head(ClassAtom(:A Variable(:x))))")] {
                    let text = format!("Prefix(top:=<http://www.w3.org/2000/01/rdf-schema#>)\nOntology({axiom})");
                    let error = check_literal_datatypes(&text).unwrap_err();
                    assert!(error.contains("line 2"));
                    assert!(error.contains("no lexical space"));
                }
            }
        }
    }
    #[test]
    fn allows_ranges_strings_rules_and_nonstandard_prefix_binding() {
        for text in [
            "Ontology(DataPropertyRange(:p rdfs:Literal) DataPropertyAssertion(:p :a \"Diabetes\"^^xsd:string))",
            "Ontology(DLSafeRule(Body(DataPropertyAtom(:p Variable(:x) \"Diabetes\"^^xsd:string)) Head(ClassAtom(:A Variable(:x)))))",
            "# \"x\"^^rdfs:Literal\nOntology()",
            "Ontology(Annotation(rdfs:comment \"rdfs:Literal is a range\"))",
        ] { assert!(check_literal_datatypes(text).is_ok(), "{text}"); }
    }
    #[test]
    fn custom_and_real_datatypes_cannot_supply_literal_lexical_forms() {
        for datatype in ["owl:real", "custom:Literal", "xsd:date"] {
            assert!(check_literal_datatypes(&format!("Ontology(DataPropertyAssertion(:p :a \"1\"^^{datatype}))")).unwrap_err().contains("no lexical interpretation"));
        }
        let error = check_literal_datatypes("Prefix(rdfs:=<urn:custom:>) Ontology(DataPropertyAssertion(:p :a \"x\"^^rdfs:Literal))").unwrap_err();
        assert!(error.contains("no lexical interpretation"));
        assert!(!error.contains("uses rdfs:Literal"));
    }
    #[test]
    fn untyped_language_tagged_and_plain_literals_are_validated() {
        for literal in ["\"hello\"@en-GB", "\"hello@en-GB\"^^rdf:PlainLiteral", "\"hello@\"^^rdf:PlainLiteral", "\"hello\"@i-klingon"] {
            assert!(check_literal_datatypes(&format!("Ontology(Annotation(rdfs:label {literal}))")).is_ok(), "{literal}");
        }
        for literal in ["\"hello\"@en--GB", "\"hello\"@", "\"hello\"^^rdf:PlainLiteral", "\"hello@en--GB\"^^rdf:PlainLiteral", "\"bad\\q\"", "\"bad\u{0}\""] {
            assert!(check_literal_datatypes(&format!("Ontology(Annotation(rdfs:label {literal}))")).is_err(), "{literal}");
        }
    }
    #[test]
    fn rejects_13129_literal_pattern_without_rewriting() {
        let text = include_str!("../../../tests/conformance/invalid-top-literal.ofn");
        assert!(check_literal_datatypes(text).unwrap_err().contains("invalid OWL 2 DL input"));
    }
}
