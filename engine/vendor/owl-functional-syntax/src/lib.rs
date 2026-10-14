//! Grammar-only validation; see README.md for upstream provenance and license.
use pest::Parser;
use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "grammars/bcp47.pest"]
#[grammar = "grammars/rfc3987.pest"]
#[grammar = "grammars/sparql.pest"]
#[grammar = "grammars/ofn.pest"]
struct FunctionalSyntax;

pub mod fast;

/// Validate a functional-syntax document. Every validator below has the same
/// accept/reject results and error text; they differ only in cost. The default
/// is the hand-written recognizer; `KM_GRAMMAR_VALIDATOR` selects another one
/// (`original`, `iri-cached`, `iri-cached-ascii`) for differential checks.
pub fn validate(source: &str) -> Result<(), String> {
    match std::env::var("KM_GRAMMAR_VALIDATOR").as_deref() {
        Ok("original") => validate_original(source),
        Ok("iri-cached") => validate_iri_cached(source),
        Ok("iri-cached-ascii") => validate_iri_cached_ascii(source),
        _ => validate_handwritten(source),
    }
}

pub fn validate_original(source: &str) -> Result<(), String> {
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
    validate_iri_cached_impl(source, false)
}

/// Same structural grammar and original-validator fallback, with a sufficient
/// ASCII HTTP(S) spelling check before invoking the full RFC grammar.
pub fn validate_iri_cached_ascii(source: &str) -> Result<(), String> {
    validate_iri_cached_impl(source, true)
}

/// Byte classes for [`ascii_http_iri`]: bit 0 = `RFC3987_IriUnreserved`
/// (ASCII part), bit 1 = a path/fragment byte other than `%` and `#`
/// (`/`, unreserved, sub-delims, `:`, `@`).
const ASCII_IRI_CLASS: [u8; 256] = {
    let mut table = [0u8; 256];
    let mut b = 0;
    while b < 256 {
        let c = b as u8;
        let unreserved = c.is_ascii_alphanumeric() || matches!(c, b'-' | b'.' | b'_' | b'~');
        let path = unreserved
            || matches!(c, b'/' | b':' | b'@'
                | b'!' | b'$' | b'&' | b'\'' | b'(' | b')' | b'*' | b'+' | b';' | b'=' | b',');
        table[b] = (unreserved as u8) | ((path as u8) << 1);
        b += 1;
    }
    table
};

pub(crate) fn ascii_http_iri(iri: &str) -> bool {
    let Some(body) = iri.strip_prefix("<http://")
        .or_else(|| iri.strip_prefix("<https://"))
        .and_then(|body| body.strip_suffix('>')) else { return false; };
    let body = body.as_bytes();
    let host_end = body.iter().position(|&b| b == b'/' || b == b'#').unwrap_or(body.len());
    let (host, tail) = body.split_at(host_end);
    // An alphabetic first byte excludes the grammar's earlier IPv4 branch,
    // which can consume a numeric host prefix before RegName is considered.
    if !host.first().is_some_and(u8::is_ascii_alphabetic) {
        return false;
    }
    if !host.iter().all(|&b| ASCII_IRI_CLASS[b as usize] & 1 != 0) { return false; }
    // Path segments and the fragment: every byte is `/` or an ASCII
    // `RFC3987_IriIpChar` (unreserved, sub-delims, `:`, `@`, or a complete
    // `%` HEXDIG HEXDIG). Each such character is consumed greedily by
    // `RFC3987_IriSegment` / `RFC3987_IriFragment`, so the grammar reaches the
    // closing `>` exactly when every byte qualifies. `?` (query) and a second
    // `#` still defer to the grammar.
    let mut fragment = false;
    let mut i = 0;
    while i < tail.len() {
        let byte = tail[i];
        if ASCII_IRI_CLASS[byte as usize] & 2 != 0 {
            i += 1;
        } else if byte == b'%' {
            if i + 2 < tail.len() && tail[i + 1].is_ascii_hexdigit() && tail[i + 2].is_ascii_hexdigit() {
                i += 3;
            } else {
                return false;
            }
        } else if byte == b'#' && !fragment {
            fragment = true;
            i += 1;
        } else {
            return false;
        }
    }
    true
}

/// Hand-written structural recognizer (`fast`) with the original atomic
/// `FullIRI` and `BCP47_LanguageTag` rules applied to each distinct spelling.
/// Any undecided document, IRI, or tag runs the cached pest validator, which
/// still produces every rejection and its original error text.
pub fn validate_handwritten(source: &str) -> Result<(), String> {
    if let Some(recognized) = fast::recognize(source) {
        let iris_ok = recognized.full_iris.iter().all(|iri| full_iri_accepted(iri, true));
        let tags_ok = iris_ok && recognized.language_tags.iter().all(|tag| {
            FunctionalSyntax::parse(Rule::BCP47_LanguageTag, tag)
                .is_ok_and(|mut pairs| pairs.next().is_some_and(|p| p.as_span().end() == tag.len()))
        });
        if tags_ok {
            return Ok(());
        }
    }
    validate_iri_cached_impl(source, true)
}

fn full_iri_accepted(iri: &str, ascii_fast_path: bool) -> bool {
    (ascii_fast_path && ascii_http_iri(iri)) || {
        let checked = FunctionalSyntax::parse(Rule::FullIRI, iri);
        checked.is_ok_and(|mut pairs| pairs.next()
            .is_some_and(|p| p.as_span().end() == iri.len()))
    }
}

fn validate_iri_cached_impl(source: &str, ascii_fast_path: bool) -> Result<(), String> {
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
                    let valid = full_iri_accepted(iri, ascii_fast_path);
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
    fn ascii_http_subset_is_accepted_by_original_full_iri_rule() {
        let mut cases = vec![
            "<http://purl.obolibrary.org/obo/GO_0008150>".to_owned(),
            "<https://www.w3.org/2002/07/owl#Thing>".to_owned(),
            "<http://a>".to_owned(), "<http://a/#>".to_owned(),
            "<http://a//b/#c/d>".to_owned(),
        ];
        for byte in 0..=127u8 {
            for template in ["<http://a{}b/x#y>", "<http://ab/{}x#y>",
                "<http://ab/x#{}y>", "<http://ab/x{}>", "<http://ab/{}>", "<http://ab/x#{}>",
                "<http://ab{}>", "<http://ab/%{}0>", "<http://ab/%0{}>", "<http://ab/x#%{}a>"] {
                cases.push(template.replace("{}", &char::from(byte).to_string()));
            }
        }
        for iri in ["<http://purl.obolibrary.org/obo/MGI_MGI%3A1929705-GO%3A0006886>",
            "<http://purl.obolibrary.org/obo/MGI_MGI:107706>", "<http://a/b:c@d!$&'()*+,;=>",
            "<http://a/%>", "<http://a/%4>", "<http://a/%4g>", "<http://a/%41%>", "<http://a#b%2Fc>",
            "<http://a/b%>", "<http://a/:>", "<http://a/@>", "<http://a#:@>", "<http://a:/b>"] {
            cases.push(iri.to_owned());
        }
        for iri in cases {
            if ascii_http_iri(&iri) {
                let mut pairs = FunctionalSyntax::parse(Rule::FullIRI, &iri).unwrap();
                assert_eq!(pairs.next().unwrap().as_span().end(), iri.len(), "{iri}");
            }
            let source = format!("Ontology(Declaration(Class({iri})))");
            assert_eq!(validate_original(&source), validate_iri_cached_ascii(&source), "{iri}");
        }
        for iri in ["<http://127.0.0.1/a>", "<http://1.2.3.4abc/a>",
            "<http://[::1]/a>", "<http://a:80/b>", "<http://u@a/b>",
            "<http://a/b?q=c>", "<http://a/%2>", "<http://a/é>",
            "<http://a/b#c#d>", "<http:///a>", "<https://a/\\b>"] {
            assert!(!ascii_http_iri(iri), "specialized check must defer: {iri}");
            let source = format!("Ontology(Declaration(Class({iri})))");
            assert_eq!(validate_original(&source), validate_iri_cached_ascii(&source), "{iri}");
        }
    }

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
                assert_eq!(old, validate_iri_cached_ascii(&source), "{source}");
            }
        }
        for source in ["Ontology(", "Ontology() trailing", "Ontology() Ontology()",
            "Ontology(SubClassOf(<urn:A>))", "Ontology(Annotation(<urn:p> \"<not an IRI>\"))",
            "# <not an IRI>\nOntology()"] {
            assert_eq!(validate_original(source), validate_iri_cached(source), "{source}");
            assert_eq!(validate_original(source), validate_iri_cached_ascii(source), "{source}");
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
    fn handwritten_recognizer_matches_original_on_peg_edge_cases() {
        let bodies = [
            "SubClassOf(:A DataSomeValuesFrom(:p xsd:int))",
            "SubClassOf(:A DataSomeValuesFrom(:p :q xsd:int))",
            "SubClassOf(:A DataSomeValuesFrom(:p #c\n xsd:int #c\n ))",
            "SubClassOf(:A DataSomeValuesFrom(xsd:int))",
            "SubClassOf(:A DataAllValuesFrom(:p DataOneOf(\"a\" \"b\"@en)))",
            "SubClassOf(:A DataSomeValuesFrom(:p DatatypeRestriction(xsd:int xsd:minInclusive \"1\"^^xsd:int)))",
            "SubClassOf(:A DataMinCardinality(1 :p))", "SubClassOf(:A DataMinCardinality(1 :p xsd:int))",
            "SubClassOf(:A ObjectMinCardinality(01:r))", "SubClassOf(:A ObjectExactCardinality(2 :r :B))",
            "SubClassOf(ObjectSomeValuesFrom:x :B)", "SubClassOf(ObjectSomeValuesFrom: :B)",
            "SubClassOf( :A :B )", "SubClassOf\n(:A :B)", "SubClassOf(:A#c\n:B)",
            "SubClassOf(a:b.c :B)", "SubClassOf(a:b. :B)", "SubClassOf(a:b..c :B)", "SubClassOf(a.b:c :B)",
            "SubClassOf(.a:b :B)", "SubClassOf(a:-b :B)", "SubClassOf(a:1 :B)", "SubClassOf(é:ü·x :B)",
            "ClassAssertion(:A _:x)", "ClassAssertion(:A _:)", "ClassAssertion(:A _:1.2)",
            "Annotation(:p \"x\" ^ ^ xsd:string)", "Annotation(:p \"x\"^^)", "Annotation(:p \"x\" @en)",
            "Annotation(:p \"x\"@en-)", "Annotation(:p \"x\"@x-private)", "Annotation(:p \"x\"@i-klingon)",
            "Annotation(:p \"x\"@en-GB-oed)", "Annotation(:p \"x\"@123)", "Annotation(:p \"a\\\"b\\\\\")",
            "Annotation(:p \"x\"\"y\")", "Annotation(:p _:n)", "Annotation(Annotation(:q :v) :p :v)",
            "Declaration(Annotation(:q :v) Class(:A))", "Declaration(Class (:A))", "Declaration(Classes(:A))",
            "AnnotationAssertion(:p _:s \"v\")", "AnnotationAssertion(:p :s _:v)",
            "SubObjectPropertyOf(ObjectPropertyChain(:r ObjectInverseOf(:s)) :t)",
            "SubObjectPropertyOf(ObjectPropertyChain(:r) :t)", "SubObjectPropertyOf(ObjectInverseOf(:r) :t)",
            "InverseObjectProperties(:r :s)", "InverseObjectProperties(:r ObjectInverseOf(:s))",
            "HasKey(:A () ())", "HasKey(:A (:r ObjectInverseOf(:s)) (:d :e))",
            "DLSafeRule(Body(ClassAtom(:A Variable(:x)) BuiltInAtom(:f \"1\" Variable(:y))) Head())",
            "DLSafeRule(Body(DataRangeAtom(xsd:int Variable(:x)) SameIndividualAtom(:a _:b)) Head(DifferentIndividualsAtom(Variable(:x) :c)))",
            "DLSafeRule(Body(DataPropertyAtom(:p :a \"v\")) Head(ObjectPropertyAtom(ObjectInverseOf(:r) :a :b)))",
            "DescriptionGraph(Nodes(NodeAssertion(:A :n)) Edges(EdgeAssertion(:r :n :n)) MainClasses(:A))",
            "DatatypeDefinition(:d DataIntersectionOf(xsd:int DataComplementOf(xsd:string)))",
            "DatatypeDefinition(:d DataUnionOf(xsd:int))", "DisjointUnion(:A :B :C)", "DisjointUnion(:A :B)",
            "SameIndividual(:a _:b :c)", "NegativeDataPropertyAssertion(:p :a \"1\"^^xsd:int)",
            "SubClassOf(:A ObjectHasSelf(ObjectInverseOf(:r)))", "SubClassOf(:A ObjectOneOf())",
            "EquivalentClasses(:A)", "SubClassOf(:A <urn:x> )", "SubClassOf(:A <urn:x>>)", "SubClassOf(:A <urn:x)",
        ];
        let mut documents = vec![
            String::new(), "Ontology()".into(), " Ontology() ".into(), "Ontology()#c".into(), "\u{feff}Ontology()".into(),
            "Prefix(:=<urn:a:>)Ontology()".into(), "Prefix( : = <urn:a:> ) Ontology()".into(),
            "Prefix(a.b:=<urn:a:>) Ontology()".into(), "Prefix(a:b:=<urn:a:>) Ontology()".into(),
            "Ontology(<urn:o> <urn:v> Import(<urn:i>) Annotation(:p :v) SubClassOf(:A :B))".into(),
            "Ontology(<urn:o> <urn:v> <urn:w>)".into(), "Ontology(SubClassOf(:A :B) Annotation(:p :v))".into(),
            "Ontology(Import(<urn:i>) Import(a:b))".into(),
        ];
        for body in bodies {
            documents.push(format!("Prefix(:=<urn:a:>) Ontology({body})"));
        }
        for text in documents {
            assert_eq!(validate_handwritten(&text), validate_original(&text), "{text:?}");
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
