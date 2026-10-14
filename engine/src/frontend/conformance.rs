//! Source conformance checks shared by public classification and the frontend.
//! Grammar validation includes DL-safe SWRL. This is not yet a complete OWL 2
//! DL profile checker: remaining global restrictions still require audit.
//! User-entry APIs enforce declarations separately from generated documents.
use std::collections::{BTreeMap, BTreeSet};
use std::sync::{Arc, Mutex};
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
    if USER_SOURCE.lock().unwrap_or_else(|e| e.into_inner()).as_ref().is_some_and(|(source, _)| &**source == text) {
        // check_user_source traversed exactly this document and found none.
        return Ok(false);
    }
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

/// `expand(datatype, prefixes) == target`, without building the expansion.
fn expands_to(datatype: &str, prefixes: &BTreeMap<String, String>, target: &str) -> bool {
    if let Some(iri) = datatype.strip_prefix('<').and_then(|s| s.strip_suffix('>')) {
        iri == target
    } else if let Some((prefix, local)) = datatype.split_once(':') {
        match prefixes.get(prefix) {
            Some(base) => target.strip_prefix(base.as_str()) == Some(local),
            None => datatype == target,
        }
    } else { datatype == target }
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
///
/// The exact-document caches below retain one shared copy of the last
/// accepted source. The bound covers every frozen ORE input; large sources are
/// otherwise re-validated by the supervisor, route probes and the in-process
/// frontend. The retained copy costs one source size of supervisor memory.
const VALIDATED_SOURCE_CACHE_LIMIT: usize = 1024 * 1024 * 1024;

// One exact successful document per process. No hash collision or
// caller-supplied admission flag can authorize a different source: a hit
// requires byte equality with the retained copy. Process-wide because the
// in-process frontend validates on its own thread.
static VALIDATED_SOURCE: Mutex<Option<Arc<str>>> = Mutex::new(None);

// One exact document that passed `check_user_source`, which includes the
// import scan, plus source facts computed in the same traversal. Populated
// only with `KM_CACHE_CONFORMANCE`, like the cache above.
static USER_SOURCE: Mutex<Option<(Arc<str>, SourceFacts)>> = Mutex::new(None);

/// Pure functions of a validated source document, computed during the shared
/// conformance traversal so the orchestrator's scheduling scans need not parse
/// the same text again. Each field equals the value its consumer would compute.
#[derive(Clone, Debug)]
pub struct SourceFacts {
    /// `SourceProfileBuilder` over every ontology child, finished with the
    /// document length; `None` above the data-source scan's 4 MiB bound.
    pub source_statistics: Option<super::profile::SourceStatistics>,
    /// The symbolic-source scheduling scan: some object cardinality restriction
    /// has a bound of at least 128 and the document has no DL-safe rule.
    pub high_object_cardinality_without_rules: bool,
}

/// Facts for exactly `text`, when `check_user_source` accepted it in this thread.
pub fn cached_source_facts(text: &str) -> Option<SourceFacts> {
    USER_SOURCE.lock().unwrap_or_else(|e| e.into_inner()).as_ref()
        .filter(|(source, _)| &**source == text).map(|(_, facts)| facts.clone())
}

const SOURCE_STATISTICS_BOUND: usize = 4 * 1024 * 1024;

/// Node form of the symbolic scheduler's token scan: a `DLSafeRule(` or an
/// object cardinality `(` followed by a numeric bound are exactly the list
/// nodes with those heads, because the parser makes a list from an
/// alphabetic token followed by `(` and keeps literals and IRIs atomic.
#[derive(Default)]
struct CardinalityScan { rule: bool, high: bool }

impl CardinalityScan {
    fn observe(&mut self, node: &Node<'_>) {
        if let Node::List(head, args) = node {
            match *head {
                "DLSafeRule" => self.rule = true,
                "ObjectMinCardinality" | "ObjectMaxCardinality" | "ObjectExactCardinality" => {
                    if let Some(Node::Atom(bound)) = args.first() {
                        self.high |= bound.parse::<u64>().is_ok_and(|n| n >= 128);
                    }
                }
                _ => {}
            }
            for arg in args { self.observe(arg); }
        }
    }
}

/// Why [`check_user_source`] rejected a document.
#[derive(Debug, PartialEq, Eq)]
pub enum UserSourceError {
    /// The document has an `Import`; the caller reports its loading limitation.
    Imports,
    /// The first conformance error, exactly as the separate checks report it.
    Invalid(String),
}

enum Slot<C> { Live(C), Failed(String) }

impl<C> Slot<C> {
    fn feed(&mut self, step: impl FnOnce(&mut C) -> Result<(), String>) {
        if let Slot::Live(checker) = self {
            if let Err(error) = step(checker) {
                *self = Slot::Failed(error);
            }
        }
    }
}

/// The user-entry sequence `has_imports` (an import is rejected),
/// `check_source`, `check_iri_prefixes` and `check_declarations`, with one
/// shared parse for the import scan and the four node checkers.
///
/// Each checker receives the same ontology children, in the same order, as
/// its own traversal would, and stops at its own first error; results are
/// reported in the original order. The traversal reports a parse error first,
/// as `has_imports` does. Every accept/reject decision and message is
/// unchanged; only the repeated parses are gone.
pub fn check_user_source(text: &str) -> Result<(), UserSourceError> {
    use UserSourceError::*;
    let timing = std::env::var_os("KM_CONFORMANCE_TIMING").is_some();
    let start = timing.then(std::time::Instant::now);
    let prefix_map = prefixes(text);
    let mut imports = false;
    let mut roles = Slot::Live(roles::Checker::default());
    let mut anonymous = Slot::Live(anonymous::Checker::default());
    let mut entities = Slot::Live(entities::Checker::default());
    let mut datatypes = Slot::Live(datatypes::Checker::default());
    let cache_enabled = std::env::var_os("KM_CACHE_CONFORMANCE").is_some()
        && text.len() <= VALIDATED_SOURCE_CACHE_LIMIT;
    let mut profile = (cache_enabled && text.len() <= SOURCE_STATISTICS_BOUND)
        .then(super::profile::SourceProfileBuilder::new);
    let mut cardinality = CardinalityScan::default();
    let mut lap = [0f64; 4];
    let mut clock = |slot: usize, step: &mut dyn FnMut()| {
        if timing {
            let t = std::time::Instant::now();
            step();
            lap[slot] += t.elapsed().as_secs_f64();
        } else {
            step();
        }
    };
    super::parse::for_each_ontology_child(text, |node| {
        imports |= node.head() == Some("Import");
        if let Ok(map) = &prefix_map {
            clock(0, &mut || roles.feed(|c| c.observe(node, map)));
            clock(1, &mut || anonymous.feed(|c| c.observe(node, map)));
            clock(2, &mut || entities.feed(|c| c.observe(node, map)));
            clock(3, &mut || datatypes.feed(|c| c.observe(node, map)));
        }
        if cache_enabled {
            if let Some(profile) = profile.as_mut() { profile.observe(node); }
            cardinality.observe(node);
        }
        Ok(())
    }).map_err(|error| Invalid(error.0))?;
    if timing {
        eprintln!("CONFORMANCE traversal seconds={:.6} roles={:.6} anonymous={:.6} entities={:.6} datatypes={:.6}",
            start.map_or(0.0, |s| s.elapsed().as_secs_f64()), lap[0], lap[1], lap[2], lap[3]);
    }
    if imports {
        return Err(Imports);
    }
    let reused = cache_enabled
        && VALIDATED_SOURCE.lock().unwrap_or_else(|e| e.into_inner()).as_deref() == Some(text);
    if !reused {
        let t = timing.then(std::time::Instant::now);
        check_literal_datatypes(text).map_err(Invalid)?;
        let t2 = timing.then(std::time::Instant::now);
        km_owl_functional_syntax::validate(text).map_err(Invalid)?;
        if let (Some(t), Some(t2)) = (t, t2) {
            eprintln!("CONFORMANCE literal_datatypes={:.6} grammar={:.6}",
                (t2 - t).as_secs_f64(), t2.elapsed().as_secs_f64());
        }
        prefix_map.as_ref().map_err(|error| Invalid(error.clone()))?;
        match roles { Slot::Failed(error) => return Err(Invalid(error)), Slot::Live(c) => c.finish().map_err(Invalid)? }
        match anonymous { Slot::Failed(error) => return Err(Invalid(error)), Slot::Live(c) => c.finish().map_err(Invalid)? }
        match &entities { Slot::Failed(error) => return Err(Invalid(error.clone())), Slot::Live(c) => c.finish().map_err(Invalid)? }
        match datatypes { Slot::Failed(error) => return Err(Invalid(error)), Slot::Live(c) => c.finish().map_err(Invalid)? }
        if cache_enabled {
            *VALIDATED_SOURCE.lock().unwrap_or_else(|e| e.into_inner()) = Some(Arc::from(text));
        }
    }
    check_iri_prefixes(text).map_err(Invalid)?;
    // check_declarations: its prefix map, declaration check, then finish().
    prefix_map.as_ref().map_err(|error| Invalid(error.clone()))?;
    match &entities {
        // Without a cache hit `finish` already passed above; it is a pure
        // function of the checker, so only a reused document needs it here.
        Slot::Live(c) => { c.declarations().map_err(Invalid)?; if reused { c.finish().map_err(Invalid)?; } }
        // A cached document passed every checker earlier, so this is unreachable
        // there; without the cache the error was already returned above.
        Slot::Failed(error) => return Err(Invalid(error.clone())),
    }
    if cache_enabled {
        let facts = SourceFacts {
            source_statistics: profile.map(|profile| profile.finish(text.len() as u64).source),
            high_object_cardinality_without_rules: cardinality.high && !cardinality.rule,
        };
        // Share one retained copy between both exact-document caches.
        let retained = VALIDATED_SOURCE.lock().unwrap_or_else(|e| e.into_inner()).clone()
            .filter(|cached| &**cached == text).unwrap_or_else(|| Arc::from(text));
        *USER_SOURCE.lock().unwrap_or_else(|e| e.into_inner()) = Some((retained, facts));
    }
    if let Some(start) = start {
        eprintln!("CONFORMANCE user-source seconds={:.6} bytes={} reused={}",
            start.elapsed().as_secs_f64(), text.len(), reused);
    }
    Ok(())
}

pub fn check_source(text: &str) -> Result<(), String> {
    let timing = std::env::var_os("KM_CONFORMANCE_TIMING").is_some();
    let start = timing.then(std::time::Instant::now);
    let mut reused = false;
    let result = if std::env::var_os("KM_CACHE_CONFORMANCE").is_some() {
        // Take the retained copy out while validating so the lock is never
        // held across a long check; put it, or the new document, back after.
        let mut cache = VALIDATED_SOURCE.lock().unwrap_or_else(|e| e.into_inner()).take();
        reused = cache.as_deref() == Some(text);
        let result = check_source_cached(text, &mut cache, VALIDATED_SOURCE_CACHE_LIMIT);
        *VALIDATED_SOURCE.lock().unwrap_or_else(|e| e.into_inner()) = cache;
        result
    } else {
        check_source_uncached(text)
    };
    if let Some(start) = start {
        eprintln!("CONFORMANCE seconds={:.6} bytes={} reused={} ok={}",
            start.elapsed().as_secs_f64(), text.len(), reused, result.is_ok());
    }
    result
}

fn check_source_cached(text: &str, cache: &mut Option<Arc<str>>, limit: usize) -> Result<(), String> {
    if cache.as_deref() == Some(text) {
        return Ok(());
    }
    check_source_uncached(text)?;
    if text.len() <= limit {
        *cache = Some(Arc::from(text));
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
        check_source_cached(valid, &mut cache, VALIDATED_SOURCE_CACHE_LIMIT).unwrap();
        check_source_cached(valid, &mut cache, VALIDATED_SOURCE_CACHE_LIMIT).unwrap();
        for invalid in [
            "Ontology(Declaration(Class(<urn:A>))) trailing",
            "Ontology(Annotation(<urn:p> \"x\"^^rdfs:Literal))",
            "Ontology(TransitiveObjectProperty(<urn:r>) SubClassOf(<urn:A> ObjectMaxCardinality(1 <urn:r>)))",
        ] {
            let expected = check_source_uncached(invalid);
            assert!(expected.is_err());
            assert_eq!(check_source_cached(invalid, &mut cache, VALIDATED_SOURCE_CACHE_LIMIT), expected);
            assert_eq!(cache.as_deref(), Some(valid));
        }
        let replacement = "Ontology(Declaration(Class(<urn:B>)))";
        check_source_cached(replacement, &mut cache, VALIDATED_SOURCE_CACHE_LIMIT).unwrap();
        assert_eq!(cache.as_deref(), Some(replacement));
        check_source_cached(valid, &mut cache, VALIDATED_SOURCE_CACHE_LIMIT).unwrap();
    }

    #[test]
    fn exact_validation_cache_does_not_retain_oversized_sources() {
        // The production bound is 1 GiB; the same rule is exercised at 1 KiB.
        let limit = 1024;
        let source = format!("Ontology(){}", " ".repeat(limit));
        let mut cache = None;
        check_source_cached(&source, &mut cache, limit).unwrap();
        assert!(cache.is_none());
        let small = "Ontology()";
        check_source_cached(small, &mut cache, limit).unwrap();
        assert_eq!(cache.as_deref(), Some(small));
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
