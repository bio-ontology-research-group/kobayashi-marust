//! Resolve six OWL semantic constants without changing ordinary source names.
//!
//! The original source must pass the public conformance boundary first. This
//! preserves source bytes outside semantic builtin tokens, including annotations,
//! comments, literals, ontology identity, and every nonbuiltin entity spelling.
use std::borrow::Cow;
use std::collections::BTreeMap;
use super::sexpr::{Node, Parser};

const OWL: &str = "http://www.w3.org/2002/07/owl#";
const BUILTINS: [(&str, &str, &str); 6] = [
    ("http://www.w3.org/2002/07/owl#Thing", "owl:Thing", "<http://www.w3.org/2002/07/owl#Thing>"),
    ("http://www.w3.org/2002/07/owl#Nothing", "owl:Nothing", "<http://www.w3.org/2002/07/owl#Nothing>"),
    ("http://www.w3.org/2002/07/owl#topObjectProperty", "owl:topObjectProperty", "<http://www.w3.org/2002/07/owl#topObjectProperty>"),
    ("http://www.w3.org/2002/07/owl#bottomObjectProperty", "owl:bottomObjectProperty", "<http://www.w3.org/2002/07/owl#bottomObjectProperty>"),
    ("http://www.w3.org/2002/07/owl#topDataProperty", "owl:topDataProperty", "<http://www.w3.org/2002/07/owl#topDataProperty>"),
    ("http://www.w3.org/2002/07/owl#bottomDataProperty", "owl:bottomDataProperty", "<http://www.w3.org/2002/07/owl#bottomDataProperty>"),
];

/// Canonicalize the source before parsing: nonstandard spellings of the six
/// OWL semantic constants, then mixed spellings of one entity (a full IRI and
/// a prefixed name that expands to it). Sources without either stay
/// byte-identical.
pub fn canonicalize(text: &str) -> Result<Cow<'_, str>, String> {
    match canonicalize_builtins(text)? {
        Cow::Borrowed(t) => canonicalize_entity_spellings(t),
        Cow::Owned(t) => Ok(Cow::Owned(canonicalize_entity_spellings(&t)?.into_owned())),
    }
}

/// Namespaces whose prefixed names are vocabulary, not source entities.
const VOCABULARY: [&str; 4] = [
    "http://www.w3.org/2002/07/owl#",
    "http://www.w3.org/1999/02/22-rdf-syntax-ns#",
    "http://www.w3.org/2000/01/rdf-schema#",
    "http://www.w3.org/2001/XMLSchema#",
];

/// One entity may be written as a full IRI `<ns:local>` and as a prefixed name
/// `p:local` with `Prefix(p:=<ns:>)`. OWL identifies the two; KM's IRI registry
/// keys entities by spelling. Where a document uses both spellings for the
/// same IRI, rewrite every prefixed occurrence of that IRI to the full IRI.
fn canonicalize_entity_spellings(text: &str) -> Result<Cow<'_, str>, String> {
    let mut parser = Parser::new(text);
    let mut prefixes: BTreeMap<String, String> = BTreeMap::new();
    while parser.peek() == Some("Prefix") {
        let Node::List("Prefix", args) = parser.parse()? else {
            return Err("spelling canonicalization: malformed Prefix".into());
        };
        let parts: Option<Vec<_>> = args.iter().map(Node::as_atom).collect();
        let definition = parts.ok_or("spelling canonicalization: non-atom Prefix")?.concat();
        let (prefix, value) = definition.split_once(":=")
            .ok_or("spelling canonicalization: malformed Prefix binding")?;
        let iri = value.strip_prefix('<').and_then(|v| v.strip_suffix('>'))
            .ok_or("spelling canonicalization: malformed Prefix IRI")?;
        if prefix != "_" && !VOCABULARY.contains(&iri) {
            prefixes.insert(prefix.to_owned(), iri.to_owned());
        }
    }
    if prefixes.is_empty() {
        return Ok(Cow::Borrowed(text));
    }
    if parser.next_tok() != Some("Ontology") || parser.next_tok() != Some("(") {
        return Err("spelling canonicalization: missing Ontology(".into());
    }
    let expand = |token: &str| -> Option<String> {
        if token.starts_with('<') || token.starts_with('"') || token.starts_with("_:") {
            return None;
        }
        let (prefix, local) = token.split_once(':')?;
        prefixes.get(prefix).map(|ns| format!("{ns}{local}"))
    };
    let mut full_iris: std::collections::BTreeSet<&str> = std::collections::BTreeSet::new();
    let mut prefixed: Vec<(usize, usize, String)> = Vec::new();
    fn visit<'a>(
        text: &'a str,
        node: &Node<'a>,
        expand: &dyn Fn(&str) -> Option<String>,
        full_iris: &mut std::collections::BTreeSet<&'a str>,
        prefixed: &mut Vec<(usize, usize, String)>,
    ) -> Result<(), String> {
        match node {
            Node::List("Annotation" | "AnnotationAssertion" | "SubAnnotationPropertyOf"
                | "AnnotationPropertyDomain" | "AnnotationPropertyRange", _) => {}
            Node::List(_, args) => {
                for arg in args {
                    visit(text, arg, expand, full_iris, prefixed)?;
                }
            }
            Node::Atom(token) => {
                if let Some(iri) = token.strip_prefix('<').and_then(|t| t.strip_suffix('>')) {
                    full_iris.insert(iri);
                } else if let Some(iri) = expand(token) {
                    let start = (token.as_ptr() as usize).checked_sub(text.as_ptr() as usize)
                        .ok_or("spelling canonicalization: foreign token")?;
                    let end = start + token.len();
                    if text.get(start..end) != Some(*token) {
                        return Err("spelling canonicalization: invalid token range".into());
                    }
                    prefixed.push((start, end, iri));
                }
            }
        }
        Ok(())
    }
    while parser.peek() != Some(")") {
        if parser.peek().is_none() {
            return Err("spelling canonicalization: unterminated Ontology".into());
        }
        if let node @ Node::List(_, _) = parser.parse()? {
            visit(text, &node, &expand, &mut full_iris, &mut prefixed)?;
        }
    }
    // An IRI is respelled in full when it has more than one spelling: the
    // full form, or two prefixes bound to the same namespace.
    let mut spellings: BTreeMap<&str, std::collections::BTreeSet<&str>> = BTreeMap::new();
    for (start, end, iri) in &prefixed {
        spellings.entry(iri.as_str()).or_default().insert(&text[*start..*end]);
    }
    let respell: std::collections::BTreeSet<String> = spellings
        .iter()
        .filter(|(iri, forms)| forms.len() > 1 || full_iris.contains(*iri))
        .map(|(iri, _)| (*iri).to_owned())
        .collect();
    let mut edits: Vec<(usize, usize, String)> = prefixed
        .into_iter()
        .filter(|(_, _, iri)| respell.contains(iri.as_str()))
        .collect();
    if edits.is_empty() {
        return Ok(Cow::Borrowed(text));
    }
    edits.sort_by_key(|e| e.0);
    let mut out = String::with_capacity(text.len() + edits.len() * 16);
    let mut copied = 0;
    for (start, end, iri) in edits {
        if start < copied {
            return Err("spelling canonicalization: overlapping tokens".into());
        }
        out.push_str(&text[copied..start]);
        out.push('<');
        out.push_str(&iri);
        out.push('>');
        copied = end;
    }
    out.push_str(&text[copied..]);
    Ok(Cow::Owned(out))
}

/// Canonicalize nonstandard abbreviated spellings of six semantic constants.
/// Already supported full IRIs and `owl:` spellings remain byte-identical.
/// No owned source buffer or ontology traversal when no relevant alias occurs.
/// This is not an OWL validator; callers must validate the original source.
fn canonicalize_builtins(text: &str) -> Result<Cow<'_, str>, String> {
    let mut parser = Parser::new(text);
    let mut prefixes = BTreeMap::new();
    while parser.peek() == Some("Prefix") {
        let Node::List("Prefix", args) = parser.parse()? else {
            return Err("builtin canonicalization: malformed Prefix".into());
        };
        let parts: Option<Vec<_>> = args.iter().map(Node::as_atom).collect();
        let definition = parts.ok_or("builtin canonicalization: non-atom Prefix")?.concat();
        let (prefix, value) = definition.split_once(":=")
            .ok_or("builtin canonicalization: malformed Prefix binding")?;
        let iri = value.strip_prefix('<').and_then(|v| v.strip_suffix('>'))
            .ok_or("builtin canonicalization: malformed Prefix IRI")?;
        if prefix == "owl" && iri != OWL {
            return Err("builtin canonicalization: rebound owl prefix".into());
        }
        if prefixes.insert(prefix.to_owned(), iri.to_owned()).is_some() {
            return Err("builtin canonicalization: duplicate Prefix".into());
        }
    }
    let mut aliases = BTreeMap::new();
    for (prefix, iri) in &prefixes {
        // Blank node IDs remain anonymous even if a source declares `_:`.
        if prefix == "_" { continue; }
        for &(full, canonical, replacement) in &BUILTINS {
            if let Some(local) = full.strip_prefix(iri) {
                let alias = format!("{prefix}:{local}");
                if alias != canonical && text.contains(&alias) {
                    aliases.insert(alias, replacement);
                }
            }
        }
    }
    if aliases.is_empty() { return Ok(Cow::Borrowed(text)); }
    if parser.next_tok() != Some("Ontology") || parser.next_tok() != Some("(") {
        return Err("builtin canonicalization: missing Ontology(".into());
    }
    let mut edits = Vec::new();
    while parser.peek() != Some(")") {
        if parser.peek().is_none() {
            return Err("builtin canonicalization: unterminated Ontology".into());
        }
        // One axiom subtree at a time; bare ontology/version IRIs stay intact.
        if let node @ Node::List(_, _) = parser.parse()? {
            collect(text, &node, &aliases, &mut edits)?;
        }
    }
    parser.next_tok();
    if parser.peek().is_some() {
        return Err("builtin canonicalization: trailing source".into());
    }
    if edits.is_empty() { return Ok(Cow::Borrowed(text)); }
    let mut out = String::with_capacity(text.len());
    let mut copied = 0;
    for (start, end, canonical) in edits {
        if start < copied { return Err("builtin canonicalization: overlapping tokens".into()); }
        out.push_str(&text[copied..start]);
        out.push_str(canonical);
        copied = end;
    }
    out.push_str(&text[copied..]);
    Ok(Cow::Owned(out))
}

fn collect<'a>(text: &'a str, node: &Node<'a>, aliases: &BTreeMap<String, &'static str>,
    edits: &mut Vec<(usize, usize, &'static str)>) -> Result<(), String>
{
    match node {
        Node::List("Annotation" | "AnnotationAssertion" | "SubAnnotationPropertyOf"
            | "AnnotationPropertyDomain" | "AnnotationPropertyRange", _) => {},
        Node::List(_, args) => for arg in args { collect(text, arg, aliases, edits)?; },
        Node::Atom(token) if token.starts_with("_:") => {},
        Node::Atom(token) => if let Some(&canonical) = aliases.get(*token) {
            let start = (token.as_ptr() as usize).checked_sub(text.as_ptr() as usize)
                .ok_or("builtin canonicalization: foreign token")?;
            let end = start.checked_add(token.len())
                .ok_or("builtin canonicalization: token overflow")?;
            if text.get(start..end) != Some(*token) {
                return Err("builtin canonicalization: invalid token range".into());
            }
            edits.push((start, end, canonical));
        },
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn all_six_resolved_aliases_and_idempotence() {
        for &(full, _canonical, replacement) in &BUILTINS {
            let local = full.strip_prefix(OWL).unwrap();
            let source = format!("Prefix(o:=<{OWL}>) Ontology(Declaration(Class(o:{local})))");
            let expected = source.replace(&format!("Class(o:{local})"), &format!("Class({replacement})"));
            let actual = canonicalize(&source).unwrap();assert_eq!(actual, expected);
            assert!(matches!(canonicalize(&actual).unwrap(), Cow::Borrowed(_)));
        }
    }
    #[test]
    fn canonical_and_unrelated_inputs_borrow_original() {
        for source in ["Ontology(SubClassOf(owl:Thing owl:Nothing))", "Ontology(SubClassOf(<http://www.w3.org/2002/07/owl#Thing> <http://www.w3.org/2002/07/owl#Nothing>))", "Prefix(o:=<urn:unrelated#>) Ontology(SubClassOf(o:Thing o:Nothing))", "Prefix(o:=<http://www.w3.org/2002/07/owl#>) Ontology(SubClassOf(o:NothingElse <urn:A>))"] {
            let result=canonicalize(source).unwrap();assert!(matches!(result,Cow::Borrowed(_)));assert_eq!(result.as_ptr(),source.as_ptr());
        }
    }
    #[test]
    fn preserves_comments_literal_escapes_annotation_bytes_and_headers() {
        let source = r###"Prefix(o:=<http://www.w3.org/2002/07/owl#>)
Ontology(o:Nothing o:Thing
# o:Nothing comment
Annotation(o:Nothing o:Thing)
AnnotationAssertion(o:Nothing o:Thing o:Nothing)
SubAnnotationPropertyOf(o:Nothing o:Thing)
SubClassOf(Annotation(o:Thing "o:Nothing") <urn:é> o:Nothing)
DataPropertyAssertion(<urn:d> <urn:i> "escaped \"o:Nothing\"")
)"###;
        let expected=source.replace("<urn:é> o:Nothing)","<urn:é> <http://www.w3.org/2002/07/owl#Nothing>)");
        assert_eq!(canonicalize(source).unwrap(),expected);
    }
    #[test]
    fn partial_namespace_default_prefix_and_exact_token_matching() {
        let source="Prefix(:=<http://www.w3.org/2002/07/owl#Noth>) Prefix(x:=<http://www.w3.org/2002/07/owl#Th>) Ontology(SubClassOf(:ing x:ing) SubClassOf(:ingElse <urn:Nothing>))";
        assert_eq!(canonicalize(source).unwrap(),source.replace("(:ing x:ing)","(<http://www.w3.org/2002/07/owl#Nothing> <http://www.w3.org/2002/07/owl#Thing>)"));
    }
    #[test]
    fn literal_unicode_prefix_is_resolved_without_decoding_escape_like_names() {
        let source="Prefix(Ω:=<http://www.w3.org/2002/07/owl#>) Ontology(SubClassOf(<urn:A> Ω:Nothing))";
        assert_eq!(canonicalize(source).unwrap(), source.replace("Ω:Nothing", "<http://www.w3.org/2002/07/owl#Nothing>"));
        // Such escaped local tokens are not accepted by the source grammar;
        // this pure helper must never invent an unescape interpretation either.
        for source in [r"Prefix(o:=<http://www.w3.org/2002/07/owl#>) Ontology(SubClassOf(<urn:A> o:Th\u0069ng))", r"Prefix(o:=<http://www.w3.org/2002/07/owl#>) Ontology(SubClassOf(<urn:A> o:Noth%69ng))"] {
            assert!(matches!(canonicalize(source).unwrap(), Cow::Borrowed(_)));
        }
    }

    #[test]
    fn anonymous_ids_are_never_prefix_expanded() {
        let source="Prefix(_:=<http://www.w3.org/2002/07/owl#>) Ontology(ClassAssertion(<urn:A> _:Nothing) SameIndividual(_:Thing _:Nothing))";
        assert!(matches!(canonicalize(source).unwrap(), Cow::Borrowed(_)));
        let mixed="Prefix(_:=<http://www.w3.org/2002/07/owl#>) Prefix(o:=<http://www.w3.org/2002/07/owl#>) Ontology(ClassAssertion(o:Thing _:Nothing))";
        assert_eq!(canonicalize(mixed).unwrap(), mixed.replace("ClassAssertion(o:Thing", "ClassAssertion(<http://www.w3.org/2002/07/owl#Thing>"));
    }
    #[test]
    fn annotation_only_alias_borrows_and_invalid_binding_refuses() {
        let source=r###"Prefix(o:=<http://www.w3.org/2002/07/owl#>) Ontology(AnnotationAssertion(o:Nothing o:Thing "o:Nothing"))"###;
        assert!(matches!(canonicalize(&source).unwrap(),Cow::Borrowed(_)));
        assert!(canonicalize("Prefix(owl:=<urn:evil#>) Ontology()").is_err());
        assert!(canonicalize("Prefix(o:=<urn:a>) Prefix(o:=<urn:b>) Ontology()").is_err());
    }

    #[test]
    fn mixed_entity_spellings_are_unified() {
        let source = "Prefix(:=<urn:t#>)\nOntology(<urn:t>\nSubObjectPropertyOf(:r :s)\nSubClassOf(:A ObjectSomeValuesFrom(<urn:t#r> :B))\nAnnotationAssertion(:p :A \"x:y\")\n)";
        let out = canonicalize(source).unwrap();
        assert!(out.contains("SubObjectPropertyOf(<urn:t#r> :s)"), "{out}");
        assert!(out.contains("SubClassOf(:A ObjectSomeValuesFrom(<urn:t#r> :B))"), "{out}");
        assert!(out.contains("AnnotationAssertion(:p :A \"x:y\")"), "{out}");
        let two_prefixes = "Prefix(p:=<urn:t#>)\nPrefix(q:=<urn:t#>)\nOntology(SubClassOf(p:A p:C)\nSubClassOf(q:C q:D))";
        let out = canonicalize(two_prefixes).unwrap();
        assert!(out.contains("SubClassOf(p:A <urn:t#C>)"), "{out}");
        assert!(out.contains("SubClassOf(<urn:t#C> q:D)"), "{out}");
        let consistent = "Prefix(:=<urn:t#>)\nOntology(SubObjectPropertyOf(:r :s))";
        assert!(matches!(canonicalize(consistent).unwrap(), Cow::Borrowed(_)));
    }
}
