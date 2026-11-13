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

/// The four standard prefixes of FSS 2.4 (Table 2) and their namespaces.
/// IRIs in these namespaces are OWL vocabulary, not source entities.
const STANDARD: [(&str, &str); 4] = [
    ("owl", "http://www.w3.org/2002/07/owl#"),
    ("rdf", "http://www.w3.org/1999/02/22-rdf-syntax-ns#"),
    ("rdfs", "http://www.w3.org/2000/01/rdf-schema#"),
    ("xsd", "http://www.w3.org/2001/XMLSchema#"),
];

/// Give every entity one spelling, so that KM's IRI registry, which keys
/// entities by spelling, identifies exactly the IRIs that OWL identifies
/// (FSS 2.4: an abbreviated IRI `p:x` denotes the full IRI `ns(p) ++ x`,
/// using the document's `Prefix` declarations and the standard prefixes).
///
/// For each distinct abbreviated spelling `p:x` in a logical position (not
/// in annotations, not the ontology IRI) with expansion `e`:
///
/// * `e` in a standard namespace (vocabulary such as datatypes and facets):
///   respelled with the standard prefix, `xsd:integer` for `x:integer` with
///   `x:` bound to the XSD namespace. The standard spelling stays as it is.
///   (The six OWL semantic constants were already respelled in full by
///   [`canonicalize_builtins`].)
/// * any other `e`: respelled as the full IRI `<e>` when the document also
///   spells `e` another way (the full IRI, or a second prefix).
/// * in both cases, respelled as `<e>` when the document uses the text `p:x`
///   itself as a full IRI `<p:x>`: that is a different IRI, which the
///   registry (it strips the brackets) would otherwise merge with this one.
///
/// So an entity spelled one way keeps its spelling (and km prints it as
/// before); an entity spelled several ways is printed as its full IRI.
/// Literal datatypes (`"1"^^x:integer`) follow the same rules. Expansion is
/// computed once per distinct spelling. A document without a respelling is
/// returned borrowed, and one with neither a declared prefix nor a standard
/// prefix in its text is not walked at all.
fn canonicalize_entity_spellings(text: &str) -> Result<Cow<'_, str>, String> {
    use crate::fxhash::{FxHashMap, FxHashSet};
    let mut parser = Parser::new(text);
    let mut prefixes: BTreeMap<String, String> = STANDARD
        .iter()
        .map(|(name, ns)| ((*name).to_owned(), (*ns).to_owned()))
        .collect();
    let mut declared = false;
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
        // Blank node IDs remain anonymous even if a source declares `_:`.
        if prefix != "_" && !STANDARD.contains(&(prefix, iri)) {
            declared = true;
            prefixes.insert(prefix.to_owned(), iri.to_owned());
        }
    }
    if !declared && !STANDARD.iter().any(|(name, _)| text.contains(&format!("{name}:"))) {
        return Ok(Cow::Borrowed(text));
    }
    if parser.next_tok() != Some("Ontology") || parser.next_tok() != Some("(") {
        return Err("spelling canonicalization: missing Ontology(".into());
    }

    /// What one walk over the logical positions has seen.
    #[derive(Default)]
    struct Seen<'a> {
        /// Each distinct abbreviated spelling and the index of its expansion
        /// (`None`: undeclared prefix).
        spellings: FxHashMap<&'a str, Option<u32>>,
        /// Distinct expansions, with the number of spellings of each.
        iris: Vec<(String, u32)>,
        index: FxHashMap<String, u32>,
        /// The contents of the full IRIs `<..>`.
        full: FxHashSet<&'a str>,
    }

    /// An atom in a logical position: the part that names an IRI (a literal's
    /// `^^` suffix is dropped), or `None` for literals, language tags and
    /// anonymous individuals.
    fn iri_part(token: &str) -> Option<&str> {
        let body = token.strip_prefix("^^").unwrap_or(token);
        (!body.is_empty() && !body.starts_with(['"', '@']) && !body.starts_with("_:"))
            .then_some(body)
    }

    /// Visit the atoms of `node` in logical positions, in document order.
    fn atoms<'a>(node: &Node<'a>, f: &mut dyn FnMut(&'a str)) {
        match node {
            Node::List("Annotation" | "AnnotationAssertion" | "SubAnnotationPropertyOf"
                | "AnnotationPropertyDomain" | "AnnotationPropertyRange", _) => {}
            Node::List(_, args) => {
                for arg in args {
                    atoms(arg, f);
                }
            }
            Node::Atom(token) => f(token),
        }
    }

    let mut seen = Seen::default();
    while parser.peek() != Some(")") {
        if parser.peek().is_none() {
            return Err("spelling canonicalization: unterminated Ontology".into());
        }
        if let node @ Node::List(_, _) = parser.parse()? {
            atoms(&node, &mut |token| {
                let Some(body) = iri_part(token) else { return };
                if let Some(iri) = body.strip_prefix('<') {
                    seen.full.insert(iri.strip_suffix('>').unwrap_or(iri));
                    return;
                }
                if seen.spellings.contains_key(body) {
                    return;
                }
                let expansion = body.split_once(':').and_then(|(prefix, local)| {
                    prefixes.get(prefix).map(|ns| format!("{ns}{local}"))
                });
                let id = expansion.map(|iri| {
                    let next = seen.iris.len() as u32;
                    let id = *seen.index.entry(iri.clone()).or_insert(next);
                    if id == next {
                        seen.iris.push((iri, 0));
                    }
                    seen.iris[id as usize].1 += 1;
                    id
                });
                seen.spellings.insert(body, id);
            });
        }
    }

    let mut respell: FxHashMap<&str, String> = FxHashMap::default();
    for (&spelling, id) in &seen.spellings {
        let Some(id) = id else { continue };
        let (iri, count) = &seen.iris[*id as usize];
        if seen.full.contains(spelling) {
            // `<p:x>` is the IRI `p:x`, not the expansion of `p:x`.
            respell.insert(spelling, format!("<{iri}>"));
        } else if let Some((name, ns)) = STANDARD.iter().find(|(_, ns)| iri.starts_with(ns)) {
            let standard = format!("{name}:{}", &iri[ns.len()..]);
            if spelling != standard {
                respell.insert(spelling, standard);
            }
        } else if *count > 1 || seen.full.contains(iri.as_str()) {
            respell.insert(spelling, format!("<{iri}>"));
        }
    }
    if respell.is_empty() {
        return Ok(Cow::Borrowed(text));
    }

    // Second walk: copy the text, replacing each respelled atom.
    let mut parser = Parser::new(text);
    while parser.peek() == Some("Prefix") {
        parser.parse()?;
    }
    parser.next_tok();
    parser.next_tok();
    let mut out = String::with_capacity(text.len() + respell.len() * 32);
    let mut copied = 0;
    let mut failure: Option<String> = None;
    while parser.peek() != Some(")") && parser.peek().is_some() {
        if let node @ Node::List(_, _) = parser.parse()? {
            atoms(&node, &mut |token| {
                let Some(body) = iri_part(token) else { return };
                let Some(replacement) = respell.get(body) else { return };
                let Some(start) = (body.as_ptr() as usize).checked_sub(text.as_ptr() as usize)
                else {
                    failure.get_or_insert("spelling canonicalization: foreign token".into());
                    return;
                };
                let end = start + body.len();
                if start < copied || text.get(start..end) != Some(body) {
                    failure.get_or_insert("spelling canonicalization: invalid token range".into());
                    return;
                }
                out.push_str(&text[copied..start]);
                out.push_str(replacement);
                copied = end;
            });
        }
    }
    if let Some(failure) = failure {
        return Err(failure);
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
        for source in ["Ontology(SubClassOf(owl:Thing owl:Nothing))", "Ontology(SubClassOf(<http://www.w3.org/2002/07/owl#Thing> <http://www.w3.org/2002/07/owl#Nothing>))", "Prefix(o:=<urn:unrelated#>) Ontology(SubClassOf(o:Thing o:Nothing))"] {
            let result=canonicalize(source).unwrap();assert!(matches!(result,Cow::Borrowed(_)));assert_eq!(result.as_ptr(),source.as_ptr());
        }
        // `o:NothingElse` is no builtin, but it is the OWL-namespace IRI
        // `owl:NothingElse`, so it takes the standard spelling.
        let source = "Prefix(o:=<http://www.w3.org/2002/07/owl#>) Ontology(SubClassOf(o:NothingElse <urn:A>))";
        assert_eq!(canonicalize(source).unwrap(), source.replace("(o:NothingElse", "(owl:NothingElse"));
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
        assert_eq!(canonicalize(source).unwrap(),source.replace("(:ing x:ing)","(<http://www.w3.org/2002/07/owl#Nothing> <http://www.w3.org/2002/07/owl#Thing>)")
            .replace("(:ingElse", "(owl:NothingElse"));
    }
    #[test]
    fn literal_unicode_prefix_is_resolved_without_decoding_escape_like_names() {
        let source="Prefix(Ω:=<http://www.w3.org/2002/07/owl#>) Ontology(SubClassOf(<urn:A> Ω:Nothing))";
        assert_eq!(canonicalize(source).unwrap(), source.replace("Ω:Nothing", "<http://www.w3.org/2002/07/owl#Nothing>"));
        // Such escaped local tokens are not accepted by the source grammar;
        // this pure helper must never invent an unescape interpretation either.
        for source in [r"Prefix(o:=<http://www.w3.org/2002/07/owl#>) Ontology(SubClassOf(<urn:A> o:Th\u0069ng))", r"Prefix(o:=<http://www.w3.org/2002/07/owl#>) Ontology(SubClassOf(<urn:A> o:Noth%69ng))"] {
            // The OWL-namespace IRI keeps its local text verbatim.
            let out = canonicalize(source).unwrap();
            assert_eq!(out, source.replace("> o:", "> owl:"));
            assert!(!out.contains("owl#Thing") && !out.contains("owl#Nothing"), "{out}");
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
