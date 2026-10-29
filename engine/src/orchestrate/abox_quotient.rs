//! Fail-closed ABox quotient for large ABoxes over a nominal-free TBox.
//!
//! The classification of a *consistent* ontology `K = T ∪ A` whose TBox `T`
//! is closed under disjoint unions (nominal-free, no universal role, no keys,
//! no rules) equals the classification of `T` alone
//! (`NativeABox.entailsSubWith_iff_entailsSub_of_modelAmalgamation` in
//! `lean/ContextCalculus/HypertableauDisjointUnionABoxProjection.lean`).
//! What remains is a complete *consistency* decision for `K`. This module
//! builds a much smaller ABox `Q` such that
//!
//! ```text
//!     T ∪ Q consistent  ==>  T ∪ A consistent                          (1)
//! ```
//!
//! and hands `T ∪ Q` to the ordinary certified pipeline. If that pipeline
//! certifies `T ∪ Q` consistent, then `K` is consistent by (1), and the
//! taxonomy of `T ∪ Q` equals the taxonomy of `T`, which equals the taxonomy
//! of `K` (the theorem above applied to `Q` and to `A`). If `T ∪ Q` is
//! inconsistent, or the pipeline declines, nothing is published and the
//! unchanged ontology is classified as before: a quotient clash means
//! "defer", never "inconsistent".
//!
//! `Q` is obtained from `A` by three transformations, each satisfying (1):
//!
//! * **Component canonicalisation (S2).** Two connected components of the
//!   ABox graph that are equal up to a bijective renaming of individuals and a
//!   bijective renaming of `xsd:string` values that fixes every literal of the
//!   TBox (and is the identity on all other literals) are equi-consistent with
//!   `T`: a global data-value permutation that preserves every data range of
//!   `T` maps models of `T` to models of `T`. Since `T` is closed under
//!   disjoint unions, `T ∪ A` is consistent iff `T ∪ C` is consistent for every
//!   component `C`; one representative per isomorphism class suffices.
//!   String renaming is admitted only when no data range of the ontology can
//!   distinguish two string values outside the literal set of the ontology
//!   (no facet restriction, datatype definition, or string-derived datatype).
//! * **Homomorphic merging (S1).** OWL has no unique-name assumption. For any
//!   map `h` on individuals (fixing every individual that occurs outside the
//!   ABox), a model `I` of `T ∪ h(A)` yields a model of `T ∪ A` by
//!   interpreting `a` as `h(a)^I`. Individuals are merged by a key (asserted
//!   classes, values of count-restricted data properties, identity-assertion
//!   participation) refined along count-restricted object roles. The key only
//!   influences how often the merged ABox stays consistent, never soundness.
//! * **Data-value thinning.** Let `p` be a data property such that neither `p`
//!   nor any super-property is functional, used in a data max/exact
//!   cardinality, or disjoint with another data property. Adding a `p`-edge
//!   from an element to a value that no data range of the ontology can
//!   distinguish from a value the element already has for `p` preserves every
//!   axiom of `T`. A model of the thinned ABox (one renamable value per node
//!   and such property) therefore extends to a model of the complete ABox.
//!
//! Every input feature outside the admitted syntax declines: imports, rules,
//! keys, the universal object/data role, negative property assertions,
//! nominals (`ObjectOneOf`, `ObjectHasValue`) anywhere, comments, and any
//! malformed or unexpected token.

use std::collections::hash_map::DefaultHasher;
use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};
use std::io::{Read, Seek, SeekFrom};
use std::path::Path;

use super::tmpfile::TempPath;
use super::OrchestrateError;

/// Smallest source considered. Smaller ABoxes are already handled by the
/// established exact routes; the quotient is a large-ABox scaling device.
const MIN_SOURCE_BYTES: u64 = 4_000_000;
/// Minimum number of ABox assertions before the quotient is attempted.
const MIN_ABOX_ASSERTIONS: usize = 10_000;
/// Required reduction of the assertion count. The quotient attempt is a
/// complete classification of a smaller ontology and, when it is a source
/// subset, a certified inconsistency is accepted outright (see
/// `Quotient::subset_of_source`). A 2x reduction already pays for it: on the
/// frozen corpus every input with a 2x-8x reduction was faster through the
/// quotient (ORE 4410 117 -> 32 s, 10391 38 -> 1.1 s, 13526 43 -> 1.0 s,
/// 5544 4.1 -> 0.6 s) or failed both ways.
const MIN_REDUCTION: usize = 2;
/// Largest component that is canonicalised in S2.
const MAX_CANONICAL_COMPONENT: usize = 64;
const SAMPLE_BYTES: usize = 256 * 1024;
const XSD: &str = "http://www.w3.org/2001/XMLSchema#";
const XSD_STRING: &str = "<http://www.w3.org/2001/XMLSchema#string>";
const CANON_PREFIX: &str = "urn:km:abox-quotient:";
const OWL_THING: &str = "http://www.w3.org/2002/07/owl#Thing";
const OWL_NOTHING: &str = "http://www.w3.org/2002/07/owl#Nothing";

/// Built quotient source plus provenance for diagnostics.
pub(super) struct Quotient {
    pub(super) path: TempPath,
    /// The ontology without its ABox. Present exactly when the TBox contains
    /// nominals; the taxonomy may then be published only if the TBox
    /// taxonomy equals the quotient taxonomy (sandwich argument).
    pub(super) tbox: Option<TempPath>,
    /// Atomic mode: `path` holds the TBox without any individual. The source
    /// is consistent iff none of these (full-IRI) classes is unsatisfiable.
    pub(super) atomic_classes: Option<Vec<String>>,
    /// Every quotient assertion is literally an assertion of the source ABox
    /// (same individuals, classes, roles and values). Then the quotient
    /// ontology is a subset of the source, so a certified inconsistency of
    /// the quotient is an inconsistency of the source (monotonicity).
    pub(super) subset_of_source: bool,
    pub(super) individuals: usize,
    pub(super) blocks: usize,
    pub(super) assertions: usize,
    pub(super) quotient_assertions: usize,
}

// ---------------------------------------------------------------------------
// Lexical layer: a strict subset of OWL 2 functional syntax.
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Tok<'a> {
    Open,
    Close,
    /// `<...>` including the brackets.
    Iri(&'a str),
    /// Prefixed name, keyword, number, or blank node.
    Word(&'a str),
    /// Complete literal: quoted lexical form plus optional `^^dt` / `@lang`.
    Lit(&'a str),
}

struct Lexer<'a> {
    text: &'a str,
    pos: usize,
}

impl<'a> Lexer<'a> {
    fn new(text: &'a str) -> Self {
        Lexer { text, pos: 0 }
    }

    /// Next token and its start offset. `Err(())` marks unsupported syntax.
    fn next(&mut self) -> Result<Option<(usize, Tok<'a>)>, ()> {
        let bytes = self.text.as_bytes();
        while self.pos < bytes.len() && bytes[self.pos].is_ascii_whitespace() {
            self.pos += 1;
        }
        if self.pos >= bytes.len() {
            return Ok(None);
        }
        let start = self.pos;
        let tok = match bytes[start] {
            b'(' => {
                self.pos += 1;
                Tok::Open
            }
            b')' => {
                self.pos += 1;
                Tok::Close
            }
            b'#' => return Err(()),
            b'<' => {
                let end = memchr(b'>', &bytes[start..]).ok_or(())?;
                let iri = &self.text[start..start + end + 1];
                if iri[1..iri.len() - 1]
                    .bytes()
                    .any(|b| b.is_ascii_whitespace() || b == b'<' || b == b'"')
                {
                    return Err(());
                }
                self.pos = start + end + 1;
                Tok::Iri(iri)
            }
            b'"' => {
                let mut i = start + 1;
                loop {
                    match bytes.get(i) {
                        None => return Err(()),
                        Some(b'\\') => i += 2,
                        Some(b'"') => break,
                        Some(_) => i += 1,
                    }
                }
                i += 1;
                if bytes.get(i) == Some(&b'^') {
                    if bytes.get(i + 1) != Some(&b'^') {
                        return Err(());
                    }
                    i += 2;
                    if bytes.get(i) == Some(&b'<') {
                        let end = memchr(b'>', &bytes[i..]).ok_or(())?;
                        i += end + 1;
                    } else {
                        let len = word_len(&bytes[i..]);
                        if len == 0 {
                            return Err(());
                        }
                        i += len;
                    }
                } else if bytes.get(i) == Some(&b'@') {
                    i += 1;
                    let len = bytes[i..]
                        .iter()
                        .take_while(|b| b.is_ascii_alphanumeric() || **b == b'-')
                        .count();
                    if len == 0 {
                        return Err(());
                    }
                    i += len;
                }
                self.pos = i;
                Tok::Lit(&self.text[start..i])
            }
            _ => {
                let len = word_len(&bytes[start..]);
                if len == 0 {
                    return Err(());
                }
                self.pos = start + len;
                Tok::Word(&self.text[start..start + len])
            }
        };
        Ok(Some((start, tok)))
    }
}

fn memchr(needle: u8, haystack: &[u8]) -> Option<usize> {
    haystack.iter().position(|&b| b == needle)
}

fn word_len(bytes: &[u8]) -> usize {
    bytes
        .iter()
        .take_while(|&&b| {
            !(b.is_ascii_whitespace() || b == b'(' || b == b')' || b == b'"' || b == b'<' || b == b'#')
        })
        .count()
}

/// Split a literal into (quoted lexical form without quotes, suffix).
fn split_literal(lit: &str) -> Option<(&str, &str)> {
    let bytes = lit.as_bytes();
    let mut i = 1;
    while i < bytes.len() {
        match bytes[i] {
            b'\\' => i += 2,
            b'"' => return Some((&lit[1..i], &lit[i + 1..])),
            _ => i += 1,
        }
    }
    None
}

/// One top-level item inside `Ontology( ... )`.
struct Item<'a> {
    keyword: &'a str,
    start: usize,
    end: usize,
    /// Tokens strictly inside the item's outer parentheses.
    tokens: Vec<Tok<'a>>,
}

struct Document<'a> {
    prefixes: HashMap<&'a str, &'a str>,
    items: Vec<Item<'a>>,
    /// Offset of the closing parenthesis of `Ontology(`.
    close: usize,
}

fn parse_document(text: &str) -> Result<Document<'_>, ()> {
    let mut lexer = Lexer::new(text);
    let mut prefixes = HashMap::new();
    // Header: Prefix(name:=<iri>)* Ontology(
    loop {
        let (_, tok) = lexer.next()?.ok_or(())?;
        match tok {
            Tok::Word("Prefix") => {
                if lexer.next()?.map(|t| t.1) != Some(Tok::Open) {
                    return Err(());
                }
                let (_, name) = lexer.next()?.ok_or(())?;
                let Tok::Word(name) = name else { return Err(()) };
                let name = name.strip_suffix(":=").ok_or(())?;
                let (_, iri) = lexer.next()?.ok_or(())?;
                let Tok::Iri(iri) = iri else { return Err(()) };
                if lexer.next()?.map(|t| t.1) != Some(Tok::Close) {
                    return Err(());
                }
                prefixes.insert(name, &iri[1..iri.len() - 1]);
            }
            Tok::Word("Ontology") => {
                if lexer.next()?.map(|t| t.1) != Some(Tok::Open) {
                    return Err(());
                }
                break;
            }
            _ => return Err(()),
        }
    }
    // Reserved prefixes of OWL 2 functional syntax.
    for (name, iri) in [
        ("owl", "http://www.w3.org/2002/07/owl#"),
        ("rdf", "http://www.w3.org/1999/02/22-rdf-syntax-ns#"),
        ("rdfs", "http://www.w3.org/2000/01/rdf-schema#"),
        ("xsd", "http://www.w3.org/2001/XMLSchema#"),
        ("xml", "http://www.w3.org/XML/1998/namespace"),
    ] {
        prefixes.entry(name).or_insert(iri);
    }
    let mut items = Vec::new();
    let close;
    loop {
        let (start, tok) = lexer.next()?.ok_or(())?;
        match tok {
            Tok::Close => {
                close = start;
                break;
            }
            // Ontology IRI and version IRI.
            Tok::Iri(_) => continue,
            Tok::Word(keyword) => {
                if lexer.next()?.map(|t| t.1) != Some(Tok::Open) {
                    return Err(());
                }
                let mut depth = 1usize;
                let mut tokens = Vec::new();
                let end;
                loop {
                    let (offset, tok) = lexer.next()?.ok_or(())?;
                    match tok {
                        Tok::Open => depth += 1,
                        Tok::Close => {
                            depth -= 1;
                            if depth == 0 {
                                end = offset + 1;
                                break;
                            }
                        }
                        _ => {}
                    }
                    tokens.push(tok);
                }
                items.push(Item { keyword, start, end, tokens });
            }
            _ => return Err(()),
        }
    }
    if lexer.next()?.is_some() {
        return Err(());
    }
    Ok(Document { prefixes, items, close })
}

/// Split the argument tokens of an item (or nested expression) into
/// top-level arguments.
fn split_args<'t, 'a>(tokens: &'t [Tok<'a>]) -> Result<Vec<&'t [Tok<'a>]>, ()> {
    let mut args = Vec::new();
    let mut i = 0;
    while i < tokens.len() {
        let start = i;
        match tokens[i] {
            Tok::Word(_) if tokens.get(i + 1) == Some(&Tok::Open) => {
                let mut depth = 0usize;
                i += 1;
                loop {
                    match tokens.get(i).ok_or(())? {
                        Tok::Open => depth += 1,
                        Tok::Close => {
                            depth -= 1;
                            if depth == 0 {
                                break;
                            }
                        }
                        _ => {}
                    }
                    i += 1;
                }
                i += 1;
            }
            Tok::Open | Tok::Close => return Err(()),
            _ => i += 1,
        }
        args.push(&tokens[start..i]);
    }
    Ok(args)
}

fn is_annotation(arg: &[Tok<'_>]) -> bool {
    matches!(arg.first(), Some(Tok::Word("Annotation")))
}

struct Expander<'a> {
    prefixes: HashMap<&'a str, &'a str>,
}

impl<'a> Expander<'a> {
    /// Full IRI (with brackets) for an IRI or prefixed-name entity token.
    fn entity(&self, tok: &Tok<'a>) -> Result<String, ()> {
        match *tok {
            Tok::Iri(iri) => Ok(iri.to_string()),
            Tok::Word(word) => {
                if word.starts_with("_:") {
                    return Ok(word.to_string());
                }
                let colon = word.find(':').ok_or(())?;
                let base = self.prefixes.get(&word[..colon]).ok_or(())?;
                Ok(format!("<{}{}>", base, &word[colon + 1..]))
            }
            _ => Err(()),
        }
    }

    /// Canonical literal text: prefixed datatypes expanded, plain literals
    /// without a language tag written as `xsd:string` literals (same value).
    fn literal(&self, lit: &str) -> Result<String, ()> {
        let (lexical, suffix) = split_literal(lit).ok_or(())?;
        if suffix.is_empty() {
            return Ok(format!("\"{lexical}\"^^{XSD_STRING}"));
        }
        if suffix.starts_with('@') {
            return Ok(lit.to_string());
        }
        let datatype = suffix.strip_prefix("^^").ok_or(())?;
        let datatype = if datatype.starts_with('<') {
            datatype.to_string()
        } else {
            self.entity(&Tok::Word(datatype))?
        };
        Ok(format!("\"{lexical}\"^^{datatype}"))
    }

    /// Canonical single-space serialization of an expression with all
    /// prefixed names expanded.
    fn expression(&self, tokens: &[Tok<'a>]) -> Result<String, ()> {
        let mut out = String::new();
        let mut previous_open = true;
        for (index, tok) in tokens.iter().enumerate() {
            match tok {
                Tok::Open => {
                    out.push('(');
                    previous_open = true;
                    continue;
                }
                Tok::Close => {
                    out.push(')');
                    previous_open = false;
                    continue;
                }
                _ => {}
            }
            if !previous_open {
                out.push(' ');
            }
            previous_open = false;
            match tok {
                Tok::Iri(iri) => out.push_str(iri),
                Tok::Lit(lit) => out.push_str(&self.literal(lit)?),
                Tok::Word(word) => {
                    let keyword = tokens.get(index + 1) == Some(&Tok::Open)
                        || word.bytes().all(|b| b.is_ascii_digit());
                    if keyword {
                        out.push_str(word);
                    } else {
                        out.push_str(&self.entity(tok)?);
                    }
                }
                Tok::Open | Tok::Close => unreachable!(),
            }
        }
        Ok(out)
    }
}

// ---------------------------------------------------------------------------
// Semantic screen of the non-ABox part.
// ---------------------------------------------------------------------------

const DECLINED_KEYWORDS: &[&str] = &[
    "ObjectOneOf",
    "ObjectHasValue",
    "HasKey",
    "DLSafeRule",
    "Import",
    "NegativeObjectPropertyAssertion",
    "NegativeDataPropertyAssertion",
];
const UNIVERSAL_ROLES: &[&str] = &[
    "<http://www.w3.org/2002/07/owl#topObjectProperty>",
    "<http://www.w3.org/2002/07/owl#topDataProperty>",
];
/// Datatypes whose membership of an `xsd:string` value depends on the value.
const STRING_DERIVED: &[&str] = &[
    "normalizedString",
    "token",
    "language",
    "Name",
    "NCName",
    "NMTOKEN",
    "NMTOKENS",
    "ID",
    "IDREF",
    "IDREFS",
    "ENTITY",
    "ENTITIES",
];
const IGNORED_ITEMS: &[&str] = &[
    "Declaration",
    "Annotation",
    "AnnotationAssertion",
    "SubAnnotationPropertyOf",
    "AnnotationPropertyDomain",
    "AnnotationPropertyRange",
];

#[derive(Default)]
struct Screen {
    /// Data properties with a direct count restriction.
    counted_data: HashSet<String>,
    /// Object roles with a direct count restriction (merge effectiveness only).
    counted_roles: HashSet<String>,
    /// (sub, super) data-property edges.
    data_edges: Vec<(String, String)>,
    /// (sub, super) object-property edges, inverse pairs in both directions.
    role_edges: Vec<(String, String)>,
    /// Lexical forms of literals outside data-property assertions.
    literals: HashSet<String>,
    /// A data range may distinguish string values.
    string_sensitive: bool,
    /// Individuals occurring in TBox nominals (`ObjectOneOf`, `ObjectHasValue`).
    nominal_individuals: HashSet<String>,
}

impl Screen {
    /// Inspect one non-ABox item, or a class expression of an ABox item.
    fn observe(
        &mut self,
        expander: &Expander<'_>,
        keyword: &str,
        tokens: &[Tok<'_>],
        allow_nominals: bool,
    ) -> Result<(), ()> {
        if DECLINED_KEYWORDS.contains(&keyword) {
            return Err(());
        }
        if keyword == "DatatypeDefinition" {
            self.string_sensitive = true;
        }
        let args = split_args(tokens)?;
        let args: Vec<_> = args.into_iter().filter(|arg| !is_annotation(arg)).collect();
        let entities = |args: &[&[Tok<'_>]]| -> Result<Vec<String>, ()> {
            args.iter()
                .map(|arg| if arg.len() == 1 { expander.entity(&arg[0]) } else { Err(()) })
                .collect()
        };
        match keyword {
            "FunctionalDataProperty" | "DisjointDataProperties" => {
                self.counted_data.extend(entities(&args)?);
            }
            "FunctionalObjectProperty" | "InverseFunctionalObjectProperty" => {
                if let [arg] = args.as_slice() {
                    self.counted_roles.insert(role_name(expander, arg)?);
                }
            }
            "SubDataPropertyOf" => {
                let names = entities(&args)?;
                if names.len() != 2 {
                    return Err(());
                }
                self.data_edges.push((names[0].clone(), names[1].clone()));
            }
            "EquivalentDataProperties" => {
                let names = entities(&args)?;
                for left in &names {
                    for right in &names {
                        self.data_edges.push((left.clone(), right.clone()));
                    }
                }
            }
            "SubObjectPropertyOf" | "EquivalentObjectProperties" | "InverseObjectProperties" => {
                let names: Vec<String> = args
                    .iter()
                    .filter(|arg| !matches!(arg.first(), Some(Tok::Word("ObjectPropertyChain"))))
                    .map(|arg| role_name(expander, arg))
                    .collect::<Result<_, _>>()?;
                for left in &names {
                    for right in &names {
                        self.role_edges.push((left.clone(), right.clone()));
                    }
                }
            }
            _ => {}
        }
        // Nested constructors anywhere in the item.
        for (index, tok) in tokens.iter().enumerate() {
            match *tok {
                Tok::Word(word) if tokens.get(index + 1) == Some(&Tok::Open) => {
                    if allow_nominals && matches!(word, "ObjectOneOf" | "ObjectHasValue") {
                        // TBox nominal: record its individuals; the caller
                        // pins them and requires the TBox sandwich check.
                        let mut depth = 0usize;
                        let mut end = index + 1;
                        loop {
                            match tokens.get(end).ok_or(())? {
                                Tok::Open => depth += 1,
                                Tok::Close => {
                                    depth -= 1;
                                    if depth == 0 {
                                        break;
                                    }
                                }
                                _ => {}
                            }
                            end += 1;
                        }
                        let inner = split_args(&tokens[index + 2..end])?;
                        let members: &[&[Tok<'_>]] = if word == "ObjectHasValue" {
                            if inner.len() != 2 {
                                return Err(());
                            }
                            &inner[1..]
                        } else {
                            &inner
                        };
                        for member in members {
                            self.nominal_individuals.insert(individual(expander, member)?);
                        }
                        continue;
                    }
                    if DECLINED_KEYWORDS.contains(&word) {
                        return Err(());
                    }
                    match word {
                        "DatatypeRestriction" | "DatatypeDefinition" => self.string_sensitive = true,
                        "DataMaxCardinality" | "DataExactCardinality" => {
                            if let Some(tok) = tokens.get(index + 3) {
                                self.counted_data.insert(expander.entity(tok)?);
                            }
                        }
                        "ObjectMaxCardinality" | "ObjectExactCardinality" => {
                            let role = match tokens.get(index + 3) {
                                Some(Tok::Word("ObjectInverseOf")) => tokens.get(index + 5),
                                other => other,
                            };
                            if let Some(tok) = role {
                                self.counted_roles.insert(expander.entity(tok)?);
                            }
                        }
                        _ => {}
                    }
                }
                Tok::Word(_) | Tok::Iri(_) => {
                    if tokens.get(index + 1) == Some(&Tok::Open) {
                        continue;
                    }
                    if let Tok::Word(word) = tok {
                        if word.bytes().all(|b| b.is_ascii_digit()) {
                            continue;
                        }
                    }
                    let name = expander.entity(tok)?;
                    if UNIVERSAL_ROLES.contains(&name.as_str()) {
                        return Err(());
                    }
                    if let Some(local) = name
                        .strip_prefix('<')
                        .and_then(|name| name.strip_prefix(XSD))
                        .and_then(|name| name.strip_suffix('>'))
                    {
                        if STRING_DERIVED.contains(&local) {
                            self.string_sensitive = true;
                        }
                    }
                }
                Tok::Lit(lit) => {
                    let (lexical, suffix) = split_literal(lit).ok_or(())?;
                    if let Some(datatype) = suffix.strip_prefix("^^") {
                        let name = if datatype.starts_with('<') {
                            datatype.to_string()
                        } else {
                            expander.entity(&Tok::Word(datatype))?
                        };
                        if let Some(local) = name
                            .strip_prefix('<')
                            .and_then(|name| name.strip_prefix(XSD))
                            .and_then(|name| name.strip_suffix('>'))
                        {
                            if STRING_DERIVED.contains(&local) {
                                self.string_sensitive = true;
                            }
                        }
                    }
                    self.literals.insert(lexical.to_string());
                }
                _ => {}
            }
        }
        Ok(())
    }

    /// Data properties whose own or inherited count restriction makes their
    /// values non-thinnable.
    fn restricted_data(&self) -> HashSet<String> {
        downward_closure(&self.counted_data, &self.data_edges)
    }

    fn restricted_roles(&self) -> HashSet<String> {
        downward_closure(&self.counted_roles, &self.role_edges)
    }
}

fn role_name(expander: &Expander<'_>, arg: &[Tok<'_>]) -> Result<String, ()> {
    match arg {
        [tok] => expander.entity(tok),
        [Tok::Word("ObjectInverseOf"), Tok::Open, tok, Tok::Close] => expander.entity(tok),
        _ => Err(()),
    }
}

fn downward_closure(seeds: &HashSet<String>, edges: &[(String, String)]) -> HashSet<String> {
    let mut subs: HashMap<&str, Vec<&str>> = HashMap::new();
    for (sub, sup) in edges {
        subs.entry(sup.as_str()).or_default().push(sub.as_str());
    }
    let mut closed: HashSet<String> = seeds.clone();
    let mut stack: Vec<&str> = seeds.iter().map(String::as_str).collect();
    while let Some(name) = stack.pop() {
        if let Some(children) = subs.get(name) {
            for child in children {
                if closed.insert((*child).to_string()) {
                    stack.push(child);
                }
            }
        }
    }
    closed
}

// ---------------------------------------------------------------------------
// ABox model.
// ---------------------------------------------------------------------------

#[derive(Default)]
struct Interner {
    ids: HashMap<String, u32>,
    names: Vec<String>,
}

impl Interner {
    fn id(&mut self, name: String) -> u32 {
        if let Some(&id) = self.ids.get(&name) {
            return id;
        }
        let id = self.names.len() as u32;
        self.ids.insert(name.clone(), id);
        self.names.push(name);
        id
    }
}

/// A data value in the (possibly renamed) ABox.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Value {
    /// Literal text, interned canonical form.
    Exact(u32),
    /// Canonical fresh `xsd:string` value number `n` (S2 renaming).
    Canon(u32),
}

#[derive(Default)]
struct Abox {
    individuals: Interner,
    classes: Interner,
    roles: Interner,
    properties: Interner,
    literals: Interner,
    /// Per interned literal: renamable `xsd:string` value.
    renamable: Vec<bool>,
    class_assertions: Vec<(u32, u32)>,
    role_assertions: Vec<(u32, u32, u32)>,
    data_assertions: Vec<(u32, u32, Value)>,
    /// (is SameIndividual, members).
    identities: Vec<(bool, Vec<u32>)>,
}

impl Abox {
    fn assertion_count(&self) -> usize {
        self.class_assertions.len()
            + self.role_assertions.len()
            + self.data_assertions.len()
            + self.identities.len()
    }

    fn is_renamable(&self, value: Value) -> bool {
        match value {
            Value::Exact(id) => self.renamable[id as usize],
            Value::Canon(_) => true,
        }
    }
}

fn individual(expander: &Expander<'_>, arg: &[Tok<'_>]) -> Result<String, ()> {
    match arg {
        [tok @ (Tok::Iri(_) | Tok::Word(_))] => expander.entity(tok),
        _ => Err(()),
    }
}

fn read_abox_item(
    abox: &mut Abox,
    screen: &mut Screen,
    expander: &Expander<'_>,
    item: &Item<'_>,
    pending_literals: &mut Vec<(String, String)>,
) -> Result<(), ()> {
    let args: Vec<_> = split_args(&item.tokens)?
        .into_iter()
        .filter(|arg| !is_annotation(arg))
        .collect();
    match item.keyword {
        "ClassAssertion" => {
            let [class, ind] = args.as_slice() else { return Err(()) };
            // A class expression is part of the semantic screen: nominals
            // decline, literals fix the string renaming, counts restrict.
            screen.observe(expander, "", class, false)?;
            let class = abox.classes.id(expander.expression(class)?);
            let ind = abox.individuals.id(individual(expander, ind)?);
            abox.class_assertions.push((ind, class));
        }
        "ObjectPropertyAssertion" => {
            let [role, subject, object] = args.as_slice() else { return Err(()) };
            let subject = abox.individuals.id(individual(expander, subject)?);
            let object = abox.individuals.id(individual(expander, object)?);
            let (role, subject, object) = match role {
                [tok] => (expander.entity(tok)?, subject, object),
                [Tok::Word("ObjectInverseOf"), Tok::Open, tok, Tok::Close] => {
                    (expander.entity(tok)?, object, subject)
                }
                _ => return Err(()),
            };
            if UNIVERSAL_ROLES.contains(&role.as_str()) {
                return Err(());
            }
            let role = abox.roles.id(role);
            abox.role_assertions.push((role, subject, object));
        }
        "DataPropertyAssertion" => {
            let [property, ind, literal] = args.as_slice() else { return Err(()) };
            let property = match property {
                [tok] => expander.entity(tok)?,
                _ => return Err(()),
            };
            if UNIVERSAL_ROLES.contains(&property.as_str()) {
                return Err(());
            }
            let [Tok::Lit(literal)] = literal else { return Err(()) };
            let canonical = expander.literal(literal)?;
            let (lexical, _) = split_literal(&canonical).ok_or(())?;
            let lexical = lexical.to_string();
            let property = abox.properties.id(property);
            let ind = abox.individuals.id(individual(expander, ind)?);
            let literal_id = abox.literals.id(canonical.clone());
            if literal_id as usize == abox.renamable.len() {
                abox.renamable.push(false);
                pending_literals.push((canonical, lexical));
            }
            abox.data_assertions.push((property, ind, Value::Exact(literal_id)));
        }
        "SameIndividual" | "DifferentIndividuals" => {
            if args.len() < 2 {
                return Err(());
            }
            let members = args
                .iter()
                .map(|arg| individual(expander, arg).map(|name| abox.individuals.id(name)))
                .collect::<Result<Vec<_>, _>>()?;
            abox.identities.push((item.keyword == "SameIndividual", members));
        }
        _ => return Err(()),
    }
    Ok(())
}

fn is_abox_keyword(keyword: &str) -> bool {
    matches!(
        keyword,
        "ClassAssertion"
            | "ObjectPropertyAssertion"
            | "DataPropertyAssertion"
            | "SameIndividual"
            | "DifferentIndividuals"
    )
}

// ---------------------------------------------------------------------------
// S2: component canonicalisation.
// ---------------------------------------------------------------------------

struct UnionFind(Vec<u32>);

impl UnionFind {
    fn new(n: usize) -> Self {
        UnionFind((0..n as u32).collect())
    }
    fn find(&mut self, mut x: u32) -> u32 {
        while self.0[x as usize] != x {
            let parent = self.0[self.0[x as usize] as usize];
            self.0[x as usize] = parent;
            x = parent;
        }
        x
    }
    fn union(&mut self, a: u32, b: u32) {
        let (a, b) = (self.find(a), self.find(b));
        if a != b {
            self.0[a.max(b) as usize] = a.min(b);
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum FormItem {
    Class(u32, u32),
    Role(u32, u32, u32),
    Data(u32, u32, Value),
    Identity(bool, Vec<u32>),
}

fn hash64<T: Hash>(value: &T) -> u64 {
    let mut hasher = DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

/// Replace every small component by the representative of its canonical
/// form. Returns the reduced ABox (same interners, new assertion lists).
fn canonicalize_components(abox: &mut Abox) {
    let n = abox.individuals.names.len();
    let mut uf = UnionFind::new(n);
    for &(_, a, b) in &abox.role_assertions {
        uf.union(a, b);
    }
    for (_, members) in &abox.identities {
        for &m in &members[1..] {
            uf.union(members[0], m);
        }
    }
    let mut component: Vec<u32> = (0..n as u32).map(|x| uf.find(x)).collect();
    let mut members: HashMap<u32, Vec<u32>> = HashMap::new();
    for x in 0..n as u32 {
        members.entry(component[x as usize]).or_default().push(x);
    }
    // Per-individual adjacency.
    let mut classes: Vec<Vec<u32>> = vec![Vec::new(); n];
    for &(ind, class) in &abox.class_assertions {
        classes[ind as usize].push(class);
    }
    let mut data: Vec<Vec<(u32, Value)>> = vec![Vec::new(); n];
    for &(p, ind, v) in &abox.data_assertions {
        data[ind as usize].push((p, v));
    }
    let mut edges: Vec<Vec<(u32, bool, u32)>> = vec![Vec::new(); n];
    for &(r, a, b) in &abox.role_assertions {
        edges[a as usize].push((r, true, b));
        edges[b as usize].push((r, false, a));
    }
    let mut identities: HashMap<u32, Vec<usize>> = HashMap::new();
    for (index, (_, m)) in abox.identities.iter().enumerate() {
        identities.entry(component[m[0] as usize]).or_default().push(index);
    }
    let renamable = abox.renamable.clone();
    let value_shape = |v: Value| -> Option<Value> {
        match v {
            Value::Exact(id) if renamable[id as usize] => None,
            other => Some(other),
        }
    };

    let mut seen_forms: HashSet<Vec<FormItem>> = HashSet::new();
    let mut keep = vec![true; n];
    let mut renamed: HashMap<(u32, u32, Value), Value> = HashMap::new();
    let mut roots: Vec<u32> = members.keys().copied().collect();
    roots.sort_unstable();
    for root in roots {
        let comp = &members[&root];
        if comp.len() > MAX_CANONICAL_COMPONENT {
            continue;
        }
        // Weisfeiler-Leman colours give an isomorphism-invariant order up to
        // ties; ties only reduce sharing, never soundness.
        let mut colour: HashMap<u32, u64> = comp
            .iter()
            .map(|&x| {
                let mut cls = classes[x as usize].clone();
                cls.sort_unstable();
                let mut dat: Vec<(u32, Option<Value>)> = data[x as usize]
                    .iter()
                    .map(|&(p, v)| (p, value_shape(v)))
                    .collect();
                dat.sort_unstable();
                (x, hash64(&(cls, dat)))
            })
            .collect();
        for _ in 0..3 {
            colour = comp
                .iter()
                .map(|&x| {
                    let mut adj: Vec<(u32, bool, u64)> = edges[x as usize]
                        .iter()
                        .map(|&(r, d, y)| (r, d, colour[&y]))
                        .collect();
                    adj.sort_unstable();
                    (x, hash64(&(colour[&x], adj)))
                })
                .collect();
        }
        let mut order = comp.clone();
        order.sort_by_key(|&x| (colour[&x], x));
        let index: HashMap<u32, u32> = order.iter().enumerate().map(|(i, &x)| (x, i as u32)).collect();
        let mut value_numbers: HashMap<u32, u32> = HashMap::new();
        let mut form = Vec::new();
        let mut renames = Vec::new();
        for &x in &order {
            let i = index[&x];
            let mut cls = classes[x as usize].clone();
            cls.sort_unstable();
            cls.dedup();
            form.extend(cls.into_iter().map(|c| FormItem::Class(i, c)));
            let mut dat = data[x as usize].clone();
            dat.sort_by_key(|&(p, v)| (p, value_shape(v), v));
            dat.dedup();
            for (p, v) in dat {
                let canonical = match v {
                    Value::Exact(id) if renamable[id as usize] => {
                        let next = value_numbers.len() as u32;
                        let number = *value_numbers.entry(id).or_insert(next);
                        let canon = Value::Canon(number);
                        renames.push(((p, x, v), canon));
                        canon
                    }
                    other => other,
                };
                form.push(FormItem::Data(i, p, canonical));
            }
            for &(r, out, y) in &edges[x as usize] {
                if out {
                    form.push(FormItem::Role(r, i, index[&y]));
                }
            }
        }
        if let Some(list) = identities.get(&root) {
            for &k in list {
                let (same, m) = &abox.identities[k];
                let mut idx: Vec<u32> = m.iter().map(|x| index[x]).collect();
                idx.sort_unstable();
                idx.dedup();
                form.push(FormItem::Identity(*same, idx));
            }
        }
        form.sort_unstable();
        form.dedup();
        if seen_forms.contains(&form) {
            for &x in comp {
                keep[x as usize] = false;
            }
        } else {
            seen_forms.insert(form);
            renamed.extend(renames);
        }
    }
    component.clear();
    abox.class_assertions.retain(|&(x, _)| keep[x as usize]);
    abox.role_assertions.retain(|&(_, a, _)| keep[a as usize]);
    abox.identities.retain(|(_, m)| keep[m[0] as usize]);
    abox.data_assertions.retain(|&(_, x, _)| keep[x as usize]);
    for assertion in &mut abox.data_assertions {
        if let Some(&canon) = renamed.get(assertion) {
            assertion.2 = canon;
        }
    }
}

/// Whether a classification marks the full-IRI `class` unsatisfiable, in any
/// of the published representations (unsatisfiable list, a flat or grouped
/// subsumption by `owl:Nothing`).
pub(super) fn marks_unsatisfiable(evidence: &super::ClassificationEvidence, class: &str) -> bool {
    let bottom = |name: &str| name == OWL_NOTHING || name == "owl:Nothing";
    if evidence.classification.unsatisfiable.iter().any(|name| name == class) {
        return true;
    }
    if evidence
        .classification
        .subsumptions
        .iter()
        .any(|[sub, sup]| sub == class && bottom(sup))
    {
        return true;
    }
    if let Some(grouped) = &evidence.grouped_subsumptions {
        let Some(index) = grouped.iris.iter().position(|iri| iri.as_ref() == class) else {
            return false;
        };
        if let Some(graph) = &grouped.reachability_graph {
            let mut seen = HashSet::new();
            let mut stack = vec![index as u32];
            while let Some(node) = stack.pop() {
                for &next in &graph[node as usize] {
                    if bottom(&grouped.iris[next as usize]) {
                        return true;
                    }
                    if seen.insert(next) {
                        stack.push(next);
                    }
                }
            }
            return false;
        }
        if let Some(row) = grouped.rows.get(&(index as u32)) {
            return row.iter().any(|&sup| bottom(&grouped.iris[sup as usize]));
        }
    }
    false
}

/// Exact comparison of two flat taxonomies modulo representation: reflexive
/// rows, `owl:Thing` superclasses, `owl:Nothing` subclasses, and rows implied
/// by unsatisfiability are ignored; the remaining rows are compared under
/// transitive closure. Returns `false` (decline) on any doubt.
pub(super) fn same_taxonomy(left: &super::Classification, right: &super::Classification) -> bool {
    fn normal(c: &super::Classification) -> Option<(Vec<String>, Vec<(String, String)>)> {
        const THING: &[&str] = &["owl:Thing", "http://www.w3.org/2002/07/owl#Thing"];
        const NOTHING: &[&str] = &["owl:Nothing", "http://www.w3.org/2002/07/owl#Nothing"];
        if !c.consistent || c.dropped != 0 {
            return None;
        }
        let mut unsat: Vec<String> = c
            .unsatisfiable
            .iter()
            .filter(|name| !NOTHING.contains(&name.as_str()))
            .cloned()
            .collect();
        unsat.sort_unstable();
        unsat.dedup();
        let unsat_set: HashSet<&str> = unsat.iter().map(String::as_str).collect();
        let mut successors: HashMap<&str, Vec<&str>> = HashMap::new();
        for [sub, sup] in &c.subsumptions {
            if sub == sup
                || THING.contains(&sup.as_str())
                || NOTHING.contains(&sub.as_str())
                || unsat_set.contains(sub.as_str())
            {
                continue;
            }
            successors.entry(sub.as_str()).or_default().push(sup.as_str());
        }
        let mut pairs = Vec::new();
        for (&start, _) in &successors {
            let mut seen: HashSet<&str> = HashSet::new();
            let mut stack = vec![start];
            while let Some(node) = stack.pop() {
                for &next in successors.get(node).map(Vec::as_slice).unwrap_or(&[]) {
                    if next != start && seen.insert(next) {
                        stack.push(next);
                    }
                }
            }
            for sup in seen {
                pairs.push((start.to_string(), sup.to_string()));
            }
            if pairs.len() > 20_000_000 {
                return None;
            }
        }
        pairs.sort_unstable();
        Some((unsat, pairs))
    }
    match (normal(left), normal(right)) {
        (Some(left), Some(right)) => left == right,
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// S1: homomorphic merging; thinning; output.
// ---------------------------------------------------------------------------

fn merge_blocks(
    abox: &Abox,
    restricted_data: &HashSet<u32>,
    restricted_roles: &HashSet<u32>,
    mut pinned: Vec<bool>,
) -> Vec<u32> {
    let n = abox.individuals.names.len();
    for (_, members) in &abox.identities {
        for &m in members {
            pinned[m as usize] = true;
        }
    }
    let mut present = vec![false; n];
    let mut classes: Vec<Vec<u32>> = vec![Vec::new(); n];
    for &(x, c) in &abox.class_assertions {
        classes[x as usize].push(c);
        present[x as usize] = true;
    }
    let mut counted: Vec<Vec<(u32, Value)>> = vec![Vec::new(); n];
    for &(p, x, v) in &abox.data_assertions {
        present[x as usize] = true;
        if restricted_data.contains(&p) {
            counted[x as usize].push((p, v));
        }
    }
    let mut edges: Vec<Vec<(u32, bool, u32)>> = vec![Vec::new(); n];
    for &(r, a, b) in &abox.role_assertions {
        present[a as usize] = true;
        present[b as usize] = true;
        if restricted_roles.contains(&r) {
            edges[a as usize].push((r, true, b));
            edges[b as usize].push((r, false, a));
        }
    }
    for (_, members) in &abox.identities {
        for &m in members {
            present[m as usize] = true;
        }
    }
    let mut keys: HashMap<(Vec<u32>, Vec<(u32, Value)>, Option<u32>), u32> = HashMap::new();
    let mut block = vec![u32::MAX; n];
    for x in 0..n {
        if !present[x] {
            continue;
        }
        let mut cls = classes[x].clone();
        cls.sort_unstable();
        cls.dedup();
        let mut dat = counted[x].clone();
        dat.sort_unstable();
        dat.dedup();
        let pin = pinned[x].then_some(x as u32);
        let next = keys.len() as u32;
        block[x] = *keys.entry((cls, dat, pin)).or_insert(next);
    }
    let mut blocks = keys.len();
    for _ in 0..64 {
        let mut refined: HashMap<(u32, Vec<(u32, bool, u32)>), u32> = HashMap::new();
        let mut next_block = vec![u32::MAX; n];
        for x in 0..n {
            if !present[x] {
                continue;
            }
            let mut adj: Vec<(u32, bool, u32)> = edges[x]
                .iter()
                .map(|&(r, d, y)| (r, d, block[y as usize]))
                .collect();
            adj.sort_unstable();
            adj.dedup();
            let next = refined.len() as u32;
            next_block[x] = *refined.entry((block[x], adj)).or_insert(next);
        }
        block = next_block;
        if refined.len() == blocks {
            break;
        }
        blocks = refined.len();
    }
    block
}

fn render_value(abox: &Abox, value: Value) -> String {
    match value {
        Value::Exact(id) => abox.literals.names[id as usize].clone(),
        Value::Canon(n) => format!("\"{CANON_PREFIX}{n}\"^^{XSD_STRING}"),
    }
}

/// Cheap rejection of sources without a dense ABox: count assertion
/// keywords in three samples.
fn looks_like_abox(path: &Path, bytes: u64) -> std::io::Result<bool> {
    let mut file = std::fs::File::open(path)?;
    let len = SAMPLE_BYTES.min(bytes as usize);
    let mut hits = 0usize;
    for start in [0, bytes.saturating_sub(len as u64) / 2, bytes.saturating_sub(len as u64)] {
        file.seek(SeekFrom::Start(start))?;
        let mut sample = vec![0; len];
        file.read_exact(&mut sample)?;
        for token in [&b"Assertion("[..], &b"Individual"[..]] {
            hits += sample.windows(token.len()).filter(|w| *w == token).count();
        }
    }
    Ok(hits >= 1000)
}

/// Build the quotient source or return `None` (unchanged semantics).
fn decline_trace(site: u32) {
    if std::env::var_os("KM_TIMING").is_some() {
        eprintln!("KM_TIMING ABox quotient not built: site {site}");
    }
}

pub(super) fn try_build(path: &Path) -> Result<Option<Quotient>, OrchestrateError> {
    let bytes = path.metadata()?.len();
    if bytes < MIN_SOURCE_BYTES || !looks_like_abox(path, bytes)? {
        return { decline_trace(1); Ok(None) };
    }
    let text = match std::fs::read_to_string(path) {
        Ok(text) => text,
        Err(_) => return { decline_trace(2); Ok(None) },
    };
    let Some(built) = build_from_text(&text, MIN_ABOX_ASSERTIONS, MIN_REDUCTION)? else {
        return { decline_trace(3); Ok(None) };
    };
    drop(text);
    let output = TempPath::new(".abox-quotient.ofn");
    std::fs::write(output.path(), &built.source)?;
    let tbox = match &built.tbox {
        Some(tbox) => {
            let path = TempPath::new(".abox-quotient-tbox.ofn");
            std::fs::write(path.path(), tbox)?;
            Some(path)
        }
        None => None,
    };
    Ok(Some(Quotient {
        path: output,
        tbox,
        atomic_classes: built.atomic_classes,
        subset_of_source: built.subset_of_source,
        individuals: built.stats.0,
        blocks: built.stats.1,
        assertions: built.stats.2,
        quotient_assertions: built.stats.3,
    }))
}

type Stats = (usize, usize, usize, usize);

struct Built {
    source: String,
    /// The source without its ABox, present when the TBox has nominals.
    tbox: Option<String>,
    /// Atomic mode: `source` is the TBox alone; these classes must be
    /// satisfiable.
    atomic_classes: Option<Vec<String>>,
    subset_of_source: bool,
    stats: Stats,
}

fn build_from_text(
    text: &str,
    min_assertions: usize,
    min_reduction: usize,
) -> Result<Option<Built>, OrchestrateError> {
    let Ok(document) = parse_document(text) else { return { decline_trace(4); Ok(None) } };
    let expander = Expander { prefixes: document.prefixes.clone() };
    let mut screen = Screen::default();
    let mut abox = Abox::default();
    let mut pending = Vec::new();
    let mut abox_spans = Vec::new();
    for item in &document.items {
        let result = if is_abox_keyword(item.keyword) {
            abox_spans.push((item.start, item.end));
            read_abox_item(&mut abox, &mut screen, &expander, item, &mut pending)
        } else if IGNORED_ITEMS.contains(&item.keyword) {
            Ok(())
        } else {
            screen.observe(&expander, item.keyword, &item.tokens, true)
        };
        if result.is_err() {
            if std::env::var_os("KM_TIMING").is_some() {
                let shown: Vec<String> = item.tokens.iter().take(12).map(|t| format!("{t:?}")).collect();
                eprintln!("KM_TIMING ABox quotient item declined: {} {}", item.keyword, shown.join(" "));
            }
            return { decline_trace(5); Ok(None) };
        }
    }
    let assertions = abox.assertion_count();
    if assertions < min_assertions {
        return { decline_trace(6); Ok(None) };
    }
    // Renamability of every ABox literal against the complete literal set.
    let canon_clash = screen.literals.iter().any(|l| l.starts_with(CANON_PREFIX))
        || pending.iter().any(|(_, lexical)| lexical.starts_with(CANON_PREFIX));
    let renaming = !screen.string_sensitive && !canon_clash;
    for (index, (canonical, lexical)) in pending.iter().enumerate() {
        abox.renamable[index] = renaming
            && canonical.ends_with(&format!("^^{XSD_STRING}"))
            && !screen.literals.contains(lexical);
    }
    let individuals = abox.individuals.names.len();
    // Component canonicalisation relies on closure of the TBox under disjoint
    // unions, which TBox nominals break. Homomorphic merging that fixes every
    // nominal individual remains sound for consistency; publication then
    // additionally requires the TBox sandwich check (see `Quotient::tbox`).
    let sandwich = !screen.nominal_individuals.is_empty();
    // Source assertions by id, before canonicalisation drops duplicate
    // components and renames string values. Individual, class, role and
    // property ids are stable across canonicalisation.
    let source_classes: HashSet<(u32, u32)> = abox.class_assertions.iter().copied().collect();
    let source_roles: HashSet<(u32, u32, u32)> = abox.role_assertions.iter().copied().collect();
    let source_data: HashSet<(u32, u32, Value)> = abox.data_assertions.iter().copied().collect();
    if !sandwich {
        canonicalize_components(&mut abox);
    }
    let mut pinned = vec![false; abox.individuals.names.len()];
    for name in &screen.nominal_individuals {
        if let Some(&id) = abox.individuals.ids.get(name) {
            pinned[id as usize] = true;
        }
    }

    let restricted_data_names = screen.restricted_data();
    let restricted_roles_names = screen.restricted_roles();
    let restricted_data: HashSet<u32> = abox
        .properties
        .names
        .iter()
        .enumerate()
        .filter(|(_, name)| restricted_data_names.contains(*name))
        .map(|(i, _)| i as u32)
        .collect();
    let restricted_roles: HashSet<u32> = abox
        .roles
        .names
        .iter()
        .enumerate()
        .filter(|(_, name)| restricted_roles_names.contains(*name))
        .map(|(i, _)| i as u32)
        .collect();
    let block = merge_blocks(&abox, &restricted_data, &restricted_roles, pinned);
    // Representative: first individual (in source order) of each block.
    let mut representative: HashMap<u32, u32> = HashMap::new();
    for (x, &b) in block.iter().enumerate() {
        if b != u32::MAX {
            representative.entry(b).or_insert(x as u32);
        }
    }
    let h = |x: u32| -> &str { &abox.individuals.names[representative[&block[x as usize]] as usize] };
    let rep_id = |x: u32| -> u32 { representative[&block[x as usize]] };
    let mut subset_of_source = true;

    let mut lines: Vec<String> = Vec::new();
    let mut seen: HashSet<String> = HashSet::new();
    let mut push = |line: String, lines: &mut Vec<String>| {
        if seen.insert(line.clone()) {
            lines.push(line);
        }
    };
    for &(x, c) in &abox.class_assertions {
        subset_of_source &= source_classes.contains(&(rep_id(x), c));
        push(format!("ClassAssertion({} {})", abox.classes.names[c as usize], h(x)), &mut lines);
    }
    for &(r, a, b) in &abox.role_assertions {
        subset_of_source &= source_roles.contains(&(r, rep_id(a), rep_id(b)));
        push(
            format!("ObjectPropertyAssertion({} {} {})", abox.roles.names[r as usize], h(a), h(b)),
            &mut lines,
        );
    }
    // Thinning: keep one renamable value per (node, unrestricted property).
    let mut thinned: HashMap<(u32, u32), Value> = HashMap::new();
    for &(p, x, v) in &abox.data_assertions {
        let node = representative[&block[x as usize]];
        if !restricted_data.contains(&p) && abox.is_renamable(v) {
            let slot = thinned.entry((node, p)).or_insert(v);
            if v < *slot {
                *slot = v;
            }
            continue;
        }
        subset_of_source &= source_data.contains(&(p, rep_id(x), v));
        push(
            format!(
                "DataPropertyAssertion({} {} {})",
                abox.properties.names[p as usize],
                h(x),
                render_value(&abox, v)
            ),
            &mut lines,
        );
    }
    let mut thinned: Vec<_> = thinned.into_iter().collect();
    thinned.sort_unstable();
    for ((node, p), v) in thinned {
        subset_of_source &= source_data.contains(&(p, node, v));
        push(
            format!(
                "DataPropertyAssertion({} {} {})",
                abox.properties.names[p as usize],
                abox.individuals.names[node as usize],
                render_value(&abox, v)
            ),
            &mut lines,
        );
    }
    for (same, members) in &abox.identities {
        // An identity axiom is a source axiom only if no member was renamed
        // to its block representative.
        subset_of_source &= members.iter().all(|&m| rep_id(m) == m);
        let names: Vec<&str> = members.iter().map(|&m| h(m)).collect();
        push(
            format!(
                "{}({})",
                if *same { "SameIndividual" } else { "DifferentIndividuals" },
                names.join(" ")
            ),
            &mut lines,
        );
    }
    let blocks = representative.len();
    if lines.len().saturating_mul(min_reduction) > assertions {
        if std::env::var_os("KM_TIMING").is_some() {
            eprintln!(
                "KM_TIMING ABox quotient reduction too small: individuals={} blocks={} assertions={} lines={} roles={} classes={} data={} restricted_roles={} restricted_data={}",
                individuals, representative.len(), assertions, lines.len(),
                abox.role_assertions.len(), abox.class_assertions.len(), abox.data_assertions.len(),
                restricted_roles.len(), restricted_data.len()
            );
        }
        return { decline_trace(7); Ok(None) };
    }
    // Atomic mode: the quotient asserts exactly one named class per node and
    // nothing else. Over a TBox closed under disjoint unions the ontology is
    // then consistent iff every asserted class is satisfiable in the TBox, so
    // the TBox alone is classified (without any individual) and the asserted
    // classes are checked against its unsatisfiable set.
    let atomic = (!sandwich
        && abox.role_assertions.is_empty()
        && abox.data_assertions.is_empty()
        && abox.identities.is_empty())
    .then(|| {
        let mut per_node: HashMap<u32, HashSet<u32>> = HashMap::new();
        for &(x, c) in &abox.class_assertions {
            per_node.entry(representative[&block[x as usize]]).or_default().insert(c);
        }
        let mut classes = Vec::new();
        for set in per_node.values() {
            if set.len() != 1 {
                return None;
            }
            let name = &abox.classes.names[*set.iter().next()? as usize];
            let iri = name.strip_prefix('<')?.strip_suffix('>')?;
            if iri == OWL_NOTHING {
                return None;
            }
            if iri != OWL_THING {
                classes.push(iri.to_string());
            }
        }
        classes.sort_unstable();
        classes.dedup();
        Some(classes)
    })
    .flatten();
    // Source with every ABox item removed, quotient inserted before the
    // closing parenthesis of the ontology.
    let mut tbox = String::with_capacity(text.len() / 4);
    let mut cursor = 0;
    for (start, end) in abox_spans {
        tbox.push_str(&text[cursor..start]);
        cursor = end;
    }
    tbox.push_str(&text[cursor..document.close]);
    let mut out = tbox.clone();
    if atomic.is_none() {
        out.push('\n');
        for line in &lines {
            out.push_str(line);
            out.push('\n');
        }
    }
    out.push_str(&text[document.close..]);
    tbox.push_str(&text[document.close..]);
    Ok(Some(Built {
        source: out,
        tbox: sandwich.then_some(tbox),
        atomic_classes: atomic,
        subset_of_source,
        stats: (individuals, blocks, assertions, lines.len()),
    }))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn build(text: &str) -> Option<String> {
        build_from_text(text, 1, 1).unwrap().map(|b| b.source)
    }

    fn quotient_lines(text: &str) -> Vec<String> {
        build_from_text(text, 1, 1)
            .unwrap()
            .map(|b| {
                b.source
                    .lines()
                    .filter(|l| l.contains("Assertion(") || l.contains("Individual"))
                    .map(str::to_string)
                    .collect()
            })
            .unwrap_or_default()
    }

    const HEAD: &str = "Prefix(:=<http://e/>)\nPrefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\nOntology(<http://e/o>\n";

    fn many(body: &str, n: usize) -> String {
        (0..n).map(|i| body.replace("{i}", &i.to_string())).collect::<Vec<_>>().join("\n")
    }

    #[test]
    fn source_subset_flag_is_exact() {
        // Equal-key individuals merge onto the first one; every emitted
        // assertion is then a source assertion of that representative.
        let subset = format!("{HEAD}SubClassOf(:A :B)\n{}\n)\n", many("ClassAssertion(:A :a{i})", 20));
        assert!(build_from_text(&subset, 1, 1).unwrap().unwrap().subset_of_source);
        // a1 and a2 merge; s(a2, c) is emitted as s(a1, c), which the source
        // does not contain.
        let merged = format!(
            "{HEAD}SubClassOf(:A :B)\nClassAssertion(:A :a1)\nClassAssertion(:A :a2)\n\
             ObjectPropertyAssertion(:r :a1 :c)\nObjectPropertyAssertion(:s :a2 :c)\n)\n"
        );
        let built = build_from_text(&merged, 1, 1).unwrap().unwrap();
        assert!(built.source.contains("ObjectPropertyAssertion(<http://e/s> <http://e/a1> <http://e/c>)"), "{}", built.source);
        assert!(!built.subset_of_source);
    }

    #[test]
    fn merges_individuals_with_equal_keys_and_expands_prefixes() {
        let text = format!(
            "{HEAD}SubClassOf(:A :B)\n{}\n{}\n)\n",
            many("ClassAssertion(:A :a{i})", 20),
            many("ObjectPropertyAssertion(:r :a{i} <http://e/b{i}>)", 20)
        );
        let lines = quotient_lines(&text);
        assert_eq!(lines.len(), 2, "{lines:?}");
        assert!(lines.contains(&"ClassAssertion(<http://e/A> <http://e/a0>)".to_string()), "{lines:?}");
    }

    #[test]
    fn declines_nominals_keys_rules_universal_role_and_comments() {
        for axiom in [
            "HasKey(:A () (:p))",
            "SubObjectPropertyOf(:r owl:topObjectProperty)",
            "NegativeObjectPropertyAssertion(:r :a0 :a1)",
        ] {
            let text = format!(
                "Prefix(owl:=<http://www.w3.org/2002/07/owl#>)\n{HEAD}{axiom}\n{}\n)\n",
                many("ClassAssertion(:A :a{i})", 20)
            );
            assert!(build(&text).is_none(), "{axiom}");
        }
        let comment = format!("{HEAD}# comment\n{}\n)\n", many("ClassAssertion(:A :a{i})", 20));
        assert!(build(&comment).is_none());
        let abox_nominal = format!(
            "{HEAD}{}\nClassAssertion(ObjectHasValue(:r :x) :y)\n)\n",
            many("ClassAssertion(:A :a{i})", 20)
        );
        assert!(build(&abox_nominal).is_none());
    }

    #[test]
    fn tbox_nominals_pin_their_individuals_and_request_the_sandwich() {
        let text = format!(
            "{HEAD}EquivalentClasses(:C ObjectSomeValuesFrom(:r ObjectOneOf(:a0 :a1)))\n{}\n)\n",
            many("ClassAssertion(:A :a{i})", 20)
        );
        let built = build_from_text(&text, 1, 1).unwrap().expect("quotient");
        let tbox = built.tbox.expect("sandwich TBox");
        assert!(!tbox.contains("ClassAssertion"));
        assert!(tbox.contains("ObjectOneOf"));
        let lines: Vec<_> = built.source.lines().filter(|l| l.starts_with("ClassAssertion")).collect();
        // a0 and a1 are fixed; all other individuals merge into one.
        assert_eq!(lines.len(), 3, "{lines:?}");
        assert!(lines.contains(&"ClassAssertion(<http://e/A> <http://e/a1>)"), "{lines:?}");
        let plain = format!("{HEAD}{}\n)\n", many("ClassAssertion(:A :a{i})", 20));
        assert!(build_from_text(&plain, 1, 1).unwrap().unwrap().tbox.is_none());
    }

    /// Diagnostic admission survey: `KM_ABOX_QUOTIENT_SURVEY=<file of paths>
    /// cargo test --release --lib abox_quotient_survey -- --ignored --nocapture`.
    #[test]
    #[ignore]
    fn abox_quotient_survey() {
        let Some(list) = std::env::var_os("KM_ABOX_QUOTIENT_SURVEY") else { return };
        for path in std::fs::read_to_string(list).unwrap().lines() {
            let started = std::time::Instant::now();
            let result = try_build(Path::new(path)).unwrap();
            match result {
                Some(q) => println!(
                    "ADMIT {path} individuals={} blocks={} assertions={} quotient={} sandwich={} secs={:.2}",
                    q.individuals,
                    q.blocks,
                    q.assertions,
                    q.quotient_assertions,
                    q.tbox.is_some(),
                    started.elapsed().as_secs_f64()
                ),
                None => println!("DECLINE {path} secs={:.2}", started.elapsed().as_secs_f64()),
            }
        }
    }

    #[test]
    fn taxonomy_comparison_ignores_representation_only() {
        let c = |rows: &[(&str, &str)], unsat: &[&str]| super::super::Classification {
            approximate: None,
            consistent: true,
            subsumptions: rows.iter().map(|(a, b)| [a.to_string(), b.to_string()]).collect(),
            unsatisfiable: unsat.iter().map(|u| u.to_string()).collect(),
            dropped: 0,
        };
        let reduced = c(&[("A", "B"), ("B", "C")], &[]);
        let closed = c(&[("A", "B"), ("B", "C"), ("A", "C"), ("A", "owl:Thing"), ("A", "A")], &[]);
        assert!(same_taxonomy(&reduced, &closed));
        let more = c(&[("A", "B"), ("B", "C"), ("C", "A")], &[]);
        assert!(!same_taxonomy(&reduced, &more));
        let unsat = c(&[("A", "B"), ("B", "C"), ("D", "A")], &["D"]);
        let unsat_alone = c(&[("A", "B"), ("B", "C")], &["D"]);
        assert!(same_taxonomy(&unsat, &unsat_alone));
        assert!(!same_taxonomy(&unsat_alone, &reduced));
    }

    #[test]
    fn single_class_abox_becomes_a_tbox_with_asserted_class_checks() {
        let text = format!(
            "{HEAD}SubClassOf(:A :B)\n{}\n{}\nClassAssertion(owl:Thing :t)\n)\n",
            many("ClassAssertion(:A :a{i})", 20),
            many("ClassAssertion(:B :b{i})", 20)
        );
        let built = build_from_text(&text, 1, 1).unwrap().expect("quotient");
        assert!(!built.source.contains("ClassAssertion"));
        assert_eq!(
            built.atomic_classes.unwrap(),
            vec!["http://e/A".to_string(), "http://e/B".to_string()]
        );
        // Two classes on one individual need a joint check: keep the ABox.
        let joint = format!("{HEAD}{}\nClassAssertion(:B :a0)\n)\n", many("ClassAssertion(:A :a{i})", 20));
        let built = build_from_text(&joint, 1, 1).unwrap().expect("quotient");
        assert!(built.atomic_classes.is_none());
        assert!(built.source.contains("ClassAssertion"));
    }

    #[test]
    fn multiline_literals_and_annotations_are_read() {
        let text = format!(
            "{HEAD}{}\nDataPropertyAssertion(Annotation(:c \"x\") :p :a0 \"line one\nline two\"^^xsd:string)\n)\n",
            many("ClassAssertion(:A :a{i})", 20)
        );
        let out = build(&text).expect("quotient");
        assert!(!out.contains("Annotation(:c"));
    }

    #[test]
    fn functional_data_values_keep_individuals_apart() {
        let text = format!(
            "{HEAD}FunctionalDataProperty(:f)\nSubDataPropertyOf(:g :f)\n{}\n{}\n)\n",
            many("ClassAssertion(:A :a{i})", 20),
            many("DataPropertyAssertion(:g :a{i} \"{i}\"^^xsd:integer)", 20)
        );
        let lines = quotient_lines(&text);
        // :g inherits the count restriction of :f; integer values are never
        // renamed, so all 20 individuals stay apart.
        assert_eq!(lines.iter().filter(|l| l.starts_with("ClassAssertion")).count(), 20);
    }

    #[test]
    fn unrestricted_string_values_are_thinned() {
        let text = format!(
            "{HEAD}DataPropertyRange(:p xsd:string)\n{}\n{}\n)\n",
            many("ClassAssertion(:A :a{i})", 20),
            many("DataPropertyAssertion(:p :a{i} \"v{i}\")", 20)
        );
        let lines = quotient_lines(&text);
        assert_eq!(lines.iter().filter(|l| l.starts_with("DataPropertyAssertion")).count(), 1, "{lines:?}");
    }

    #[test]
    fn isomorphic_components_with_renamed_strings_collapse() {
        let text = format!(
            "{HEAD}FunctionalDataProperty(:id)\nDataPropertyRange(:kind DataOneOf(\"x\" \"y\"))\n{}\n{}\n{}\n{}\n)\n",
            many("ClassAssertion(:A :a{i})", 20),
            many("ObjectPropertyAssertion(:r :a{i} :b{i})", 20),
            many("DataPropertyAssertion(:id :a{i} \"id{i}\")", 20),
            many("DataPropertyAssertion(:kind :b{i} \"x\")", 20)
        );
        let lines = quotient_lines(&text);
        assert_eq!(lines.iter().filter(|l| l.starts_with("ClassAssertion")).count(), 1, "{lines:?}");
        assert!(lines.iter().any(|l| l.contains(CANON_PREFIX)), "{lines:?}");
        // TBox literals are never renamed.
        assert!(lines.iter().any(|l| l.contains("\"x\"^^")), "{lines:?}");
    }

    #[test]
    fn facet_restrictions_disable_string_renaming() {
        let text = format!(
            "{HEAD}FunctionalDataProperty(:id)\nDataPropertyRange(:id DatatypeRestriction(xsd:string xsd:maxLength \"3\"^^xsd:integer))\n{}\n{}\n)\n",
            many("ClassAssertion(:A :a{i})", 20),
            many("DataPropertyAssertion(:id :a{i} \"id{i}\")", 20)
        );
        let lines = quotient_lines(&text);
        assert!(!lines.iter().any(|l| l.contains(CANON_PREFIX)), "{lines:?}");
        assert_eq!(lines.iter().filter(|l| l.starts_with("ClassAssertion")).count(), 20);
    }

    #[test]
    fn identity_participants_are_never_merged() {
        let text = format!(
            "{HEAD}{}\nDifferentIndividuals(:a0 :a1)\n)\n",
            many("ClassAssertion(:A :a{i})", 20)
        );
        let lines = quotient_lines(&text);
        assert!(lines.contains(&"DifferentIndividuals(<http://e/a0> <http://e/a1>)".to_string()), "{lines:?}");
    }

    /// Re-validation of a quotient is skipped for the orchestrator's own
    /// rewrites (`TrustedRewrite`). Every rewrite of a valid source must
    /// therefore stay valid: TBox and declarations are copied verbatim, every
    /// emitted assertion reuses a source class, property, individual, and
    /// literal spelling (prefixed names expanded to the full IRI they denote),
    /// and the only new token is a canonical `xsd:string` literal. This test
    /// fails if a rewrite ever emits a document `check_source` rejects.
    #[test]
    fn quotients_of_valid_sources_pass_conformance() {
        let sources = [
            // class + role assertions, merged blocks, expanded prefixes
            format!(
                "{HEAD}Declaration(Class(:A))\nSubClassOf(:A :B)\n{}\n{}\n)\n",
                many("ClassAssertion(:A :a{i})", 20),
                many("ObjectPropertyAssertion(:r :a{i} <http://e/b{i}>)", 20)
            ),
            // thinned and canonically renamed strings, TBox literal kept
            format!(
                "{HEAD}DataPropertyRange(:p xsd:string)\nSubClassOf(:A DataHasValue(:q \"x\"))\n{}\n{}\n{}\n)\n",
                many("ClassAssertion(:A :a{i})", 20),
                many("DataPropertyAssertion(:p :a{i} \"v{i}\")", 20),
                many("DataPropertyAssertion(:q :a{i} \"w{i}\"^^xsd:string)", 20)
            ),
            // typed literals under a count-restricted property, identities
            format!(
                "{HEAD}FunctionalDataProperty(:f)\n{}\n{}\nSameIndividual(:a0 :a1)\nDifferentIndividuals(:a2 :a3)\n)\n",
                many("ClassAssertion(:A :a{i})", 20),
                many("DataPropertyAssertion(:f :a{i} \"{i}\"^^xsd:integer)", 20)
            ),
            // isomorphic components over two roles
            format!(
                "{HEAD}SubClassOf(:A ObjectSomeValuesFrom(:r :B))\n{}\n{}\n{}\n)\n",
                many("ClassAssertion(:A :x{i})", 20),
                many("ObjectPropertyAssertion(:r :x{i} :y{i})", 20),
                many("DataPropertyAssertion(:p :y{i} \"s{i}\")", 20)
            ),
        ];
        let mut built_any = false;
        for source in &sources {
            crate::frontend::conformance::check_source(source)
                .unwrap_or_else(|e| panic!("fixture must be valid: {e}\n{source}"));
            let Some(built) = build_from_text(source, 1, 1).unwrap() else { continue };
            built_any = true;
            crate::frontend::conformance::check_source(&built.source)
                .unwrap_or_else(|e| panic!("quotient rejected: {e}\n{}", built.source));
            if let Some(tbox) = &built.tbox {
                crate::frontend::conformance::check_source(tbox)
                    .unwrap_or_else(|e| panic!("TBox document rejected: {e}\n{tbox}"));
            }
        }
        assert!(built_any, "no fixture produced a quotient");
    }
}

/// The source minus every axiom that mentions a data property, a datatype,
/// a literal, or a `Data*` constructor; `None` when nothing is removed.
///
/// A subset of an ontology has every model of the ontology, so its
/// inconsistency is the ontology's inconsistency. The caller publishes only
/// a certified inconsistent answer from it. Removing the data part lets the
/// native bridge decide object-level inconsistency that its datatype
/// admission would otherwise defer (ore_ont_1123: the quotient's TBox makes
/// `owl:Thing` unsatisfiable through universally satisfied `∀` definitions,
/// independently of its data properties).
pub(super) fn data_free_subset(path: &Path) -> Result<Option<TempPath>, OrchestrateError> {
    use crate::frontend::sexpr::Node;
    let text = std::fs::read_to_string(path)?;
    let Some(ontology_start) = text.find("Ontology(") else {
        return Ok(None);
    };
    let mut data_properties: HashSet<String> = HashSet::new();
    let parse = |text: &str, f: &mut dyn FnMut(&Node<'_>)| {
        crate::frontend::parse::for_each_ontology_child(text, |node| {
            f(node);
            Ok(())
        })
    };
    if parse(&text, &mut |node| {
        if let Node::List("Declaration", args) = node {
            if let [Node::List("DataProperty", inner)] = args.as_slice() {
                if let [Node::Atom(name)] = inner.as_slice() {
                    data_properties.insert(name.to_string());
                }
            }
        }
    })
    .is_err()
    {
        return Ok(None);
    }
    fn mentions_data(node: &Node<'_>, data_properties: &HashSet<String>) -> bool {
        match node {
            Node::Atom(atom) => {
                atom.starts_with('"') || atom.contains("^^") || data_properties.contains(*atom)
            }
            Node::List(head, args) => {
                head.starts_with("Data")
                    || *head == "Datatype"
                    || *head == "DatatypeDefinition"
                    || *head == "HasKey"
                    || args.iter().any(|arg| mentions_data(arg, data_properties))
            }
        }
    }
    fn write(node: &Node<'_>, out: &mut String) {
        match node {
            Node::Atom(atom) => out.push_str(atom),
            Node::List(head, args) => {
                out.push_str(head);
                out.push('(');
                for (index, arg) in args.iter().enumerate() {
                    if index > 0 {
                        out.push(' ');
                    }
                    write(arg, out);
                }
                out.push(')');
            }
        }
    }
    let mut body = String::new();
    let mut removed = 0usize;
    if parse(&text, &mut |node| {
        if mentions_data(node, &data_properties) {
            removed += 1;
        } else {
            write(node, &mut body);
            body.push('\n');
        }
    })
    .is_err()
    {
        return Ok(None);
    }
    if removed == 0 {
        return Ok(None);
    }
    let output = TempPath::new(".data-free-subset.ofn");
    let mut content = String::with_capacity(text.len());
    content.push_str(&text[..ontology_start]);
    content.push_str("Ontology(\n");
    content.push_str(&body);
    content.push_str(")\n");
    std::fs::write(output.path(), content)?;
    Ok(Some(output))
}

#[cfg(test)]
mod data_free_subset_tests {
    use super::data_free_subset;

    fn subset(text: &str) -> Option<String> {
        let input = super::TempPath::new(".data-free-input.ofn");
        std::fs::write(input.path(), text).unwrap();
        data_free_subset(input.path())
            .unwrap()
            .map(|output| std::fs::read_to_string(output.path()).unwrap())
    }

    #[test]
    fn data_axioms_are_removed_and_object_axioms_kept() {
        let text = "Prefix(:=<http://f/>)\nPrefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\n\
            Ontology(<http://f/o>\n\
            Declaration(Class(:A)) Declaration(Class(:B)) Declaration(DataProperty(:p))\n\
            SubClassOf(:A :B)\n\
            SubClassOf(:A DataSomeValuesFrom(:p xsd:string))\n\
            FunctionalDataProperty(:p)\n\
            DataPropertyRange(:p xsd:integer)\n\
            ClassAssertion(:A :a)\n\
            DataPropertyAssertion(:p :a \"1\"^^xsd:integer)\n\
            )\n";
        let out = subset(text).expect("data content is removed");
        assert!(out.starts_with("Prefix(:=<http://f/>)"));
        assert!(out.contains("SubClassOf(:A :B)"));
        assert!(out.contains("ClassAssertion(:A :a)"));
        assert!(out.contains("Declaration(Class(:A))"));
        for removed in ["DataSomeValuesFrom", "FunctionalDataProperty", "DataPropertyRange", "DataPropertyAssertion", "DataProperty(:p)"] {
            assert!(!out.contains(removed), "{removed} survived: {out}");
        }
    }

    #[test]
    fn data_free_input_has_no_subset() {
        let text = "Prefix(:=<http://f/>)\nOntology(<http://f/o>\nDeclaration(Class(:A))\nSubClassOf(:A :A)\n)\n";
        assert!(subset(text).is_none());
    }
}
