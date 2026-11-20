//! Realization: the entailed named types of every named individual and the
//! entailed equalities between named individuals (`km classify --realize`).
//!
//! # Semantics
//!
//! For a consistent ontology `O`, a named individual `a` and a named class `C`
//! other than `owl:Thing`:
//!
//! * `TYPE a C` is reported iff `O ⊨ C(a)` (mode [`TypeMode::All`]), or iff
//!   additionally no reported type `D` of `a` satisfies `O ⊨ D ⊑ C` and
//!   `O ⊭ C ⊑ D` (mode [`TypeMode::Direct`]);
//! * `SAME a b` is reported, once per unordered pair with `a < b`, iff
//!   `a ≠ b` and `O ⊨ a = b`.
//!
//! An individual with no `TYPE` row has `owl:Thing` as its only type. For an
//! inconsistent ontology the classification reports `CONSISTENT 0` and no
//! `TYPE` or `SAME` rows are written (every assertion is entailed).
//!
//! # Mechanism
//!
//! None of KM's reasoning routes currently publishes a completeness guarantee
//! for ground facts `C(a)`: the EL++ completion rejects individual terms, the
//! TBox-only routes do not place the ABox in the saturated clause set, and the
//! consequence-based and hypertableau routes are complete for query-class
//! subsumption, not for unit ground facts under their literal orderings.
//! Reading types from a saturated state would therefore need a new
//! completeness argument (and Lean re-certification for the CB calculus).
//!
//! Realization therefore uses the exact reduction to classification. For each
//! named individual `a` of the source signature, a fresh class `P_a` with
//! `P_a ≡ {a}` is added. This is a conservative extension: it entails no new
//! subsumption between source names. Then, for a consistent `O`,
//! `O ⊨ C(a)` iff `O' ⊨ P_a ⊑ C`, and `O ⊨ a = b` iff `O' ⊨ P_a ⊑ P_b`.
//! The extended ontology is classified once by the ordinary production
//! pipeline, so every route that classifies it exactly also realizes `O`
//! exactly. Rows that mention a probe class are then removed from the
//! taxonomy, which leaves the classification of `O` itself.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::io::Write;
use std::path::Path;

use crate::frontend::sexpr::{self, Node};

use super::{tmpfile, Classification, Config, OrchestrateError, TrustedRewrite};

const OWL_THING: &str = "http://www.w3.org/2002/07/owl#Thing";

/// Diagnostic override: realize under a manually forced route.
pub const ANY_ROUTE_ENV: &str = "KM_REALIZE_ANY_ROUTE";

/// Which entailed types `TYPE` rows report.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TypeMode {
    /// Every entailed named type except `owl:Thing`.
    All,
    /// The most specific entailed named types (all members of each minimal
    /// equivalence class), except `owl:Thing`.
    Direct,
}

/// The classification of an ontology together with its realization.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Realization {
    /// The classification of the source ontology, as `km classify` reports it.
    pub classification: Classification,
    /// `[individual, class]` rows, sorted.
    pub types: Vec<[String; 2]>,
    /// `[a, b]` rows with `a < b`, sorted.
    pub same: Vec<[String; 2]>,
}

/// The source spelling of every named individual that occurs in an OFN
/// document, in first-occurrence order and without duplicates.
///
/// Individuals are the arguments in individual position of declarations,
/// assertions, `SameIndividual`/`DifferentIndividuals`, `ObjectOneOf`,
/// `ObjectHasValue` and DL-safe rule atoms. Anonymous individuals (`_:x`) are
/// not named individuals and are skipped. Annotation values are IRIs, not
/// individuals.
pub fn source_individuals(text: &str) -> Result<Vec<String>, OrchestrateError> {
    let mut seen: HashSet<&str> = HashSet::new();
    let mut ordered: Vec<String> = Vec::new();
    crate::frontend::parse::for_each_ontology_child(text, |node| {
        let mut found = Vec::new();
        individuals_in(node, &mut found);
        for token in found {
            if seen.insert(token) {
                ordered.push(token.to_string());
            }
        }
        Ok(())
    })
    .map_err(|error| OrchestrateError::OutOfFragment(error.0))?;
    Ok(ordered)
}

fn push_individual<'a>(node: Option<&&Node<'a>>, out: &mut Vec<&'a str>) {
    if let Some(Node::Atom(token)) = node.copied() {
        if !token.starts_with('"')
            && !token.starts_with("_:")
            && !crate::frontend::lenient::is_skolem_anon_iri(token)
        {
            out.push(token);
        }
    }
}

fn individuals_in<'a>(node: &Node<'a>, out: &mut Vec<&'a str>) {
    let Node::List(head, args) = node else { return };
    let plain: Vec<&Node<'a>> = args
        .iter()
        .filter(|arg| arg.head() != Some("Annotation"))
        .collect();
    match *head {
        "Annotation" | "AnnotationAssertion" | "SubAnnotationPropertyOf"
        | "AnnotationPropertyDomain" | "AnnotationPropertyRange" | "Prefix" | "Import" => {}
        "Declaration" => {
            if let Some(Node::List("NamedIndividual", inner)) = plain.first().copied() {
                if let Some(Node::Atom(token)) = inner.first() {
                    if !token.starts_with("_:")
                        && !crate::frontend::lenient::is_skolem_anon_iri(token)
                    {
                        out.push(token);
                    }
                }
            }
        }
        "ClassAssertion" => {
            if let Some(class) = plain.first() {
                individuals_in(class, out);
            }
            push_individual(plain.get(1), out);
        }
        "ObjectPropertyAssertion" | "NegativeObjectPropertyAssertion" => {
            push_individual(plain.get(1), out);
            push_individual(plain.get(2), out);
        }
        "DataPropertyAssertion" | "NegativeDataPropertyAssertion" => {
            push_individual(plain.get(1), out);
        }
        "SameIndividual" | "DifferentIndividuals" | "ObjectOneOf" => {
            for arg in &plain {
                push_individual(Some(arg), out);
            }
        }
        "ObjectHasValue" => push_individual(plain.get(1), out),
        // DL-safe rule atoms: a non-variable argument is a named individual.
        "ClassAtom" => {
            if let Some(class) = plain.first() {
                individuals_in(class, out);
            }
            push_individual(plain.get(1), out);
        }
        "ObjectPropertyAtom" => {
            push_individual(plain.get(1), out);
            push_individual(plain.get(2), out);
        }
        "DataPropertyAtom" => push_individual(plain.get(1), out),
        "SameIndividualAtom" | "DifferentIndividualsAtom" => {
            push_individual(plain.first(), out);
            push_individual(plain.get(1), out);
        }
        "BuiltInAtom" | "DataRangeAtom" => {}
        _ => {
            for arg in &plain {
                individuals_in(arg, out);
            }
        }
    }
}

/// The `Prefix(p:=<ns>)` bindings of an OFN document.
pub(super) fn prefix_bindings(text: &str) -> Result<BTreeMap<String, String>, OrchestrateError> {
    let mut parser = sexpr::Parser::new(text);
    let mut prefixes = BTreeMap::new();
    while parser.peek() == Some("Prefix") {
        let node = parser.parse().map_err(OrchestrateError::InvalidOntology)?;
        let Node::List(_, args) = node else { break };
        let parts: Option<Vec<&str>> = args.iter().map(Node::as_atom).collect();
        let Some(definition) = parts.map(|p| p.concat()) else { continue };
        if let Some((prefix, value)) = definition.split_once(":=") {
            if let Some(iri) = value.strip_prefix('<').and_then(|v| v.strip_suffix('>')) {
                prefixes.insert(prefix.to_string(), iri.to_string());
            }
        }
    }
    Ok(prefixes)
}

/// The source after the classifier's own spelling canonicalization
/// (`builtin_aliases::canonicalize`, which rewrites a prefixed name to the
/// full IRI wherever one entity has more than one spelling), and its named
/// individuals, one per IRI, in the spelling the classification uses.
///
/// Probes are written in that canonical spelling, so the extended document
/// canonicalizes to itself and each probe names exactly the entity the
/// classifier sees. After canonicalization every IRI has one spelling; the
/// check below declines, rather than report one individual under two
/// names, should that invariant ever fail.
pub(super) fn canonical_individuals(text: &str) -> Result<(String, Vec<String>), OrchestrateError> {
    let canonical = canonical_source(text)?;
    let individuals = source_individuals(&canonical)?;
    check_one_spelling(&canonical, &individuals, "realization: individual")?;
    Ok((canonical, individuals))
}

/// The source after `builtin_aliases::canonicalize`.
pub(super) fn canonical_source(text: &str) -> Result<String, OrchestrateError> {
    Ok(crate::frontend::builtin_aliases::canonicalize(text)
        .map_err(OrchestrateError::from_conformance)?
        .into_owned())
}

/// Decline, rather than report one entity under two names, if two tokens of
/// the canonical source `canonical` expand to the same IRI.
pub(super) fn check_one_spelling(canonical: &str, tokens: &[String], what: &str) -> Result<(), OrchestrateError> {
    let prefixes = prefix_bindings(canonical)?;
    let expand = |token: &str| -> String {
        if let Some(iri) = token.strip_prefix('<').and_then(|t| t.strip_suffix('>')) {
            return iri.to_string();
        }
        token
            .split_once(':')
            .and_then(|(prefix, local)| prefixes.get(prefix).map(|ns| format!("{ns}{local}")))
            .unwrap_or_else(|| token.to_string())
    };
    let mut spelling_of: BTreeMap<String, &str> = BTreeMap::new();
    for token in tokens {
        if let Some(other) = spelling_of.insert(expand(token), token) {
            return Err(OrchestrateError::OutOfFragment(format!(
                "{what} {} is spelled both {other} and {token}",
                expand(token)
            )));
        }
    }
    Ok(())
}

/// The public name of a source token, as the classification output spells
/// class names: the IRI without its angle brackets, otherwise the token.
pub(super) fn public_name(token: &str) -> String {
    let raw = token
        .strip_prefix('<')
        .and_then(|inner| inner.strip_suffix('>'))
        .unwrap_or(token);
    crate::frontend::lenient::unescape_iri(raw).into_owned()
}

/// Byte offset of the `)` that closes the document's `Ontology(` node.
fn ontology_close_offset(text: &str) -> Option<usize> {
    let mut depth = 0usize;
    let mut previous: Option<&str> = None;
    let mut inside = false;
    for token in sexpr::tokens(text) {
        match token {
            "(" => {
                if depth == 0 && previous == Some("Ontology") {
                    inside = true;
                }
                depth += 1;
            }
            ")" => {
                depth = depth.checked_sub(1)?;
                if depth == 0 && inside {
                    return Some(token.as_ptr() as usize - text.as_ptr() as usize);
                }
            }
            _ => {}
        }
        previous = Some(token);
    }
    None
}

/// A probe-class namespace whose IRIs do not occur in `text`.
fn fresh_namespace(text: &str) -> String {
    fresh_namespace_for(text, "realize")
}

/// A namespace `http://km.invalid/<base>[N]#` whose IRIs do not occur in `text`.
pub(super) fn fresh_namespace_for(text: &str, base: &str) -> String {
    let mut namespace = format!("http://km.invalid/{base}#");
    let mut nonce = 0u64;
    while text.contains(namespace.trim_end_matches('#')) {
        nonce += 1;
        namespace = format!("http://km.invalid/{base}{nonce}#");
    }
    namespace
}

/// The source extended with one probe class `P ≡ {a}` per named individual,
/// and the probe IRI (as the output spells it) for each individual's public
/// name.
#[cfg(test)]
fn probe_source(text: &str, individuals: &[String]) -> Result<(String, Vec<(String, String)>), OrchestrateError> {
    let (extension, probes) = individual_extension(text, individuals);
    Ok((insert_extension(text, &extension)?, probes))
}

/// The probe axioms `P ≡ {a}`, one per named individual, and the probe IRI
/// (as the output spells it) for each individual's public name.
fn individual_extension(text: &str, individuals: &[String]) -> (String, Vec<(String, String)>) {
    let namespace = fresh_namespace(text);
    let mut extension = String::with_capacity(individuals.len() * 128 + 2);
    let mut probes = Vec::with_capacity(individuals.len());
    extension.push('\n');
    for (index, token) in individuals.iter().enumerate() {
        let probe = format!("{namespace}individual{index}");
        extension.push_str(&format!(
            "Declaration(Class(<{probe}>))\nEquivalentClasses(<{probe}> ObjectOneOf({token}))\n"
        ));
        probes.push((probe, public_name(token)));
    }
    (extension, probes)
}

struct NominalFreeIndividualProbes {
    extension: String,
    probes: Vec<(String, String)>,
    precomputed_same: Vec<[String; 2]>,
    /// Which argument applies: `false` for case A, `true` for case B.
    #[cfg_attr(not(test), allow(dead_code))]
    case_b: bool,
}

const OWL_NS: &str = "http://www.w3.org/2002/07/owl#";

fn is_top_class_token(token: &str) -> bool {
    matches!(token, "owl:Thing" | "<http://www.w3.org/2002/07/owl#Thing>")
}

/// What an OFN token names when it lies in the OWL namespace.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum OwlToken {
    NotOwl,
    Thing,
    Nothing,
    TopObjectProperty,
    TopDataProperty,
    /// Any other `owl:` name (bottom properties, `owl:real`, ...).
    Other,
}

fn plain_args<'n, 'a>(args: &'n [Node<'a>]) -> Vec<&'n Node<'a>> {
    args.iter()
        .filter(|arg| arg.head() != Some("Annotation"))
        .collect()
}

fn render_node_into(node: &Node<'_>, out: &mut String) {
    match node {
        Node::Atom(token) => out.push_str(token),
        Node::List(head, args) => {
            out.push_str(head);
            out.push('(');
            let mut first = true;
            for arg in args {
                if arg.head() == Some("Annotation") {
                    continue;
                }
                if !first {
                    out.push(' ');
                }
                first = false;
                render_node_into(arg, out);
            }
            out.push(')');
        }
    }
}

fn render_node(node: &Node<'_>) -> String {
    let mut out = String::new();
    render_node_into(node, &mut out);
    out
}

/// One pass over the source for [`nominal_free_individual_extension`].
///
/// The scan accepts an explicit list of axiom and class-expression kinds and
/// declines (returns `false` from [`NominalFreeScan::axiom`]) on everything
/// else. `docs/V1.7.0-SPEED.md` section 4(c) lists every OWL 2 kind with the
/// treatment it gets here and the argument for it.
struct NominalFreeScan<'a> {
    prefixes: BTreeMap<String, String>,
    /// Object properties that some axiom other than an
    /// `ObjectPropertyAssertion`, the outer role of a
    /// `ClassAssertion(ObjectSomeValuesFrom(r F) x)`, or a tautology
    /// `SubObjectPropertyOf(R owl:topObjectProperty)` mentions. A property
    /// outside this set is *free*: no axiom constrains it except its own
    /// assertions.
    mentioned: HashSet<&'a str>,
    /// Every axiom seen so far lies in the Horn fragment of case B (EL class
    /// expressions, named properties, no data class expressions, no
    /// functionality, symmetry, inverses, reflexivity or disjunction).
    horn: bool,
    /// Named properties under an existential in a premise position
    /// (the left side of `SubClassOf`, any side of `EquivalentClasses` and
    /// `DisjointClasses`) and properties with a domain axiom.
    premise_roles: HashSet<&'a str>,
    sub_roles: HashMap<&'a str, Vec<&'a str>>,
    /// `SubObjectPropertyOf(ObjectPropertyChain(links) sup)`; a transitive
    /// property `t` is recorded as the chain `t t -> t`.
    chains: Vec<(Vec<&'a str>, &'a str)>,
    /// Range class expressions of named properties, rendered.
    ranges: HashMap<&'a str, Vec<String>>,
    /// `(individual token, rendered class, outer role of an existential)`.
    class_assertions: Vec<(&'a str, String, Option<&'a str>)>,
    /// `(role, subject, object)`, with `ObjectInverseOf` assertions flipped.
    role_assertions: Vec<(&'a str, &'a str, &'a str)>,
    same_groups: Vec<Vec<&'a str>>,
    diff_groups: Vec<Vec<&'a str>>,
    /// The first axiom kind that made the scan decline, for `KM_REALIZE_TRACE`.
    declined_at: Option<String>,
}

impl<'a> NominalFreeScan<'a> {
    fn owl_token(&self, token: &str) -> OwlToken {
        let local: String = if let Some(inner) = token.strip_prefix('<').and_then(|t| t.strip_suffix('>')) {
            match inner.strip_prefix(OWL_NS) {
                Some(local) => local.to_string(),
                None => return OwlToken::NotOwl,
            }
        } else if let Some((prefix, local)) = token.split_once(':') {
            let ns = match self.prefixes.get(prefix) {
                Some(ns) => ns.as_str(),
                None if prefix == "owl" => OWL_NS,
                None => return OwlToken::NotOwl,
            };
            let full = format!("{ns}{local}");
            match full.strip_prefix(OWL_NS) {
                Some(local) => local.to_string(),
                None => return OwlToken::NotOwl,
            }
        } else {
            return OwlToken::NotOwl;
        };
        match local.as_str() {
            "Thing" => OwlToken::Thing,
            "Nothing" => OwlToken::Nothing,
            "topObjectProperty" => OwlToken::TopObjectProperty,
            "topDataProperty" => OwlToken::TopDataProperty,
            _ => OwlToken::Other,
        }
    }

    /// A token that names an ordinary (non-OWL, non-literal, non-anonymous)
    /// entity.
    fn plain_entity(&self, token: &str) -> bool {
        !token.is_empty()
            && !token.starts_with('"')
            && !token.starts_with("_:")
            && !token.starts_with('^')
            && !token.starts_with('@')
            && self.owl_token(token) == OwlToken::NotOwl
    }

    /// The shape of an object property expression without recording it:
    /// `(name, inverse)`.
    fn role_shape(&self, node: &Node<'a>) -> Option<(&'a str, bool)> {
        let (token, inverse) = match node {
            Node::Atom(token) => (*token, false),
            Node::List("ObjectInverseOf", args) => {
                let plain = plain_args(args);
                if plain.len() != 1 {
                    return None;
                }
                (plain[0].as_atom()?, true)
            }
            _ => return None,
        };
        self.plain_entity(token).then_some((token, inverse))
    }

    /// An object property expression in a constraining position: recorded as
    /// mentioned; an inverse leaves the Horn fragment.
    fn object_role(&mut self, node: &Node<'a>) -> Option<(&'a str, bool)> {
        let (token, inverse) = self.role_shape(node)?;
        if inverse {
            self.horn = false;
        }
        self.mentioned.insert(token);
        Some((token, inverse))
    }

    fn data_role(&self, node: &Node<'a>) -> bool {
        node.as_atom().is_some_and(|token| self.plain_entity(token))
    }

    /// A data range. Data ranges never mention individuals or object
    /// properties; any datatype, facet or literal token is accepted.
    fn data_range(node: &Node<'a>) -> bool {
        match node {
            Node::Atom(token) => !token.starts_with("_:"),
            Node::List(head, args) => {
                matches!(
                    *head,
                    "DataIntersectionOf"
                        | "DataUnionOf"
                        | "DataComplementOf"
                        | "DataOneOf"
                        | "DatatypeRestriction"
                ) && plain_args(args).into_iter().all(Self::data_range)
            }
        }
    }

    fn cardinality(node: &Node<'_>) -> bool {
        node.as_atom().is_some_and(|token| token.parse::<u64>().is_ok())
    }

    /// A class expression. `premise`: the expression sits where an
    /// existential matches an existing edge (left side of an inclusion).
    fn class(&mut self, node: &Node<'a>, premise: bool) -> bool {
        match node {
            Node::Atom(token) => {
                if token.starts_with('"') || token.starts_with("_:") {
                    return false;
                }
                matches!(
                    self.owl_token(token),
                    OwlToken::NotOwl | OwlToken::Thing | OwlToken::Nothing
                )
            }
            Node::List(head, args) => {
                let plain = plain_args(args);
                match *head {
                    "ObjectIntersectionOf" => {
                        !plain.is_empty() && plain.iter().all(|arg| self.class(arg, premise))
                    }
                    "ObjectUnionOf" => {
                        self.horn = false;
                        !plain.is_empty() && plain.iter().all(|arg| self.class(arg, premise))
                    }
                    "ObjectComplementOf" => {
                        self.horn = false;
                        plain.len() == 1 && self.class(plain[0], !premise)
                    }
                    "ObjectSomeValuesFrom" => {
                        if plain.len() != 2 {
                            return false;
                        }
                        let Some((role, inverse)) = self.object_role(plain[0]) else {
                            return false;
                        };
                        if premise && !inverse {
                            self.premise_roles.insert(role);
                        }
                        self.class(plain[1], premise)
                    }
                    "ObjectAllValuesFrom" => {
                        self.horn = false;
                        plain.len() == 2
                            && self.object_role(plain[0]).is_some()
                            && self.class(plain[1], premise)
                    }
                    "ObjectMinCardinality" | "ObjectMaxCardinality" | "ObjectExactCardinality" => {
                        self.horn = false;
                        (plain.len() == 2 || plain.len() == 3)
                            && Self::cardinality(plain[0])
                            && self.object_role(plain[1]).is_some()
                            && (plain.len() == 2 || self.class(plain[2], premise))
                    }
                    "ObjectHasSelf" => {
                        self.horn = false;
                        plain.len() == 1 && self.object_role(plain[0]).is_some()
                    }
                    "DataSomeValuesFrom" | "DataAllValuesFrom" => {
                        self.horn = false;
                        plain.len() >= 2
                            && plain[..plain.len() - 1].iter().all(|p| self.data_role(p))
                            && Self::data_range(plain[plain.len() - 1])
                    }
                    "DataHasValue" => {
                        self.horn = false;
                        plain.len() >= 2
                            && self.data_role(plain[0])
                            && plain[1..].iter().all(|arg| arg.as_atom().is_some())
                    }
                    "DataMinCardinality" | "DataMaxCardinality" | "DataExactCardinality" => {
                        self.horn = false;
                        (plain.len() == 2 || plain.len() == 3)
                            && Self::cardinality(plain[0])
                            && self.data_role(plain[1])
                            && (plain.len() == 2 || Self::data_range(plain[2]))
                    }
                    // ObjectOneOf, ObjectHasValue and every unknown kind.
                    _ => false,
                }
            }
        }
    }

    fn individual(token: &str) -> bool {
        !token.is_empty() && !token.starts_with('"') && !token.starts_with('^') && !token.starts_with('@')
    }

    /// One ontology child. `false` means decline.
    fn axiom(&mut self, node: &Node<'a>) -> bool {
        // The ontology and version IRIs are bare atoms.
        let Node::List(head, args) = node else { return true };
        let plain = plain_args(args);
        match *head {
            "Annotation"
            | "AnnotationAssertion"
            | "SubAnnotationPropertyOf"
            | "AnnotationPropertyDomain"
            | "AnnotationPropertyRange"
            | "Declaration" => true,
            "SubClassOf" => {
                plain.len() == 2 && self.class(plain[0], true) && self.class(plain[1], false)
            }
            "EquivalentClasses" | "DisjointClasses" => {
                plain.len() >= 2 && plain.iter().all(|c| self.class(c, true))
            }
            "DisjointUnion" => {
                self.horn = false;
                plain.len() >= 2 && plain.iter().all(|c| self.class(c, true))
            }
            "SubObjectPropertyOf" => {
                if plain.len() != 2 {
                    return false;
                }
                if plain[1]
                    .as_atom()
                    .is_some_and(|sup| self.owl_token(sup) == OwlToken::TopObjectProperty)
                {
                    // `R ⊑ U` and `R1 ... Rn ⊑ U` hold in every interpretation.
                    return match plain[0] {
                        Node::List("ObjectPropertyChain", links) => {
                            let links = plain_args(links);
                            !links.is_empty() && links.iter().all(|l| self.role_shape(l).is_some())
                        }
                        sub => self.role_shape(sub).is_some(),
                    };
                }
                let Some((sup, sup_inverse)) = self.object_role(plain[1]) else {
                    return false;
                };
                match plain[0] {
                    Node::List("ObjectPropertyChain", links) => {
                        let links = plain_args(links);
                        if links.is_empty() {
                            return false;
                        }
                        let mut named = Vec::with_capacity(links.len());
                        for link in links {
                            match self.object_role(link) {
                                Some((role, false)) => named.push(role),
                                Some((_, true)) => {}
                                None => return false,
                            }
                        }
                        if !sup_inverse && self.horn {
                            self.chains.push((named, sup));
                        }
                        true
                    }
                    sub => match self.object_role(sub) {
                        Some((role, false)) => {
                            if !sup_inverse {
                                self.sub_roles.entry(role).or_default().push(sup);
                            }
                            true
                        }
                        Some((_, true)) => true,
                        None => false,
                    },
                }
            }
            "EquivalentObjectProperties" => {
                let mut named = Vec::with_capacity(plain.len());
                for arg in &plain {
                    match self.object_role(arg) {
                        Some((role, false)) => named.push(role),
                        Some((_, true)) => {}
                        None => return false,
                    }
                }
                for &a in &named {
                    for &b in &named {
                        if a != b {
                            self.sub_roles.entry(a).or_default().push(b);
                        }
                    }
                }
                plain.len() >= 2
            }
            "DisjointObjectProperties" => {
                plain.len() >= 2 && plain.iter().all(|r| self.object_role(r).is_some())
            }
            "InverseObjectProperties" => {
                self.horn = false;
                plain.len() == 2 && plain.iter().all(|r| self.object_role(r).is_some())
            }
            "ObjectPropertyDomain" => {
                if plain.len() != 2 {
                    return false;
                }
                let Some((role, inverse)) = self.object_role(plain[0]) else {
                    return false;
                };
                if !inverse {
                    self.premise_roles.insert(role);
                }
                self.class(plain[1], false)
            }
            "ObjectPropertyRange" => {
                if plain.len() != 2 {
                    return false;
                }
                let Some((role, inverse)) = self.object_role(plain[0]) else {
                    return false;
                };
                if !self.class(plain[1], false) {
                    return false;
                }
                let is_top = plain[1]
                    .as_atom()
                    .is_some_and(|c| self.owl_token(c) == OwlToken::Thing);
                if !inverse && !is_top {
                    self.ranges.entry(role).or_default().push(render_node(plain[1]));
                }
                true
            }
            "FunctionalObjectProperty"
            | "InverseFunctionalObjectProperty"
            | "ReflexiveObjectProperty"
            | "SymmetricObjectProperty" => {
                self.horn = false;
                plain.len() == 1 && self.object_role(plain[0]).is_some()
            }
            "IrreflexiveObjectProperty" | "AsymmetricObjectProperty" => {
                plain.len() == 1 && self.object_role(plain[0]).is_some()
            }
            "TransitiveObjectProperty" => {
                if plain.len() != 1 {
                    return false;
                }
                match self.object_role(plain[0]) {
                    Some((role, false)) => {
                        self.chains.push((vec![role, role], role));
                        true
                    }
                    Some((_, true)) => true,
                    None => false,
                }
            }
            "SubDataPropertyOf" => {
                plain.len() == 2
                    && self.data_role(plain[0])
                    && (self.data_role(plain[1])
                        || plain[1]
                            .as_atom()
                            .is_some_and(|t| self.owl_token(t) == OwlToken::TopDataProperty))
            }
            "EquivalentDataProperties" | "DisjointDataProperties" => {
                plain.len() >= 2 && plain.iter().all(|p| self.data_role(p))
            }
            "FunctionalDataProperty" => plain.len() == 1 && self.data_role(plain[0]),
            "DataPropertyDomain" => {
                plain.len() == 2 && self.data_role(plain[0]) && self.class(plain[1], false)
            }
            "DataPropertyRange" => {
                plain.len() == 2 && self.data_role(plain[0]) && Self::data_range(plain[1])
            }
            "DatatypeDefinition" => {
                plain.len() == 2 && plain[0].as_atom().is_some() && Self::data_range(plain[1])
            }
            "ClassAssertion" => {
                if plain.len() != 2 {
                    return false;
                }
                let Some(ind) = plain[1].as_atom().filter(|t| Self::individual(t)) else {
                    return false;
                };
                if let Node::List("ObjectSomeValuesFrom", ex) = plain[0] {
                    let ex = plain_args(ex);
                    if ex.len() == 2 {
                        if let Some((role, false)) = self.role_shape(ex[0]) {
                            // The outer role is not recorded as mentioned.
                            if !self.class(ex[1], false) {
                                return false;
                            }
                            self.class_assertions.push((ind, render_node(plain[0]), Some(role)));
                            return true;
                        }
                    }
                }
                if !self.class(plain[0], false) {
                    return false;
                }
                self.class_assertions.push((ind, render_node(plain[0]), None));
                true
            }
            "ObjectPropertyAssertion" => {
                if plain.len() != 3 {
                    return false;
                }
                let Some((role, inverse)) = self.role_shape(plain[0]) else {
                    return false;
                };
                let (Some(s), Some(o)) = (
                    plain[1].as_atom().filter(|t| Self::individual(t)),
                    plain[2].as_atom().filter(|t| Self::individual(t)),
                ) else {
                    return false;
                };
                if inverse {
                    self.role_assertions.push((role, o, s));
                } else {
                    self.role_assertions.push((role, s, o));
                }
                true
            }
            "SameIndividual" | "DifferentIndividuals" => {
                let mut group = Vec::with_capacity(plain.len());
                for arg in &plain {
                    match arg.as_atom().filter(|t| Self::individual(t)) {
                        Some(token) => group.push(token),
                        None => return false,
                    }
                }
                if *head == "SameIndividual" {
                    self.same_groups.push(group);
                } else {
                    self.diff_groups.push(group);
                }
                true
            }
            // Import, HasKey, DLSafeRule, NegativeObjectPropertyAssertion,
            // NegativeDataPropertyAssertion, DataPropertyAssertion and every
            // unknown kind.
            _ => false,
        }
    }
}

fn super_roles<'a>(role: &'a str, sub_roles: &HashMap<&'a str, Vec<&'a str>>) -> HashSet<&'a str> {
    let mut out = HashSet::new();
    let mut stack = vec![role];
    while let Some(r) = stack.pop() {
        if out.insert(r) {
            if let Some(sups) = sub_roles.get(r) {
                stack.extend(sups.iter().copied());
            }
        }
    }
    out
}

fn nominal_free_trace(message: &str) {
    if std::env::var_os("KM_REALIZE_TRACE").is_some() {
        eprintln!("km: nominal-free realization: {message}");
    }
}

/// Block probes for realization without one nominal `P_a ≡ {a}` per named
/// individual, or `None` when no exactness argument covers the ontology.
///
/// Case A (any nominal-free OWL 2 DL TBox): every `ObjectPropertyAssertion`
/// uses a *free* property (one no other axiom mentions). Then
/// `O ⊨ C(a)` iff `T ⊨ ⊓S(a) ⊑ C`, where `S(a)` are the class assertions of
/// `a`'s `SameIndividual` group, so one probe `P ⊑ ⊓S` per distinct `S`
/// gives the types of all individuals with that `S`.
///
/// Case B (Horn EL TBox with role inclusions, chains, transitivity,
/// domains and ranges): the ABox graph is quotiented by the coarsest forward
/// bisimulation over its labels and over the edges of *relevant* properties;
/// each block gets `P_b ⊑ label` and `P_b ⊑ ∃r.P_b'` per edge.
///
/// The arguments and the treatment of every OWL 2 kind are in
/// `docs/V1.7.0-SPEED.md` section 4(c).
fn nominal_free_individual_extension<'a>(
    text: &'a str,
    individuals: &[String],
) -> Option<NominalFreeIndividualProbes> {
    if individuals.is_empty() || std::env::var_os("KM_NO_NOMINAL_FREE_REALIZE").is_some() {
        return None;
    }
    let mut scan = NominalFreeScan {
        prefixes: prefix_bindings(text).ok()?,
        mentioned: HashSet::new(),
        horn: true,
        premise_roles: HashSet::new(),
        sub_roles: HashMap::new(),
        chains: Vec::new(),
        ranges: HashMap::new(),
        class_assertions: Vec::new(),
        role_assertions: Vec::new(),
        same_groups: Vec::new(),
        diff_groups: Vec::new(),
        declined_at: None,
    };
    let walked = crate::frontend::parse::for_each_ontology_child(text, |node| {
        if scan.declined_at.is_none() && !scan.axiom(node) {
            scan.declined_at = Some(node.head().unwrap_or("?").to_string());
        }
        Ok(())
    });
    if walked.is_err() {
        nominal_free_trace("declined: parse error");
        return None;
    }
    if let Some(kind) = &scan.declined_at {
        nominal_free_trace(&format!("declined: unsupported {kind}"));
        return None;
    }

    // `SameIndividual` groups by union-find over the named individuals.
    let ind_index: HashMap<&str, usize> = individuals
        .iter()
        .enumerate()
        .map(|(idx, tok)| (tok.as_str(), idx))
        .collect();
    let mut parent: Vec<usize> = (0..individuals.len()).collect();
    fn find(parent: &mut [usize], mut x: usize) -> usize {
        let mut root = x;
        while parent[root] != root {
            root = parent[root];
        }
        while parent[x] != root {
            let next = parent[x];
            parent[x] = root;
            x = next;
        }
        root
    }
    for group in &scan.same_groups {
        let mut members = Vec::with_capacity(group.len());
        for token in group {
            let Some(&idx) = ind_index.get(token) else {
                nominal_free_trace("declined: SameIndividual on an unnamed individual");
                return None;
            };
            members.push(idx);
        }
        for pair in members.windows(2) {
            let (a, b) = (find(&mut parent, pair[0]), find(&mut parent, pair[1]));
            if a != b {
                parent[a.max(b)] = a.min(b);
            }
        }
    }
    for group in &scan.diff_groups {
        let mut roots = HashSet::with_capacity(group.len());
        for token in group {
            let Some(&idx) = ind_index.get(token) else {
                nominal_free_trace("declined: DifferentIndividuals on an unnamed individual");
                return None;
            };
            if !roots.insert(find(&mut parent, idx)) {
                // An asserted equality contradicts an asserted difference.
                nominal_free_trace("declined: SameIndividual meets DifferentIndividuals");
                return None;
            }
        }
    }
    let mut comp_of = vec![usize::MAX; individuals.len()];
    let mut comp_members: Vec<Vec<usize>> = Vec::new();
    for i in 0..individuals.len() {
        let root = find(&mut parent, i);
        if comp_of[root] == usize::MAX {
            comp_of[root] = comp_members.len();
            comp_members.push(Vec::new());
        }
        let comp = comp_of[root];
        comp_of[i] = comp;
        comp_members[comp].push(i);
    }
    let n_comps = comp_members.len();

    let mut precomputed_same: BTreeSet<[String; 2]> = BTreeSet::new();
    for members in &comp_members {
        if members.len() < 2 {
            continue;
        }
        let names: Vec<String> = members.iter().map(|&i| public_name(&individuals[i])).collect();
        for i in 0..names.len() {
            for j in (i + 1)..names.len() {
                if names[i] != names[j] {
                    let (low, high) = if names[i] < names[j] { (i, j) } else { (j, i) };
                    precomputed_same.insert([names[low].clone(), names[high].clone()]);
                }
            }
        }
    }
    let precomputed_same: Vec<[String; 2]> = precomputed_same.into_iter().collect();

    let free = |role: &str| !scan.mentioned.contains(role);
    let active: Vec<(&str, &str, &str)> = scan
        .role_assertions
        .iter()
        .copied()
        .filter(|&(role, _, _)| !free(role))
        .collect();

    // Class labels of each group. `owl:Thing` is dropped, and so is an
    // existential `∃r.F` over a free property `r` (argued in the docs).
    let is_thing = |rendered: &str| {
        is_top_class_token(rendered)
            || (!rendered.contains('(') && scan.owl_token(rendered) == OwlToken::Thing)
    };
    let mut labels: Vec<Vec<String>> = vec![Vec::new(); n_comps];
    let mut unnamed_assertion = false;
    for (ind, rendered, outer) in &scan.class_assertions {
        let Some(&idx) = ind_index.get(ind) else {
            unnamed_assertion = true;
            continue;
        };
        if is_thing(rendered) || outer.is_some_and(|role| free(role)) {
            continue;
        }
        labels[comp_of[idx]].push(rendered.clone());
    }

    let namespace = fresh_namespace(text);
    if active.is_empty() {
        // Case A.
        for set in &mut labels {
            set.sort_unstable();
            set.dedup();
        }
        let mut probe_of_labels: HashMap<&[String], usize> = HashMap::new();
        let mut ordered: Vec<usize> = Vec::new();
        let mut comp_probe = vec![0usize; n_comps];
        for comp in 0..n_comps {
            let next = ordered.len();
            let id = *probe_of_labels.entry(labels[comp].as_slice()).or_insert_with(|| {
                ordered.push(comp);
                next
            });
            comp_probe[comp] = id;
        }
        let mut probes = Vec::with_capacity(individuals.len());
        for (comp, members) in comp_members.iter().enumerate() {
            let probe = format!("{namespace}individual{}", comp_probe[comp]);
            for &idx in members {
                probes.push((probe.clone(), public_name(&individuals[idx])));
            }
        }
        let mut extension = String::with_capacity(ordered.len() * 128 + 2);
        extension.push('\n');
        for (id, &comp) in ordered.iter().enumerate() {
            let probe = format!("{namespace}individual{id}");
            extension.push_str(&format!("Declaration(Class(<{probe}>))\n"));
            if labels[comp].is_empty() {
                extension.push_str(&format!("SubClassOf(<{probe}> owl:Thing)\n"));
            }
            for class in &labels[comp] {
                extension.push_str(&format!("SubClassOf(<{probe}> {class})\n"));
            }
        }
        nominal_free_trace(&format!(
            "case A: {} individuals, {} groups, {} probes",
            individuals.len(),
            n_comps,
            ordered.len()
        ));
        return Some(NominalFreeIndividualProbes { extension, probes, precomputed_same, case_b: false });
    }

    // Case B.
    if !scan.horn {
        nominal_free_trace("declined: a constrained property assertion outside the Horn EL fragment");
        return None;
    }
    if unnamed_assertion {
        nominal_free_trace("declined: case B with an assertion on an unnamed individual");
        return None;
    }
    // Reflexive-transitive super-properties, memoized per property.
    let mut supers_memo: HashMap<&'a str, std::rc::Rc<HashSet<&'a str>>> = HashMap::new();
    let mut supers_of = |role: &'a str| -> std::rc::Rc<HashSet<&'a str>> {
        supers_memo
            .entry(role)
            .or_insert_with(|| std::rc::Rc::new(super_roles(role, &scan.sub_roles)))
            .clone()
    };

    // A range of a super-property of a chain must also be a range of a
    // super-property of the chain's last link, or the range labels below miss
    // chain-derived edges (the OWL 2 EL restriction on ranges and chains).
    for (links, sup) in &scan.chains {
        let last = supers_of(links[links.len() - 1]);
        for &q in supers_of(sup).iter() {
            if scan.ranges.contains_key(q) && !last.contains(q) {
                nominal_free_trace("declined: a range on a property chain's super-property");
                return None;
            }
        }
    }

    // Relevant properties: those with a super-property in a premise position,
    // closed under the links of chains whose super-property is relevant.
    let mut premise: HashSet<&str> = scan.premise_roles.clone();
    loop {
        let mut grew = false;
        for (links, sup) in &scan.chains {
            let relevant = supers_of(sup).iter().any(|q| premise.contains(q));
            if relevant {
                for &link in links {
                    grew |= premise.insert(link);
                }
            }
        }
        if !grew {
            break;
        }
    }

    let mut relevant_memo: HashMap<&str, bool> = HashMap::new();
    let mut edges: Vec<Vec<(&str, usize)>> = vec![Vec::new(); n_comps];
    for &(role, s, o) in &active {
        let (Some(&si), Some(&oi)) = (ind_index.get(s), ind_index.get(o)) else {
            nominal_free_trace("declined: case B with a property assertion on an unnamed individual");
            return None;
        };
        let (u, v) = (comp_of[si], comp_of[oi]);
        let sups = supers_of(role);
        for &q in sups.iter() {
            if let Some(range) = scan.ranges.get(q) {
                labels[v].extend(range.iter().cloned());
            }
        }
        let relevant = *relevant_memo
            .entry(role)
            .or_insert_with(|| sups.iter().any(|q| premise.contains(q)));
        if relevant {
            edges[u].push((role, v));
        }
    }
    for set in &mut labels {
        set.sort_unstable();
        set.dedup();
    }
    for out in &mut edges {
        out.sort_unstable();
        out.dedup();
    }

    // Coarsest partition that refines equal labels and is stable under
    // successors along relevant edges (forward bisimulation).
    let mut color = vec![0usize; n_comps];
    let mut n_colors;
    {
        let mut palette: HashMap<&[String], usize> = HashMap::new();
        for comp in 0..n_comps {
            let next = palette.len();
            color[comp] = *palette.entry(labels[comp].as_slice()).or_insert(next);
        }
        n_colors = palette.len();
    }
    let mut block_rep: Vec<usize> = Vec::new();
    let mut stable = false;
    for _round in 0..64 {
        let mut palette: HashMap<(usize, Vec<(&str, usize)>), usize> = HashMap::with_capacity(n_colors);
        let mut next_color = vec![0usize; n_comps];
        let mut reps = Vec::with_capacity(n_colors);
        for comp in 0..n_comps {
            let mut signature: Vec<(&str, usize)> =
                edges[comp].iter().map(|&(role, v)| (role, color[v])).collect();
            signature.sort_unstable();
            signature.dedup();
            let next = palette.len();
            next_color[comp] = match palette.entry((color[comp], signature)) {
                std::collections::hash_map::Entry::Occupied(e) => *e.get(),
                std::collections::hash_map::Entry::Vacant(e) => {
                    reps.push(comp);
                    *e.insert(next)
                }
            };
        }
        let grew = palette.len() != n_colors;
        n_colors = palette.len();
        color = next_color;
        block_rep = reps;
        if !grew {
            stable = true;
            break;
        }
    }
    if !stable {
        nominal_free_trace("declined: bisimulation refinement did not settle in 64 rounds");
        return None;
    }
    // Once stable, every member of a block has the same successor blocks as
    // the block's representative `block_rep[block]`.
    let mut probes = Vec::with_capacity(individuals.len());
    for (comp, members) in comp_members.iter().enumerate() {
        let probe = format!("{namespace}individual{}", color[comp]);
        for &idx in members {
            probes.push((probe.clone(), public_name(&individuals[idx])));
        }
    }
    let mut extension = String::with_capacity(n_colors * 160 + 2);
    extension.push('\n');
    for block in 0..n_colors {
        extension.push_str(&format!("Declaration(Class(<{namespace}individual{block}>))\n"));
    }
    for block in 0..n_colors {
        let probe = format!("{namespace}individual{block}");
        let rep = block_rep[block];
        if labels[rep].is_empty() && edges[rep].is_empty() {
            extension.push_str(&format!("SubClassOf(<{probe}> owl:Thing)\n"));
        }
        for class in &labels[rep] {
            extension.push_str(&format!("SubClassOf(<{probe}> {class})\n"));
        }
        let mut targets: Vec<(&str, usize)> =
            edges[rep].iter().map(|&(role, v)| (role, color[v])).collect();
        targets.sort_unstable();
        targets.dedup();
        for (role, target) in targets {
            extension.push_str(&format!(
                "SubClassOf(<{probe}> ObjectSomeValuesFrom({role} <{namespace}individual{target}>))\n"
            ));
        }
    }
    nominal_free_trace(&format!(
        "case B: {} individuals, {} groups, {} blocks",
        individuals.len(),
        n_comps,
        n_colors
    ));
    Some(NominalFreeIndividualProbes { extension, probes, precomputed_same, case_b: true })
}

/// `text` with `extension` inserted before the `)` that closes its
/// `Ontology(` node.
pub(super) fn insert_extension(text: &str, extension: &str) -> Result<String, OrchestrateError> {
    let close = ontology_close_offset(text).ok_or_else(|| {
        OrchestrateError::InvalidOntology("probe extension: no complete Ontology(...) node".into())
    })?;
    let mut extended = String::with_capacity(text.len() + extension.len());
    extended.push_str(&text[..close]);
    extended.push_str(extension);
    extended.push_str(&text[close..]);
    Ok(extended)
}

/// Split the classification of the probe-extended ontology into the source
/// classification and its realization.
fn split(
    extended: Classification,
    probes: &[(String, String)],
    mode: TypeMode,
) -> Result<Realization, OrchestrateError> {
    split_with_options(extended, probes, mode, true, Vec::new())
}

fn split_with_options(
    mut extended: Classification,
    probes: &[(String, String)],
    mode: TypeMode,
    nominal_equality_probes: bool,
    precomputed_same: Vec<[String; 2]>,
) -> Result<Realization, OrchestrateError> {
    let mut individuals_of: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    for (probe, individual) in probes {
        individuals_of
            .entry(probe.as_str())
            .or_default()
            .push(individual.as_str());
    }
    let is_probe = |name: &str| individuals_of.contains_key(name);

    let mut probe_types: BTreeMap<&str, BTreeSet<String>> = BTreeMap::new();
    let mut same: BTreeSet<[String; 2]> = precomputed_same.into_iter().collect();
    let mut source_rows = Vec::with_capacity(extended.subsumptions.len());
    for [sub, sup] in std::mem::take(&mut extended.subsumptions) {
        match (
            individuals_of.get(sub.as_str()),
            individuals_of.get(sup.as_str()),
        ) {
            (None, None) => source_rows.push([sub, sup]),
            (Some(_), None) => {
                if sup != OWL_THING {
                    if let Some((&probe_key, _)) = individuals_of.get_key_value(sub.as_str()) {
                        probe_types.entry(probe_key).or_default().insert(sup);
                    }
                }
            }
            (Some(a_list), Some(b_list)) => {
                if nominal_equality_probes {
                    for &a in a_list {
                        for &b in b_list {
                            if a != b {
                                let (low, high) = if a < b { (a, b) } else { (b, a) };
                                same.insert([low.to_string(), high.to_string()]);
                            }
                        }
                    }
                }
            }
            // `C ⊑ {a}`: a fact about the source class, not about `a`.
            (None, Some(_)) => {}
        }
    }
    let unsatisfiable_probe = extended.unsatisfiable.iter().any(|name| is_probe(name));
    extended.unsatisfiable.retain(|name| !is_probe(name));
    extended.subsumptions = source_rows;
    if !extended.consistent {
        return Ok(Realization {
            classification: extended,
            types: Vec::new(),
            same: Vec::new(),
        });
    }
    // An unsatisfiable class is below every class, and its `UNSAT` row says
    // so. Which `SUB` rows a route also prints for it depends on the route
    // the probe-extended ontology takes, so the rows would depend on the
    // probe extension (docs/V1.7.0-SPEED.md 4(c3)). Print none.
    if !extended.unsatisfiable.is_empty() && std::env::var_os("KM_REALIZE_KEEP_UNSAT_SUB").is_none() {
        let unsat: HashSet<&str> = extended.unsatisfiable.iter().map(String::as_str).collect();
        let kept: Vec<[String; 2]> = std::mem::take(&mut extended.subsumptions)
            .into_iter()
            .filter(|[sub, _]| !unsat.contains(sub.as_str()))
            .collect();
        extended.subsumptions = kept;
    }
    if unsatisfiable_probe {
        // `{a}` is unsatisfiable only in an inconsistent ontology.
        return Err(OrchestrateError::InvalidOntology(
            "realization: a nominal probe is unsatisfiable in a consistent classification".into(),
        ));
    }

    if mode == TypeMode::Direct {
        let below: HashSet<(&str, &str)> = extended
            .subsumptions
            .iter()
            .map(|[sub, sup]| (sub.as_str(), sup.as_str()))
            .collect();
        let strictly_below = |d: &str, c: &str| below.contains(&(d, c)) && !below.contains(&(c, d));
        for classes in probe_types.values_mut() {
            let direct: BTreeSet<String> = classes
                .iter()
                .filter(|c| !classes.iter().any(|d| strictly_below(d, c)))
                .cloned()
                .collect();
            *classes = direct;
        }
    }
    let mut ind_to_probe: BTreeMap<&str, &str> = BTreeMap::new();
    for (probe, individual) in probes {
        ind_to_probe.insert(individual.as_str(), probe.as_str());
    }
    let mut types = Vec::new();
    for (individual, probe) in ind_to_probe {
        if let Some(classes) = probe_types.get(probe) {
            for c in classes {
                types.push([individual.to_string(), c.clone()]);
            }
        }
    }
    Ok(Realization {
        classification: extended,
        types,
        same: same.into_iter().collect(),
    })
}

/// Classify `ont` and realize its named individuals (see the module docs).
///
/// Like `km explain`, realization is answered only under the automatic route
/// policy. A manually forced route may lie outside the fragment it is exact
/// for; on the probe-extended ontology (which always contains nominals) several
/// non-nominal routes are incomplete. `KM_REALIZE_ANY_ROUTE=1` lifts this check
/// for route diagnostics only.
pub fn realize(cfg: &Config, ont: &Path, mode: TypeMode) -> Result<Realization, OrchestrateError> {
    Ok(classify_extended(cfg, ont, Some(mode), false, false, false, false, false)?.realization)
}

/// The classification of an ontology with the answers to the requested probe
/// queries: realization (`--realize`) and the object property hierarchy
/// (`--properties`, see [`super::properties`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Extended {
    /// The classification and, if requested, the realization. Without
    /// `--realize` its `types` and `same` are empty.
    pub realization: Realization,
    /// Present iff the property hierarchy was requested.
    pub properties: Option<super::properties::PropertyHierarchy>,
    /// Present iff `--data-properties` was requested: the data property rows
    /// (see [`super::data_properties`]).
    pub data_properties: Option<super::data_properties::DataPropertyHierarchy>,
    /// `--values` and `--different` rows (see [`super::abox_rows`]).
    pub abox: super::abox_rows::AboxRows,
    /// Present iff `--top` was requested: the named classes equivalent to
    /// `owl:Thing`, sorted.
    pub top: Option<Vec<String>>,
}

/// The `--top` probe: a fresh class `T ≡ owl:Thing`. A named class `C` is
/// equivalent to `owl:Thing` iff `O ⊨ ⊤ ⊑ C` iff `O' ⊨ T ⊑ C`; the
/// definition only names a fresh class, so the extension is conservative.
fn top_extension(text: &str) -> (String, String) {
    let probe = format!("{}thing", fresh_namespace_for(text, "top"));
    let axiom = if super::mirror::detect(text).ok().flatten().is_some() {
        format!("Declaration(Class(<{probe}>))\nSubClassOf(<{probe}> owl:Thing)\n")
    } else {
        format!("Declaration(Class(<{probe}>))\nEquivalentClasses(<{probe}> owl:Thing)\n")
    };
    (axiom, probe)
}

/// Remove the `--top` probe from the classification and return the named
/// classes it is subsumed by. `foreign` names the probe classes of the other
/// queries, which are not source classes.
fn split_top(
    extended: &mut Classification,
    probe: &str,
    foreign: &dyn Fn(&str) -> bool,
) -> Result<Vec<String>, OrchestrateError> {
    let mut top = BTreeSet::new();
    extended.subsumptions.retain(|[low, high]| {
        if low == probe {
            if high != OWL_THING && high != probe && !foreign(high) {
                top.insert(high.clone());
            }
            return false;
        }
        high != probe
    });
    let unsatisfiable = extended.unsatisfiable.iter().any(|name| name == probe);
    extended.unsatisfiable.retain(|name| name != probe);
    if !extended.consistent {
        return Ok(Vec::new());
    }
    if unsatisfiable {
        return Err(OrchestrateError::InvalidOntology(
            "top classes: the owl:Thing probe is unsatisfiable in a consistent classification".into(),
        ));
    }
    Ok(top.into_iter().collect())
}

/// Classify `ont` once, extended with the probe classes of every requested
/// query, and split the answer (see [`realize`] for the route policy, which
/// covers both queries: the property probes contain inverse roles and the
/// universal role, which several non-nominal routes do not handle exactly).
pub fn classify_extended(
    cfg: &Config,
    ont: &Path,
    mode: Option<TypeMode>,
    properties: bool,
    top: bool,
    data_properties: bool,
    values: bool,
    different: bool,
) -> Result<Extended, OrchestrateError> {
    let route = std::env::var("KM_ROUTE").unwrap_or_default();
    if route != crate::routing::Route::Auto.as_str()
        && std::env::var_os(ANY_ROUTE_ENV).is_none()
    {
        let what = if mode.is_some() {
            "realization"
        } else if properties {
            "property hierarchy"
        } else {
            "top class"
        };
        return Err(OrchestrateError::OutOfFragment(format!(
            "route {route:?} is not a {what}-safe production oracle; use auto"
        )));
    }
    super::validate_user_input(ont)?;
    let prepared = super::input::prepare(ont)?;
    let text = std::fs::read_to_string(prepared.path())?;
    let text = if crate::frontend::lenient::enabled() {
        let (rewritten, notes) = crate::frontend::lenient::rewrite_source(&text)
            .map_err(OrchestrateError::from_conformance)?;
        crate::frontend::lenient::record_published_notes(notes);
        rewritten.into_owned()
    } else {
        text
    };
    let (text, individuals) = if mode.is_some() || values || different {
        canonical_individuals(&text)?
    } else {
        (canonical_source(&text)?, Vec::new())
    };
    // `⊤ ⊑ {o}`: every individual equals `o`, so the rows of `o` are the rows
    // of every individual. Probing only `o` avoids one nominal probe per
    // individual (review/e10/found/hang_f808_194.ofn).
    let singleton = singleton_domain_individual(&text, &individuals);
    let (individuals, collapsed_names) = match singleton {
        Some(o) => {
            let names: Vec<String> = individuals.iter().map(|t| public_name(t)).collect();
            (vec![o.clone()], Some((public_name(&o), names)))
        }
        None => (individuals, None),
    };
    let roles = if properties || values {
        super::properties::canonical_properties(&text)?
    } else {
        Vec::new()
    };
    let mut shape = if roles.is_empty() {
        super::properties::SourceShape::default()
    } else {
        super::properties::source_shape(&text)?
    };
    if shape.universal_possible && super::properties::isolated_blank_element_admissible(&text) {
        shape.universal_possible = false;
    }
    let empty_properties = properties.then(super::properties::PropertyHierarchy::default);
    let data_roles = if data_properties {
        super::data_properties::canonical_data_properties(&text)?
    } else {
        Vec::new()
    };
    let empty_data = data_properties.then(super::data_properties::DataPropertyHierarchy::default);
    let empty_abox = super::abox_rows::AboxRows {
        values: values.then(Vec::new),
        different: different.then(Vec::new),
    };
    if individuals.is_empty() && (roles.is_empty() || !properties) && data_roles.is_empty() && !top {
        let classification = super::classify_with_evidence(cfg, ont)?.classification;
        let realization = Realization { classification, types: Vec::new(), same: Vec::new() };
        return Ok(Extended { realization, properties: empty_properties, data_properties: empty_data, abox: empty_abox, top: None });
    }
    let bound_disabled = crate::frontend::named_role_bound::NamedRoleBound::bound_disabled();
    let want_model_abox = (values || different)
        && !(bound_disabled && !different)
        && !individuals.is_empty()
        && (!values || !roles.is_empty() || different)
        && !text.contains("DLSafeRule(")
        && !text.contains("HasKey(")
        && std::env::var_os("KM_ABOX_PROBES_ONLY").is_none();
    let need_ind_probes = mode.is_some() || ((values || different) && !want_model_abox);
    let (mut extension, probes, nominal_equality_probes, precomputed_same) = if !need_ind_probes {
        (String::new(), Vec::new(), true, Vec::new())
    } else if !values && !different {
        if let Some(nf) = nominal_free_individual_extension(&text, &individuals) {
            (nf.extension, nf.probes, false, nf.precomputed_same)
        } else {
            let (ext, pr) = individual_extension(&text, &individuals);
            (ext, pr, true, Vec::new())
        }
    } else {
        let (ext, pr) = individual_extension(&text, &individuals);
        (ext, pr, true, Vec::new())
    };
    let top_probe = if top {
        let (top_axioms, probe) = top_extension(&text);
        extension.push_str(&top_axioms);
        Some(probe)
    } else {
        None
    };
    let separate_prop_run = need_ind_probes
        && properties
        && std::env::var_os("KM_COMBINED_PROP_PROBES").is_none();
    let property_probes = if roles.is_empty() || !properties {
        None
    } else if separate_prop_run {
        Some(super::properties::extension(&text, &roles, shape))
    } else {
        let (property_extension, property_probes) = super::properties::extension(&text, &roles, shape);
        extension.push_str(&property_extension);
        Some((String::new(), property_probes))
    };
    let separate_diff_run = values
        && different
        && !want_model_abox
        && !individuals.is_empty()
        && std::env::var_os("KM_COMBINED_ABOX_PROBES").is_none();
    let abox_probes = if (values || different) && !want_model_abox && !individuals.is_empty() {
        let (abox_extension, abox_probes) = super::abox_rows::extension(
            &text,
            &roles,
            &individuals,
            values,
            different && !separate_diff_run,
        );
        extension.push_str(&abox_extension);
        Some(abox_probes)
    } else {
        None
    };
    let separate_data_run = !data_roles.is_empty()
        && (need_ind_probes || property_probes.is_some() || want_model_abox)
        && std::env::var_os("KM_COMBINED_DATA_PROBES").is_none();
    let data_probes = if data_roles.is_empty() {
        None
    } else if separate_data_run {
        Some(super::data_properties::extension(&text, &data_roles))
    } else {
        let (data_extension, data_probes) = super::data_properties::extension(&text, &data_roles);
        extension.push_str(&data_extension);
        Some((String::new(), data_probes))
    };
    if std::env::var_os("KM_TIMING").is_some() {
        eprintln!(
            "KM_TIMING probes: {} individual, {} object property, {} data property",
            probes.len(),
            roles.len(),
            data_roles.len()
        );
    }
    let caller_export_active = std::env::var_os("KM_EXPORT_MODEL_ACTIVE").is_some();
    if want_model_abox && !caller_export_active {
        super::model_export::begin_session(None);
        std::env::set_var("KM_EXPORT_ABOX_ONLY", "1");
    }
    let _free = (!separate_data_run && data_probes.is_some()).then(FreeDatatypes::enable);
    let main_res = if extension.is_empty() {
        super::classify_with_evidence(cfg, ont).map(|ev| ev.classification)
    } else {
        classify_probe_source(cfg, &text, &extension, "-probes.ofn")
    };
    drop(_free);
    let exported_model = if want_model_abox {
        Some(super::model_export::resolve_session_model(!caller_export_active))
    } else {
        None
    };
    let mut classification = main_res?;
    let individual_probes: HashSet<&str> = probes.iter().map(|(probe, _)| probe.as_str()).collect();
    let top_classes = match &top_probe {
        Some(top_probe) => {
            let foreign = |name: &str| {
                individual_probes.contains(name)
                    || property_probes.as_ref().is_some_and(|(_, p)| p.is_probe(name))
                    || data_probes.as_ref().is_some_and(|(_, p)| p.is_probe(name))
                    || abox_probes.as_ref().is_some_and(|p| p.is_probe(name))
            };
            Some(split_top(&mut classification, top_probe, &foreign)?)
        }
        None => None,
    };
    let mut abox = match &abox_probes {
        Some(abox_probes) => {
            let individual_of: BTreeMap<String, String> = probes.iter().cloned().collect();
            let rows = super::abox_rows::split(&mut classification, abox_probes, &individual_of)?;
            if classification.consistent { rows } else { empty_abox.clone() }
        }
        None => empty_abox.clone(),
    };
    if separate_diff_run && classification.consistent {
        let (mut diff_ext, ind_probes) = individual_extension(&text, &individuals);
        let (ext_d, abox_pd) =
            super::abox_rows::extension(&text, &roles, &individuals, false, true);
        diff_ext.push_str(&ext_d);
        let mut diff_cls =
            classify_probe_source(cfg, &text, &diff_ext, "-abox-diff-probes.ofn")?;
        let individual_of: BTreeMap<String, String> = ind_probes.into_iter().collect();
        let diff_rows = super::abox_rows::split(&mut diff_cls, &abox_pd, &individual_of)?;
        if diff_cls.consistent {
            abox.different = diff_rows.different;
        }
    }
    let data_hierarchy = match data_probes {
        Some((data_ext, data_probes)) => {
            if separate_data_run {
                if !classification.consistent {
                    Some(super::data_properties::DataPropertyHierarchy::default())
                } else {
                    let _free = FreeDatatypes::enable();
                    let mut data_cls =
                        classify_probe_source(cfg, &text, &data_ext, "-data-probes.ofn")?;
                    drop(_free);
                    let foreign = |_: &str| false;
                    Some(super::data_properties::split(
                        &mut data_cls,
                        &data_probes,
                        &foreign,
                    )?)
                }
            } else {
                let foreign = |name: &str| {
                    individual_probes.contains(name)
                        || property_probes.as_ref().is_some_and(|(_, p)| p.is_probe(name))
                };
                Some(super::data_properties::split(
                    &mut classification,
                    &data_probes,
                    &foreign,
                )?)
            }
        }
        None => empty_data,
    };
    let hierarchy = match property_probes {
        Some((prop_ext, property_probes)) => {
            if separate_prop_run {
                if !classification.consistent {
                    Some(super::properties::PropertyHierarchy::default())
                } else {
                    let mut prop_cls =
                        classify_probe_source(cfg, &text, &prop_ext, "-prop-probes.ofn")?;
                    let foreign = |_: &str| false;
                    let mut hierarchy =
                        super::properties::split(&mut prop_cls, &property_probes, &foreign)?;
                    if prop_cls.consistent && property_probes.ranges_by_assertion() {
                        hierarchy.ranges = range_run(cfg, &text, &property_probes, &hierarchy)?;
                    }
                    Some(hierarchy)
                }
            } else {
                let foreign = |name: &str| individual_probes.contains(name);
                let mut hierarchy =
                    super::properties::split(&mut classification, &property_probes, &foreign)?;
                if classification.consistent && property_probes.ranges_by_assertion() {
                    hierarchy.ranges = range_run(cfg, &text, &property_probes, &hierarchy)?;
                }
                Some(hierarchy)
            }
        }
        None => empty_properties,
    };
    let mut realization = split_with_options(
        classification,
        &probes,
        mode.unwrap_or(TypeMode::All),
        nominal_equality_probes,
        precomputed_same,
    )?;
    if want_model_abox && realization.classification.consistent {
        if std::env::var_os("KM_TIMING").is_some() {
            eprintln!(
                "KM_TIMING realize: entering from_exported_model (has_model={})",
                exported_model.as_ref().is_some_and(|r| r.as_ref().is_ok_and(|o| o.is_some()))
            );
        }
        let model_plan = exported_model
            .and_then(|res| res.ok().flatten())
            .and_then(|(raw, meta)| {
                super::abox_rows::from_exported_model(
                    &text,
                    &roles,
                    &individuals,
                    values,
                    different,
                    &realization.classification,
                    &realization,
                    &raw,
                    &meta,
                )
            });
        if let Some(plan) = model_plan {
            if std::env::var_os("KM_TIMING").is_some() {
                eprintln!(
                    "KM_TIMING realize: model_plan ok (proved_val={}, proved_diff={}, res_val={}, res_diff={})",
                    plan.proved_values.len(),
                    plan.proved_different.len(),
                    plan.residual_value_targets.len(),
                    plan.residual_different_pairs.len()
                );
            }
            let mut val_set = plan.proved_values.clone();
            let mut diff_set = plan.proved_different.clone();
            if values && !plan.residual_value_targets.is_empty() {
                let (res_ext, ind_probes, abox_p) = super::abox_rows::residual_extension(
                    &text,
                    &roles,
                    &individuals,
                    true,
                    false,
                    &plan,
                );
                if !res_ext.is_empty() {
                    let mut abox_cls =
                        classify_probe_source(cfg, &text, &res_ext, "-abox-val-probes.ofn")?;
                    let individual_of: BTreeMap<String, String> = ind_probes.into_iter().collect();
                    let rows = super::abox_rows::split(&mut abox_cls, &abox_p, &individual_of)?;
                    if abox_cls.consistent {
                        if let Some(vs) = rows.values {
                            val_set.extend(vs);
                        }
                    }
                }
            }
            if different && !plan.residual_different_pairs.is_empty() {
                let (res_ext, ind_probes, abox_p) = super::abox_rows::residual_extension(
                    &text,
                    &roles,
                    &individuals,
                    false,
                    true,
                    &plan,
                );
                if !res_ext.is_empty() {
                    let mut abox_cls =
                        classify_probe_source(cfg, &text, &res_ext, "-abox-diff-probes.ofn")?;
                    let individual_of: BTreeMap<String, String> = ind_probes.into_iter().collect();
                    let rows = super::abox_rows::split(&mut abox_cls, &abox_p, &individual_of)?;
                    if abox_cls.consistent {
                        if let Some(ds) = rows.different {
                            diff_set.extend(ds);
                        }
                    }
                }
            }
            abox = super::abox_rows::AboxRows {
                values: values.then(|| val_set.into_iter().collect()),
                different: different.then(|| diff_set.into_iter().collect()),
            };
        } else if values && different {
            let (ind_ext, ind_probes) = individual_extension(&text, &individuals);
            let individual_of: BTreeMap<String, String> = ind_probes.into_iter().collect();
            let mut val_ext = ind_ext.clone();
            let (ext_v, abox_pv) =
                super::abox_rows::extension(&text, &roles, &individuals, true, false);
            val_ext.push_str(&ext_v);
            let mut val_cls =
                classify_probe_source(cfg, &text, &val_ext, "-abox-val-probes.ofn")?;
            let val_rows = super::abox_rows::split(&mut val_cls, &abox_pv, &individual_of)?;

            let mut diff_ext = ind_ext;
            let (ext_d, abox_pd) =
                super::abox_rows::extension(&text, &roles, &individuals, false, true);
            diff_ext.push_str(&ext_d);
            let mut diff_cls =
                classify_probe_source(cfg, &text, &diff_ext, "-abox-diff-probes.ofn")?;
            let diff_rows = super::abox_rows::split(&mut diff_cls, &abox_pd, &individual_of)?;
            if val_cls.consistent && diff_cls.consistent {
                abox = super::abox_rows::AboxRows {
                    values: val_rows.values,
                    different: diff_rows.different,
                };
            }
        } else {
            let (mut abox_ext, ind_probes) = individual_extension(&text, &individuals);
            let (ext2, abox_p) =
                super::abox_rows::extension(&text, &roles, &individuals, values, different);
            abox_ext.push_str(&ext2);
            let mut abox_cls =
                classify_probe_source(cfg, &text, &abox_ext, "-abox-probes.ofn")?;
            let individual_of: BTreeMap<String, String> = ind_probes.into_iter().collect();
            let rows = super::abox_rows::split(&mut abox_cls, &abox_p, &individual_of)?;
            if abox_cls.consistent {
                abox = rows;
            }
        }
    }
    if mode.is_none() {
        // The individual probes were added only for --values or --different.
        realization.types.clear();
        realization.same.clear();
    }
    if let Some((o, names)) = collapsed_names {
        expand_singleton_domain(&o, &names, mode.is_some(), &mut realization, &mut abox);
    }
    Ok(Extended { realization, properties: hierarchy, data_properties: data_hierarchy, abox, top: top_classes })
}

/// The individual `o` of an asserted `SubClassOf(owl:Thing ObjectOneOf(o))`
/// or `EquivalentClasses(owl:Thing ObjectOneOf(o))` (one distinct
/// individual), when the source has more than one named individual.
///
/// Such an axiom makes the domain of every model the single element `o^I`,
/// so `O ⊨ a = o` for every individual `a` of a consistent `O`; then
/// `O ⊨ C(a)` iff `O ⊨ C(o)`, `O ⊨ r(a, b)` iff `O ⊨ r(o, o)`, every pair
/// is `SAME` and no pair is `DIFFERENT`. Lenient input is left alone.
fn singleton_domain_individual(text: &str, individuals: &[String]) -> Option<String> {
    if individuals.len() < 2
        || crate::frontend::lenient::enabled()
        || std::env::var_os("KM_NO_SINGLETON_DOMAIN").is_some()
        || !text.contains("ObjectOneOf(")
    {
        return None;
    }
    let prefixes = prefix_bindings(text).ok()?;
    let is_thing = |token: &str| {
        if is_top_class_token(token) {
            return true;
        }
        let Some((prefix, local)) = token.split_once(':') else { return false };
        prefixes
            .get(prefix)
            .is_some_and(|ns| format!("{ns}{local}") == format!("{OWL_NS}Thing"))
    };
    let mut found: Option<String> = None;
    let _ = crate::frontend::parse::for_each_ontology_child(text, |node| {
        if found.is_some() {
            return Ok(());
        }
        let Node::List(head @ ("SubClassOf" | "EquivalentClasses"), args) = node else {
            return Ok(());
        };
        let plain = plain_args(args);
        if plain.len() != 2 {
            return Ok(());
        }
        let (thing, one_of) = match (plain[0], plain[1]) {
            (Node::Atom(t), other) => (*t, other),
            (other, Node::Atom(t)) if *head == "EquivalentClasses" => (*t, other),
            _ => return Ok(()),
        };
        if !is_thing(thing) {
            return Ok(());
        }
        let Node::List("ObjectOneOf", members) = one_of else { return Ok(()) };
        let members: BTreeSet<&str> = plain_args(members).iter().filter_map(|m| m.as_atom()).collect();
        if members.len() == 1 {
            let o = *members.iter().next().unwrap();
            if individuals.iter().any(|i| i == o) {
                found = Some(o.to_string());
            }
        }
        Ok(())
    });
    found
}

/// Rows of the one-element domain `{o}` for every individual in `names`
/// (public names); see [`singleton_domain_individual`].
fn expand_singleton_domain(
    o: &str,
    names: &[String],
    realize: bool,
    realization: &mut Realization,
    abox: &mut super::abox_rows::AboxRows,
) {
    if !realization.classification.consistent {
        return;
    }
    let mut names: Vec<&String> = names.iter().collect();
    names.sort();
    names.dedup();
    if realize {
        let classes: Vec<String> = realization
            .types
            .iter()
            .filter(|[ind, _]| ind == o)
            .map(|[_, class]| class.clone())
            .collect();
        let mut types = Vec::with_capacity(classes.len() * names.len());
        for name in &names {
            for class in &classes {
                types.push([(*name).clone(), class.clone()]);
            }
        }
        types.sort();
        realization.types = types;
        let mut same = Vec::new();
        for (i, a) in names.iter().enumerate() {
            for b in &names[i + 1..] {
                same.push([(*a).clone(), (*b).clone()]);
            }
        }
        realization.same = same;
    }
    if let Some(values) = abox.values.as_mut() {
        let roles: BTreeSet<String> = values
            .iter()
            .filter(|[_, a, b]| a == o && b == o)
            .map(|[r, _, _]| r.clone())
            .collect();
        let mut out = Vec::with_capacity(roles.len() * names.len() * names.len());
        for r in &roles {
            for a in &names {
                for b in &names {
                    out.push([r.clone(), (*a).clone(), (*b).clone()]);
                }
            }
        }
        out.sort();
        *values = out;
    }
    if let Some(different) = abox.different.as_mut() {
        different.clear();
    }
}

/// Sets `KM_UNKNOWN_DATATYPES=free` for the probe run of the data property
/// probes and restores the caller's value when dropped.
struct FreeDatatypes(Option<std::ffi::OsString>);

impl FreeDatatypes {
    fn enable() -> Self {
        let previous = std::env::var_os("KM_UNKNOWN_DATATYPES");
        std::env::set_var("KM_UNKNOWN_DATATYPES", "free");
        FreeDatatypes(previous)
    }
}

impl Drop for FreeDatatypes {
    fn drop(&mut self) {
        match self.0.take() {
            Some(value) => std::env::set_var("KM_UNKNOWN_DATATYPES", value),
            None => std::env::remove_var("KM_UNKNOWN_DATATYPES"),
        }
    }
}

/// The message of the positive-EL ABox consistency certificate when it
/// declines an input its profile gate admitted (`orchestrate::mod`).
const POSITIVE_EL_ABOX_DECLINED: &str = "positive EL ABox consistency certificate declined";

/// Classify `text` extended with `extension` (inserted before the closing
/// parenthesis of its `Ontology(` node) through the production pipeline.
///
/// The positive-EL ABox certificate admits a source by its profile and then
/// fails the whole classification closed when the completion declines it,
/// which happens on some property extensions (inverse probes `∃r⁻.B` next to
/// reflexive and transitive properties and an ABox). Then KM classifies once
/// more with one more tautology on a fresh property,
/// `ObjectPropertyRange(g owl:Thing)`, which leaves the profile gate of that
/// certificate (a range axiom) and so takes the general route. The added
/// axiom holds in every interpretation, so the answer is the same.
fn classify_probe_source(
    cfg: &Config,
    text: &str,
    extension: &str,
    suffix: &str,
) -> Result<Classification, OrchestrateError> {
    let run = |extension: &str| -> Result<Classification, OrchestrateError> {
        super::engine_run::reset_cancel();
        let rewritten = tmpfile::TempPath::new(suffix);
        std::fs::write(rewritten.path(), insert_extension(text, extension)?)?;
        let _trusted = TrustedRewrite::register(rewritten.path());
        Ok(super::classify_with_evidence(cfg, rewritten.path())?.classification)
    };
    match run(extension) {
        Err(OrchestrateError::OutOfFragment(message)) if message == POSITIVE_EL_ABOX_DECLINED => {
            if std::env::var_os("KM_TIMING").is_some() {
                eprintln!("KM_TIMING probe run: positive EL ABox certificate declined; general route");
            }
            let guard = format!("{}guard", fresh_namespace_for(text, "guard"));
            let guarded = format!(
                "{extension}Declaration(ObjectProperty(<{guard}>))\nObjectPropertyRange(<{guard}> owl:Thing)\n"
            );
            run(&guarded)
        }
        other => other,
    }
}

/// The ranges of an inverse-free source from one more classification: the
/// source with a fresh asserted pair `r(a_r, b_r)` per nonempty named
/// property and a realization probe `{b_r}` per pair (see
/// [`super::properties::range_extension`] for the argument). The fresh
/// individuals never reach the output.
fn range_run(
    cfg: &Config,
    text: &str,
    probes: &super::properties::PropertyProbes,
    hierarchy: &super::properties::PropertyHierarchy,
) -> Result<Vec<[String; 2]>, OrchestrateError> {
    let (assertions, pairs) = super::properties::range_extension(text, probes, hierarchy);
    if pairs.is_empty() {
        return Ok(Vec::new());
    }
    let individuals: Vec<String> = pairs.iter().map(|(_, b)| b.clone()).collect();
    let (mut extension, individual_probes) = individual_extension(text, &individuals);
    extension.push_str(&assertions);
    if std::env::var_os("KM_TIMING").is_some() {
        eprintln!("KM_TIMING range run: {} asserted pairs", pairs.len());
    }
    // The rewrite is the validated source plus fresh named individuals, one
    // assertion of a source object property per pair, and probe classes that
    // name only those individuals.
    let classification = classify_probe_source(cfg, text, &extension, "-ranges.ofn")?;
    if !classification.consistent {
        return Err(OrchestrateError::InvalidOntology(
            "property ranges: the source is consistent but its extension with fresh asserted pairs is not \
             (a bug in the range reduction; please report the input)"
                .into(),
        ));
    }
    let realization = split(classification, &individual_probes, TypeMode::All)?;
    Ok(super::properties::ranges_from_types(probes, &pairs, &realization.types))
}

impl Realization {
    /// `--lines` output: the classification rows, then `TYPE` and `SAME` rows.
    pub fn to_lines(&self) -> String {
        let mut out = self.classification.to_lines();
        for [a, c] in &self.types {
            out.push_str(&format!("\nTYPE\t{a}\t{c}"));
        }
        for [a, b] in &self.same {
            out.push_str(&format!("\nSAME\t{a}\t{b}"));
        }
        out
    }

    /// JSON output: the classification object with `types` and `same` keys.
    pub fn write_json<W: Write>(&self, writer: W) -> serde_json::Result<()> {
        #[derive(serde::Serialize)]
        struct Encoded<'a> {
            consistent: bool,
            subsumptions: &'a [[String; 2]],
            unsatisfiable: &'a [String],
            dropped: usize,
            #[serde(skip_serializing_if = "Option::is_none")]
            approximate: Option<&'a str>,
            #[serde(skip_serializing_if = "Option::is_none")]
            lenient: Option<&'a [String]>,
            types: &'a [[String; 2]],
            same: &'a [[String; 2]],
        }
        let notes = crate::frontend::lenient::published_notes();
        let encoded = Encoded {
            consistent: self.classification.consistent,
            subsumptions: &self.classification.subsumptions,
            unsatisfiable: &self.classification.unsatisfiable,
            dropped: self.classification.dropped,
            approximate: self.classification.approximate.as_deref(),
            lenient: (!notes.is_empty()).then_some(notes.as_slice()),
            types: &self.types,
            same: &self.same,
        };
        let mut ser = serde_json::Serializer::with_formatter(writer, super::PyFmt);
        serde::Serialize::serialize(&encoded, &mut ser)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn collects_individuals_in_every_individual_position() {
        let _test_env = crate::test_env::write();
        let text = "Prefix(:=<urn:t#>)\nOntology(<urn:o>\n\
            Declaration(NamedIndividual(:d))\n\
            Declaration(Class(:C))\n\
            ClassAssertion(Annotation(rdfs:comment \"x\") ObjectSomeValuesFrom(:r ObjectOneOf(:n1 :n2)) :a)\n\
            ObjectPropertyAssertion(:r :a <urn:t#b>)\n\
            NegativeObjectPropertyAssertion(:r :a :c)\n\
            DataPropertyAssertion(:p :e \"1\")\n\
            SameIndividual(:a :f)\n\
            DifferentIndividuals(:g :h)\n\
            SubClassOf(:C ObjectHasValue(:r :v))\n\
            ClassAssertion(:C _:anon)\n\
            AnnotationAssertion(rdfs:label :notind \"x\")\n\
            DLSafeRule(Body(ClassAtom(:C Variable(<urn:x>)) ObjectPropertyAtom(:r Variable(<urn:x>) :w)) Head(ClassAtom(:C :k)))\n\
            )";
        let found = source_individuals(text).unwrap();
        assert_eq!(found, [":d", ":n1", ":n2", ":a", "<urn:t#b>", ":c", ":e", ":f", ":g", ":h", ":v", ":w", ":k"]);
    }

    #[test]
    fn probes_are_inserted_inside_the_ontology_node() {
        let _test_env = crate::test_env::write();
        let text = "Ontology(<urn:o> ClassAssertion(<urn:C> <urn:a>)) # trailing ) comment\n";
        let individuals = source_individuals(text).unwrap();
        let (extended, probes) = probe_source(text, &individuals).unwrap();
        assert_eq!(probes, [("http://km.invalid/realize#individual0".to_string(), "urn:a".to_string())]);
        assert!(extended.starts_with("Ontology(<urn:o> ClassAssertion(<urn:C> <urn:a>)\n"));
        assert!(extended.contains("EquivalentClasses(<http://km.invalid/realize#individual0> ObjectOneOf(<urn:a>))\n)"));
        assert_eq!(source_individuals(&extended).unwrap(), ["<urn:a>"]);
    }

    #[test]
    fn mixed_spellings_of_one_individual_yield_one_canonical_individual() {
        let _test_env = crate::test_env::write();
        let text = "Prefix(:=<http://x/o#>)\nOntology(<http://x/o>\n\
            Declaration(Class(:C)) Declaration(NamedIndividual(:a))\n\
            ClassAssertion(:C <http://x/o#a>)\nClassAssertion(:C :a)\n\
            SameIndividual(:b <http://x/o#c>) ClassAssertion(:C :c))";
        let (canonical, individuals) = canonical_individuals(text).unwrap();
        assert_eq!(individuals, ["<http://x/o#a>", ":b", "<http://x/o#c>"]);
        assert!(!canonical.contains(" :a") && !canonical.contains("(:a"));
        let (extended, probes) = probe_source(&canonical, &individuals).unwrap();
        assert_eq!(probes[0].1, "http://x/o#a");
        // The probe-extended document is its own canonical form.
        assert_eq!(crate::frontend::builtin_aliases::canonicalize(&extended).unwrap(), extended);
    }

    #[test]
    fn two_prefixed_spellings_of_one_individual_are_one_individual() {
        let _test_env = crate::test_env::write();
        let text = "Prefix(p:=<http://x/o#>)\nPrefix(q:=<http://x/o#>)\nOntology(ClassAssertion(p:C p:a) ClassAssertion(p:C q:a))";
        let (_, individuals) = canonical_individuals(text).unwrap();
        assert_eq!(individuals, ["<http://x/o#a>"]);
    }

    #[test]
    fn probe_namespace_avoids_source_iris() {
        let _test_env = crate::test_env::write();
        assert_eq!(fresh_namespace("<http://km.invalid/realize#x>"), "http://km.invalid/realize1#");
    }

    fn row(a: &str, b: &str) -> [String; 2] {
        [a.to_string(), b.to_string()]
    }

    /// U2 (round 4): the rows of an unsatisfiable class must not depend on
    /// the probe extension, so a consistent split prints no `SUB` row whose
    /// subclass is unsatisfiable.
    #[test]
    fn split_prints_no_sub_row_of_an_unsatisfiable_class() {
        let _test_env = crate::test_env::write();
        let probes = vec![("P0".to_string(), "a".to_string())];
        let extended = Classification {
            approximate: None,
            consistent: true,
            subsumptions: vec![row("A", "B"), row("U", "A"), row("U", "V"), row("V", "U"), row("P0", "A")],
            unsatisfiable: vec!["U".to_string(), "V".to_string()],
            dropped: 0,
        };
        let r = split(extended, &probes, TypeMode::All).unwrap();
        assert_eq!(r.classification.subsumptions, [row("A", "B")]);
        assert_eq!(r.classification.unsatisfiable, ["U", "V"]);
        assert_eq!(r.types, [row("a", "A")]);
    }

    #[test]
    fn split_separates_types_same_and_source_rows() {
        let _test_env = crate::test_env::write();
        let probes = vec![("P0".to_string(), "a".to_string()), ("P1".to_string(), "b".to_string())];
        let extended = Classification {
            approximate: None,
            consistent: true,
            subsumptions: vec![
                row("A", "B"), row("P0", "A"), row("P0", "B"), row("P0", OWL_THING),
                row("P0", "P1"), row("P1", "P0"), row("P1", "A"), row("P1", "B"),
                row("N", "P0"),
            ],
            unsatisfiable: vec!["U".to_string()],
            dropped: 0,
        };
        let all = split(extended.clone(), &probes, TypeMode::All).unwrap();
        assert_eq!(all.classification.subsumptions, [row("A", "B")]);
        assert_eq!(all.classification.unsatisfiable, ["U"]);
        assert_eq!(all.types, [row("a", "A"), row("a", "B"), row("b", "A"), row("b", "B")]);
        assert_eq!(all.same, [row("a", "b")]);
        let direct = split(extended, &probes, TypeMode::Direct).unwrap();
        assert_eq!(direct.types, [row("a", "A"), row("b", "A")]);
    }

    #[test]
    fn direct_types_keep_every_member_of_a_minimal_equivalence_class() {
        let _test_env = crate::test_env::write();
        let probes = vec![("P0".to_string(), "a".to_string())];
        let extended = Classification {
            approximate: None,
            consistent: true,
            subsumptions: vec![
                row("A", "A2"), row("A2", "A"), row("A", "B"), row("A2", "B"),
                row("P0", "A"), row("P0", "A2"), row("P0", "B"),
            ],
            unsatisfiable: vec![],
            dropped: 0,
        };
        let direct = split(extended, &probes, TypeMode::Direct).unwrap();
        assert_eq!(direct.types, [row("a", "A"), row("a", "A2")]);
    }

    #[test]
    fn split_top_reads_classes_below_the_thing_probe() {
        let _test_env = crate::test_env::write();
        let text = "Ontology(<urn:o> EquivalentClasses(<urn:E> owl:Thing))";
        let (axioms, probe) = top_extension(text);
        assert!(axioms.contains(&format!("EquivalentClasses(<{probe}> owl:Thing)")), "{axioms}");
        let mut extended = Classification {
            approximate: None,
            consistent: true,
            subsumptions: vec![
                row("A", "B"),
                row(&probe, "urn:E"),
                row(&probe, OWL_THING),
                row(&probe, "foreign"),
                row("urn:E", &probe),
                row("A", &probe),
            ],
            unsatisfiable: vec!["U".into()],
            dropped: 0,
        };
        let top = split_top(&mut extended, &probe, &|name| name == "foreign").unwrap();
        assert_eq!(top, ["urn:E"]);
        assert_eq!(extended.subsumptions, [row("A", "B")]);
        assert_eq!(extended.unsatisfiable, ["U"]);
        extended.unsatisfiable.push(probe.clone());
        assert!(split_top(&mut extended, &probe, &|_| false).is_err());
        extended.consistent = false;
        extended.unsatisfiable.push(probe.clone());
        assert!(split_top(&mut extended, &probe, &|_| false).unwrap().is_empty());
    }

    #[test]
    fn inconsistent_classification_has_no_realization_rows() {
        let _test_env = crate::test_env::write();
        let probes = vec![("P0".to_string(), "a".to_string())];
        let extended = Classification {
            approximate: None,
            consistent: false,
            subsumptions: vec![],
            unsatisfiable: vec!["P0".to_string()],
            dropped: 0,
        };
        let result = split(extended, &probes, TypeMode::All).unwrap();
        assert!(!result.classification.consistent);
        assert!(result.classification.unsatisfiable.is_empty());
        assert!(result.types.is_empty() && result.same.is_empty());
    }

    #[test]
    fn separate_and_combined_property_and_abox_probe_paths_match_identically() {
        let _test_env = crate::test_env::write();
        let _env = crate::routing::EnvironmentGuard::capture();
        std::env::set_var("KM_ROUTE", "auto");
        std::env::set_var("KM_THREADS", "1");
        let text = "Prefix(:=<http://ex.org/>)\nPrefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\nOntology(<http://ex.org/p3>\n\
            Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C))\n\
            Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:s))\n\
            Declaration(DataProperty(:dp1)) Declaration(DataProperty(:dp2))\n\
            Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b)) Declaration(NamedIndividual(:c))\n\
            SubObjectPropertyOf(:r :s)\n\
            SubDataPropertyOf(:dp1 :dp2)\n\
            DataPropertyDomain(:dp2 :A)\n\
            ObjectPropertyDomain(:s :A)\n\
            ObjectPropertyRange(:s :B)\n\
            SubClassOf(ObjectIntersectionOf(:A :B) :C)\n\
            DisjointClasses(:B :C)\n\
            ObjectPropertyAssertion(:r :a :b)\n\
            ClassAssertion(:B :c)\n\
        )";
        let path = super::tmpfile::TempPath::new("-p3-split-equiv.ofn");
        std::fs::write(path.path(), text).unwrap();
        let cfg = Config::from_env();

        let sep = classify_extended(
            &cfg,
            path.path(),
            Some(TypeMode::All),
            true,
            true,
            true,
            true,
            true,
        )
        .unwrap();

        let comb = {
            let _g = crate::routing::EnvironmentGuard::capture();
            std::env::set_var("KM_COMBINED_PROP_PROBES", "1");
            std::env::set_var("KM_COMBINED_DATA_PROBES", "1");
            std::env::set_var("KM_ABOX_PROBES_ONLY", "1");
            classify_extended(
                &cfg,
                path.path(),
                Some(TypeMode::All),
                true,
                true,
                true,
                true,
                true,
            )
            .unwrap()
        };

        assert_eq!(sep.realization, comb.realization);
        assert_eq!(sep.properties, comb.properties);
        assert_eq!(sep.data_properties, comb.data_properties);
        assert_eq!(sep.abox, comb.abox);
        assert_eq!(sep.top, comb.top);
    }

    #[test]
    fn nominal_free_case_a_coalesces_signatures_and_matches_nominal_probes() {
        let _test_env = crate::test_env::write();
        let _env = crate::routing::EnvironmentGuard::capture();
        std::env::set_var("KM_ROUTE", "auto");
        std::env::set_var("KM_THREADS", "1");
        let text = "Prefix(:=<http://ex.org/>)\nOntology(<http://ex.org/nf-a>\n\
            Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C))\n\
            Declaration(ObjectProperty(:inert))\n\
            Declaration(NamedIndividual(:a1)) Declaration(NamedIndividual(:a2))\n\
            Declaration(NamedIndividual(:b1)) Declaration(NamedIndividual(:b2))\n\
            Declaration(NamedIndividual(:u))\n\
            SubClassOf(:A :B)\n\
            SubClassOf(:B :C)\n\
            ClassAssertion(:A :a1)\n\
            ClassAssertion(:A :a2)\n\
            ClassAssertion(ObjectSomeValuesFrom(:inert owl:Thing) :a1)\n\
            ClassAssertion(:B :b1)\n\
            SameIndividual(:b1 :b2)\n\
        )";
        let (canon, individuals) = canonical_individuals(text).unwrap();
        let nf = nominal_free_individual_extension(&canon, &individuals)
            .expect("Case A nominal-free extension applies");
        assert!(!nf.extension.contains("ObjectOneOf("));
        assert_eq!(
            nf.precomputed_same,
            vec![[":b1".to_string(), ":b2".to_string()]]
        );

        let path = super::tmpfile::TempPath::new("-nf-case-a.ofn");
        std::fs::write(path.path(), text).unwrap();
        let cfg = Config::from_env();
        let fast = realize(&cfg, path.path(), TypeMode::All).unwrap();
        let slow = {
            let _g = crate::test_env::EnvVar::set("KM_NO_NOMINAL_FREE_REALIZE", "1");
            realize(&cfg, path.path(), TypeMode::All).unwrap()
        };
        assert_eq!(fast, slow);
    }

    #[test]
    fn nominal_free_case_b_bisimulation_matches_nominal_probes_and_declines_unsafe_constructs() {
        let _test_env = crate::test_env::write();
        let _env = crate::routing::EnvironmentGuard::capture();
        std::env::set_var("KM_ROUTE", "auto");
        std::env::set_var("KM_THREADS", "1");
        let text = "Prefix(:=<http://ex.org/>)\nOntology(<http://ex.org/nf-b>\n\
            Declaration(Class(:Leaf)) Declaration(Class(:Parent)) Declaration(Class(:Root))\n\
            Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:s))\n\
            Declaration(NamedIndividual(:x1)) Declaration(NamedIndividual(:x2))\n\
            Declaration(NamedIndividual(:y1)) Declaration(NamedIndividual(:y2))\n\
            SubObjectPropertyOf(:r :s)\n\
            TransitiveObjectProperty(:s)\n\
            SubClassOf(ObjectSomeValuesFrom(:s :Leaf) :Parent)\n\
            SubClassOf(ObjectSomeValuesFrom(:r :Parent) :Root)\n\
            ClassAssertion(:Leaf :y1)\n\
            ClassAssertion(:Leaf :y2)\n\
            ObjectPropertyAssertion(:r :x1 :y1)\n\
            ObjectPropertyAssertion(:r :x2 :y2)\n\
        )";
        let (canon, individuals) = canonical_individuals(text).unwrap();
        let nf = nominal_free_individual_extension(&canon, &individuals)
            .expect("Case B nominal-free bisimulation extension applies");
        assert!(!nf.extension.contains("ObjectOneOf("));
        assert!(nf.extension.contains("ObjectSomeValuesFrom("));

        let path = super::tmpfile::TempPath::new("-nf-case-b.ofn");
        std::fs::write(path.path(), text).unwrap();
        let cfg = Config::from_env();
        let fast = realize(&cfg, path.path(), TypeMode::All).unwrap();
        let slow = {
            let _g = crate::test_env::EnvVar::set("KM_NO_NOMINAL_FREE_REALIZE", "1");
            realize(&cfg, path.path(), TypeMode::All).unwrap()
        };
        assert_eq!(fast, slow);

        // Declines when an active role has functionality, cardinality, universal restriction, or nominal coupling.
        for extra in [
            "FunctionalObjectProperty(:r)",
            "SubClassOf(:Root ObjectAllValuesFrom(:r :Leaf))",
            "SubClassOf(:Root ObjectMaxCardinality(1 :r :Leaf))",
            "SubClassOf(:Root ObjectHasSelf(:r))",
            "NegativeObjectPropertyAssertion(:r :x1 :y2)",
        ] {
            let declined_src = text.replace(
                "ObjectPropertyAssertion(:r :x2 :y2)",
                &format!("ObjectPropertyAssertion(:r :x2 :y2)\n{extra}"),
            );
            let (c2, inds2) = canonical_individuals(&declined_src).unwrap();
            assert!(
                nominal_free_individual_extension(&c2, &inds2).is_none(),
                "Case B must decline when {extra} is present"
            );
        }
    }

    /// The decision table of `docs/V1.7.0-SPEED.md` section 4(c): which
    /// case each axiom kind leaves the scan in. `'A'`, `'B'` or `'-'`
    /// (decline).
    fn nominal_free_decision(src: &str) -> char {
        let (canon, individuals) = match canonical_individuals(src) {
            Ok(found) => found,
            Err(_) => return '-',
        };
        match nominal_free_individual_extension(&canon, &individuals) {
            None => '-',
            Some(nf) if nf.case_b => 'B',
            Some(_) => 'A',
        }
    }

    fn nominal_free_doc(body: &str) -> String {
        format!(
            "Prefix(:=<http://ex.org/>)\nPrefix(owl:=<http://www.w3.org/2002/07/owl#>)\n\
             Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\nOntology(<http://ex.org/t>\n\
             Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C)) Declaration(Class(:D))\n\
             Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:s)) Declaration(ObjectProperty(:t))\n\
             Declaration(ObjectProperty(:f)) Declaration(DataProperty(:d)) Declaration(DataProperty(:e))\n\
             Declaration(NamedIndividual(:x1)) Declaration(NamedIndividual(:x2))\n\
             Declaration(NamedIndividual(:y1)) Declaration(NamedIndividual(:y2))\n\
             {body}\n)"
        )
    }

    #[test]
    fn nominal_free_scan_decision_table_covers_every_axiom_kind() {
        let _test_env = crate::test_env::write();
        let _env = crate::routing::EnvironmentGuard::capture();
        std::env::remove_var("KM_NO_NOMINAL_FREE_REALIZE");
        // Base B: `r` is constrained by an EL axiom and asserted.
        let base_b = "SubClassOf(ObjectSomeValuesFrom(:r :A) :B)\nClassAssertion(:A :y1)\n\
                      ObjectPropertyAssertion(:r :x1 :y1)\nObjectPropertyAssertion(:r :x2 :y2)";
        // Base A: `f` is asserted and mentioned nowhere else.
        let base_a = "SubClassOf(:A :B)\nClassAssertion(:A :y1)\nObjectPropertyAssertion(:f :x1 :y1)";
        assert_eq!(nominal_free_decision(&nominal_free_doc(base_b)), 'B');
        assert_eq!(nominal_free_decision(&nominal_free_doc(base_a)), 'A');
        let table: &[(&str, char, char)] = &[
            // (extra axiom, decision with base A, decision with base B)
            ("SubClassOf(:A :B)", 'A', 'B'),
            ("SubClassOf(owl:Thing ObjectSomeValuesFrom(:s :C))", 'A', 'B'),
            ("EquivalentClasses(:C ObjectIntersectionOf(:A ObjectSomeValuesFrom(:s :B)))", 'A', 'B'),
            ("DisjointClasses(:A :D)", 'A', 'B'),
            ("SubClassOf(:A owl:Nothing)", 'A', 'B'),
            ("SubObjectPropertyOf(:r :s)", 'A', 'B'),
            ("SubObjectPropertyOf(ObjectPropertyChain(:r :s) :t)", 'A', 'B'),
            ("EquivalentObjectProperties(:r :t)", 'A', 'B'),
            ("TransitiveObjectProperty(:r)", 'A', 'B'),
            ("ObjectPropertyDomain(:r :C)", 'A', 'B'),
            ("ObjectPropertyRange(:r :C)", 'A', 'B'),
            ("DisjointObjectProperties(:r :t)", 'A', 'B'),
            ("IrreflexiveObjectProperty(:r)", 'A', 'B'),
            ("AsymmetricObjectProperty(:r)", 'A', 'B'),
            ("SubObjectPropertyOf(:f owl:topObjectProperty)", 'A', 'B'),
            ("SubDataPropertyOf(:d :e)", 'A', 'B'),
            ("EquivalentDataProperties(:d :e)", 'A', 'B'),
            ("DisjointDataProperties(:d :e)", 'A', 'B'),
            ("FunctionalDataProperty(:d)", 'A', 'B'),
            ("DataPropertyDomain(:d :C)", 'A', 'B'),
            ("DataPropertyRange(:d xsd:integer)", 'A', 'B'),
            ("SameIndividual(:x1 :x2)", 'A', 'B'),
            ("DifferentIndividuals(:x1 :y2)", 'A', 'B'),
            ("ClassAssertion(ObjectSomeValuesFrom(:f :A) :x2)", 'A', 'B'),
            ("AnnotationAssertion(<http://www.w3.org/2000/01/rdf-schema#comment> :A \"c\")", 'A', 'B'),
            // Outside the Horn fragment: case A only.
            ("SubClassOf(:A ObjectUnionOf(:C :D))", 'A', '-'),
            ("SubClassOf(ObjectComplementOf(:A) :C)", 'A', '-'),
            ("SubClassOf(:A ObjectAllValuesFrom(:s :C))", 'A', '-'),
            ("SubClassOf(:A ObjectMinCardinality(2 :s :C))", 'A', '-'),
            ("SubClassOf(:A ObjectMaxCardinality(1 :s))", 'A', '-'),
            ("SubClassOf(:A ObjectExactCardinality(1 :s :C))", 'A', '-'),
            ("SubClassOf(:A ObjectHasSelf(:s))", 'A', '-'),
            ("SubClassOf(ObjectSomeValuesFrom(ObjectInverseOf(:s) owl:Thing) :C)", 'A', '-'),
            ("InverseObjectProperties(:s :t)", 'A', '-'),
            ("SymmetricObjectProperty(:s)", 'A', '-'),
            ("FunctionalObjectProperty(:s)", 'A', '-'),
            ("InverseFunctionalObjectProperty(:s)", 'A', '-'),
            ("ReflexiveObjectProperty(:s)", 'A', '-'),
            ("DisjointUnion(:A :C :D)", 'A', '-'),
            ("SubClassOf(:A DataSomeValuesFrom(:d xsd:integer))", 'A', '-'),
            ("SubClassOf(:A DataAllValuesFrom(:d xsd:integer))", 'A', '-'),
            ("SubClassOf(:A DataHasValue(:d \"1\"^^xsd:integer))", 'A', '-'),
            ("SubClassOf(:A DataMaxCardinality(1 :d))", 'A', '-'),
            ("ClassAssertion(ObjectAllValuesFrom(ObjectInverseOf(:s) :B) :y1)", 'A', '-'),
            // A free property loses its freedom once another axiom mentions it.
            ("SubClassOf(ObjectSomeValuesFrom(ObjectInverseOf(:f) owl:Thing) :C)", '-', '-'),
            ("ClassAssertion(ObjectAllValuesFrom(ObjectInverseOf(:f) :B) :y1)", '-', '-'),
            ("ObjectPropertyRange(:f :C)", 'B', 'B'),
            // A range on a chain's super-property that the last link lacks.
            ("SubObjectPropertyOf(ObjectPropertyChain(:r :s) :t)\nObjectPropertyRange(:t :C)", 'A', '-'),
            // Always declined.
            ("SubClassOf(:A ObjectOneOf(:x1))", '-', '-'),
            ("SubClassOf(:A ObjectHasValue(:s :x1))", '-', '-'),
            ("SubClassOf(:A ObjectSomeValuesFrom(owl:topObjectProperty :C))", '-', '-'),
            ("SubObjectPropertyOf(:s owl:bottomObjectProperty)", '-', '-'),
            ("HasKey(:A (:s) ())", '-', '-'),
            ("NegativeObjectPropertyAssertion(:s :x1 :y1)", '-', '-'),
            ("DataPropertyAssertion(:d :x1 \"1\"^^xsd:integer)", '-', '-'),
            ("NegativeDataPropertyAssertion(:d :x1 \"1\"^^xsd:integer)", '-', '-'),
            ("DLSafeRule(Body(ClassAtom(:A Variable(<urn:v>))) Head(ClassAtom(:B Variable(<urn:v>))))", '-', '-'),
            ("Import(<http://ex.org/other>)", '-', '-'),
            ("SameIndividual(:x1 :x2)\nDifferentIndividuals(:x1 :x2)", '-', '-'),
        ];
        for &(extra, with_a, with_b) in table {
            let a = nominal_free_decision(&nominal_free_doc(&format!("{base_a}\n{extra}")));
            let b = nominal_free_decision(&nominal_free_doc(&format!("{base_b}\n{extra}")));
            assert_eq!((a, b), (with_a, with_b), "decision for {extra}");
        }
    }

    /// Each ontology here is one step of the case A or case B argument (or a
    /// past counterexample); the block probes must give exactly the rows of
    /// one nominal per individual.
    #[test]
    fn nominal_free_block_probes_match_one_nominal_per_individual() {
        let _test_env = crate::test_env::write();
        let _env = crate::routing::EnvironmentGuard::capture();
        std::env::set_var("KM_ROUTE", "auto");
        std::env::set_var("KM_THREADS", "1");
        std::env::remove_var("KM_NO_NOMINAL_FREE_REALIZE");
        let cases: &[(&str, char, &str)] = &[
            // review/e10/found/g22_496.ofn: a universal over an inverse in an assertion.
            ("g22", '-', "SubClassOf(:A :D)\nClassAssertion(ObjectAllValuesFrom(ObjectInverseOf(:r) :B) :y1)\n\
              ObjectPropertyAssertion(:r :x1 :y1)\nClassAssertion(:A :x2)"),
            // review/e10/found/g11_210.ofn: an inverse existential in a premise.
            ("g11", '-', "SubClassOf(ObjectSomeValuesFrom(ObjectInverseOf(:r) owl:Thing) ObjectIntersectionOf(:B :D))\n\
              ObjectPropertyAssertion(:r :x1 :y1)"),
            // Disjunction over a shared successor (bisimulation is not exact here).
            ("diamond", '-', "SubClassOf(:C ObjectUnionOf(:A :D))\nSubClassOf(ObjectSomeValuesFrom(:r :A) :B)\n\
              SubClassOf(ObjectSomeValuesFrom(:s :D) :B)\nClassAssertion(:C :y1)\n\
              ObjectPropertyAssertion(:r :x1 :y1)\nObjectPropertyAssertion(:s :x1 :y1)"),
            // Case A with a non-Horn TBox; `f` is free and its existential is dropped.
            ("case-a", 'A', "SubClassOf(:A ObjectUnionOf(:B :C))\nSubClassOf(:B :D)\nSubClassOf(:C :D)\n\
              SubClassOf(:D ObjectAllValuesFrom(:r ObjectComplementOf(:A)))\nClassAssertion(:A :x1)\n\
              ClassAssertion(ObjectSomeValuesFrom(:f :B) :x2)\nClassAssertion(:A :x2)\n\
              ObjectPropertyAssertion(:f :x1 :y1)\nSameIndividual(:y1 :y2)"),
            // Case B: an untyped successor still fires `∃r.⊤`.
            ("untyped", 'B', "SubClassOf(ObjectIntersectionOf(:A ObjectSomeValuesFrom(:r owl:Thing)) :B)\n\
              ClassAssertion(:A :x1)\nClassAssertion(:A :x2)\nObjectPropertyAssertion(:r :x1 :y1)"),
            // Case B: a range of an asserted edge feeds a premise on another edge.
            ("range", 'B', "ObjectPropertyRange(:s :A)\nSubClassOf(ObjectSomeValuesFrom(:r :A) :B)\n\
              ObjectPropertyAssertion(:s :x2 :y1)\nObjectPropertyAssertion(:r :x1 :y1)\n\
              ObjectPropertyAssertion(:r :x2 :y2)"),
            // Case B: a chain and a domain on a super-property.
            ("chain", 'B', "SubObjectPropertyOf(ObjectPropertyChain(:r :s) :t)\nSubClassOf(ObjectSomeValuesFrom(:t :B) :C)\n\
              SubObjectPropertyOf(:s :f)\nObjectPropertyDomain(:f :D)\nClassAssertion(:B :y2)\n\
              ObjectPropertyAssertion(:r :x1 :y1)\nObjectPropertyAssertion(:s :y1 :y2)\n\
              ObjectPropertyAssertion(:r :x2 :y1)"),
            // Case B: transitivity over a bisimilar cycle and a tail.
            ("cycle", 'B', "TransitiveObjectProperty(:r)\nSubClassOf(ObjectSomeValuesFrom(:r :A) :B)\n\
              SubClassOf(ObjectIntersectionOf(:B :C) :D)\nClassAssertion(:C :x1)\n\
              ObjectPropertyAssertion(:r :x1 :x2)\nObjectPropertyAssertion(:r :x2 :x1)\n\
              ObjectPropertyAssertion(:r :x2 :y1)\nObjectPropertyAssertion(:r :y1 :y2)\nClassAssertion(:A :y2)"),
            // Case B: an edge of an irrelevant property is dropped; SAME rows.
            ("irrelevant", 'B', "SubClassOf(:A ObjectSomeValuesFrom(:s :B))\nSubClassOf(ObjectSomeValuesFrom(:r :B) :C)\n\
              DisjointClasses(:C :D)\nClassAssertion(:A :x1)\nObjectPropertyAssertion(:s :x1 :y1)\n\
              ObjectPropertyAssertion(:r :x2 :x1)\nSameIndividual(:y1 :y2)"),
        ];
        let cfg = Config::from_env();
        for &(name, case, body) in cases {
            let src = nominal_free_doc(body);
            assert_eq!(nominal_free_decision(&src), case, "case of {name}");
            let path = super::tmpfile::TempPath::new(&format!("-nf-{name}.ofn"));
            std::fs::write(path.path(), &src).unwrap();
            let fast = realize(&cfg, path.path(), TypeMode::All).unwrap();
            let slow = {
                let _g = crate::test_env::EnvVar::set("KM_NO_NOMINAL_FREE_REALIZE", "1");
                realize(&cfg, path.path(), TypeMode::All).unwrap()
            };
            assert_eq!(fast, slow, "block probes differ from nominals on {name}");
            assert!(!fast.types.is_empty() || name == "g11", "{name} has types");
        }
    }

    /// review/e10/found/hang_f808_194.ofn: `⊤ ⊑ {a0}` with 36 individuals ran
    /// past 120 s under `--realize` and `--values` (one nominal probe per
    /// individual). Must finish in 10 s, and on a 6-individual variant the
    /// realization must equal that of one nominal probe per individual.
    #[test]
    fn singleton_domain_realization_finishes_and_equals_per_individual_probes() {
        let _test_env = crate::test_env::write();
        let _env = crate::routing::EnvironmentGuard::capture();
        std::env::set_var("KM_ROUTE", "auto");
        std::env::set_var("KM_THREADS", "1");
        std::env::remove_var("KM_NO_SINGLETON_DOMAIN");
        let cfg = Config::from_env();
        const HANG: &str = r#"Prefix(:=<http://ex.org/>)
Prefix(owl:=<http://www.w3.org/2002/07/owl#>)
Ontology(<http://ex.org/f>
Declaration(ObjectProperty(:s0))
Declaration(ObjectProperty(:s1))
Declaration(ObjectProperty(:s2))
Declaration(ObjectProperty(:s3))
Declaration(ObjectProperty(:c0))
Declaration(ObjectProperty(:c1))
Declaration(ObjectProperty(:p0))
Declaration(ObjectProperty(:p1))
Declaration(ObjectProperty(:p2))
Declaration(ObjectProperty(:p3))
Declaration(ObjectProperty(:p4))
Declaration(ObjectProperty(:p5))
Declaration(ObjectProperty(:p6))
Declaration(ObjectProperty(:p7))
Declaration(ObjectProperty(:p8))
Declaration(ObjectProperty(:p9))
Declaration(NamedIndividual(:a0))
Declaration(NamedIndividual(:a1))
Declaration(NamedIndividual(:a2))
Declaration(NamedIndividual(:a3))
Declaration(NamedIndividual(:a4))
Declaration(NamedIndividual(:a5))
Declaration(NamedIndividual(:z0))
Declaration(NamedIndividual(:z1))
Declaration(NamedIndividual(:z2))
Declaration(NamedIndividual(:z3))
Declaration(NamedIndividual(:z4))
Declaration(NamedIndividual(:z5))
Declaration(NamedIndividual(:z6))
Declaration(NamedIndividual(:z7))
Declaration(NamedIndividual(:z8))
Declaration(NamedIndividual(:z9))
Declaration(NamedIndividual(:z10))
Declaration(NamedIndividual(:z11))
Declaration(NamedIndividual(:z12))
Declaration(NamedIndividual(:z13))
Declaration(NamedIndividual(:z14))
Declaration(NamedIndividual(:z15))
Declaration(NamedIndividual(:z16))
Declaration(NamedIndividual(:z17))
Declaration(NamedIndividual(:z18))
Declaration(NamedIndividual(:z19))
Declaration(NamedIndividual(:z20))
Declaration(NamedIndividual(:z21))
Declaration(NamedIndividual(:z22))
Declaration(NamedIndividual(:z23))
Declaration(NamedIndividual(:z24))
Declaration(NamedIndividual(:z25))
Declaration(NamedIndividual(:z26))
Declaration(NamedIndividual(:z27))
Declaration(NamedIndividual(:z28))
Declaration(NamedIndividual(:z29))
Declaration(Class(:A))
Declaration(Class(:B))
Declaration(Class(:D))
SubClassOf(owl:Thing ObjectOneOf(:a0))
ObjectPropertyAssertion(:s3 :a5 :a3)
ObjectPropertyAssertion(:s1 :a2 :a2)
SubClassOf(:B ObjectMaxCardinality(1 :s2))
SubObjectPropertyOf(ObjectPropertyChain(:s3 :s3) :c1)
ObjectPropertyAssertion(:c0 :a1 :a0)
ObjectPropertyAssertion(:s2 :a1 :a5)
ObjectPropertyAssertion(:s0 :a5 :a1)
InverseObjectProperties(:s3 :s3)
ObjectPropertyAssertion(:p0 :z0 :z1)
)
"#;
        const SMALL: &str = r#"Prefix(:=<http://ex.org/>)
Prefix(owl:=<http://www.w3.org/2002/07/owl#>)
Ontology(<http://ex.org/f>
Declaration(ObjectProperty(:s0))
Declaration(ObjectProperty(:s1))
Declaration(ObjectProperty(:s2))
Declaration(ObjectProperty(:s3))
Declaration(ObjectProperty(:c0))
Declaration(ObjectProperty(:c1))
Declaration(ObjectProperty(:p0))
Declaration(ObjectProperty(:p1))
Declaration(ObjectProperty(:p2))
Declaration(ObjectProperty(:p3))
Declaration(ObjectProperty(:p4))
Declaration(ObjectProperty(:p5))
Declaration(ObjectProperty(:p6))
Declaration(ObjectProperty(:p7))
Declaration(ObjectProperty(:p8))
Declaration(ObjectProperty(:p9))
Declaration(NamedIndividual(:a0))
Declaration(NamedIndividual(:a1))
Declaration(NamedIndividual(:a2))
Declaration(NamedIndividual(:a3))
Declaration(NamedIndividual(:a4))
Declaration(NamedIndividual(:a5))
Declaration(Class(:A))
Declaration(Class(:B))
Declaration(Class(:D))
SubClassOf(owl:Thing ObjectOneOf(:a0))
ObjectPropertyAssertion(:s3 :a5 :a3)
ObjectPropertyAssertion(:s1 :a2 :a2)
SubClassOf(:B ObjectMaxCardinality(1 :s2))
SubObjectPropertyOf(ObjectPropertyChain(:s3 :s3) :c1)
ObjectPropertyAssertion(:c0 :a1 :a0)
ObjectPropertyAssertion(:s2 :a1 :a5)
ObjectPropertyAssertion(:s0 :a5 :a1)
InverseObjectProperties(:s3 :s3)
)
"#;
        let path = super::tmpfile::TempPath::new("-singleton-domain.ofn");
        std::fs::write(path.path(), HANG).unwrap();
        let started = std::time::Instant::now();
        let ext = classify_extended(&cfg, path.path(), Some(TypeMode::All), false, false, false, true, false)
            .unwrap();
        assert!(started.elapsed() < std::time::Duration::from_secs(10), "took {:?}", started.elapsed());
        let r = &ext.realization;
        assert!(r.classification.consistent);
        assert_eq!(r.same.len(), 36 * 35 / 2);
        let values = ext.abox.values.as_ref().unwrap();
        assert!(!values.is_empty() && values.len() % (36 * 36) == 0);

        let path = super::tmpfile::TempPath::new("-singleton-domain-small.ofn");
        std::fs::write(path.path(), SMALL).unwrap();
        // `--values` with one probe per individual does not finish here
        // either (over 120 s on 6 individuals); its rows are checked
        // against HermiT in the T4 fuzz run instead.
        let fast = classify_extended(&cfg, path.path(), Some(TypeMode::All), true, false, false, false, false)
            .unwrap();
        let slow = {
            let _g = crate::test_env::EnvVar::set("KM_NO_SINGLETON_DOMAIN", "1");
            classify_extended(&cfg, path.path(), Some(TypeMode::All), true, false, false, false, false).unwrap()
        };
        assert_eq!(fast.realization, slow.realization);
        assert_eq!(fast.realization.same.len(), 6 * 5 / 2);
        assert_eq!(fast.properties, slow.properties);
    }

    #[test]
    fn classify_probe_source_resets_stale_engine_cancel_flag() {
        let _test_env = crate::test_env::write();
        let _env = crate::routing::EnvironmentGuard::capture();
        std::env::set_var("KM_ROUTE", "auto");
        std::env::set_var("KM_THREADS", "1");
        let text = "Prefix(:=<http://ex.org/>)\nOntology(<http://ex.org/cancel-reset>\n\
            Declaration(Class(:A)) Declaration(Class(:B))\n\
            Declaration(NamedIndividual(:a))\n\
            SubClassOf(:A :B)\n\
            ClassAssertion(:A :a)\n\
        )";
        let path = super::tmpfile::TempPath::new("-cancel-reset.ofn");
        std::fs::write(path.path(), text).unwrap();
        super::super::engine_run::cancel_and_kill_engines();
        let cfg = Config::from_env();
        let res = realize(&cfg, path.path(), TypeMode::All).unwrap();
        assert!(res.classification.consistent);
        assert_eq!(
            res.types,
            vec![
                [":a".to_string(), ":A".to_string()],
                [":a".to_string(), ":B".to_string()],
            ]
        );
    }
}
