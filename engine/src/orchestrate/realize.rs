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

use std::collections::{BTreeMap, BTreeSet, HashSet};
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
}

fn is_top_class_token(token: &str) -> bool {
    matches!(token, "owl:Thing" | "<http://www.w3.org/2002/07/owl#Thing>")
}

fn is_top_object_property_token(token: &str) -> bool {
    matches!(
        token,
        "owl:topObjectProperty" | "<http://www.w3.org/2002/07/owl#topObjectProperty>"
    )
}

fn is_top_data_property_token(token: &str) -> bool {
    matches!(
        token,
        "owl:topDataProperty" | "<http://www.w3.org/2002/07/owl#topDataProperty>"
    )
}

fn node_has_literal(node: &Node<'_>) -> bool {
    match node {
        Node::Atom(token) => token.starts_with('"'),
        Node::List("Annotation", _) => false,
        Node::List(_, args) => args.iter().any(node_has_literal),
    }
}

fn node_mentions_atom(node: &Node<'_>, target: &str) -> bool {
    match node {
        Node::Atom(token) => *token == target,
        Node::List("Annotation", _) => false,
        Node::List(_, args) => args.iter().any(|arg| node_mentions_atom(arg, target)),
    }
}

fn node_mentions_nominal_or_top_role(node: &Node<'_>) -> bool {
    match node {
        Node::Atom(token) => {
            is_top_object_property_token(token) || is_top_data_property_token(token)
        }
        Node::List("Annotation", _) => false,
        Node::List("ObjectOneOf" | "ObjectHasValue", _) => true,
        Node::List(_, args) => args.iter().any(node_mentions_nominal_or_top_role),
    }
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

fn collect_object_roles_in_node<'a>(node: &Node<'a>, out: &mut HashSet<&'a str>) {
    let Node::List(head, args) = node else { return };
    if *head == "Annotation" {
        return;
    }
    let plain: Vec<&Node<'a>> = args
        .iter()
        .filter(|arg| arg.head() != Some("Annotation"))
        .collect();
    match *head {
        "ObjectSomeValuesFrom"
        | "ObjectAllValuesFrom"
        | "ObjectHasValue"
        | "ObjectHasSelf"
        | "ObjectPropertyDomain"
        | "ObjectPropertyRange" => {
            if let Some(Node::Atom(role)) = plain.first().copied() {
                out.insert(role);
            }
            for arg in plain.iter().skip(1) {
                collect_object_roles_in_node(arg, out);
            }
        }
        "ObjectMinCardinality" | "ObjectMaxCardinality" | "ObjectExactCardinality" => {
            if let Some(Node::Atom(role)) = plain.get(1).copied() {
                out.insert(role);
            }
            for arg in plain.iter().skip(2) {
                collect_object_roles_in_node(arg, out);
            }
        }
        "ObjectInverseOf" => {
            if let Some(Node::Atom(role)) = plain.first().copied() {
                out.insert(role);
            }
        }
        _ => {
            for arg in &plain {
                collect_object_roles_in_node(arg, out);
            }
        }
    }
}

fn collect_bad_case_b_roles_in_concept<'a>(
    node: &Node<'a>,
    in_complement: bool,
    bad_roles: &mut HashSet<&'a str>,
    has_equality_generators: &mut bool,
) {
    let Node::List(head, args) = node else { return };
    if *head == "Annotation" {
        return;
    }
    let plain: Vec<&Node<'a>> = args
        .iter()
        .filter(|arg| arg.head() != Some("Annotation"))
        .collect();
    match *head {
        "ObjectComplementOf" => {
            for arg in &plain {
                collect_object_roles_in_node(arg, bad_roles);
                collect_bad_case_b_roles_in_concept(
                    arg,
                    !in_complement,
                    bad_roles,
                    has_equality_generators,
                );
            }
        }
        "ObjectAllValuesFrom" | "ObjectHasSelf" | "ObjectInverseOf" => {
            collect_object_roles_in_node(node, bad_roles);
            for arg in &plain {
                collect_bad_case_b_roles_in_concept(
                    arg,
                    in_complement,
                    bad_roles,
                    has_equality_generators,
                );
            }
        }
        "ObjectMinCardinality" => {
            collect_object_roles_in_node(node, bad_roles);
            if in_complement {
                *has_equality_generators = true;
            }
            for arg in plain.iter().skip(2) {
                collect_bad_case_b_roles_in_concept(
                    arg,
                    in_complement,
                    bad_roles,
                    has_equality_generators,
                );
            }
        }
        "ObjectMaxCardinality" | "ObjectExactCardinality" => {
            collect_object_roles_in_node(node, bad_roles);
            *has_equality_generators = true;
            for arg in plain.iter().skip(2) {
                collect_bad_case_b_roles_in_concept(
                    arg,
                    in_complement,
                    bad_roles,
                    has_equality_generators,
                );
            }
        }
        "DataMaxCardinality" | "DataExactCardinality" => {
            *has_equality_generators = true;
        }
        "DataMinCardinality" if in_complement => {
            *has_equality_generators = true;
        }
        _ => {
            for arg in &plain {
                collect_bad_case_b_roles_in_concept(
                    arg,
                    in_complement,
                    bad_roles,
                    has_equality_generators,
                );
            }
        }
    }
}

fn lhs_can_match_untyped(node: &Node<'_>) -> bool {
    match node {
        Node::Atom(token) => is_top_class_token(token),
        Node::List("ObjectIntersectionOf", args) => args
            .iter()
            .filter(|arg| arg.head() != Some("Annotation"))
            .all(lhs_can_match_untyped),
        _ => true,
    }
}

/// Exact nominal-free block-probe realization extension for ontologies whose
/// TBox+RBox is closed under disjoint unions (no TBox nominals, keys, rules, or
/// non-tautological universal roles) and whose ABox is a positive object ABox
/// (with optional `SameIndividual`, `DifferentIndividuals`, and inert
/// existential-witness assertions).
fn nominal_free_individual_extension(
    text: &str,
    individuals: &[String],
) -> Option<NominalFreeIndividualProbes> {
    if individuals.is_empty() || std::env::var_os("KM_NO_NOMINAL_FREE_REALIZE").is_some() {
        return None;
    }
    let mut aborted = false;
    let mut has_anon_abox = false;
    let mut all_ca_atomic = true;
    let mut has_equality_generators = false;
    let mut untyped_can_fire_tbox = false;

    let mut ind_assertions: std::collections::HashMap<&str, Vec<(Option<&str>, String)>> =
        std::collections::HashMap::with_capacity(individuals.len());
    let mut existential_ca_roles: HashSet<&str> = HashSet::new();
    let mut opa_edges: Vec<(&str, &str, &str)> = Vec::new();
    let mut opa_roles: HashSet<&str> = HashSet::new();
    let mut same_groups: Vec<Vec<&str>> = Vec::new();
    let mut diff_groups: Vec<Vec<&str>> = Vec::new();

    let mut tbox_or_rbox_roles: HashSet<&str> = HashSet::new();
    let mut non_inert_existential_roles: HashSet<&str> = HashSet::new();
    let mut neg_tbox_roles: HashSet<&str> = HashSet::new();
    let mut bad_case_b_roles: HashSet<&str> = HashSet::new();
    let mut bad_case_b = false;

    let mut sub_roles: std::collections::HashMap<&str, Vec<&str>> =
        std::collections::HashMap::new();
    let mut inv_roles: std::collections::HashMap<&str, Vec<&str>> =
        std::collections::HashMap::new();
    let mut sym_roles: HashSet<&str> = HashSet::new();
    let mut trans_roles: HashSet<&str> = HashSet::new();
    let mut role_chains: Vec<(Vec<&str>, &str)> = Vec::new();
    let mut domains: std::collections::HashMap<&str, Vec<&str>> =
        std::collections::HashMap::new();
    let mut ranges: std::collections::HashMap<&str, Vec<&str>> =
        std::collections::HashMap::new();

    let scan_ok = crate::frontend::parse::for_each_ontology_child(text, |node| {
        if aborted {
            return Ok(());
        }
        let Node::List(head, args) = node else {
            return Ok(());
        };
        if matches!(
            *head,
            "Prefix"
                | "Annotation"
                | "AnnotationAssertion"
                | "SubAnnotationPropertyOf"
                | "AnnotationPropertyDomain"
                | "AnnotationPropertyRange"
                | "Declaration"
        ) {
            return Ok(());
        }
        if matches!(
            *head,
            "Import"
                | "DLSafeRule"
                | "HasKey"
                | "NegativeObjectPropertyAssertion"
                | "DataPropertyAssertion"
                | "NegativeDataPropertyAssertion"
        ) {
            aborted = true;
            return Ok(());
        }
        let plain: Vec<&Node<'_>> = args
            .iter()
            .filter(|arg| arg.head() != Some("Annotation"))
            .collect();
        if *head == "SubObjectPropertyOf" && plain.len() == 2 {
            if plain[1].as_atom().is_some_and(is_top_object_property_token)
                && !node_mentions_nominal_or_top_role(plain[0])
            {
                return Ok(());
            }
        }
        if *head == "SubDataPropertyOf" && plain.len() == 2 {
            if plain[1].as_atom().is_some_and(is_top_data_property_token)
                && !node_mentions_nominal_or_top_role(plain[0])
            {
                return Ok(());
            }
        }
        if node_mentions_nominal_or_top_role(node) {
            aborted = true;
            return Ok(());
        }

        match *head {
            "ClassAssertion" => {
                if plain.len() != 2 || node_has_literal(plain[0]) {
                    aborted = true;
                    return Ok(());
                }
                let Some(ind_tok) = plain[1].as_atom() else {
                    aborted = true;
                    return Ok(());
                };
                if let Node::List("ObjectSomeValuesFrom", ex_args) = plain[0] {
                    let ex_plain: Vec<&Node<'_>> = ex_args
                        .iter()
                        .filter(|arg| arg.head() != Some("Annotation"))
                        .collect();
                    if ex_plain.len() == 2 {
                        if let Some(r_tok) = ex_plain[0].as_atom() {
                            if !node_mentions_atom(ex_plain[1], r_tok) {
                                collect_object_roles_in_node(ex_plain[1], &mut tbox_or_rbox_roles);
                                collect_object_roles_in_node(
                                    ex_plain[1],
                                    &mut non_inert_existential_roles,
                                );
                                collect_object_roles_in_node(ex_plain[1], &mut neg_tbox_roles);
                                existential_ca_roles.insert(r_tok);
                                if ind_tok.starts_with("_:") {
                                    has_anon_abox = true;
                                } else {
                                    all_ca_atomic = false;
                                    ind_assertions
                                        .entry(ind_tok)
                                        .or_default()
                                        .push((Some(r_tok), render_node(plain[0])));
                                }
                                return Ok(());
                            }
                        }
                    }
                }
                collect_object_roles_in_node(plain[0], &mut tbox_or_rbox_roles);
                collect_object_roles_in_node(plain[0], &mut non_inert_existential_roles);
                collect_object_roles_in_node(plain[0], &mut neg_tbox_roles);
                if ind_tok.starts_with("_:") {
                    has_anon_abox = true;
                } else {
                    if plain[0].as_atom().is_none() {
                        all_ca_atomic = false;
                    }
                    ind_assertions
                        .entry(ind_tok)
                        .or_default()
                        .push((None, render_node(plain[0])));
                }
            }
            "ObjectPropertyAssertion" => {
                if plain.len() != 3 {
                    aborted = true;
                    return Ok(());
                }
                let (Some(r_tok), Some(a_tok), Some(b_tok)) = (
                    plain[0].as_atom(),
                    plain[1].as_atom(),
                    plain[2].as_atom(),
                ) else {
                    aborted = true;
                    return Ok(());
                };
                if a_tok.starts_with("_:") || b_tok.starts_with("_:") {
                    aborted = true;
                    return Ok(());
                }
                opa_edges.push((r_tok, a_tok, b_tok));
                opa_roles.insert(r_tok);
                non_inert_existential_roles.insert(r_tok);
            }
            "SameIndividual" => {
                let mut group = Vec::with_capacity(plain.len());
                for arg in &plain {
                    let Some(tok) = arg.as_atom() else {
                        aborted = true;
                        return Ok(());
                    };
                    if tok.starts_with("_:") {
                        aborted = true;
                        return Ok(());
                    }
                    group.push(tok);
                }
                if group.len() >= 2 {
                    same_groups.push(group);
                }
            }
            "DifferentIndividuals" => {
                let mut group = Vec::with_capacity(plain.len());
                for arg in &plain {
                    let Some(tok) = arg.as_atom() else {
                        aborted = true;
                        return Ok(());
                    };
                    if tok.starts_with("_:") {
                        aborted = true;
                        return Ok(());
                    }
                    group.push(tok);
                }
                if group.len() >= 2 {
                    diff_groups.push(group);
                }
            }
            "SubObjectPropertyOf" => {
                if plain.len() == 2 {
                    if let (Some(r1), Some(r2)) = (plain[0].as_atom(), plain[1].as_atom()) {
                        tbox_or_rbox_roles.insert(r1);
                        tbox_or_rbox_roles.insert(r2);
                        non_inert_existential_roles.insert(r1);
                        non_inert_existential_roles.insert(r2);
                        sub_roles.entry(r1).or_default().push(r2);
                    } else if let (Node::List("ObjectPropertyChain", ch), Some(sup)) =
                        (plain[0], plain[1].as_atom())
                    {
                        let mut chain_atoms = Vec::new();
                        for item in ch {
                            if item.head() == Some("Annotation") {
                                continue;
                            }
                            if let Some(r) = item.as_atom() {
                                chain_atoms.push(r);
                                tbox_or_rbox_roles.insert(r);
                            } else {
                                bad_case_b = true;
                            }
                        }
                        tbox_or_rbox_roles.insert(sup);
                        let is_inert_witness_chain = chain_atoms.len() >= 2
                            && chain_atoms[0] == sup
                            && chain_atoms[1..].iter().all(|&r| r != sup);
                        if !is_inert_witness_chain {
                            non_inert_existential_roles.extend(chain_atoms.iter().copied());
                            non_inert_existential_roles.insert(sup);
                        }
                        role_chains.push((chain_atoms, sup));
                    } else {
                        collect_object_roles_in_node(node, &mut tbox_or_rbox_roles);
                        collect_object_roles_in_node(node, &mut non_inert_existential_roles);
                        bad_case_b = true;
                    }
                } else {
                    collect_object_roles_in_node(node, &mut tbox_or_rbox_roles);
                    collect_object_roles_in_node(node, &mut non_inert_existential_roles);
                    bad_case_b = true;
                }
            }
            "EquivalentObjectProperties" => {
                let mut rs = Vec::new();
                for arg in &plain {
                    if let Some(r) = arg.as_atom() {
                        rs.push(r);
                        tbox_or_rbox_roles.insert(r);
                        non_inert_existential_roles.insert(r);
                    } else {
                        bad_case_b = true;
                    }
                }
                for i in 0..rs.len() {
                    for j in 0..rs.len() {
                        if i != j {
                            sub_roles.entry(rs[i]).or_default().push(rs[j]);
                        }
                    }
                }
            }
            "InverseObjectProperties" => {
                if let [Node::Atom(r1), Node::Atom(r2)] = plain.as_slice() {
                    tbox_or_rbox_roles.insert(*r1);
                    tbox_or_rbox_roles.insert(*r2);
                    non_inert_existential_roles.insert(*r1);
                    non_inert_existential_roles.insert(*r2);
                    inv_roles.entry(*r1).or_default().push(*r2);
                    inv_roles.entry(*r2).or_default().push(*r1);
                } else {
                    collect_object_roles_in_node(node, &mut tbox_or_rbox_roles);
                    collect_object_roles_in_node(node, &mut non_inert_existential_roles);
                    bad_case_b = true;
                }
            }
            "SymmetricObjectProperty" => {
                if let [Node::Atom(r)] = plain.as_slice() {
                    tbox_or_rbox_roles.insert(*r);
                    non_inert_existential_roles.insert(*r);
                    sym_roles.insert(*r);
                } else {
                    collect_object_roles_in_node(node, &mut tbox_or_rbox_roles);
                    collect_object_roles_in_node(node, &mut non_inert_existential_roles);
                    bad_case_b = true;
                }
            }
            "TransitiveObjectProperty" => {
                if let [Node::Atom(r)] = plain.as_slice() {
                    tbox_or_rbox_roles.insert(*r);
                    non_inert_existential_roles.insert(*r);
                    trans_roles.insert(*r);
                } else {
                    collect_object_roles_in_node(node, &mut tbox_or_rbox_roles);
                    collect_object_roles_in_node(node, &mut non_inert_existential_roles);
                    bad_case_b = true;
                }
            }
            "ObjectPropertyDomain" => {
                collect_object_roles_in_node(node, &mut tbox_or_rbox_roles);
                collect_object_roles_in_node(node, &mut non_inert_existential_roles);
                if let [Node::Atom(r), Node::Atom(c)] = plain.as_slice() {
                    if !is_top_class_token(c) {
                        domains.entry(*r).or_default().push(*c);
                    }
                } else {
                    collect_object_roles_in_node(node, &mut bad_case_b_roles);
                }
            }
            "ObjectPropertyRange" => {
                collect_object_roles_in_node(node, &mut tbox_or_rbox_roles);
                collect_object_roles_in_node(node, &mut non_inert_existential_roles);
                if let [Node::Atom(r), Node::Atom(c)] = plain.as_slice() {
                    if !is_top_class_token(c) {
                        ranges.entry(*r).or_default().push(*c);
                    }
                } else {
                    collect_object_roles_in_node(node, &mut bad_case_b_roles);
                }
            }
            "FunctionalObjectProperty"
            | "InverseFunctionalObjectProperty"
            | "ReflexiveObjectProperty"
            | "IrreflexiveObjectProperty"
            | "AsymmetricObjectProperty"
            | "DisjointObjectProperties" => {
                for arg in &plain {
                    if let Some(r) = arg.as_atom() {
                        tbox_or_rbox_roles.insert(r);
                        non_inert_existential_roles.insert(r);
                        bad_case_b_roles.insert(r);
                    } else {
                        collect_object_roles_in_node(arg, &mut tbox_or_rbox_roles);
                        collect_object_roles_in_node(arg, &mut non_inert_existential_roles);
                        collect_object_roles_in_node(arg, &mut bad_case_b_roles);
                    }
                }
                if matches!(
                    *head,
                    "FunctionalObjectProperty" | "InverseFunctionalObjectProperty"
                ) {
                    has_equality_generators = true;
                }
                if *head == "ReflexiveObjectProperty" {
                    untyped_can_fire_tbox = true;
                }
            }
            "FunctionalDataProperty" => {
                has_equality_generators = true;
            }
            "SubClassOf" => {
                for arg in &plain {
                    collect_object_roles_in_node(arg, &mut tbox_or_rbox_roles);
                    collect_object_roles_in_node(arg, &mut non_inert_existential_roles);
                }
                if let Some(lhs) = plain.first() {
                    collect_object_roles_in_node(lhs, &mut neg_tbox_roles);
                    if lhs_can_match_untyped(lhs) {
                        untyped_can_fire_tbox = true;
                    }
                    collect_bad_case_b_roles_in_concept(
                        lhs,
                        true,
                        &mut bad_case_b_roles,
                        &mut has_equality_generators,
                    );
                }
                for rhs in plain.iter().skip(1) {
                    collect_bad_case_b_roles_in_concept(
                        rhs,
                        false,
                        &mut bad_case_b_roles,
                        &mut has_equality_generators,
                    );
                }
            }
            "EquivalentClasses" | "DisjointClasses" => {
                for arg in &plain {
                    collect_object_roles_in_node(arg, &mut tbox_or_rbox_roles);
                    collect_object_roles_in_node(arg, &mut non_inert_existential_roles);
                    collect_object_roles_in_node(arg, &mut neg_tbox_roles);
                    if lhs_can_match_untyped(arg) {
                        untyped_can_fire_tbox = true;
                    }
                    collect_bad_case_b_roles_in_concept(
                        arg,
                        true,
                        &mut bad_case_b_roles,
                        &mut has_equality_generators,
                    );
                    collect_bad_case_b_roles_in_concept(
                        arg,
                        false,
                        &mut bad_case_b_roles,
                        &mut has_equality_generators,
                    );
                }
            }
            "DisjointUnion" => {
                untyped_can_fire_tbox = true;
                for arg in &plain {
                    collect_object_roles_in_node(arg, &mut tbox_or_rbox_roles);
                    collect_object_roles_in_node(arg, &mut non_inert_existential_roles);
                    collect_object_roles_in_node(arg, &mut neg_tbox_roles);
                    collect_bad_case_b_roles_in_concept(
                        arg,
                        true,
                        &mut bad_case_b_roles,
                        &mut has_equality_generators,
                    );
                    collect_bad_case_b_roles_in_concept(
                        arg,
                        false,
                        &mut bad_case_b_roles,
                        &mut has_equality_generators,
                    );
                }
            }
            _ => {
                for arg in &plain {
                    collect_object_roles_in_node(arg, &mut tbox_or_rbox_roles);
                    collect_object_roles_in_node(arg, &mut non_inert_existential_roles);
                }
            }
        }
        Ok(())
    });

    if scan_ok.is_err() || aborted {
        return None;
    }

    // Build SameIndividual union-find over `individuals`.
    let ind_index: std::collections::HashMap<&str, usize> = individuals
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
    for group in &same_groups {
        let first = *ind_index.get(group[0])?;
        let r0 = find(&mut parent, first);
        for &member in &group[1..] {
            let idx = *ind_index.get(member)?;
            let r = find(&mut parent, idx);
            if r != r0 {
                parent[r.max(r0)] = r.min(r0);
            }
        }
    }
    for group in &diff_groups {
        let mut seen_roots = HashSet::with_capacity(group.len());
        for &member in group {
            let idx = *ind_index.get(member)?;
            let r = find(&mut parent, idx);
            if !seen_roots.insert(r) {
                return None;
            }
        }
    }

    let mut comp_members: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    for i in 0..individuals.len() {
        let r = find(&mut parent, i);
        comp_members.entry(r).or_default().push(i);
    }
    let mut precomputed_same_set: BTreeSet<[String; 2]> = BTreeSet::new();
    if !same_groups.is_empty() {
        for members in comp_members.values() {
            if members.len() >= 2 {
                let pub_names: Vec<String> = members
                    .iter()
                    .map(|&i| public_name(&individuals[i]))
                    .collect();
                for i in 0..pub_names.len() {
                    for j in (i + 1)..pub_names.len() {
                        if pub_names[i] != pub_names[j] {
                            let (low, high) = if pub_names[i] < pub_names[j] {
                                (pub_names[i].clone(), pub_names[j].clone())
                            } else {
                                (pub_names[j].clone(), pub_names[i].clone())
                            };
                            precomputed_same_set.insert([low, high]);
                        }
                    }
                }
            }
        }
    }
    let precomputed_same: Vec<[String; 2]> = precomputed_same_set.into_iter().collect();

    let has_active_opa = opa_roles.iter().any(|r| tbox_or_rbox_roles.contains(r));

    // Case A: No active role assertions in the ABox and no DifferentIndividuals.
    if !has_active_opa
        && diff_groups.is_empty()
        && (same_groups.is_empty() || (opa_edges.is_empty() && !has_equality_generators))
    {
        // An existential-witness role R is inert when all existential ClassAssertions
        // use that single role R and R never occurs in non_inert_existential_roles.
        let inert_existential_role: Option<&str> = if existential_ca_roles.len() == 1 {
            let r = *existential_ca_roles.iter().next().unwrap();
            (!non_inert_existential_roles.contains(r)).then_some(r)
        } else {
            None
        };

        let namespace = fresh_namespace(text);
        let mut sig_to_probe: std::collections::HashMap<Vec<String>, String> =
            std::collections::HashMap::new();
        let mut ordered_sigs: Vec<(String, Vec<String>)> = Vec::new();
        let mut probes: Vec<(String, String)> = Vec::with_capacity(individuals.len());

        for members in comp_members.values() {
            let mut classes: Vec<String> = Vec::new();
            for &idx in members {
                if let Some(asserted) = ind_assertions.get(individuals[idx].as_str()) {
                    for (ex_role, rendered) in asserted {
                        if is_top_class_token(rendered) {
                            continue;
                        }
                        if ex_role.is_some() && *ex_role == inert_existential_role {
                            continue;
                        }
                        classes.push(rendered.clone());
                    }
                }
            }
            classes.sort_unstable();
            classes.dedup();
            let probe = if let Some(existing) = sig_to_probe.get(&classes) {
                existing.clone()
            } else {
                let id = ordered_sigs.len();
                let p = format!("{namespace}individual{id}");
                sig_to_probe.insert(classes.clone(), p.clone());
                ordered_sigs.push((p.clone(), classes));
                p
            };
            for &idx in members {
                probes.push((probe.clone(), public_name(&individuals[idx])));
            }
        }

        let mut extension = String::with_capacity(ordered_sigs.len() * 128 + 2);
        extension.push('\n');
        for (probe, classes) in &ordered_sigs {
            extension.push_str(&format!("Declaration(Class(<{probe}>))\n"));
            if classes.is_empty() {
                extension.push_str(&format!("SubClassOf(<{probe}> owl:Thing)\n"));
            } else {
                for class_expr in classes {
                    extension.push_str(&format!("SubClassOf(<{probe}> {class_expr})\n"));
                }
            }
        }
        return Some(NominalFreeIndividualProbes {
            extension,
            probes,
            precomputed_same,
        });
    }

    // Case B: Positive active role-assertion ABox (with optional DifferentIndividuals).
    if bad_case_b
        || has_anon_abox
        || !all_ca_atomic
        || (!diff_groups.is_empty() && has_equality_generators)
        || (!same_groups.is_empty() && has_equality_generators)
    {
        return None;
    }

    // Compute forward super-roles and inverse super-roles for every role in opa_roles.
    let mut fwd_supers: std::collections::HashMap<&str, HashSet<&str>> =
        std::collections::HashMap::new();
    let mut inv_supers: std::collections::HashMap<&str, HashSet<&str>> =
        std::collections::HashMap::new();
    for &r in &opa_roles {
        let mut f_set: HashSet<&str> = HashSet::new();
        let mut i_set: HashSet<&str> = HashSet::new();
        f_set.insert(r);
        if sym_roles.contains(r) {
            i_set.insert(r);
        }
        let mut changed = true;
        while changed {
            changed = false;
            let f_cur: Vec<&str> = f_set.iter().copied().collect();
            for s in f_cur {
                if let Some(sups) = sub_roles.get(s) {
                    for &sup in sups {
                        if f_set.insert(sup) {
                            changed = true;
                        }
                    }
                }
                if sym_roles.contains(s) && i_set.insert(s) {
                    changed = true;
                }
                if let Some(invs) = inv_roles.get(s) {
                    for &inv in invs {
                        if i_set.insert(inv) {
                            changed = true;
                        }
                    }
                }
            }
            let i_cur: Vec<&str> = i_set.iter().copied().collect();
            for s in i_cur {
                if let Some(sups) = sub_roles.get(s) {
                    for &sup in sups {
                        if i_set.insert(sup) {
                            changed = true;
                        }
                    }
                }
                if sym_roles.contains(s) && f_set.insert(s) {
                    changed = true;
                }
                if let Some(invs) = inv_roles.get(s) {
                    for &inv in invs {
                        if f_set.insert(inv) {
                            changed = true;
                        }
                    }
                }
            }
        }
        fwd_supers.insert(r, f_set);
        inv_supers.insert(r, i_set);
    }

    let mut active_opa_closure: HashSet<&str> = HashSet::new();
    for &r in &opa_roles {
        if let Some(f) = fwd_supers.get(r) {
            active_opa_closure.extend(f.iter().copied());
        }
        if let Some(i) = inv_supers.get(r) {
            active_opa_closure.extend(i.iter().copied());
        }
    }
    if active_opa_closure
        .iter()
        .any(|r| bad_case_b_roles.contains(r))
    {
        return None;
    }
    for (chain_atoms, _) in &role_chains {
        if chain_atoms.iter().all(|r| active_opa_closure.contains(r)) {
            return None;
        }
    }

    // Close neg_tbox_roles downward under sub_roles.
    let mut neg_closed = neg_tbox_roles.clone();
    loop {
        let mut added = false;
        for (&sub, sups) in &sub_roles {
            if !neg_closed.contains(sub) && sups.iter().any(|sup| neg_closed.contains(sup)) {
                neg_closed.insert(sub);
                added = true;
            }
        }
        if !added {
            break;
        }
    }
    // Check that no non-symmetric inverse super-role of an OPA role is in neg_closed.
    for &r in &opa_roles {
        let f_set = &fwd_supers[r];
        let i_set = &inv_supers[r];
        for &inv_r in i_set {
            if !f_set.contains(inv_r) && neg_closed.contains(inv_r) {
                return None;
            }
        }
    }

    let comp_roots: Vec<usize> = comp_members.keys().copied().collect();
    let root_to_cid: std::collections::HashMap<usize, usize> = comp_roots
        .iter()
        .enumerate()
        .map(|(cid, &root)| (root, cid))
        .collect();
    let n_comps = comp_roots.len();
    let mut comp_ca: Vec<Vec<String>> = vec![Vec::new(); n_comps];
    for (cid, &root) in comp_roots.iter().enumerate() {
        for &idx in &comp_members[&root] {
            if let Some(asserted) = ind_assertions.get(individuals[idx].as_str()) {
                for (_, rendered) in asserted {
                    if !is_top_class_token(rendered) {
                        comp_ca[cid].push(rendered.clone());
                    }
                }
            }
        }
    }

    // Expand OPA edges across SameIndividual components, symmetry, and forward super-roles,
    // and propagate ObjectPropertyDomain / ObjectPropertyRange onto endpoint components.
    let mut active_edges_by_role: std::collections::HashMap<&str, Vec<(usize, usize)>> =
        std::collections::HashMap::new();
    for &(r, a_tok, b_tok) in &opa_edges {
        let u = root_to_cid[&find(&mut parent, *ind_index.get(a_tok)?)];
        let v = root_to_cid[&find(&mut parent, *ind_index.get(b_tok)?)];
        for &s in &fwd_supers[r] {
            if let Some(doms) = domains.get(s) {
                for &d in doms {
                    comp_ca[u].push(d.to_string());
                }
            }
            if let Some(rngs) = ranges.get(s) {
                for &e in rngs {
                    comp_ca[v].push(e.to_string());
                }
            }
            if neg_closed.contains(s) {
                active_edges_by_role.entry(s).or_default().push((u, v));
                if sym_roles.contains(s) {
                    active_edges_by_role.entry(s).or_default().push((v, u));
                }
            }
        }
        for &s in &inv_supers[r] {
            if let Some(doms) = domains.get(s) {
                for &d in doms {
                    comp_ca[v].push(d.to_string());
                }
            }
            if let Some(rngs) = ranges.get(s) {
                for &e in rngs {
                    comp_ca[u].push(e.to_string());
                }
            }
        }
    }
    for ca_vec in &mut comp_ca {
        ca_vec.sort_unstable();
        ca_vec.dedup();
    }
    for edges in active_edges_by_role.values_mut() {
        edges.sort_unstable();
        edges.dedup();
    }

    // Build adjacency list for partition refinement.
    let mut active_participants = vec![true; n_comps];
    let mut adj: Vec<Vec<(&str, usize)>> = vec![Vec::new(); n_comps];
    if !untyped_can_fire_tbox {
        // Only typed components (!comp_ca[u].is_empty()) can ever satisfy any TBox
        // premise. Contract transitive paths through untyped components so untyped
        // components collapse to a single owl:Thing probe.
        for u in 0..n_comps {
            active_participants[u] = !comp_ca[u].is_empty();
        }
        let mut active_roles_sorted: Vec<&str> = active_edges_by_role.keys().copied().collect();
        active_roles_sorted.sort_unstable();
        for r in active_roles_sorted {
            let edges = &active_edges_by_role[r];
            if trans_roles.contains(r) {
                let mut r_adj: Vec<Vec<usize>> = vec![Vec::new(); n_comps];
                for &(u, v) in edges {
                    r_adj[u].push(v);
                }
                let mut memo: Vec<Option<Vec<usize>>> = vec![None; n_comps];
                let mut state: Vec<u8> = vec![0; n_comps];
                fn collect_typed(
                    u: usize,
                    r_adj: &[Vec<usize>],
                    typed: &[bool],
                    memo: &mut [Option<Vec<usize>>],
                    state: &mut [u8],
                ) -> Vec<usize> {
                    if let Some(cached) = &memo[u] {
                        return cached.clone();
                    }
                    state[u] = 1;
                    let mut out = Vec::new();
                    for &v in &r_adj[u] {
                        if typed[v] {
                            out.push(v);
                        }
                        if state[v] != 1 {
                            out.extend(collect_typed(v, r_adj, typed, memo, state));
                        }
                    }
                    out.sort_unstable();
                    out.dedup();
                    state[u] = 2;
                    memo[u] = Some(out.clone());
                    out
                }
                for u in 0..n_comps {
                    if active_participants[u] && !r_adj[u].is_empty() {
                        let targets =
                            collect_typed(u, &r_adj, &active_participants, &mut memo, &mut state);
                        for v in targets {
                            adj[u].push((r, v));
                        }
                    }
                }
            } else {
                for &(u, v) in edges {
                    if active_participants[u] && active_participants[v] {
                        adj[u].push((r, v));
                    }
                }
            }
        }
    } else {
        let mut active_roles_sorted: Vec<&str> = active_edges_by_role.keys().copied().collect();
        active_roles_sorted.sort_unstable();
        for r in active_roles_sorted {
            for &(u, v) in &active_edges_by_role[r] {
                adj[u].push((r, v));
            }
        }
    }
    for edges in &mut adj {
        edges.sort_unstable();
        edges.dedup();
    }

    let participant_ids: Vec<usize> = (0..n_comps)
        .filter(|&u| active_participants[u])
        .collect();
    let mut color = vec![usize::MAX; n_comps];
    let mut init_palette: std::collections::HashMap<&[String], usize> =
        std::collections::HashMap::new();
    for &u in &participant_ids {
        let next_id = init_palette.len();
        let c = *init_palette
            .entry(comp_ca[u].as_slice())
            .or_insert(next_id);
        color[u] = c;
    }
    let init_color = color.clone();
    let mut n_colors = init_palette.len();
    let mut converged = participant_ids.is_empty();
    let mut block_succs: Vec<Vec<(&str, usize)>> = vec![Vec::new(); n_colors];
    let mut block_init_ca: Vec<usize> = (0..n_colors).collect();

    for _round in 0..32 {
        if converged {
            break;
        }
        let mut new_palette: std::collections::HashMap<(usize, Vec<(&str, usize)>), usize> =
            std::collections::HashMap::with_capacity(n_colors);
        let mut new_color = vec![usize::MAX; n_comps];
        let mut new_block_succs: Vec<Vec<(&str, usize)>> = Vec::with_capacity(n_colors);
        let mut new_block_init_ca: Vec<usize> = Vec::with_capacity(n_colors);

        for &u in &participant_ids {
            let mut succ: Vec<(&str, usize)> = adj[u]
                .iter()
                .map(|&(r, v)| (r, color[v]))
                .collect();
            succ.sort_unstable();
            succ.dedup();
            let key = (init_color[u], succ);
            let next_id = new_palette.len();
            let c = match new_palette.entry(key) {
                std::collections::hash_map::Entry::Occupied(e) => *e.get(),
                std::collections::hash_map::Entry::Vacant(e) => {
                    new_block_init_ca.push(u);
                    new_block_succs.push(e.key().1.clone());
                    *e.insert(next_id)
                }
            };
            new_color[u] = c;
        }
        let new_n_colors = new_palette.len();
        color = new_color;
        block_succs = new_block_succs;
        block_init_ca = new_block_init_ca;
        if new_n_colors == n_colors {
            converged = true;
            break;
        }
        n_colors = new_n_colors;
    }
    if !converged {
        return None;
    }

    let namespace = fresh_namespace(text);
    let untyped_probe = if participant_ids.len() < n_comps {
        Some(format!("{namespace}individual{n_colors}"))
    } else {
        None
    };
    let mut probes: Vec<(String, String)> = Vec::with_capacity(individuals.len());
    for (cid, &root) in comp_roots.iter().enumerate() {
        let probe = if active_participants[cid] {
            format!("{namespace}individual{}", color[cid])
        } else {
            untyped_probe.as_ref().unwrap().clone()
        };
        for &idx in &comp_members[&root] {
            probes.push((probe.clone(), public_name(&individuals[idx])));
        }
    }

    let mut extension = String::with_capacity((n_colors + 1) * 160 + 2);
    extension.push('\n');
    for b in 0..n_colors {
        let probe = format!("{namespace}individual{b}");
        extension.push_str(&format!("Declaration(Class(<{probe}>))\n"));
    }
    if let Some(ref up) = untyped_probe {
        extension.push_str(&format!(
            "Declaration(Class(<{up}>))\nSubClassOf(<{up}> owl:Thing)\n"
        ));
    }
    for b in 0..n_colors {
        let probe = format!("{namespace}individual{b}");
        let rep_u = block_init_ca[b];
        if comp_ca[rep_u].is_empty() && block_succs[b].is_empty() {
            extension.push_str(&format!("SubClassOf(<{probe}> owl:Thing)\n"));
        } else {
            for c in &comp_ca[rep_u] {
                extension.push_str(&format!("SubClassOf(<{probe}> {c})\n"));
            }
            for &(r, target_b) in &block_succs[b] {
                let target_probe = format!("{namespace}individual{target_b}");
                extension.push_str(&format!(
                    "SubClassOf(<{probe}> ObjectSomeValuesFrom({r} <{target_probe}>))\n"
                ));
            }
        }
    }

    Some(NominalFreeIndividualProbes {
        extension,
        probes,
        precomputed_same,
    })
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
    Ok(Extended { realization, properties: hierarchy, data_properties: data_hierarchy, abox, top: top_classes })
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
