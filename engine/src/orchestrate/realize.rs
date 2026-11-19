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
    mut extended: Classification,
    probes: &[(String, String)],
    mode: TypeMode,
) -> Result<Realization, OrchestrateError> {
    let individual_of: BTreeMap<&str, &str> = probes
        .iter()
        .map(|(probe, individual)| (probe.as_str(), individual.as_str()))
        .collect();
    let is_probe = |name: &str| individual_of.contains_key(name);

    let mut types: BTreeMap<&str, BTreeSet<String>> = BTreeMap::new();
    let mut same: BTreeSet<[String; 2]> = BTreeSet::new();
    let mut source_rows = Vec::with_capacity(extended.subsumptions.len());
    for [sub, sup] in std::mem::take(&mut extended.subsumptions) {
        match (individual_of.get(sub.as_str()), individual_of.get(sup.as_str())) {
            (None, None) => source_rows.push([sub, sup]),
            (Some(a), None) => {
                if sup != OWL_THING {
                    types.entry(a).or_default().insert(sup);
                }
            }
            (Some(a), Some(b)) => {
                if a != b {
                    let (low, high) = if a < b { (a, b) } else { (b, a) };
                    same.insert([low.to_string(), high.to_string()]);
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
        return Ok(Realization { classification: extended, types: Vec::new(), same: Vec::new() });
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
        for classes in types.values_mut() {
            let direct: BTreeSet<String> = classes
                .iter()
                .filter(|c| !classes.iter().any(|d| strictly_below(d, c)))
                .cloned()
                .collect();
            *classes = direct;
        }
    }
    let types = types
        .into_iter()
        .flat_map(|(a, classes)| classes.into_iter().map(move |c| [a.to_string(), c]))
        .collect();
    Ok(Realization { classification: extended, types, same: same.into_iter().collect() })
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
    (format!("Declaration(Class(<{probe}>))\nEquivalentClasses(<{probe}> owl:Thing)\n"), probe)
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
    let (mut extension, probes) = if need_ind_probes {
        individual_extension(&text, &individuals)
    } else {
        (String::new(), Vec::new())
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
    let mut realization = split(classification, &probes, mode.unwrap_or(TypeMode::All))?;
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
}
